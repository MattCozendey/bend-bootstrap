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

# The drops of a reused cell
# --------------------------
#
# M.alloc reuses q, the first of the pend list: each part of q (by its
# mask) loses a pointer (M.dec), and one whose count reaches 0 goes to the
# pend list. A part may be twice in q, so that its count drops twice; it
# reaches 0 only at its last drop, as q's pointers to it are at most its
# count. Dv keeps the count of each part by the drops done.

# the cells pu are garbage out of the pend list Q
def Gq(pu: List<&2, U32>, +P: List<&2, U32>, +Q: List<&2, U32>) -> Bool:
  match pu:
    case Nil{}:
      True{}
    case Con{+x, rest}:
      Bool.and(Bool.and(D.Has(P, x), Bool.not(D.Has(Q, x))), Gq(rest, P, Q))

def Dv.of(s: Bool, h: Bool, +c0: Nat, +c3: Nat, +d: Nat) -> Bool:
  match s:
    case True{}:
      Bool.and(Nat.is_eq(c3, c0), Bool.not(h))
    case False{}:
      match h:
        case True{}:
          Nat.is_eq(c0, d)
        case False{}:
          Bool.and(Nat.is_eq(Nat.add(c3, d), c0), Bool.or(Nat.is_eq(d, 0n), Nat.is_lt(0n, c3)))

# the count of the cell y in M (from m), d of q's pointers to it dropped, the
# cells pu pushed to the pend list: a STATIC cell keeps its count and is not
# pushed; a pushed cell counted just them; another lost them, and keeps one
# when it lost any
def Dv(+m: Cr.Cir.Cells, +M: Cr.Cir.Cells, +pu: List<&2, U32>, +y: U32, +d: Nat) -> Bool:
  Dv.of(D.Stc(m, y), D.Has(pu, y), U32.to_nat(D.Fd(1n, m, y)), U32.to_nat(D.Fd(1n, M, y)), d)

# Dv of a part y of the mask bit b, by the drops done
def Dvm(+b: Bool, +y: U32, +m: Cr.Cir.Cells, +M: Cr.Cir.Cells, +pu: List<&2, U32>, +done: List<&2, U32>) -> Bool:
  Bool.or(Bool.not(b), Bool.or(U32.is_zero(y), Dv(m, M, pu, y, D.Occ(done, y))))

# Dv of the parts of q, of the mask am
def Dv3(+am: U32, +q: U32, +m: Cr.Cir.Cells, +M: Cr.Cir.Cells, +pu: List<&2, U32>, +done: List<&2, U32>) -> Bool:
  Bool.and(Dvm(U32.is_ne(U32.and(am, 1), 0), D.Fd(2n, m, q), m, M, pu, done),
    Bool.and(Dvm(U32.is_ne(U32.and(am, 2), 0), D.Fd(3n, m, q), m, M, pu, done),
      Dvm(U32.is_ne(U32.and(am, 4), 0), D.Fd(4n, m, q), m, M, pu, done)))

# before any drop
def dv.init.of(s: Bool, +c0: Nat) -> {Dv.of(s, False{}, c0, c0, 0n) == True{} : Bool}:
  match s:
    case True{}:
      K.Bo.and_i(Nat.is_eq(c0, c0), Bool.not(False{}), K.Na.eq_refl(c0), {==})
    case False{}:
      %Equal.sym(Nat, Nat.add(c0, 0n), c0, N.add_zero(c0)) :
        {Bool.and(Nat.is_eq(_, c0), Bool.or(Nat.is_eq(0n, 0n), Nat.is_lt(0n, c0))) == True{} : Bool}
      K.Bo.and_i(Nat.is_eq(c0, c0), Bool.or(Nat.is_eq(0n, 0n), Nat.is_lt(0n, c0)), K.Na.eq_refl(c0), {==})

def dv.init(+m: Cr.Cir.Cells, +y: U32) -> {Dv(m, m, Nil{}, y, 0n) == True{} : Bool}:
  dv.init.of(D.Stc(m, y), U32.to_nat(D.Fd(1n, m, y)))

def dvm.init(b: Bool, +y: U32, +m: Cr.Cir.Cells) -> {Dvm(b, y, m, m, Nil{}, Nil{}) == True{} : Bool}:
  K.Bo.or_ir(Bool.not(b), Bool.or(U32.is_zero(y), Dv(m, m, Nil{}, y, 0n)), K.Bo.or_ir(U32.is_zero(y), Dv(m, m, Nil{}, y, 0n), dv.init(m, y)))

def dv3.init(+am: U32, +q: U32, +m: Cr.Cir.Cells) -> {Dv3(am, q, m, m, Nil{}, Nil{}) == True{} : Bool}:
  +b1 = U32.is_ne(U32.and(am, 1), 0)
  +b2 = U32.is_ne(U32.and(am, 2), 0)
  +b4 = U32.is_ne(U32.and(am, 4), 0)
  +f2 = D.Fd(2n, m, q)
  +f3 = D.Fd(3n, m, q)
  +f4 = D.Fd(4n, m, q)
  K.Bo.and_i(Dvm(b1, f2, m, m, Nil{}, Nil{}), Bool.and(Dvm(b2, f3, m, m, Nil{}, Nil{}), Dvm(b4, f4, m, m, Nil{}, Nil{})), dvm.init(b1, f2, m),
    K.Bo.and_i(Dvm(b2, f3, m, m, Nil{}, Nil{}), Dvm(b4, f4, m, m, Nil{}, Nil{}), dvm.init(b2, f3, m), dvm.init(b4, f4, m)))

# the drop of x0 keeps Dv of a part y: y is x0 (hx), or another one, whose
# count and push stay (hf, hp)
def dvm.step.e(e: Bool, +y: U32, +m: Cr.Cir.Cells, +M: Cr.Cir.Cells, +M2: Cr.Cir.Cells, +pu: List<&2, U32>, +pu2: List<&2, U32>,
  +done: List<&2, U32>, +x0: U32, +eb: {U32.is_eq(y, x0) == e : Bool},
  h: {Bool.or(U32.is_zero(y), Dv(m, M, pu, y, D.Occ(done, y))) == True{} : Bool},
  hx: {Bool.or(U32.is_zero(x0), Dv(m, M2, pu2, x0, D.Occ(Con{x0, done}, x0))) == True{} : Bool},
  hf: {U32.is_eq(y, x0) == False{} : Bool} -> {D.Fd(1n, M2, y) == D.Fd(1n, M, y) : U32},
  hp: {U32.is_eq(y, x0) == False{} : Bool} -> {D.Has(pu2, y) == D.Has(pu, y) : Bool}) ->
  {Bool.or(U32.is_zero(y), Dv(m, M2, pu2, y, D.Occ(Con{x0, done}, y))) == True{} : Bool}:
  match e:
    case True{}:
      +ey = K.U.eq(y, x0, eb)
      %Equal.sym(U32, y, x0, ey) : {Bool.or(U32.is_zero(_), Dv(m, M2, pu2, _, D.Occ(Con{x0, done}, _))) == True{} : Bool}
      hx
    case False{}:
      +ex = K.U.ne.sym(y, x0, eb)
      +c0 = U32.to_nat(D.Fd(1n, m, y))
      %Equal.sym(Bool, U32.is_eq(x0, y), False{}, ex) :
        {Bool.or(U32.is_zero(y), Dv.of(D.Stc(m, y), D.Has(pu2, y), c0, U32.to_nat(D.Fd(1n, M2, y)), Nat.add(D.Nat.of(_), D.Occ(done, y)))) ==
          True{} : Bool}
      %Equal.sym(Bool, D.Has(pu2, y), D.Has(pu, y), hp(eb)) :
        {Bool.or(U32.is_zero(y), Dv.of(D.Stc(m, y), _, c0, U32.to_nat(D.Fd(1n, M2, y)), D.Occ(done, y))) == True{} : Bool}
      %Equal.sym(U32, D.Fd(1n, M2, y), D.Fd(1n, M, y), hf(eb)) :
        {Bool.or(U32.is_zero(y), Dv.of(D.Stc(m, y), D.Has(pu, y), c0, U32.to_nat(_), D.Occ(done, y))) == True{} : Bool}
      h

def dvm.step(b: Bool, +y: U32, +m: Cr.Cir.Cells, +M: Cr.Cir.Cells, +M2: Cr.Cir.Cells, +pu: List<&2, U32>, +pu2: List<&2, U32>,
  +done: List<&2, U32>, +x0: U32, h: {Dvm(b, y, m, M, pu, done) == True{} : Bool},
  hx: {Bool.or(U32.is_zero(x0), Dv(m, M2, pu2, x0, D.Occ(Con{x0, done}, x0))) == True{} : Bool},
  hf: {U32.is_eq(y, x0) == False{} : Bool} -> {D.Fd(1n, M2, y) == D.Fd(1n, M, y) : U32},
  hp: {U32.is_eq(y, x0) == False{} : Bool} -> {D.Has(pu2, y) == D.Has(pu, y) : Bool}) ->
  {Dvm(b, y, m, M2, pu2, Con{x0, done}) == True{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      dvm.step.e(U32.is_eq(y, x0), y, m, M, M2, pu, pu2, done, x0, {==}, h, hx, hf, hp)

def dv3.step(+am: U32, +q: U32, +m: Cr.Cir.Cells, +M: Cr.Cir.Cells, +M2: Cr.Cir.Cells, +pu: List<&2, U32>, +pu2: List<&2, U32>,
  +done: List<&2, U32>, +x0: U32, h: {Dv3(am, q, m, M, pu, done) == True{} : Bool},
  +hx: {Bool.or(U32.is_zero(x0), Dv(m, M2, pu2, x0, D.Occ(Con{x0, done}, x0))) == True{} : Bool},
  hf2: {U32.is_eq(D.Fd(2n, m, q), x0) == False{} : Bool} -> {D.Fd(1n, M2, D.Fd(2n, m, q)) == D.Fd(1n, M, D.Fd(2n, m, q)) : U32},
  hp2: {U32.is_eq(D.Fd(2n, m, q), x0) == False{} : Bool} -> {D.Has(pu2, D.Fd(2n, m, q)) == D.Has(pu, D.Fd(2n, m, q)) : Bool},
  hf3: {U32.is_eq(D.Fd(3n, m, q), x0) == False{} : Bool} -> {D.Fd(1n, M2, D.Fd(3n, m, q)) == D.Fd(1n, M, D.Fd(3n, m, q)) : U32},
  hp3: {U32.is_eq(D.Fd(3n, m, q), x0) == False{} : Bool} -> {D.Has(pu2, D.Fd(3n, m, q)) == D.Has(pu, D.Fd(3n, m, q)) : Bool},
  hf4: {U32.is_eq(D.Fd(4n, m, q), x0) == False{} : Bool} -> {D.Fd(1n, M2, D.Fd(4n, m, q)) == D.Fd(1n, M, D.Fd(4n, m, q)) : U32},
  hp4: {U32.is_eq(D.Fd(4n, m, q), x0) == False{} : Bool} -> {D.Has(pu2, D.Fd(4n, m, q)) == D.Has(pu, D.Fd(4n, m, q)) : Bool}) ->
  {Dv3(am, q, m, M2, pu2, Con{x0, done}) == True{} : Bool}:
  +h2 = h
  +b1 = U32.is_ne(U32.and(am, 1), 0)
  +b2 = U32.is_ne(U32.and(am, 2), 0)
  +b4 = U32.is_ne(U32.and(am, 4), 0)
  +f2 = D.Fd(2n, m, q)
  +f3 = D.Fd(3n, m, q)
  +f4 = D.Fd(4n, m, q)
  +A = Dvm(b1, f2, m, M, pu, done)
  +B = Dvm(b2, f3, m, M, pu, done)
  +C = Dvm(b4, f4, m, M, pu, done)
  +hbc = K.Bo.and_r(A, Bool.and(B, C), h2)
  K.Bo.and_i(Dvm(b1, f2, m, M2, pu2, Con{x0, done}), Bool.and(Dvm(b2, f3, m, M2, pu2, Con{x0, done}), Dvm(b4, f4, m, M2, pu2, Con{x0, done})),
    dvm.step(b1, f2, m, M, M2, pu, pu2, done, x0, K.Bo.and_l(A, Bool.and(B, C), h2), hx, hf2, hp2),
    K.Bo.and_i(Dvm(b2, f3, m, M2, pu2, Con{x0, done}), Dvm(b4, f4, m, M2, pu2, Con{x0, done}),
      dvm.step(b2, f3, m, M, M2, pu, pu2, done, x0, K.Bo.and_l(B, C, hbc), hx, hf3, hp3),
      dvm.step(b4, f4, m, M, M2, pu, pu2, done, x0, K.Bo.and_r(B, C, hbc), hx, hf4, hp4)))

# The parts of a garbage cell
# ---------------------------

# AL.cells of a garbage cell x of os
def al.mem.b(e: Bool, +o: U32, +rest: List<&2, U32>, +m: Cr.Cir.Cells, +P: List<&2, U32>, +Q: List<&2, U32>, +zs: List<&2, D.Zs>,
  +K: U32, +F: U32, +N: U32, +x: U32, +eo: {U32.is_eq(o, x) == e : Bool},
  hx: {Bool.or(U32.is_eq(o, x), D.Has(rest, x)) == True{} : Bool}, +h: {D.AL.cells(Con{o, rest}, m, P, Q, zs, K, F, N) == True{} : Bool},
  k: {D.Has(rest, x) == True{} : Bool} -> {D.AL.cells(rest, m, P, Q, zs, K, F, N) == True{} : Bool} ->
    {Bool.and(K.AL.hd(m, Q, x, F, N), Bool.and(K.AL.pt(m, P, zs, x, K, F, N), K.AL.ct(m, P, Q, x, F, N))) == True{} : Bool}) ->
  {Bool.and(K.AL.hd(m, Q, x, F, N), Bool.and(K.AL.pt(m, P, zs, x, K, F, N), K.AL.ct(m, P, Q, x, F, N))) == True{} : Bool}:
  match e:
    case True{}:
      +ex = K.U.eq(o, x, eo)
      %ex : {Bool.and(K.AL.hd(m, Q, _, F, N), Bool.and(K.AL.pt(m, P, zs, _, K, F, N), K.AL.ct(m, P, Q, _, F, N))) == True{} : Bool}
      K.Bo.and_i(K.AL.hd(m, Q, o, F, N), Bool.and(K.AL.pt(m, P, zs, o, K, F, N), K.AL.ct(m, P, Q, o, F, N)), K.al.hd(o, rest, m, P, Q, zs, K, F, N, h),
        K.Bo.and_i(K.AL.pt(m, P, zs, o, K, F, N), K.AL.ct(m, P, Q, o, F, N), K.al.pt(o, rest, m, P, Q, zs, K, F, N, h),
          K.al.ct(o, rest, m, P, Q, zs, K, F, N, h)))
    case False{}:
      k((%eo : {Bool.or(_, D.Has(rest, x)) == True{} : Bool}; hx), K.al.rest(o, rest, m, P, Q, zs, K, F, N, h))

def al.mem(os: List<&2, U32>, +m: Cr.Cir.Cells, +P: List<&2, U32>, +Q: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32,
  +N: U32, +x: U32, hx: {D.Has(os, x) == True{} : Bool}, h: {D.AL.cells(os, m, P, Q, zs, K, F, N) == True{} : Bool}) ->
  {Bool.and(K.AL.hd(m, Q, x, F, N), Bool.and(K.AL.pt(m, P, zs, x, K, F, N), K.AL.ct(m, P, Q, x, F, N))) == True{} : Bool}:
  match os:
    case Nil{}:
      K.Bo.tf({Bool.and(K.AL.hd(m, Q, x, F, N), Bool.and(K.AL.pt(m, P, zs, x, K, F, N), K.AL.ct(m, P, Q, x, F, N))) == True{} : Bool}, hx)
    case Con{+o, +rest}:
      al.mem.b(U32.is_eq(o, x), o, rest, m, P, Q, zs, K, F, N, x, {==}, hx, h,
        hr => cr => al.mem(rest, m, P, Q, zs, K, F, N, x, hr, cr))

# q's pointers are among the garbage's, q one of it
def pp.ge.b(e: Bool, +o: U32, +rest: List<&2, U32>, +m: Cr.Cir.Cells, +q: U32, +c: U32, eo: {U32.is_eq(o, q) == e : Bool},
  h: {Bool.or(U32.is_eq(o, q), D.Has(rest, q)) == True{} : Bool},
  k: {D.Has(rest, q) == True{} : Bool} -> N.Le(D.Ow(m, q, c), D.Pp(rest, m, c))) ->
  N.Le(D.Ow(m, q, c), Nat.add(D.Ow(m, o, c), D.Pp(rest, m, c))):
  match e:
    case True{}:
      +ex = K.U.eq(o, q, eo)
      %ex : N.Le(D.Ow(m, _, c), Nat.add(D.Ow(m, o, c), D.Pp(rest, m, c)))
      N.le_add_r(D.Ow(m, o, c), D.Pp(rest, m, c))
    case False{}:
      N.le_trans(D.Ow(m, q, c), D.Pp(rest, m, c), Nat.add(D.Ow(m, o, c), D.Pp(rest, m, c)),
        k((%eo : {Bool.or(_, D.Has(rest, q)) == True{} : Bool}; h)), N.le_add_l(D.Ow(m, o, c), D.Pp(rest, m, c)))

def pp.ge(P: List<&2, U32>, +m: Cr.Cir.Cells, +q: U32, +c: U32, h: {D.Has(P, q) == True{} : Bool}) -> N.Le(D.Ow(m, q, c), D.Pp(P, m, c)):
  match P:
    case Nil{}:
      K.Bo.tf(N.Le(D.Ow(m, q, c), 0n), h)
    case Con{+o, +rest}:
      pp.ge.b(U32.is_eq(o, q), o, rest, m, q, c, {==}, h, hr => pp.ge(rest, m, q, c, hr))

# a part x of the garbage cell q, by a mask bit, neither 0 nor STATIC: q's
# pointers to it at most its count, out of the pend list Q, and garbage
# unless it counts more than q's pointers
def PtF(+m: Cr.Cir.Cells, +P: List<&2, U32>, +Q: List<&2, U32>, +q: U32, +x: U32) -> Bool:
  +ow = D.Ow(m, q, x)
  +c0 = U32.to_nat(D.Fd(1n, m, x))
  Bool.and(Nat.is_le(ow, c0), Bool.and(Bool.not(D.Has(Q, x)), Bool.or(D.Has(P, x), Nat.is_lt(ow, c0))))

def pt.fx.q(g: Bool, +m: Cr.Cir.Cells, +P: List<&2, U32>, +Q: List<&2, U32>, +q: U32, +x: U32, +eg: {D.Has(Q, x) == g : Bool},
  +ep: {D.Has(P, x) == True{} : Bool},
  hpk: {Bool.pick(Bool, D.Has(Q, x), Nat.is_eq(D.Pp(P, m, x), 0n),
    Bool.and(Nat.is_eq(D.Pp(P, m, x), U32.to_nat(D.Fd(1n, m, x))), Nat.is_lt(0n, D.Pp(P, m, x)))) == True{} : Bool},
  hge: N.Le(D.Ow(m, q, x), D.Pp(P, m, x)), hb1: N.Le(1n, D.Ow(m, q, x))) -> {PtF(m, P, Q, q, x) == True{} : Bool}:
  match g:
    case True{}:
      +pp = D.Pp(P, m, x)
      +ow = D.Ow(m, q, x)
      +c0 = U32.to_nat(D.Fd(1n, m, x))
      +h0 = {(%eg : {Bool.pick(Bool, _, Nat.is_eq(pp, 0n), Bool.and(Nat.is_eq(pp, c0), Nat.is_lt(0n, pp))) == True{} : Bool}; hpk) :
        {Nat.is_eq(pp, 0n) == True{} : Bool}}
      Empty.absurd({PtF(m, P, Q, q, x) == True{} : Bool},
        N.le_trans(1n, ow, 0n, hb1, (%K.Na.eq(pp, 0n, h0) : N.Le(ow, _); hge)))
    case False{}:
      +pp = D.Pp(P, m, x)
      +ow = D.Ow(m, q, x)
      +c0 = U32.to_nat(D.Fd(1n, m, x))
      +h1 = {(%eg : {Bool.pick(Bool, _, Nat.is_eq(pp, 0n), Bool.and(Nat.is_eq(pp, c0), Nat.is_lt(0n, pp))) == True{} : Bool}; hpk) :
        {Bool.and(Nat.is_eq(pp, c0), Nat.is_lt(0n, pp)) == True{} : Bool}}
      +le = {(%K.Na.eq(pp, c0, K.Bo.and_l(Nat.is_eq(pp, c0), Nat.is_lt(0n, pp), h1)) : N.Le(ow, _); hge) : N.Le(ow, c0)}
      K.Bo.and_i(Nat.is_le(ow, c0), Bool.and(Bool.not(D.Has(Q, x)), Bool.or(D.Has(P, x), Nat.is_lt(ow, c0))), K.ofT(Nat.is_le(ow, c0), le),
        K.Bo.and_i(Bool.not(D.Has(Q, x)), Bool.or(D.Has(P, x), Nat.is_lt(ow, c0)), K.Bo.not_i(D.Has(Q, x), eg),
          K.Bo.or_il(D.Has(P, x), Nat.is_lt(ow, c0), ep)))

def pt.fx.p(e: Bool, +m: Cr.Cir.Cells, +P: List<&2, U32>, +Q: List<&2, U32>, +zs: List<&2, D.Zs>, +q: U32, +x: U32, +K: U32,
  +F: U32, +N: U32, +ep: {D.Has(P, x) == e : Bool},
  hor: {Bool.or(Bool.and(D.Has(P, x), Nat.is_lt(D.Zz(zs, x), D.Zz(zs, q))), Nat.is_lt(D.Pp(P, m, x), U32.to_nat(D.Fd(1n, m, x)))) == True{} : Bool},
  +hq: {D.Has(P, q) == True{} : Bool}, +hsub: {D.Sub(Q, P) == True{} : Bool}, +hcs: {D.AL.cells(P, m, P, Q, zs, K, F, N) == True{} : Bool},
  +hb1: N.Le(1n, D.Ow(m, q, x))) -> {PtF(m, P, Q, q, x) == True{} : Bool}:
  match e:
    case True{}:
      +pp = D.Pp(P, m, x)
      +c0 = U32.to_nat(D.Fd(1n, m, x))
      +hx = al.mem(P, m, P, Q, zs, K, F, N, x, ep, hcs)
      +Hd = K.AL.hd(m, Q, x, F, N)
      +Pt = K.AL.pt(m, P, zs, x, K, F, N)
      +Ct = K.AL.ct(m, P, Q, x, F, N)
      +hct = K.Bo.and_r(Pt, Ct, K.Bo.and_r(Hd, Bool.and(Pt, Ct), hx))
      +hpk = K.Bo.and_r(Nat.is_eq(D.Pc(Nat.sub(U32.to_nat(N), U32.to_nat(F)), m, Q, F, x), pp),
        Bool.pick(Bool, D.Has(Q, x), Nat.is_eq(pp, 0n), Bool.and(Nat.is_eq(pp, c0), Nat.is_lt(0n, pp))), hct)
      pt.fx.q(D.Has(Q, x), m, P, Q, q, x, {==}, ep, hpk, pp.ge(P, m, q, x, hq), hb1)
    case False{}:
      +pp = D.Pp(P, m, x)
      +ow = D.Ow(m, q, x)
      +c0 = U32.to_nat(D.Fd(1n, m, x))
      +hlive = {(%ep : {Bool.or(Bool.and(_, Nat.is_lt(D.Zz(zs, x), D.Zz(zs, q))), Nat.is_lt(pp, c0)) == True{} : Bool}; hor) :
        {Nat.is_lt(pp, c0) == True{} : Bool}}
      +h1 = N.le_trans(1n+ow, 1n+pp, c0, pp.ge(P, m, q, x, hq), K.Na.lt1(pp, c0, hlive))
      K.Bo.and_i(Nat.is_le(ow, c0), Bool.and(Bool.not(D.Has(Q, x)), Bool.or(D.Has(P, x), Nat.is_lt(ow, c0))),
        K.ofT(Nat.is_le(ow, c0), N.weaken(ow, c0, h1)),
        K.Bo.and_i(Bool.not(D.Has(Q, x)), Bool.or(D.Has(P, x), Nat.is_lt(ow, c0)), K.Bo.not_i(D.Has(Q, x), K.sub.nhas(Q, P, x, hsub, ep)),
          K.Bo.or_ir(D.Has(P, x), Nat.is_lt(ow, c0), K.Na.lt1i(ow, c0, h1))))

# the part x of q by a mask bit of am: a cell, and with x not STATIC, PtF
def pt.cell(+m: Cr.Cir.Cells, +P: List<&2, U32>, +zs: List<&2, D.Zs>, +z: Nat, +am: U32, +bit: U32, +x: U32, +K: U32, +F: U32, +N: U32,
  h: {D.AL.part(m, P, zs, z, am, bit, x, K, F, N) == True{} : Bool}, hon: {U32.is_zero(U32.and(am, bit)) == False{} : Bool},
  hz: {U32.is_zero(x) == False{} : Bool}) -> {Cr.Cir.is_cell(x, K, F, N) == True{} : Bool}:
  +R3 = Bool.or(D.Stc(m, x), Bool.or(Bool.and(D.Has(P, x), Nat.is_lt(D.Zz(zs, x), z)), Nat.is_lt(D.Pp(P, m, x), U32.to_nat(D.Fd(1n, m, x)))))
  +r1 = K.Bo.or_r(U32.is_zero(U32.and(am, bit)), Bool.or(U32.is_zero(x), Bool.and(Cr.Cir.is_cell(x, K, F, N), R3)), h, hon)
  K.Bo.and_l(Cr.Cir.is_cell(x, K, F, N), R3, K.Bo.or_r(U32.is_zero(x), Bool.and(Cr.Cir.is_cell(x, K, F, N), R3), r1, hz))

def pt.fx(+m: Cr.Cir.Cells, +P: List<&2, U32>, +Q: List<&2, U32>, +zs: List<&2, D.Zs>, +q: U32, +am: U32, +bit: U32, +x: U32,
  +K: U32, +F: U32, +N: U32, h: {D.AL.part(m, P, zs, D.Zz(zs, q), am, bit, x, K, F, N) == True{} : Bool},
  hon: {U32.is_zero(U32.and(am, bit)) == False{} : Bool}, hz: {U32.is_zero(x) == False{} : Bool}, hs: {D.Stc(m, x) == False{} : Bool},
  +hq: {D.Has(P, q) == True{} : Bool}, +hsub: {D.Sub(Q, P) == True{} : Bool}, +hcs: {D.AL.cells(P, m, P, Q, zs, K, F, N) == True{} : Bool},
  +hb1: N.Le(1n, D.Ow(m, q, x))) -> {PtF(m, P, Q, q, x) == True{} : Bool}:
  +z = D.Zz(zs, q)
  +R4 = Bool.or(Bool.and(D.Has(P, x), Nat.is_lt(D.Zz(zs, x), z)), Nat.is_lt(D.Pp(P, m, x), U32.to_nat(D.Fd(1n, m, x))))
  +R3 = Bool.or(D.Stc(m, x), R4)
  +r1 = K.Bo.or_r(U32.is_zero(U32.and(am, bit)), Bool.or(U32.is_zero(x), Bool.and(Cr.Cir.is_cell(x, K, F, N), R3)), h, hon)
  +r2 = K.Bo.or_r(U32.is_zero(x), Bool.and(Cr.Cir.is_cell(x, K, F, N), R3), r1, hz)
  pt.fx.p(D.Has(P, x), m, P, Q, zs, q, x, K, F, N, {==}, K.Bo.or_r(D.Stc(m, x), R4, K.Bo.and_r(Cr.Cir.is_cell(x, K, F, N), R3, r2), hs),
    hq, hsub, hcs, hb1)

# The drop's steps
# ----------------

# each of the cells xs is a part of c
def Pts(xs: List<&2, U32>, +m: Cr.Cir.Cells, +c: U32) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, rest}:
      Bool.and(Nat.is_lt(0n, D.Ow(m, c, x)), Pts(rest, m, c))

# the registers at a drop: Rg.ex's, with pend, dx, dr, aq and am
def Rd(+R: List<&2, U32>, +p3: U32, +p4: U32, +p5: U32, +q: U32, +am: U32) -> List<&2, U32>:
  Rp([p3, p4, p5, q, am], D.Rg.ex(63n, R, 0n))

def rd.z(+R: List<&2, U32>, +p3: U32, +p4: U32, +p5: U32, +q: U32, +am: U32, +x: U32) ->
  {Sr.X.set(Rd(R, p3, p4, p5, q, am), 4n, x) == Rd(R, p3, x, p5, q, am) : List<&2, U32>}:
  {==}

def rd.n(+R: List<&2, U32>, +p3: U32, +p4: U32, +p5: U32, +q: U32, +am: U32, +x: U32, +dn: U32) ->
  {Sr.X.set(Sr.X.set(Rd(R, p3, p4, p5, q, am), 4n, x), 5n, dn) == Rd(R, p3, x, dn, q, am) : List<&2, U32>}:
  {==}

def rd.p(+R: List<&2, U32>, +p3: U32, +p4: U32, +p5: U32, +q: U32, +am: U32, +x: U32, +dn: U32) ->
  {Sr.X.set(Sr.X.set(Sr.X.set(Rd(R, p3, p4, p5, q, am), 4n, x), 5n, dn), 3n, x) == Rd(R, x, x, dn, q, am) : List<&2, U32>}:
  {==}

# what follows a drop: the run from the state after it, with the drops done
def Dk(+f: Nat, +B: Cr.Cir.Stmt, +R: List<&2, U32>, +q: U32, +m: Cr.Cir.Cells, +nx: U32, +F: U32, +K: U32, +pg: U32, +L: U32,
  +I: List<&2, Word(8n)>, +P: List<&2, U32>, +Qr: List<&2, U32>, +done: List<&2, U32>, -Bud: Nat,
  -Rq: List<&2, U32> -> Cr.Cir.Cells -> U32 -> U32 -> Type) -> Type:
  @p3: U32 -> @p4: U32 -> @p5: U32 -> @ws: List<&2, W1> -> @pu: List<&2, U32> ->
    {W1s.pt(ws, m, q) == True{} : Bool} -> {Dv3(D.Am(m, q), q, m, W1s(ws, m), pu, done) == True{} : Bool} ->
    {D.Chain(List.append(&2, U32, pu, Qr), W1s(ws, m), p3) == True{} : Bool} -> {D.Nodup(pu) == True{} : Bool} ->
    {Gq(pu, P, Con{q, Qr}) == True{} : Bool} -> {Pts(pu, m, q) == True{} : Bool} ->
    D.Ok(Cr.Cir.exec(1n+f, B, Sr.X.st(Rd(R, p3, p4, p5, q, D.Am(m, q)), W1s(ws, m), nx, F, K, pg, L, I)), F, K, L, I, Bud, Rq)

# a statement a whose run is M.dec's, which reaches st2 (st3), then B
def dr.run(+f: Nat, +a: Cr.Cir.Stmt, +B: Cr.Cir.Stmt, +st0: Cr.Cir.State, +st1: Cr.Cir.State, +st2: Cr.Cir.State, +st3: Cr.Cir.State,
  +F: U32, +K: U32, +L: U32, +I: List<&2, Word(8n)>, -Bud: Nat, -Rq: List<&2, U32> -> Cr.Cir.Cells -> U32 -> U32 -> Type,
  e1: {Cr.Cir.exec(1n+f, a, st0) == Cr.Cir.exec(1n+f, Mc.M.dec(4n), st1) : Cr.Cir.Out},
  e2: {Cr.Cir.exec(1n+f, Mc.M.dec(4n), st1) == Cr.Cir.Out.next{st2} : Cr.Cir.Out}, e3: {st2 == st3 : Cr.Cir.State},
  k: D.Ok(Cr.Cir.exec(1n+f, B, st3), F, K, L, I, Bud, Rq)) -> D.Ok(Cr.Cir.exec(1n+f, Cr.Cir.Stmt.seq{a, B}, st0), F, K, L, I, Bud, Rq):
  +o0 = Cr.Cir.exec(1n+f, a, st0)
  +o1 = Cr.Cir.exec(1n+f, Mc.M.dec(4n), st1)
  +h = Equal.sym(Cr.Cir.Out, o0, Cr.Cir.Out.next{st2}, Equal.trans(Cr.Cir.Out, o0, o1, Cr.Cir.Out.next{st2}, e1, e2))
  +s0 = Cr.Cir.exec(1n+f, Cr.Cir.Stmt.seq{a, B}, st0)
  K.Ok.eq(s0, Cr.Cir.exec(1n+f, B, st3), F, K, L, I, Bud, Rq,
    Equal.sym(Cr.Cir.Out, s0, Cr.Cir.exec(1n+f, B, st3),
      Equal.trans(Cr.Cir.Out, s0, Cr.Cir.exec(1n+f, B, st2), Cr.Cir.exec(1n+f, B, st3), K.X.seq(f, a, B, st0, st2, h),
        Equal.cong(Cr.Cir.State, Cr.Cir.Out, s => Cr.Cir.exec(1n+f, B, s), st2, st3, e3))),
    k)

# Dv of a STATIC cell does not see the drops
def dv.s(+m: Cr.Cir.Cells, +M: Cr.Cir.Cells, +pu: List<&2, U32>, +x0: U32, +d: Nat, +d2: Nat, +hs: {D.Stc(m, x0) == True{} : Bool},
  h: {Dv(m, M, pu, x0, d) == True{} : Bool}) -> {Dv(m, M, pu, x0, d2) == True{} : Bool}:
  +c0 = U32.to_nat(D.Fd(1n, m, x0))
  +c3 = U32.to_nat(D.Fd(1n, M, x0))
  %Equal.sym(Bool, D.Stc(m, x0), True{}, hs) : {Dv.of(_, D.Has(pu, x0), c0, c3, d2) == True{} : Bool}
  (%hs : {Dv.of(_, D.Has(pu, x0), c0, c3, d) == True{} : Bool}; h)

# a part neither STATIC nor pushed, which lost d of q's pointers: its count
# and d give its old count
def dv.np.of(hp: Bool, +c0: Nat, +c3: Nat, +d: Nat, +pu: List<&2, U32>, +x0: U32, ehp: {D.Has(pu, x0) == hp : Bool},
  h: {Dv.of(False{}, hp, c0, c3, d) == True{} : Bool}, hb: N.Le(1n+d, c0)) -> {D.Has(pu, x0) == False{} : Bool}:
  match hp:
    case True{}:
      Empty.absurd({D.Has(pu, x0) == False{} : Bool}, N.not_succ_le(d, (%K.Na.eq(c0, d, h) : N.Le(1n+d, _); hb)))
    case False{}:
      ehp

def dv.np(+m: Cr.Cir.Cells, +M: Cr.Cir.Cells, +pu: List<&2, U32>, +x0: U32, +d: Nat, +hs: {D.Stc(m, x0) == False{} : Bool},
  h: {Dv(m, M, pu, x0, d) == True{} : Bool}, hb: N.Le(1n+d, U32.to_nat(D.Fd(1n, m, x0)))) -> {D.Has(pu, x0) == False{} : Bool}:
  +c0 = U32.to_nat(D.Fd(1n, m, x0))
  +c3 = U32.to_nat(D.Fd(1n, M, x0))
  dv.np.of(D.Has(pu, x0), c0, c3, d, pu, x0, {==}, (%hs : {Dv.of(_, D.Has(pu, x0), c0, c3, d) == True{} : Bool}; h), hb)

def dv.ne(+m: Cr.Cir.Cells, +M: Cr.Cir.Cells, +pu: List<&2, U32>, +x0: U32, +d: Nat, +hs: {D.Stc(m, x0) == False{} : Bool},
  +hp: {D.Has(pu, x0) == False{} : Bool}, h: {Dv(m, M, pu, x0, d) == True{} : Bool}) ->
  {Nat.add(U32.to_nat(D.Fd(1n, M, x0)), d) == U32.to_nat(D.Fd(1n, m, x0)) : Nat}:
  +c0 = U32.to_nat(D.Fd(1n, m, x0))
  +c3 = U32.to_nat(D.Fd(1n, M, x0))
  +h2 = {(%hp : {Dv.of(False{}, _, c0, c3, d) == True{} : Bool}; (%hs : {Dv.of(_, D.Has(pu, x0), c0, c3, d) == True{} : Bool}; h)) :
    {Bool.and(Nat.is_eq(Nat.add(c3, d), c0), Bool.or(Nat.is_eq(d, 0n), Nat.is_lt(0n, c3))) == True{} : Bool}}
  K.Na.eq(Nat.add(c3, d), c0, K.Bo.and_l(Nat.is_eq(Nat.add(c3, d), c0), Bool.or(Nat.is_eq(d, 0n), Nat.is_lt(0n, c3)), h2))

# Dv of a part after its drop to dn, not pushed
def dv.n(+m: Cr.Cir.Cells, +M: Cr.Cir.Cells, +pu: List<&2, U32>, +x0: U32, +done: List<&2, U32>, +hs: {D.Stc(m, x0) == False{} : Bool},
  +hp: {D.Has(pu, x0) == False{} : Bool},
  e: {Nat.add(U32.to_nat(D.Fd(1n, M, x0)), D.Occ(done, x0)) == U32.to_nat(D.Fd(1n, m, x0)) : Nat},
  +hd: {U32.is_eq(U32.sub(D.Fd(1n, M, x0), 1), 0) == False{} : Bool}, +h1: N.Le(1n, U32.to_nat(D.Fd(1n, M, x0)))) ->
  {Dv(m, K.St1(M, x0, U32.sub(D.Fd(1n, M, x0), 1)), pu, x0, D.Occ(Con{x0, done}, x0)) == True{} : Bool}:
  +dn = U32.sub(D.Fd(1n, M, x0), 1)
  +M2 = K.St1(M, x0, dn)
  +c0 = U32.to_nat(D.Fd(1n, m, x0))
  +c3 = U32.to_nat(D.Fd(1n, M, x0))
  +d = D.Occ(done, x0)
  +E1 = N.add_succ_r(U32.to_nat(dn), d)
  +E2 = Equal.cong(Nat, Nat, z => Nat.add(z, d), 1n+U32.to_nat(dn), c3, K.U.dec(D.Fd(1n, M, x0), h1))
  +Et = Equal.trans(Nat, Nat.add(U32.to_nat(dn), 1n+d), 1n+Nat.add(U32.to_nat(dn), d), c0, E1,
    Equal.trans(Nat, 1n+Nat.add(U32.to_nat(dn), d), Nat.add(c3, d), c0, E2, e))
  %Equal.sym(Bool, U32.is_eq(x0, x0), True{}, K.U.eq_refl(x0)) :
    {Dv.of(D.Stc(m, x0), D.Has(pu, x0), c0, U32.to_nat(D.Fd(1n, M2, x0)), Nat.add(D.Nat.of(_), d)) == True{} : Bool}
  %Equal.sym(Bool, D.Stc(m, x0), False{}, hs) : {Dv.of(_, D.Has(pu, x0), c0, U32.to_nat(D.Fd(1n, M2, x0)), 1n+d) == True{} : Bool}
  %Equal.sym(Bool, D.Has(pu, x0), False{}, hp) : {Dv.of(False{}, _, c0, U32.to_nat(D.Fd(1n, M2, x0)), 1n+d) == True{} : Bool}
  %Equal.sym(U32, D.Fd(1n, M2, x0), dn, K.f1.st1(M, x0, dn)) : {Dv.of(False{}, False{}, c0, U32.to_nat(_), 1n+d) == True{} : Bool}
  K.Bo.and_i(Nat.is_eq(Nat.add(U32.to_nat(dn), 1n+d), c0), Bool.or(Nat.is_eq(1n+d, 0n), Nat.is_lt(0n, U32.to_nat(dn))),
    (%Equal.sym(Nat, Nat.add(U32.to_nat(dn), 1n+d), c0, Et) : {Nat.is_eq(_, c0) == True{} : Bool}; K.Na.eq_refl(c0)),
    K.Bo.or_ir(Nat.is_eq(1n+d, 0n), Nat.is_lt(0n, U32.to_nat(dn)), K.Na.lt1i(0n, U32.to_nat(dn), K.U.pos(dn, hd))))

# a part whose count reaches 0 counted just the drops done
def p.c0(+M: Cr.Cir.Cells, +x0: U32, +d: Nat, +c0: Nat, e: {Nat.add(U32.to_nat(D.Fd(1n, M, x0)), d) == c0 : Nat},
  +hd: {U32.is_eq(U32.sub(D.Fd(1n, M, x0), 1), 0) == True{} : Bool}, +h1: N.Le(1n, U32.to_nat(D.Fd(1n, M, x0)))) -> {1n+d == c0 : Nat}:
  +dn = U32.sub(D.Fd(1n, M, x0), 1)
  +c3 = U32.to_nat(D.Fd(1n, M, x0))
  +tz = Equal.cong(U32, Nat, z => U32.to_nat(z), dn, 0, K.U.eq(dn, 0, hd))
  +c3e = {(%tz : {1n+_ == c3 : Nat}; K.U.dec(D.Fd(1n, M, x0), h1)) : {1n == c3 : Nat}}
  Equal.trans(Nat, 1n+d, Nat.add(c3, d), c0, Equal.cong(Nat, Nat, z => Nat.add(z, d), 1n, c3, c3e), e)

# Dv of a part after its drop to 0: pushed
def dv.p(+m: Cr.Cir.Cells, +M: Cr.Cir.Cells, +pu: List<&2, U32>, +x0: U32, +p3: U32, +done: List<&2, U32>,
  +hs: {D.Stc(m, x0) == False{} : Bool}, E: {1n+D.Occ(done, x0) == U32.to_nat(D.Fd(1n, m, x0)) : Nat}) ->
  {Dv(m, K.St1(K.St1(M, x0, U32.sub(D.Fd(1n, M, x0), 1)), x0, p3), Con{x0, pu}, x0, D.Occ(Con{x0, done}, x0)) == True{} : Bool}:
  +M3 = K.St1(K.St1(M, x0, U32.sub(D.Fd(1n, M, x0), 1)), x0, p3)
  +c0 = U32.to_nat(D.Fd(1n, m, x0))
  +d = D.Occ(done, x0)
  %Equal.sym(Bool, U32.is_eq(x0, x0), True{}, K.U.eq_refl(x0)) :
    {Dv.of(D.Stc(m, x0), Bool.or(_, D.Has(pu, x0)), c0, U32.to_nat(D.Fd(1n, M3, x0)), Nat.add(D.Nat.of(_), d)) == True{} : Bool}
  %Equal.sym(Bool, D.Stc(m, x0), False{}, hs) : {Dv.of(_, True{}, c0, U32.to_nat(D.Fd(1n, M3, x0)), 1n+d) == True{} : Bool}
  (%E : {Nat.is_eq(_, 1n+d) == True{} : Bool}; K.Na.eq_refl(1n+d))

# a push keeps whether another cell is pushed
def hpu.push(+pu: List<&2, U32>, +x0: U32, +y: U32, ne: {U32.is_eq(y, x0) == False{} : Bool}) ->
  {D.Has(Con{x0, pu}, y) == D.Has(pu, y) : Bool}:
  %Equal.sym(Bool, U32.is_eq(x0, y), False{}, K.U.ne.sym(y, x0, ne)) : {Bool.or(_, D.Has(pu, y)) == D.Has(pu, y) : Bool}
  {==}

# b <= a: not a < b
def na.nlt(b: Bool, +a: Nat, +c: Nat, eb: {Nat.is_lt(a, c) == b : Bool}, h: N.Le(c, a)) -> {Nat.is_lt(a, c) == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({Nat.is_lt(a, c) == False{} : Bool}, N.not_succ_le(a, N.le_trans(1n+a, c, a, K.Na.lt1(a, c, eb), h)))
    case False{}:
      eb

# the drop of the part 0: nothing
def dr.z(+f: Nat, +k: Nat, +bit: U32, +B: Cr.Cir.Stmt, +R: List<&2, U32>, +p3: U32, +p4: U32, +p5: U32, +q: U32, +m: Cr.Cir.Cells,
  +ws: List<&2, W1>, +nx: U32, +F: U32, +K: U32, +pg: U32, +L: U32, +I: List<&2, Word(8n)>, +P: List<&2, U32>, +Qr: List<&2, U32>,
  +zs: List<&2, D.Zs>, +pu: List<&2, U32>, +done: List<&2, U32>, -Bud: Nat, -Rq: List<&2, U32> -> Cr.Cir.Cells -> U32 -> U32 -> Type,
  +hz0: {U32.is_eq(D.Fd(k, m, q), 0) == True{} : Bool}, e1: {Cr.Cir.exec(1n+f, Mc.M.dec.part(k, bit), Sr.X.st(Rd(R, p3, p4, p5, q, D.Am(m, q)), W1s(ws, m), nx, F, K, pg, L, I)) == Cr.Cir.exec(1n+f, Mc.M.dec(4n), Sr.X.st(Sr.X.set(Rd(R, p3, p4, p5, q, D.Am(m, q)), 4n, D.Fd(k, m, q)), W1s(ws, m), nx, F, K, pg, L, I)) : Cr.Cir.Out},
  hpt: {W1s.pt(ws, m, q) == True{} : Bool}, +hdv: {Dv3(D.Am(m, q), q, m, W1s(ws, m), pu, done) == True{} : Bool},
  hch: {D.Chain(List.append(&2, U32, pu, Qr), W1s(ws, m), p3) == True{} : Bool}, hnd: {D.Nodup(pu) == True{} : Bool},
  hgq: {Gq(pu, P, Con{q, Qr}) == True{} : Bool}, hpp: {Pts(pu, m, q) == True{} : Bool},
  kont: Dk(f, B, R, q, m, nx, F, K, pg, L, I, P, Qr, Con{D.Fd(k, m, q), done}, Bud, Rq)) ->
  D.Ok(Cr.Cir.exec(1n+f, Cr.Cir.Stmt.seq{Mc.M.dec.part(k, bit), B}, Sr.X.st(Rd(R, p3, p4, p5, q, D.Am(m, q)), W1s(ws, m), nx, F, K, pg, L, I)), F, K, L, I, Bud, Rq):
  +am = D.Am(m, q)
  +M = W1s(ws, m)
  +x0 = D.Fd(k, m, q)
  +regs = Rd(R, p3, p4, p5, q, am)
  +regs4 = Sr.X.set(regs, 4n, x0)
  +st0 = Sr.X.st(regs, M, nx, F, K, pg, L, I)
  +st1 = Sr.X.st(regs4, M, nx, F, K, pg, L, I)
  +e0 = K.U.eq(x0, 0, hz0)
  +hr0 = {%e0 : {List.get(&2, U32, regs4, 4n) == Some{_} : Maybe<&2, U32>}; {==} : {List.get(&2, U32, regs4, 4n) == Some{0} : Maybe<&2, U32>}}
  +e2 = Sr.dec.eq.z(1n+f, regs4, M, nx, F, K, pg, L, I, 4n, hr0)
  +e3 = Equal.cong(List<&2, U32>, Cr.Cir.State, rg => Sr.X.st(rg, M, nx, F, K, pg, L, I), regs4, Rd(R, p3, x0, p5, q, am), rd.z(R, p3, p4, p5, q, am, x0))
  +hx = K.Bo.or_il(U32.is_zero(x0), Dv(m, M, pu, x0, D.Occ(Con{x0, done}, x0)), hz0)
  dr.run(f, Mc.M.dec.part(k, bit), B, st0, st1, st1, Sr.X.st(Rd(R, p3, x0, p5, q, am), M, nx, F, K, pg, L, I), F, K, L, I, Bud, Rq, e1, e2, e3,
    kont(p3, x0, p5, ws, pu, hpt, dv3.step(am, q, m, M, M, pu, pu, done, x0, hdv, hx, +ne => {==}, +ne => {==}, +ne => {==}, +ne => {==},
      +ne => {==}, +ne => {==}), hch, hnd, hgq, hpp))

# the drop of a STATIC part: nothing
def dr.s(+f: Nat, +k: Nat, +bit: U32, +B: Cr.Cir.Stmt, +R: List<&2, U32>, +p3: U32, +p4: U32, +p5: U32, +q: U32, +m: Cr.Cir.Cells,
  +ws: List<&2, W1>, +nx: U32, +F: U32, +K: U32, +pg: U32, +L: U32, +I: List<&2, Word(8n)>, +P: List<&2, U32>, +Qr: List<&2, U32>,
  +zs: List<&2, D.Zs>, +pu: List<&2, U32>, +done: List<&2, U32>, -Bud: Nat, -Rq: List<&2, U32> -> Cr.Cir.Cells -> U32 -> U32 -> Type,
  +hz: {U32.is_eq(D.Fd(k, m, q), 0) == False{} : Bool}, +hc: {Cr.Cir.is_cell(D.Fd(k, m, q), K, F, nx) == True{} : Bool}, +hs: {D.Stc(m, D.Fd(k, m, q)) == True{} : Bool}, +hcur: {Dv(m, W1s(ws, m), pu, D.Fd(k, m, q), D.Occ(done, D.Fd(k, m, q))) == True{} : Bool}, e1: {Cr.Cir.exec(1n+f, Mc.M.dec.part(k, bit), Sr.X.st(Rd(R, p3, p4, p5, q, D.Am(m, q)), W1s(ws, m), nx, F, K, pg, L, I)) == Cr.Cir.exec(1n+f, Mc.M.dec(4n), Sr.X.st(Sr.X.set(Rd(R, p3, p4, p5, q, D.Am(m, q)), 4n, D.Fd(k, m, q)), W1s(ws, m), nx, F, K, pg, L, I)) : Cr.Cir.Out},
  hpt: {W1s.pt(ws, m, q) == True{} : Bool}, +hdv: {Dv3(D.Am(m, q), q, m, W1s(ws, m), pu, done) == True{} : Bool},
  hch: {D.Chain(List.append(&2, U32, pu, Qr), W1s(ws, m), p3) == True{} : Bool}, hnd: {D.Nodup(pu) == True{} : Bool},
  hgq: {Gq(pu, P, Con{q, Qr}) == True{} : Bool}, hpp: {Pts(pu, m, q) == True{} : Bool},
  kont: Dk(f, B, R, q, m, nx, F, K, pg, L, I, P, Qr, Con{D.Fd(k, m, q), done}, Bud, Rq)) ->
  D.Ok(Cr.Cir.exec(1n+f, Cr.Cir.Stmt.seq{Mc.M.dec.part(k, bit), B}, Sr.X.st(Rd(R, p3, p4, p5, q, D.Am(m, q)), W1s(ws, m), nx, F, K, pg, L, I)), F, K, L, I, Bud, Rq):
  +am = D.Am(m, q)
  +M = W1s(ws, m)
  +x0 = D.Fd(k, m, q)
  +regs = Rd(R, p3, p4, p5, q, am)
  +regs4 = Sr.X.set(regs, 4n, x0)
  +st0 = Sr.X.st(regs, M, nx, F, K, pg, L, I)
  +st1 = Sr.X.st(regs4, M, nx, F, K, pg, L, I)
  +hsM = Equal.trans(Bool, D.Stc(M, x0), D.Stc(m, x0), True{}, stc.w1s(ws, m, x0), hs)
  +e2 = Sr.dec.eq.s(1n+f, regs4, M, nx, F, K, pg, L, I, 4n, x0, {==}, hz, hc, hsM)
  +e3 = Equal.cong(List<&2, U32>, Cr.Cir.State, rg => Sr.X.st(rg, M, nx, F, K, pg, L, I), regs4, Rd(R, p3, x0, p5, q, am), rd.z(R, p3, p4, p5, q, am, x0))
  +hx = K.Bo.or_ir(U32.is_zero(x0), Dv(m, M, pu, x0, D.Occ(Con{x0, done}, x0)),
    dv.s(m, M, pu, x0, D.Occ(done, x0), D.Occ(Con{x0, done}, x0), hs, hcur))
  dr.run(f, Mc.M.dec.part(k, bit), B, st0, st1, st1, Sr.X.st(Rd(R, p3, x0, p5, q, am), M, nx, F, K, pg, L, I), F, K, L, I, Bud, Rq, e1, e2, e3,
    kont(p3, x0, p5, ws, pu, hpt, dv3.step(am, q, m, M, M, pu, pu, done, x0, hdv, hx, +ne => {==}, +ne => {==}, +ne => {==}, +ne => {==},
      +ne => {==}, +ne => {==}), hch, hnd, hgq, hpp))

# the drop of a part whose count stays above 0
def dr.n(+f: Nat, +k: Nat, +bit: U32, +B: Cr.Cir.Stmt, +R: List<&2, U32>, +p3: U32, +p4: U32, +p5: U32, +q: U32, +m: Cr.Cir.Cells,
  +ws: List<&2, W1>, +nx: U32, +F: U32, +K: U32, +pg: U32, +L: U32, +I: List<&2, Word(8n)>, +P: List<&2, U32>, +Qr: List<&2, U32>,
  +zs: List<&2, D.Zs>, +pu: List<&2, U32>, +done: List<&2, U32>, -Bud: Nat, -Rq: List<&2, U32> -> Cr.Cir.Cells -> U32 -> U32 -> Type,
  +hz: {U32.is_eq(D.Fd(k, m, q), 0) == False{} : Bool}, +hc: {Cr.Cir.is_cell(D.Fd(k, m, q), K, F, nx) == True{} : Bool}, +hs: {D.Stc(m, D.Fd(k, m, q)) == False{} : Bool},
  +hd: {U32.is_eq(U32.sub(D.Fd(1n, W1s(ws, m), D.Fd(k, m, q)), 1), 0) == False{} : Bool}, +hcur: {Dv(m, W1s(ws, m), pu, D.Fd(k, m, q), D.Occ(done, D.Fd(k, m, q))) == True{} : Bool}, +hpf: {PtF(m, P, Con{q, Qr}, q, D.Fd(k, m, q)) == True{} : Bool}, +hbd: N.Le(1n+D.Occ(done, D.Fd(k, m, q)), D.Ow(m, q, D.Fd(k, m, q))), e1: {Cr.Cir.exec(1n+f, Mc.M.dec.part(k, bit), Sr.X.st(Rd(R, p3, p4, p5, q, D.Am(m, q)), W1s(ws, m), nx, F, K, pg, L, I)) == Cr.Cir.exec(1n+f, Mc.M.dec(4n), Sr.X.st(Sr.X.set(Rd(R, p3, p4, p5, q, D.Am(m, q)), 4n, D.Fd(k, m, q)), W1s(ws, m), nx, F, K, pg, L, I)) : Cr.Cir.Out},
  hpt: {W1s.pt(ws, m, q) == True{} : Bool}, +hdv: {Dv3(D.Am(m, q), q, m, W1s(ws, m), pu, done) == True{} : Bool},
  hch: {D.Chain(List.append(&2, U32, pu, Qr), W1s(ws, m), p3) == True{} : Bool}, hnd: {D.Nodup(pu) == True{} : Bool},
  hgq: {Gq(pu, P, Con{q, Qr}) == True{} : Bool}, hpp: {Pts(pu, m, q) == True{} : Bool},
  kont: Dk(f, B, R, q, m, nx, F, K, pg, L, I, P, Qr, Con{D.Fd(k, m, q), done}, Bud, Rq)) ->
  D.Ok(Cr.Cir.exec(1n+f, Cr.Cir.Stmt.seq{Mc.M.dec.part(k, bit), B}, Sr.X.st(Rd(R, p3, p4, p5, q, D.Am(m, q)), W1s(ws, m), nx, F, K, pg, L, I)), F, K, L, I, Bud, Rq):
  +am = D.Am(m, q)
  +M = W1s(ws, m)
  +x0 = D.Fd(k, m, q)
  +regs = Rd(R, p3, p4, p5, q, am)
  +regs4 = Sr.X.set(regs, 4n, x0)
  +st0 = Sr.X.st(regs, M, nx, F, K, pg, L, I)
  +st1 = Sr.X.st(regs4, M, nx, F, K, pg, L, I)
  +ow = D.Ow(m, q, x0)
  +c0 = U32.to_nat(D.Fd(1n, m, x0))
  +d = D.Occ(done, x0)
  +R3 = Bool.and(Bool.not(D.Has(Con{q, Qr}, x0)), Bool.or(D.Has(P, x0), Nat.is_lt(ow, c0)))
  +hle = N.toLe(ow, c0, K.Bo.and_l(Nat.is_le(ow, c0), R3, hpf))
  +hnq = K.Bo.not_t(D.Has(Con{q, Qr}, x0), K.Bo.and_l(Bool.not(D.Has(Con{q, Qr}, x0)), Bool.or(D.Has(P, x0), Nat.is_lt(ow, c0)),
    K.Bo.and_r(Nat.is_le(ow, c0), R3, hpf)))
  +hnqr = K.or.fr(U32.is_eq(q, x0), D.Has(Qr, x0), hnq)
  +hb = N.le_trans(1n+d, ow, c0, hbd, hle)
  +hp0 = dv.np(m, M, pu, x0, d, hs, hcur, hb)
  +ec = dv.ne(m, M, pu, x0, d, hs, hp0, hcur)
  +h1 = K.ar.pos(U32.to_nat(D.Fd(1n, M, x0)), d, c0, ec, hb)
  +dn = U32.sub(D.Fd(1n, M, x0), 1)
  +hsM = Equal.trans(Bool, D.Stc(M, x0), D.Stc(m, x0), False{}, stc.w1s(ws, m, x0), hs)
  +lt0 = K.Na.lt1i(0n, ow, N.le_trans(1n, 1n+d, ow, N.le_zero(d), hbd))
  +hnin = K.has.app.f(pu, Qr, x0, hp0, hnqr)
  +M2 = K.St1(M, x0, dn)
  +hx = K.Bo.or_ir(U32.is_zero(x0), Dv(m, M2, pu, x0, D.Occ(Con{x0, done}, x0)), dv.n(m, M, pu, x0, done, hs, hp0, ec, hd, h1))
  +hdv2 = dv3.step(am, q, m, M, M2, pu, pu, done, x0, hdv, hx,
    +ne => K.f1.st1.ne(M, x0, dn, D.Fd(2n, m, q), ne), +ne => {==}, +ne => K.f1.st1.ne(M, x0, dn, D.Fd(3n, m, q), ne), +ne => {==},
    +ne => K.f1.st1.ne(M, x0, dn, D.Fd(4n, m, q), ne), +ne => {==})
  +hpt2 = K.Bo.and_i(Nat.is_lt(0n, ow), W1s.pt(ws, m, q), lt0, hpt)
  +hch2 = K.chain.st1(List.append(&2, U32, pu, Qr), M, x0, dn, p3, hch, hnin)
  +e2 = Sr.dec.eq.n(1n+f, regs4, M, nx, F, K, pg, L, I, 4n, x0, {==}, {==}, hz, hc, hsM, hd, {==})
  +e3 = Equal.cong(List<&2, U32>, Cr.Cir.State, rg => Sr.X.st(rg, Sr.X.put(M, 1n, x0, dn), nx, F, K, pg, L, I), Sr.X.set(regs4, 5n, dn),
    Rd(R, p3, x0, dn, q, am), rd.n(R, p3, p4, p5, q, am, x0, dn))
  dr.run(f, Mc.M.dec.part(k, bit), B, st0, st1, Sr.X.st(Sr.X.set(regs4, 5n, dn), Sr.X.put(M, 1n, x0, dn), nx, F, K, pg, L, I),
    Sr.X.st(Rd(R, p3, x0, dn, q, am), W1s(Con{W1{x0, dn}, ws}, m), nx, F, K, pg, L, I), F, K, L, I, Bud, Rq, e1, e2, e3,
    kont(p3, x0, dn, Con{W1{x0, dn}, ws}, pu, hpt2, hdv2, hch2, hnd, hgq, hpp))

# the drop of a part whose count reaches 0: it goes to the pend list
def dr.p(+f: Nat, +k: Nat, +bit: U32, +B: Cr.Cir.Stmt, +R: List<&2, U32>, +p3: U32, +p4: U32, +p5: U32, +q: U32, +m: Cr.Cir.Cells,
  +ws: List<&2, W1>, +nx: U32, +F: U32, +K: U32, +pg: U32, +L: U32, +I: List<&2, Word(8n)>, +P: List<&2, U32>, +Qr: List<&2, U32>,
  +zs: List<&2, D.Zs>, +pu: List<&2, U32>, +done: List<&2, U32>, -Bud: Nat, -Rq: List<&2, U32> -> Cr.Cir.Cells -> U32 -> U32 -> Type,
  +hz: {U32.is_eq(D.Fd(k, m, q), 0) == False{} : Bool}, +hc: {Cr.Cir.is_cell(D.Fd(k, m, q), K, F, nx) == True{} : Bool}, +hs: {D.Stc(m, D.Fd(k, m, q)) == False{} : Bool},
  +hd: {U32.is_eq(U32.sub(D.Fd(1n, W1s(ws, m), D.Fd(k, m, q)), 1), 0) == True{} : Bool}, +hcur: {Dv(m, W1s(ws, m), pu, D.Fd(k, m, q), D.Occ(done, D.Fd(k, m, q))) == True{} : Bool}, +hpf: {PtF(m, P, Con{q, Qr}, q, D.Fd(k, m, q)) == True{} : Bool}, +hbd: N.Le(1n+D.Occ(done, D.Fd(k, m, q)), D.Ow(m, q, D.Fd(k, m, q))), e1: {Cr.Cir.exec(1n+f, Mc.M.dec.part(k, bit), Sr.X.st(Rd(R, p3, p4, p5, q, D.Am(m, q)), W1s(ws, m), nx, F, K, pg, L, I)) == Cr.Cir.exec(1n+f, Mc.M.dec(4n), Sr.X.st(Sr.X.set(Rd(R, p3, p4, p5, q, D.Am(m, q)), 4n, D.Fd(k, m, q)), W1s(ws, m), nx, F, K, pg, L, I)) : Cr.Cir.Out},
  hpt: {W1s.pt(ws, m, q) == True{} : Bool}, +hdv: {Dv3(D.Am(m, q), q, m, W1s(ws, m), pu, done) == True{} : Bool},
  hch: {D.Chain(List.append(&2, U32, pu, Qr), W1s(ws, m), p3) == True{} : Bool}, hnd: {D.Nodup(pu) == True{} : Bool},
  hgq: {Gq(pu, P, Con{q, Qr}) == True{} : Bool}, hpp: {Pts(pu, m, q) == True{} : Bool},
  kont: Dk(f, B, R, q, m, nx, F, K, pg, L, I, P, Qr, Con{D.Fd(k, m, q), done}, Bud, Rq)) ->
  D.Ok(Cr.Cir.exec(1n+f, Cr.Cir.Stmt.seq{Mc.M.dec.part(k, bit), B}, Sr.X.st(Rd(R, p3, p4, p5, q, D.Am(m, q)), W1s(ws, m), nx, F, K, pg, L, I)), F, K, L, I, Bud, Rq):
  +am = D.Am(m, q)
  +M = W1s(ws, m)
  +x0 = D.Fd(k, m, q)
  +regs = Rd(R, p3, p4, p5, q, am)
  +regs4 = Sr.X.set(regs, 4n, x0)
  +st0 = Sr.X.st(regs, M, nx, F, K, pg, L, I)
  +st1 = Sr.X.st(regs4, M, nx, F, K, pg, L, I)
  +ow = D.Ow(m, q, x0)
  +c0 = U32.to_nat(D.Fd(1n, m, x0))
  +d = D.Occ(done, x0)
  +R3 = Bool.and(Bool.not(D.Has(Con{q, Qr}, x0)), Bool.or(D.Has(P, x0), Nat.is_lt(ow, c0)))
  +hle = N.toLe(ow, c0, K.Bo.and_l(Nat.is_le(ow, c0), R3, hpf))
  +hnq = K.Bo.not_t(D.Has(Con{q, Qr}, x0), K.Bo.and_l(Bool.not(D.Has(Con{q, Qr}, x0)), Bool.or(D.Has(P, x0), Nat.is_lt(ow, c0)),
    K.Bo.and_r(Nat.is_le(ow, c0), R3, hpf)))
  +hnqr = K.or.fr(U32.is_eq(q, x0), D.Has(Qr, x0), hnq)
  +hb = N.le_trans(1n+d, ow, c0, hbd, hle)
  +hp0 = dv.np(m, M, pu, x0, d, hs, hcur, hb)
  +ec = dv.ne(m, M, pu, x0, d, hs, hp0, hcur)
  +h1 = K.ar.pos(U32.to_nat(D.Fd(1n, M, x0)), d, c0, ec, hb)
  +dn = U32.sub(D.Fd(1n, M, x0), 1)
  +hsM = Equal.trans(Bool, D.Stc(M, x0), D.Stc(m, x0), False{}, stc.w1s(ws, m, x0), hs)
  +lt0 = K.Na.lt1i(0n, ow, N.le_trans(1n, 1n+d, ow, N.le_zero(d), hbd))
  +hnin = K.has.app.f(pu, Qr, x0, hp0, hnqr)
  +M2 = K.St1(M, x0, dn)
  +M3 = K.St1(M2, x0, p3)
  +E = p.c0(M, x0, d, c0, ec, hd, h1)
  +hlt = na.nlt(Nat.is_lt(ow, c0), ow, c0, {==}, (%E : N.Le(_, ow); hbd))
  +hinP = K.Bo.or_l(D.Has(P, x0), Nat.is_lt(ow, c0), K.Bo.and_r(Bool.not(D.Has(Con{q, Qr}, x0)), Bool.or(D.Has(P, x0), Nat.is_lt(ow, c0)),
    K.Bo.and_r(Nat.is_le(ow, c0), R3, hpf)), hlt)
  +hx = K.Bo.or_ir(U32.is_zero(x0), Dv(m, M3, Con{x0, pu}, x0, D.Occ(Con{x0, done}, x0)), dv.p(m, M, pu, x0, p3, done, hs, E))
  +hdv2 = dv3.step(am, q, m, M, M3, pu, Con{x0, pu}, done, x0, hdv, hx,
    +ne => Equal.trans(U32, D.Fd(1n, M3, D.Fd(2n, m, q)), D.Fd(1n, M2, D.Fd(2n, m, q)), D.Fd(1n, M, D.Fd(2n, m, q)),
      K.f1.st1.ne(M2, x0, p3, D.Fd(2n, m, q), ne), K.f1.st1.ne(M, x0, dn, D.Fd(2n, m, q), ne)),
    +ne => hpu.push(pu, x0, D.Fd(2n, m, q), ne),
    +ne => Equal.trans(U32, D.Fd(1n, M3, D.Fd(3n, m, q)), D.Fd(1n, M2, D.Fd(3n, m, q)), D.Fd(1n, M, D.Fd(3n, m, q)),
      K.f1.st1.ne(M2, x0, p3, D.Fd(3n, m, q), ne), K.f1.st1.ne(M, x0, dn, D.Fd(3n, m, q), ne)),
    +ne => hpu.push(pu, x0, D.Fd(3n, m, q), ne),
    +ne => Equal.trans(U32, D.Fd(1n, M3, D.Fd(4n, m, q)), D.Fd(1n, M2, D.Fd(4n, m, q)), D.Fd(1n, M, D.Fd(4n, m, q)),
      K.f1.st1.ne(M2, x0, p3, D.Fd(4n, m, q), ne), K.f1.st1.ne(M, x0, dn, D.Fd(4n, m, q), ne)),
    +ne => hpu.push(pu, x0, D.Fd(4n, m, q), ne))
  +hpt2 = K.Bo.and_i(Nat.is_lt(0n, ow), Bool.and(Nat.is_lt(0n, ow), W1s.pt(ws, m, q)), lt0, K.Bo.and_i(Nat.is_lt(0n, ow), W1s.pt(ws, m, q), lt0, hpt))
  +AP = List.append(&2, U32, pu, Qr)
  +chM3 = K.chain.st1(AP, M2, x0, p3, p3, K.chain.st1(AP, M, x0, dn, p3, hch, hnin), hnin)
  +hch2 = K.Bo.and_i(U32.is_eq(x0, x0), Bool.and(Bool.not(U32.is_zero(x0)), D.Chain(AP, M3, D.Fd(1n, M3, x0))), K.U.eq_refl(x0),
    K.Bo.and_i(Bool.not(U32.is_zero(x0)), D.Chain(AP, M3, D.Fd(1n, M3, x0)), K.Bo.not_i(U32.is_zero(x0), hz),
      (%Equal.sym(U32, D.Fd(1n, M3, x0), p3, K.f1.st1(M2, x0, p3)) : {D.Chain(AP, M3, _) == True{} : Bool}; chM3)))
  +hnd2 = K.Bo.and_i(Bool.not(D.Has(pu, x0)), D.Nodup(pu), K.Bo.not_i(D.Has(pu, x0), hp0), hnd)
  +hgq2 = K.Bo.and_i(Bool.and(D.Has(P, x0), Bool.not(D.Has(Con{q, Qr}, x0))), Gq(pu, P, Con{q, Qr}),
    K.Bo.and_i(D.Has(P, x0), Bool.not(D.Has(Con{q, Qr}, x0)), hinP, K.Bo.not_i(D.Has(Con{q, Qr}, x0), hnq)), hgq)
  +e2 = Sr.dec.eq.p(1n+f, regs4, M, nx, F, K, pg, L, I, 4n, x0, p3, {==}, {==}, {==}, hz, hc, hsM, hd, {==})
  +e3 = Equal.cong(List<&2, U32>, Cr.Cir.State, rg => Sr.X.st(rg, Sr.X.put(Sr.X.put(M, 1n, x0, dn), 1n, x0, p3), nx, F, K, pg, L, I),
    Sr.X.set(Sr.X.set(regs4, 5n, dn), 3n, x0), Rd(R, x0, x0, dn, q, am), rd.p(R, p3, p4, p5, q, am, x0, dn))
  dr.run(f, Mc.M.dec.part(k, bit), B, st0, st1, Sr.X.st(Sr.X.set(Sr.X.set(regs4, 5n, dn), 3n, x0), Sr.X.put(Sr.X.put(M, 1n, x0, dn), 1n, x0, p3),
    nx, F, K, pg, L, I), Sr.X.st(Rd(R, x0, x0, dn, q, am), W1s(Con{W1{x0, p3}, Con{W1{x0, dn}, ws}}, m), nx, F, K, pg, L, I),
    F, K, L, I, Bud, Rq, e1, e2, e3,
    kont(x0, x0, dn, Con{W1{x0, p3}, Con{W1{x0, dn}, ws}}, Con{x0, pu}, hpt2, hdv2, hch2, hnd2, hgq2,
      K.Bo.and_i(Nat.is_lt(0n, ow), Pts(pu, m, q), lt0, hpp)))

# a drop of a part neither 0 nor STATIC, by whether its count reaches 0
def dr.ns(b: Bool, +f: Nat, +k: Nat, +bit: U32, +B: Cr.Cir.Stmt, +R: List<&2, U32>, +p3: U32, +p4: U32, +p5: U32, +q: U32, +m: Cr.Cir.Cells,
  +ws: List<&2, W1>, +nx: U32, +F: U32, +K: U32, +pg: U32, +L: U32, +I: List<&2, Word(8n)>, +P: List<&2, U32>, +Qr: List<&2, U32>,
  +zs: List<&2, D.Zs>, +pu: List<&2, U32>, +done: List<&2, U32>, -Bud: Nat, -Rq: List<&2, U32> -> Cr.Cir.Cells -> U32 -> U32 -> Type,
  eb: {U32.is_eq(U32.sub(D.Fd(1n, W1s(ws, m), D.Fd(k, m, q)), 1), 0) == b : Bool}, +hz: {U32.is_eq(D.Fd(k, m, q), 0) == False{} : Bool}, +hc: {Cr.Cir.is_cell(D.Fd(k, m, q), K, F, nx) == True{} : Bool}, +hs: {D.Stc(m, D.Fd(k, m, q)) == False{} : Bool},
  +hcur: {Dv(m, W1s(ws, m), pu, D.Fd(k, m, q), D.Occ(done, D.Fd(k, m, q))) == True{} : Bool}, +hpf: {PtF(m, P, Con{q, Qr}, q, D.Fd(k, m, q)) == True{} : Bool}, +hbd: N.Le(1n+D.Occ(done, D.Fd(k, m, q)), D.Ow(m, q, D.Fd(k, m, q))), e1: {Cr.Cir.exec(1n+f, Mc.M.dec.part(k, bit), Sr.X.st(Rd(R, p3, p4, p5, q, D.Am(m, q)), W1s(ws, m), nx, F, K, pg, L, I)) == Cr.Cir.exec(1n+f, Mc.M.dec(4n), Sr.X.st(Sr.X.set(Rd(R, p3, p4, p5, q, D.Am(m, q)), 4n, D.Fd(k, m, q)), W1s(ws, m), nx, F, K, pg, L, I)) : Cr.Cir.Out},
  hpt: {W1s.pt(ws, m, q) == True{} : Bool}, +hdv: {Dv3(D.Am(m, q), q, m, W1s(ws, m), pu, done) == True{} : Bool},
  hch: {D.Chain(List.append(&2, U32, pu, Qr), W1s(ws, m), p3) == True{} : Bool}, hnd: {D.Nodup(pu) == True{} : Bool},
  hgq: {Gq(pu, P, Con{q, Qr}) == True{} : Bool}, hpp: {Pts(pu, m, q) == True{} : Bool},
  kont: Dk(f, B, R, q, m, nx, F, K, pg, L, I, P, Qr, Con{D.Fd(k, m, q), done}, Bud, Rq)) ->
  D.Ok(Cr.Cir.exec(1n+f, Cr.Cir.Stmt.seq{Mc.M.dec.part(k, bit), B}, Sr.X.st(Rd(R, p3, p4, p5, q, D.Am(m, q)), W1s(ws, m), nx, F, K, pg, L, I)), F, K, L, I, Bud, Rq):
  match b:
    case False{}:
      dr.n(f, k, bit, B, R, p3, p4, p5, q, m, ws, nx, F, K, pg, L, I, P, Qr, zs, pu, done, Bud, Rq, hz, hc, hs, eb, hcur, hpf, hbd, e1, hpt, hdv, hch, hnd, hgq, hpp, kont)
    case True{}:
      dr.p(f, k, bit, B, R, p3, p4, p5, q, m, ws, nx, F, K, pg, L, I, P, Qr, zs, pu, done, Bud, Rq, hz, hc, hs, eb, hcur, hpf, hbd, e1, hpt, hdv, hch, hnd, hgq, hpp, kont)

# a drop of a part that is not 0, by whether it is STATIC
def dr.nz(s: Bool, +f: Nat, +k: Nat, +bit: U32, +B: Cr.Cir.Stmt, +R: List<&2, U32>, +p3: U32, +p4: U32, +p5: U32, +q: U32, +m: Cr.Cir.Cells,
  +ws: List<&2, W1>, +nx: U32, +F: U32, +K: U32, +pg: U32, +L: U32, +I: List<&2, Word(8n)>, +P: List<&2, U32>, +Qr: List<&2, U32>,
  +zs: List<&2, D.Zs>, +pu: List<&2, U32>, +done: List<&2, U32>, -Bud: Nat, -Rq: List<&2, U32> -> Cr.Cir.Cells -> U32 -> U32 -> Type,
  +es: {D.Stc(m, D.Fd(k, m, q)) == s : Bool}, +hon: {U32.is_zero(U32.and(D.Am(m, q), bit)) == False{} : Bool}, +hz: {U32.is_eq(D.Fd(k, m, q), 0) == False{} : Bool}, +hc: {Cr.Cir.is_cell(D.Fd(k, m, q), K, F, nx) == True{} : Bool},
  +hcur: {Dv(m, W1s(ws, m), pu, D.Fd(k, m, q), D.Occ(done, D.Fd(k, m, q))) == True{} : Bool}, +hpart: {D.AL.part(m, P, zs, D.Zz(zs, q), D.Am(m, q), bit, D.Fd(k, m, q), K, F, nx) == True{} : Bool}, +hq: {D.Has(P, q) == True{} : Bool}, +hsub: {D.Sub(Con{q, Qr}, P) == True{} : Bool},
  +hcs: {D.AL.cells(P, m, P, Con{q, Qr}, zs, K, F, nx) == True{} : Bool}, +hbd: N.Le(1n+D.Occ(done, D.Fd(k, m, q)), D.Ow(m, q, D.Fd(k, m, q))), e1: {Cr.Cir.exec(1n+f, Mc.M.dec.part(k, bit), Sr.X.st(Rd(R, p3, p4, p5, q, D.Am(m, q)), W1s(ws, m), nx, F, K, pg, L, I)) == Cr.Cir.exec(1n+f, Mc.M.dec(4n), Sr.X.st(Sr.X.set(Rd(R, p3, p4, p5, q, D.Am(m, q)), 4n, D.Fd(k, m, q)), W1s(ws, m), nx, F, K, pg, L, I)) : Cr.Cir.Out},
  hpt: {W1s.pt(ws, m, q) == True{} : Bool}, +hdv: {Dv3(D.Am(m, q), q, m, W1s(ws, m), pu, done) == True{} : Bool},
  hch: {D.Chain(List.append(&2, U32, pu, Qr), W1s(ws, m), p3) == True{} : Bool}, hnd: {D.Nodup(pu) == True{} : Bool},
  hgq: {Gq(pu, P, Con{q, Qr}) == True{} : Bool}, hpp: {Pts(pu, m, q) == True{} : Bool},
  kont: Dk(f, B, R, q, m, nx, F, K, pg, L, I, P, Qr, Con{D.Fd(k, m, q), done}, Bud, Rq)) ->
  D.Ok(Cr.Cir.exec(1n+f, Cr.Cir.Stmt.seq{Mc.M.dec.part(k, bit), B}, Sr.X.st(Rd(R, p3, p4, p5, q, D.Am(m, q)), W1s(ws, m), nx, F, K, pg, L, I)), F, K, L, I, Bud, Rq):
  match s:
    case True{}:
      dr.s(f, k, bit, B, R, p3, p4, p5, q, m, ws, nx, F, K, pg, L, I, P, Qr, zs, pu, done, Bud, Rq, hz, hc, es, hcur, e1, hpt, hdv, hch, hnd, hgq, hpp, kont)
    case False{}:
      +x0 = D.Fd(k, m, q)
      +hb1 = N.le_trans(1n, 1n+D.Occ(done, x0), D.Ow(m, q, x0), N.le_zero(D.Occ(done, x0)), hbd)
      +hpf = pt.fx(m, P, Con{q, Qr}, zs, q, D.Am(m, q), bit, x0, K, F, nx, hpart, hon, hz, es, hq, hsub, hcs, hb1)
      dr.ns(U32.is_eq(U32.sub(D.Fd(1n, W1s(ws, m), x0), 1), 0), f, k, bit, B, R, p3, p4, p5, q, m, ws, nx, F, K, pg, L, I, P, Qr, zs, pu, done, Bud, Rq, {==}, hz, hc, es, hcur, hpf, hbd, e1, hpt, hdv, hch, hnd, hgq, hpp, kont)

# a drop of a part, by whether it is 0
def dr.on(z: Bool, +f: Nat, +k: Nat, +bit: U32, +B: Cr.Cir.Stmt, +R: List<&2, U32>, +p3: U32, +p4: U32, +p5: U32, +q: U32, +m: Cr.Cir.Cells,
  +ws: List<&2, W1>, +nx: U32, +F: U32, +K: U32, +pg: U32, +L: U32, +I: List<&2, Word(8n)>, +P: List<&2, U32>, +Qr: List<&2, U32>,
  +zs: List<&2, D.Zs>, +pu: List<&2, U32>, +done: List<&2, U32>, -Bud: Nat, -Rq: List<&2, U32> -> Cr.Cir.Cells -> U32 -> U32 -> Type,
  +ez: {U32.is_eq(D.Fd(k, m, q), 0) == z : Bool}, +hon: {U32.is_zero(U32.and(D.Am(m, q), bit)) == False{} : Bool},
  +hcur: {Bool.or(U32.is_zero(D.Fd(k, m, q)), Dv(m, W1s(ws, m), pu, D.Fd(k, m, q), D.Occ(done, D.Fd(k, m, q)))) == True{} : Bool},
  +hpart: {D.AL.part(m, P, zs, D.Zz(zs, q), D.Am(m, q), bit, D.Fd(k, m, q), K, F, nx) == True{} : Bool}, +hq: {D.Has(P, q) == True{} : Bool}, +hsub: {D.Sub(Con{q, Qr}, P) == True{} : Bool},
  +hcs: {D.AL.cells(P, m, P, Con{q, Qr}, zs, K, F, nx) == True{} : Bool}, +hbd: N.Le(1n+D.Occ(done, D.Fd(k, m, q)), D.Ow(m, q, D.Fd(k, m, q))), e1: {Cr.Cir.exec(1n+f, Mc.M.dec.part(k, bit), Sr.X.st(Rd(R, p3, p4, p5, q, D.Am(m, q)), W1s(ws, m), nx, F, K, pg, L, I)) == Cr.Cir.exec(1n+f, Mc.M.dec(4n), Sr.X.st(Sr.X.set(Rd(R, p3, p4, p5, q, D.Am(m, q)), 4n, D.Fd(k, m, q)), W1s(ws, m), nx, F, K, pg, L, I)) : Cr.Cir.Out},
  hpt: {W1s.pt(ws, m, q) == True{} : Bool}, +hdv: {Dv3(D.Am(m, q), q, m, W1s(ws, m), pu, done) == True{} : Bool},
  hch: {D.Chain(List.append(&2, U32, pu, Qr), W1s(ws, m), p3) == True{} : Bool}, hnd: {D.Nodup(pu) == True{} : Bool},
  hgq: {Gq(pu, P, Con{q, Qr}) == True{} : Bool}, hpp: {Pts(pu, m, q) == True{} : Bool},
  kont: Dk(f, B, R, q, m, nx, F, K, pg, L, I, P, Qr, Con{D.Fd(k, m, q), done}, Bud, Rq)) ->
  D.Ok(Cr.Cir.exec(1n+f, Cr.Cir.Stmt.seq{Mc.M.dec.part(k, bit), B}, Sr.X.st(Rd(R, p3, p4, p5, q, D.Am(m, q)), W1s(ws, m), nx, F, K, pg, L, I)), F, K, L, I, Bud, Rq):
  match z:
    case True{}:
      dr.z(f, k, bit, B, R, p3, p4, p5, q, m, ws, nx, F, K, pg, L, I, P, Qr, zs, pu, done, Bud, Rq, ez, e1, hpt, hdv, hch, hnd, hgq, hpp, kont)
    case False{}:
      +x0 = D.Fd(k, m, q)
      +hc = pt.cell(m, P, zs, D.Zz(zs, q), D.Am(m, q), bit, x0, K, F, nx, hpart, hon, ez)
      +hv = K.Bo.or_r(U32.is_zero(x0), Dv(m, W1s(ws, m), pu, x0, D.Occ(done, x0)), hcur, ez)
      dr.nz(D.Stc(m, x0), f, k, bit, B, R, p3, p4, p5, q, m, ws, nx, F, K, pg, L, I, P, Qr, zs, pu, done, Bud, Rq, {==}, hon, ez, hc, hv, hpart, hq, hsub, hcs, hbd, e1, hpt, hdv, hch, hnd, hgq, hpp, kont)

# the drop of the part in field k of q, by the bit of its mask
def dr.step.b(b: Bool, +f: Nat, +k: Nat, +bit: U32, +B: Cr.Cir.Stmt, +R: List<&2, U32>, +p3: U32, +p4: U32, +p5: U32, +q: U32, +m: Cr.Cir.Cells,
  +ws: List<&2, W1>, +nx: U32, +F: U32, +K: U32, +pg: U32, +L: U32, +I: List<&2, Word(8n)>, +P: List<&2, U32>, +Qr: List<&2, U32>,
  +zs: List<&2, D.Zs>, +pu: List<&2, U32>, +done: List<&2, U32>, -Bud: Nat, -Rq: List<&2, U32> -> Cr.Cir.Cells -> U32 -> U32 -> Type,
  eb: {U32.is_ne(U32.and(D.Am(m, q), bit), 0) == b : Bool}, +hk: {Nat.is_eq(k, 1n) == False{} : Bool},
  +hqc: {Cr.Cir.is_cell(q, K, F, nx) == True{} : Bool},
  +hcur: {Bool.or(Bool.not(b), Bool.or(U32.is_zero(D.Fd(k, m, q)), Dv(m, W1s(ws, m), pu, D.Fd(k, m, q), D.Occ(done, D.Fd(k, m, q))))) == True{} : Bool},
  +hpart: {D.AL.part(m, P, zs, D.Zz(zs, q), D.Am(m, q), bit, D.Fd(k, m, q), K, F, nx) == True{} : Bool}, +hq: {D.Has(P, q) == True{} : Bool}, +hsub: {D.Sub(Con{q, Qr}, P) == True{} : Bool},
  +hcs: {D.AL.cells(P, m, P, Con{q, Qr}, zs, K, F, nx) == True{} : Bool},
  +hbd: {Bool.or(Bool.not(b), Nat.is_le(1n+D.Occ(done, D.Fd(k, m, q)), D.Ow(m, q, D.Fd(k, m, q)))) == True{} : Bool},
  hpt: {W1s.pt(ws, m, q) == True{} : Bool}, +hdv: {Dv3(D.Am(m, q), q, m, W1s(ws, m), pu, done) == True{} : Bool},
  hch: {D.Chain(List.append(&2, U32, pu, Qr), W1s(ws, m), p3) == True{} : Bool}, hnd: {D.Nodup(pu) == True{} : Bool},
  hgq: {Gq(pu, P, Con{q, Qr}) == True{} : Bool}, hpp: {Pts(pu, m, q) == True{} : Bool},
  kont: Dk(f, B, R, q, m, nx, F, K, pg, L, I, P, Qr, D.Ps.opt(b, D.Fd(k, m, q), done), Bud, Rq)) ->
  D.Ok(Cr.Cir.exec(1n+f, Cr.Cir.Stmt.seq{Mc.M.dec.part(k, bit), B}, Sr.X.st(Rd(R, p3, p4, p5, q, D.Am(m, q)), W1s(ws, m), nx, F, K, pg, L, I)), F, K, L, I, Bud, Rq):
  match b:
    case False{}:
      +am = D.Am(m, q)
      +M = W1s(ws, m)
      +x0 = D.Fd(k, m, q)
      +regs = Rd(R, p3, p4, p5, q, am)
      +regs4 = Sr.X.set(regs, 4n, x0)
      +st0 = Sr.X.st(regs, M, nx, F, K, pg, L, I)
      +st1 = Sr.X.st(regs4, M, nx, F, K, pg, L, I)

      +hb = K.Bo.not_f(U32.is_eq(U32.and(am, bit), 0), eb)
      +e1 = Sr.dec.part.off(1n+f, regs, M, nx, F, K, pg, L, I, k, bit, am, {==}, hb)
      K.Ok.eq(Cr.Cir.exec(1n+f, Cr.Cir.Stmt.seq{Mc.M.dec.part(k, bit), B}, st0), Cr.Cir.exec(1n+f, B, st0), F, K, L, I, Bud, Rq,
        Equal.sym(Cr.Cir.Out, Cr.Cir.exec(1n+f, Cr.Cir.Stmt.seq{Mc.M.dec.part(k, bit), B}, st0), Cr.Cir.exec(1n+f, B, st0),
          K.X.seq(f, Mc.M.dec.part(k, bit), B, st0, st0,
            Equal.sym(Cr.Cir.Out, Cr.Cir.exec(1n+f, Mc.M.dec.part(k, bit), st0), Cr.Cir.Out.next{st0}, e1))),
        kont(p3, p4, p5, ws, pu, hpt, hdv, hch, hnd, hgq, hpp))
    case True{}:
      +am = D.Am(m, q)
      +M = W1s(ws, m)
      +x0 = D.Fd(k, m, q)
      +regs = Rd(R, p3, p4, p5, q, am)
      +regs4 = Sr.X.set(regs, 4n, x0)
      +st0 = Sr.X.st(regs, M, nx, F, K, pg, L, I)
      +st1 = Sr.X.st(regs4, M, nx, F, K, pg, L, I)

      +hb = K.Bo.not_t(U32.is_eq(U32.and(am, bit), 0), eb)
      +e1a = Sr.dec.part.on(1n+f, regs, M, nx, F, K, pg, L, I, k, bit, am, q, {==}, {==}, {==}, hb, hqc)
      +e1 = {(%fd.w1s(ws, m, k, hk, q) : {Cr.Cir.exec(1n+f, Mc.M.dec.part(k, bit), st0) ==
          Cr.Cir.exec(1n+f, Mc.M.dec(4n), Sr.X.st(Sr.X.set(regs, 4n, _), M, nx, F, K, pg, L, I)) : Cr.Cir.Out}; e1a) : {Cr.Cir.exec(1n+f, Mc.M.dec.part(k, bit), Sr.X.st(Rd(R, p3, p4, p5, q, D.Am(m, q)), W1s(ws, m), nx, F, K, pg, L, I)) == Cr.Cir.exec(1n+f, Mc.M.dec(4n), Sr.X.st(Sr.X.set(Rd(R, p3, p4, p5, q, D.Am(m, q)), 4n, D.Fd(k, m, q)), W1s(ws, m), nx, F, K, pg, L, I)) : Cr.Cir.Out}}
      dr.on(U32.is_eq(x0, 0), f, k, bit, B, R, p3, p4, p5, q, m, ws, nx, F, K, pg, L, I, P, Qr, zs, pu, done, Bud, Rq, {==}, hb, hcur, hpart, hq, hsub, hcs, N.toLe(1n+D.Occ(done, x0), D.Ow(m, q, x0), hbd), e1, hpt, hdv, hch, hnd, hgq, hpp, kont)

def dr.step(+f: Nat, +k: Nat, +bit: U32, +B: Cr.Cir.Stmt, +R: List<&2, U32>, +p3: U32, +p4: U32, +p5: U32, +q: U32, +m: Cr.Cir.Cells,
  +ws: List<&2, W1>, +nx: U32, +F: U32, +K: U32, +pg: U32, +L: U32, +I: List<&2, Word(8n)>, +P: List<&2, U32>, +Qr: List<&2, U32>,
  +zs: List<&2, D.Zs>, +pu: List<&2, U32>, +done: List<&2, U32>, -Bud: Nat, -Rq: List<&2, U32> -> Cr.Cir.Cells -> U32 -> U32 -> Type,
  +hk: {Nat.is_eq(k, 1n) == False{} : Bool}, +hqc: {Cr.Cir.is_cell(q, K, F, nx) == True{} : Bool},
  +hcur: {Dvm(U32.is_ne(U32.and(D.Am(m, q), bit), 0), D.Fd(k, m, q), m, W1s(ws, m), pu, done) == True{} : Bool},
  +hpart: {D.AL.part(m, P, zs, D.Zz(zs, q), D.Am(m, q), bit, D.Fd(k, m, q), K, F, nx) == True{} : Bool}, +hq: {D.Has(P, q) == True{} : Bool}, +hsub: {D.Sub(Con{q, Qr}, P) == True{} : Bool},
  +hcs: {D.AL.cells(P, m, P, Con{q, Qr}, zs, K, F, nx) == True{} : Bool},
  +hbd: {Bool.or(Bool.not(U32.is_ne(U32.and(D.Am(m, q), bit), 0)), Nat.is_le(1n+D.Occ(done, D.Fd(k, m, q)), D.Ow(m, q, D.Fd(k, m, q)))) == True{} : Bool},
  hpt: {W1s.pt(ws, m, q) == True{} : Bool}, +hdv: {Dv3(D.Am(m, q), q, m, W1s(ws, m), pu, done) == True{} : Bool},
  hch: {D.Chain(List.append(&2, U32, pu, Qr), W1s(ws, m), p3) == True{} : Bool}, hnd: {D.Nodup(pu) == True{} : Bool},
  hgq: {Gq(pu, P, Con{q, Qr}) == True{} : Bool}, hpp: {Pts(pu, m, q) == True{} : Bool},
  kont: Dk(f, B, R, q, m, nx, F, K, pg, L, I, P, Qr, D.Ps.opt(U32.is_ne(U32.and(D.Am(m, q), bit), 0), D.Fd(k, m, q), done), Bud, Rq)) ->
  D.Ok(Cr.Cir.exec(1n+f, Cr.Cir.Stmt.seq{Mc.M.dec.part(k, bit), B}, Sr.X.st(Rd(R, p3, p4, p5, q, D.Am(m, q)), W1s(ws, m), nx, F, K, pg, L, I)), F, K, L, I, Bud, Rq):
  dr.step.b(U32.is_ne(U32.and(D.Am(m, q), bit), 0), f, k, bit, B, R, p3, p4, p5, q, m, ws, nx, F, K, pg, L, I, P, Qr, zs, pu, done, Bud, Rq, {==}, hk, hqc, hcur, hpart, hq, hsub, hcs, hbd, hpt, hdv, hch, hnd, hgq, hpp, kont)

# The three drops
# ---------------

# Ow of a cell q by its mask's bits and parts
def OwE(+b1: Bool, +b2: Bool, +b4: Bool, +f2: U32, +f3: U32, +f4: U32, +c: U32) -> Nat:
  Nat.add(D.Nat.of(Bool.and(b1, U32.is_eq(f2, c))), Nat.add(D.Nat.of(Bool.and(b2, U32.is_eq(f3, c))), D.Nat.of(Bool.and(b4, U32.is_eq(f4, c)))))

# the parts that the three drops did
def Dn3(+m: Cr.Cir.Cells, +q: U32) -> List<&2, U32>:
  +a = D.Am(m, q)
  D.Ps.opt(U32.is_ne(U32.and(a, 4), 0), D.Fd(4n, m, q), D.Ps.opt(U32.is_ne(U32.and(a, 2), 0), D.Fd(3n, m, q),
    D.Ps.opt(U32.is_ne(U32.and(a, 1), 0), D.Fd(2n, m, q), Nil{})))

def occ.opt(b: Bool, +v: U32, +r: List<&2, U32>, +y: U32) ->
  {D.Occ(D.Ps.opt(b, v, r), y) == Nat.add(D.Nat.of(Bool.and(b, U32.is_eq(v, y))), D.Occ(r, y)) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def Na.comm(a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, N.add_zero(b))
    case 1n+(+p):
      Equal.trans(Nat, 1n+Nat.add(p, b), 1n+Nat.add(b, p), Nat.add(b, 1n+p), Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, b), Nat.add(b, p), Na.comm(p, b)),
        Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), N.add_succ_r(b, p)))

def ar3(+A: Nat, +C: Nat) -> N.Le(1n+Nat.add(A, 0n), Nat.add(A, 1n+C)):
  N.le_rw_r(1n+Nat.add(A, 0n), 1n+Nat.add(A, C), Nat.add(A, 1n+C), Equal.sym(Nat, Nat.add(A, 1n+C), 1n+Nat.add(A, C), N.add_succ_r(A, C)),
    N.le_rw_l(A, Nat.add(A, 0n), Nat.add(A, C), Equal.sym(Nat, Nat.add(A, 0n), A, N.add_zero(A)), N.le_add_r(A, C)))

def ar4(+A: Nat, +B: Nat) -> N.Le(1n+Nat.add(B, Nat.add(A, 0n)), Nat.add(A, Nat.add(B, 1n))):
  +L0 = {1n+Nat.add(B, Nat.add(A, 0n)) : Nat}
  +E = Equal.trans(Nat, Nat.add(A, Nat.add(B, 1n)), Nat.add(B, Nat.add(A, 1n)), L0, N.add_swap(A, B, 1n),
    Equal.trans(Nat, Nat.add(B, Nat.add(A, 1n)), Nat.add(B, 1n+Nat.add(A, 0n)), L0,
      Equal.cong(Nat, Nat, z => Nat.add(B, z), Nat.add(A, 1n), 1n+Nat.add(A, 0n), N.add_succ_r(A, 0n)), N.add_succ_r(B, Nat.add(A, 0n))))
  N.le_rw_r(L0, L0, Nat.add(A, Nat.add(B, 1n)), Equal.sym(Nat, Nat.add(A, Nat.add(B, 1n)), L0, E), N.le_refl(L0))

# before each drop, the drops done are fewer than q's pointers to the part
def bk2.of(b1: Bool, +b2: Bool, +b4: Bool, +f2: U32, +f3: U32, +f4: U32) ->
  {Bool.or(Bool.not(b1), Nat.is_le(1n+D.Occ(Nil{}, f2), OwE(b1, b2, b4, f2, f3, f4, f2))) == True{} : Bool}:
  match b1:
    case False{}:
      {==}
    case True{}:
      +RE = Nat.add(D.Nat.of(Bool.and(b2, U32.is_eq(f3, f2))), D.Nat.of(Bool.and(b4, U32.is_eq(f4, f2))))
      %Equal.sym(Bool, U32.is_eq(f2, f2), True{}, K.U.eq_refl(f2)) : {Nat.is_le(1n, Nat.add(D.Nat.of(_), RE)) == True{} : Bool}
      K.Na.le0(RE)

def bk3.of(+b1: Bool, b2: Bool, +b4: Bool, +f2: U32, +f3: U32, +f4: U32) ->
  {Bool.or(Bool.not(b2), Nat.is_le(1n+D.Occ(D.Ps.opt(b1, f2, Nil{}), f3), OwE(b1, b2, b4, f2, f3, f4, f3))) == True{} : Bool}:
  match b2:
    case False{}:
      {==}
    case True{}:
      +A = D.Nat.of(Bool.and(b1, U32.is_eq(f2, f3)))
      +C = D.Nat.of(Bool.and(b4, U32.is_eq(f4, f3)))
      %Equal.sym(Nat, D.Occ(D.Ps.opt(b1, f2, Nil{}), f3), Nat.add(A, 0n), occ.opt(b1, f2, Nil{}, f3)) :
        {Nat.is_le(1n+_, Nat.add(A, Nat.add(D.Nat.of(Bool.and(True{}, U32.is_eq(f3, f3))), C))) == True{} : Bool}
      %Equal.sym(Bool, U32.is_eq(f3, f3), True{}, K.U.eq_refl(f3)) : {Nat.is_le(1n+Nat.add(A, 0n), Nat.add(A, Nat.add(D.Nat.of(_), C))) == True{} : Bool}
      K.ofT(Nat.is_le(1n+Nat.add(A, 0n), Nat.add(A, 1n+C)), ar3(A, C))

def bk4.of(+b1: Bool, +b2: Bool, b4: Bool, +f2: U32, +f3: U32, +f4: U32) ->
  {Bool.or(Bool.not(b4), Nat.is_le(1n+D.Occ(D.Ps.opt(b2, f3, D.Ps.opt(b1, f2, Nil{})), f4), OwE(b1, b2, b4, f2, f3, f4, f4))) == True{} : Bool}:
  match b4:
    case False{}:
      {==}
    case True{}:
      +A = D.Nat.of(Bool.and(b1, U32.is_eq(f2, f4)))
      +B = D.Nat.of(Bool.and(b2, U32.is_eq(f3, f4)))
      +O1 = D.Ps.opt(b1, f2, Nil{})
      %Equal.sym(Nat, D.Occ(D.Ps.opt(b2, f3, O1), f4), Nat.add(B, D.Occ(O1, f4)), occ.opt(b2, f3, O1, f4)) :
        {Nat.is_le(1n+_, Nat.add(A, Nat.add(B, D.Nat.of(Bool.and(True{}, U32.is_eq(f4, f4)))))) == True{} : Bool}
      %Equal.sym(Nat, D.Occ(O1, f4), Nat.add(A, 0n), occ.opt(b1, f2, Nil{}, f4)) :
        {Nat.is_le(1n+Nat.add(B, _), Nat.add(A, Nat.add(B, D.Nat.of(Bool.and(True{}, U32.is_eq(f4, f4)))))) == True{} : Bool}
      %Equal.sym(Bool, U32.is_eq(f4, f4), True{}, K.U.eq_refl(f4)) :
        {Nat.is_le(1n+Nat.add(B, Nat.add(A, 0n)), Nat.add(A, Nat.add(B, D.Nat.of(_)))) == True{} : Bool}
      K.ofT(Nat.is_le(1n+Nat.add(B, Nat.add(A, 0n)), Nat.add(A, Nat.add(B, 1n))), ar4(A, B))

# after the three drops, each part's drops are q's pointers to it
def occ.fin(+b1: Bool, +b2: Bool, +b4: Bool, +f2: U32, +f3: U32, +f4: U32, +y: U32) ->
  {D.Occ(D.Ps.opt(b4, f4, D.Ps.opt(b2, f3, D.Ps.opt(b1, f2, Nil{}))), y) == OwE(b1, b2, b4, f2, f3, f4, y) : Nat}:
  +A = D.Nat.of(Bool.and(b1, U32.is_eq(f2, y)))
  +B = D.Nat.of(Bool.and(b2, U32.is_eq(f3, y)))
  +C = D.Nat.of(Bool.and(b4, U32.is_eq(f4, y)))
  +O1 = D.Ps.opt(b1, f2, Nil{})
  +O2 = D.Ps.opt(b2, f3, O1)
  +O3 = D.Ps.opt(b4, f4, O2)
  +e1 = occ.opt(b4, f4, O2, y)
  +e2 = Equal.cong(Nat, Nat, z => Nat.add(C, z), D.Occ(O2, y), Nat.add(B, D.Occ(O1, y)), occ.opt(b2, f3, O1, y))
  +e3 = Equal.cong(Nat, Nat, z => Nat.add(C, Nat.add(B, z)), D.Occ(O1, y), A, Equal.trans(Nat, D.Occ(O1, y), Nat.add(A, 0n), A,
    occ.opt(b1, f2, Nil{}, y), N.add_zero(A)))
  +e4 = Equal.trans(Nat, Nat.add(C, Nat.add(B, A)), Nat.add(Nat.add(B, C), A), Nat.add(A, Nat.add(B, C)), N.add_comm3(C, B, A),
    Na.comm(Nat.add(B, C), A))
  Equal.trans(Nat, D.Occ(O3, y), Nat.add(C, D.Occ(O2, y)), Nat.add(A, Nat.add(B, C)), e1,
    Equal.trans(Nat, Nat.add(C, D.Occ(O2, y)), Nat.add(C, Nat.add(B, D.Occ(O1, y))), Nat.add(A, Nat.add(B, C)), e2,
      Equal.trans(Nat, Nat.add(C, Nat.add(B, D.Occ(O1, y))), Nat.add(C, Nat.add(B, A)), Nat.add(A, Nat.add(B, C)), e3, e4)))

# a cell of which q has no part is none of the pushed ones
def pts.nhas(pu: List<&2, U32>, +m: Cr.Cir.Cells, +q: U32, +y: U32, h: {Pts(pu, m, q) == True{} : Bool}, +h0: {D.Ow(m, q, y) == 0n : Nat}) ->
  {D.Has(pu, y) == False{} : Bool}:
  match pu:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      +h2 = h
      +ne = ne.ow(U32.is_eq(y, x), m, q, x, y, {==}, K.Bo.and_l(Nat.is_lt(0n, D.Ow(m, q, x)), Pts(rest, m, q), h2), h0)
      %Equal.sym(Bool, U32.is_eq(x, y), False{}, K.U.ne.sym(y, x, ne)) : {Bool.or(_, D.Has(rest, y)) == False{} : Bool}
      pts.nhas(rest, m, q, y, K.Bo.and_r(Nat.is_lt(0n, D.Ow(m, q, x)), Pts(rest, m, q), h2), h0)

# Dv of a part y (field f, bit b, the drops' Dvm of it, mh)
def dv.at(+b: Bool, +f: U32, +y: U32, +m: Cr.Cir.Cells, +M: Cr.Cir.Cells, +pu: List<&2, U32>, +dn: List<&2, U32>,
  et: {Bool.and(b, U32.is_eq(f, y)) == True{} : Bool}, +hz: {U32.is_zero(y) == False{} : Bool}, mh: {Dvm(b, f, m, M, pu, dn) == True{} : Bool}) ->
  {Dv(m, M, pu, y, D.Occ(dn, y)) == True{} : Bool}:
  +et2 = et
  +eb = K.Bo.and_l(b, U32.is_eq(f, y), et2)
  +ef = K.U.eq(f, y, K.Bo.and_r(b, U32.is_eq(f, y), et2))
  +h1 = {(%ef : {Dvm(b, _, m, M, pu, dn) == True{} : Bool}; mh) : {Dvm(b, y, m, M, pu, dn) == True{} : Bool}}
  +h2 = {(%eb : {Bool.or(Bool.not(_), Bool.or(U32.is_zero(y), Dv(m, M, pu, y, D.Occ(dn, y)))) == True{} : Bool}; h1) :
    {Bool.or(U32.is_zero(y), Dv(m, M, pu, y, D.Occ(dn, y))) == True{} : Bool}}
  K.Bo.or_r(U32.is_zero(y), Dv(m, M, pu, y, D.Occ(dn, y)), h2, hz)

# Dv of a cell of which q has no part: it kept its count and was not pushed
def dv.out(+m: Cr.Cir.Cells, +q: U32, +ws: List<&2, W1>, +pu: List<&2, U32>, +y: U32, +hpt: {W1s.pt(ws, m, q) == True{} : Bool},
  +hpp: {Pts(pu, m, q) == True{} : Bool}, +h0: {D.Ow(m, q, y) == 0n : Nat}) -> {Dv(m, W1s(ws, m), pu, y, 0n) == True{} : Bool}:
  +c0 = U32.to_nat(D.Fd(1n, m, y))
  %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(W1s(ws, m), y), Cr.Cir.Cells.get(m, y), w1s.get(ws, m, q, y, hpt, h0)) :
    {Dv.of(D.Stc(m, y), D.Has(pu, y), c0, U32.to_nat(Cr.Cir.Cell.get(1n, _)), 0n) == True{} : Bool}
  %Equal.sym(Bool, D.Has(pu, y), False{}, pts.nhas(pu, m, q, y, hpp, h0)) : {Dv.of(D.Stc(m, y), _, c0, c0, 0n) == True{} : Bool}
  dv.init.of(D.Stc(m, y), c0)

# after the three drops: Dv of every cell y but 0, with all of q's pointers
# dropped; y is the part in field 2, 3, 4, or none
def dv.all.k1(+m: Cr.Cir.Cells, +q: U32, +ws: List<&2, W1>, +pu: List<&2, U32>, +y: U32, +e1: {Bool.and(U32.is_ne(U32.and(D.Am(m, q), 1), 0), U32.is_eq(D.Fd(2n, m, q), y)) == True{} : Bool},
  +hz: {U32.is_zero(y) == False{} : Bool}, +hdv: {Dv3(D.Am(m, q), q, m, W1s(ws, m), pu, Dn3(m, q)) == True{} : Bool},
  +hpt: {W1s.pt(ws, m, q) == True{} : Bool}, +hpp: {Pts(pu, m, q) == True{} : Bool}) ->
  {Dv(m, W1s(ws, m), pu, y, D.Ow(m, q, y)) == True{} : Bool}:
  +a = D.Am(m, q)
  +b1 = U32.is_ne(U32.and(a, 1), 0)
  +b2 = U32.is_ne(U32.and(a, 2), 0)
  +b4 = U32.is_ne(U32.and(a, 4), 0)
  +f2 = D.Fd(2n, m, q)
  +f3 = D.Fd(3n, m, q)
  +f4 = D.Fd(4n, m, q)
  +M = W1s(ws, m)
  +dn = Dn3(m, q)
  +A = Dvm(b1, f2, m, M, pu, dn)
  +B = Dvm(b2, f3, m, M, pu, dn)
  +C = Dvm(b4, f4, m, M, pu, dn)
  +hbc = K.Bo.and_r(A, Bool.and(B, C), hdv)
  +eo = occ.fin(b1, b2, b4, f2, f3, f4, y)
  (%eo : {Dv(m, M, pu, y, _) == True{} : Bool}; dv.at(b1, f2, y, m, M, pu, dn, e1, hz, K.Bo.and_l(A, Bool.and(B, C), hdv)))

def dv.all.k2(+m: Cr.Cir.Cells, +q: U32, +ws: List<&2, W1>, +pu: List<&2, U32>, +y: U32, +e2: {Bool.and(U32.is_ne(U32.and(D.Am(m, q), 2), 0), U32.is_eq(D.Fd(3n, m, q), y)) == True{} : Bool},
  +hz: {U32.is_zero(y) == False{} : Bool}, +hdv: {Dv3(D.Am(m, q), q, m, W1s(ws, m), pu, Dn3(m, q)) == True{} : Bool},
  +hpt: {W1s.pt(ws, m, q) == True{} : Bool}, +hpp: {Pts(pu, m, q) == True{} : Bool}) ->
  {Dv(m, W1s(ws, m), pu, y, D.Ow(m, q, y)) == True{} : Bool}:
  +a = D.Am(m, q)
  +b1 = U32.is_ne(U32.and(a, 1), 0)
  +b2 = U32.is_ne(U32.and(a, 2), 0)
  +b4 = U32.is_ne(U32.and(a, 4), 0)
  +f2 = D.Fd(2n, m, q)
  +f3 = D.Fd(3n, m, q)
  +f4 = D.Fd(4n, m, q)
  +M = W1s(ws, m)
  +dn = Dn3(m, q)
  +A = Dvm(b1, f2, m, M, pu, dn)
  +B = Dvm(b2, f3, m, M, pu, dn)
  +C = Dvm(b4, f4, m, M, pu, dn)
  +hbc = K.Bo.and_r(A, Bool.and(B, C), hdv)
  +eo = occ.fin(b1, b2, b4, f2, f3, f4, y)
  (%eo : {Dv(m, M, pu, y, _) == True{} : Bool}; dv.at(b2, f3, y, m, M, pu, dn, e2, hz, K.Bo.and_l(B, C, hbc)))

def dv.all.k3(+m: Cr.Cir.Cells, +q: U32, +ws: List<&2, W1>, +pu: List<&2, U32>, +y: U32, +e3: {Bool.and(U32.is_ne(U32.and(D.Am(m, q), 4), 0), U32.is_eq(D.Fd(4n, m, q), y)) == True{} : Bool},
  +hz: {U32.is_zero(y) == False{} : Bool}, +hdv: {Dv3(D.Am(m, q), q, m, W1s(ws, m), pu, Dn3(m, q)) == True{} : Bool},
  +hpt: {W1s.pt(ws, m, q) == True{} : Bool}, +hpp: {Pts(pu, m, q) == True{} : Bool}) ->
  {Dv(m, W1s(ws, m), pu, y, D.Ow(m, q, y)) == True{} : Bool}:
  +a = D.Am(m, q)
  +b1 = U32.is_ne(U32.and(a, 1), 0)
  +b2 = U32.is_ne(U32.and(a, 2), 0)
  +b4 = U32.is_ne(U32.and(a, 4), 0)
  +f2 = D.Fd(2n, m, q)
  +f3 = D.Fd(3n, m, q)
  +f4 = D.Fd(4n, m, q)
  +M = W1s(ws, m)
  +dn = Dn3(m, q)
  +A = Dvm(b1, f2, m, M, pu, dn)
  +B = Dvm(b2, f3, m, M, pu, dn)
  +C = Dvm(b4, f4, m, M, pu, dn)
  +hbc = K.Bo.and_r(A, Bool.and(B, C), hdv)
  +eo = occ.fin(b1, b2, b4, f2, f3, f4, y)
  (%eo : {Dv(m, M, pu, y, _) == True{} : Bool}; dv.at(b4, f4, y, m, M, pu, dn, e3, hz, K.Bo.and_r(B, C, hbc)))

def dv.all.k0(+m: Cr.Cir.Cells, +q: U32, +ws: List<&2, W1>, +pu: List<&2, U32>, +y: U32, +e1: {Bool.and(U32.is_ne(U32.and(D.Am(m, q), 1), 0), U32.is_eq(D.Fd(2n, m, q), y)) == False{} : Bool}, +e2: {Bool.and(U32.is_ne(U32.and(D.Am(m, q), 2), 0), U32.is_eq(D.Fd(3n, m, q), y)) == False{} : Bool},
  +e3: {Bool.and(U32.is_ne(U32.and(D.Am(m, q), 4), 0), U32.is_eq(D.Fd(4n, m, q), y)) == False{} : Bool}, +hz: {U32.is_zero(y) == False{} : Bool}, +hdv: {Dv3(D.Am(m, q), q, m, W1s(ws, m), pu, Dn3(m, q)) == True{} : Bool},
  +hpt: {W1s.pt(ws, m, q) == True{} : Bool}, +hpp: {Pts(pu, m, q) == True{} : Bool}) ->
  {Dv(m, W1s(ws, m), pu, y, D.Ow(m, q, y)) == True{} : Bool}:
  +a = D.Am(m, q)
  +b2 = U32.is_ne(U32.and(a, 2), 0)
  +b4 = U32.is_ne(U32.and(a, 4), 0)
  +f3 = D.Fd(3n, m, q)
  +f4 = D.Fd(4n, m, q)
  +M = W1s(ws, m)
  +t1 = Bool.and(U32.is_ne(U32.and(a, 1), 0), U32.is_eq(D.Fd(2n, m, q), y))
  +t2 = Bool.and(b2, U32.is_eq(f3, y))
  +t3 = Bool.and(b4, U32.is_eq(f4, y))
  +h0 = {%Equal.sym(Bool, t1, False{}, e1) : {Nat.add(D.Nat.of(_), Nat.add(D.Nat.of(t2), D.Nat.of(t3))) == 0n : Nat};
    %Equal.sym(Bool, t2, False{}, e2) : {Nat.add(0n, Nat.add(D.Nat.of(_), D.Nat.of(t3))) == 0n : Nat};
    %Equal.sym(Bool, t3, False{}, e3) : {Nat.add(0n, Nat.add(0n, D.Nat.of(_))) == 0n : Nat};
    {==} : {D.Ow(m, q, y) == 0n : Nat}}
  (%Equal.sym(Nat, D.Ow(m, q, y), 0n, h0) : {Dv(m, M, pu, y, _) == True{} : Bool}; dv.out(m, q, ws, pu, y, hpt, hpp, h0))

def dv.all.c(t1: Bool, t2: Bool, t3: Bool, +m: Cr.Cir.Cells, +q: U32, +ws: List<&2, W1>, +pu: List<&2, U32>, +y: U32, +e1: {Bool.and(U32.is_ne(U32.and(D.Am(m, q), 1), 0), U32.is_eq(D.Fd(2n, m, q), y)) == t1 : Bool}, +e2: {Bool.and(U32.is_ne(U32.and(D.Am(m, q), 2), 0), U32.is_eq(D.Fd(3n, m, q), y)) == t2 : Bool},
  +e3: {Bool.and(U32.is_ne(U32.and(D.Am(m, q), 4), 0), U32.is_eq(D.Fd(4n, m, q), y)) == t3 : Bool}, +hz: {U32.is_zero(y) == False{} : Bool}, +hdv: {Dv3(D.Am(m, q), q, m, W1s(ws, m), pu, Dn3(m, q)) == True{} : Bool},
  +hpt: {W1s.pt(ws, m, q) == True{} : Bool}, +hpp: {Pts(pu, m, q) == True{} : Bool}) ->
  {Dv(m, W1s(ws, m), pu, y, D.Ow(m, q, y)) == True{} : Bool}:
  match t1:
    case True{}:
      dv.all.k1(m, q, ws, pu, y, e1, hz, hdv, hpt, hpp)
    case False{}:
      match t2:
        case True{}:
          dv.all.k2(m, q, ws, pu, y, e2, hz, hdv, hpt, hpp)
        case False{}:
          match t3:
            case True{}:
              dv.all.k3(m, q, ws, pu, y, e3, hz, hdv, hpt, hpp)
            case False{}:
              dv.all.k0(m, q, ws, pu, y, e1, e2, e3, hz, hdv, hpt, hpp)

def dv.all(+m: Cr.Cir.Cells, +q: U32, +ws: List<&2, W1>, +pu: List<&2, U32>, +y: U32, +hz: {U32.is_zero(y) == False{} : Bool},
  +hdv: {Dv3(D.Am(m, q), q, m, W1s(ws, m), pu, Dn3(m, q)) == True{} : Bool}, +hpt: {W1s.pt(ws, m, q) == True{} : Bool},
  +hpp: {Pts(pu, m, q) == True{} : Bool}) -> {Dv(m, W1s(ws, m), pu, y, D.Ow(m, q, y)) == True{} : Bool}:
  +a = D.Am(m, q)
  dv.all.c(Bool.and(U32.is_ne(U32.and(a, 1), 0), U32.is_eq(D.Fd(2n, m, q), y)), Bool.and(U32.is_ne(U32.and(a, 2), 0), U32.is_eq(D.Fd(3n, m, q), y)),
    Bool.and(U32.is_ne(U32.and(a, 4), 0), U32.is_eq(D.Fd(4n, m, q), y)), m, q, ws, pu, y, {==}, {==}, {==}, hz, hdv, hpt, hpp)

# The garbage and the pend list after a reuse
# -------------------------------------------

# a or b, with b giving b2
def or.mono_r(a: Bool, -b: Bool, -b2: Bool, h: {Bool.or(a, b) == True{} : Bool}, k: {b == True{} : Bool} -> {b2 == True{} : Bool}) ->
  {Bool.or(a, b2) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      k(h)

# Del of q keeps every other cell
def has.del.b(e: Bool, +o: U32, +rest: List<&2, U32>, +q: U32, +x: U32, +eo: {U32.is_eq(o, q) == e : Bool},
  +ne: {U32.is_eq(x, q) == False{} : Bool}, k: {D.Has(Del(rest, q), x) == D.Has(rest, x) : Bool}) ->
  {D.Has(Bool.pick(List<&2, U32>, e, rest, Con{o, Del(rest, q)}), x) == Bool.or(U32.is_eq(o, x), D.Has(rest, x)) : Bool}:
  match e:
    case True{}:
      +eq = K.U.eq(o, q, eo)
      +nox = {(%Equal.sym(U32, o, q, eq) : {U32.is_eq(_, x) == False{} : Bool}; K.U.ne.sym(x, q, ne)) : {U32.is_eq(o, x) == False{} : Bool}}
      %Equal.sym(Bool, U32.is_eq(o, x), False{}, nox) : {D.Has(rest, x) == Bool.or(_, D.Has(rest, x)) : Bool}
      {==}
    case False{}:
      Equal.cong(Bool, Bool, w => Bool.or(U32.is_eq(o, x), w), D.Has(Del(rest, q), x), D.Has(rest, x), k)

def has.del(P: List<&2, U32>, +q: U32, +x: U32, +ne: {U32.is_eq(x, q) == False{} : Bool}) -> {D.Has(Del(P, q), x) == D.Has(P, x) : Bool}:
  match P:
    case Nil{}:
      {==}
    case Con{+o, +rest}:
      has.del.b(U32.is_eq(o, q), o, rest, q, x, {==}, ne, has.del(rest, q, x, ne))

def has.del.le.b(e: Bool, +o: U32, +rest: List<&2, U32>, +q: U32, +x: U32,
  h: {D.Has(Bool.pick(List<&2, U32>, e, rest, Con{o, Del(rest, q)}), x) == True{} : Bool},
  k: {D.Has(Del(rest, q), x) == True{} : Bool} -> {D.Has(rest, x) == True{} : Bool}) ->
  {Bool.or(U32.is_eq(o, x), D.Has(rest, x)) == True{} : Bool}:
  match e:
    case True{}:
      K.Bo.or_ir(U32.is_eq(o, x), D.Has(rest, x), h)
    case False{}:
      or.mono_r(U32.is_eq(o, x), D.Has(Del(rest, q), x), D.Has(rest, x), h, k)

def has.del.le(P: List<&2, U32>, +q: U32, +x: U32, h: {D.Has(Del(P, q), x) == True{} : Bool}) -> {D.Has(P, x) == True{} : Bool}:
  match P:
    case Nil{}:
      h
    case Con{+o, +rest}:
      has.del.le.b(U32.is_eq(o, q), o, rest, q, x, h, h2 => has.del.le(rest, q, x, h2))

def has.del.f.b(v: Bool, +L: List<&2, U32>, +q: U32, +x: U32, ev: {D.Has(Del(L, q), x) == v : Bool}, h: {D.Has(L, x) == False{} : Bool}) ->
  {D.Has(Del(L, q), x) == False{} : Bool}:
  match v:
    case True{}:
      K.Bo.ft({D.Has(Del(L, q), x) == False{} : Bool}, Equal.trans(Bool, True{}, D.Has(L, x), False{},
        Equal.sym(Bool, D.Has(L, x), True{}, has.del.le(L, q, x, ev)), h))
    case False{}:
      ev

def has.del.f(+L: List<&2, U32>, +q: U32, +x: U32, h: {D.Has(L, x) == False{} : Bool}) -> {D.Has(Del(L, q), x) == False{} : Bool}:
  has.del.f.b(D.Has(Del(L, q), x), L, q, x, {==}, h)

# q is no more in Del(P, q), when it was once in P
def del.nhas.b(e: Bool, +o: U32, +rest: List<&2, U32>, +q: U32, +eo: {U32.is_eq(o, q) == e : Bool},
  h: {Bool.and(Bool.not(D.Has(rest, o)), D.Nodup(rest)) == True{} : Bool}, k: {D.Nodup(rest) == True{} : Bool} -> {D.Has(Del(rest, q), q) == False{} : Bool}) ->
  {D.Has(Bool.pick(List<&2, U32>, e, rest, Con{o, Del(rest, q)}), q) == False{} : Bool}:
  match e:
    case True{}:
      +h2 = h
      +eq = K.U.eq(o, q, eo)
      (%eq : {D.Has(rest, _) == False{} : Bool}; K.Bo.not_t(D.Has(rest, o), K.Bo.and_l(Bool.not(D.Has(rest, o)), D.Nodup(rest), h2)))
    case False{}:
      +h2 = h
      %Equal.sym(Bool, U32.is_eq(o, q), False{}, eo) : {Bool.or(_, D.Has(Del(rest, q), q)) == False{} : Bool}
      k(K.Bo.and_r(Bool.not(D.Has(rest, o)), D.Nodup(rest), h2))

def del.nhas(P: List<&2, U32>, +q: U32, h: {D.Nodup(P) == True{} : Bool}) -> {D.Has(Del(P, q), q) == False{} : Bool}:
  match P:
    case Nil{}:
      {==}
    case Con{+o, +rest}:
      del.nhas.b(U32.is_eq(o, q), o, rest, q, {==}, h, h2 => del.nhas(rest, q, h2))

def nodup.del.b(e: Bool, +o: U32, +rest: List<&2, U32>, +q: U32, h: {Bool.and(Bool.not(D.Has(rest, o)), D.Nodup(rest)) == True{} : Bool},
  k: {D.Nodup(rest) == True{} : Bool} -> {D.Nodup(Del(rest, q)) == True{} : Bool}) ->
  {D.Nodup(Bool.pick(List<&2, U32>, e, rest, Con{o, Del(rest, q)})) == True{} : Bool}:
  match e:
    case True{}:
      K.Bo.and_r(Bool.not(D.Has(rest, o)), D.Nodup(rest), h)
    case False{}:
      +h2 = h
      K.Bo.and_i(Bool.not(D.Has(Del(rest, q), o)), D.Nodup(Del(rest, q)),
        K.Bo.not_i(D.Has(Del(rest, q), o), has.del.f(rest, q, o, K.Bo.not_t(D.Has(rest, o), K.Bo.and_l(Bool.not(D.Has(rest, o)), D.Nodup(rest), h2)))),
        k(K.Bo.and_r(Bool.not(D.Has(rest, o)), D.Nodup(rest), h2)))

def nodup.del(P: List<&2, U32>, +q: U32, h: {D.Nodup(P) == True{} : Bool}) -> {D.Nodup(Del(P, q)) == True{} : Bool}:
  match P:
    case Nil{}:
      {==}
    case Con{+o, +rest}:
      nodup.del.b(U32.is_eq(o, q), o, rest, q, h, h2 => nodup.del(rest, q, h2))

# cells of P, none q, are cells of Del(P, q)
def sub.del(L: List<&2, U32>, +P: List<&2, U32>, +q: U32, hs: {D.Sub(L, P) == True{} : Bool}, hn: {D.Has(L, q) == False{} : Bool}) ->
  {D.Sub(L, Del(P, q)) == True{} : Bool}:
  match L:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      +hs2 = hs
      +hn2 = hn
      +ne = K.or.fl(U32.is_eq(x, q), D.Has(rest, q), hn2)
      K.Bo.and_i(D.Has(Del(P, q), x), D.Sub(rest, Del(P, q)),
        (%Equal.sym(Bool, D.Has(Del(P, q), x), D.Has(P, x), has.del(P, q, x, ne)) : {_ == True{} : Bool};
          K.Bo.and_l(D.Has(P, x), D.Sub(rest, P), hs2)),
        sub.del(rest, P, q, K.Bo.and_r(D.Has(P, x), D.Sub(rest, P), hs2), K.or.fr(U32.is_eq(x, q), D.Has(rest, q), hn2)))

# the garbage's pointers, without q's
def pp.del.b(e: Bool, +o: U32, +rest: List<&2, U32>, +m: Cr.Cir.Cells, +q: U32, +c: U32, +eo: {U32.is_eq(o, q) == e : Bool},
  h: {Bool.or(U32.is_eq(o, q), D.Has(rest, q)) == True{} : Bool},
  k: {D.Has(rest, q) == True{} : Bool} -> {D.Pp(rest, m, c) == Nat.add(D.Ow(m, q, c), D.Pp(Del(rest, q), m, c)) : Nat}) ->
  {Nat.add(D.Ow(m, o, c), D.Pp(rest, m, c)) == Nat.add(D.Ow(m, q, c), D.Pp(Bool.pick(List<&2, U32>, e, rest, Con{o, Del(rest, q)}), m, c)) : Nat}:
  match e:
    case True{}:
      +eq = K.U.eq(o, q, eo)
      (%eq : {Nat.add(D.Ow(m, o, c), D.Pp(rest, m, c)) == Nat.add(D.Ow(m, _, c), D.Pp(rest, m, c)) : Nat}; {==})
    case False{}:
      +A = D.Ow(m, o, c)
      +B = D.Ow(m, q, c)
      +C = D.Pp(Del(rest, q), m, c)
      Equal.trans(Nat, Nat.add(A, D.Pp(rest, m, c)), Nat.add(A, Nat.add(B, C)), Nat.add(B, Nat.add(A, C)),
        Equal.cong(Nat, Nat, z => Nat.add(A, z), D.Pp(rest, m, c), Nat.add(B, C), k((%eo : {Bool.or(_, D.Has(rest, q)) == True{} : Bool}; h))),
        N.add_swap(A, B, C))

def pp.del(P: List<&2, U32>, +m: Cr.Cir.Cells, +q: U32, +c: U32, h: {D.Has(P, q) == True{} : Bool}) ->
  {D.Pp(P, m, c) == Nat.add(D.Ow(m, q, c), D.Pp(Del(P, q), m, c)) : Nat}:
  match P:
    case Nil{}:
      K.Bo.tf({0n == Nat.add(D.Ow(m, q, c), 0n) : Nat}, h)
    case Con{+o, +rest}:
      pp.del.b(U32.is_eq(o, q), o, rest, m, q, c, {==}, h, h2 => pp.del(rest, m, q, c, h2))

# the pushed cells: garbage out of the pend list
def gq.sub(pu: List<&2, U32>, +P: List<&2, U32>, +Q: List<&2, U32>, h: {Gq(pu, P, Q) == True{} : Bool}) -> {D.Sub(pu, P) == True{} : Bool}:
  match pu:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      +h2 = h
      +A = Bool.and(D.Has(P, x), Bool.not(D.Has(Q, x)))
      K.Bo.and_i(D.Has(P, x), D.Sub(rest, P), K.Bo.and_l(D.Has(P, x), Bool.not(D.Has(Q, x)), K.Bo.and_l(A, Gq(rest, P, Q), h2)),
        gq.sub(rest, P, Q, K.Bo.and_r(A, Gq(rest, P, Q), h2)))

def gq.dsj(pu: List<&2, U32>, +P: List<&2, U32>, +q: U32, +Qr: List<&2, U32>, h: {Gq(pu, P, Con{q, Qr}) == True{} : Bool}) ->
  {K.Dsj(pu, Qr) == True{} : Bool}:
  match pu:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      +h2 = h
      +A = Bool.and(D.Has(P, x), Bool.not(D.Has(Con{q, Qr}, x)))
      +hn = K.Bo.not_t(D.Has(Con{q, Qr}, x), K.Bo.and_r(D.Has(P, x), Bool.not(D.Has(Con{q, Qr}, x)), K.Bo.and_l(A, Gq(rest, P, Con{q, Qr}), h2)))
      K.Bo.and_i(Bool.not(D.Has(Qr, x)), K.Dsj(rest, Qr), K.Bo.not_i(D.Has(Qr, x), K.or.fr(U32.is_eq(q, x), D.Has(Qr, x), hn)),
        gq.dsj(rest, P, q, Qr, K.Bo.and_r(A, Gq(rest, P, Con{q, Qr}), h2)))

def gq.mem.b(e: Bool, +x: U32, +rest: List<&2, U32>, +P: List<&2, U32>, +Q: List<&2, U32>, +y: U32, +ex: {U32.is_eq(x, y) == e : Bool},
  h: {Bool.and(Bool.and(D.Has(P, x), Bool.not(D.Has(Q, x))), Gq(rest, P, Q)) == True{} : Bool},
  hy: {Bool.or(U32.is_eq(x, y), D.Has(rest, y)) == True{} : Bool},
  k: {Gq(rest, P, Q) == True{} : Bool} -> {D.Has(rest, y) == True{} : Bool} -> {Bool.and(D.Has(P, y), Bool.not(D.Has(Q, y))) == True{} : Bool}) ->
  {Bool.and(D.Has(P, y), Bool.not(D.Has(Q, y))) == True{} : Bool}:
  match e:
    case True{}:
      +A = Bool.and(D.Has(P, x), Bool.not(D.Has(Q, x)))
      +eq = K.U.eq(x, y, ex)
      (%eq : {Bool.and(D.Has(P, _), Bool.not(D.Has(Q, _))) == True{} : Bool}; K.Bo.and_l(A, Gq(rest, P, Q), h))
    case False{}:
      +A = Bool.and(D.Has(P, x), Bool.not(D.Has(Q, x)))
      k(K.Bo.and_r(A, Gq(rest, P, Q), h), (%ex : {Bool.or(_, D.Has(rest, y)) == True{} : Bool}; hy))

def gq.mem(pu: List<&2, U32>, +P: List<&2, U32>, +Q: List<&2, U32>, +y: U32, h: {Gq(pu, P, Q) == True{} : Bool},
  hy: {D.Has(pu, y) == True{} : Bool}) -> {Bool.and(D.Has(P, y), Bool.not(D.Has(Q, y))) == True{} : Bool}:
  match pu:
    case Nil{}:
      K.Bo.tf({Bool.and(D.Has(P, y), Bool.not(D.Has(Q, y))) == True{} : Bool}, hy)
    case Con{+x, +rest}:
      gq.mem.b(U32.is_eq(x, y), x, rest, P, Q, y, {==}, h, hy, h2 => hy2 => gq.mem(rest, P, Q, y, h2, hy2))

# The cells after a reuse
# -----------------------
#
# After the drops (W1s(ws, m)), M.alloc sets q to zeros (ms): every other
# cell keeps its fields 0, 2 to 4 and its pointers, but the pend list has
# changed (Q2: the pushed cells, then the rest Qr of the old one).

def fd.zq(+m: Cr.Cir.Cells, +q: U32, +Qr: List<&2, U32>, +P: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32, +nx: U32,
  +ws: List<&2, W1>, +pu: List<&2, U32>, +k: Nat, +hk: {Nat.is_eq(k, 1n) == False{} : Bool}, +y: U32,
  +ne: {U32.is_eq(y, q) == False{} : Bool}) -> {D.Fd(k, Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), y) == D.Fd(k, m, y) : U32}:
  +M = W1s(ws, m)
  +ms = Cr.Cir.Cells.set(M, q, Cr.Cir.Cell.zero())
  +Q2 = List.append(&2, U32, pu, Qr)
  +Q = {Con{q, Qr} : List<&2, U32>}
  +Dl = Del(P, q)
  Equal.trans(U32, D.Fd(k, ms, y), D.Fd(k, M, y), D.Fd(k, m, y),
    Equal.cong(Cr.Cir.Cell, U32, w => Cr.Cir.Cell.get(k, w), Cr.Cir.Cells.get(ms, y), Cr.Cir.Cells.get(M, y), K.Cl.get_ne(M, y, q, Cr.Cir.Cell.zero(), ne)),
    fd.w1s(ws, m, k, hk, y))

def f1.zq(+m: Cr.Cir.Cells, +q: U32, +Qr: List<&2, U32>, +P: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32, +nx: U32,
  +ws: List<&2, W1>, +pu: List<&2, U32>, +y: U32, +ne: {U32.is_eq(y, q) == False{} : Bool}) ->
  {D.Fd(1n, Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), y) == D.Fd(1n, W1s(ws, m), y) : U32}:
  +M = W1s(ws, m)
  +ms = Cr.Cir.Cells.set(M, q, Cr.Cir.Cell.zero())
  +Q2 = List.append(&2, U32, pu, Qr)
  +Q = {Con{q, Qr} : List<&2, U32>}
  +Dl = Del(P, q)
  Equal.cong(Cr.Cir.Cell, U32, w => Cr.Cir.Cell.get(1n, w), Cr.Cir.Cells.get(ms, y), Cr.Cir.Cells.get(M, y), K.Cl.get_ne(M, y, q, Cr.Cir.Cell.zero(), ne))

def stc.zq(+m: Cr.Cir.Cells, +q: U32, +Qr: List<&2, U32>, +P: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32, +nx: U32,
  +ws: List<&2, W1>, +pu: List<&2, U32>, +y: U32, +ne: {U32.is_eq(y, q) == False{} : Bool}) -> {D.Stc(Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), y) == D.Stc(m, y) : Bool}:
  K.stc.eq(Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), m, y, fd.zq(m, q, Qr, P, zs, K, F, nx, ws, pu, 0n, {==}, y, ne))

# Ps by the Bool of the pend list
def PsH(+f0: U32, +t2: U32, +f2: U32, +f3: U32, +f4: U32, +h: Bool) -> List<&2, U32>:
  +tg = U32.and(f0, 63)
  Bool.pick(List<&2, U32>, U32.is_lt(tg, 19), D.Ps.term(t2, f2, f3, f4),
    Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_le(32, tg), U32.is_le(tg, 40)), Bool.not(h)),
      Con{f2, D.Ps.opt(U32.is_eq(tg, 38), f3, Nil{})},
      Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_eq(tg, 41), U32.is_ne(U32.and(f0, 4096), 0)), Bool.not(h)), [f2], Nil{})))

def ps.h(+M: Cr.Cir.Cells, +Q: List<&2, U32>, +o: U32) ->
  {D.Ps(M, Q, o) == PsH(D.Fd(0n, M, o), D.Fd(2n, M, U32.add(272, U32.and(D.Fd(0n, M, o), 63))), D.Fd(2n, M, o), D.Fd(3n, M, o), D.Fd(4n, M, o),
    D.Has(Q, o)) : List<&2, U32>}:
  {==}

# Ps sees the pend list only by whether the cell is in it
def ps.hq(+M: Cr.Cir.Cells, +Q1: List<&2, U32>, +Q2: List<&2, U32>, +o: U32, e: {D.Has(Q1, o) == D.Has(Q2, o) : Bool}) ->
  {D.Ps(M, Q1, o) == D.Ps(M, Q2, o) : List<&2, U32>}:
  +f0 = D.Fd(0n, M, o)
  +t2 = D.Fd(2n, M, U32.add(272, U32.and(f0, 63)))
  +f2 = D.Fd(2n, M, o)
  +f3 = D.Fd(3n, M, o)
  +f4 = D.Fd(4n, M, o)
  Equal.trans(List<&2, U32>, D.Ps(M, Q1, o), PsH(f0, t2, f2, f3, f4, D.Has(Q1, o)), D.Ps(M, Q2, o), ps.h(M, Q1, o),
    Equal.trans(List<&2, U32>, PsH(f0, t2, f2, f3, f4, D.Has(Q1, o)), PsH(f0, t2, f2, f3, f4, D.Has(Q2, o)), D.Ps(M, Q2, o),
      Equal.cong(Bool, List<&2, U32>, h => PsH(f0, t2, f2, f3, f4, h), D.Has(Q1, o), D.Has(Q2, o), e),
      Equal.sym(List<&2, U32>, D.Ps(M, Q2, o), PsH(f0, t2, f2, f3, f4, D.Has(Q2, o)), ps.h(M, Q2, o))))

# and not at all for a term cell
def ps.q19(+M: Cr.Cir.Cells, +Q1: List<&2, U32>, +Q2: List<&2, U32>, +o: U32,
  +ht: {U32.is_lt(U32.and(D.Fd(0n, M, o), 63), 19) == True{} : Bool}) -> {D.Ps(M, Q1, o) == D.Ps(M, Q2, o) : List<&2, U32>}:
  +f0 = D.Fd(0n, M, o)
  +tg = U32.and(f0, 63)
  +f2 = D.Fd(2n, M, o)
  +f3 = D.Fd(3n, M, o)
  +f4 = D.Fd(4n, M, o)
  +PT = D.Ps.term(D.Fd(2n, M, U32.add(272, tg)), f2, f3, f4)
  +R1 = Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_le(32, tg), U32.is_le(tg, 40)), Bool.not(D.Has(Q1, o))),
    Con{f2, D.Ps.opt(U32.is_eq(tg, 38), f3, Nil{})},
    Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_eq(tg, 41), U32.is_ne(U32.and(f0, 4096), 0)), Bool.not(D.Has(Q1, o))), [f2], Nil{}))
  +R2 = Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_le(32, tg), U32.is_le(tg, 40)), Bool.not(D.Has(Q2, o))),
    Con{f2, D.Ps.opt(U32.is_eq(tg, 38), f3, Nil{})},
    Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_eq(tg, 41), U32.is_ne(U32.and(f0, 4096), 0)), Bool.not(D.Has(Q2, o))), [f2], Nil{}))
  %Equal.sym(Bool, U32.is_lt(tg, 19), True{}, ht) :
    {Bool.pick(List<&2, U32>, _, PT, R1) == Bool.pick(List<&2, U32>, _, PT, R2) : List<&2, U32>}
  {==}

# a or (b and c), with c false, gives a
def or.and.f(a: Bool, +b: Bool, +c: Bool, h: {Bool.or(a, Bool.and(b, c)) == True{} : Bool}, hc: {c == False{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      K.Bo.tf({False{} == True{} : Bool}, Equal.trans(Bool, False{}, c, True{}, Equal.sym(Bool, c, False{}, hc), K.Bo.and_r(b, c, h)))

# a pushed cell is a term cell
def pu.tg(+m: Cr.Cir.Cells, +P: List<&2, U32>, +Q: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32, +N: U32, +pu: List<&2, U32>, +y: U32,
  +hgq: {Gq(pu, P, Q) == True{} : Bool}, +hcs: {D.AL.cells(P, m, P, Q, zs, K, F, N) == True{} : Bool}, +hy: {D.Has(pu, y) == True{} : Bool}) ->
  {U32.is_lt(U32.and(D.Fd(0n, m, y), 63), 19) == True{} : Bool}:
  +tg = U32.and(D.Fd(0n, m, y), 63)
  +g = gq.mem(pu, P, Q, y, hgq, hy)
  +hpy = K.Bo.and_l(D.Has(P, y), Bool.not(D.Has(Q, y)), g)
  +hqy = K.Bo.not_t(D.Has(Q, y), K.Bo.and_r(D.Has(P, y), Bool.not(D.Has(Q, y)), g))
  +hx = al.mem(P, m, P, Q, zs, K, F, N, y, hpy, hcs)
  +hd = K.Bo.and_l(K.AL.hd(m, Q, y, F, N), Bool.and(K.AL.pt(m, P, zs, y, K, F, N), K.AL.ct(m, P, Q, y, F, N)), hx)
  +h18 = or.and.f(U32.is_le(tg, 18), U32.is_le(32, tg), D.Has(Q, y), K.al.hd.tg(m, Q, y, F, N, hd), hqy)
  K.U.lt_t(tg, 19, K.U.le(tg, 18, h18))

def ps.qq.b(hp: Bool, +m: Cr.Cir.Cells, +q: U32, +Qr: List<&2, U32>, +P: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32, +nx: U32,
  +ws: List<&2, W1>, +pu: List<&2, U32>, +hq: {D.Has(P, q) == True{} : Bool}, +hsub: {D.Sub(Con{q, Qr}, P) == True{} : Bool},
  +hcs: {D.AL.cells(P, m, P, Con{q, Qr}, zs, K, F, nx) == True{} : Bool}, +hnp: {D.Nodup(P) == True{} : Bool},
  +hnqr: {D.Has(Qr, q) == False{} : Bool}, +hgq: {Gq(pu, P, Con{q, Qr}) == True{} : Bool}, +hpp: {Pts(pu, m, q) == True{} : Bool},
  +hpt: {W1s.pt(ws, m, q) == True{} : Bool}, +hdv: {Dv3(D.Am(m, q), q, m, W1s(ws, m), pu, Dn3(m, q)) == True{} : Bool},
  +hzq: N.Le(291n, U32.to_nat(q)), +hk: {U32.is_le(290, K) == True{} : Bool}, +hkf: {U32.is_lt(K, F) == True{} : Bool}, +tb: D.Tb(m), +y: U32, +ne: {U32.is_eq(y, q) == False{} : Bool}, +ehp: {D.Has(pu, y) == hp : Bool}) ->
  {D.Ps(m, List.append(&2, U32, pu, Qr), y) == D.Ps(m, Con{q, Qr}, y) : List<&2, U32>}:
  match hp:
    case True{}:
      ps.q19(m, List.append(&2, U32, pu, Qr), Con{q, Qr}, y, pu.tg(m, P, Con{q, Qr}, zs, K, F, nx, pu, y, hgq, hcs, ehp))
    case False{}:
      +e1 = {(%ehp : {D.Has(List.append(&2, U32, pu, Qr), y) == Bool.or(_, D.Has(Qr, y)) : Bool}; K.has.app(pu, Qr, y)) : {D.Has(List.append(&2, U32, pu, Qr), y) == D.Has(Qr, y) : Bool}}
      +e2 = {(%Equal.sym(Bool, U32.is_eq(q, y), False{}, K.U.ne.sym(y, q, ne)) : {D.Has(Qr, y) == Bool.or(_, D.Has(Qr, y)) : Bool}; {==}) :
        {D.Has(Qr, y) == D.Has(Con{q, Qr}, y) : Bool}}
      ps.hq(m, List.append(&2, U32, pu, Qr), Con{q, Qr}, y, Equal.trans(Bool, D.Has(List.append(&2, U32, pu, Qr), y), D.Has(Qr, y), D.Has(Con{q, Qr}, y), e1, e2))

def ps.zq(+m: Cr.Cir.Cells, +q: U32, +Qr: List<&2, U32>, +P: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32, +nx: U32,
  +ws: List<&2, W1>, +pu: List<&2, U32>, +hq: {D.Has(P, q) == True{} : Bool}, +hsub: {D.Sub(Con{q, Qr}, P) == True{} : Bool},
  +hcs: {D.AL.cells(P, m, P, Con{q, Qr}, zs, K, F, nx) == True{} : Bool}, +hnp: {D.Nodup(P) == True{} : Bool},
  +hnqr: {D.Has(Qr, q) == False{} : Bool}, +hgq: {Gq(pu, P, Con{q, Qr}) == True{} : Bool}, +hpp: {Pts(pu, m, q) == True{} : Bool},
  +hpt: {W1s.pt(ws, m, q) == True{} : Bool}, +hdv: {Dv3(D.Am(m, q), q, m, W1s(ws, m), pu, Dn3(m, q)) == True{} : Bool},
  +hzq: N.Le(291n, U32.to_nat(q)), +hk: {U32.is_le(290, K) == True{} : Bool}, +hkf: {U32.is_lt(K, F) == True{} : Bool}, +tb: D.Tb(m), +y: U32, +ne: {U32.is_eq(y, q) == False{} : Bool}) ->
  {D.Ps(Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), List.append(&2, U32, pu, Qr), y) == D.Ps(m, Con{q, Qr}, y) : List<&2, U32>}:
  +M = W1s(ws, m)
  +ms = Cr.Cir.Cells.set(M, q, Cr.Cir.Cell.zero())
  +Q2 = List.append(&2, U32, pu, Qr)
  +Q = {Con{q, Qr} : List<&2, U32>}
  +Dl = Del(P, q)
  Equal.trans(List<&2, U32>, D.Ps(ms, Q2, y), D.Ps(M, Q2, y), D.Ps(m, Q, y), K.ps.set(M, q, Cr.Cir.Cell.zero(), Q2, y, ne, hzq),
    Equal.trans(List<&2, U32>, D.Ps(M, Q2, y), D.Ps(m, Q2, y), D.Ps(m, Q, y), ps.w1s(ws, m, Q2, y),
      ps.qq.b(D.Has(pu, y), m, q, Qr, P, zs, K, F, nx, ws, pu, hq, hsub, hcs, hnp, hnqr, hgq, hpp, hpt, hdv, hzq, hk, hkf, tb, y, ne, {==})))


# a cell that no garbage part can be: not 0, not STATIC, not garbage, and
# counting 0 (as a table cell)
def part.no.e(e: Bool, +m: Cr.Cir.Cells, +P: List<&2, U32>, +zs: List<&2, D.Zs>, +z: Nat, +am: U32, +bit: U32, +f: U32, +y: U32, +K: U32,
  +F: U32, +N: U32, +ef: {U32.is_eq(f, y) == e : Bool}, +hon: {U32.is_zero(U32.and(am, bit)) == False{} : Bool},
  h: {D.AL.part(m, P, zs, z, am, bit, f, K, F, N) == True{} : Bool}, +hy0: {U32.is_zero(y) == False{} : Bool},
  +hs: {D.Stc(m, y) == False{} : Bool}, +hp: {D.Has(P, y) == False{} : Bool}, +hc: {U32.to_nat(D.Fd(1n, m, y)) == 0n : Nat}) ->
  {e == False{} : Bool}:
  match e:
    case False{}:
      {==}
    case True{}:
      +ex = K.U.eq(f, y, ef)
      +h2 = {(%ex : {D.AL.part(m, P, zs, z, am, bit, _, K, F, N) == True{} : Bool}; h) : {D.AL.part(m, P, zs, z, am, bit, y, K, F, N) == True{} : Bool}}
      +pp = D.Pp(P, m, y)
      +R4 = Bool.or(Bool.and(D.Has(P, y), Nat.is_lt(D.Zz(zs, y), z)), Nat.is_lt(pp, U32.to_nat(D.Fd(1n, m, y))))
      +R3 = Bool.or(D.Stc(m, y), R4)
      +r1 = K.Bo.or_r(U32.is_zero(U32.and(am, bit)), Bool.or(U32.is_zero(y), Bool.and(Cr.Cir.is_cell(y, K, F, N), R3)), h2, hon)
      +r2 = K.Bo.or_r(U32.is_zero(y), Bool.and(Cr.Cir.is_cell(y, K, F, N), R3), r1, hy0)
      +r4 = K.Bo.or_r(D.Stc(m, y), R4, K.Bo.and_r(Cr.Cir.is_cell(y, K, F, N), R3, r2), hs)
      +r5 = {(%hp : {Bool.or(Bool.and(_, Nat.is_lt(D.Zz(zs, y), z)), Nat.is_lt(pp, U32.to_nat(D.Fd(1n, m, y)))) == True{} : Bool}; r4) :
        {Nat.is_lt(pp, U32.to_nat(D.Fd(1n, m, y))) == True{} : Bool}}
      +r6 = {(%hc : {Nat.is_lt(pp, _) == True{} : Bool}; r5) : {Nat.is_lt(pp, 0n) == True{} : Bool}}
      Empty.absurd({True{} == False{} : Bool}, K.Na.lt1(pp, 0n, r6))

def part.no.b(b: Bool, +m: Cr.Cir.Cells, +P: List<&2, U32>, +zs: List<&2, D.Zs>, +z: Nat, +am: U32, +bit: U32, +f: U32, +y: U32, +K: U32,
  +F: U32, +N: U32, +eb: {U32.is_ne(U32.and(am, bit), 0) == b : Bool}, h: {D.AL.part(m, P, zs, z, am, bit, f, K, F, N) == True{} : Bool},
  +hy0: {U32.is_zero(y) == False{} : Bool}, +hs: {D.Stc(m, y) == False{} : Bool}, +hp: {D.Has(P, y) == False{} : Bool},
  +hc: {U32.to_nat(D.Fd(1n, m, y)) == 0n : Nat}) -> {Bool.and(b, U32.is_eq(f, y)) == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      part.no.e(U32.is_eq(f, y), m, P, zs, z, am, bit, f, y, K, F, N, {==}, K.Bo.not_t(U32.is_eq(U32.and(am, bit), 0), eb), h, hy0, hs, hp, hc)

# such a cell is no part of a garbage cell q
def ow.zero(+m: Cr.Cir.Cells, +P: List<&2, U32>, +zs: List<&2, D.Zs>, +q: U32, +K: U32, +F: U32, +N: U32, +y: U32,
  +hpq: {K.AL.pt(m, P, zs, q, K, F, N) == True{} : Bool}, +hy0: {U32.is_zero(y) == False{} : Bool}, +hs: {D.Stc(m, y) == False{} : Bool},
  +hp: {D.Has(P, y) == False{} : Bool}, +hc: {U32.to_nat(D.Fd(1n, m, y)) == 0n : Nat}) -> {D.Ow(m, q, y) == 0n : Nat}:
  +a = D.Am(m, q)
  +z = D.Zz(zs, q)
  +b1 = U32.is_ne(U32.and(a, 1), 0)
  +b2 = U32.is_ne(U32.and(a, 2), 0)
  +b4 = U32.is_ne(U32.and(a, 4), 0)
  +f2 = D.Fd(2n, m, q)
  +f3 = D.Fd(3n, m, q)
  +f4 = D.Fd(4n, m, q)
  +A1 = D.AL.part(m, P, zs, z, a, 1, f2, K, F, N)
  +A2 = D.AL.part(m, P, zs, z, a, 2, f3, K, F, N)
  +A4 = D.AL.part(m, P, zs, z, a, 4, f4, K, F, N)
  +r = K.Bo.and_r(A1, Bool.and(A2, A4), hpq)
  +t1 = part.no.b(b1, m, P, zs, z, a, 1, f2, y, K, F, N, {==}, K.Bo.and_l(A1, Bool.and(A2, A4), hpq), hy0, hs, hp, hc)
  +t2 = part.no.b(b2, m, P, zs, z, a, 2, f3, y, K, F, N, {==}, K.Bo.and_l(A2, A4, r), hy0, hs, hp, hc)
  +t3 = part.no.b(b4, m, P, zs, z, a, 4, f4, y, K, F, N, {==}, K.Bo.and_r(A2, A4, r), hy0, hs, hp, hc)
  +T1 = Bool.and(b1, U32.is_eq(f2, y))
  +T2 = Bool.and(b2, U32.is_eq(f3, y))
  +T3 = Bool.and(b4, U32.is_eq(f4, y))
  {%Equal.sym(Bool, T1, False{}, t1) : {Nat.add(D.Nat.of(_), Nat.add(D.Nat.of(T2), D.Nat.of(T3))) == 0n : Nat};
    %Equal.sym(Bool, T2, False{}, t2) : {Nat.add(0n, Nat.add(D.Nat.of(_), D.Nat.of(T3))) == 0n : Nat};
    %Equal.sym(Bool, T3, False{}, t3) : {Nat.add(0n, Nat.add(0n, D.Nat.of(_))) == 0n : Nat};
    {==} : {D.Ow(m, q, y) == 0n : Nat}}

# a garbage cell is from F on
def al.hd.le(+m: Cr.Cir.Cells, +Q: List<&2, U32>, +o: U32, +F: U32, +N: U32, h: {K.AL.hd(m, Q, o, F, N) == True{} : Bool}) ->
  {U32.is_le(F, o) == True{} : Bool}:
  +tg = U32.and(D.Fd(0n, m, o), 63)
  K.Bo.and_l(U32.is_le(F, o), U32.is_lt(o, N), K.Bo.and_l(Bool.and(U32.is_le(F, o), U32.is_lt(o, N)), Bool.not(D.Stc(m, o)),
    K.Bo.and_l(Bool.and(Bool.and(U32.is_le(F, o), U32.is_lt(o, N)), Bool.not(D.Stc(m, o))),
      Bool.or(U32.is_le(tg, 18), Bool.and(U32.is_le(32, tg), D.Has(Q, o))), h)))

# a cell below F is no garbage cell
def has.ltF(os: List<&2, U32>, +m: Cr.Cir.Cells, +P: List<&2, U32>, +Q: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32,
  +N: U32, +z: U32, +hz: N.Le(1n+U32.to_nat(z), U32.to_nat(F)), h: {D.AL.cells(os, m, P, Q, zs, K, F, N) == True{} : Bool}) ->
  {D.Has(os, z) == False{} : Bool}:
  match os:
    case Nil{}:
      {==}
    case Con{+o, +rest}:
      +h2 = h
      +hle = al.hd.le(m, Q, o, F, N, K.al.hd(o, rest, m, P, Q, zs, K, F, N, h2))
      +ne = K.U.ne.sym(z, o, K.Ar.ne(z, o, N.le_trans(1n+U32.to_nat(z), U32.to_nat(F), U32.to_nat(o), hz, K.U.le(F, o, hle))))
      %Equal.sym(Bool, U32.is_eq(o, z), False{}, ne) : {Bool.or(_, D.Has(rest, z)) == False{} : Bool}
      has.ltF(rest, m, P, Q, zs, K, F, N, z, hz, K.al.rest(o, rest, m, P, Q, zs, K, F, N, h2))

# the facts of AL of the reused cell q
def q.al(+m: Cr.Cir.Cells, +q: U32, +Qr: List<&2, U32>, +P: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32, +nx: U32,
  +ws: List<&2, W1>, +pu: List<&2, U32>, +hq: {D.Has(P, q) == True{} : Bool}, +hsub: {D.Sub(Con{q, Qr}, P) == True{} : Bool},
  +hcs: {D.AL.cells(P, m, P, Con{q, Qr}, zs, K, F, nx) == True{} : Bool}, +hnp: {D.Nodup(P) == True{} : Bool},
  +hnqr: {D.Has(Qr, q) == False{} : Bool}, +hgq: {Gq(pu, P, Con{q, Qr}) == True{} : Bool}, +hpp: {Pts(pu, m, q) == True{} : Bool},
  +hpt: {W1s.pt(ws, m, q) == True{} : Bool}, +hdv: {Dv3(D.Am(m, q), q, m, W1s(ws, m), pu, Dn3(m, q)) == True{} : Bool},
  +hzq: N.Le(291n, U32.to_nat(q)), +hk: {U32.is_le(290, K) == True{} : Bool}, +hkf: {U32.is_lt(K, F) == True{} : Bool}, +tb: D.Tb(m)) ->
  {Bool.and(K.AL.hd(m, Con{q, Qr}, q, F, nx), Bool.and(K.AL.pt(m, P, zs, q, K, F, nx), K.AL.ct(m, P, Con{q, Qr}, q, F, nx))) == True{} : Bool}:
  al.mem(P, m, P, Con{q, Qr}, zs, K, F, nx, q, hq, hcs)

def q.hd(+m: Cr.Cir.Cells, +q: U32, +Qr: List<&2, U32>, +P: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32, +nx: U32,
  +ws: List<&2, W1>, +pu: List<&2, U32>, +hq: {D.Has(P, q) == True{} : Bool}, +hsub: {D.Sub(Con{q, Qr}, P) == True{} : Bool},
  +hcs: {D.AL.cells(P, m, P, Con{q, Qr}, zs, K, F, nx) == True{} : Bool}, +hnp: {D.Nodup(P) == True{} : Bool},
  +hnqr: {D.Has(Qr, q) == False{} : Bool}, +hgq: {Gq(pu, P, Con{q, Qr}) == True{} : Bool}, +hpp: {Pts(pu, m, q) == True{} : Bool},
  +hpt: {W1s.pt(ws, m, q) == True{} : Bool}, +hdv: {Dv3(D.Am(m, q), q, m, W1s(ws, m), pu, Dn3(m, q)) == True{} : Bool},
  +hzq: N.Le(291n, U32.to_nat(q)), +hk: {U32.is_le(290, K) == True{} : Bool}, +hkf: {U32.is_lt(K, F) == True{} : Bool}, +tb: D.Tb(m)) -> {K.AL.hd(m, Con{q, Qr}, q, F, nx) == True{} : Bool}:
  K.Bo.and_l(K.AL.hd(m, Con{q, Qr}, q, F, nx), Bool.and(K.AL.pt(m, P, zs, q, K, F, nx), K.AL.ct(m, P, Con{q, Qr}, q, F, nx)), q.al(m, q, Qr, P, zs, K, F, nx, ws, pu, hq, hsub, hcs, hnp, hnqr, hgq, hpp, hpt, hdv, hzq, hk, hkf, tb))

def q.pt(+m: Cr.Cir.Cells, +q: U32, +Qr: List<&2, U32>, +P: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32, +nx: U32,
  +ws: List<&2, W1>, +pu: List<&2, U32>, +hq: {D.Has(P, q) == True{} : Bool}, +hsub: {D.Sub(Con{q, Qr}, P) == True{} : Bool},
  +hcs: {D.AL.cells(P, m, P, Con{q, Qr}, zs, K, F, nx) == True{} : Bool}, +hnp: {D.Nodup(P) == True{} : Bool},
  +hnqr: {D.Has(Qr, q) == False{} : Bool}, +hgq: {Gq(pu, P, Con{q, Qr}) == True{} : Bool}, +hpp: {Pts(pu, m, q) == True{} : Bool},
  +hpt: {W1s.pt(ws, m, q) == True{} : Bool}, +hdv: {Dv3(D.Am(m, q), q, m, W1s(ws, m), pu, Dn3(m, q)) == True{} : Bool},
  +hzq: N.Le(291n, U32.to_nat(q)), +hk: {U32.is_le(290, K) == True{} : Bool}, +hkf: {U32.is_lt(K, F) == True{} : Bool}, +tb: D.Tb(m)) -> {K.AL.pt(m, P, zs, q, K, F, nx) == True{} : Bool}:
  K.Bo.and_l(K.AL.pt(m, P, zs, q, K, F, nx), K.AL.ct(m, P, Con{q, Qr}, q, F, nx), K.Bo.and_r(K.AL.hd(m, Con{q, Qr}, q, F, nx),
    Bool.and(K.AL.pt(m, P, zs, q, K, F, nx), K.AL.ct(m, P, Con{q, Qr}, q, F, nx)), q.al(m, q, Qr, P, zs, K, F, nx, ws, pu, hq, hsub, hcs, hnp, hnqr, hgq, hpp, hpt, hdv, hzq, hk, hkf, tb)))

def q.ct(+m: Cr.Cir.Cells, +q: U32, +Qr: List<&2, U32>, +P: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32, +nx: U32,
  +ws: List<&2, W1>, +pu: List<&2, U32>, +hq: {D.Has(P, q) == True{} : Bool}, +hsub: {D.Sub(Con{q, Qr}, P) == True{} : Bool},
  +hcs: {D.AL.cells(P, m, P, Con{q, Qr}, zs, K, F, nx) == True{} : Bool}, +hnp: {D.Nodup(P) == True{} : Bool},
  +hnqr: {D.Has(Qr, q) == False{} : Bool}, +hgq: {Gq(pu, P, Con{q, Qr}) == True{} : Bool}, +hpp: {Pts(pu, m, q) == True{} : Bool},
  +hpt: {W1s.pt(ws, m, q) == True{} : Bool}, +hdv: {Dv3(D.Am(m, q), q, m, W1s(ws, m), pu, Dn3(m, q)) == True{} : Bool},
  +hzq: N.Le(291n, U32.to_nat(q)), +hk: {U32.is_le(290, K) == True{} : Bool}, +hkf: {U32.is_lt(K, F) == True{} : Bool}, +tb: D.Tb(m)) -> {K.AL.ct(m, P, Con{q, Qr}, q, F, nx) == True{} : Bool}:
  K.Bo.and_r(K.AL.pt(m, P, zs, q, K, F, nx), K.AL.ct(m, P, Con{q, Qr}, q, F, nx), K.Bo.and_r(K.AL.hd(m, Con{q, Qr}, q, F, nx),
    Bool.and(K.AL.pt(m, P, zs, q, K, F, nx), K.AL.ct(m, P, Con{q, Qr}, q, F, nx)), q.al(m, q, Qr, P, zs, K, F, nx, ws, pu, hq, hsub, hcs, hnp, hnqr, hgq, hpp, hpt, hdv, hzq, hk, hkf, tb)))

# F <= q
def q.F(+m: Cr.Cir.Cells, +q: U32, +Qr: List<&2, U32>, +P: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32, +nx: U32,
  +ws: List<&2, W1>, +pu: List<&2, U32>, +hq: {D.Has(P, q) == True{} : Bool}, +hsub: {D.Sub(Con{q, Qr}, P) == True{} : Bool},
  +hcs: {D.AL.cells(P, m, P, Con{q, Qr}, zs, K, F, nx) == True{} : Bool}, +hnp: {D.Nodup(P) == True{} : Bool},
  +hnqr: {D.Has(Qr, q) == False{} : Bool}, +hgq: {Gq(pu, P, Con{q, Qr}) == True{} : Bool}, +hpp: {Pts(pu, m, q) == True{} : Bool},
  +hpt: {W1s.pt(ws, m, q) == True{} : Bool}, +hdv: {Dv3(D.Am(m, q), q, m, W1s(ws, m), pu, Dn3(m, q)) == True{} : Bool},
  +hzq: N.Le(291n, U32.to_nat(q)), +hk: {U32.is_le(290, K) == True{} : Bool}, +hkf: {U32.is_lt(K, F) == True{} : Bool}, +tb: D.Tb(m)) -> {U32.is_le(F, q) == True{} : Bool}:
  al.hd.le(m, Con{q, Qr}, q, F, nx, q.hd(m, q, Qr, P, zs, K, F, nx, ws, pu, hq, hsub, hcs, hnp, hnqr, hgq, hpp, hpt, hdv, hzq, hk, hkf, tb))

# 291 <= F
def F.big(+K: U32, +F: U32, hk: {U32.is_le(290, K) == True{} : Bool}, hkf: {U32.is_lt(K, F) == True{} : Bool}) -> N.Le(291n, U32.to_nat(F)):
  N.le_trans(291n, 1n+U32.to_nat(K), U32.to_nat(F), K.U.le(290, K, hk), K.U.lt(K, F, hkf))

# the first cell of the table
def tb.fst(+M: Cr.Cir.Cells, t: D.Tb(M)) -> {Cr.Cir.Cells.get(M, 272) == Cr.Cir.Cell{0, 0, 0, 0, 0} : Cr.Cir.Cell}:
  (t0, _) = t
  t0

# each cell of cs has fields 0 and 1 zero
def Z01(cs: List<&2, Cr.Cir.Cell>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{+c, rest}:
      Bool.and(Bool.and(U32.is_eq(Cr.Cir.Cell.get(0n, c), 0), U32.is_eq(Cr.Cir.Cell.get(1n, c), 0)), Z01(rest))

# a table cell (fields 0 and 1 zero, below F) is no part of q, so the writes
# keep it
def tbl.cell(+m: Cr.Cir.Cells, +q: U32, +Qr: List<&2, U32>, +P: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32, +nx: U32,
  +ws: List<&2, W1>, +pu: List<&2, U32>, +hq: {D.Has(P, q) == True{} : Bool}, +hsub: {D.Sub(Con{q, Qr}, P) == True{} : Bool},
  +hcs: {D.AL.cells(P, m, P, Con{q, Qr}, zs, K, F, nx) == True{} : Bool}, +hnp: {D.Nodup(P) == True{} : Bool},
  +hnqr: {D.Has(Qr, q) == False{} : Bool}, +hgq: {Gq(pu, P, Con{q, Qr}) == True{} : Bool}, +hpp: {Pts(pu, m, q) == True{} : Bool},
  +hpt: {W1s.pt(ws, m, q) == True{} : Bool}, +hdv: {Dv3(D.Am(m, q), q, m, W1s(ws, m), pu, Dn3(m, q)) == True{} : Bool},
  +hzq: N.Le(291n, U32.to_nat(q)), +hk: {U32.is_le(290, K) == True{} : Bool}, +hkf: {U32.is_lt(K, F) == True{} : Bool}, +tb: D.Tb(m), +i: U32, +c: Cr.Cir.Cell, +e: {Cr.Cir.Cells.get(m, i) == c : Cr.Cir.Cell},
  +e0: {Cr.Cir.Cell.get(0n, c) == 0 : U32}, +e1: {Cr.Cir.Cell.get(1n, c) == 0 : U32}, +lt: N.Le(1n+U32.to_nat(i), U32.to_nat(F)),
  +hi: N.Le(1n, U32.to_nat(i))) -> {D.Ow(m, q, i) == 0n : Nat}:
  +hs = {%Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(m, i), c, e) : {U32.is_ne(U32.and(Cr.Cir.Cell.get(0n, _), 1024), 0) == False{} : Bool};
    %Equal.sym(U32, Cr.Cir.Cell.get(0n, c), 0, e0) : {U32.is_ne(U32.and(_, 1024), 0) == False{} : Bool}; {==} : {D.Stc(m, i) == False{} : Bool}}
  +hc = {%Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(m, i), c, e) : {U32.to_nat(Cr.Cir.Cell.get(1n, _)) == 0n : Nat};
    %Equal.sym(U32, Cr.Cir.Cell.get(1n, c), 0, e1) : {U32.to_nat(_) == 0n : Nat}; {==} : {U32.to_nat(D.Fd(1n, m, i)) == 0n : Nat}}
  +hy0 = K.U.nz.of(U32.cmp(i, 0), U32.to_nat(i), K.U.rel(i, 0), hi)
  ow.zero(m, P, zs, q, K, F, nx, i, q.pt(m, q, Qr, P, zs, K, F, nx, ws, pu, hq, hsub, hcs, hnp, hnqr, hgq, hpp, hpt, hdv, hzq, hk, hkf, tb), hy0, hs, has.ltF(P, m, P, Con{q, Qr}, zs, K, F, nx, i, lt, hcs), hc)

def tbgo.zq(cs: List<&2, Cr.Cir.Cell>, +m: Cr.Cir.Cells, +q: U32, +Qr: List<&2, U32>, +P: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32, +nx: U32,
  +ws: List<&2, W1>, +pu: List<&2, U32>, +hq: {D.Has(P, q) == True{} : Bool}, +hsub: {D.Sub(Con{q, Qr}, P) == True{} : Bool},
  +hcs: {D.AL.cells(P, m, P, Con{q, Qr}, zs, K, F, nx) == True{} : Bool}, +hnp: {D.Nodup(P) == True{} : Bool},
  +hnqr: {D.Has(Qr, q) == False{} : Bool}, +hgq: {Gq(pu, P, Con{q, Qr}) == True{} : Bool}, +hpp: {Pts(pu, m, q) == True{} : Bool},
  +hpt: {W1s.pt(ws, m, q) == True{} : Bool}, +hdv: {Dv3(D.Am(m, q), q, m, W1s(ws, m), pu, Dn3(m, q)) == True{} : Bool},
  +hzq: N.Le(291n, U32.to_nat(q)), +hk: {U32.is_le(290, K) == True{} : Bool}, +hkf: {U32.is_lt(K, F) == True{} : Bool}, +tb: D.Tb(m), +i: U32, h: N.Le(Nat.add(U32.to_nat(i), List.length(&2, Cr.Cir.Cell, cs)), U32.to_nat(F)),
  +hi: N.Le(1n, U32.to_nat(i)), hz: {Z01(cs) == True{} : Bool}, t: D.Tb.go(m, i, cs)) -> D.Tb.go(Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), i, cs):
  match cs:
    case Nil{}:
      Unit{}
    case Con{+c, +rest}:
      (e0c, t2) = t
      +e = e0c
      +M = W1s(ws, m)
      +ms = Cr.Cir.Cells.set(M, q, Cr.Cir.Cell.zero())
      +Q2 = List.append(&2, U32, pu, Qr)
      +Q = {Con{q, Qr} : List<&2, U32>}
      +Dl = Del(P, q)
      +xi = U32.to_nat(i)
      +k = List.length(&2, Cr.Cir.Cell, rest)
      +h1 = N.le_rw_l(Nat.add(xi, 1n+k), 1n+Nat.add(xi, k), U32.to_nat(F), N.add_succ_r(xi, k), h)
      +lt = N.le_trans(1n+xi, 1n+Nat.add(xi, k), U32.to_nat(F), N.le_add_r(1n+xi, k), h1)
      +ei = K.Ar.u.inc(i, F, lt)
      +h2 = N.le_rw_l(1n+Nat.add(xi, k), Nat.add(U32.to_nat(U32.inc(i)), k), U32.to_nat(F),
        Equal.sym(Nat, Nat.add(U32.to_nat(U32.inc(i)), k), 1n+Nat.add(xi, k),
          Equal.cong(Nat, Nat, y => Nat.add(y, k), U32.to_nat(U32.inc(i)), 1n+xi, ei)), h1)
      +hz2 = hz
      +C01 = Bool.and(U32.is_eq(Cr.Cir.Cell.get(0n, c), 0), U32.is_eq(Cr.Cir.Cell.get(1n, c), 0))
      +c01 = K.Bo.and_l(C01, Z01(rest), hz2)
      +e0 = K.U.eq(Cr.Cir.Cell.get(0n, c), 0, K.Bo.and_l(U32.is_eq(Cr.Cir.Cell.get(0n, c), 0), U32.is_eq(Cr.Cir.Cell.get(1n, c), 0), c01))
      +e1 = K.U.eq(Cr.Cir.Cell.get(1n, c), 0, K.Bo.and_r(U32.is_eq(Cr.Cir.Cell.get(0n, c), 0), U32.is_eq(Cr.Cir.Cell.get(1n, c), 0), c01))
      +h0 = tbl.cell(m, q, Qr, P, zs, K, F, nx, ws, pu, hq, hsub, hcs, hnp, hnqr, hgq, hpp, hpt, hdv, hzq, hk, hkf, tb, i, c, e, e0, e1, lt, hi)
      +eM = w1s.get(ws, m, q, i, hpt, h0)
      +neq = K.Ar.ne(i, q, N.le_trans(1n+xi, U32.to_nat(F), U32.to_nat(q), lt, K.U.le(F, q, q.F(m, q, Qr, P, zs, K, F, nx, ws, pu, hq, hsub, hcs, hnp, hnqr, hgq, hpp, hpt, hdv, hzq, hk, hkf, tb))))
      +eS = K.Cl.get_ne(M, i, q, Cr.Cir.Cell.zero(), neq)
      (Equal.trans(Cr.Cir.Cell, Cr.Cir.Cells.get(ms, i), Cr.Cir.Cells.get(M, i), c, eS,
          Equal.trans(Cr.Cir.Cell, Cr.Cir.Cells.get(M, i), Cr.Cir.Cells.get(m, i), c, eM, e)),
        tbgo.zq(rest, m, q, Qr, P, zs, K, F, nx, ws, pu, hq, hsub, hcs, hnp, hnqr, hgq, hpp, hpt, hdv, hzq, hk, hkf, tb, U32.inc(i), h2,
          N.le_rw_r(1n, 1n+xi, U32.to_nat(U32.inc(i)), Equal.sym(Nat, U32.to_nat(U32.inc(i)), 1n+xi, ei), N.le_zero(xi)),
          K.Bo.and_r(C01, Z01(rest), hz2), t2))

# the table after a reuse
def tb.zq(+m: Cr.Cir.Cells, +q: U32, +Qr: List<&2, U32>, +P: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32, +nx: U32,
  +ws: List<&2, W1>, +pu: List<&2, U32>, +hq: {D.Has(P, q) == True{} : Bool}, +hsub: {D.Sub(Con{q, Qr}, P) == True{} : Bool},
  +hcs: {D.AL.cells(P, m, P, Con{q, Qr}, zs, K, F, nx) == True{} : Bool}, +hnp: {D.Nodup(P) == True{} : Bool},
  +hnqr: {D.Has(Qr, q) == False{} : Bool}, +hgq: {Gq(pu, P, Con{q, Qr}) == True{} : Bool}, +hpp: {Pts(pu, m, q) == True{} : Bool},
  +hpt: {W1s.pt(ws, m, q) == True{} : Bool}, +hdv: {Dv3(D.Am(m, q), q, m, W1s(ws, m), pu, Dn3(m, q)) == True{} : Bool},
  +hzq: N.Le(291n, U32.to_nat(q)), +hk: {U32.is_le(290, K) == True{} : Bool}, +hkf: {U32.is_lt(K, F) == True{} : Bool}, +tb: D.Tb(m)) -> D.Tb(Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero())):
  tbgo.zq(Mc.Img.table([]), m, q, Qr, P, zs, K, F, nx, ws, pu, hq, hsub, hcs, hnp, hnqr, hgq, hpp, hpt, hdv, hzq, hk, hkf, tb, 272, F.big(K, F, hk, hkf), N.le_zero(271n), {==}, tb)

# q holds no pointer after the reuse
def ps.zq0(+m: Cr.Cir.Cells, +q: U32, +Qr: List<&2, U32>, +P: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32, +nx: U32,
  +ws: List<&2, W1>, +pu: List<&2, U32>, +hq: {D.Has(P, q) == True{} : Bool}, +hsub: {D.Sub(Con{q, Qr}, P) == True{} : Bool},
  +hcs: {D.AL.cells(P, m, P, Con{q, Qr}, zs, K, F, nx) == True{} : Bool}, +hnp: {D.Nodup(P) == True{} : Bool},
  +hnqr: {D.Has(Qr, q) == False{} : Bool}, +hgq: {Gq(pu, P, Con{q, Qr}) == True{} : Bool}, +hpp: {Pts(pu, m, q) == True{} : Bool},
  +hpt: {W1s.pt(ws, m, q) == True{} : Bool}, +hdv: {Dv3(D.Am(m, q), q, m, W1s(ws, m), pu, Dn3(m, q)) == True{} : Bool},
  +hzq: N.Le(291n, U32.to_nat(q)), +hk: {U32.is_le(290, K) == True{} : Bool}, +hkf: {U32.is_lt(K, F) == True{} : Bool}, +tb: D.Tb(m)) -> {D.Ps(Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), List.append(&2, U32, pu, Qr), q) == Nil{} : List<&2, U32>}:
  +M = W1s(ws, m)
  +ms = Cr.Cir.Cells.set(M, q, Cr.Cir.Cell.zero())
  +Q2 = List.append(&2, U32, pu, Qr)
  +Q = {Con{q, Qr} : List<&2, U32>}
  +Dl = Del(P, q)
  +t0 = tb.fst(m, tb)
  +h0 = tbl.cell(m, q, Qr, P, zs, K, F, nx, ws, pu, hq, hsub, hcs, hnp, hnqr, hgq, hpp, hpt, hdv, hzq, hk, hkf, tb, 272, Cr.Cir.Cell{0, 0, 0, 0, 0}, t0, {==}, {==},
    N.le_trans(273n, 291n, U32.to_nat(F), N.le_zero(18n), F.big(K, F, hk, hkf)), N.le_zero(271n))
  +t0M = Equal.trans(Cr.Cir.Cell, Cr.Cir.Cells.get(M, 272), Cr.Cir.Cells.get(m, 272), Cr.Cir.Cell{0, 0, 0, 0, 0},
    w1s.get(ws, m, q, 272, hpt, h0), t0)
  K.ps.zero(M, q, Q2, t0M, hzq)


# q's old pointers: its parts by its mask, or none for a cell of the
# machine's own kinds in the pend list
def and.f(a: Bool) -> {Bool.and(a, False{}) == False{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def psh.in(+f0: U32, +t2: U32, +f2: U32, +f3: U32, +f4: U32, +ht: {U32.is_lt(U32.and(f0, 63), 19) == False{} : Bool}) ->
  {PsH(f0, t2, f2, f3, f4, True{}) == Nil{} : List<&2, U32>}:
  +tg = U32.and(f0, 63)
  +PT = D.Ps.term(t2, f2, f3, f4)
  +Y1 = Bool.and(U32.is_le(32, tg), U32.is_le(tg, 40))
  +Y2 = Bool.and(U32.is_eq(tg, 41), U32.is_ne(U32.and(f0, 4096), 0))
  +C1 = {Con{f2, D.Ps.opt(U32.is_eq(tg, 38), f3, Nil{})} : List<&2, U32>}
  %Equal.sym(Bool, U32.is_lt(tg, 19), False{}, ht) :
    {Bool.pick(List<&2, U32>, _, PT, Bool.pick(List<&2, U32>, Bool.and(Y1, False{}), C1, Bool.pick(List<&2, U32>, Bool.and(Y2, False{}), [f2], Nil{}))) ==
      Nil{} : List<&2, U32>}
  %Equal.sym(Bool, Bool.and(Y1, False{}), False{}, and.f(Y1)) :
    {Bool.pick(List<&2, U32>, _, C1, Bool.pick(List<&2, U32>, Bool.and(Y2, False{}), [f2], Nil{})) == Nil{} : List<&2, U32>}
  %Equal.sym(Bool, Bool.and(Y2, False{}), False{}, and.f(Y2)) : {Bool.pick(List<&2, U32>, _, [f2], Nil{}) == Nil{} : List<&2, U32>}
  {==}

# a < 19 gives a < 32; b <= a gives not a < b
def lt19.t32(+t: U32, h: {U32.is_lt(t, 19) == True{} : Bool}) -> {U32.is_lt(t, 32) == True{} : Bool}:
  K.U.lt_t(t, 32, N.le_trans(1n+U32.to_nat(t), 19n, 32n, K.U.lt(t, 19, h), N.le_zero(13n)))

def le.nlt.b(c: Bool, +a: U32, +b: U32, ec: {U32.is_lt(a, b) == c : Bool}, h: {U32.is_le(b, a) == True{} : Bool}) ->
  {U32.is_lt(a, b) == False{} : Bool}:
  match c:
    case True{}:
      K.U.lt_ge(a, b, {U32.is_lt(a, b) == False{} : Bool}, ec, h)
    case False{}:
      ec

def le18.f.b(c: Bool, +t: U32, ec: {U32.is_le(t, 18) == c : Bool}, h: {U32.is_lt(t, 19) == False{} : Bool}) -> {U32.is_le(t, 18) == False{} : Bool}:
  match c:
    case True{}:
      K.Bo.tf({U32.is_le(t, 18) == False{} : Bool}, Equal.trans(Bool, False{}, U32.is_lt(t, 19), True{}, Equal.sym(Bool, U32.is_lt(t, 19), False{}, h),
        K.U.lt_t(t, 19, K.U.le(t, 18, ec))))
    case False{}:
      ec

def ps.ow.t(+m: Cr.Cir.Cells, +Q: List<&2, U32>, +q: U32, +c: U32, +ht: {U32.is_lt(U32.and(D.Fd(0n, m, q), 63), 19) == True{} : Bool}) ->
  {D.Occ(D.Ps(m, Q, q), c) == D.Ow(m, q, c) : Nat}:
  +f0 = D.Fd(0n, m, q)
  +tg = U32.and(f0, 63)
  +a = D.Fd(2n, m, U32.add(272, tg))
  +f2 = D.Fd(2n, m, q)
  +f3 = D.Fd(3n, m, q)
  +f4 = D.Fd(4n, m, q)
  +b1 = U32.is_ne(U32.and(a, 1), 0)
  +b2 = U32.is_ne(U32.and(a, 2), 0)
  +b4 = U32.is_ne(U32.and(a, 4), 0)
  +PT = D.Ps.term(a, f2, f3, f4)
  +REST = Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_le(32, tg), U32.is_le(tg, 40)), Bool.not(D.Has(Q, q))),
    Con{f2, D.Ps.opt(U32.is_eq(tg, 38), f3, Nil{})},
    Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_eq(tg, 41), U32.is_ne(U32.and(f0, 4096), 0)), Bool.not(D.Has(Q, q))), [f2], Nil{}))
  +e1 = {(%Equal.sym(Bool, U32.is_lt(tg, 19), True{}, ht) : {Bool.pick(List<&2, U32>, _, PT, REST) == PT : List<&2, U32>}; {==}) :
    {D.Ps(m, Q, q) == PT : List<&2, U32>}}
  +eA = {(%Equal.sym(Bool, U32.is_lt(tg, 32), True{}, lt19.t32(tg, ht)) : {Bool.pick(U32, _, a, 0) == a : U32}; {==}) : {D.Am(m, q) == a : U32}}
  +A = D.Nat.of(Bool.and(b1, U32.is_eq(f2, c)))
  +B = D.Nat.of(Bool.and(b2, U32.is_eq(f3, c)))
  +C = D.Nat.of(Bool.and(b4, U32.is_eq(f4, c)))
  +O3 = D.Ps.opt(b4, f4, Nil{})
  +O2 = D.Ps.opt(b2, f3, O3)
  +eo = Equal.trans(Nat, D.Occ(PT, c), Nat.add(A, D.Occ(O2, c)), Nat.add(A, Nat.add(B, C)), occ.opt(b1, f2, O2, c),
    Equal.cong(Nat, Nat, z => Nat.add(A, z), D.Occ(O2, c), Nat.add(B, C), Equal.trans(Nat, D.Occ(O2, c), Nat.add(B, D.Occ(O3, c)), Nat.add(B, C),
      occ.opt(b2, f3, O3, c), Equal.cong(Nat, Nat, z => Nat.add(B, z), D.Occ(O3, c), C,
        Equal.trans(Nat, D.Occ(O3, c), Nat.add(C, 0n), C, occ.opt(b4, f4, Nil{}, c), N.add_zero(C))))))
  +eW = {(%Equal.sym(U32, D.Am(m, q), a, eA) :
      {Nat.add(D.Nat.of(Bool.and(U32.is_ne(U32.and(_, 1), 0), U32.is_eq(f2, c))), Nat.add(D.Nat.of(Bool.and(U32.is_ne(U32.and(_, 2), 0), U32.is_eq(f3, c))),
        D.Nat.of(Bool.and(U32.is_ne(U32.and(_, 4), 0), U32.is_eq(f4, c))))) == Nat.add(A, Nat.add(B, C)) : Nat}; {==}) :
    {D.Ow(m, q, c) == Nat.add(A, Nat.add(B, C)) : Nat}}
  Equal.trans(Nat, D.Occ(D.Ps(m, Q, q), c), D.Occ(PT, c), D.Ow(m, q, c), Equal.cong(List<&2, U32>, Nat, z => D.Occ(z, c), D.Ps(m, Q, q), PT, e1),
    Equal.trans(Nat, D.Occ(PT, c), Nat.add(A, Nat.add(B, C)), D.Ow(m, q, c), eo, Equal.sym(Nat, D.Ow(m, q, c), Nat.add(A, Nat.add(B, C)), eW)))

def ps.ow.o(+m: Cr.Cir.Cells, +Q: List<&2, U32>, +q: U32, +c: U32, +h19: {U32.is_lt(U32.and(D.Fd(0n, m, q), 63), 19) == False{} : Bool},
  +h32: {U32.is_le(32, U32.and(D.Fd(0n, m, q), 63)) == True{} : Bool}, +hq: {D.Has(Q, q) == True{} : Bool}) ->
  {D.Occ(D.Ps(m, Q, q), c) == D.Ow(m, q, c) : Nat}:
  +f0 = D.Fd(0n, m, q)
  +tg = U32.and(f0, 63)
  +t2 = D.Fd(2n, m, U32.add(272, tg))
  +f2 = D.Fd(2n, m, q)
  +f3 = D.Fd(3n, m, q)
  +f4 = D.Fd(4n, m, q)
  +eP = {(%hq : {D.Ps(m, Q, q) == PsH(f0, t2, f2, f3, f4, _) : List<&2, U32>}; ps.h(m, Q, q)) : {D.Ps(m, Q, q) == PsH(f0, t2, f2, f3, f4, True{}) : List<&2, U32>}}
  +eN = Equal.trans(List<&2, U32>, D.Ps(m, Q, q), PsH(f0, t2, f2, f3, f4, True{}), Nil{}, eP, psh.in(f0, t2, f2, f3, f4, h19))
  +eA = {(%Equal.sym(Bool, U32.is_lt(tg, 32), False{}, le.nlt.b(U32.is_lt(tg, 32), tg, 32, {==}, h32)) : {Bool.pick(U32, _, t2, 0) == 0 : U32}; {==}) :
    {D.Am(m, q) == 0 : U32}}
  +eW = {(%Equal.sym(U32, D.Am(m, q), 0, eA) :
      {Nat.add(D.Nat.of(Bool.and(U32.is_ne(U32.and(_, 1), 0), U32.is_eq(f2, c))), Nat.add(D.Nat.of(Bool.and(U32.is_ne(U32.and(_, 2), 0), U32.is_eq(f3, c))),
        D.Nat.of(Bool.and(U32.is_ne(U32.and(_, 4), 0), U32.is_eq(f4, c))))) == 0n : Nat}; {==}) : {D.Ow(m, q, c) == 0n : Nat}}
  Equal.trans(Nat, D.Occ(D.Ps(m, Q, q), c), 0n, D.Ow(m, q, c), Equal.cong(List<&2, U32>, Nat, z => D.Occ(z, c), D.Ps(m, Q, q), Nil{}, eN),
    Equal.sym(Nat, D.Ow(m, q, c), 0n, eW))

def ps.ow.b(t: Bool, +m: Cr.Cir.Cells, +q: U32, +Qr: List<&2, U32>, +P: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32, +nx: U32,
  +ws: List<&2, W1>, +pu: List<&2, U32>, +hq: {D.Has(P, q) == True{} : Bool}, +hsub: {D.Sub(Con{q, Qr}, P) == True{} : Bool},
  +hcs: {D.AL.cells(P, m, P, Con{q, Qr}, zs, K, F, nx) == True{} : Bool}, +hnp: {D.Nodup(P) == True{} : Bool},
  +hnqr: {D.Has(Qr, q) == False{} : Bool}, +hgq: {Gq(pu, P, Con{q, Qr}) == True{} : Bool}, +hpp: {Pts(pu, m, q) == True{} : Bool},
  +hpt: {W1s.pt(ws, m, q) == True{} : Bool}, +hdv: {Dv3(D.Am(m, q), q, m, W1s(ws, m), pu, Dn3(m, q)) == True{} : Bool},
  +hzq: N.Le(291n, U32.to_nat(q)), +hk: {U32.is_le(290, K) == True{} : Bool}, +hkf: {U32.is_lt(K, F) == True{} : Bool}, +tb: D.Tb(m), +c: U32, +et: {U32.is_lt(U32.and(D.Fd(0n, m, q), 63), 19) == t : Bool}) ->
  {D.Occ(D.Ps(m, Con{q, Qr}, q), c) == D.Ow(m, q, c) : Nat}:
  match t:
    case True{}:
      ps.ow.t(m, Con{q, Qr}, q, c, et)
    case False{}:
      +tg = U32.and(D.Fd(0n, m, q), 63)
      +hqq = {K.Bo.or_il(U32.is_eq(q, q), D.Has(Qr, q), K.U.eq_refl(q)) : {D.Has(Con{q, Qr}, q) == True{} : Bool}}
      +ht = K.al.hd.tg(m, Con{q, Qr}, q, F, nx, q.hd(m, q, Qr, P, zs, K, F, nx, ws, pu, hq, hsub, hcs, hnp, hnqr, hgq, hpp, hpt, hdv, hzq, hk, hkf, tb))
      +hb = K.Bo.or_r(U32.is_le(tg, 18), Bool.and(U32.is_le(32, tg), D.Has(Con{q, Qr}, q)), ht, le18.f.b(U32.is_le(tg, 18), tg, {==}, et))
      ps.ow.o(m, Con{q, Qr}, q, c, et, K.Bo.and_l(U32.is_le(32, tg), D.Has(Con{q, Qr}, q), hb), hqq)

def ps.ow.q(+m: Cr.Cir.Cells, +q: U32, +Qr: List<&2, U32>, +P: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32, +nx: U32,
  +ws: List<&2, W1>, +pu: List<&2, U32>, +hq: {D.Has(P, q) == True{} : Bool}, +hsub: {D.Sub(Con{q, Qr}, P) == True{} : Bool},
  +hcs: {D.AL.cells(P, m, P, Con{q, Qr}, zs, K, F, nx) == True{} : Bool}, +hnp: {D.Nodup(P) == True{} : Bool},
  +hnqr: {D.Has(Qr, q) == False{} : Bool}, +hgq: {Gq(pu, P, Con{q, Qr}) == True{} : Bool}, +hpp: {Pts(pu, m, q) == True{} : Bool},
  +hpt: {W1s.pt(ws, m, q) == True{} : Bool}, +hdv: {Dv3(D.Am(m, q), q, m, W1s(ws, m), pu, Dn3(m, q)) == True{} : Bool},
  +hzq: N.Le(291n, U32.to_nat(q)), +hk: {U32.is_le(290, K) == True{} : Bool}, +hkf: {U32.is_lt(K, F) == True{} : Bool}, +tb: D.Tb(m), +c: U32) -> {D.Occ(D.Ps(m, Con{q, Qr}, q), c) == D.Ow(m, q, c) : Nat}:
  ps.ow.b(U32.is_lt(U32.and(D.Fd(0n, m, q), 63), 19), m, q, Qr, P, zs, K, F, nx, ws, pu, hq, hsub, hcs, hnp, hnqr, hgq, hpp, hpt, hdv, hzq, hk, hkf, tb, c, {==})

# The pointers to a cell after a reuse: q's old ones go
# -----------------------------------------------------

# q once among the n cells from o
def Once(n: Nat, +o: U32, +q: U32) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+(+p):
      Bool.pick(Bool, U32.is_eq(o, q), K.Ne(p, U32.inc(o), q), Once(p, U32.inc(o), q))

def pc.ne(n: Nat, +m: Cr.Cir.Cells, +q: U32, +Qr: List<&2, U32>, +P: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32, +nx: U32,
  +ws: List<&2, W1>, +pu: List<&2, U32>, +hq: {D.Has(P, q) == True{} : Bool}, +hsub: {D.Sub(Con{q, Qr}, P) == True{} : Bool},
  +hcs: {D.AL.cells(P, m, P, Con{q, Qr}, zs, K, F, nx) == True{} : Bool}, +hnp: {D.Nodup(P) == True{} : Bool},
  +hnqr: {D.Has(Qr, q) == False{} : Bool}, +hgq: {Gq(pu, P, Con{q, Qr}) == True{} : Bool}, +hpp: {Pts(pu, m, q) == True{} : Bool},
  +hpt: {W1s.pt(ws, m, q) == True{} : Bool}, +hdv: {Dv3(D.Am(m, q), q, m, W1s(ws, m), pu, Dn3(m, q)) == True{} : Bool},
  +hzq: N.Le(291n, U32.to_nat(q)), +hk: {U32.is_le(290, K) == True{} : Bool}, +hkf: {U32.is_lt(K, F) == True{} : Bool}, +tb: D.Tb(m), +o: U32, +c: U32, hn: {K.Ne(n, o, q) == True{} : Bool}) ->
  {D.Pc(n, Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), List.append(&2, U32, pu, Qr), o, c) == D.Pc(n, m, Con{q, Qr}, o, c) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      +M = W1s(ws, m)
      +ms = Cr.Cir.Cells.set(M, q, Cr.Cir.Cell.zero())
      +Q2 = List.append(&2, U32, pu, Qr)
      +Q = {Con{q, Qr} : List<&2, U32>}
      +Dl = Del(P, q)

      +hn2 = hn
      +ne = K.Bo.not_t(U32.is_eq(o, q), K.Bo.and_l(Bool.not(U32.is_eq(o, q)), K.Ne(p, U32.inc(o), q), hn2))
      %Equal.sym(List<&2, U32>, D.Ps(ms, Q2, o), D.Ps(m, Q, o), ps.zq(m, q, Qr, P, zs, K, F, nx, ws, pu, hq, hsub, hcs, hnp, hnqr, hgq, hpp, hpt, hdv, hzq, hk, hkf, tb, o, ne)) :
        {Nat.add(D.Occ(_, c), D.Pc(p, ms, Q2, U32.inc(o), c)) == Nat.add(D.Occ(D.Ps(m, Q, o), c), D.Pc(p, m, Q, U32.inc(o), c)) : Nat}
      %Equal.sym(Nat, D.Pc(p, ms, Q2, U32.inc(o), c), D.Pc(p, m, Q, U32.inc(o), c),
        pc.ne(p, m, q, Qr, P, zs, K, F, nx, ws, pu, hq, hsub, hcs, hnp, hnqr, hgq, hpp, hpt, hdv, hzq, hk, hkf, tb, U32.inc(o), c, K.Bo.and_r(Bool.not(U32.is_eq(o, q)), K.Ne(p, U32.inc(o), q), hn2))) :
        {Nat.add(D.Occ(D.Ps(m, Q, o), c), _) == Nat.add(D.Occ(D.Ps(m, Q, o), c), D.Pc(p, m, Q, U32.inc(o), c)) : Nat}
      {==}

def pc.once.b(e: Bool, +p: Nat, +m: Cr.Cir.Cells, +q: U32, +Qr: List<&2, U32>, +P: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32, +nx: U32,
  +ws: List<&2, W1>, +pu: List<&2, U32>, +hq: {D.Has(P, q) == True{} : Bool}, +hsub: {D.Sub(Con{q, Qr}, P) == True{} : Bool},
  +hcs: {D.AL.cells(P, m, P, Con{q, Qr}, zs, K, F, nx) == True{} : Bool}, +hnp: {D.Nodup(P) == True{} : Bool},
  +hnqr: {D.Has(Qr, q) == False{} : Bool}, +hgq: {Gq(pu, P, Con{q, Qr}) == True{} : Bool}, +hpp: {Pts(pu, m, q) == True{} : Bool},
  +hpt: {W1s.pt(ws, m, q) == True{} : Bool}, +hdv: {Dv3(D.Am(m, q), q, m, W1s(ws, m), pu, Dn3(m, q)) == True{} : Bool},
  +hzq: N.Le(291n, U32.to_nat(q)), +hk: {U32.is_le(290, K) == True{} : Bool}, +hkf: {U32.is_lt(K, F) == True{} : Bool}, +tb: D.Tb(m), +o: U32, +c: U32, +eo: {U32.is_eq(o, q) == e : Bool},
  h: {Bool.pick(Bool, e, K.Ne(p, U32.inc(o), q), Once(p, U32.inc(o), q)) == True{} : Bool},
  k: {Once(p, U32.inc(o), q) == True{} : Bool} -> {Nat.add(D.Pc(p, Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), List.append(&2, U32, pu, Qr), U32.inc(o), c), D.Ow(m, q, c)) == D.Pc(p, m, Con{q, Qr}, U32.inc(o), c) : Nat}) ->
  {Nat.add(Nat.add(D.Occ(D.Ps(Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), List.append(&2, U32, pu, Qr), o), c), D.Pc(p, Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), List.append(&2, U32, pu, Qr), U32.inc(o), c)), D.Ow(m, q, c)) ==
    Nat.add(D.Occ(D.Ps(m, Con{q, Qr}, o), c), D.Pc(p, m, Con{q, Qr}, U32.inc(o), c)) : Nat}:
  match e:
    case True{}:
      +M = W1s(ws, m)
      +ms = Cr.Cir.Cells.set(M, q, Cr.Cir.Cell.zero())
      +Q2 = List.append(&2, U32, pu, Qr)
      +Q = {Con{q, Qr} : List<&2, U32>}
      +Dl = Del(P, q)

      +eq = Equal.sym(U32, o, q, K.U.eq(o, q, eo))
      +X = D.Pc(p, ms, Q2, U32.inc(o), c)
      +Y = D.Pc(p, m, Q, U32.inc(o), c)
      +W = D.Ow(m, q, c)
      +e0 = {(%eq : {D.Ps(ms, Q2, _) == Nil{} : List<&2, U32>}; ps.zq0(m, q, Qr, P, zs, K, F, nx, ws, pu, hq, hsub, hcs, hnp, hnqr, hgq, hpp, hpt, hdv, hzq, hk, hkf, tb)) : {D.Ps(ms, Q2, o) == Nil{} : List<&2, U32>}}
      +e1 = {(%eq : {D.Occ(D.Ps(m, Q, _), c) == W : Nat}; ps.ow.q(m, q, Qr, P, zs, K, F, nx, ws, pu, hq, hsub, hcs, hnp, hnqr, hgq, hpp, hpt, hdv, hzq, hk, hkf, tb, c)) : {D.Occ(D.Ps(m, Q, o), c) == W : Nat}}
      %Equal.sym(List<&2, U32>, D.Ps(ms, Q2, o), Nil{}, e0) : {Nat.add(Nat.add(D.Occ(_, c), X), W) == Nat.add(D.Occ(D.Ps(m, Q, o), c), Y) : Nat}
      %Equal.sym(Nat, D.Occ(D.Ps(m, Q, o), c), W, e1) : {Nat.add(X, W) == Nat.add(_, Y) : Nat}
      %Equal.sym(Nat, X, Y, pc.ne(p, m, q, Qr, P, zs, K, F, nx, ws, pu, hq, hsub, hcs, hnp, hnqr, hgq, hpp, hpt, hdv, hzq, hk, hkf, tb, U32.inc(o), c, h)) : {Nat.add(_, W) == Nat.add(W, Y) : Nat}
      Na.comm(Y, W)
    case False{}:
      +M = W1s(ws, m)
      +ms = Cr.Cir.Cells.set(M, q, Cr.Cir.Cell.zero())
      +Q2 = List.append(&2, U32, pu, Qr)
      +Q = {Con{q, Qr} : List<&2, U32>}
      +Dl = Del(P, q)

      +X = D.Pc(p, ms, Q2, U32.inc(o), c)
      +Y = D.Pc(p, m, Q, U32.inc(o), c)
      +W = D.Ow(m, q, c)
      +A = D.Occ(D.Ps(m, Q, o), c)
      %Equal.sym(List<&2, U32>, D.Ps(ms, Q2, o), D.Ps(m, Q, o), ps.zq(m, q, Qr, P, zs, K, F, nx, ws, pu, hq, hsub, hcs, hnp, hnqr, hgq, hpp, hpt, hdv, hzq, hk, hkf, tb, o, eo)) :
        {Nat.add(Nat.add(D.Occ(_, c), X), W) == Nat.add(A, Y) : Nat}
      Equal.trans(Nat, Nat.add(Nat.add(A, X), W), Nat.add(A, Nat.add(X, W)), Nat.add(A, Y), N.add_assoc(A, X, W),
        Equal.cong(Nat, Nat, z => Nat.add(A, z), Nat.add(X, W), Y, k(h)))

# the pointers to c of the n cells from o, q once among them: q's go
def pc.once(n: Nat, +m: Cr.Cir.Cells, +q: U32, +Qr: List<&2, U32>, +P: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32, +nx: U32,
  +ws: List<&2, W1>, +pu: List<&2, U32>, +hq: {D.Has(P, q) == True{} : Bool}, +hsub: {D.Sub(Con{q, Qr}, P) == True{} : Bool},
  +hcs: {D.AL.cells(P, m, P, Con{q, Qr}, zs, K, F, nx) == True{} : Bool}, +hnp: {D.Nodup(P) == True{} : Bool},
  +hnqr: {D.Has(Qr, q) == False{} : Bool}, +hgq: {Gq(pu, P, Con{q, Qr}) == True{} : Bool}, +hpp: {Pts(pu, m, q) == True{} : Bool},
  +hpt: {W1s.pt(ws, m, q) == True{} : Bool}, +hdv: {Dv3(D.Am(m, q), q, m, W1s(ws, m), pu, Dn3(m, q)) == True{} : Bool},
  +hzq: N.Le(291n, U32.to_nat(q)), +hk: {U32.is_le(290, K) == True{} : Bool}, +hkf: {U32.is_lt(K, F) == True{} : Bool}, +tb: D.Tb(m), +o: U32, +c: U32, h: {Once(n, o, q) == True{} : Bool}) ->
  {Nat.add(D.Pc(n, Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), List.append(&2, U32, pu, Qr), o, c), D.Ow(m, q, c)) == D.Pc(n, m, Con{q, Qr}, o, c) : Nat}:
  match n:
    case 0n:
      K.Bo.tf({Nat.add(0n, D.Ow(m, q, c)) == 0n : Nat}, h)
    case 1n+(+p):
      pc.once.b(U32.is_eq(o, q), p, m, q, Qr, P, zs, K, F, nx, ws, pu, hq, hsub, hcs, hnp, hnqr, hgq, hpp, hpt, hdv, hzq, hk, hkf, tb, o, c, {==}, h, h2 => pc.once(p, m, q, Qr, P, zs, K, F, nx, ws, pu, hq, hsub, hcs, hnp, hnqr, hgq, hpp, hpt, hdv, hzq, hk, hkf, tb, U32.inc(o), c, h2))

# the n cells from o, all above z and below N, are not z
def Ar.ne.above(n: Nat, +o: U32, +z: U32, +N: U32, hz: N.Le(1n+U32.to_nat(z), U32.to_nat(o)), hb: N.Le(Nat.add(U32.to_nat(o), n), U32.to_nat(N))) ->
  {K.Ne(n, o, z) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      +x = U32.to_nat(o)
      +hz2 = hz
      +h1 = N.le_rw_l(Nat.add(x, 1n+p), 1n+Nat.add(x, p), U32.to_nat(N), N.add_succ_r(x, p), hb)
      +lt = N.le_trans(1n+x, 1n+Nat.add(x, p), U32.to_nat(N), N.le_add_r(1n+x, p), h1)
      +ei = K.Ar.u.inc(o, N, lt)
      +h2 = N.le_rw_l(1n+Nat.add(x, p), Nat.add(U32.to_nat(U32.inc(o)), p), U32.to_nat(N),
        Equal.sym(Nat, Nat.add(U32.to_nat(U32.inc(o)), p), 1n+Nat.add(x, p), Equal.cong(Nat, Nat, y => Nat.add(y, p), U32.to_nat(U32.inc(o)), 1n+x, ei)), h1)
      +hz3 = N.le_rw_r(1n+U32.to_nat(z), 1n+x, U32.to_nat(U32.inc(o)), Equal.sym(Nat, U32.to_nat(U32.inc(o)), 1n+x, ei),
        N.le_succ(1n+U32.to_nat(z), x, hz2))
      K.Bo.and_i(Bool.not(U32.is_eq(o, z)), K.Ne(p, U32.inc(o), z), K.Bo.not_i(U32.is_eq(o, z), K.U.ne.sym(z, o, K.Ar.ne(z, o, hz2))),
        Ar.ne.above(p, U32.inc(o), z, N, hz3, h2))

# a <= b, not equal: a < b
def lt.of.ne.c(c: Cmp, +x: Nat, +y: Nat, r: N.Rel(c, x, y), h: N.Le(x, y), ne: {Cmp.is_eq(c) == False{} : Bool}) -> N.Le(1n+x, y):
  match c:
    case LT{}:
      r
    case EQ{}:
      K.Bo.ft(N.Le(1n+x, y), ne)
    case GT{}:
      Empty.absurd(N.Le(1n+x, y), N.not_succ_le(y, N.le_trans(1n+y, x, y, r, h)))

def lt.of.ne(+a: U32, +b: U32, h: N.Le(U32.to_nat(a), U32.to_nat(b)), ne: {U32.is_eq(a, b) == False{} : Bool}) -> N.Le(1n+U32.to_nat(a), U32.to_nat(b)):
  lt.of.ne.c(U32.cmp(a, b), U32.to_nat(a), U32.to_nat(b), K.U.rel(a, b), h, ne)

def once.at.b(e: Bool, +p: Nat, +o: U32, +q: U32, +N: U32, +eo: {U32.is_eq(o, q) == e : Bool}, +h1: N.Le(U32.to_nat(o), U32.to_nat(q)),
  +h2: N.Le(1n+U32.to_nat(q), Nat.add(U32.to_nat(o), 1n+p)), +ei: {U32.to_nat(U32.inc(o)) == 1n+U32.to_nat(o) : Nat},
  +eI: {1n+Nat.add(U32.to_nat(o), p) == Nat.add(U32.to_nat(U32.inc(o)), p) : Nat}, +hb2: N.Le(Nat.add(U32.to_nat(U32.inc(o)), p), U32.to_nat(N)),
  k: N.Le(U32.to_nat(U32.inc(o)), U32.to_nat(q)) -> N.Le(1n+U32.to_nat(q), Nat.add(U32.to_nat(U32.inc(o)), p)) ->
    N.Le(Nat.add(U32.to_nat(U32.inc(o)), p), U32.to_nat(N)) -> {Once(p, U32.inc(o), q) == True{} : Bool}) ->
  {Bool.pick(Bool, e, K.Ne(p, U32.inc(o), q), Once(p, U32.inc(o), q)) == True{} : Bool}:
  match e:
    case True{}:
      +x = U32.to_nat(o)
      +eq = K.U.eq(o, q, eo)
      +hz = {(%eq : N.Le(1n+U32.to_nat(_), U32.to_nat(U32.inc(o))); N.le_rw_r(1n+x, 1n+x, U32.to_nat(U32.inc(o)),
        Equal.sym(Nat, U32.to_nat(U32.inc(o)), 1n+x, ei), N.le_refl(1n+x))) : N.Le(1n+U32.to_nat(q), U32.to_nat(U32.inc(o)))}
      Ar.ne.above(p, U32.inc(o), q, N, hz, hb2)
    case False{}:
      +x = U32.to_nat(o)
      +hlt = lt.of.ne(o, q, h1, eo)
      k(N.le_rw_l(1n+x, U32.to_nat(U32.inc(o)), U32.to_nat(q), Equal.sym(Nat, U32.to_nat(U32.inc(o)), 1n+x, ei), hlt),
        N.le_rw_r(1n+U32.to_nat(q), Nat.add(x, 1n+p), Nat.add(U32.to_nat(U32.inc(o)), p), Equal.trans(Nat, Nat.add(x, 1n+p), 1n+Nat.add(x, p),
          Nat.add(U32.to_nat(U32.inc(o)), p), N.add_succ_r(x, p), eI), h2), hb2)

# q is once among the cells from o to N, when o <= q < N
def once.at(n: Nat, +o: U32, +q: U32, +N: U32, h1: N.Le(U32.to_nat(o), U32.to_nat(q)), h2: N.Le(1n+U32.to_nat(q), Nat.add(U32.to_nat(o), n)),
  hb: N.Le(Nat.add(U32.to_nat(o), n), U32.to_nat(N))) -> {Once(n, o, q) == True{} : Bool}:
  match n:
    case 0n:
      Empty.absurd({Once(0n, o, q) == True{} : Bool}, N.not_succ_le(U32.to_nat(q), N.le_trans(1n+U32.to_nat(q), U32.to_nat(o), U32.to_nat(q),
        N.le_rw_r(1n+U32.to_nat(q), Nat.add(U32.to_nat(o), 0n), U32.to_nat(o), N.add_zero(U32.to_nat(o)), h2), h1)))
    case 1n+(+p):
      +x = U32.to_nat(o)
      +h1b = N.le_rw_l(Nat.add(x, 1n+p), 1n+Nat.add(x, p), U32.to_nat(N), N.add_succ_r(x, p), hb)
      +lt = N.le_trans(1n+x, 1n+Nat.add(x, p), U32.to_nat(N), N.le_add_r(1n+x, p), h1b)
      +ei = K.Ar.u.inc(o, N, lt)
      +eI = Equal.sym(Nat, Nat.add(U32.to_nat(U32.inc(o)), p), 1n+Nat.add(x, p), Equal.cong(Nat, Nat, y => Nat.add(y, p), U32.to_nat(U32.inc(o)), 1n+x, ei))
      +hb2 = N.le_rw_l(1n+Nat.add(x, p), Nat.add(U32.to_nat(U32.inc(o)), p), U32.to_nat(N), eI, h1b)
      once.at.b(U32.is_eq(o, q), p, o, q, N, {==}, h1, h2, ei, eI, hb2, a => b => c => once.at(p, U32.inc(o), q, N, a, b, c))


# The pointers stay below next after a reuse
def lt.zq.b(e: Bool, +p: Nat, +m: Cr.Cir.Cells, +q: U32, +Qr: List<&2, U32>, +P: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32, +nx: U32,
  +ws: List<&2, W1>, +pu: List<&2, U32>, +hq: {D.Has(P, q) == True{} : Bool}, +hsub: {D.Sub(Con{q, Qr}, P) == True{} : Bool},
  +hcs: {D.AL.cells(P, m, P, Con{q, Qr}, zs, K, F, nx) == True{} : Bool}, +hnp: {D.Nodup(P) == True{} : Bool},
  +hnqr: {D.Has(Qr, q) == False{} : Bool}, +hgq: {Gq(pu, P, Con{q, Qr}) == True{} : Bool}, +hpp: {Pts(pu, m, q) == True{} : Bool},
  +hpt: {W1s.pt(ws, m, q) == True{} : Bool}, +hdv: {Dv3(D.Am(m, q), q, m, W1s(ws, m), pu, Dn3(m, q)) == True{} : Bool},
  +hzq: N.Le(291n, U32.to_nat(q)), +hk: {U32.is_le(290, K) == True{} : Bool}, +hkf: {U32.is_lt(K, F) == True{} : Bool}, +tb: D.Tb(m), +o: U32, +eo: {U32.is_eq(o, q) == e : Bool},
  h: {Bool.and(D.All.lt(D.Ps(m, Con{q, Qr}, o), nx), D.Lt(p, m, Con{q, Qr}, U32.inc(o), nx)) == True{} : Bool},
  k: {D.Lt(p, m, Con{q, Qr}, U32.inc(o), nx) == True{} : Bool} -> {D.Lt(p, Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), List.append(&2, U32, pu, Qr), U32.inc(o), nx) == True{} : Bool}) ->
  {Bool.and(D.All.lt(D.Ps(Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), List.append(&2, U32, pu, Qr), o), nx), D.Lt(p, Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), List.append(&2, U32, pu, Qr), U32.inc(o), nx)) == True{} : Bool}:
  match e:
    case True{}:
      +M = W1s(ws, m)
      +ms = Cr.Cir.Cells.set(M, q, Cr.Cir.Cell.zero())
      +Q2 = List.append(&2, U32, pu, Qr)
      +Q = {Con{q, Qr} : List<&2, U32>}
      +Dl = Del(P, q)

      +eq = Equal.sym(U32, o, q, K.U.eq(o, q, eo))
      +e0 = {(%eq : {D.Ps(ms, Q2, _) == Nil{} : List<&2, U32>}; ps.zq0(m, q, Qr, P, zs, K, F, nx, ws, pu, hq, hsub, hcs, hnp, hnqr, hgq, hpp, hpt, hdv, hzq, hk, hkf, tb)) : {D.Ps(ms, Q2, o) == Nil{} : List<&2, U32>}}
      %Equal.sym(List<&2, U32>, D.Ps(ms, Q2, o), Nil{}, e0) : {Bool.and(D.All.lt(_, nx), D.Lt(p, ms, Q2, U32.inc(o), nx)) == True{} : Bool}
      k(K.Bo.and_r(D.All.lt(D.Ps(m, Q, o), nx), D.Lt(p, m, Q, U32.inc(o), nx), h))
    case False{}:
      +M = W1s(ws, m)
      +ms = Cr.Cir.Cells.set(M, q, Cr.Cir.Cell.zero())
      +Q2 = List.append(&2, U32, pu, Qr)
      +Q = {Con{q, Qr} : List<&2, U32>}
      +Dl = Del(P, q)

      +h2 = h
      %Equal.sym(List<&2, U32>, D.Ps(ms, Q2, o), D.Ps(m, Q, o), ps.zq(m, q, Qr, P, zs, K, F, nx, ws, pu, hq, hsub, hcs, hnp, hnqr, hgq, hpp, hpt, hdv, hzq, hk, hkf, tb, o, eo)) :
        {Bool.and(D.All.lt(_, nx), D.Lt(p, ms, Q2, U32.inc(o), nx)) == True{} : Bool}
      K.Bo.and_i(D.All.lt(D.Ps(m, Q, o), nx), D.Lt(p, ms, Q2, U32.inc(o), nx), K.Bo.and_l(D.All.lt(D.Ps(m, Q, o), nx), D.Lt(p, m, Q, U32.inc(o), nx), h2),
        k(K.Bo.and_r(D.All.lt(D.Ps(m, Q, o), nx), D.Lt(p, m, Q, U32.inc(o), nx), h2)))

def lt.zq(n: Nat, +m: Cr.Cir.Cells, +q: U32, +Qr: List<&2, U32>, +P: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32, +nx: U32,
  +ws: List<&2, W1>, +pu: List<&2, U32>, +hq: {D.Has(P, q) == True{} : Bool}, +hsub: {D.Sub(Con{q, Qr}, P) == True{} : Bool},
  +hcs: {D.AL.cells(P, m, P, Con{q, Qr}, zs, K, F, nx) == True{} : Bool}, +hnp: {D.Nodup(P) == True{} : Bool},
  +hnqr: {D.Has(Qr, q) == False{} : Bool}, +hgq: {Gq(pu, P, Con{q, Qr}) == True{} : Bool}, +hpp: {Pts(pu, m, q) == True{} : Bool},
  +hpt: {W1s.pt(ws, m, q) == True{} : Bool}, +hdv: {Dv3(D.Am(m, q), q, m, W1s(ws, m), pu, Dn3(m, q)) == True{} : Bool},
  +hzq: N.Le(291n, U32.to_nat(q)), +hk: {U32.is_le(290, K) == True{} : Bool}, +hkf: {U32.is_lt(K, F) == True{} : Bool}, +tb: D.Tb(m), +o: U32, h: {D.Lt(n, m, Con{q, Qr}, o, nx) == True{} : Bool}) -> {D.Lt(n, Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), List.append(&2, U32, pu, Qr), o, nx) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      lt.zq.b(U32.is_eq(o, q), p, m, q, Qr, P, zs, K, F, nx, ws, pu, hq, hsub, hcs, hnp, hnqr, hgq, hpp, hpt, hdv, hzq, hk, hkf, tb, o, {==}, h, h2 => lt.zq(p, m, q, Qr, P, zs, K, F, nx, ws, pu, hq, hsub, hcs, hnp, hnqr, hgq, hpp, hpt, hdv, hzq, hk, hkf, tb, U32.inc(o), h2))

# What stays after a reuse
# ------------------------

# a cell but q keeps its fields 0 and 2 to 4
def same.zq(+m: Cr.Cir.Cells, +q: U32, +Qr: List<&2, U32>, +P: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32, +nx: U32,
  +ws: List<&2, W1>, +pu: List<&2, U32>, +y: U32, +ne: {U32.is_eq(y, q) == False{} : Bool}) -> {D.Same.at(m, Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), y) == True{} : Bool}:
  +ms = Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero())
  %Equal.sym(U32, D.Fd(0n, ms, y), D.Fd(0n, m, y), fd.zq(m, q, Qr, P, zs, K, F, nx, ws, pu, 0n, {==}, y, ne)) :
    {Bool.and(U32.is_eq(_, D.Fd(0n, m, y)), Bool.and(U32.is_eq(D.Fd(2n, ms, y), D.Fd(2n, m, y)),
      Bool.and(U32.is_eq(D.Fd(3n, ms, y), D.Fd(3n, m, y)), U32.is_eq(D.Fd(4n, ms, y), D.Fd(4n, m, y))))) == True{} : Bool}
  %Equal.sym(U32, D.Fd(2n, ms, y), D.Fd(2n, m, y), fd.zq(m, q, Qr, P, zs, K, F, nx, ws, pu, 2n, {==}, y, ne)) :
    {Bool.and(U32.is_eq(D.Fd(0n, m, y), D.Fd(0n, m, y)), Bool.and(U32.is_eq(_, D.Fd(2n, m, y)),
      Bool.and(U32.is_eq(D.Fd(3n, ms, y), D.Fd(3n, m, y)), U32.is_eq(D.Fd(4n, ms, y), D.Fd(4n, m, y))))) == True{} : Bool}
  %Equal.sym(U32, D.Fd(3n, ms, y), D.Fd(3n, m, y), fd.zq(m, q, Qr, P, zs, K, F, nx, ws, pu, 3n, {==}, y, ne)) :
    {Bool.and(U32.is_eq(D.Fd(0n, m, y), D.Fd(0n, m, y)), Bool.and(U32.is_eq(D.Fd(2n, m, y), D.Fd(2n, m, y)),
      Bool.and(U32.is_eq(_, D.Fd(3n, m, y)), U32.is_eq(D.Fd(4n, ms, y), D.Fd(4n, m, y))))) == True{} : Bool}
  %Equal.sym(U32, D.Fd(4n, ms, y), D.Fd(4n, m, y), fd.zq(m, q, Qr, P, zs, K, F, nx, ws, pu, 4n, {==}, y, ne)) :
    {Bool.and(U32.is_eq(D.Fd(0n, m, y), D.Fd(0n, m, y)), Bool.and(U32.is_eq(D.Fd(2n, m, y), D.Fd(2n, m, y)),
      Bool.and(U32.is_eq(D.Fd(3n, m, y), D.Fd(3n, m, y)), U32.is_eq(_, D.Fd(4n, m, y))))) == True{} : Bool}
  K.same.refl(m, y)

# c3 + ((Pcs + ow) + 0) = (c3 + ow) + (Pcs + 0)
def ar.kept(+c3: Nat, +ow: Nat, +pcs: Nat) -> {Nat.add(c3, Nat.add(Nat.add(pcs, ow), 0n)) == Nat.add(Nat.add(c3, ow), Nat.add(pcs, 0n)) : Nat}:
  %Equal.sym(Nat, Nat.add(Nat.add(pcs, ow), 0n), Nat.add(pcs, ow), N.add_zero(Nat.add(pcs, ow))) :
    {Nat.add(c3, _) == Nat.add(Nat.add(c3, ow), Nat.add(pcs, 0n)) : Nat}
  %Equal.sym(Nat, Nat.add(pcs, 0n), pcs, N.add_zero(pcs)) : {Nat.add(c3, Nat.add(pcs, ow)) == Nat.add(Nat.add(c3, ow), _) : Nat}
  Equal.trans(Nat, Nat.add(c3, Nat.add(pcs, ow)), Nat.add(c3, Nat.add(ow, pcs)), Nat.add(Nat.add(c3, ow), pcs),
    Equal.cong(Nat, Nat, z => Nat.add(c3, z), Nat.add(pcs, ow), Nat.add(ow, pcs), Na.comm(pcs, ow)),
    Equal.sym(Nat, Nat.add(Nat.add(c3, ow), pcs), Nat.add(c3, Nat.add(ow, pcs)), N.add_assoc(c3, ow, pcs)))

# a live term cell c, neither q nor STATIC nor garbage: its count lost q's
# pointers, as the pointers to it did
def kept.eq(+m: Cr.Cir.Cells, +q: U32, +Qr: List<&2, U32>, +P: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32, +nx: U32,
  +ws: List<&2, W1>, +pu: List<&2, U32>, +hq: {D.Has(P, q) == True{} : Bool}, +hsub: {D.Sub(Con{q, Qr}, P) == True{} : Bool},
  +hcs: {D.AL.cells(P, m, P, Con{q, Qr}, zs, K, F, nx) == True{} : Bool}, +hnp: {D.Nodup(P) == True{} : Bool},
  +hnqr: {D.Has(Qr, q) == False{} : Bool}, +hgq: {Gq(pu, P, Con{q, Qr}) == True{} : Bool}, +hpp: {Pts(pu, m, q) == True{} : Bool},
  +hpt: {W1s.pt(ws, m, q) == True{} : Bool}, +hdv: {Dv3(D.Am(m, q), q, m, W1s(ws, m), pu, Dn3(m, q)) == True{} : Bool},
  +hzq: N.Le(291n, U32.to_nat(q)), +hk: {U32.is_le(290, K) == True{} : Bool}, +hkf: {U32.is_lt(K, F) == True{} : Bool}, +tb: D.Tb(m), +c: U32, +hOnce: {Once(Nat.sub(U32.to_nat(nx), U32.to_nat(F)), F, q) == True{} : Bool}, +hFc: {U32.is_le(F, c) == True{} : Bool},
  +ne: {U32.is_eq(c, q) == False{} : Bool}, +hs: {D.Stc(m, c) == False{} : Bool}, +hD: {D.Has(Del(P, q), c) == False{} : Bool}) ->
  {Nat.is_eq(Nat.add(U32.to_nat(D.Fd(1n, Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), c)), Nat.add(D.Pc(Nat.sub(U32.to_nat(nx), U32.to_nat(F)), m, Con{q, Qr}, F, c), D.Occ(Nil{}, c))),
    Nat.add(U32.to_nat(D.Fd(1n, m, c)), Nat.add(D.Pc(Nat.sub(U32.to_nat(nx), U32.to_nat(F)), Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), List.append(&2, U32, pu, Qr), F, c), D.Occ(Nil{}, c)))) == True{} : Bool}:
  +M = W1s(ws, m)
  +ms = Cr.Cir.Cells.set(M, q, Cr.Cir.Cell.zero())
  +Q2 = List.append(&2, U32, pu, Qr)
  +Q = {Con{q, Qr} : List<&2, U32>}
  +Dl = Del(P, q)
  +n = Nat.sub(U32.to_nat(nx), U32.to_nat(F))
  +ow = D.Ow(m, q, c)
  +hP = {(%has.del(P, q, c, ne) : {_ == False{} : Bool}; hD) : {D.Has(P, c) == False{} : Bool}}
  +hpu = K.sub.nhas(pu, P, c, gq.sub(pu, P, Q, hgq), hP)
  +hv = dv.all(m, q, ws, pu, c, K.U.nz(c, K, F, hkf, hFc), hdv, hpt, hpp)
  +e3 = dv.ne(m, M, pu, c, ow, hs, hpu, hv)
  +ep = pc.once(n, m, q, Qr, P, zs, K, F, nx, ws, pu, hq, hsub, hcs, hnp, hnqr, hgq, hpp, hpt, hdv, hzq, hk, hkf, tb, F, c, hOnce)
  +c3 = U32.to_nat(D.Fd(1n, M, c))
  +pcs = D.Pc(n, ms, Q2, F, c)
  %Equal.sym(U32, D.Fd(1n, ms, c), D.Fd(1n, M, c), f1.zq(m, q, Qr, P, zs, K, F, nx, ws, pu, c, ne)) :
    {Nat.is_eq(Nat.add(U32.to_nat(_), Nat.add(D.Pc(n, m, Q, F, c), 0n)), Nat.add(U32.to_nat(D.Fd(1n, m, c)), Nat.add(pcs, 0n))) == True{} : Bool}
  %ep : {Nat.is_eq(Nat.add(c3, Nat.add(_, 0n)), Nat.add(U32.to_nat(D.Fd(1n, m, c)), Nat.add(pcs, 0n))) == True{} : Bool}
  %e3 : {Nat.is_eq(Nat.add(c3, Nat.add(Nat.add(pcs, ow), 0n)), Nat.add(_, Nat.add(pcs, 0n))) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(c3, Nat.add(Nat.add(pcs, ow), 0n)), Nat.add(Nat.add(c3, ow), Nat.add(pcs, 0n)), ar.kept(c3, ow, pcs)) :
    {Nat.is_eq(_, Nat.add(Nat.add(c3, ow), Nat.add(pcs, 0n))) == True{} : Bool}
  K.Na.eq_refl(Nat.add(Nat.add(c3, ow), Nat.add(pcs, 0n)))


def kept.or(g: Bool, +m: Cr.Cir.Cells, +q: U32, +Qr: List<&2, U32>, +P: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32, +nx: U32,
  +ws: List<&2, W1>, +pu: List<&2, U32>, +hq: {D.Has(P, q) == True{} : Bool}, +hsub: {D.Sub(Con{q, Qr}, P) == True{} : Bool},
  +hcs: {D.AL.cells(P, m, P, Con{q, Qr}, zs, K, F, nx) == True{} : Bool}, +hnp: {D.Nodup(P) == True{} : Bool},
  +hnqr: {D.Has(Qr, q) == False{} : Bool}, +hgq: {Gq(pu, P, Con{q, Qr}) == True{} : Bool}, +hpp: {Pts(pu, m, q) == True{} : Bool},
  +hpt: {W1s.pt(ws, m, q) == True{} : Bool}, +hdv: {Dv3(D.Am(m, q), q, m, W1s(ws, m), pu, Dn3(m, q)) == True{} : Bool},
  +hzq: N.Le(291n, U32.to_nat(q)), +hk: {U32.is_le(290, K) == True{} : Bool}, +hkf: {U32.is_lt(K, F) == True{} : Bool}, +tb: D.Tb(m), +c: U32, +hOnce: {Once(Nat.sub(U32.to_nat(nx), U32.to_nat(F)), F, q) == True{} : Bool}, +hFc: {U32.is_le(F, c) == True{} : Bool},
  +ne: {U32.is_eq(c, q) == False{} : Bool},
  +eg: {Bool.or(U32.is_le(19, U32.and(D.Fd(0n, m, c), 63)), Bool.or(D.Stc(m, c), D.Has(Del(P, q), c))) == g : Bool}) ->
  {Bool.or(Bool.or(U32.is_le(19, U32.and(D.Fd(0n, m, c), 63)), Bool.or(D.Stc(m, c), D.Has(Del(P, q), c))),
    Nat.is_eq(Nat.add(U32.to_nat(D.Fd(1n, Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), c)), Nat.add(D.Pc(Nat.sub(U32.to_nat(nx), U32.to_nat(F)), m, Con{q, Qr}, F, c), D.Occ(Nil{}, c))),
      Nat.add(U32.to_nat(D.Fd(1n, m, c)), Nat.add(D.Pc(Nat.sub(U32.to_nat(nx), U32.to_nat(F)), Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), List.append(&2, U32, pu, Qr), F, c), D.Occ(Nil{}, c))))) == True{} : Bool}:
  match g:
    case True{}:
      +G = Bool.or(U32.is_le(19, U32.and(D.Fd(0n, m, c), 63)), Bool.or(D.Stc(m, c), D.Has(Del(P, q), c)))
      +Eq = Nat.is_eq(Nat.add(U32.to_nat(D.Fd(1n, Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), c)), Nat.add(D.Pc(Nat.sub(U32.to_nat(nx), U32.to_nat(F)), m, Con{q, Qr}, F, c), D.Occ(Nil{}, c))),
        Nat.add(U32.to_nat(D.Fd(1n, m, c)), Nat.add(D.Pc(Nat.sub(U32.to_nat(nx), U32.to_nat(F)), Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), List.append(&2, U32, pu, Qr), F, c), D.Occ(Nil{}, c))))
      K.Bo.or_il(G, Eq, eg)
    case False{}:
      +G = Bool.or(U32.is_le(19, U32.and(D.Fd(0n, m, c), 63)), Bool.or(D.Stc(m, c), D.Has(Del(P, q), c)))
      +Eq = Nat.is_eq(Nat.add(U32.to_nat(D.Fd(1n, Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), c)), Nat.add(D.Pc(Nat.sub(U32.to_nat(nx), U32.to_nat(F)), m, Con{q, Qr}, F, c), D.Occ(Nil{}, c))),
        Nat.add(U32.to_nat(D.Fd(1n, m, c)), Nat.add(D.Pc(Nat.sub(U32.to_nat(nx), U32.to_nat(F)), Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), List.append(&2, U32, pu, Qr), F, c), D.Occ(Nil{}, c))))
      +g2 = K.or.fr(U32.is_le(19, U32.and(D.Fd(0n, m, c), 63)), Bool.or(D.Stc(m, c), D.Has(Del(P, q), c)), eg)
      K.Bo.or_ir(G, Eq, kept.eq(m, q, Qr, P, zs, K, F, nx, ws, pu, hq, hsub, hcs, hnp, hnqr, hgq, hpp, hpt, hdv, hzq, hk, hkf, tb, c, hOnce, hFc, ne, K.or.fl(D.Stc(m, c), D.Has(Del(P, q), c), g2), K.or.fr(D.Stc(m, c), D.Has(Del(P, q), c), g2)))

def kept.cell.e(e: Bool, +m: Cr.Cir.Cells, +q: U32, +Qr: List<&2, U32>, +P: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32, +nx: U32,
  +ws: List<&2, W1>, +pu: List<&2, U32>, +hq: {D.Has(P, q) == True{} : Bool}, +hsub: {D.Sub(Con{q, Qr}, P) == True{} : Bool},
  +hcs: {D.AL.cells(P, m, P, Con{q, Qr}, zs, K, F, nx) == True{} : Bool}, +hnp: {D.Nodup(P) == True{} : Bool},
  +hnqr: {D.Has(Qr, q) == False{} : Bool}, +hgq: {Gq(pu, P, Con{q, Qr}) == True{} : Bool}, +hpp: {Pts(pu, m, q) == True{} : Bool},
  +hpt: {W1s.pt(ws, m, q) == True{} : Bool}, +hdv: {Dv3(D.Am(m, q), q, m, W1s(ws, m), pu, Dn3(m, q)) == True{} : Bool},
  +hzq: N.Le(291n, U32.to_nat(q)), +hk: {U32.is_le(290, K) == True{} : Bool}, +hkf: {U32.is_lt(K, F) == True{} : Bool}, +tb: D.Tb(m), +c: U32, +ee: {U32.is_eq(q, c) == e : Bool}, +hOnce: {Once(Nat.sub(U32.to_nat(nx), U32.to_nat(F)), F, q) == True{} : Bool},
  +hFc: {U32.is_le(F, c) == True{} : Bool}) ->
  {Bool.or(D.Has([q], c), Bool.and(D.Same.at(m, Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), c), Bool.or(Bool.or(U32.is_le(19, U32.and(D.Fd(0n, m, c), 63)),
    Bool.or(D.Stc(m, c), D.Has(Del(P, q), c))), Nat.is_eq(Nat.add(U32.to_nat(D.Fd(1n, Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), c)), Nat.add(D.Pc(Nat.sub(U32.to_nat(nx), U32.to_nat(F)), m, Con{q, Qr}, F, c), D.Occ(Nil{}, c))),
    Nat.add(U32.to_nat(D.Fd(1n, m, c)), Nat.add(D.Pc(Nat.sub(U32.to_nat(nx), U32.to_nat(F)), Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), List.append(&2, U32, pu, Qr), F, c), D.Occ(Nil{}, c))))))) == True{} : Bool}:
  match e:
    case True{}:
      +G = Bool.or(U32.is_le(19, U32.and(D.Fd(0n, m, c), 63)), Bool.or(D.Stc(m, c), D.Has(Del(P, q), c)))
      +Eq = Nat.is_eq(Nat.add(U32.to_nat(D.Fd(1n, Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), c)), Nat.add(D.Pc(Nat.sub(U32.to_nat(nx), U32.to_nat(F)), m, Con{q, Qr}, F, c), D.Occ(Nil{}, c))),
        Nat.add(U32.to_nat(D.Fd(1n, m, c)), Nat.add(D.Pc(Nat.sub(U32.to_nat(nx), U32.to_nat(F)), Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), List.append(&2, U32, pu, Qr), F, c), D.Occ(Nil{}, c))))
      +Sa = D.Same.at(m, Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), c)
      K.Bo.or_il(D.Has([q], c), Bool.and(Sa, Bool.or(G, Eq)),
        (%Equal.sym(Bool, U32.is_eq(q, c), True{}, ee) : {Bool.or(_, False{}) == True{} : Bool}; {==}))
    case False{}:
      +G = Bool.or(U32.is_le(19, U32.and(D.Fd(0n, m, c), 63)), Bool.or(D.Stc(m, c), D.Has(Del(P, q), c)))
      +Eq = Nat.is_eq(Nat.add(U32.to_nat(D.Fd(1n, Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), c)), Nat.add(D.Pc(Nat.sub(U32.to_nat(nx), U32.to_nat(F)), m, Con{q, Qr}, F, c), D.Occ(Nil{}, c))),
        Nat.add(U32.to_nat(D.Fd(1n, m, c)), Nat.add(D.Pc(Nat.sub(U32.to_nat(nx), U32.to_nat(F)), Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), List.append(&2, U32, pu, Qr), F, c), D.Occ(Nil{}, c))))
      +Sa = D.Same.at(m, Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), c)
      +ne = K.U.ne.sym(q, c, ee)
      K.Bo.or_ir(D.Has([q], c), Bool.and(Sa, Bool.or(G, Eq)), K.Bo.and_i(Sa, Bool.or(G, Eq), same.zq(m, q, Qr, P, zs, K, F, nx, ws, pu, c, ne),
        kept.or(G, m, q, Qr, P, zs, K, F, nx, ws, pu, hq, hsub, hcs, hnp, hnqr, hgq, hpp, hpt, hdv, hzq, hk, hkf, tb, c, hOnce, hFc, ne, {==})))

# Kept of the n cells from o after a reuse
def kept.zq(k: Nat, +m: Cr.Cir.Cells, +q: U32, +Qr: List<&2, U32>, +P: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32, +nx: U32,
  +ws: List<&2, W1>, +pu: List<&2, U32>, +hq: {D.Has(P, q) == True{} : Bool}, +hsub: {D.Sub(Con{q, Qr}, P) == True{} : Bool},
  +hcs: {D.AL.cells(P, m, P, Con{q, Qr}, zs, K, F, nx) == True{} : Bool}, +hnp: {D.Nodup(P) == True{} : Bool},
  +hnqr: {D.Has(Qr, q) == False{} : Bool}, +hgq: {Gq(pu, P, Con{q, Qr}) == True{} : Bool}, +hpp: {Pts(pu, m, q) == True{} : Bool},
  +hpt: {W1s.pt(ws, m, q) == True{} : Bool}, +hdv: {Dv3(D.Am(m, q), q, m, W1s(ws, m), pu, Dn3(m, q)) == True{} : Bool},
  +hzq: N.Le(291n, U32.to_nat(q)), +hk: {U32.is_le(290, K) == True{} : Bool}, +hkf: {U32.is_lt(K, F) == True{} : Bool}, +tb: D.Tb(m), +o: U32, +hOnce: {Once(Nat.sub(U32.to_nat(nx), U32.to_nat(F)), F, q) == True{} : Bool}, +hFo: N.Le(U32.to_nat(F), U32.to_nat(o)),
  hb: N.Le(Nat.add(U32.to_nat(o), k), U32.to_nat(nx))) ->
  {D.Kept(k, m, Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), o, [q], Del(P, q), F, Nat.sub(U32.to_nat(nx), U32.to_nat(F)), Nat.sub(U32.to_nat(nx), U32.to_nat(F)), Con{q, Qr}, List.append(&2, U32, pu, Qr), Nil{}, Nil{}) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+(+p):
      +x = U32.to_nat(o)
      +h1 = N.le_rw_l(Nat.add(x, 1n+p), 1n+Nat.add(x, p), U32.to_nat(nx), N.add_succ_r(x, p), hb)
      +lt = N.le_trans(1n+x, 1n+Nat.add(x, p), U32.to_nat(nx), N.le_add_r(1n+x, p), h1)
      +ei = K.Ar.u.inc(o, nx, lt)
      +h2 = N.le_rw_l(1n+Nat.add(x, p), Nat.add(U32.to_nat(U32.inc(o)), p), U32.to_nat(nx),
        Equal.sym(Nat, Nat.add(U32.to_nat(U32.inc(o)), p), 1n+Nat.add(x, p), Equal.cong(Nat, Nat, y => Nat.add(y, p), U32.to_nat(U32.inc(o)), 1n+x, ei)), h1)
      +hFo2 = N.le_rw_r(U32.to_nat(F), 1n+x, U32.to_nat(U32.inc(o)), Equal.sym(Nat, U32.to_nat(U32.inc(o)), 1n+x, ei), N.le_succ(U32.to_nat(F), x, hFo))
      K.Bo.and_i(Bool.or(D.Has([q], o), Bool.and(D.Same.at(m, Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), o), Bool.or(Bool.or(U32.is_le(19, U32.and(D.Fd(0n, m, o), 63)),
    Bool.or(D.Stc(m, o), D.Has(Del(P, q), o))), Nat.is_eq(Nat.add(U32.to_nat(D.Fd(1n, Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), o)), Nat.add(D.Pc(Nat.sub(U32.to_nat(nx), U32.to_nat(F)), m, Con{q, Qr}, F, o), D.Occ(Nil{}, o))),
    Nat.add(U32.to_nat(D.Fd(1n, m, o)), Nat.add(D.Pc(Nat.sub(U32.to_nat(nx), U32.to_nat(F)), Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), List.append(&2, U32, pu, Qr), F, o), D.Occ(Nil{}, o))))))), D.Kept(p, m, Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), U32.inc(o), [q], Del(P, q), F, Nat.sub(U32.to_nat(nx), U32.to_nat(F)), Nat.sub(U32.to_nat(nx), U32.to_nat(F)), Con{q, Qr}, List.append(&2, U32, pu, Qr), Nil{}, Nil{}),
        kept.cell.e(U32.is_eq(q, o), m, q, Qr, P, zs, K, F, nx, ws, pu, hq, hsub, hcs, hnp, hnqr, hgq, hpp, hpt, hdv, hzq, hk, hkf, tb, o, {==}, hOnce, K.U.le_t(F, o, hFo)), kept.zq(p, m, q, Qr, P, zs, K, F, nx, ws, pu, hq, hsub, hcs, hnp, hnqr, hgq, hpp, hpt, hdv, hzq, hk, hkf, tb, U32.inc(o), hOnce, hFo2, h2))


# The garbage after a reuse
# -------------------------

# nothing of the garbage points to q, so no garbage cell has q as a part
def le0.eq(a: Nat, h: N.Le(a, 0n)) -> {a == 0n : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Empty.absurd({1n+p == 0n : Nat}, h)

def Na.add0l(a: Nat, +b: Nat, h: {Nat.add(a, b) == 0n : Nat}) -> {a == 0n : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Empty.absurd({1n+p == 0n : Nat}, N.not_succ_le(0n, (%h : N.Le(1n, _); N.le_zero(Nat.add(p, b)))))

def nof.z(b: Bool, h: {D.Nat.of(b) == 0n : Nat}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, N.not_succ_le(0n, (%h : N.Le(1n, _); N.le_refl(1n))))
    case False{}:
      {==}

def q.pp0(+m: Cr.Cir.Cells, +q: U32, +Qr: List<&2, U32>, +P: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32, +nx: U32,
  +ws: List<&2, W1>, +pu: List<&2, U32>, +hq: {D.Has(P, q) == True{} : Bool}, +hsub: {D.Sub(Con{q, Qr}, P) == True{} : Bool},
  +hcs: {D.AL.cells(P, m, P, Con{q, Qr}, zs, K, F, nx) == True{} : Bool}, +hnp: {D.Nodup(P) == True{} : Bool},
  +hnqr: {D.Has(Qr, q) == False{} : Bool}, +hgq: {Gq(pu, P, Con{q, Qr}) == True{} : Bool}, +hpp: {Pts(pu, m, q) == True{} : Bool},
  +hpt: {W1s.pt(ws, m, q) == True{} : Bool}, +hdv: {Dv3(D.Am(m, q), q, m, W1s(ws, m), pu, Dn3(m, q)) == True{} : Bool},
  +hzq: N.Le(291n, U32.to_nat(q)), +hk: {U32.is_le(290, K) == True{} : Bool}, +hkf: {U32.is_lt(K, F) == True{} : Bool}, +tb: D.Tb(m)) -> {D.Pp(P, m, q) == 0n : Nat}:
  +pp = D.Pp(P, m, q)
  +c0 = U32.to_nat(D.Fd(1n, m, q))
  +hqq = {K.Bo.or_il(U32.is_eq(q, q), D.Has(Qr, q), K.U.eq_refl(q)) : {D.Has(Con{q, Qr}, q) == True{} : Bool}}
  +h1 = K.Bo.and_r(Nat.is_eq(D.Pc(Nat.sub(U32.to_nat(nx), U32.to_nat(F)), m, Con{q, Qr}, F, q), pp), Bool.pick(Bool, D.Has(Con{q, Qr}, q), Nat.is_eq(pp, 0n),
    Bool.and(Nat.is_eq(pp, c0), Nat.is_lt(0n, pp))), q.ct(m, q, Qr, P, zs, K, F, nx, ws, pu, hq, hsub, hcs, hnp, hnqr, hgq, hpp, hpt, hdv, hzq, hk, hkf, tb))
  K.Na.eq(pp, 0n, (%hqq : {Bool.pick(Bool, _, Nat.is_eq(pp, 0n), Bool.and(Nat.is_eq(pp, c0), Nat.is_lt(0n, pp))) == True{} : Bool}; h1))

def ow.q0(+m: Cr.Cir.Cells, +q: U32, +Qr: List<&2, U32>, +P: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32, +nx: U32,
  +ws: List<&2, W1>, +pu: List<&2, U32>, +hq: {D.Has(P, q) == True{} : Bool}, +hsub: {D.Sub(Con{q, Qr}, P) == True{} : Bool},
  +hcs: {D.AL.cells(P, m, P, Con{q, Qr}, zs, K, F, nx) == True{} : Bool}, +hnp: {D.Nodup(P) == True{} : Bool},
  +hnqr: {D.Has(Qr, q) == False{} : Bool}, +hgq: {Gq(pu, P, Con{q, Qr}) == True{} : Bool}, +hpp: {Pts(pu, m, q) == True{} : Bool},
  +hpt: {W1s.pt(ws, m, q) == True{} : Bool}, +hdv: {Dv3(D.Am(m, q), q, m, W1s(ws, m), pu, Dn3(m, q)) == True{} : Bool},
  +hzq: N.Le(291n, U32.to_nat(q)), +hk: {U32.is_le(290, K) == True{} : Bool}, +hkf: {U32.is_lt(K, F) == True{} : Bool}, +tb: D.Tb(m), +o: U32, +hP: {D.Has(P, o) == True{} : Bool}) -> {D.Ow(m, o, q) == 0n : Nat}:
  le0.eq(D.Ow(m, o, q), (%q.pp0(m, q, Qr, P, zs, K, F, nx, ws, pu, hq, hsub, hcs, hnp, hnqr, hgq, hpp, hpt, hdv, hzq, hk, hkf, tb) : N.Le(D.Ow(m, o, q), _); pp.ge(P, m, o, q, hP)))

# cells of a list: in the list and its extensions
def sub.cons(xs: List<&2, U32>, +y: U32, +ys: List<&2, U32>, h: {D.Sub(xs, ys) == True{} : Bool}) -> {D.Sub(xs, Con{y, ys}) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      +h2 = h
      K.Bo.and_i(D.Has(Con{y, ys}, x), D.Sub(rest, Con{y, ys}),
        K.Bo.or_ir(U32.is_eq(y, x), D.Has(ys, x), K.Bo.and_l(D.Has(ys, x), D.Sub(rest, ys), h2)),
        sub.cons(rest, y, ys, K.Bo.and_r(D.Has(ys, x), D.Sub(rest, ys), h2)))

def sub.refl(xs: List<&2, U32>) -> {D.Sub(xs, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      K.Bo.and_i(D.Has(Con{x, rest}, x), D.Sub(rest, Con{x, rest}), K.Bo.or_il(U32.is_eq(x, x), D.Has(rest, x), K.U.eq_refl(x)),
        sub.cons(rest, x, rest, sub.refl(rest)))

# a cell of Del(P, q) is not q
def neq.del.b(e: Bool, +P: List<&2, U32>, +q: U32, +o: U32, +eo: {U32.is_eq(o, q) == e : Bool}, +hnp: {D.Nodup(P) == True{} : Bool},
  hD: {D.Has(Del(P, q), o) == True{} : Bool}) -> {U32.is_eq(o, q) == False{} : Bool}:
  match e:
    case True{}:
      +eq = K.U.eq(o, q, eo)
      K.Bo.ft({U32.is_eq(o, q) == False{} : Bool}, Equal.trans(Bool, True{}, D.Has(Del(P, q), q), False{},
        Equal.sym(Bool, D.Has(Del(P, q), q), True{}, (%eq : {D.Has(Del(P, q), _) == True{} : Bool}; hD)), del.nhas(P, q, hnp)))
    case False{}:
      eo

def neq.del(+P: List<&2, U32>, +q: U32, +o: U32, +hnp: {D.Nodup(P) == True{} : Bool}, hD: {D.Has(Del(P, q), o) == True{} : Bool}) ->
  {U32.is_eq(o, q) == False{} : Bool}:
  neq.del.b(U32.is_eq(o, q), P, q, o, {==}, hnp, hD)

# the garbage's pointers after the zero store at q
def pp.zqr(os: List<&2, U32>, +m: Cr.Cir.Cells, +q: U32, +Qr: List<&2, U32>, +P: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32, +nx: U32,
  +ws: List<&2, W1>, +pu: List<&2, U32>, +hq: {D.Has(P, q) == True{} : Bool}, +hsub: {D.Sub(Con{q, Qr}, P) == True{} : Bool},
  +hcs: {D.AL.cells(P, m, P, Con{q, Qr}, zs, K, F, nx) == True{} : Bool}, +hnp: {D.Nodup(P) == True{} : Bool},
  +hnqr: {D.Has(Qr, q) == False{} : Bool}, +hgq: {Gq(pu, P, Con{q, Qr}) == True{} : Bool}, +hpp: {Pts(pu, m, q) == True{} : Bool},
  +hpt: {W1s.pt(ws, m, q) == True{} : Bool}, +hdv: {Dv3(D.Am(m, q), q, m, W1s(ws, m), pu, Dn3(m, q)) == True{} : Bool},
  +hzq: N.Le(291n, U32.to_nat(q)), +hk: {U32.is_le(290, K) == True{} : Bool}, +hkf: {U32.is_lt(K, F) == True{} : Bool}, +tb: D.Tb(m), +c: U32, hos: {D.Sub(os, Del(P, q)) == True{} : Bool}) ->
  {D.Pp(os, Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), c) == D.Pp(os, W1s(ws, m), c) : Nat}:
  match os:
    case Nil{}:
      {==}
    case Con{+o, +rest}:
      +M = W1s(ws, m)
      +ms = Cr.Cir.Cells.set(M, q, Cr.Cir.Cell.zero())
      +Q2 = List.append(&2, U32, pu, Qr)
      +Q = {Con{q, Qr} : List<&2, U32>}
      +Dl = Del(P, q)

      +h2 = hos
      +hD = K.Bo.and_l(D.Has(Dl, o), D.Sub(rest, Dl), h2)
      +hP = has.del.le(P, q, o, hD)
      +ne = neq.del(P, q, o, hnp, hD)
      +hx = al.mem(P, m, P, Q, zs, K, F, nx, o, hP, hcs)
      +hd0 = K.Bo.and_l(K.AL.hd(m, Q, o, F, nx), Bool.and(K.AL.pt(m, P, zs, o, K, F, nx), K.AL.ct(m, P, Q, o, F, nx)), hx)
      +ht = {(%Equal.sym(U32, D.Fd(0n, M, o), D.Fd(0n, m, o), fd.w1s(ws, m, 0n, {==}, o)) :
          {Bool.or(U32.is_le(U32.and(_, 63), 18), Bool.and(U32.is_le(32, U32.and(_, 63)), D.Has(Q, o))) == True{} : Bool};
        K.al.hd.tg(m, Q, o, F, nx, hd0)) :
        {Bool.or(U32.is_le(U32.and(D.Fd(0n, M, o), 63), 18), Bool.and(U32.is_le(32, U32.and(D.Fd(0n, M, o), 63)), D.Has(Q, o))) == True{} : Bool}}
      %Equal.sym(Nat, D.Ow(ms, o, c), D.Ow(M, o, c), K.ow.set(M, q, Cr.Cir.Cell.zero(), o, c, D.Has(Q, o), ne, ht, hzq)) :
        {Nat.add(_, D.Pp(rest, ms, c)) == Nat.add(D.Ow(M, o, c), D.Pp(rest, M, c)) : Nat}
      %Equal.sym(Nat, D.Pp(rest, ms, c), D.Pp(rest, M, c), pp.zqr(rest, m, q, Qr, P, zs, K, F, nx, ws, pu, hq, hsub, hcs, hnp, hnqr, hgq, hpp, hpt, hdv, hzq, hk, hkf, tb, c, K.Bo.and_r(D.Has(Dl, o), D.Sub(rest, Dl), h2))) :
        {Nat.add(D.Ow(M, o, c), _) == Nat.add(D.Ow(M, o, c), D.Pp(rest, M, c)) : Nat}
      {==}

def pp.zq(+m: Cr.Cir.Cells, +q: U32, +Qr: List<&2, U32>, +P: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32, +nx: U32,
  +ws: List<&2, W1>, +pu: List<&2, U32>, +hq: {D.Has(P, q) == True{} : Bool}, +hsub: {D.Sub(Con{q, Qr}, P) == True{} : Bool},
  +hcs: {D.AL.cells(P, m, P, Con{q, Qr}, zs, K, F, nx) == True{} : Bool}, +hnp: {D.Nodup(P) == True{} : Bool},
  +hnqr: {D.Has(Qr, q) == False{} : Bool}, +hgq: {Gq(pu, P, Con{q, Qr}) == True{} : Bool}, +hpp: {Pts(pu, m, q) == True{} : Bool},
  +hpt: {W1s.pt(ws, m, q) == True{} : Bool}, +hdv: {Dv3(D.Am(m, q), q, m, W1s(ws, m), pu, Dn3(m, q)) == True{} : Bool},
  +hzq: N.Le(291n, U32.to_nat(q)), +hk: {U32.is_le(290, K) == True{} : Bool}, +hkf: {U32.is_lt(K, F) == True{} : Bool}, +tb: D.Tb(m), +c: U32) -> {D.Pp(Del(P, q), Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), c) == D.Pp(Del(P, q), m, c) : Nat}:
  Equal.trans(Nat, D.Pp(Del(P, q), Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), c), D.Pp(Del(P, q), W1s(ws, m), c), D.Pp(Del(P, q), m, c), pp.zqr(Del(P, q), m, q, Qr, P, zs, K, F, nx, ws, pu, hq, hsub, hcs, hnp, hnqr, hgq, hpp, hpt, hdv, hzq, hk, hkf, tb, c, sub.refl(Del(P, q))),
    pp.w1s(Del(P, q), ws, m, c))

# a garbage cell's part p: the same after the reuse
def live.zq(+m: Cr.Cir.Cells, +q: U32, +Qr: List<&2, U32>, +P: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32, +nx: U32,
  +ws: List<&2, W1>, +pu: List<&2, U32>, +hq: {D.Has(P, q) == True{} : Bool}, +hsub: {D.Sub(Con{q, Qr}, P) == True{} : Bool},
  +hcs: {D.AL.cells(P, m, P, Con{q, Qr}, zs, K, F, nx) == True{} : Bool}, +hnp: {D.Nodup(P) == True{} : Bool},
  +hnqr: {D.Has(Qr, q) == False{} : Bool}, +hgq: {Gq(pu, P, Con{q, Qr}) == True{} : Bool}, +hpp: {Pts(pu, m, q) == True{} : Bool},
  +hpt: {W1s.pt(ws, m, q) == True{} : Bool}, +hdv: {Dv3(D.Am(m, q), q, m, W1s(ws, m), pu, Dn3(m, q)) == True{} : Bool},
  +hzq: N.Le(291n, U32.to_nat(q)), +hk: {U32.is_le(290, K) == True{} : Bool}, +hkf: {U32.is_lt(K, F) == True{} : Bool}, +tb: D.Tb(m), +p: U32, +hz: {U32.is_zero(p) == False{} : Bool}, +hs: {D.Stc(m, p) == False{} : Bool},
  hl: {Nat.is_lt(D.Pp(P, m, p), U32.to_nat(D.Fd(1n, m, p))) == True{} : Bool}) ->
  {Nat.is_lt(D.Pp(Del(P, q), m, p), U32.to_nat(D.Fd(1n, W1s(ws, m), p))) == True{} : Bool}:
  +M = W1s(ws, m)
  +ow = D.Ow(m, q, p)
  +c0 = U32.to_nat(D.Fd(1n, m, p))
  +c3 = U32.to_nat(D.Fd(1n, M, p))
  +PpP = D.Pp(P, m, p)
  +PpD = D.Pp(Del(P, q), m, p)
  +hl1 = K.Na.lt1(PpP, c0, hl)
  +hb = N.le_trans(1n+ow, 1n+PpP, c0, pp.ge(P, m, q, p, hq), hl1)
  +hv = dv.all(m, q, ws, pu, p, hz, hdv, hpt, hpp)
  +hpu = dv.np(m, M, pu, p, ow, hs, hv, hb)
  +e3 = dv.ne(m, M, pu, p, ow, hs, hpu, hv)
  +ed = pp.del(P, m, q, p, hq)
  +h2 = {(%ed : N.Le(1n+_, Nat.add(c3, ow)); (%Equal.sym(Nat, Nat.add(c3, ow), c0, e3) : N.Le(1n+PpP, _); hl1)) : N.Le(1n+Nat.add(ow, PpD), Nat.add(c3, ow))}
  +h3 = N.le_rw_r(1n+Nat.add(ow, PpD), Nat.add(c3, ow), Nat.add(ow, c3), Na.comm(c3, ow), h2)
  +h4 = N.le_rw_l(1n+Nat.add(ow, PpD), Nat.add(ow, 1n+PpD), Nat.add(ow, c3), Equal.sym(Nat, Nat.add(ow, 1n+PpD), 1n+Nat.add(ow, PpD), N.add_succ_r(ow, PpD)), h3)
  K.Na.lt1i(PpD, c3, K.Na.le.canc(ow, 1n+PpD, c3, h4))

def inner.ip(ip: Bool, +m: Cr.Cir.Cells, +q: U32, +Qr: List<&2, U32>, +P: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32, +nx: U32,
  +ws: List<&2, W1>, +pu: List<&2, U32>, +hq: {D.Has(P, q) == True{} : Bool}, +hsub: {D.Sub(Con{q, Qr}, P) == True{} : Bool},
  +hcs: {D.AL.cells(P, m, P, Con{q, Qr}, zs, K, F, nx) == True{} : Bool}, +hnp: {D.Nodup(P) == True{} : Bool},
  +hnqr: {D.Has(Qr, q) == False{} : Bool}, +hgq: {Gq(pu, P, Con{q, Qr}) == True{} : Bool}, +hpp: {Pts(pu, m, q) == True{} : Bool},
  +hpt: {W1s.pt(ws, m, q) == True{} : Bool}, +hdv: {Dv3(D.Am(m, q), q, m, W1s(ws, m), pu, Dn3(m, q)) == True{} : Bool},
  +hzq: N.Le(291n, U32.to_nat(q)), +hk: {U32.is_le(290, K) == True{} : Bool}, +hkf: {U32.is_lt(K, F) == True{} : Bool}, +tb: D.Tb(m), +p: U32, +z: Nat, +hz: {U32.is_zero(p) == False{} : Bool}, +hs: {D.Stc(m, p) == False{} : Bool},
  +eip: {Bool.and(D.Has(P, p), Nat.is_lt(D.Zz(zs, p), z)) == ip : Bool},
  h: {Bool.or(Bool.and(D.Has(P, p), Nat.is_lt(D.Zz(zs, p), z)), Nat.is_lt(D.Pp(P, m, p), U32.to_nat(D.Fd(1n, m, p)))) == True{} : Bool}) ->
  {Bool.or(Bool.and(D.Has(P, p), Nat.is_lt(D.Zz(zs, p), z)), Nat.is_lt(D.Pp(Del(P, q), m, p), U32.to_nat(D.Fd(1n, W1s(ws, m), p)))) == True{} : Bool}:
  match ip:
    case True{}:
      +IP = Bool.and(D.Has(P, p), Nat.is_lt(D.Zz(zs, p), z))
      K.Bo.or_il(IP, Nat.is_lt(D.Pp(Del(P, q), m, p), U32.to_nat(D.Fd(1n, W1s(ws, m), p))), eip)
    case False{}:
      +IP = Bool.and(D.Has(P, p), Nat.is_lt(D.Zz(zs, p), z))
      K.Bo.or_ir(IP, Nat.is_lt(D.Pp(Del(P, q), m, p), U32.to_nat(D.Fd(1n, W1s(ws, m), p))),
        live.zq(m, q, Qr, P, zs, K, F, nx, ws, pu, hq, hsub, hcs, hnp, hnqr, hgq, hpp, hpt, hdv, hzq, hk, hkf, tb, p, hz, hs, K.Bo.or_r(IP, Nat.is_lt(D.Pp(P, m, p), U32.to_nat(D.Fd(1n, m, p))), h, eip)))

def inner.st(st: Bool, +m: Cr.Cir.Cells, +q: U32, +Qr: List<&2, U32>, +P: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32, +nx: U32,
  +ws: List<&2, W1>, +pu: List<&2, U32>, +hq: {D.Has(P, q) == True{} : Bool}, +hsub: {D.Sub(Con{q, Qr}, P) == True{} : Bool},
  +hcs: {D.AL.cells(P, m, P, Con{q, Qr}, zs, K, F, nx) == True{} : Bool}, +hnp: {D.Nodup(P) == True{} : Bool},
  +hnqr: {D.Has(Qr, q) == False{} : Bool}, +hgq: {Gq(pu, P, Con{q, Qr}) == True{} : Bool}, +hpp: {Pts(pu, m, q) == True{} : Bool},
  +hpt: {W1s.pt(ws, m, q) == True{} : Bool}, +hdv: {Dv3(D.Am(m, q), q, m, W1s(ws, m), pu, Dn3(m, q)) == True{} : Bool},
  +hzq: N.Le(291n, U32.to_nat(q)), +hk: {U32.is_le(290, K) == True{} : Bool}, +hkf: {U32.is_lt(K, F) == True{} : Bool}, +tb: D.Tb(m), +p: U32, +z: Nat, +hz: {U32.is_zero(p) == False{} : Bool}, +est: {D.Stc(m, p) == st : Bool},
  h: {Bool.or(D.Stc(m, p), Bool.or(Bool.and(D.Has(P, p), Nat.is_lt(D.Zz(zs, p), z)), Nat.is_lt(D.Pp(P, m, p), U32.to_nat(D.Fd(1n, m, p))))) == True{} : Bool}) ->
  {Bool.or(D.Stc(m, p), Bool.or(Bool.and(D.Has(P, p), Nat.is_lt(D.Zz(zs, p), z)), Nat.is_lt(D.Pp(Del(P, q), m, p), U32.to_nat(D.Fd(1n, W1s(ws, m), p))))) ==
    True{} : Bool}:
  match st:
    case True{}:
      +R4N = Bool.or(Bool.and(D.Has(P, p), Nat.is_lt(D.Zz(zs, p), z)), Nat.is_lt(D.Pp(Del(P, q), m, p), U32.to_nat(D.Fd(1n, W1s(ws, m), p))))
      K.Bo.or_il(D.Stc(m, p), R4N, est)
    case False{}:
      +R4N = Bool.or(Bool.and(D.Has(P, p), Nat.is_lt(D.Zz(zs, p), z)), Nat.is_lt(D.Pp(Del(P, q), m, p), U32.to_nat(D.Fd(1n, W1s(ws, m), p))))
      +R4O = Bool.or(Bool.and(D.Has(P, p), Nat.is_lt(D.Zz(zs, p), z)), Nat.is_lt(D.Pp(P, m, p), U32.to_nat(D.Fd(1n, m, p))))
      K.Bo.or_ir(D.Stc(m, p), R4N, inner.ip(Bool.and(D.Has(P, p), Nat.is_lt(D.Zz(zs, p), z)), m, q, Qr, P, zs, K, F, nx, ws, pu, hq, hsub, hcs, hnp, hnqr, hgq, hpp, hpt, hdv, hzq, hk, hkf, tb, p, z, hz, est, {==},
        K.Bo.or_r(D.Stc(m, p), R4O, h, est)))

def inner.zq(+m: Cr.Cir.Cells, +q: U32, +Qr: List<&2, U32>, +P: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32, +nx: U32,
  +ws: List<&2, W1>, +pu: List<&2, U32>, +hq: {D.Has(P, q) == True{} : Bool}, +hsub: {D.Sub(Con{q, Qr}, P) == True{} : Bool},
  +hcs: {D.AL.cells(P, m, P, Con{q, Qr}, zs, K, F, nx) == True{} : Bool}, +hnp: {D.Nodup(P) == True{} : Bool},
  +hnqr: {D.Has(Qr, q) == False{} : Bool}, +hgq: {Gq(pu, P, Con{q, Qr}) == True{} : Bool}, +hpp: {Pts(pu, m, q) == True{} : Bool},
  +hpt: {W1s.pt(ws, m, q) == True{} : Bool}, +hdv: {Dv3(D.Am(m, q), q, m, W1s(ws, m), pu, Dn3(m, q)) == True{} : Bool},
  +hzq: N.Le(291n, U32.to_nat(q)), +hk: {U32.is_le(290, K) == True{} : Bool}, +hkf: {U32.is_lt(K, F) == True{} : Bool}, +tb: D.Tb(m), +p: U32, +z: Nat, h: {Bool.or(D.Stc(m, p), Bool.or(Bool.and(D.Has(P, p), Nat.is_lt(D.Zz(zs, p), z)), Nat.is_lt(D.Pp(P, m, p), U32.to_nat(D.Fd(1n, m, p))))) == True{} : Bool}, +hz: {U32.is_zero(p) == False{} : Bool},
  +ne: {U32.is_eq(p, q) == False{} : Bool}) -> {Bool.or(D.Stc(Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), p), Bool.or(Bool.and(D.Has(Del(P, q), p), Nat.is_lt(D.Zz(zs, p), z)), Nat.is_lt(D.Pp(Del(P, q), Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), p), U32.to_nat(D.Fd(1n, Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), p))))) == True{} : Bool}:
  +M = W1s(ws, m)
  +ms = Cr.Cir.Cells.set(M, q, Cr.Cir.Cell.zero())
  +Q2 = List.append(&2, U32, pu, Qr)
  +Q = {Con{q, Qr} : List<&2, U32>}
  +Dl = Del(P, q)
  %Equal.sym(Bool, D.Stc(ms, p), D.Stc(m, p), stc.zq(m, q, Qr, P, zs, K, F, nx, ws, pu, p, ne)) :
    {Bool.or(_, Bool.or(Bool.and(D.Has(Dl, p), Nat.is_lt(D.Zz(zs, p), z)), Nat.is_lt(D.Pp(Dl, ms, p), U32.to_nat(D.Fd(1n, ms, p))))) == True{} : Bool}
  %Equal.sym(Bool, D.Has(Dl, p), D.Has(P, p), has.del(P, q, p, ne)) :
    {Bool.or(D.Stc(m, p), Bool.or(Bool.and(_, Nat.is_lt(D.Zz(zs, p), z)), Nat.is_lt(D.Pp(Dl, ms, p), U32.to_nat(D.Fd(1n, ms, p))))) == True{} : Bool}
  %Equal.sym(Nat, D.Pp(Dl, ms, p), D.Pp(Dl, m, p), pp.zq(m, q, Qr, P, zs, K, F, nx, ws, pu, hq, hsub, hcs, hnp, hnqr, hgq, hpp, hpt, hdv, hzq, hk, hkf, tb, p)) :
    {Bool.or(D.Stc(m, p), Bool.or(Bool.and(D.Has(P, p), Nat.is_lt(D.Zz(zs, p), z)), Nat.is_lt(_, U32.to_nat(D.Fd(1n, ms, p))))) == True{} : Bool}
  %Equal.sym(U32, D.Fd(1n, ms, p), D.Fd(1n, M, p), f1.zq(m, q, Qr, P, zs, K, F, nx, ws, pu, p, ne)) :
    {Bool.or(D.Stc(m, p), Bool.or(Bool.and(D.Has(P, p), Nat.is_lt(D.Zz(zs, p), z)), Nat.is_lt(D.Pp(Dl, m, p), U32.to_nat(_)))) == True{} : Bool}
  inner.st(D.Stc(m, p), m, q, Qr, P, zs, K, F, nx, ws, pu, hq, hsub, hcs, hnp, hnqr, hgq, hpp, hpt, hdv, hzq, hk, hkf, tb, p, z, hz, {==}, h)


# a garbage cell's own facts after the reuse
def hd.mono(+A: Bool, +B: Bool, +C: Bool, +X: Bool, +X2: Bool, h: {Bool.and(A, Bool.or(B, Bool.and(C, X))) == True{} : Bool},
  k: {X == True{} : Bool} -> {X2 == True{} : Bool}) -> {Bool.and(A, Bool.or(B, Bool.and(C, X2))) == True{} : Bool}:
  +h2 = h
  K.Bo.and_i(A, Bool.or(B, Bool.and(C, X2)), K.Bo.and_l(A, Bool.or(B, Bool.and(C, X)), h2),
    or.mono_r(B, Bool.and(C, X), Bool.and(C, X2), K.Bo.and_r(A, Bool.or(B, Bool.and(C, X)), h2),
      +hc => K.Bo.and_i(C, X2, K.Bo.and_l(C, X, hc), k(K.Bo.and_r(C, X, hc)))))

def has.q2(+m: Cr.Cir.Cells, +q: U32, +Qr: List<&2, U32>, +P: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32, +nx: U32,
  +ws: List<&2, W1>, +pu: List<&2, U32>, +o: U32, +ne: {U32.is_eq(o, q) == False{} : Bool}, hx: {D.Has(Con{q, Qr}, o) == True{} : Bool}) -> {D.Has(List.append(&2, U32, pu, Qr), o) == True{} : Bool}:
  +hr = {(%K.U.ne.sym(o, q, ne) : {Bool.or(_, D.Has(Qr, o)) == True{} : Bool}; hx) : {D.Has(Qr, o) == True{} : Bool}}
  (%Equal.sym(Bool, D.Has(List.append(&2, U32, pu, Qr), o), Bool.or(D.Has(pu, o), D.Has(Qr, o)), K.has.app(pu, Qr, o)) : {_ == True{} : Bool};
    K.Bo.or_ir(D.Has(pu, o), D.Has(Qr, o), hr))

def al.o.hd(+m: Cr.Cir.Cells, +q: U32, +Qr: List<&2, U32>, +P: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32, +nx: U32,
  +ws: List<&2, W1>, +pu: List<&2, U32>, +hq: {D.Has(P, q) == True{} : Bool}, +hsub: {D.Sub(Con{q, Qr}, P) == True{} : Bool},
  +hcs: {D.AL.cells(P, m, P, Con{q, Qr}, zs, K, F, nx) == True{} : Bool}, +hnp: {D.Nodup(P) == True{} : Bool},
  +hnqr: {D.Has(Qr, q) == False{} : Bool}, +hgq: {Gq(pu, P, Con{q, Qr}) == True{} : Bool}, +hpp: {Pts(pu, m, q) == True{} : Bool},
  +hpt: {W1s.pt(ws, m, q) == True{} : Bool}, +hdv: {Dv3(D.Am(m, q), q, m, W1s(ws, m), pu, Dn3(m, q)) == True{} : Bool},
  +hzq: N.Le(291n, U32.to_nat(q)), +hk: {U32.is_le(290, K) == True{} : Bool}, +hkf: {U32.is_lt(K, F) == True{} : Bool}, +tb: D.Tb(m), +o: U32, +ne: {U32.is_eq(o, q) == False{} : Bool}, +hd0: {K.AL.hd(m, Con{q, Qr}, o, F, nx) == True{} : Bool}) ->
  {K.AL.hd(Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), List.append(&2, U32, pu, Qr), o, F, nx) == True{} : Bool}:
  +M = W1s(ws, m)
  +ms = Cr.Cir.Cells.set(M, q, Cr.Cir.Cell.zero())
  +Q2 = List.append(&2, U32, pu, Qr)
  +Q = {Con{q, Qr} : List<&2, U32>}
  +Dl = Del(P, q)
  +f0 = D.Fd(0n, m, o)
  +tg = U32.and(f0, 63)
  +A = Bool.and(Bool.and(U32.is_le(F, o), U32.is_lt(o, nx)), Bool.not(U32.is_ne(U32.and(f0, 1024), 0)))
  %Equal.sym(U32, D.Fd(0n, ms, o), f0, fd.zq(m, q, Qr, P, zs, K, F, nx, ws, pu, 0n, {==}, o, ne)) :
    {Bool.and(Bool.and(Bool.and(U32.is_le(F, o), U32.is_lt(o, nx)), Bool.not(U32.is_ne(U32.and(_, 1024), 0))),
      Bool.or(U32.is_le(U32.and(_, 63), 18), Bool.and(U32.is_le(32, U32.and(_, 63)), D.Has(Q2, o)))) == True{} : Bool}
  hd.mono(A, U32.is_le(tg, 18), U32.is_le(32, tg), D.Has(Q, o), D.Has(Q2, o), hd0, hx => has.q2(m, q, Qr, P, zs, K, F, nx, ws, pu, o, ne, hx))

# the mask of a garbage cell after the reuse
def am.zq(+m: Cr.Cir.Cells, +q: U32, +Qr: List<&2, U32>, +P: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32, +nx: U32,
  +ws: List<&2, W1>, +pu: List<&2, U32>, +hq: {D.Has(P, q) == True{} : Bool}, +hsub: {D.Sub(Con{q, Qr}, P) == True{} : Bool},
  +hcs: {D.AL.cells(P, m, P, Con{q, Qr}, zs, K, F, nx) == True{} : Bool}, +hnp: {D.Nodup(P) == True{} : Bool},
  +hnqr: {D.Has(Qr, q) == False{} : Bool}, +hgq: {Gq(pu, P, Con{q, Qr}) == True{} : Bool}, +hpp: {Pts(pu, m, q) == True{} : Bool},
  +hpt: {W1s.pt(ws, m, q) == True{} : Bool}, +hdv: {Dv3(D.Am(m, q), q, m, W1s(ws, m), pu, Dn3(m, q)) == True{} : Bool},
  +hzq: N.Le(291n, U32.to_nat(q)), +hk: {U32.is_le(290, K) == True{} : Bool}, +hkf: {U32.is_lt(K, F) == True{} : Bool}, +tb: D.Tb(m), +o: U32, +ne: {U32.is_eq(o, q) == False{} : Bool},
  +htag: {Bool.or(U32.is_le(U32.and(D.Fd(0n, m, o), 63), 18), Bool.and(U32.is_le(32, U32.and(D.Fd(0n, m, o), 63)), D.Has(Con{q, Qr}, o))) == True{} : Bool}) ->
  {D.Am(Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), o) == D.Am(m, o) : U32}:
  +M = W1s(ws, m)
  +ms = Cr.Cir.Cells.set(M, q, Cr.Cir.Cell.zero())
  +Q2 = List.append(&2, U32, pu, Qr)
  +Q = {Con{q, Qr} : List<&2, U32>}
  +Dl = Del(P, q)
  +htM = {(%Equal.sym(U32, D.Fd(0n, M, o), D.Fd(0n, m, o), fd.w1s(ws, m, 0n, {==}, o)) :
      {Bool.or(U32.is_le(U32.and(_, 63), 18), Bool.and(U32.is_le(32, U32.and(_, 63)), D.Has(Q, o))) == True{} : Bool}; htag) :
    {Bool.or(U32.is_le(U32.and(D.Fd(0n, M, o), 63), 18), Bool.and(U32.is_le(32, U32.and(D.Fd(0n, M, o), 63)), D.Has(Q, o))) == True{} : Bool}}
  Equal.trans(U32, D.Am(ms, o), D.Am(M, o), D.Am(m, o), K.am.set(M, q, Cr.Cir.Cell.zero(), o, D.Has(Q, o), ne, htM, hzq), am.w1s(ws, m, o))

# a part of a garbage cell after the reuse
def part.zq.z(z0: Bool, +m: Cr.Cir.Cells, +q: U32, +Qr: List<&2, U32>, +P: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32, +nx: U32,
  +ws: List<&2, W1>, +pu: List<&2, U32>, +hq: {D.Has(P, q) == True{} : Bool}, +hsub: {D.Sub(Con{q, Qr}, P) == True{} : Bool},
  +hcs: {D.AL.cells(P, m, P, Con{q, Qr}, zs, K, F, nx) == True{} : Bool}, +hnp: {D.Nodup(P) == True{} : Bool},
  +hnqr: {D.Has(Qr, q) == False{} : Bool}, +hgq: {Gq(pu, P, Con{q, Qr}) == True{} : Bool}, +hpp: {Pts(pu, m, q) == True{} : Bool},
  +hpt: {W1s.pt(ws, m, q) == True{} : Bool}, +hdv: {Dv3(D.Am(m, q), q, m, W1s(ws, m), pu, Dn3(m, q)) == True{} : Bool},
  +hzq: N.Le(291n, U32.to_nat(q)), +hk: {U32.is_le(290, K) == True{} : Bool}, +hkf: {U32.is_lt(K, F) == True{} : Bool}, +tb: D.Tb(m), +p: U32, +z: Nat, +ez: {U32.is_zero(p) == z0 : Bool}, +ne: {U32.is_eq(p, q) == False{} : Bool},
  h1: {Bool.or(U32.is_zero(p), Bool.and(Cr.Cir.is_cell(p, K, F, nx), Bool.or(D.Stc(m, p), Bool.or(Bool.and(D.Has(P, p), Nat.is_lt(D.Zz(zs, p), z)),
    Nat.is_lt(D.Pp(P, m, p), U32.to_nat(D.Fd(1n, m, p))))))) == True{} : Bool}) ->
  {Bool.or(U32.is_zero(p), Bool.and(Cr.Cir.is_cell(p, K, F, nx), Bool.or(D.Stc(Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), p), Bool.or(Bool.and(D.Has(Del(P, q), p), Nat.is_lt(D.Zz(zs, p), z)),
    Nat.is_lt(D.Pp(Del(P, q), Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), p), U32.to_nat(D.Fd(1n, Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), p))))))) == True{} : Bool}:
  match z0:
    case True{}:
      +R3O = Bool.or(D.Stc(m, p), Bool.or(Bool.and(D.Has(P, p), Nat.is_lt(D.Zz(zs, p), z)), Nat.is_lt(D.Pp(P, m, p), U32.to_nat(D.Fd(1n, m, p)))))
      +R3N = Bool.or(D.Stc(Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), p), Bool.or(Bool.and(D.Has(Del(P, q), p), Nat.is_lt(D.Zz(zs, p), z)), Nat.is_lt(D.Pp(Del(P, q), Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), p), U32.to_nat(D.Fd(1n, Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), p)))))
      +IC = Cr.Cir.is_cell(p, K, F, nx)
      K.Bo.or_il(U32.is_zero(p), Bool.and(IC, R3N), ez)
    case False{}:
      +R3O = Bool.or(D.Stc(m, p), Bool.or(Bool.and(D.Has(P, p), Nat.is_lt(D.Zz(zs, p), z)), Nat.is_lt(D.Pp(P, m, p), U32.to_nat(D.Fd(1n, m, p)))))
      +R3N = Bool.or(D.Stc(Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), p), Bool.or(Bool.and(D.Has(Del(P, q), p), Nat.is_lt(D.Zz(zs, p), z)), Nat.is_lt(D.Pp(Del(P, q), Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), p), U32.to_nat(D.Fd(1n, Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), p)))))
      +IC = Cr.Cir.is_cell(p, K, F, nx)
      +r = K.Bo.or_r(U32.is_zero(p), Bool.and(IC, R3O), h1, ez)
      K.Bo.or_ir(U32.is_zero(p), Bool.and(IC, R3N), K.Bo.and_i(IC, R3N, K.Bo.and_l(IC, R3O, r), inner.zq(m, q, Qr, P, zs, K, F, nx, ws, pu, hq, hsub, hcs, hnp, hnqr, hgq, hpp, hpt, hdv, hzq, hk, hkf, tb, p, z, K.Bo.and_r(IC, R3O, r), ez, ne)))

def part.zq.s(s: Bool, +m: Cr.Cir.Cells, +q: U32, +Qr: List<&2, U32>, +P: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32, +nx: U32,
  +ws: List<&2, W1>, +pu: List<&2, U32>, +hq: {D.Has(P, q) == True{} : Bool}, +hsub: {D.Sub(Con{q, Qr}, P) == True{} : Bool},
  +hcs: {D.AL.cells(P, m, P, Con{q, Qr}, zs, K, F, nx) == True{} : Bool}, +hnp: {D.Nodup(P) == True{} : Bool},
  +hnqr: {D.Has(Qr, q) == False{} : Bool}, +hgq: {Gq(pu, P, Con{q, Qr}) == True{} : Bool}, +hpp: {Pts(pu, m, q) == True{} : Bool},
  +hpt: {W1s.pt(ws, m, q) == True{} : Bool}, +hdv: {Dv3(D.Am(m, q), q, m, W1s(ws, m), pu, Dn3(m, q)) == True{} : Bool},
  +hzq: N.Le(291n, U32.to_nat(q)), +hk: {U32.is_le(290, K) == True{} : Bool}, +hkf: {U32.is_lt(K, F) == True{} : Bool}, +tb: D.Tb(m), +am: U32, +bit: U32, +p: U32, +z: Nat, +es: {U32.is_zero(U32.and(am, bit)) == s : Bool},
  h: {D.AL.part(m, P, zs, z, am, bit, p, K, F, nx) == True{} : Bool}, +hpq: {Bool.and(U32.is_ne(U32.and(am, bit), 0), U32.is_eq(p, q)) == False{} : Bool}) ->
  {D.AL.part(Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), Del(P, q), zs, z, am, bit, p, K, F, nx) == True{} : Bool}:
  match s:
    case True{}:
      +R1N = Bool.or(U32.is_zero(p), Bool.and(Cr.Cir.is_cell(p, K, F, nx), Bool.or(D.Stc(Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), p), Bool.or(Bool.and(D.Has(Del(P, q), p), Nat.is_lt(D.Zz(zs, p), z)),
        Nat.is_lt(D.Pp(Del(P, q), Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), p), U32.to_nat(D.Fd(1n, Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), p)))))))
      +R1O = Bool.or(U32.is_zero(p), Bool.and(Cr.Cir.is_cell(p, K, F, nx), Bool.or(D.Stc(m, p), Bool.or(Bool.and(D.Has(P, p), Nat.is_lt(D.Zz(zs, p), z)),
        Nat.is_lt(D.Pp(P, m, p), U32.to_nat(D.Fd(1n, m, p)))))))
      K.Bo.or_il(U32.is_zero(U32.and(am, bit)), R1N, es)
    case False{}:
      +R1N = Bool.or(U32.is_zero(p), Bool.and(Cr.Cir.is_cell(p, K, F, nx), Bool.or(D.Stc(Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), p), Bool.or(Bool.and(D.Has(Del(P, q), p), Nat.is_lt(D.Zz(zs, p), z)),
        Nat.is_lt(D.Pp(Del(P, q), Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), p), U32.to_nat(D.Fd(1n, Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), p)))))))
      +R1O = Bool.or(U32.is_zero(p), Bool.and(Cr.Cir.is_cell(p, K, F, nx), Bool.or(D.Stc(m, p), Bool.or(Bool.and(D.Has(P, p), Nat.is_lt(D.Zz(zs, p), z)),
        Nat.is_lt(D.Pp(P, m, p), U32.to_nat(D.Fd(1n, m, p)))))))
      +ne = {(%es : {Bool.and(Bool.not(_), U32.is_eq(p, q)) == False{} : Bool}; hpq) : {U32.is_eq(p, q) == False{} : Bool}}
      K.Bo.or_ir(U32.is_zero(U32.and(am, bit)), R1N,
        part.zq.z(U32.is_zero(p), m, q, Qr, P, zs, K, F, nx, ws, pu, hq, hsub, hcs, hnp, hnqr, hgq, hpp, hpt, hdv, hzq, hk, hkf, tb, p, z, {==}, ne, K.Bo.or_r(U32.is_zero(U32.and(am, bit)), R1O, h, es)))

def part.zq(+m: Cr.Cir.Cells, +q: U32, +Qr: List<&2, U32>, +P: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32, +nx: U32,
  +ws: List<&2, W1>, +pu: List<&2, U32>, +hq: {D.Has(P, q) == True{} : Bool}, +hsub: {D.Sub(Con{q, Qr}, P) == True{} : Bool},
  +hcs: {D.AL.cells(P, m, P, Con{q, Qr}, zs, K, F, nx) == True{} : Bool}, +hnp: {D.Nodup(P) == True{} : Bool},
  +hnqr: {D.Has(Qr, q) == False{} : Bool}, +hgq: {Gq(pu, P, Con{q, Qr}) == True{} : Bool}, +hpp: {Pts(pu, m, q) == True{} : Bool},
  +hpt: {W1s.pt(ws, m, q) == True{} : Bool}, +hdv: {Dv3(D.Am(m, q), q, m, W1s(ws, m), pu, Dn3(m, q)) == True{} : Bool},
  +hzq: N.Le(291n, U32.to_nat(q)), +hk: {U32.is_le(290, K) == True{} : Bool}, +hkf: {U32.is_lt(K, F) == True{} : Bool}, +tb: D.Tb(m), +am: U32, +bit: U32, +p: U32, +z: Nat, h: {D.AL.part(m, P, zs, z, am, bit, p, K, F, nx) == True{} : Bool},
  +hpq: {Bool.and(U32.is_ne(U32.and(am, bit), 0), U32.is_eq(p, q)) == False{} : Bool}) ->
  {D.AL.part(Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), Del(P, q), zs, z, am, bit, p, K, F, nx) == True{} : Bool}:
  part.zq.s(U32.is_zero(U32.and(am, bit)), m, q, Qr, P, zs, K, F, nx, ws, pu, hq, hsub, hcs, hnp, hnqr, hgq, hpp, hpt, hdv, hzq, hk, hkf, tb, am, bit, p, z, {==}, h, hpq)

def al.o.pt(+m: Cr.Cir.Cells, +q: U32, +Qr: List<&2, U32>, +P: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32, +nx: U32,
  +ws: List<&2, W1>, +pu: List<&2, U32>, +hq: {D.Has(P, q) == True{} : Bool}, +hsub: {D.Sub(Con{q, Qr}, P) == True{} : Bool},
  +hcs: {D.AL.cells(P, m, P, Con{q, Qr}, zs, K, F, nx) == True{} : Bool}, +hnp: {D.Nodup(P) == True{} : Bool},
  +hnqr: {D.Has(Qr, q) == False{} : Bool}, +hgq: {Gq(pu, P, Con{q, Qr}) == True{} : Bool}, +hpp: {Pts(pu, m, q) == True{} : Bool},
  +hpt: {W1s.pt(ws, m, q) == True{} : Bool}, +hdv: {Dv3(D.Am(m, q), q, m, W1s(ws, m), pu, Dn3(m, q)) == True{} : Bool},
  +hzq: N.Le(291n, U32.to_nat(q)), +hk: {U32.is_le(290, K) == True{} : Bool}, +hkf: {U32.is_lt(K, F) == True{} : Bool}, +tb: D.Tb(m), +o: U32, +ne: {U32.is_eq(o, q) == False{} : Bool}, +hP: {D.Has(P, o) == True{} : Bool},
  +hd0: {K.AL.hd(m, Con{q, Qr}, o, F, nx) == True{} : Bool}, pt0: {K.AL.pt(m, P, zs, o, K, F, nx) == True{} : Bool}) ->
  {K.AL.pt(Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), Del(P, q), zs, o, K, F, nx) == True{} : Bool}:
  +M = W1s(ws, m)
  +ms = Cr.Cir.Cells.set(M, q, Cr.Cir.Cell.zero())
  +Q2 = List.append(&2, U32, pu, Qr)
  +Q = {Con{q, Qr} : List<&2, U32>}
  +Dl = Del(P, q)
  +pt2 = pt0
  +a = D.Am(m, o)
  +z = D.Zz(zs, o)
  +f2 = D.Fd(2n, m, o)
  +f3 = D.Fd(3n, m, o)
  +f4 = D.Fd(4n, m, o)
  +A1 = D.AL.part(m, P, zs, z, a, 1, f2, K, F, nx)
  +A2 = D.AL.part(m, P, zs, z, a, 2, f3, K, F, nx)
  +A4 = D.AL.part(m, P, zs, z, a, 4, f4, K, F, nx)
  +r = K.Bo.and_r(A1, Bool.and(A2, A4), pt2)
  +w0 = ow.q0(m, q, Qr, P, zs, K, F, nx, ws, pu, hq, hsub, hcs, hnp, hnqr, hgq, hpp, hpt, hdv, hzq, hk, hkf, tb, o, hP)
  +T1 = Bool.and(U32.is_ne(U32.and(a, 1), 0), U32.is_eq(f2, q))
  +T2 = Bool.and(U32.is_ne(U32.and(a, 2), 0), U32.is_eq(f3, q))
  +T3 = Bool.and(U32.is_ne(U32.and(a, 4), 0), U32.is_eq(f4, q))
  +t1 = nof.z(T1, Na.add0l(D.Nat.of(T1), Nat.add(D.Nat.of(T2), D.Nat.of(T3)), w0))
  +w1 = K.Na.add0r(D.Nat.of(T1), Nat.add(D.Nat.of(T2), D.Nat.of(T3)), w0)
  +t2 = nof.z(T2, Na.add0l(D.Nat.of(T2), D.Nat.of(T3), w1))
  +t3 = nof.z(T3, K.Na.add0r(D.Nat.of(T2), D.Nat.of(T3), w1))
  +ea = am.zq(m, q, Qr, P, zs, K, F, nx, ws, pu, hq, hsub, hcs, hnp, hnqr, hgq, hpp, hpt, hdv, hzq, hk, hkf, tb, o, ne, K.al.hd.tg(m, Q, o, F, nx, hd0))
  %Equal.sym(U32, D.Am(ms, o), a, ea) :
    {Bool.and(D.AL.part(ms, Dl, zs, z, _, 1, D.Fd(2n, ms, o), K, F, nx), Bool.and(D.AL.part(ms, Dl, zs, z, _, 2, D.Fd(3n, ms, o), K, F, nx),
      D.AL.part(ms, Dl, zs, z, _, 4, D.Fd(4n, ms, o), K, F, nx))) == True{} : Bool}
  %Equal.sym(U32, D.Fd(2n, ms, o), f2, fd.zq(m, q, Qr, P, zs, K, F, nx, ws, pu, 2n, {==}, o, ne)) :
    {Bool.and(D.AL.part(ms, Dl, zs, z, a, 1, _, K, F, nx), Bool.and(D.AL.part(ms, Dl, zs, z, a, 2, D.Fd(3n, ms, o), K, F, nx),
      D.AL.part(ms, Dl, zs, z, a, 4, D.Fd(4n, ms, o), K, F, nx))) == True{} : Bool}
  %Equal.sym(U32, D.Fd(3n, ms, o), f3, fd.zq(m, q, Qr, P, zs, K, F, nx, ws, pu, 3n, {==}, o, ne)) :
    {Bool.and(D.AL.part(ms, Dl, zs, z, a, 1, f2, K, F, nx), Bool.and(D.AL.part(ms, Dl, zs, z, a, 2, _, K, F, nx),
      D.AL.part(ms, Dl, zs, z, a, 4, D.Fd(4n, ms, o), K, F, nx))) == True{} : Bool}
  %Equal.sym(U32, D.Fd(4n, ms, o), f4, fd.zq(m, q, Qr, P, zs, K, F, nx, ws, pu, 4n, {==}, o, ne)) :
    {Bool.and(D.AL.part(ms, Dl, zs, z, a, 1, f2, K, F, nx), Bool.and(D.AL.part(ms, Dl, zs, z, a, 2, f3, K, F, nx),
      D.AL.part(ms, Dl, zs, z, a, 4, _, K, F, nx))) == True{} : Bool}
  K.Bo.and_i(D.AL.part(ms, Dl, zs, z, a, 1, f2, K, F, nx), Bool.and(D.AL.part(ms, Dl, zs, z, a, 2, f3, K, F, nx), D.AL.part(ms, Dl, zs, z, a, 4, f4, K, F, nx)),
    part.zq(m, q, Qr, P, zs, K, F, nx, ws, pu, hq, hsub, hcs, hnp, hnqr, hgq, hpp, hpt, hdv, hzq, hk, hkf, tb, a, 1, f2, z, K.Bo.and_l(A1, Bool.and(A2, A4), pt2), t1),
    K.Bo.and_i(D.AL.part(ms, Dl, zs, z, a, 2, f3, K, F, nx), D.AL.part(ms, Dl, zs, z, a, 4, f4, K, F, nx),
      part.zq(m, q, Qr, P, zs, K, F, nx, ws, pu, hq, hsub, hcs, hnp, hnqr, hgq, hpp, hpt, hdv, hzq, hk, hkf, tb, a, 2, f3, z, K.Bo.and_l(A2, A4, r), t2), part.zq(m, q, Qr, P, zs, K, F, nx, ws, pu, hq, hsub, hcs, hnp, hnqr, hgq, hpp, hpt, hdv, hzq, hk, hkf, tb, a, 4, f4, z, K.Bo.and_r(A2, A4, r), t3)))


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

# The allocation's run: a reused cell
# -----------------------------------

# the table's entry of a term's tag (below 19) is a cell of the image
def tb.cell(+tg: U32, +K: U32, +F: U32, +nx: U32, e: {U32.is_lt(tg, 19) == True{} : Bool}, hk: {U32.is_le(290, K) == True{} : Bool}) ->
  {Cr.Cir.is_cell(U32.add(272, tg), K, F, nx) == True{} : Bool}:
  +t = U32.to_nat(tg)
  +x = U32.add(272, tg)
  +hs = N.le_trans(Nat.add(272n, t), 290n, U32.to_nat(K), N.add_mono(272n, 272n, t, 18n, N.le_refl(272n), K.U.lt(tg, 19, e)), K.U.le(290, K, hk))
  +ex = K.add.ex(272, tg, K, hs)
  +hx1 = {(%Equal.sym(Nat, U32.to_nat(x), Nat.add(272n, t), ex) : N.Le(1n, _); N.le_trans(1n, 272n, Nat.add(272n, t), N.le_zero(271n),
    N.le_add_r(272n, t))) : N.Le(1n, U32.to_nat(x))}
  +hxk = {(%Equal.sym(Nat, U32.to_nat(x), Nat.add(272n, t), ex) : N.Le(_, U32.to_nat(K)); hs) : N.Le(U32.to_nat(x), U32.to_nat(K))}
  K.Bo.or_il(Bool.and(Bool.not(U32.is_zero(x)), U32.is_le(x, K)), Bool.and(U32.is_le(F, x), U32.is_lt(x, nx)),
    K.Bo.and_i(Bool.not(U32.is_zero(x)), U32.is_le(x, K), K.Bo.not_i(U32.is_zero(x), K.U.ne.sym(0, x, K.Ar.ne(0, x, hx1))),
      K.U.le_t(x, K, hxk)))

# a cell from F to next is a cell
def cell.in(+q: U32, +K: U32, +F: U32, +nx: U32, hFq: {U32.is_le(F, q) == True{} : Bool}, hqn: {U32.is_lt(q, nx) == True{} : Bool}) ->
  {Cr.Cir.is_cell(q, K, F, nx) == True{} : Bool}:
  K.Bo.or_ir(Bool.and(Bool.not(U32.is_zero(q)), U32.is_le(q, K)), Bool.and(U32.is_le(F, q), U32.is_lt(q, nx)),
    K.Bo.and_i(U32.is_le(F, q), U32.is_lt(q, nx), hFq, hqn))

# a cell from F to nx is once among the cells from F
def once.q(+q: U32, +F: U32, +nx: U32, hfn: {U32.is_le(F, nx) == True{} : Bool}, hFq: {U32.is_le(F, q) == True{} : Bool},
  hqn: {U32.is_lt(q, nx) == True{} : Bool}) -> {Once(Nat.sub(U32.to_nat(nx), U32.to_nat(F)), F, q) == True{} : Bool}:
  +x = U32.to_nat(F)
  +X = U32.to_nat(nx)
  +n = Nat.sub(X, x)
  +es = Equal.sym(Nat, Nat.add(x, n), X, K.Ar.sub.add(x, X, K.U.le(F, nx, hfn)))
  once.at(n, F, q, nx, K.U.le(F, q, hFq), N.le_rw_r(1n+U32.to_nat(q), X, Nat.add(x, n), es, K.U.lt(q, nx, hqn)),
    N.le_rw_l(X, Nat.add(x, n), X, es, N.le_refl(X)))

# a garbage cell is not STATIC
def al.hd.ns(+m: Cr.Cir.Cells, +Q: List<&2, U32>, +o: U32, +F: U32, +N: U32, h: {K.AL.hd(m, Q, o, F, N) == True{} : Bool}) ->
  {D.Stc(m, o) == False{} : Bool}:
  +tg = U32.and(D.Fd(0n, m, o), 63)
  K.Bo.not_t(D.Stc(m, o), K.Bo.and_r(Bool.and(U32.is_le(F, o), U32.is_lt(o, N)), Bool.not(D.Stc(m, o)),
    K.Bo.and_l(Bool.and(Bool.and(U32.is_le(F, o), U32.is_lt(o, N)), Bool.not(D.Stc(m, o))),
      Bool.or(U32.is_le(tg, 18), Bool.and(U32.is_le(32, tg), D.Has(Q, o))), h)))

# a pushed cell is none of the pend list's rest
def gq.nq.b(u: Bool, +pu: List<&2, U32>, +P: List<&2, U32>, +q: U32, +Qr: List<&2, U32>, +o: U32, eu: {D.Has(pu, o) == u : Bool},
  +hgq: {Gq(pu, P, Con{q, Qr}) == True{} : Bool}) -> {Bool.and(D.Has(Qr, o), u) == False{} : Bool}:
  match u:
    case True{}:
      +h = gq.mem(pu, P, Con{q, Qr}, o, hgq, eu)
      +hn = K.Bo.not_t(D.Has(Con{q, Qr}, o), K.Bo.and_r(D.Has(P, o), Bool.not(D.Has(Con{q, Qr}, o)), h))
      +hr = K.or.fr(U32.is_eq(q, o), D.Has(Qr, o), hn)
      (%Equal.sym(Bool, D.Has(Qr, o), False{}, hr) : {Bool.and(_, True{}) == False{} : Bool}; {==})
    case False{}:
      and.f(D.Has(Qr, o))

def gq.nq(+pu: List<&2, U32>, +P: List<&2, U32>, +q: U32, +Qr: List<&2, U32>, +o: U32, +hgq: {Gq(pu, P, Con{q, Qr}) == True{} : Bool}) ->
  {Bool.and(D.Has(Qr, o), D.Has(pu, o)) == False{} : Bool}:
  gq.nq.b(D.Has(pu, o), pu, P, q, Qr, o, {==}, hgq)

# q, the pend list's first cell, was not pushed
def gq.nq0.b(u: Bool, +pu: List<&2, U32>, +P: List<&2, U32>, +q: U32, +Qr: List<&2, U32>, eu: {D.Has(pu, q) == u : Bool},
  +hgq: {Gq(pu, P, Con{q, Qr}) == True{} : Bool}) -> {D.Has(pu, q) == False{} : Bool}:
  match u:
    case True{}:
      +h = gq.mem(pu, P, Con{q, Qr}, q, hgq, eu)
      +hn = K.Bo.not_t(D.Has(Con{q, Qr}, q), K.Bo.and_r(D.Has(P, q), Bool.not(D.Has(Con{q, Qr}, q)), h))
      K.Bo.tf({D.Has(pu, q) == False{} : Bool}, Equal.trans(Bool, False{}, D.Has(Con{q, Qr}, q), True{},
        Equal.sym(Bool, D.Has(Con{q, Qr}, q), False{}, hn), K.Bo.or_il(U32.is_eq(q, q), D.Has(Qr, q), K.U.eq_refl(q))))
    case False{}:
      eu

def gq.nq0(+pu: List<&2, U32>, +P: List<&2, U32>, +q: U32, +Qr: List<&2, U32>, +hgq: {Gq(pu, P, Con{q, Qr}) == True{} : Bool}) ->
  {D.Has(pu, q) == False{} : Bool}:
  gq.nq0.b(D.Has(pu, q), pu, P, q, Qr, {==}, hgq)

# a count c3 that lost ow of the pointers ow + ppD, ppD of them left: above 0
def ct.lt(z: Bool, +ow: Nat, +ppD: Nat, +c3: Nat, ez: {Nat.is_eq(ow, 0n) == z : Bool}, e: {ppD == c3 : Nat},
  hlt: {Nat.is_lt(0n, Nat.add(ow, ppD)) == True{} : Bool}, hor: {Bool.or(Nat.is_eq(ow, 0n), Nat.is_lt(0n, c3)) == True{} : Bool}) ->
  {Nat.is_lt(0n, ppD) == True{} : Bool}:
  match z:
    case True{}:
      (%K.Na.eq(ow, 0n, ez) : {Nat.is_lt(0n, Nat.add(_, ppD)) == True{} : Bool}; hlt)
    case False{}:
      (%Equal.sym(Nat, ppD, c3, e) : {Nat.is_lt(0n, _) == True{} : Bool}; K.Bo.or_r(Nat.is_eq(ow, 0n), Nat.is_lt(0n, c3), hor, ez))

# the pick of AL.ct after the reuse of q, for a garbage cell of the pend
# list's rest (g) or pushed (u), never both: ow + ppD were the garbage's
# pointers to it, ow of them q's; its count went from c0 to c3 (Dv)
def ct.pick(g: Bool, u: Bool, +ow: Nat, +ppD: Nat, +c0: Nat, +c3: Nat, hgu: {Bool.and(g, u) == False{} : Bool},
  hpk: {Bool.pick(Bool, g, Nat.is_eq(Nat.add(ow, ppD), 0n), Bool.and(Nat.is_eq(Nat.add(ow, ppD), c0), Nat.is_lt(0n, Nat.add(ow, ppD)))) == True{} : Bool},
  hdv: {Dv.of(False{}, u, c0, c3, ow) == True{} : Bool}) ->
  {Bool.pick(Bool, Bool.or(u, g), Nat.is_eq(ppD, 0n), Bool.and(Nat.is_eq(ppD, c3), Nat.is_lt(0n, ppD))) == True{} : Bool}:
  match g u:
    case True{} True{}:
      K.Bo.ft({Nat.is_eq(ppD, 0n) == True{} : Bool}, hgu)
    case True{} False{}:
      +e0 = K.Na.add0r(ow, ppD, K.Na.eq(Nat.add(ow, ppD), 0n, hpk))
      (%Equal.sym(Nat, ppD, 0n, e0) : {Nat.is_eq(_, 0n) == True{} : Bool}; K.Na.eq_refl(0n))
    case False{} True{}:
      +A = Nat.is_eq(Nat.add(ow, ppD), c0)
      +B = Nat.is_lt(0n, Nat.add(ow, ppD))
      +e1 = K.Na.eq(Nat.add(ow, ppD), c0, K.Bo.and_l(A, B, hpk))
      +e2 = K.Na.eq(c0, ow, hdv)
      +e3 = Equal.trans(Nat, Nat.add(ow, ppD), c0, Nat.add(ow, 0n), e1,
        Equal.trans(Nat, c0, ow, Nat.add(ow, 0n), e2, Equal.sym(Nat, Nat.add(ow, 0n), ow, N.add_zero(ow))))
      +e0 = K.Na.canc(ow, ppD, 0n, e3)
      (%Equal.sym(Nat, ppD, 0n, e0) : {Nat.is_eq(_, 0n) == True{} : Bool}; K.Na.eq_refl(0n))
    case False{} False{}:
      +A = Nat.is_eq(Nat.add(ow, ppD), c0)
      +B = Nat.is_lt(0n, Nat.add(ow, ppD))
      +C = Nat.is_eq(Nat.add(c3, ow), c0)
      +D0 = Bool.or(Nat.is_eq(ow, 0n), Nat.is_lt(0n, c3))
      +hpk2 = hpk
      +hdv2 = hdv
      +e1 = K.Na.eq(Nat.add(ow, ppD), c0, K.Bo.and_l(A, B, hpk2))
      +e3 = K.Na.eq(Nat.add(c3, ow), c0, K.Bo.and_l(C, D0, hdv2))
      +e4 = Equal.trans(Nat, Nat.add(ow, ppD), c0, Nat.add(ow, c3), e1,
        Equal.trans(Nat, c0, Nat.add(c3, ow), Nat.add(ow, c3), Equal.sym(Nat, Nat.add(c3, ow), c0, e3), Na.comm(c3, ow)))
      +e = K.Na.canc(ow, ppD, c3, e4)
      K.Bo.and_i(Nat.is_eq(ppD, c3), Nat.is_lt(0n, ppD),
        (%Equal.sym(Nat, ppD, c3, e) : {Nat.is_eq(_, c3) == True{} : Bool}; K.Na.eq_refl(c3)),
        ct.lt(Nat.is_eq(ow, 0n), ow, ppD, c3, {==}, e, K.Bo.and_r(A, B, hpk2), K.Bo.and_r(C, D0, hdv2)))

# AL.ct of a garbage cell o, but q, after the reuse of q: the pointers to it
# lost q's, as the garbage's did; pushed, or in the pend list, it has none
def al.o.ct(+m: Cr.Cir.Cells, +q: U32, +Qr: List<&2, U32>, +P: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32, +nx: U32,
  +ws: List<&2, W1>, +pu: List<&2, U32>, +hq: {D.Has(P, q) == True{} : Bool}, +hsub: {D.Sub(Con{q, Qr}, P) == True{} : Bool},
  +hcs: {D.AL.cells(P, m, P, Con{q, Qr}, zs, K, F, nx) == True{} : Bool}, +hnp: {D.Nodup(P) == True{} : Bool},
  +hnqr: {D.Has(Qr, q) == False{} : Bool}, +hgq: {Gq(pu, P, Con{q, Qr}) == True{} : Bool}, +hpp: {Pts(pu, m, q) == True{} : Bool},
  +hpt: {W1s.pt(ws, m, q) == True{} : Bool}, +hdv: {Dv3(D.Am(m, q), q, m, W1s(ws, m), pu, Dn3(m, q)) == True{} : Bool},
  +hzq: N.Le(291n, U32.to_nat(q)), +hk: {U32.is_le(290, K) == True{} : Bool}, +hkf: {U32.is_lt(K, F) == True{} : Bool}, +tb: D.Tb(m), +o: U32, +ne: {U32.is_eq(o, q) == False{} : Bool},
  +hP: {D.Has(P, o) == True{} : Bool}, +hOnce: {Once(Nat.sub(U32.to_nat(nx), U32.to_nat(F)), F, q) == True{} : Bool}) ->
  {K.AL.ct(Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), Del(P, q), List.append(&2, U32, pu, Qr), o, F, nx) == True{} : Bool}:
  +M = W1s(ws, m)
  +ms = Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero())
  +Q2 = List.append(&2, U32, pu, Qr)
  +Q = {Con{q, Qr} : List<&2, U32>}
  +Dl = Del(P, q)
  +n = Nat.sub(U32.to_nat(nx), U32.to_nat(F))
  +ow = D.Ow(m, q, o)
  +ppP = D.Pp(P, m, o)
  +ppD = D.Pp(Dl, m, o)
  +c0 = U32.to_nat(D.Fd(1n, m, o))
  +c3 = U32.to_nat(D.Fd(1n, M, o))
  +pcs = D.Pc(n, ms, Q2, F, o)
  +pcm = D.Pc(n, m, Q, F, o)
  +Hd = K.AL.hd(m, Q, o, F, nx)
  +Pt = K.AL.pt(m, P, zs, o, K, F, nx)
  +Ct = K.AL.ct(m, P, Q, o, F, nx)
  +hx = al.mem(P, m, P, Q, zs, K, F, nx, o, hP, hcs)
  +hd0 = K.Bo.and_l(Hd, Bool.and(Pt, Ct), hx)
  +hct = K.Bo.and_r(Pt, Ct, K.Bo.and_r(Hd, Bool.and(Pt, Ct), hx))
  +PK0 = Bool.pick(Bool, D.Has(Q, o), Nat.is_eq(ppP, 0n), Bool.and(Nat.is_eq(ppP, c0), Nat.is_lt(0n, ppP)))
  +epc = K.Na.eq(pcm, ppP, K.Bo.and_l(Nat.is_eq(pcm, ppP), PK0, hct))
  +hpk0 = K.Bo.and_r(Nat.is_eq(pcm, ppP), PK0, hct)
  +epd = pp.del(P, m, q, o, hq)
  +eon = pc.once(n, m, q, Qr, P, zs, K, F, nx, ws, pu, hq, hsub, hcs, hnp, hnqr, hgq, hpp, hpt, hdv, hzq, hk, hkf, tb, F, o, hOnce)
  +e1 = Equal.trans(Nat, Nat.add(pcs, ow), pcm, Nat.add(ow, ppD), eon, Equal.trans(Nat, pcm, ppP, Nat.add(ow, ppD), epc, epd))
  +e2 = K.Na.canc(ow, pcs, ppD, Equal.trans(Nat, Nat.add(ow, pcs), Nat.add(pcs, ow), Nat.add(ow, ppD), Na.comm(ow, pcs), e1))
  +hpk1 = {(%K.U.ne.sym(o, q, ne) : {Bool.pick(Bool, Bool.or(_, D.Has(Qr, o)), Nat.is_eq(ppP, 0n), Bool.and(Nat.is_eq(ppP, c0), Nat.is_lt(0n, ppP))) ==
      True{} : Bool}; hpk0) :
    {Bool.pick(Bool, Bool.or(False{}, D.Has(Qr, o)), Nat.is_eq(ppP, 0n), Bool.and(Nat.is_eq(ppP, c0), Nat.is_lt(0n, ppP))) == True{} : Bool}}
  +hpk = {(%epd : {Bool.pick(Bool, Bool.or(False{}, D.Has(Qr, o)), Nat.is_eq(_, 0n), Bool.and(Nat.is_eq(_, c0), Nat.is_lt(0n, _))) == True{} : Bool}; hpk1) :
    {Bool.pick(Bool, D.Has(Qr, o), Nat.is_eq(Nat.add(ow, ppD), 0n), Bool.and(Nat.is_eq(Nat.add(ow, ppD), c0), Nat.is_lt(0n, Nat.add(ow, ppD)))) ==
      True{} : Bool}}
  +hz = K.U.nz(o, K, F, hkf, al.hd.le(m, Q, o, F, nx, hd0))
  +hdv0 = dv.all(m, q, ws, pu, o, hz, hdv, hpt, hpp)
  +hdv1 = {(%al.hd.ns(m, Q, o, F, nx, hd0) : {Dv.of(_, D.Has(pu, o), c0, c3, ow) == True{} : Bool}; hdv0) :
    {Dv.of(False{}, D.Has(pu, o), c0, c3, ow) == True{} : Bool}}
  %Equal.sym(Nat, D.Pp(Dl, ms, o), ppD, pp.zq(m, q, Qr, P, zs, K, F, nx, ws, pu, hq, hsub, hcs, hnp, hnqr, hgq, hpp, hpt, hdv, hzq, hk, hkf, tb, o)) :
    {Bool.and(Nat.is_eq(pcs, _), Bool.pick(Bool, D.Has(Q2, o), Nat.is_eq(_, 0n), Bool.and(Nat.is_eq(_, U32.to_nat(D.Fd(1n, ms, o))),
      Nat.is_lt(0n, _)))) == True{} : Bool}
  %Equal.sym(U32, D.Fd(1n, ms, o), D.Fd(1n, M, o), f1.zq(m, q, Qr, P, zs, K, F, nx, ws, pu, o, ne)) :
    {Bool.and(Nat.is_eq(pcs, ppD), Bool.pick(Bool, D.Has(Q2, o), Nat.is_eq(ppD, 0n), Bool.and(Nat.is_eq(ppD, U32.to_nat(_)), Nat.is_lt(0n, ppD)))) ==
      True{} : Bool}
  %Equal.sym(Bool, D.Has(Q2, o), Bool.or(D.Has(pu, o), D.Has(Qr, o)), K.has.app(pu, Qr, o)) :
    {Bool.and(Nat.is_eq(pcs, ppD), Bool.pick(Bool, _, Nat.is_eq(ppD, 0n), Bool.and(Nat.is_eq(ppD, c3), Nat.is_lt(0n, ppD)))) == True{} : Bool}
  %Equal.sym(Nat, pcs, ppD, e2) :
    {Bool.and(Nat.is_eq(_, ppD), Bool.pick(Bool, Bool.or(D.Has(pu, o), D.Has(Qr, o)), Nat.is_eq(ppD, 0n), Bool.and(Nat.is_eq(ppD, c3), Nat.is_lt(0n, ppD)))) ==
      True{} : Bool}
  K.Bo.and_i(Nat.is_eq(ppD, ppD), Bool.pick(Bool, Bool.or(D.Has(pu, o), D.Has(Qr, o)), Nat.is_eq(ppD, 0n), Bool.and(Nat.is_eq(ppD, c3), Nat.is_lt(0n, ppD))),
    K.Na.eq_refl(ppD), ct.pick(D.Has(Qr, o), D.Has(pu, o), ow, ppD, c0, c3, gq.nq(pu, P, q, Qr, o, hgq), hpk, hdv1))

# AL.cells after the reuse of q, of the cells os of Del(P, q)
def al.cells.zq(os: List<&2, U32>, +m: Cr.Cir.Cells, +q: U32, +Qr: List<&2, U32>, +P: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32, +nx: U32,
  +ws: List<&2, W1>, +pu: List<&2, U32>, +hq: {D.Has(P, q) == True{} : Bool}, +hsub: {D.Sub(Con{q, Qr}, P) == True{} : Bool},
  +hcs: {D.AL.cells(P, m, P, Con{q, Qr}, zs, K, F, nx) == True{} : Bool}, +hnp: {D.Nodup(P) == True{} : Bool},
  +hnqr: {D.Has(Qr, q) == False{} : Bool}, +hgq: {Gq(pu, P, Con{q, Qr}) == True{} : Bool}, +hpp: {Pts(pu, m, q) == True{} : Bool},
  +hpt: {W1s.pt(ws, m, q) == True{} : Bool}, +hdv: {Dv3(D.Am(m, q), q, m, W1s(ws, m), pu, Dn3(m, q)) == True{} : Bool},
  +hzq: N.Le(291n, U32.to_nat(q)), +hk: {U32.is_le(290, K) == True{} : Bool}, +hkf: {U32.is_lt(K, F) == True{} : Bool}, +tb: D.Tb(m), +hOnce: {Once(Nat.sub(U32.to_nat(nx), U32.to_nat(F)), F, q) == True{} : Bool},
  hos: {D.Sub(os, Del(P, q)) == True{} : Bool}) -> {D.AL.cells(os, Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), Del(P, q), List.append(&2, U32, pu, Qr), zs, K, F, nx) == True{} : Bool}:
  match os:
    case Nil{}:
      {==}
    case Con{+o, +rest}:
      +ms = Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero())
      +Q2 = List.append(&2, U32, pu, Qr)
      +Q = {Con{q, Qr} : List<&2, U32>}
      +Dl = Del(P, q)
      +h2 = hos
      +hD = K.Bo.and_l(D.Has(Dl, o), D.Sub(rest, Dl), h2)
      +hP = has.del.le(P, q, o, hD)
      +ne = neq.del(P, q, o, hnp, hD)
      +Hd = K.AL.hd(m, Q, o, F, nx)
      +Pt = K.AL.pt(m, P, zs, o, K, F, nx)
      +Ct = K.AL.ct(m, P, Q, o, F, nx)
      +hx = al.mem(P, m, P, Q, zs, K, F, nx, o, hP, hcs)
      +hd0 = K.Bo.and_l(Hd, Bool.and(Pt, Ct), hx)
      +pt0 = K.Bo.and_l(Pt, Ct, K.Bo.and_r(Hd, Bool.and(Pt, Ct), hx))
      K.al.cons(o, rest, ms, Dl, Q2, zs, K, F, nx, al.o.hd(m, q, Qr, P, zs, K, F, nx, ws, pu, hq, hsub, hcs, hnp, hnqr, hgq, hpp, hpt, hdv, hzq, hk, hkf, tb, o, ne, hd0), al.o.pt(m, q, Qr, P, zs, K, F, nx, ws, pu, hq, hsub, hcs, hnp, hnqr, hgq, hpp, hpt, hdv, hzq, hk, hkf, tb, o, ne, hP, hd0, pt0),
        al.o.ct(m, q, Qr, P, zs, K, F, nx, ws, pu, hq, hsub, hcs, hnp, hnqr, hgq, hpp, hpt, hdv, hzq, hk, hkf, tb, o, ne, hP, hOnce), al.cells.zq(rest, m, q, Qr, P, zs, K, F, nx, ws, pu, hq, hsub, hcs, hnp, hnqr, hgq, hpp, hpt, hdv, hzq, hk, hkf, tb, hOnce, K.Bo.and_r(D.Has(Dl, o), D.Sub(rest, Dl), h2)))

# the allocation's invariant after the reuse of q, with the pend list from p3
def al.zq(+m: Cr.Cir.Cells, +q: U32, +Qr: List<&2, U32>, +P: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32, +nx: U32,
  +ws: List<&2, W1>, +pu: List<&2, U32>, +hq: {D.Has(P, q) == True{} : Bool}, +hsub: {D.Sub(Con{q, Qr}, P) == True{} : Bool},
  +hcs: {D.AL.cells(P, m, P, Con{q, Qr}, zs, K, F, nx) == True{} : Bool}, +hnp: {D.Nodup(P) == True{} : Bool},
  +hnqr: {D.Has(Qr, q) == False{} : Bool}, +hgq: {Gq(pu, P, Con{q, Qr}) == True{} : Bool}, +hpp: {Pts(pu, m, q) == True{} : Bool},
  +hpt: {W1s.pt(ws, m, q) == True{} : Bool}, +hdv: {Dv3(D.Am(m, q), q, m, W1s(ws, m), pu, Dn3(m, q)) == True{} : Bool},
  +hzq: N.Le(291n, U32.to_nat(q)), +hk: {U32.is_le(290, K) == True{} : Bool}, +hkf: {U32.is_lt(K, F) == True{} : Bool}, +tb: D.Tb(m), +p3: U32, +hOnce: {Once(Nat.sub(U32.to_nat(nx), U32.to_nat(F)), F, q) == True{} : Bool},
  hch: {D.Chain(List.append(&2, U32, pu, Qr), W1s(ws, m), p3) == True{} : Bool}, hnq: {D.Nodup(Qr) == True{} : Bool}, hnd: {D.Nodup(pu) == True{} : Bool},
  hlt: {D.Lt(Nat.sub(U32.to_nat(nx), U32.to_nat(F)), m, Con{q, Qr}, F, nx) == True{} : Bool}) ->
  {D.AL(Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), p3, Del(P, q), List.append(&2, U32, pu, Qr), zs, K, F, nx) == True{} : Bool}:
  +M = W1s(ws, m)
  +ms = Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero())
  +Q2 = List.append(&2, U32, pu, Qr)
  +Dl = Del(P, q)
  +n = Nat.sub(U32.to_nat(nx), U32.to_nat(F))
  +hpq = gq.nq0(pu, P, q, Qr, hgq)
  +hq2 = K.has.app.f(pu, Qr, q, hpq, hnqr)
  +hsq = K.Bo.and_r(D.Has(P, q), D.Sub(Qr, P), hsub)
  K.Bo.and_i(Bool.and(D.Chain(Q2, ms, p3), D.Nodup(Q2)), Bool.and(Bool.and(D.Sub(Q2, Dl), D.Nodup(Dl)),
    Bool.and(D.AL.cells(Dl, ms, Dl, Q2, zs, K, F, nx), D.Lt(n, ms, Q2, F, nx))),
    K.Bo.and_i(D.Chain(Q2, ms, p3), D.Nodup(Q2), K.chain.set(Q2, M, q, Cr.Cir.Cell.zero(), p3, hch, hq2),
      K.nodup.app(pu, Qr, hnd, hnq, gq.dsj(pu, P, q, Qr, hgq))),
    K.Bo.and_i(Bool.and(D.Sub(Q2, Dl), D.Nodup(Dl)), Bool.and(D.AL.cells(Dl, ms, Dl, Q2, zs, K, F, nx), D.Lt(n, ms, Q2, F, nx)),
      K.Bo.and_i(D.Sub(Q2, Dl), D.Nodup(Dl), K.sub.app(pu, Qr, Dl, sub.del(pu, P, q, gq.sub(pu, P, Con{q, Qr}, hgq), hpq),
        sub.del(Qr, P, q, hsq, hnqr)), nodup.del(P, q, hnp)),
      K.Bo.and_i(D.AL.cells(Dl, ms, Dl, Q2, zs, K, F, nx), D.Lt(n, ms, Q2, F, nx), al.cells.zq(Dl, m, q, Qr, P, zs, K, F, nx, ws, pu, hq, hsub, hcs, hnp, hnqr, hgq, hpp, hpt, hdv, hzq, hk, hkf, tb, hOnce, sub.refl(Dl)),
        lt.zq(n, m, q, Qr, P, zs, K, F, nx, ws, pu, hq, hsub, hcs, hnp, hnqr, hgq, hpp, hpt, hdv, hzq, hk, hkf, tb, F, hlt))))

# no pointer reaches q after its reuse
def pc.q0(+m: Cr.Cir.Cells, +q: U32, +Qr: List<&2, U32>, +P: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32, +nx: U32,
  +ws: List<&2, W1>, +pu: List<&2, U32>, +hq: {D.Has(P, q) == True{} : Bool}, +hsub: {D.Sub(Con{q, Qr}, P) == True{} : Bool},
  +hcs: {D.AL.cells(P, m, P, Con{q, Qr}, zs, K, F, nx) == True{} : Bool}, +hnp: {D.Nodup(P) == True{} : Bool},
  +hnqr: {D.Has(Qr, q) == False{} : Bool}, +hgq: {Gq(pu, P, Con{q, Qr}) == True{} : Bool}, +hpp: {Pts(pu, m, q) == True{} : Bool},
  +hpt: {W1s.pt(ws, m, q) == True{} : Bool}, +hdv: {Dv3(D.Am(m, q), q, m, W1s(ws, m), pu, Dn3(m, q)) == True{} : Bool},
  +hzq: N.Le(291n, U32.to_nat(q)), +hk: {U32.is_le(290, K) == True{} : Bool}, +hkf: {U32.is_lt(K, F) == True{} : Bool}, +tb: D.Tb(m), +hOnce: {Once(Nat.sub(U32.to_nat(nx), U32.to_nat(F)), F, q) == True{} : Bool}) ->
  {D.Pc(Nat.sub(U32.to_nat(nx), U32.to_nat(F)), Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero()), List.append(&2, U32, pu, Qr), F, q) == 0n : Nat}:
  +ms = Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero())
  +Q2 = List.append(&2, U32, pu, Qr)
  +Q = {Con{q, Qr} : List<&2, U32>}
  +n = Nat.sub(U32.to_nat(nx), U32.to_nat(F))
  +pcs = D.Pc(n, ms, Q2, F, q)
  +pcm = D.Pc(n, m, Q, F, q)
  +ppq = D.Pp(P, m, q)
  +c0 = U32.to_nat(D.Fd(1n, m, q))
  +PK = Bool.pick(Bool, D.Has(Q, q), Nat.is_eq(ppq, 0n), Bool.and(Nat.is_eq(ppq, c0), Nat.is_lt(0n, ppq)))
  +epc = K.Na.eq(pcm, ppq, K.Bo.and_l(Nat.is_eq(pcm, ppq), PK, q.ct(m, q, Qr, P, zs, K, F, nx, ws, pu, hq, hsub, hcs, hnp, hnqr, hgq, hpp, hpt, hdv, hzq, hk, hkf, tb)))
  Na.add0l(pcs, D.Ow(m, q, q), Equal.trans(Nat, Nat.add(pcs, D.Ow(m, q, q)), pcm, 0n, pc.once(n, m, q, Qr, P, zs, K, F, nx, ws, pu, hq, hsub, hcs, hnp, hnqr, hgq, hpp, hpt, hdv, hzq, hk, hkf, tb, F, q, hOnce),
    Equal.trans(Nat, pcm, ppq, 0n, epc, q.pp0(m, q, Qr, P, zs, K, F, nx, ws, pu, hq, hsub, hcs, hnp, hnqr, hgq, hpp, hpt, hdv, hzq, hk, hkf, tb))))

# M.alloc's end, after the three drops of q's parts: the zero stores and r
# get q; Al.post of the reused q
def al.reuse.end(+f: Nat, +r: Nat, +R: List<&2, U32>, +pg: U32, +L: U32, +I: List<&2, Word(8n)>, +m: Cr.Cir.Cells, +q: U32, +Qr: List<&2, U32>, +P: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32, +nx: U32,
  +hq: {D.Has(P, q) == True{} : Bool}, +hsub: {D.Sub(Con{q, Qr}, P) == True{} : Bool},
  +hcs: {D.AL.cells(P, m, P, Con{q, Qr}, zs, K, F, nx) == True{} : Bool}, +hnp: {D.Nodup(P) == True{} : Bool},
  +hnqr: {D.Has(Qr, q) == False{} : Bool}, +hzq: N.Le(291n, U32.to_nat(q)), +hk: {U32.is_le(290, K) == True{} : Bool},
  +hkf: {U32.is_lt(K, F) == True{} : Bool}, +tb: D.Tb(m), +hr: {Nat.is_lt(r, 63n) == True{} : Bool}, +hnq: {D.Nodup(Qr) == True{} : Bool},
  +hlt: {D.Lt(Nat.sub(U32.to_nat(nx), U32.to_nat(F)), m, Con{q, Qr}, F, nx) == True{} : Bool}, +hOnce: {Once(Nat.sub(U32.to_nat(nx), U32.to_nat(F)), F, q) == True{} : Bool},
  +hFq: {U32.is_le(F, q) == True{} : Bool}, +hqn: {U32.is_lt(q, nx) == True{} : Bool},
  +hb: N.Le(Nat.add(U32.to_nat(F), Nat.sub(U32.to_nat(nx), U32.to_nat(F))), U32.to_nat(nx)),
  +p3: U32, +p4: U32, +p5: U32, +ws: List<&2, W1>, +pu: List<&2, U32>, +hpt: {W1s.pt(ws, m, q) == True{} : Bool},
  +hdv: {Dv3(D.Am(m, q), q, m, W1s(ws, m), pu, Dn3(m, q)) == True{} : Bool}, +hch: {D.Chain(List.append(&2, U32, pu, Qr), W1s(ws, m), p3) == True{} : Bool},
  +hnd: {D.Nodup(pu) == True{} : Bool}, +hgq: {Gq(pu, P, Con{q, Qr}) == True{} : Bool}, +hpp: {Pts(pu, m, q) == True{} : Bool}) ->
  D.Ok(Cr.Cir.exec(1n+f, Sr.sel.b(Sr.sel.b(Sr.sel.b(Sr.sel.b(Sr.sel.b(Sr.sel.b(Sr.sel.t(Mc.M.alloc(r)))))))), Sr.X.st(Rd(R, p3, p4, p5, q, D.Am(m, q)), W1s(ws, m), nx, F, K, pg, L, I)), F, K, L, I, Al.b(Con{q, Qr}, nx),
    rg => ms => nx2 => pg2 => D.Ex(Aw, w => Al.post(r, R, m, nx, K, F, P, Con{q, Qr}, zs, w, rg, ms, nx2))):
  +am = D.Am(m, q)
  +M = W1s(ws, m)
  +ms = Cr.Cir.Cells.set(W1s(ws, m), q, Cr.Cir.Cell.zero())
  +regs = Rd(R, p3, p4, p5, q, am)
  +Q2 = List.append(&2, U32, pu, Qr)
  +Dl = Del(P, q)
  +a = {[p3, p4, p5, q, am] : List<&2, U32>}
  +n = Nat.sub(U32.to_nat(nx), U32.to_nat(F))
  +hc = cell.in(q, K, F, nx, hFq, hqn)
  +st0 = Sr.X.st(regs, M, nx, F, K, pg, L, I)
  +o2 = {Cr.Cir.Out.next{Sr.X.st(Sr.X.set(regs, r, q), ms, nx, F, K, pg, L, I)} : Cr.Cir.Out}
  K.Ok.eq(Cr.Cir.exec(1n+f, Sr.sel.b(Sr.sel.b(Sr.sel.b(Sr.sel.b(Sr.sel.b(Sr.sel.b(Sr.sel.t(Mc.M.alloc(r)))))))), st0), o2, F, K, L, I, Al.b(Con{q, Qr}, nx), rg => ms => nx2 => pg2 => D.Ex(Aw, w => Al.post(r, R, m, nx, K, F, P, Con{q, Qr}, zs, w, rg, ms, nx2)),
    Equal.sym(Cr.Cir.Out, Cr.Cir.exec(1n+f, Sr.sel.b(Sr.sel.b(Sr.sel.b(Sr.sel.b(Sr.sel.b(Sr.sel.b(Sr.sel.t(Mc.M.alloc(r)))))))), st0), o2, Sr.alloc.eq.end(1n+f, regs, M, nx, F, K, pg, L, I, r, q, {==}, {==}, hc, hr)),
    K.Ok.next(Sr.X.set(regs, r, q), ms, nx, F, K, pg, L, I, Al.b(Con{q, Qr}, nx), rg => ms => nx2 => pg2 => D.Ex(Aw, w => Al.post(r, R, m, nx, K, F, P, Con{q, Qr}, zs, w, rg, ms, nx2)),
      (Aw{q, False{}, Dl, Q2, ws, a},
        ({==},
        ({==},
        (hpt,
        ((hq, ({==}, {==})),
        (al.zq(m, q, Qr, P, zs, K, F, nx, ws, pu, hq, hsub, hcs, hnp, hnqr, hgq, hpp, hpt, hdv, hzq, hk, hkf, tb, p3, hOnce, hch, hnq, hnd, hlt),
        (hFq,
        (hc,
        (del.nhas(P, q, hnp),
        (tb.zq(m, q, Qr, P, zs, K, F, nx, ws, pu, hq, hsub, hcs, hnp, hnqr, hgq, hpp, hpt, hdv, hzq, hk, hkf, tb),
        (kept.zq(n, m, q, Qr, P, zs, K, F, nx, ws, pu, hq, hsub, hcs, hnp, hnqr, hgq, hpp, hpt, hdv, hzq, hk, hkf, tb, F, hOnce, N.le_refl(U32.to_nat(F)), hb),
          pc.q0(m, q, Qr, P, zs, K, F, nx, ws, pu, hq, hsub, hcs, hnp, hnqr, hgq, hpp, hpt, hdv, hzq, hk, hkf, tb, hOnce))))))))))))))

# M.alloc's statements from its three drops
def al.tail(+r: Nat) -> {Sr.sel.b(Sr.sel.b(Sr.sel.b(Sr.sel.t(Mc.M.alloc(r))))) == Cr.Cir.Stmt.seq{Mc.M.dec.part(2n, 1), Cr.Cir.Stmt.seq{Mc.M.dec.part(3n, 2), Cr.Cir.Stmt.seq{Mc.M.dec.part(4n, 4), Sr.sel.b(Sr.sel.b(Sr.sel.b(Sr.sel.b(Sr.sel.b(Sr.sel.b(Sr.sel.t(Mc.M.alloc(r))))))))}}} : Cr.Cir.Stmt}:
  {==}

# M.alloc's three drops of q's parts, from the registers Rd (pend the next
# of the pend list), then its end
def al.drops(+f: Nat, +r: Nat, +R: List<&2, U32>, +pg: U32, +L: U32, +I: List<&2, Word(8n)>, +m: Cr.Cir.Cells, +q: U32, +Qr: List<&2, U32>, +P: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32, +nx: U32,
  +hq: {D.Has(P, q) == True{} : Bool}, +hsub: {D.Sub(Con{q, Qr}, P) == True{} : Bool},
  +hcs: {D.AL.cells(P, m, P, Con{q, Qr}, zs, K, F, nx) == True{} : Bool}, +hnp: {D.Nodup(P) == True{} : Bool},
  +hnqr: {D.Has(Qr, q) == False{} : Bool}, +hzq: N.Le(291n, U32.to_nat(q)), +hk: {U32.is_le(290, K) == True{} : Bool},
  +hkf: {U32.is_lt(K, F) == True{} : Bool}, +tb: D.Tb(m), +hr: {Nat.is_lt(r, 63n) == True{} : Bool}, +hnq: {D.Nodup(Qr) == True{} : Bool},
  +hlt: {D.Lt(Nat.sub(U32.to_nat(nx), U32.to_nat(F)), m, Con{q, Qr}, F, nx) == True{} : Bool}, +hOnce: {Once(Nat.sub(U32.to_nat(nx), U32.to_nat(F)), F, q) == True{} : Bool},
  +hFq: {U32.is_le(F, q) == True{} : Bool}, +hqn: {U32.is_lt(q, nx) == True{} : Bool},
  +hb: N.Le(Nat.add(U32.to_nat(F), Nat.sub(U32.to_nat(nx), U32.to_nat(F))), U32.to_nat(nx)),
  +hptq: {K.AL.pt(m, P, zs, q, K, F, nx) == True{} : Bool}, hch0: {D.Chain(Qr, m, D.Fd(1n, m, q)) == True{} : Bool}) ->
  D.Ok(Cr.Cir.exec(1n+f, Cr.Cir.Stmt.seq{Mc.M.dec.part(2n, 1), Cr.Cir.Stmt.seq{Mc.M.dec.part(3n, 2), Cr.Cir.Stmt.seq{Mc.M.dec.part(4n, 4), Sr.sel.b(Sr.sel.b(Sr.sel.b(Sr.sel.b(Sr.sel.b(Sr.sel.b(Sr.sel.t(Mc.M.alloc(r))))))))}}}, Sr.X.st(Rd(R, D.Fd(1n, m, q), T.tm.reg(R, 4n), T.tm.reg(R, 5n), q, D.Am(m, q)), W1s(Nil{}, m), nx, F, K, pg, L, I)), F, K, L, I, Al.b(Con{q, Qr}, nx), rg => ms => nx2 => pg2 => D.Ex(Aw, w => Al.post(r, R, m, nx, K, F, P, Con{q, Qr}, zs, w, rg, ms, nx2))):
  +am = D.Am(m, q)
  +B4 = Sr.sel.b(Sr.sel.b(Sr.sel.b(Sr.sel.b(Sr.sel.b(Sr.sel.b(Sr.sel.t(Mc.M.alloc(r))))))))
  +B3 = {Cr.Cir.Stmt.seq{Mc.M.dec.part(4n, 4), B4} : Cr.Cir.Stmt}
  +B2 = {Cr.Cir.Stmt.seq{Mc.M.dec.part(3n, 2), B3} : Cr.Cir.Stmt}
  +b1 = U32.is_ne(U32.and(am, 1), 0)
  +b2 = U32.is_ne(U32.and(am, 2), 0)
  +b4 = U32.is_ne(U32.and(am, 4), 0)
  +f2 = D.Fd(2n, m, q)
  +f3 = D.Fd(3n, m, q)
  +f4 = D.Fd(4n, m, q)
  +z = D.Zz(zs, q)
  +A1 = D.AL.part(m, P, zs, z, am, 1, f2, K, F, nx)
  +A2 = D.AL.part(m, P, zs, z, am, 2, f3, K, F, nx)
  +A4 = D.AL.part(m, P, zs, z, am, 4, f4, K, F, nx)
  +hp24 = K.Bo.and_r(A1, Bool.and(A2, A4), hptq)
  +hqc = cell.in(q, K, F, nx, hFq, hqn)
  +D1 = D.Ps.opt(b1, f2, Nil{})
  +D2 = D.Ps.opt(b2, f3, D1)
  +M0 = W1s(Nil{}, m)
  +ew = {{==} : {m == M0 : Cr.Cir.Cells}}
  +ea = {{==} : {Qr == List.append(&2, U32, Nil{}, Qr) : List<&2, U32>}}
  +hdv0 = {(%ew : {Dv3(am, q, m, _, Nil{}, Nil{}) == True{} : Bool}; dv3.init(am, q, m)) : {Dv3(am, q, m, M0, Nil{}, Nil{}) == True{} : Bool}}
  +hch1 = {(%ea : {D.Chain(_, M0, D.Fd(1n, m, q)) == True{} : Bool}; (%ew : {D.Chain(Qr, _, D.Fd(1n, m, q)) == True{} : Bool}; hch0)) :
    {D.Chain(List.append(&2, U32, Nil{}, Qr), M0, D.Fd(1n, m, q)) == True{} : Bool}}
  dr.step(f, 2n, 1, B2, R, D.Fd(1n, m, q), T.tm.reg(R, 4n), T.tm.reg(R, 5n), q, m, Nil{}, nx, F, K, pg, L, I, P, Qr, zs, Nil{}, Nil{},
    Al.b(Con{q, Qr}, nx), rg => ms => nx2 => pg2 => D.Ex(Aw, w => Al.post(r, R, m, nx, K, F, P, Con{q, Qr}, zs, w, rg, ms, nx2)), {==}, hqc,
    K.Bo.and_l(Dvm(b1, f2, m, M0, Nil{}, Nil{}), Bool.and(Dvm(b2, f3, m, M0, Nil{}, Nil{}), Dvm(b4, f4, m, M0, Nil{}, Nil{})), hdv0),
    K.Bo.and_l(A1, Bool.and(A2, A4), hptq), hq, hsub, hcs, bk2.of(b1, b2, b4, f2, f3, f4), {==}, hdv0, hch1, {==}, {==}, {==},
    +p3 => +p4 => +p5 => +ws => +pu => +hpt => +hdv => +hch => +hnd => +hgq => +hpp =>
      dr.step(f, 3n, 2, B3, R, p3, p4, p5, q, m, ws, nx, F, K, pg, L, I, P, Qr, zs, pu, D1, Al.b(Con{q, Qr}, nx), rg => ms => nx2 => pg2 => D.Ex(Aw, w => Al.post(r, R, m, nx, K, F, P, Con{q, Qr}, zs, w, rg, ms, nx2)), {==}, hqc,
        K.Bo.and_l(Dvm(b2, f3, m, W1s(ws, m), pu, D1), Dvm(b4, f4, m, W1s(ws, m), pu, D1),
          K.Bo.and_r(Dvm(b1, f2, m, W1s(ws, m), pu, D1), Bool.and(Dvm(b2, f3, m, W1s(ws, m), pu, D1), Dvm(b4, f4, m, W1s(ws, m), pu, D1)), hdv)),
        K.Bo.and_l(A2, A4, hp24), hq, hsub, hcs, bk3.of(b1, b2, b4, f2, f3, f4), hpt, hdv, hch, hnd, hgq, hpp,
        +p3 => +p4 => +p5 => +ws => +pu => +hpt => +hdv => +hch => +hnd => +hgq => +hpp =>
          dr.step(f, 4n, 4, B4, R, p3, p4, p5, q, m, ws, nx, F, K, pg, L, I, P, Qr, zs, pu, D2, Al.b(Con{q, Qr}, nx), rg => ms => nx2 => pg2 => D.Ex(Aw, w => Al.post(r, R, m, nx, K, F, P, Con{q, Qr}, zs, w, rg, ms, nx2)), {==}, hqc,
            K.Bo.and_r(Dvm(b2, f3, m, W1s(ws, m), pu, D2), Dvm(b4, f4, m, W1s(ws, m), pu, D2),
              K.Bo.and_r(Dvm(b1, f2, m, W1s(ws, m), pu, D2), Bool.and(Dvm(b2, f3, m, W1s(ws, m), pu, D2), Dvm(b4, f4, m, W1s(ws, m), pu, D2)), hdv)),
            K.Bo.and_r(A2, A4, hp24), hq, hsub, hcs, bk4.of(b1, b2, b4, f2, f3, f4), hpt, hdv, hch, hnd, hgq, hpp,
            +p3 => +p4 => +p5 => +ws => +pu => +hpt => +hdv => +hch => +hnd => +hgq => +hpp =>
              al.reuse.end(f, r, R, pg, L, I, m, q, Qr, P, zs, K, F, nx, hq, hsub, hcs, hnp, hnqr, hzq, hk, hkf, tb, hr, hnq, hlt, hOnce, hFq, hqn, hb, p3, p4, p5, ws, pu, hpt, hdv, hch, hnd, hgq, hpp))))

# M.alloc(r) from the pend list's first cell q: aq gets q, pend its field 1,
# am its mask (a term cell, by the table) or 0 (a cell of the machine's own
# kinds), by the tag t of q; then the drops
def al.reuse.t(t: Bool, +f: Nat, +r: Nat, +R: List<&2, U32>, +pg: U32, +L: U32, +I: List<&2, Word(8n)>, +m: Cr.Cir.Cells, +q: U32, +Qr: List<&2, U32>, +P: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32, +nx: U32,
  +hq: {D.Has(P, q) == True{} : Bool}, +hsub: {D.Sub(Con{q, Qr}, P) == True{} : Bool},
  +hcs: {D.AL.cells(P, m, P, Con{q, Qr}, zs, K, F, nx) == True{} : Bool}, +hnp: {D.Nodup(P) == True{} : Bool},
  +hnqr: {D.Has(Qr, q) == False{} : Bool}, +hzq: N.Le(291n, U32.to_nat(q)), +hk: {U32.is_le(290, K) == True{} : Bool},
  +hkf: {U32.is_lt(K, F) == True{} : Bool}, +tb: D.Tb(m), +hr: {Nat.is_lt(r, 63n) == True{} : Bool}, +hnq: {D.Nodup(Qr) == True{} : Bool},
  +hlt: {D.Lt(Nat.sub(U32.to_nat(nx), U32.to_nat(F)), m, Con{q, Qr}, F, nx) == True{} : Bool}, +hOnce: {Once(Nat.sub(U32.to_nat(nx), U32.to_nat(F)), F, q) == True{} : Bool},
  +hFq: {U32.is_le(F, q) == True{} : Bool}, +hqn: {U32.is_lt(q, nx) == True{} : Bool},
  +hb: N.Le(Nat.add(U32.to_nat(F), Nat.sub(U32.to_nat(nx), U32.to_nat(F))), U32.to_nat(nx)),
  +hdq: {K.AL.hd(m, Con{q, Qr}, q, F, nx) == True{} : Bool}, +hptq: {K.AL.pt(m, P, zs, q, K, F, nx) == True{} : Bool},
  +hch0: {D.Chain(Qr, m, D.Fd(1n, m, q)) == True{} : Bool}, +hz: {U32.is_eq(q, 0) == False{} : Bool},
  +h3: {List.get(&2, U32, D.Rg.ex(63n, R, 0n), 3n) == Some{q} : Maybe<&2, U32>},
  +et: {U32.is_lt(U32.and(D.Fd(0n, m, q), 63), 32) == t : Bool}) ->
  D.Ok(Cr.Cir.exec(1n+f, Mc.M.alloc(r), D.S(D.Rg.ex(63n, R, 0n), m, nx, F, K, pg, L, I)), F, K, L, I, Al.b(Con{q, Qr}, nx), rg => ms => nx2 => pg2 => D.Ex(Aw, w => Al.post(r, R, m, nx, K, F, P, Con{q, Qr}, zs, w, rg, ms, nx2))):
  match t:
    case True{}:
      +regs = D.Rg.ex(63n, R, 0n)
      +tg = U32.and(D.Fd(0n, m, q), 63)
      +c0 = Cr.Cir.Cells.get(m, q)
      +f1 = Cr.Cir.Cell.get(1n, c0)
      +am = Cr.Cir.Cell.get(2n, Cr.Cir.Cells.get(m, U32.add(272, U32.and(Cr.Cir.Cell.get(0n, c0), 63))))
      +st = D.S(regs, m, nx, F, K, pg, L, I)
      +st0 = Sr.X.st(regs, m, nx, F, K, pg, L, I)
      +st3 = Sr.X.st(Sr.X.set(Sr.X.set(Sr.X.set(regs, 6n, q), 3n, f1), 7n, am), m, nx, F, K, pg, L, I)
      +std = Sr.X.st(Rd(R, D.Fd(1n, m, q), T.tm.reg(R, 4n), T.tm.reg(R, 5n), q, D.Am(m, q)), W1s(Nil{}, m), nx, F, K, pg, L, I)
      +B3 = Sr.sel.b(Sr.sel.b(Sr.sel.b(Sr.sel.t(Mc.M.alloc(r)))))
      +SQ = {Cr.Cir.Stmt.seq{Mc.M.dec.part(2n, 1), Cr.Cir.Stmt.seq{Mc.M.dec.part(3n, 2), Cr.Cir.Stmt.seq{Mc.M.dec.part(4n, 4), Sr.sel.b(Sr.sel.b(Sr.sel.b(Sr.sel.b(Sr.sel.b(Sr.sel.b(Sr.sel.t(Mc.M.alloc(r))))))))}}} : Cr.Cir.Stmt}
      +h19 = K.Ar.t19(tg, D.Has(Con{q, Qr}, q), et, K.al.hd.tg(m, Con{q, Qr}, q, F, nx, hdq))
      +e0 = Sr.alloc.eq.term(1n+f, regs, m, nx, F, K, pg, L, I, r, q, {==}, h3, hz, cell.in(q, K, F, nx, hFq, hqn), et,
        tb.cell(tg, K, F, nx, h19, hk))
      +ex1 = {{==} : {st0 == st : Cr.Cir.State}}
      +e0b = {(%ex1 : {Cr.Cir.exec(1n+f, Mc.M.alloc(r), _) == Cr.Cir.exec(1n+f, B3, st3) : Cr.Cir.Out}; e0) :
        {Cr.Cir.exec(1n+f, Mc.M.alloc(r), st) == Cr.Cir.exec(1n+f, B3, st3) : Cr.Cir.Out}}
      +eam = {(%Equal.sym(Bool, U32.is_lt(tg, 32), True{}, et) : {Bool.pick(U32, _, D.Fd(2n, m, U32.add(272, tg)), 0) == am : U32}; {==}) :
        {D.Am(m, q) == am : U32}}
      +est = {(%Equal.sym(U32, D.Am(m, q), am, eam) :
          {st3 == Sr.X.st(Rd(R, D.Fd(1n, m, q), T.tm.reg(R, 4n), T.tm.reg(R, 5n), q, _), W1s(Nil{}, m), nx, F, K, pg, L, I) : Cr.Cir.State}; {==}) :
        {st3 == std : Cr.Cir.State}}
      +E = Equal.trans(Cr.Cir.Out, Cr.Cir.exec(1n+f, Mc.M.alloc(r), st), Cr.Cir.exec(1n+f, B3, st3), Cr.Cir.exec(1n+f, SQ, std), e0b,
        Equal.trans(Cr.Cir.Out, Cr.Cir.exec(1n+f, B3, st3), Cr.Cir.exec(1n+f, SQ, st3), Cr.Cir.exec(1n+f, SQ, std),
          Equal.cong(Cr.Cir.Stmt, Cr.Cir.Out, s => Cr.Cir.exec(1n+f, s, st3), B3, SQ, al.tail(r)),
          Equal.cong(Cr.Cir.State, Cr.Cir.Out, s => Cr.Cir.exec(1n+f, SQ, s), st3, std, est)))
      K.Ok.eq(Cr.Cir.exec(1n+f, Mc.M.alloc(r), st), Cr.Cir.exec(1n+f, SQ, std), F, K, L, I, Al.b(Con{q, Qr}, nx), rg => ms => nx2 => pg2 => D.Ex(Aw, w => Al.post(r, R, m, nx, K, F, P, Con{q, Qr}, zs, w, rg, ms, nx2)),
        Equal.sym(Cr.Cir.Out, Cr.Cir.exec(1n+f, Mc.M.alloc(r), st), Cr.Cir.exec(1n+f, SQ, std), E),
        al.drops(f, r, R, pg, L, I, m, q, Qr, P, zs, K, F, nx, hq, hsub, hcs, hnp, hnqr, hzq, hk, hkf, tb, hr, hnq, hlt, hOnce, hFq, hqn, hb, hptq, hch0))
    case False{}:
      +regs = D.Rg.ex(63n, R, 0n)
      +tg = U32.and(D.Fd(0n, m, q), 63)
      +c0 = Cr.Cir.Cells.get(m, q)
      +f1 = Cr.Cir.Cell.get(1n, c0)
      +st = D.S(regs, m, nx, F, K, pg, L, I)
      +st0 = Sr.X.st(regs, m, nx, F, K, pg, L, I)
      +st3 = Sr.X.st(Sr.X.set(Sr.X.set(Sr.X.set(regs, 6n, q), 3n, f1), 7n, 0), m, nx, F, K, pg, L, I)
      +std = Sr.X.st(Rd(R, D.Fd(1n, m, q), T.tm.reg(R, 4n), T.tm.reg(R, 5n), q, D.Am(m, q)), W1s(Nil{}, m), nx, F, K, pg, L, I)
      +B3 = Sr.sel.b(Sr.sel.b(Sr.sel.b(Sr.sel.t(Mc.M.alloc(r)))))
      +SQ = {Cr.Cir.Stmt.seq{Mc.M.dec.part(2n, 1), Cr.Cir.Stmt.seq{Mc.M.dec.part(3n, 2), Cr.Cir.Stmt.seq{Mc.M.dec.part(4n, 4), Sr.sel.b(Sr.sel.b(Sr.sel.b(Sr.sel.b(Sr.sel.b(Sr.sel.b(Sr.sel.t(Mc.M.alloc(r))))))))}}} : Cr.Cir.Stmt}
      +e0 = Sr.alloc.eq.own(1n+f, regs, m, nx, F, K, pg, L, I, r, q, {==}, h3, hz, cell.in(q, K, F, nx, hFq, hqn), et)
      +ex1 = {{==} : {st0 == st : Cr.Cir.State}}
      +e0b = {(%ex1 : {Cr.Cir.exec(1n+f, Mc.M.alloc(r), _) == Cr.Cir.exec(1n+f, B3, st3) : Cr.Cir.Out}; e0) :
        {Cr.Cir.exec(1n+f, Mc.M.alloc(r), st) == Cr.Cir.exec(1n+f, B3, st3) : Cr.Cir.Out}}
      +eam = {(%Equal.sym(Bool, U32.is_lt(tg, 32), False{}, et) : {Bool.pick(U32, _, D.Fd(2n, m, U32.add(272, tg)), 0) == 0 : U32}; {==}) :
        {D.Am(m, q) == 0 : U32}}
      +est = {(%Equal.sym(U32, D.Am(m, q), 0, eam) :
          {st3 == Sr.X.st(Rd(R, D.Fd(1n, m, q), T.tm.reg(R, 4n), T.tm.reg(R, 5n), q, _), W1s(Nil{}, m), nx, F, K, pg, L, I) : Cr.Cir.State}; {==}) :
        {st3 == std : Cr.Cir.State}}
      +E = Equal.trans(Cr.Cir.Out, Cr.Cir.exec(1n+f, Mc.M.alloc(r), st), Cr.Cir.exec(1n+f, B3, st3), Cr.Cir.exec(1n+f, SQ, std), e0b,
        Equal.trans(Cr.Cir.Out, Cr.Cir.exec(1n+f, B3, st3), Cr.Cir.exec(1n+f, SQ, st3), Cr.Cir.exec(1n+f, SQ, std),
          Equal.cong(Cr.Cir.Stmt, Cr.Cir.Out, s => Cr.Cir.exec(1n+f, s, st3), B3, SQ, al.tail(r)),
          Equal.cong(Cr.Cir.State, Cr.Cir.Out, s => Cr.Cir.exec(1n+f, SQ, s), st3, std, est)))
      K.Ok.eq(Cr.Cir.exec(1n+f, Mc.M.alloc(r), st), Cr.Cir.exec(1n+f, SQ, std), F, K, L, I, Al.b(Con{q, Qr}, nx), rg => ms => nx2 => pg2 => D.Ex(Aw, w => Al.post(r, R, m, nx, K, F, P, Con{q, Qr}, zs, w, rg, ms, nx2)),
        Equal.sym(Cr.Cir.Out, Cr.Cir.exec(1n+f, Mc.M.alloc(r), st), Cr.Cir.exec(1n+f, SQ, std), E),
        al.drops(f, r, R, pg, L, I, m, q, Qr, P, zs, K, F, nx, hq, hsub, hcs, hnp, hnqr, hzq, hk, hkf, tb, hr, hnq, hlt, hOnce, hFq, hqn, hb, hptq, hch0))

# M.alloc(r) with the pend list from its first cell q: the allocation's
# invariant gives q's facts, then the run by q's tag
def al.reuse(+f: Nat, +r: Nat, +R: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +F: U32, +K: U32, +pg: U32, +L: U32,
  +I: List<&2, Word(8n)>, +P: List<&2, U32>, +q: U32, +Qr: List<&2, U32>, +zs: List<&2, D.Zs>,
  hal: {D.AL(m, T.tm.reg(R, 3n), P, Con{q, Qr}, zs, K, F, nx) == True{} : Bool},
  +hr: {Nat.is_lt(r, 63n) == True{} : Bool}, +hk: {U32.is_le(290, K) == True{} : Bool}, +hkf: {U32.is_lt(K, F) == True{} : Bool},
  +hfn: {U32.is_le(F, nx) == True{} : Bool}, +tb: D.Tb(m)) ->
  D.Ok(Cr.Cir.exec(1n+f, Mc.M.alloc(r), D.S(D.Rg.ex(63n, R, 0n), m, nx, F, K, pg, L, I)), F, K, L, I, Al.b(Con{q, Qr}, nx), rg => ms => nx2 => pg2 => D.Ex(Aw, w => Al.post(r, R, m, nx, K, F, P, Con{q, Qr}, zs, w, rg, ms, nx2))):
  +p0 = T.tm.reg(R, 3n)
  +Q = {Con{q, Qr} : List<&2, U32>}
  +n = Nat.sub(U32.to_nat(nx), U32.to_nat(F))
  +CH = D.Chain(Q, m, p0)
  +ND = D.Nodup(Q)
  +SB = D.Sub(Q, P)
  +NP = D.Nodup(P)
  +AC = D.AL.cells(P, m, P, Q, zs, K, F, nx)
  +LQ = D.Lt(n, m, Q, F, nx)
  +h2 = hal
  +hA = K.Bo.and_l(Bool.and(CH, ND), Bool.and(Bool.and(SB, NP), Bool.and(AC, LQ)), h2)
  +hB = K.Bo.and_r(Bool.and(CH, ND), Bool.and(Bool.and(SB, NP), Bool.and(AC, LQ)), h2)
  +hch = K.Bo.and_l(CH, ND, hA)
  +hnd = K.Bo.and_r(CH, ND, hA)
  +hsn = K.Bo.and_l(Bool.and(SB, NP), Bool.and(AC, LQ), hB)
  +hal2 = K.Bo.and_r(Bool.and(SB, NP), Bool.and(AC, LQ), hB)
  +hsub = K.Bo.and_l(SB, NP, hsn)
  +hnp = K.Bo.and_r(SB, NP, hsn)
  +hcs = K.Bo.and_l(AC, LQ, hal2)
  +hlt = K.Bo.and_r(AC, LQ, hal2)
  +CR = Bool.and(Bool.not(U32.is_zero(q)), D.Chain(Qr, m, D.Fd(1n, m, q)))
  +hpq = K.Bo.and_l(U32.is_eq(p0, q), CR, hch)
  +hrest = K.Bo.and_r(U32.is_eq(p0, q), CR, hch)
  +hnz = K.Bo.not_t(U32.is_zero(q), K.Bo.and_l(Bool.not(U32.is_zero(q)), D.Chain(Qr, m, D.Fd(1n, m, q)), hrest))
  +hch0 = K.Bo.and_r(Bool.not(U32.is_zero(q)), D.Chain(Qr, m, D.Fd(1n, m, q)), hrest)
  +hnqr = K.Bo.not_t(D.Has(Qr, q), K.Bo.and_l(Bool.not(D.Has(Qr, q)), D.Nodup(Qr), hnd))
  +hnq = K.Bo.and_r(Bool.not(D.Has(Qr, q)), D.Nodup(Qr), hnd)
  +hq = K.Bo.and_l(D.Has(P, q), D.Sub(Qr, P), hsub)
  +e3 = K.U.eq(p0, q, hpq)
  +h3 = {(%e3 : {List.get(&2, U32, D.Rg.ex(63n, R, 0n), 3n) == Some{_} : Maybe<&2, U32>}; {==}) :
    {List.get(&2, U32, D.Rg.ex(63n, R, 0n), 3n) == Some{q} : Maybe<&2, U32>}}
  +Hd = K.AL.hd(m, Q, q, F, nx)
  +Pt = K.AL.pt(m, P, zs, q, K, F, nx)
  +Ct = K.AL.ct(m, P, Q, q, F, nx)
  +hxq = al.mem(P, m, P, Q, zs, K, F, nx, q, hq, hcs)
  +hdq = K.Bo.and_l(Hd, Bool.and(Pt, Ct), hxq)
  +hptq = K.Bo.and_l(Pt, Ct, K.Bo.and_r(Hd, Bool.and(Pt, Ct), hxq))
  +hFq = al.hd.le(m, Q, q, F, nx, hdq)
  +hqn = K.al.hd.lt(m, Q, q, F, nx, hdq)
  +hzq = N.le_trans(291n, U32.to_nat(F), U32.to_nat(q), F.big(K, F, hk, hkf), K.U.le(F, q, hFq))
  +hOnce = once.q(q, F, nx, hfn, hFq, hqn)
  +x = U32.to_nat(F)
  +X = U32.to_nat(nx)
  +es = Equal.sym(Nat, Nat.add(x, n), X, K.Ar.sub.add(x, X, K.U.le(F, nx, hfn)))
  +hb = N.le_rw_l(X, Nat.add(x, n), X, es, N.le_refl(X))
  al.reuse.t(U32.is_lt(U32.and(D.Fd(0n, m, q), 63), 32), f, r, R, pg, L, I, m, q, Qr, P, zs, K, F, nx, hq, hsub, hcs, hnp, hnqr, hzq, hk, hkf, tb, hr, hnq, hlt, hOnce, hFq, hqn, hb, hdq, hptq, hch0, hnz, h3, {==})

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
  match Q:
    case Nil{}:
      al.fresh.ok(f, r, R, m, nx, F, K, pg, L, I, P, zs, hal,
        K.Bo.and_l(Nat.is_lt(r, 63n), Bool.not(Bool.and(Nat.is_le(3n, r), Nat.is_le(r, 7n))), hr), hk, hkf, hfn, tb)
    case Con{+q, +Qr}:
      al.reuse(f, r, R, m, nx, F, K, pg, L, I, P, q, Qr, zs, hal,
        K.Bo.and_l(Nat.is_lt(r, 63n), Bool.not(Bool.and(Nat.is_le(3n, r), Nat.is_le(r, 7n))), hr), hk, hkf, hfn, tb)

# The garbage is well-founded
# ---------------------------
#
# With an empty pend list there is no garbage: a garbage cell y of the largest
# zombie size, out of the pend list, counts its garbage pointers, at least one;
# so a garbage cell o has y as a part, by a set bit of its mask; o's AL.part
# then gives y a zombie size below o's, which is at most y's.

# the largest zombie size of the cells P
def Zmax(P: List<&2, U32>, +zs: List<&2, D.Zs>) -> Nat:
  match P:
    case Nil{}:
      0n
    case Con{+o, rest}:
      +r = Zmax(rest, zs)
      Bool.pick(Nat, Nat.is_le(r, D.Zz(zs, o)), D.Zz(zs, o), r)

# a < b, when not b <= a
def nle.lt(a: Nat, b: Nat, h: {Nat.is_le(b, a) == False{} : Bool}) -> N.Le(1n+a, b):
  match a b:
    case 0n 0n:
      K.Bo.tf(N.Le(1n, 0n), Equal.sym(Bool, True{}, False{}, h))
    case 1n+ap 0n:
      K.Bo.tf(N.Le(2n+ap, 0n), Equal.sym(Bool, True{}, False{}, h))
    case 0n 1n+bp:
      N.le_zero(bp)
    case 1n+ap 1n+bp:
      nle.lt(ap, bp, h)

# the larger of zo and r is at least each
def zmax.top(c: Bool, +r: Nat, +zo: Nat, +z: Nat, ec: {Nat.is_le(r, zo) == c : Bool}, hz: N.Le(z, r)) ->
  N.Le(z, Bool.pick(Nat, c, zo, r)):
  match c:
    case True{}:
      N.le_trans(z, r, zo, hz, N.toLe(r, zo, ec))
    case False{}:
      hz

def zmax.self(c: Bool, +r: Nat, +zo: Nat, ec: {Nat.is_le(r, zo) == c : Bool}) -> N.Le(zo, Bool.pick(Nat, c, zo, r)):
  match c:
    case True{}:
      N.le_refl(zo)
    case False{}:
      N.weaken(zo, r, nle.lt(zo, r, ec))

# each zombie size of P is at most the largest
def zmax.ge.b(e: Bool, +o: U32, +rest: List<&2, U32>, +zs: List<&2, D.Zs>, +y: U32, eo: {U32.is_eq(o, y) == e : Bool},
  h: {Bool.or(e, D.Has(rest, y)) == True{} : Bool},
  k: {D.Has(rest, y) == True{} : Bool} -> N.Le(D.Zz(zs, y), Zmax(rest, zs))) -> N.Le(D.Zz(zs, y), Zmax(Con{o, rest}, zs)):
  match e:
    case True{}:
      +r = Zmax(rest, zs)
      +zo = D.Zz(zs, o)
      +ey = K.U.eq(o, y, eo)
      (%ey : N.Le(D.Zz(zs, _), Bool.pick(Nat, Nat.is_le(r, zo), zo, r)); zmax.self(Nat.is_le(r, zo), r, zo, {==}))
    case False{}:
      +r = Zmax(rest, zs)
      +zo = D.Zz(zs, o)
      zmax.top(Nat.is_le(r, zo), r, zo, D.Zz(zs, y), {==}, k(h))

def zmax.ge(P: List<&2, U32>, +zs: List<&2, D.Zs>, +y: U32, h: {D.Has(P, y) == True{} : Bool}) -> N.Le(D.Zz(zs, y), Zmax(P, zs)):
  match P:
    case Nil{}:
      K.Bo.tf(N.Le(D.Zz(zs, y), 0n), h)
    case Con{+o, +rest}:
      zmax.ge.b(U32.is_eq(o, y), o, rest, zs, y, {==}, h, hr => zmax.ge(rest, zs, y, hr))

# a cell of the largest zombie size, of a list that is not empty
def zmax.at.b(c: Bool, +o: U32, +o2: U32, +rest2: List<&2, U32>, +zs: List<&2, D.Zs>, -G: Type,
  ec: {Nat.is_le(Zmax(Con{o2, rest2}, zs), D.Zz(zs, o)) == c : Bool},
  k: @y: U32 -> {D.Has(Con{o, Con{o2, rest2}}, y) == True{} : Bool} ->
    {D.Zz(zs, y) == Bool.pick(Nat, c, D.Zz(zs, o), Zmax(Con{o2, rest2}, zs)) : Nat} -> G,
  kr: (@y: U32 -> {D.Has(Con{o2, rest2}, y) == True{} : Bool} -> {D.Zz(zs, y) == Zmax(Con{o2, rest2}, zs) : Nat} -> G) -> G) -> G:
  match c:
    case True{}:
      k(o, K.Bo.or_il(U32.is_eq(o, o), D.Has(Con{o2, rest2}, o), K.U.eq_refl(o)), {==})
    case False{}:
      kr(+y => +hy => +ey => k(y, K.Bo.or_ir(U32.is_eq(o, y), D.Has(Con{o2, rest2}, y), hy), ey))

def zmax.at(rest: List<&2, U32>, +o: U32, +zs: List<&2, D.Zs>, -G: Type,
  k: @y: U32 -> {D.Has(Con{o, rest}, y) == True{} : Bool} -> {D.Zz(zs, y) == Zmax(Con{o, rest}, zs) : Nat} -> G) -> G:
  match rest:
    case Nil{}:
      +zo = D.Zz(zs, o)
      k(o, K.Bo.or_il(U32.is_eq(o, o), D.Has(Nil{}, o), K.U.eq_refl(o)),
        (%Equal.sym(Bool, Nat.is_le(0n, zo), True{}, K.Na.le0(zo)) : {zo == Bool.pick(Nat, _, zo, 0n) : Nat}; {==}))
    case Con{+o2, +rest2}:
      zmax.at.b(Nat.is_le(Zmax(Con{o2, rest2}, zs), D.Zz(zs, o)), o, o2, rest2, zs, G, {==}, k, k2 => zmax.at(rest2, o2, zs, G, k2))

# a Nat that is not 0 is at least 1
def le1.of(x: Nat, e: {Nat.is_eq(x, 0n) == False{} : Bool}) -> N.Le(1n, x):
  match x:
    case 0n:
      K.Bo.tf(N.Le(1n, 0n), Equal.sym(Bool, True{}, False{}, e))
    case 1n+p:
      N.le_zero(p)

# the garbage's pointers to y, at least one: some garbage cell's pointers
def pp.pos.b(z: Bool, +o: U32, +rest: List<&2, U32>, +m: Cr.Cir.Cells, +y: U32, -G: Type, ez: {Nat.is_eq(D.Ow(m, o, y), 0n) == z : Bool},
  h: N.Le(1n, Nat.add(D.Ow(m, o, y), D.Pp(rest, m, y))),
  k: @c: U32 -> {D.Has(Con{o, rest}, c) == True{} : Bool} -> N.Le(1n, D.Ow(m, c, y)) -> G,
  kr: N.Le(1n, D.Pp(rest, m, y)) -> (@c: U32 -> {D.Has(rest, c) == True{} : Bool} -> N.Le(1n, D.Ow(m, c, y)) -> G) -> G) -> G:
  match z:
    case False{}:
      k(o, K.Bo.or_il(U32.is_eq(o, o), D.Has(rest, o), K.U.eq_refl(o)), le1.of(D.Ow(m, o, y), ez))
    case True{}:
      kr((%K.Na.eq(D.Ow(m, o, y), 0n, ez) : N.Le(1n, Nat.add(_, D.Pp(rest, m, y))); h),
        +c => +hc => hw => k(c, K.Bo.or_ir(U32.is_eq(o, c), D.Has(rest, c), hc), hw))

def pp.pos(P: List<&2, U32>, +m: Cr.Cir.Cells, +y: U32, -G: Type, h: N.Le(1n, D.Pp(P, m, y)),
  k: @c: U32 -> {D.Has(P, c) == True{} : Bool} -> N.Le(1n, D.Ow(m, c, y)) -> G) -> G:
  match P:
    case Nil{}:
      Empty.absurd(G, h)
    case Con{+o, +rest}:
      pp.pos.b(Nat.is_eq(D.Ow(m, o, y), 0n), o, rest, m, y, G, {==}, h, k, h2 => k2 => pp.pos(rest, m, y, G, h2, k2))

# a pointer of the cell o to y: a set bit of o's mask whose field holds y
def ow.pos.c(t1: Bool, t2: Bool, t3: Bool, +m: Cr.Cir.Cells, +o: U32, +y: U32, -G: Type,
  e1: {Bool.and(U32.is_ne(U32.and(D.Am(m, o), 1), 0), U32.is_eq(D.Fd(2n, m, o), y)) == t1 : Bool},
  e2: {Bool.and(U32.is_ne(U32.and(D.Am(m, o), 2), 0), U32.is_eq(D.Fd(3n, m, o), y)) == t2 : Bool},
  e3: {Bool.and(U32.is_ne(U32.and(D.Am(m, o), 4), 0), U32.is_eq(D.Fd(4n, m, o), y)) == t3 : Bool},
  h: N.Le(1n, Nat.add(D.Nat.of(t1), Nat.add(D.Nat.of(t2), D.Nat.of(t3)))),
  k2: {U32.is_zero(U32.and(D.Am(m, o), 1)) == False{} : Bool} -> {D.Fd(2n, m, o) == y : U32} -> G,
  k3: {U32.is_zero(U32.and(D.Am(m, o), 2)) == False{} : Bool} -> {D.Fd(3n, m, o) == y : U32} -> G,
  k4: {U32.is_zero(U32.and(D.Am(m, o), 4)) == False{} : Bool} -> {D.Fd(4n, m, o) == y : U32} -> G) -> G:
  match t1:
    case True{}:
      +b = e1
      +B1 = U32.is_ne(U32.and(D.Am(m, o), 1), 0)
      +E2 = U32.is_eq(D.Fd(2n, m, o), y)
      k2(K.Bo.not_t(U32.is_eq(U32.and(D.Am(m, o), 1), 0), K.Bo.and_l(B1, E2, b)), K.U.eq(D.Fd(2n, m, o), y, K.Bo.and_r(B1, E2, b)))
    case False{}:
      match t2:
        case True{}:
          +b = e2
          +B2 = U32.is_ne(U32.and(D.Am(m, o), 2), 0)
          +E3 = U32.is_eq(D.Fd(3n, m, o), y)
          k3(K.Bo.not_t(U32.is_eq(U32.and(D.Am(m, o), 2), 0), K.Bo.and_l(B2, E3, b)), K.U.eq(D.Fd(3n, m, o), y, K.Bo.and_r(B2, E3, b)))
        case False{}:
          match t3:
            case True{}:
              +b = e3
              +B4 = U32.is_ne(U32.and(D.Am(m, o), 4), 0)
              +E4 = U32.is_eq(D.Fd(4n, m, o), y)
              k4(K.Bo.not_t(U32.is_eq(U32.and(D.Am(m, o), 4), 0), K.Bo.and_l(B4, E4, b)), K.U.eq(D.Fd(4n, m, o), y, K.Bo.and_r(B4, E4, b)))
            case False{}:
              Empty.absurd(G, h)

def ow.pos(+m: Cr.Cir.Cells, +o: U32, +y: U32, -G: Type, h: N.Le(1n, D.Ow(m, o, y)),
  k2: {U32.is_zero(U32.and(D.Am(m, o), 1)) == False{} : Bool} -> {D.Fd(2n, m, o) == y : U32} -> G,
  k3: {U32.is_zero(U32.and(D.Am(m, o), 2)) == False{} : Bool} -> {D.Fd(3n, m, o) == y : U32} -> G,
  k4: {U32.is_zero(U32.and(D.Am(m, o), 4)) == False{} : Bool} -> {D.Fd(4n, m, o) == y : U32} -> G) -> G:
  +a = D.Am(m, o)
  ow.pos.c(Bool.and(U32.is_ne(U32.and(a, 1), 0), U32.is_eq(D.Fd(2n, m, o), y)), Bool.and(U32.is_ne(U32.and(a, 2), 0), U32.is_eq(D.Fd(3n, m, o), y)),
    Bool.and(U32.is_ne(U32.and(a, 4), 0), U32.is_eq(D.Fd(4n, m, o), y)), m, o, y, G, {==}, {==}, {==}, h, k2, k3, k4)

# a part p, by a set bit, of a garbage cell of the zombie size z, not 0, not
# STATIC, whose garbage pointers are not below its count: a smaller zombie size
def pt.zz(+m: Cr.Cir.Cells, +P: List<&2, U32>, +zs: List<&2, D.Zs>, +z: Nat, +am: U32, +bit: U32, +p: U32, +K: U32, +F: U32, +N: U32,
  h: {D.AL.part(m, P, zs, z, am, bit, p, K, F, N) == True{} : Bool}, hon: {U32.is_zero(U32.and(am, bit)) == False{} : Bool},
  hz: {U32.is_zero(p) == False{} : Bool}, hs: {D.Stc(m, p) == False{} : Bool},
  hc: {Nat.is_lt(D.Pp(P, m, p), U32.to_nat(D.Fd(1n, m, p))) == False{} : Bool}) -> {Nat.is_lt(D.Zz(zs, p), z) == True{} : Bool}:
  +L1 = Nat.is_lt(D.Pp(P, m, p), U32.to_nat(D.Fd(1n, m, p)))
  +A1 = Bool.and(D.Has(P, p), Nat.is_lt(D.Zz(zs, p), z))
  +R4 = Bool.or(A1, L1)
  +R3 = Bool.or(D.Stc(m, p), R4)
  +r1 = K.Bo.or_r(U32.is_zero(U32.and(am, bit)), Bool.or(U32.is_zero(p), Bool.and(Cr.Cir.is_cell(p, K, F, N), R3)), h, hon)
  +r2 = K.Bo.or_r(U32.is_zero(p), Bool.and(Cr.Cir.is_cell(p, K, F, N), R3), r1, hz)
  +r3 = K.Bo.and_r(Cr.Cir.is_cell(p, K, F, N), R3, r2)
  +r4 = K.Bo.or_r(D.Stc(m, p), R4, r3, hs)
  K.Bo.and_r(D.Has(P, p), Nat.is_lt(D.Zz(zs, p), z), K.Bo.or_l(A1, L1, r4, hc))

# no part of zombie size z gives a cell of zombie size at least z
def pt.no(+m: Cr.Cir.Cells, +P: List<&2, U32>, +zs: List<&2, D.Zs>, +z: Nat, +am: U32, +bit: U32, +p: U32, +K: U32, +F: U32, +N: U32,
  h: {D.AL.part(m, P, zs, z, am, bit, p, K, F, N) == True{} : Bool}, hon: {U32.is_zero(U32.and(am, bit)) == False{} : Bool},
  hz: {U32.is_zero(p) == False{} : Bool}, hs: {D.Stc(m, p) == False{} : Bool},
  hc: {Nat.is_lt(D.Pp(P, m, p), U32.to_nat(D.Fd(1n, m, p))) == False{} : Bool}, hle: N.Le(z, D.Zz(zs, p))) -> Empty:
  N.not_succ_le(D.Zz(zs, p), N.le_trans(1n+D.Zz(zs, p), z, D.Zz(zs, p), K.Na.lt1(D.Zz(zs, p), z, pt.zz(m, P, zs, z, am, bit, p, K, F, N, h, hon, hz, hs, hc)),
    hle))

# o, a garbage cell that points to y, the cell of the largest zombie size
def al.top.at(+m: Cr.Cir.Cells, +P: List<&2, U32>, +Q: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32, +nx: U32, +y: U32, +o: U32,
  +hcs: {D.AL.cells(P, m, P, Q, zs, K, F, nx) == True{} : Bool}, +hoP: {D.Has(P, o) == True{} : Bool}, how: N.Le(1n, D.Ow(m, o, y)),
  +hz: {U32.is_zero(y) == False{} : Bool}, +hs: {D.Stc(m, y) == False{} : Bool},
  +hc: {Nat.is_lt(D.Pp(P, m, y), U32.to_nat(D.Fd(1n, m, y))) == False{} : Bool}, +ey: {D.Zz(zs, y) == Zmax(P, zs) : Nat}) -> Empty:
  +hxo = al.mem(P, m, P, Q, zs, K, F, nx, o, hoP, hcs)
  +Hd = K.AL.hd(m, Q, o, F, nx)
  +Pt = K.AL.pt(m, P, zs, o, K, F, nx)
  +Ct = K.AL.ct(m, P, Q, o, F, nx)
  +hpt = K.Bo.and_l(Pt, Ct, K.Bo.and_r(Hd, Bool.and(Pt, Ct), hxo))
  +a = D.Am(m, o)
  +z = D.Zz(zs, o)
  +A1 = D.AL.part(m, P, zs, z, a, 1, D.Fd(2n, m, o), K, F, nx)
  +A2 = D.AL.part(m, P, zs, z, a, 2, D.Fd(3n, m, o), K, F, nx)
  +A4 = D.AL.part(m, P, zs, z, a, 4, D.Fd(4n, m, o), K, F, nx)
  +hle = {(%Equal.sym(Nat, D.Zz(zs, y), Zmax(P, zs), ey) : N.Le(z, _); zmax.ge(P, zs, o, hoP)) : N.Le(z, D.Zz(zs, y))}
  ow.pos(m, o, y, Empty, how,
    hon => e => pt.no(m, P, zs, z, a, 1, y, K, F, nx, (%e : {D.AL.part(m, P, zs, z, a, 1, _, K, F, nx) == True{} : Bool};
      K.Bo.and_l(A1, Bool.and(A2, A4), hpt)), hon, hz, hs, hc, hle),
    hon => e => pt.no(m, P, zs, z, a, 2, y, K, F, nx, (%e : {D.AL.part(m, P, zs, z, a, 2, _, K, F, nx) == True{} : Bool};
      K.Bo.and_l(A2, A4, K.Bo.and_r(A1, Bool.and(A2, A4), hpt))), hon, hz, hs, hc, hle),
    hon => e => pt.no(m, P, zs, z, a, 4, y, K, F, nx, (%e : {D.AL.part(m, P, zs, z, a, 4, _, K, F, nx) == True{} : Bool};
      K.Bo.and_r(A2, A4, K.Bo.and_r(A1, Bool.and(A2, A4), hpt))), hon, hz, hs, hc, hle))

# the garbage cell y of the largest zombie size is in the pend list
def al.top(+m: Cr.Cir.Cells, +P: List<&2, U32>, +Q: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32, +nx: U32, +y: U32,
  +hkf: {U32.is_lt(K, F) == True{} : Bool}, +hcs: {D.AL.cells(P, m, P, Q, zs, K, F, nx) == True{} : Bool},
  +hy: {D.Has(P, y) == True{} : Bool}, hyq: {D.Has(Q, y) == False{} : Bool}, +ey: {D.Zz(zs, y) == Zmax(P, zs) : Nat}) -> Empty:
  +hx = al.mem(P, m, P, Q, zs, K, F, nx, y, hy, hcs)
  +Hd = K.AL.hd(m, Q, y, F, nx)
  +Pt = K.AL.pt(m, P, zs, y, K, F, nx)
  +Ct = K.AL.ct(m, P, Q, y, F, nx)
  +hd = K.Bo.and_l(Hd, Bool.and(Pt, Ct), hx)
  +hct = K.Bo.and_r(Pt, Ct, K.Bo.and_r(Hd, Bool.and(Pt, Ct), hx))
  +pp = D.Pp(P, m, y)
  +c0 = U32.to_nat(D.Fd(1n, m, y))
  +n = Nat.sub(U32.to_nat(nx), U32.to_nat(F))
  +PK = Bool.pick(Bool, D.Has(Q, y), Nat.is_eq(pp, 0n), Bool.and(Nat.is_eq(pp, c0), Nat.is_lt(0n, pp)))
  +hpk0 = K.Bo.and_r(Nat.is_eq(D.Pc(n, m, Q, F, y), pp), PK, hct)
  +hpk = {(%hyq : {Bool.pick(Bool, _, Nat.is_eq(pp, 0n), Bool.and(Nat.is_eq(pp, c0), Nat.is_lt(0n, pp))) == True{} : Bool}; hpk0) :
    {Bool.and(Nat.is_eq(pp, c0), Nat.is_lt(0n, pp)) == True{} : Bool}}
  +epc = K.Na.eq(pp, c0, K.Bo.and_l(Nat.is_eq(pp, c0), Nat.is_lt(0n, pp), hpk))
  +hpos = K.Na.lt1(0n, pp, K.Bo.and_r(Nat.is_eq(pp, c0), Nat.is_lt(0n, pp), hpk))
  +hz = K.U.nz(y, K, F, hkf, al.hd.le(m, Q, y, F, nx, hd))
  +hs = al.hd.ns(m, Q, y, F, nx, hd)
  +hc = na.nlt(Nat.is_lt(pp, c0), pp, c0, {==}, (%epc : N.Le(_, pp); N.le_refl(pp)))
  pp.pos(P, m, y, Empty, hpos, +o => +hoP => how => al.top.at(m, P, Q, zs, K, F, nx, y, o, hcs, hoP, how, hz, hs, hc, ey))

# with an empty pend list there is no garbage
def al.nil(+m: Cr.Cir.Cells, +pend: U32, P: List<&2, U32>, +zs: List<&2, D.Zs>, +K: U32, +F: U32, +nx: U32,
  +hkf: {U32.is_lt(K, F) == True{} : Bool}, h: {D.AL(m, pend, P, Nil{}, zs, K, F, nx) == True{} : Bool}) -> {P == Nil{} : List<&2, U32>}:
  match P:
    case Nil{}:
      {==}
    case Con{+o, +rest}:
      +Pl = {Con{o, rest} : List<&2, U32>}
      +n = Nat.sub(U32.to_nat(nx), U32.to_nat(F))
      +C1 = D.AL.cells(Pl, m, Pl, Nil{}, zs, K, F, nx)
      +L1 = D.Lt(n, m, Nil{}, F, nx)
      +S1 = Bool.and(D.Sub(Nil{}, Pl), D.Nodup(Pl))
      +H1 = Bool.and(D.Chain(Nil{}, m, pend), D.Nodup(Nil{}))
      +hc = K.Bo.and_l(C1, L1, K.Bo.and_r(S1, Bool.and(C1, L1), K.Bo.and_r(H1, Bool.and(S1, Bool.and(C1, L1)), h)))
      Empty.absurd({Pl == Nil{} : List<&2, U32>}, zmax.at(rest, o, zs, Empty, +y => +hy => +ey => al.top(m, Pl, Nil{}, zs, K, F, nx, y, hkf, hc, hy, {==}, ey)))

# Distinct cells are few
# ----------------------
#
# Distinct cells, each one of S, are at most |S| (sub.len); the n cells from o
# (Rng) hold each cell from o below o + n (rng.has); so distinct cells from F
# below nx are at most nx - F (cells.few): so few are the walk's frames, and
# its depth, at most twice them, stays far below 2^32.

# |Del(S, x)| + 1 = |S|, for x one of S
def len.del.b(e: Bool, +y: U32, +rest: List<&2, U32>, +x: U32, ey: {U32.is_eq(y, x) == e : Bool},
  h: {Bool.or(e, D.Has(rest, x)) == True{} : Bool},
  k: {D.Has(rest, x) == True{} : Bool} -> {1n+List.length(&2, U32, Del(rest, x)) == List.length(&2, U32, rest) : Nat}) ->
  {1n+List.length(&2, U32, Del(Con{y, rest}, x)) == List.length(&2, U32, Con{y, rest}) : Nat}:
  match e:
    case True{}:
      (%Equal.sym(Bool, U32.is_eq(y, x), True{}, ey) :
        {1n+List.length(&2, U32, Bool.pick(List<&2, U32>, _, rest, Con{y, Del(rest, x)})) == 1n+List.length(&2, U32, rest) : Nat}; {==})
    case False{}:
      (%Equal.sym(Bool, U32.is_eq(y, x), False{}, ey) :
        {1n+List.length(&2, U32, Bool.pick(List<&2, U32>, _, rest, Con{y, Del(rest, x)})) == 1n+List.length(&2, U32, rest) : Nat};
        Equal.cong(Nat, Nat, z => 1n+z, 1n+List.length(&2, U32, Del(rest, x)), List.length(&2, U32, rest), k(h)))

def len.del(S: List<&2, U32>, +x: U32, h: {D.Has(S, x) == True{} : Bool}) ->
  {1n+List.length(&2, U32, Del(S, x)) == List.length(&2, U32, S) : Nat}:
  match S:
    case Nil{}:
      K.Bo.tf({1n == 0n : Nat}, h)
    case Con{+y, +rest}:
      len.del.b(U32.is_eq(y, x), y, rest, x, {==}, h, hr => len.del(rest, x, hr))

# distinct cells, each one of S, are at most |S|
def sub.len(xs: List<&2, U32>, +S: List<&2, U32>, hn: {D.Nodup(xs) == True{} : Bool}, hs: {D.Sub(xs, S) == True{} : Bool}) ->
  N.Le(List.length(&2, U32, xs), List.length(&2, U32, S)):
  match xs:
    case Nil{}:
      N.le_zero(List.length(&2, U32, S))
    case Con{+x, +rest}:
      +hn2 = hn
      +hs2 = hs
      +hx = K.Bo.and_l(D.Has(S, x), D.Sub(rest, S), hs2)
      +hrs = K.Bo.and_r(D.Has(S, x), D.Sub(rest, S), hs2)
      +hnx = K.Bo.not_t(D.Has(rest, x), K.Bo.and_l(Bool.not(D.Has(rest, x)), D.Nodup(rest), hn2))
      +hnr = K.Bo.and_r(Bool.not(D.Has(rest, x)), D.Nodup(rest), hn2)
      N.le_rw_r(1n+List.length(&2, U32, rest), 1n+List.length(&2, U32, Del(S, x)), List.length(&2, U32, S), len.del(S, x, hx),
        sub.len(rest, Del(S, x), hnr, sub.del(rest, S, x, hrs, hnx)))

# the n cells from o
def Rng(n: Nat, +o: U32) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Con{o, Rng(p, U32.inc(o))}

def rng.len(n: Nat, +o: U32) -> {List.length(&2, U32, Rng(n, o)) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z, List.length(&2, U32, Rng(p, U32.inc(o))), p, rng.len(p, U32.inc(o)))

# a cell q from o below o + n, all below N, is one of the n cells from o
def rng.has.b(e: Bool, +p: Nat, +o: U32, +q: U32, +N: U32, +eo: {U32.is_eq(o, q) == e : Bool}, +h1: N.Le(U32.to_nat(o), U32.to_nat(q)),
  +h2: N.Le(1n+U32.to_nat(q), Nat.add(U32.to_nat(o), 1n+p)), +ei: {U32.to_nat(U32.inc(o)) == 1n+U32.to_nat(o) : Nat},
  +eI: {1n+Nat.add(U32.to_nat(o), p) == Nat.add(U32.to_nat(U32.inc(o)), p) : Nat}, +hb2: N.Le(Nat.add(U32.to_nat(U32.inc(o)), p), U32.to_nat(N)),
  k: N.Le(U32.to_nat(U32.inc(o)), U32.to_nat(q)) -> N.Le(1n+U32.to_nat(q), Nat.add(U32.to_nat(U32.inc(o)), p)) ->
    N.Le(Nat.add(U32.to_nat(U32.inc(o)), p), U32.to_nat(N)) -> {D.Has(Rng(p, U32.inc(o)), q) == True{} : Bool}) ->
  {Bool.or(e, D.Has(Rng(p, U32.inc(o)), q)) == True{} : Bool}:
  match e:
    case True{}:
      {==}
    case False{}:
      +x = U32.to_nat(o)
      +hlt = lt.of.ne(o, q, h1, eo)
      k(N.le_rw_l(1n+x, U32.to_nat(U32.inc(o)), U32.to_nat(q), Equal.sym(Nat, U32.to_nat(U32.inc(o)), 1n+x, ei), hlt),
        N.le_rw_r(1n+U32.to_nat(q), Nat.add(x, 1n+p), Nat.add(U32.to_nat(U32.inc(o)), p), Equal.trans(Nat, Nat.add(x, 1n+p), 1n+Nat.add(x, p),
          Nat.add(U32.to_nat(U32.inc(o)), p), N.add_succ_r(x, p), eI), h2), hb2)

def rng.has(n: Nat, +o: U32, +q: U32, +N: U32, h1: N.Le(U32.to_nat(o), U32.to_nat(q)), h2: N.Le(1n+U32.to_nat(q), Nat.add(U32.to_nat(o), n)),
  hb: N.Le(Nat.add(U32.to_nat(o), n), U32.to_nat(N))) -> {D.Has(Rng(n, o), q) == True{} : Bool}:
  match n:
    case 0n:
      Empty.absurd({D.Has(Rng(0n, o), q) == True{} : Bool}, N.not_succ_le(U32.to_nat(q), N.le_trans(1n+U32.to_nat(q), U32.to_nat(o), U32.to_nat(q),
        N.le_rw_r(1n+U32.to_nat(q), Nat.add(U32.to_nat(o), 0n), U32.to_nat(o), N.add_zero(U32.to_nat(o)), h2), h1)))
    case 1n+(+p):
      +x = U32.to_nat(o)
      +h1b = N.le_rw_l(Nat.add(x, 1n+p), 1n+Nat.add(x, p), U32.to_nat(N), N.add_succ_r(x, p), hb)
      +lt = N.le_trans(1n+x, 1n+Nat.add(x, p), U32.to_nat(N), N.le_add_r(1n+x, p), h1b)
      +ei = K.Ar.u.inc(o, N, lt)
      +eI = Equal.sym(Nat, Nat.add(U32.to_nat(U32.inc(o)), p), 1n+Nat.add(x, p), Equal.cong(Nat, Nat, y => Nat.add(y, p), U32.to_nat(U32.inc(o)), 1n+x, ei))
      +hb2 = N.le_rw_l(1n+Nat.add(x, p), Nat.add(U32.to_nat(U32.inc(o)), p), U32.to_nat(N), eI, h1b)
      rng.has.b(U32.is_eq(o, q), p, o, q, N, {==}, h1, h2, ei, eI, hb2, a => b => c => rng.has(p, U32.inc(o), q, N, a, b, c))

# each of the cells xs is from F, below nx
def In.rng(xs: List<&2, U32>, +F: U32, +nx: U32) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, rest}:
      Bool.and(Bool.and(U32.is_le(F, x), U32.is_lt(x, nx)), In.rng(rest, F, nx))

def rng.sub(xs: List<&2, U32>, +F: U32, +nx: U32, +hfn: {U32.is_le(F, nx) == True{} : Bool}, h: {In.rng(xs, F, nx) == True{} : Bool}) ->
  {D.Sub(xs, Rng(Nat.sub(U32.to_nat(nx), U32.to_nat(F)), F)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      +h2 = h
      +A = Bool.and(U32.is_le(F, x), U32.is_lt(x, nx))
      +hx = K.Bo.and_l(A, In.rng(rest, F, nx), h2)
      +hFx = K.Bo.and_l(U32.is_le(F, x), U32.is_lt(x, nx), hx)
      +hxn = K.Bo.and_r(U32.is_le(F, x), U32.is_lt(x, nx), hx)
      +n = Nat.sub(U32.to_nat(nx), U32.to_nat(F))
      +es = Equal.sym(Nat, Nat.add(U32.to_nat(F), n), U32.to_nat(nx), K.Ar.sub.add(U32.to_nat(F), U32.to_nat(nx), K.U.le(F, nx, hfn)))
      K.Bo.and_i(D.Has(Rng(n, F), x), D.Sub(rest, Rng(n, F)),
        rng.has(n, F, x, nx, K.U.le(F, x, hFx), N.le_rw_r(1n+U32.to_nat(x), U32.to_nat(nx), Nat.add(U32.to_nat(F), n), es, K.U.lt(x, nx, hxn)),
          N.le_rw_l(U32.to_nat(nx), Nat.add(U32.to_nat(F), n), U32.to_nat(nx), es, N.le_refl(U32.to_nat(nx)))),
        rng.sub(rest, F, nx, hfn, K.Bo.and_r(A, In.rng(rest, F, nx), h2)))

# distinct cells from F below nx are at most nx - F
def cells.few(+xs: List<&2, U32>, +F: U32, +nx: U32, hfn: {U32.is_le(F, nx) == True{} : Bool}, hn: {D.Nodup(xs) == True{} : Bool},
  h: {In.rng(xs, F, nx) == True{} : Bool}) -> N.Le(List.length(&2, U32, xs), Nat.sub(U32.to_nat(nx), U32.to_nat(F))):
  +n = Nat.sub(U32.to_nat(nx), U32.to_nat(F))
  N.le_rw_r(List.length(&2, U32, xs), List.length(&2, U32, Rng(n, F)), n, rng.len(n, F), sub.len(xs, Rng(n, F), hn, rng.sub(xs, F, nx, hfn, h)))

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
