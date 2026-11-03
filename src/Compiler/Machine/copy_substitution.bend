# compiler: the copy of the machine computes the kernel's substitution
# ====================================================================
#
# M.copy(r, src) (impl.bend, Machine) puts a term's variables in by copying:
# from a state whose register src holds a cell of the term t, and whose
# register cenv holds a list of clen cells of the terms e_0 .. e_{clen-1}, it
# gives in register r a cell of Term.subst(t, [e_0, ..]), or runs out of
# memory; M.shift(r, v) gives Term.shift(t, amt, 0). Both are M.copy.walk.
#
# The terms of cells are checked terms (Tm): T.tm.of's term, from cells that
# the run may read (Al: a cell of the state, not one of the cells X that an
# allocation may return, nor one of the table's), whose fv bounds the term's
# free variables (FvOK). A Tm stays when the run writes a cell that it does
# not read, or only the count (field 1) of a cell.
#
# The allocation (AL): the cells that M.alloc may take are the cells from
# next on and the garbage P, whose pend list Q is a chain from register pend;
# reusing a garbage cell drops a count of each of its parts, and the counts
# make sure that only garbage reaches 0: a garbage cell out of Q counts
# exactly the garbage's pointers to it, at least one (none point to Q's),
# and a live part of the garbage counts more than them. Only garbage points
# to garbage, and every pointer is below next, so the cell that M.alloc
# takes has no pointer: a new cell counts its one pointer. Each garbage cell
# has a zombie size, the nodes of the term that it stood for, larger than
# its garbage parts': the garbage is well-founded, so once Q is empty, so is
# P. A count is at most the pointers to its cell and 64 (Cb), and next at
# most 214748364, so a count that the copy adds never wraps.
#
# The cover (Cv): every own cell (from F to next) is STATIC, garbage (in P),
# a node of the term of a root, or one of a list of cells (the kept cells,
# E, the walk's stack). A garbage cell is covered by being in P, not through
# a pointer, so no reuse and no dropped count uncovers another cell: the
# cover holds at every step, and whatever a cell points to, if it is an own
# cell, is covered. Its count: the own cells are at most B0 and the garbage.
# A new cell is taken only when Q is empty, so when the garbage is gone, and
# the copy's own cells are at most its result's nodes, its root and a
# shift's root: the copy runs out of memory only when the limit L has fewer
# than 20 (next + 1) bytes at a new cell, below the cells up to F + B0 and
# them.

import Base
import ../../Book/impl.bend as Bk
import ../../Eval/impl.bend as El
import ../../Wasm/impl.bend as Wa
import ../../Program/impl.bend as Pg
import ../Cir/impl.bend as Cr
import ./impl.bend as Mc
import ./cell_terms.bend as T
import ../need_big.bend as N

# Kit
# ---

# a pair of two Data types, itself Data
def P2(-A: Data, -B: Data) -> Data:
  Sigma<&2, &2, A, _ => B>

# a witness x of A, and B(x), as Data
def Ex(-A: Data, -B: @-x: A -> Data) -> Data:
  Sigma<&2, &2, A, B>

def Nat.of(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

# field k of the cell c
def Fd(+k: Nat, +m: Cr.Cir.Cells, +c: U32) -> U32:
  Cr.Cir.Cell.get(k, Cr.Cir.Cells.get(m, c))

# x is one of xs
def Has(xs: List<&2, U32>, +x: U32) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{y, rest}:
      Bool.or(U32.is_eq(y, x), Has(rest, x))

# every one of xs is in ys
def Sub(xs: List<&2, U32>, +ys: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, rest}:
      Bool.and(Has(ys, x), Sub(rest, ys))

# no cell is twice in xs
def Nodup(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, +rest}:
      Bool.and(Bool.not(Has(rest, x)), Nodup(rest))

# the bytes of a limit of lim pages, up to 2^16 pages (definitions.bend's
# Lim.bytes)
def Lim.bytes(lim: U32) -> Nat:
  N.D(16n, U32.to_nat(Wa.Wasm.min(lim, 65536)))

# the bytes of the cells up to F + n (definitions.bend's Cells.bytes)
def Cells.bytes(+F: U32, n: Nat) -> Nat:
  Nat.mul(20n, Nat.add(U32.to_nat(F), n))

# Terms
# -----

# 1 + the highest free variable of t, 0 when it has none (the fv of Img.go, unbounded)
def Fv(t: Bk.Term) -> Nat:
  match t:
    case Bk.Term.Var{i}:
      1n+i
    case Bk.Term.Ref{_}:
      0n
    case Bk.Term.Ann{x, T}:
      Nat.max(Fv(x), Fv(T))
    case Bk.Term.Let{_, v, f}:
      Nat.max(Fv(v), Nat.sub(Fv(f), 1n))
    case Bk.Term.Typ{q}:
      Fv(q)
    case Bk.Term.Min{a, b}:
      Nat.max(Fv(a), Fv(b))
    case Bk.Term.All{_, A, B}:
      Nat.max(Fv(A), Nat.sub(Fv(B), 1n))
    case Bk.Term.Lam{_, f}:
      Nat.sub(Fv(f), 1n)
    case Bk.Term.App{_, f, x}:
      Nat.max(Fv(f), Fv(x))
    case Bk.Term.Sig{_, A, B}:
      Nat.max(Fv(A), Nat.sub(Fv(B), 1n))
    case Bk.Term.Tup{_, a, b}:
      Nat.max(Fv(a), Fv(b))
    case Bk.Term.Prj{h}:
      Fv(h)
    case Bk.Term.Enu{_}:
      0n
    case Bk.Term.Lab{_}:
      0n
    case Bk.Term.Mat{_, h, m}:
      Nat.max(Fv(h), Fv(m))
    case Bk.Term.Efq{}:
      0n
    case Bk.Term.Eql{a, b, T}:
      Nat.max(Fv(a), Nat.max(Fv(b), Fv(T)))
    case Bk.Term.Rfl{}:
      0n
    case Bk.Term.Rwt{e, P, f}:
      Nat.max(Fv(e), Nat.max(Nat.sub(Fv(P), 2n), Fv(f)))

# the nodes of t
def Sz(t: Bk.Term) -> Nat:
  match t:
    case Bk.Term.Var{_}:
      1n
    case Bk.Term.Ref{_}:
      1n
    case Bk.Term.Ann{x, T}:
      1n+Nat.add(Sz(x), Sz(T))
    case Bk.Term.Let{_, v, f}:
      1n+Nat.add(Sz(v), Sz(f))
    case Bk.Term.Typ{q}:
      1n+Sz(q)
    case Bk.Term.Min{a, b}:
      1n+Nat.add(Sz(a), Sz(b))
    case Bk.Term.All{_, A, B}:
      1n+Nat.add(Sz(A), Sz(B))
    case Bk.Term.Lam{_, f}:
      1n+Sz(f)
    case Bk.Term.App{_, f, x}:
      1n+Nat.add(Sz(f), Sz(x))
    case Bk.Term.Sig{_, A, B}:
      1n+Nat.add(Sz(A), Sz(B))
    case Bk.Term.Tup{_, a, b}:
      1n+Nat.add(Sz(a), Sz(b))
    case Bk.Term.Prj{h}:
      1n+Sz(h)
    case Bk.Term.Enu{_}:
      1n
    case Bk.Term.Lab{_}:
      1n
    case Bk.Term.Mat{_, h, m}:
      1n+Nat.add(Sz(h), Sz(m))
    case Bk.Term.Efq{}:
      1n
    case Bk.Term.Eql{a, b, T}:
      1n+Nat.add(Sz(a), Nat.add(Sz(b), Sz(T)))
    case Bk.Term.Rfl{}:
      1n
    case Bk.Term.Rwt{e, P, f}:
      1n+Nat.add(Sz(e), Nat.add(Sz(P), Sz(f)))

# the most nodes of the terms es
def Sz.max(es: List<&2, Bk.Term>) -> Nat:
  match es:
    case Nil{}:
      0n
    case Con{e, rest}:
      Nat.max(Sz(e), Sz.max(rest))

# each variable i of t: i + a does not wrap as a U32
def Fit(t: Bk.Term, +a: U32) -> Bool:
  match t:
    case Bk.Term.Var{+i}:
      U32.is_ge(U32.add(U32.from_nat(i), a), U32.from_nat(i))
    case Bk.Term.Ref{_}:
      True{}
    case Bk.Term.Ann{x, T}:
      Bool.and(Fit(x, a), Fit(T, a))
    case Bk.Term.Let{_, v, f}:
      Bool.and(Fit(v, a), Fit(f, a))
    case Bk.Term.Typ{q}:
      Fit(q, a)
    case Bk.Term.Min{x, y}:
      Bool.and(Fit(x, a), Fit(y, a))
    case Bk.Term.All{_, A, B}:
      Bool.and(Fit(A, a), Fit(B, a))
    case Bk.Term.Lam{_, f}:
      Fit(f, a)
    case Bk.Term.App{_, f, x}:
      Bool.and(Fit(f, a), Fit(x, a))
    case Bk.Term.Sig{_, A, B}:
      Bool.and(Fit(A, a), Fit(B, a))
    case Bk.Term.Tup{_, x, y}:
      Bool.and(Fit(x, a), Fit(y, a))
    case Bk.Term.Prj{h}:
      Fit(h, a)
    case Bk.Term.Enu{_}:
      True{}
    case Bk.Term.Lab{_}:
      True{}
    case Bk.Term.Mat{_, h, m}:
      Bool.and(Fit(h, a), Fit(m, a))
    case Bk.Term.Efq{}:
      True{}
    case Bk.Term.Eql{x, y, T}:
      Bool.and(Fit(x, a), Bool.and(Fit(y, a), Fit(T, a)))
    case Bk.Term.Rfl{}:
      True{}
    case Bk.Term.Rwt{e, P, f}:
      Bool.and(Fit(e, a), Bool.and(Fit(P, a), Fit(f, a)))

# each of es fits the shift by a
def Fits(es: List<&2, Bk.Term>, +a: U32) -> Bool:
  match es:
    case Nil{}:
      True{}
    case Con{e, rest}:
      Bool.and(Fit(e, a), Fits(rest, a))

# what a walk computes, under d binders: a shift by a, or a substitution of e
type Mo is Data:
  Mo.shift{a: Nat}
  Mo.subst{e: List<&2, Bk.Term>}

def Mo.F(+mo: Mo, t: Bk.Term, +d: Nat) -> Bk.Term:
  match mo:
    case Mo.shift{a}:
      El.Term.shift(t, a, d)
    case Mo.subst{e}:
      El.Term.subst(t, e, d)

# Checked terms
# -------------

# x is one of the table's cells (I.table)
def Tbc(+x: U32) -> Bool:
  Bool.and(U32.is_le(272, x), U32.is_le(x, 290))

# the run may read the cell x: one of the state's (image K, first F, next N),
# not one of X, nor one of the table's
def Al(+K: U32, +F: U32, +X: List<&2, U32>, +N: U32, +x: U32) -> Bool:
  Bool.and(Cr.Cir.is_cell(x, K, F, N), Bool.and(Bool.not(Has(X, x)), Bool.not(Tbc(x))))

# the fv fvf of a cell of the tag tag says what the copy needs of its term t:
# a Ref or an Enu has 0, which shares it; another bounds t's free variables,
# unless it is fv_max
def FvOK(tag: Nat, +fvf: U32, t: Bk.Term) -> Bool:
  match tag:
    case 1n:
      U32.is_zero(fvf)
    case 12n:
      U32.is_zero(fvf)
    case _:
      Bool.or(U32.is_eq(fvf, 524287), Nat.is_le(Fv(t), U32.to_nat(fvf)))

def Tm.ok(b: Bool, t: Bk.Term) -> Maybe<&2, Bk.Term>:
  match b:
    case True{}:
      Some{t}
    case False{}:
      None{}

def Tm.chk(+tag: Nat, +fvf: U32, r: Maybe<&2, Bk.Term>) -> Maybe<&2, Bk.Term>:
  match r:
    case None{}:
      None{}
    case Some{+t}:
      Tm.ok(FvOK(tag, fvf, t), t)

def Tm.if(ok: Bool, r: Unit -> Maybe<&2, Bk.Term>) -> Maybe<&2, Bk.Term>:
  match ok:
    case True{}:
      r(Unit{})
    case False{}:
      None{}

# the checked term of the cell c: T.tm.of's, when every cell that it reads may
# be read (Al) and has a right fv (FvOK)
def Tm(fuel: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +K: U32, +F: U32,
  +X: List<&2, U32>, +N: U32, +c: U32) -> Maybe<&2, Bk.Term>:
  match fuel:
    case 0n:
      None{}
    case 1n+(+f):
      +cell = Cr.Cir.Cells.get(m, c)
      +f0 = Cr.Cir.Cell.get(0n, cell)
      +tag = U32.to_nat(U32.and(f0, 63))
      Tm.if(Al(K, F, X, N, c), u => Tm.chk(tag, U32.shrn(f0, 13n),
        T.tm.cell(tag, T.tm.quan(U32.and(U32.shrn(f0, 6n), 3)), c, Cr.Cir.Cell.get(2n, cell), ks, img,
          u => Tm(f, m, ks, img, K, F, X, N, Cr.Cir.Cell.get(2n, cell)),
          u => Tm(f, m, ks, img, K, F, X, N, Cr.Cir.Cell.get(3n, cell)),
          u => Tm(f, m, ks, img, K, F, X, N, Cr.Cir.Cell.get(4n, cell)))))

# the cells that may be read grow from (X, N) to (X2, N2): N2 is at least N,
# and each of X2 is one of X or from N on
def Incl.go(X2: List<&2, U32>, +X: List<&2, U32>, +N: U32) -> Bool:
  match X2:
    case Nil{}:
      True{}
    case Con{+y, rest}:
      Bool.and(Bool.or(Has(X, y), U32.is_le(N, y)), Incl.go(rest, X, N))

def Incl(+X: List<&2, U32>, +N: U32, X2: List<&2, U32>, +N2: U32) -> Bool:
  Bool.and(U32.is_le(N, N2), Incl.go(X2, X, N))

# a term that the run keeps: its fuel, cell and term
type Rt is Data:
  Rt{f: Nat, c: U32, t: Bk.Term}

# the roots rs keep their checked terms
def Rts(+m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +K: U32, +F: U32,
  +X: List<&2, U32>, +N: U32, rs: List<&2, Rt>) -> Data:
  match rs:
    case Nil{}:
      Unit
    case Con{Rt{+f, +c, +t}, rest}:
      P2({Tm(f, m, ks, img, K, F, X, N, c) == Some{t} : Maybe<&2, Bk.Term>}, Rts(m, ks, img, K, F, X, N, rest))

# a cell that the run keeps, field for field: the cell x holds cl
type Kc is Data:
  Kc{x: U32, cl: Cr.Cir.Cell}

# a kept cell: one that may be read and is no term's (a tag of the machine's
# own cells, 19 or more), so the copy never counts it; or one of the cells E
# that the run may not read, also a machine cell of tag 19 or more before N
def Kc.ok(+K: U32, +F: U32, +X: List<&2, U32>, +N: U32, +E: List<&2, U32>, +x: U32, +cl: Cr.Cir.Cell) -> Bool:
  +tg = U32.to_nat(U32.and(Cr.Cir.Cell.get(0n, cl), 63))
  Bool.or(Bool.and(Al(K, F, X, N, x), Nat.is_le(19n, tg)),
    Bool.and(Has(E, x), Bool.and(Bool.and(U32.is_le(F, x), U32.is_lt(x, N)), Nat.is_le(19n, tg))))

# each cell of kc holds its cell, and is kept
def Kcs(+m: Cr.Cir.Cells, +K: U32, +F: U32, +X: List<&2, U32>, +N: U32, +E: List<&2, U32>, kc: List<&2, Kc>) -> Data:
  match kc:
    case Nil{}:
      Unit
    case Con{Kc{+x, +cl}, rest}:
      P2({Cr.Cir.Cells.get(m, x) == cl : Cr.Cir.Cell},
      P2({Kc.ok(K, F, X, N, E, x, cl) == True{} : Bool},
        Kcs(m, K, F, X, N, E, rest)))

# the table by tag (Img.table) is at cell 272
def Tb.go(+m: Cr.Cir.Cells, +i: U32, cs: List<&2, Cr.Cir.Cell>) -> Data:
  match cs:
    case Nil{}:
      Unit
    case Con{+c, rest}:
      P2({Cr.Cir.Cells.get(m, i) == c : Cr.Cir.Cell}, Tb.go(m, U32.inc(i), rest))

def Tb(+m: Cr.Cir.Cells) -> Data:
  Tb.go(m, 272, Mc.Img.table([]))

# The pointers
# ------------
#
# The pointers of a cell, as the heap counts them (definitions.bend's Fs),
# and the pointers to a cell (definitions.bend's Pc).

# a pointer in the list, when b holds
def Ps.opt(b: Bool, +v: U32, +rest: List<&2, U32>) -> List<&2, U32>:
  Bool.pick(List<&2, U32>, b, Con{v, rest}, rest)

# the parts of a term cell of the mask a
def Ps.term(+a: U32, +x2: U32, +x3: U32, +x4: U32) -> List<&2, U32>:
  Ps.opt(U32.is_ne(U32.and(a, 1), 0), x2, Ps.opt(U32.is_ne(U32.and(a, 2), 0), x3, Ps.opt(U32.is_ne(U32.and(a, 4), 0), x4, Nil{})))

# the pointers that the cell o holds, with the pend list Q: a term cell's
# parts, by its table entry; a frame's (tags 32 to 40) field 2, and field 3
# for Rwt, and an OWNED K.arg's field 2, while out of Q
def Ps(+m: Cr.Cir.Cells, +Q: List<&2, U32>, +o: U32) -> List<&2, U32>:
  +f0 = Fd(0n, m, o)
  +tg = U32.and(f0, 63)
  Bool.pick(List<&2, U32>, U32.is_lt(tg, 19),
    Ps.term(Fd(2n, m, U32.add(272, tg)), Fd(2n, m, o), Fd(3n, m, o), Fd(4n, m, o)),
    Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_le(32, tg), U32.is_le(tg, 40)), Bool.not(Has(Q, o))),
      Con{Fd(2n, m, o), Ps.opt(U32.is_eq(tg, 38), Fd(3n, m, o), Nil{})},
      Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_eq(tg, 41), U32.is_ne(U32.and(f0, 4096), 0)), Bool.not(Has(Q, o))),
        [Fd(2n, m, o)], Nil{})))

# how many of xs are c
def Occ(xs: List<&2, U32>, +c: U32) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{x, rest}:
      Nat.add(Nat.of(U32.is_eq(x, c)), Occ(rest, c))

# the pointers to c of the n cells from o, with the pend list Q (Ps; the
# heap's Pc)
def Pc(n: Nat, +m: Cr.Cir.Cells, +Q: List<&2, U32>, +o: U32, +c: U32) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      Nat.add(Occ(Ps(m, Q, o), c), Pc(p, m, Q, U32.inc(o), c))

# each of the cells ys is below N and is 0 or a term cell in m
def All.lt(ys: List<&2, U32>, +m: Cr.Cir.Cells, +N: U32) -> Bool:
  match ys:
    case Nil{}:
      True{}
    case Con{+y, rest}:
      Bool.and(Bool.and(U32.is_lt(y, N), Bool.or(U32.is_zero(y), U32.is_le(U32.and(Fd(0n, m, y), 63), 18))), All.lt(rest, m, N))

# each pointer of the n cells from o, with the pend list Q, is below N and is
# 0 or a term cell (definitions.bend's Pts, with the machine cells excluded)
def Lt(n: Nat, +m: Cr.Cir.Cells, +Q: List<&2, U32>, +o: U32, +N: U32) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(All.lt(Ps(m, Q, o), m, N), Lt(p, m, Q, U32.inc(o), N))

# The allocation
# --------------

# the mask of the parts of the cell o that its reuse drops, as M.alloc reads
# it: its table entry's field 2, for a tag below 32
def Am(+m: Cr.Cir.Cells, +o: U32) -> U32:
  +t = U32.and(Fd(0n, m, o), 63)
  Bool.pick(U32, U32.is_lt(t, 32), Fd(2n, m, U32.add(272, t)), 0)

# the pointers of the cell o to c
def Ow(+m: Cr.Cir.Cells, +o: U32, +c: U32) -> Nat:
  +a = Am(m, o)
  Nat.add(Nat.of(Bool.and(U32.is_ne(U32.and(a, 1), 0), U32.is_eq(Fd(2n, m, o), c))),
    Nat.add(Nat.of(Bool.and(U32.is_ne(U32.and(a, 2), 0), U32.is_eq(Fd(3n, m, o), c))),
      Nat.of(Bool.and(U32.is_ne(U32.and(a, 4), 0), U32.is_eq(Fd(4n, m, o), c)))))

# the pointers of the cells P to c
def Pp(P: List<&2, U32>, +m: Cr.Cir.Cells, +c: U32) -> Nat:
  match P:
    case Nil{}:
      0n
    case Con{+o, rest}:
      Nat.add(Ow(m, o, c), Pp(rest, m, c))

# the cell c is STATIC
def Stc(+m: Cr.Cir.Cells, +c: U32) -> Bool:
  U32.is_ne(U32.and(Fd(0n, m, c), 1024), 0)

# the pend list from p: the cells Q, linked by field 1, then 0
def Chain(Q: List<&2, U32>, +m: Cr.Cir.Cells, +p: U32) -> Bool:
  match Q:
    case Nil{}:
      U32.is_zero(p)
    case Con{+q, rest}:
      Bool.and(U32.is_eq(p, q), Bool.and(Bool.not(U32.is_zero(q)), Chain(rest, m, Fd(1n, m, q))))

# a garbage cell and its zombie size: the nodes of the term that it stood for
type Zs is Data:
  Zs{c: U32, z: Nat}

# the zombie size of the cell p, by the first of zs that is p's (0 when none is)
def Zz(zs: List<&2, Zs>, +p: U32) -> Nat:
  match zs:
    case Nil{}:
      0n
    case Con{Zs{+c, z}, rest}:
      Bool.pick(Nat, U32.is_eq(c, p), z, Zz(rest, p))

# the part p of a garbage cell of the zombie size z, in its mask am at bit:
# none, a cell that is STATIC, garbage of a smaller zombie size, or a live one,
# which counts more than the garbage's pointers to it
def AL.part(+m: Cr.Cir.Cells, +P: List<&2, U32>, +zs: List<&2, Zs>, +z: Nat, +am: U32, +bit: U32, +p: U32, +K: U32,
  +F: U32, +N: U32) -> Bool:
  Bool.or(U32.is_zero(U32.and(am, bit)), Bool.or(U32.is_zero(p), Bool.and(Cr.Cir.is_cell(p, K, F, N),
    Bool.or(Stc(m, p), Bool.or(Bool.and(Has(P, p), Nat.is_lt(Zz(zs, p), z)),
      Nat.is_lt(Pp(P, m, p), U32.to_nat(Fd(1n, m, p))))))))

# each garbage cell of os: one of the machine's own, not STATIC, a term cell
# or, in the pend list, one of the machine's own kinds (so its mask is the
# table's, and its pointers are its parts'), its parts as above; the
# garbage's pointers are all the own cells' pointers to it; one of the pend
# list has none, another counts exactly them, at least one
def AL.cells(os: List<&2, U32>, +m: Cr.Cir.Cells, +P: List<&2, U32>, +Q: List<&2, U32>, +zs: List<&2, Zs>, +K: U32,
  +F: U32, +N: U32) -> Bool:
  match os:
    case Nil{}:
      True{}
    case Con{+o, rest}:
      +am = Am(m, o)
      +tg = U32.and(Fd(0n, m, o), 63)
      +z = Zz(zs, o)
      +pp = Pp(P, m, o)
      Bool.and(Bool.and(Bool.and(Bool.and(U32.is_le(F, o), U32.is_lt(o, N)), Bool.not(Stc(m, o))),
        Bool.or(U32.is_le(tg, 18), Bool.and(U32.is_le(32, tg), Has(Q, o)))),
      Bool.and(Bool.and(AL.part(m, P, zs, z, am, 1, Fd(2n, m, o), K, F, N),
        Bool.and(AL.part(m, P, zs, z, am, 2, Fd(3n, m, o), K, F, N), AL.part(m, P, zs, z, am, 4, Fd(4n, m, o), K, F, N))),
      Bool.and(Bool.and(Nat.is_eq(Pc(Nat.sub(U32.to_nat(N), U32.to_nat(F)), m, Q, F, o), pp),
        Bool.pick(Bool, Has(Q, o), Nat.is_eq(pp, 0n), Bool.and(Nat.is_eq(pp, U32.to_nat(Fd(1n, m, o))), Nat.is_lt(0n, pp)))),
        AL.cells(rest, m, P, Q, zs, K, F, N))))

# the allocation's invariant, with the pend list from pend and the zombie
# sizes zs; and every pointer of an own cell is below N, so a new cell has
# none
def AL(+m: Cr.Cir.Cells, +pend: U32, +P: List<&2, U32>, +Q: List<&2, U32>, +zs: List<&2, Zs>, +K: U32, +F: U32,
  +N: U32) -> Bool:
  Bool.and(Bool.and(Chain(Q, m, pend), Nodup(Q)), Bool.and(Bool.and(Sub(Q, P), Nodup(P)),
    Bool.and(AL.cells(P, m, P, Q, zs, K, F, N), Lt(Nat.sub(U32.to_nat(N), U32.to_nat(F)), m, Q, F, N))))

# The cover
# ---------

# c is a node of the term t at the cell r: r, or a node of one of its parts,
# in the fields that T.tm.cell reads (definitions.bend's Node)
def Node(t: Bk.Term, +m: Cr.Cir.Cells, +r: U32, +c: U32) -> Bool:
  match t:
    case Bk.Term.Var{_}:
      U32.is_eq(r, c)
    case Bk.Term.Ref{_}:
      U32.is_eq(r, c)
    case Bk.Term.Ann{y, z}:
      Bool.or(U32.is_eq(r, c), Bool.or(Node(y, m, Fd(2n, m, r), c), Node(z, m, Fd(3n, m, r), c)))
    case Bk.Term.Let{_, v, f}:
      Bool.or(U32.is_eq(r, c), Bool.or(Node(v, m, Fd(2n, m, r), c), Node(f, m, Fd(3n, m, r), c)))
    case Bk.Term.Typ{y}:
      Bool.or(U32.is_eq(r, c), Node(y, m, Fd(2n, m, r), c))
    case Bk.Term.Min{a, b}:
      Bool.or(U32.is_eq(r, c), Bool.or(Node(a, m, Fd(2n, m, r), c), Node(b, m, Fd(3n, m, r), c)))
    case Bk.Term.All{_, a, b}:
      Bool.or(U32.is_eq(r, c), Bool.or(Node(a, m, Fd(2n, m, r), c), Node(b, m, Fd(3n, m, r), c)))
    case Bk.Term.Lam{_, f}:
      Bool.or(U32.is_eq(r, c), Node(f, m, Fd(2n, m, r), c))
    case Bk.Term.App{_, f, y}:
      Bool.or(U32.is_eq(r, c), Bool.or(Node(f, m, Fd(2n, m, r), c), Node(y, m, Fd(3n, m, r), c)))
    case Bk.Term.Sig{_, a, b}:
      Bool.or(U32.is_eq(r, c), Bool.or(Node(a, m, Fd(2n, m, r), c), Node(b, m, Fd(3n, m, r), c)))
    case Bk.Term.Tup{_, a, b}:
      Bool.or(U32.is_eq(r, c), Bool.or(Node(a, m, Fd(2n, m, r), c), Node(b, m, Fd(3n, m, r), c)))
    case Bk.Term.Prj{h}:
      Bool.or(U32.is_eq(r, c), Node(h, m, Fd(2n, m, r), c))
    case Bk.Term.Enu{_}:
      U32.is_eq(r, c)
    case Bk.Term.Lab{_}:
      U32.is_eq(r, c)
    case Bk.Term.Mat{_, h, n}:
      Bool.or(U32.is_eq(r, c), Bool.or(Node(h, m, Fd(3n, m, r), c), Node(n, m, Fd(4n, m, r), c)))
    case Bk.Term.Efq{}:
      U32.is_eq(r, c)
    case Bk.Term.Eql{a, b, y}:
      Bool.or(U32.is_eq(r, c), Bool.or(Node(a, m, Fd(2n, m, r), c), Bool.or(Node(b, m, Fd(3n, m, r), c), Node(y, m, Fd(4n, m, r), c))))
    case Bk.Term.Rfl{}:
      U32.is_eq(r, c)
    case Bk.Term.Rwt{e, y, f}:
      Bool.or(U32.is_eq(r, c), Bool.or(Node(e, m, Fd(2n, m, r), c), Bool.or(Node(y, m, Fd(3n, m, r), c), Node(f, m, Fd(4n, m, r), c))))

# c is a node of the term of one of the roots rs
def Nodes(rs: List<&2, Rt>, +m: Cr.Cir.Cells, +c: U32) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case Con{Rt{_, +r, u}, rest}:
      Bool.or(Node(u, m, r, c), Nodes(rest, m, c))

# each of the n cells from c is STATIC, garbage (one of P), a node of the
# term of one of the roots rs, or one of the cells xs
def Cv(n: Nat, +m: Cr.Cir.Cells, +c: U32, +P: List<&2, U32>, +rs: List<&2, Rt>, +xs: List<&2, U32>) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(Bool.or(Stc(m, c), Bool.or(Has(P, c), Bool.or(Nodes(rs, m, c), Has(xs, c)))), Cv(p, m, U32.inc(c), P, rs, xs))

# the cells of the roots rs
def Rt.cells(rs: List<&2, Rt>) -> List<&2, U32>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{Rt{_, c, _}, rest}:
      Con{c, Rt.cells(rest)}

# a temporary: a cell that the run keeps, out of the garbage and no root,
# and the terms that its pointers hold (definitions.bend's TmpE)
type Tmp is Data:
  Tmp{c: U32, held: List<&2, Rt>}

# the temporaries' cells
def Tmp.cells(ts: List<&2, Tmp>) -> List<&2, U32>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{Tmp{c, _}, rest}:
      Con{c, Tmp.cells(rest)}

# the terms that the temporaries hold
def Tmp.held(ts: List<&2, Tmp>) -> List<&2, Rt>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{Tmp{_, h}, rest}:
      List.append(&2, Rt, h, Tmp.held(rest))

# The closure
# -----------
#
# Clo (definitions.bend's): a STATIC own cell points to STATIC cells, a
# temporary to STATIC cells, temporaries or the roots of the terms it holds.

# each of the cells ys is STATIC
def All.static(ys: List<&2, U32>, +m: Cr.Cir.Cells) -> Bool:
  match ys:
    case Nil{}:
      True{}
    case Con{+y, rest}:
      Bool.and(Stc(m, y), All.static(rest, m))

# each of the cells ys is STATIC, one of cs, or one of hc
def All.held(ys: List<&2, U32>, +m: Cr.Cir.Cells, +cs: List<&2, U32>, +hc: List<&2, U32>) -> Bool:
  match ys:
    case Nil{}:
      True{}
    case Con{+y, rest}:
      Bool.and(Bool.or(Stc(m, y), Bool.or(Has(cs, y), Has(hc, y))), All.held(rest, m, cs, hc))

# the pointers of the cell c: to STATIC cells when c is STATIC; to STATIC
# cells, temporaries (cs) or the roots of the terms that they hold (hc) when
# c is a temporary
def Clo.at(+m: Cr.Cir.Cells, +c: U32, +Q: List<&2, U32>, +cs: List<&2, U32>, +hc: List<&2, U32>) -> Bool:
  Bool.and(Bool.or(Bool.not(Stc(m, c)), All.static(Ps(m, Q, c), m)),
    Bool.or(Bool.not(Has(cs, c)), All.held(Ps(m, Q, c), m, cs, hc)))

# Clo.at of each of the n cells from c, but the cells E
def Clo(n: Nat, +m: Cr.Cir.Cells, +c: U32, +Q: List<&2, U32>, +cs: List<&2, U32>, +hc: List<&2, U32>, +E: List<&2, U32>) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(Bool.or(Has(E, c), Clo.at(m, c, Q, cs, hc)), Clo(p, m, U32.inc(c), Q, cs, hc, E))

# What stays
# ----------
#
# What a copy keeps of the cells that it does not take: their fields 0 and
# 2 to 4, and of a live term cell, its count less the pointers to it.

# each of the n cells from c, a term cell neither STATIC nor pending (Q),
# counts at most the pointers to it of the N own cells from F, and 64 more
def Cb(n: Nat, +m: Cr.Cir.Cells, +c: U32, +Q: List<&2, U32>, +F: U32, +N: Nat) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(Bool.or(Bool.or(U32.is_le(19, U32.and(Fd(0n, m, c), 63)), Bool.or(Stc(m, c), Has(Q, c))),
        Nat.is_le(U32.to_nat(Fd(1n, m, c)), Nat.add(64n, Pc(N, m, Q, F, c)))), Cb(p, m, U32.inc(c), Q, F, N))

# the cell c keeps its fields 0, 2, 3 and 4 from m to ms
def Same.at(+m: Cr.Cir.Cells, +ms: Cr.Cir.Cells, +c: U32) -> Bool:
  Bool.and(U32.is_eq(Fd(0n, ms, c), Fd(0n, m, c)), Bool.and(U32.is_eq(Fd(2n, ms, c), Fd(2n, m, c)),
    Bool.and(U32.is_eq(Fd(3n, ms, c), Fd(3n, m, c)), U32.is_eq(Fd(4n, ms, c), Fd(4n, m, c)))))

# each of the n cells from c keeps its fields 0, 2, 3 and 4
def Same(n: Nat, +m: Cr.Cir.Cells, +ms: Cr.Cir.Cells, +c: U32) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(Same.at(m, ms, c), Same(p, m, ms, U32.inc(c)))

# each of the n cells from c that is not one of the taken cells T keeps its
# fields 0, 2, 3 and 4; and, a term cell neither STATIC nor garbage (Pn),
# its count grew as the references to it did: the pointers of the own cells
# (the a cells from F in m with the pend list Q, the b cells from F in ms
# with Qn) and the others, x before and y after
def Kept(n: Nat, +m: Cr.Cir.Cells, +ms: Cr.Cir.Cells, +c: U32, +T: List<&2, U32>, +Pn: List<&2, U32>, +F: U32,
  +a: Nat, +b: Nat, +Q: List<&2, U32>, +Qn: List<&2, U32>, +x: List<&2, U32>, +y: List<&2, U32>) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(Bool.or(Has(T, c), Bool.and(Same.at(m, ms, c),
        Bool.or(Bool.or(U32.is_le(19, U32.and(Fd(0n, m, c), 63)), Bool.or(Stc(m, c), Has(Pn, c))),
          Nat.is_eq(Nat.add(U32.to_nat(Fd(1n, ms, c)), Nat.add(Pc(a, m, Q, F, c), Occ(x, c))),
            Nat.add(U32.to_nat(Fd(1n, m, c)), Nat.add(Pc(b, ms, Qn, F, c), Occ(y, c))))))),
        Kept(p, m, ms, U32.inc(c), T, Pn, F, a, b, Q, Qn, x, y))

# the cells T hold no flag (bits 8 to 12 of field 0)
def Nf(T: List<&2, U32>, +ms: Cr.Cir.Cells) -> Bool:
  match T:
    case Nil{}:
      True{}
    case Con{+c, rest}:
      Bool.and(U32.is_zero(U32.and(Fd(0n, ms, c), 7936)), Nf(rest, ms))

# What the result is made of
# --------------------------

# a new cell c and the old cell s that it copies
type Pr is Data:
  Pr{c: U32, s: U32}

# the old cell that the new cell c copies, by the first of ps that is c's
# (c itself when none is)
def Pr.of(ps: List<&2, Pr>, +c: U32) -> U32:
  match ps:
    case Nil{}:
      c
    case Con{Pr{+n, +s}, rest}:
      Bool.pick(U32, U32.is_eq(n, c), s, Pr.of(rest, c))

# the new cell c (in ms) copies the old cell s (in m): a node of the terms of
# S, with the same low byte of field 0 (its tag and quantity) and, for a Lab
# and a Mat, the same field 2 (its name)
def Cpy(+ms: Cr.Cir.Cells, +m: Cr.Cir.Cells, +S: List<&2, Rt>, +c: U32, +s: U32) -> Bool:
  +f0 = Fd(0n, ms, c)
  +tg = U32.and(f0, 63)
  Bool.and(Nodes(S, m, s), Bool.and(U32.is_eq(U32.and(f0, 255), U32.and(Fd(0n, m, s), 255)),
    Bool.or(Bool.not(Bool.or(U32.is_eq(tg, 13), U32.is_eq(tg, 14))), U32.is_eq(Fd(2n, ms, c), Fd(2n, m, s)))))

# the cell r (in ms) is a new one: taken (T), one pointer counted, no flag
def New(+ms: Cr.Cir.Cells, +T: List<&2, U32>, +r: U32) -> Bool:
  Bool.and(Has(T, r), Bool.and(U32.is_eq(Fd(1n, ms, r), 1), U32.is_zero(U32.and(Fd(0n, ms, r), 7936))))

# the cell r is new and copies the old cell that the pairs ps give it
def Nw(+ms: Cr.Cir.Cells, +m: Cr.Cir.Cells, +S: List<&2, Rt>, +T: List<&2, U32>, +ps: List<&2, Pr>, +r: U32) -> Bool:
  Bool.and(New(ms, T, r), Cpy(ms, m, S, r, Pr.of(ps, r)))

# the term u at the cell r is made of the copied cells: each node is a node
# of the terms of S (the source and the locals) as it was in m, or a new cell
# that, but for a Var, copies an old node of S (by the pairs ps), with its
# parts made so too; a Ref and an Enu, whose fv is 0, are always old (the
# walk shares them), while a Lab, an Efq or a Rfl whose fv field is not 0
# gets a copy
def Made(u: Bk.Term, +ms: Cr.Cir.Cells, +m: Cr.Cir.Cells, +r: U32, +S: List<&2, Rt>, +T: List<&2, U32>, +ps: List<&2, Pr>) ->
  Bool:
  match u:
    case Bk.Term.Var{_}:
      Bool.or(Nodes(S, m, r), New(ms, T, r))
    case Bk.Term.Ref{_}:
      Nodes(S, m, r)
    case Bk.Term.Ann{y, z}:
      Bool.or(Nodes(S, m, r), Bool.and(Nw(ms, m, S, T, ps, r), Bool.and(Made(y, ms, m, Fd(2n, ms, r), S, T, ps), Made(z, ms, m, Fd(3n, ms, r), S, T, ps))))
    case Bk.Term.Let{_, v, f}:
      Bool.or(Nodes(S, m, r), Bool.and(Nw(ms, m, S, T, ps, r), Bool.and(Made(v, ms, m, Fd(2n, ms, r), S, T, ps), Made(f, ms, m, Fd(3n, ms, r), S, T, ps))))
    case Bk.Term.Typ{y}:
      Bool.or(Nodes(S, m, r), Bool.and(Nw(ms, m, S, T, ps, r), Made(y, ms, m, Fd(2n, ms, r), S, T, ps)))
    case Bk.Term.Min{a, b}:
      Bool.or(Nodes(S, m, r), Bool.and(Nw(ms, m, S, T, ps, r), Bool.and(Made(a, ms, m, Fd(2n, ms, r), S, T, ps), Made(b, ms, m, Fd(3n, ms, r), S, T, ps))))
    case Bk.Term.All{_, a, b}:
      Bool.or(Nodes(S, m, r), Bool.and(Nw(ms, m, S, T, ps, r), Bool.and(Made(a, ms, m, Fd(2n, ms, r), S, T, ps), Made(b, ms, m, Fd(3n, ms, r), S, T, ps))))
    case Bk.Term.Lam{_, f}:
      Bool.or(Nodes(S, m, r), Bool.and(Nw(ms, m, S, T, ps, r), Made(f, ms, m, Fd(2n, ms, r), S, T, ps)))
    case Bk.Term.App{_, f, y}:
      Bool.or(Nodes(S, m, r), Bool.and(Nw(ms, m, S, T, ps, r), Bool.and(Made(f, ms, m, Fd(2n, ms, r), S, T, ps), Made(y, ms, m, Fd(3n, ms, r), S, T, ps))))
    case Bk.Term.Sig{_, a, b}:
      Bool.or(Nodes(S, m, r), Bool.and(Nw(ms, m, S, T, ps, r), Bool.and(Made(a, ms, m, Fd(2n, ms, r), S, T, ps), Made(b, ms, m, Fd(3n, ms, r), S, T, ps))))
    case Bk.Term.Tup{_, a, b}:
      Bool.or(Nodes(S, m, r), Bool.and(Nw(ms, m, S, T, ps, r), Bool.and(Made(a, ms, m, Fd(2n, ms, r), S, T, ps), Made(b, ms, m, Fd(3n, ms, r), S, T, ps))))
    case Bk.Term.Prj{h}:
      Bool.or(Nodes(S, m, r), Bool.and(Nw(ms, m, S, T, ps, r), Made(h, ms, m, Fd(2n, ms, r), S, T, ps)))
    case Bk.Term.Enu{_}:
      Nodes(S, m, r)
    case Bk.Term.Lab{_}:
      Bool.or(Nodes(S, m, r), Nw(ms, m, S, T, ps, r))
    case Bk.Term.Mat{_, h, n}:
      Bool.or(Nodes(S, m, r), Bool.and(Nw(ms, m, S, T, ps, r), Bool.and(Made(h, ms, m, Fd(3n, ms, r), S, T, ps), Made(n, ms, m, Fd(4n, ms, r), S, T, ps))))
    case Bk.Term.Efq{}:
      Bool.or(Nodes(S, m, r), Nw(ms, m, S, T, ps, r))
    case Bk.Term.Eql{a, b, y}:
      Bool.or(Nodes(S, m, r), Bool.and(Nw(ms, m, S, T, ps, r), Bool.and(Made(a, ms, m, Fd(2n, ms, r), S, T, ps), Bool.and(Made(b, ms, m, Fd(3n, ms, r), S, T, ps),
        Made(y, ms, m, Fd(4n, ms, r), S, T, ps)))))
    case Bk.Term.Rfl{}:
      Bool.or(Nodes(S, m, r), Nw(ms, m, S, T, ps, r))
    case Bk.Term.Rwt{e, y, f}:
      Bool.or(Nodes(S, m, r), Bool.and(Nw(ms, m, S, T, ps, r), Bool.and(Made(e, ms, m, Fd(2n, ms, r), S, T, ps), Bool.and(Made(y, ms, m, Fd(3n, ms, r), S, T, ps),
        Made(f, ms, m, Fd(4n, ms, r), S, T, ps)))))

# each taken cell of T is a node of the result u at r, or a root given back
# (K.root, 45) to the garbage Pn
def Tk(T: List<&2, U32>, +ms: Cr.Cir.Cells, +u: Bk.Term, +r: U32, +Pn: List<&2, U32>) -> Bool:
  match T:
    case Nil{}:
      True{}
    case Con{+c, rest}:
      Bool.and(Bool.or(Node(u, ms, r, c), Bool.and(U32.is_eq(Fd(0n, ms, c), 45), Has(Pn, c))), Tk(rest, ms, u, r, Pn))

# the garbage after a copy: each of Pn is an old garbage cell (of P) not taken
# (T), or a taken root given back (45) to the pend list Qn
def Gb(Pn: List<&2, U32>, +P: List<&2, U32>, +T: List<&2, U32>, +Qn: List<&2, U32>, +ms: Cr.Cir.Cells) -> Bool:
  match Pn:
    case Nil{}:
      True{}
    case Con{+c, rest}:
      Bool.and(Bool.or(Bool.and(Has(P, c), Bool.not(Has(T, c))), Bool.and(Has(T, c), Bool.and(U32.is_eq(Fd(0n, ms, c), 45), Has(Qn, c)))),
        Gb(rest, P, T, Qn, ms))

# each of the n cells from c is one of T
def In.all(n: Nat, +c: U32, +T: List<&2, U32>) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(Has(T, c), In.all(p, U32.inc(c), T))

# each taken cell of T, but the garbage Pn, counts its pointers: those of the
# n own cells from F, with the pend list Qn, and the result's register, of r
def Tc(T: List<&2, U32>, +ms: Cr.Cir.Cells, +Pn: List<&2, U32>, +Qn: List<&2, U32>, +n: Nat, +F: U32, +r: U32) -> Bool:
  match T:
    case Nil{}:
      True{}
    case Con{+c, rest}:
      Bool.and(Bool.or(Has(Pn, c), Nat.is_eq(U32.to_nat(Fd(1n, ms, c)), Nat.add(Pc(n, ms, Qn, F, c), Occ([r], c)))),
        Tc(rest, ms, Pn, Qn, n, F, r))

# X, when b holds
def Hx(b: Bool, X: Data) -> Data:
  match b:
    case True{}:
      X
    case False{}:
      Unit

# The registers
# -------------

# the n registers of regs from the i-th, each made explicit: the run's own
# code then reads and writes them by computation
def Rg.ex(n: Nat, +regs: List<&2, U32>, +i: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Con{T.tm.reg(regs, i), Rg.ex(p, regs, 1n+i)}

# a register write
type Up is Data:
  Up{i: Nat, v: U32}

# the registers xs after the writes ups, in order
def Ups(ups: List<&2, Up>, xs: List<&2, U32>) -> List<&2, U32>:
  match ups:
    case Nil{}:
      xs
    case Con{Up{i, v}, rest}:
      Ups(rest, List.set(&2, U32, xs, i, v))

# i is one of rs
def Has.nat(rs: List<&2, Nat>, +i: Nat) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case Con{j, rest}:
      Bool.or(Nat.is_eq(j, i), Has.nat(rest, i))

# each write of ups is to a register of rs
def Ups.in(ups: List<&2, Up>, +rs: List<&2, Nat>) -> Bool:
  match ups:
    case Nil{}:
      True{}
    case Con{Up{+i, _}, rest}:
      Bool.and(Has.nat(rs, i), Ups.in(rest, rs))

# the registers that M.shift may write: the alloc's (pend, dx, dr, aq, am),
# sdep, sres, cm, the walk's (ss to snew), t1, t2
def Sh.scratch() -> List<&2, Nat>:
  [3n, 4n, 5n, 6n, 7n, 33n, 40n, 41n, 54n, 55n, 56n, 57n, 58n, 59n, 61n, 62n]

# the registers that M.copy may write: M.shift's, the copy's (cs to croot),
# samt and the result register r
def Cp.scratch(+r: Nat) -> List<&2, Nat>:
  Con{r, List.append(&2, Nat, [30n, 31n, 32n, 34n, 35n, 38n, 39n, 60n], Sh.scratch())}

# The states
# ----------

# a state of the run: the image K, the first cell F, the limit L and the input
# I stay; there is no output
def S(regs: List<&2, U32>, m: Cr.Cir.Cells, next: U32, F: U32, K: U32, pg: U32, L: U32, I: List<&2, Word(8n)>) ->
  Cr.Cir.State:
  Cr.Cir.State{regs, m, next, F, K, pg, L, I, Nil{}, 0}

# st is such a state, and Q holds of its registers, cells, next and pages
def At(st: Cr.Cir.State, +F: U32, +K: U32, +L: U32, +I: List<&2, Word(8n)>,
  Q: List<&2, U32> -> Cr.Cir.Cells -> U32 -> U32 -> Type) -> Type:
  match st:
    case Cr.Cir.State{+rg, +ms, +nx, fi, im, +pg, li, inp, out, outn}:
      Sigma<&1, &1, {S(rg, ms, nx, F, K, pg, L, I) == Cr.Cir.State{rg, ms, nx, fi, im, pg, li, inp, out, outn} : Cr.Cir.State},
        _ => Q(rg, ms, nx, pg)>

# the outcome o: next, with a state of which Q holds, or out of memory only
# when the limit L has fewer than B bytes
def Ok(o: Cr.Cir.Out, +F: U32, +K: U32, +L: U32, +I: List<&2, Word(8n)>, +B: Nat,
  Q: List<&2, U32> -> Cr.Cir.Cells -> U32 -> U32 -> Type) -> Type:
  match o:
    case Cr.Cir.Out.next{st}:
      At(st, F, K, L, I, Q)
    case Cr.Cir.Out.halt{_, _}:
      Empty
    case Cr.Cir.Out.out_of_memory{}:
      N.Le(1n+Lim.bytes(L), B)
    case Cr.Cir.Out.trap{}:
      Empty
    case Cr.Cir.Out.not_done{}:
      Empty

# The claims
# ----------

# what a copy (of the mode mo, from the cell of the term t) leaves: the
# registers of regs but for the writes ups, to the registers rs; in register
# rr the cell r of the result Mo.F(mo, t, 0), with any fuel g, of the cells
# that may be read once the new garbage Pn and the new next may be returned,
# when hx; the allocation's invariant again, of Pn, its pend list Qn and its
# zombie sizes zn; the cells that may be read only grow; the table, the
# roots rs, the terms that the temporaries ts hold and the kept cells kc
# stay; the cover and the closure again, with the result among the roots;
# what the result is made of (Made: the old nodes of S, the source and the
# locals, and new cells, by the pairs ps); the cells taken (T) are the
# result's new nodes and roots given back, the new garbage the old garbage
# not taken and those roots, pending; the taken cells were garbage or new,
# and each new cell is taken; they hold no flag, and but those given back
# they count their pointers, the result's register's too; the others keep
# their fields 0 and 2 to 4 (Kept, and the image's: Same) and their counts
# follow the pointers, the result's register counting one more; when next
# grows, it stays at most 214748364, and the own cells (from F to next) are
# at most Bc, the cells that the out-of-memory budget counts (a new cell is
# taken only once the garbage is gone); and the cells taken, less those
# given back, are at most the result's nodes
type Wt is Data:
  Wt{ups: List<&2, Up>, r: U32, g: Nat, Pn: List<&2, U32>, Qn: List<&2, U32>, zn: List<&2, Zs>, T: List<&2, U32>,
    ps: List<&2, Pr>}

def Post(+hx: Bool, +mo: Mo, +t: Bk.Term, +regs: List<&2, U32>, +scr: List<&2, Nat>, +rr: Nat,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +K: U32, +F: U32, +m: Cr.Cir.Cells, +P: List<&2, U32>,
  +Q: List<&2, U32>, +E: List<&2, U32>, +N: U32, +Bc: Nat, +rs: List<&2, Rt>, +ts: List<&2, Tmp>, +kc: List<&2, Kc>,
  +S: List<&2, Rt>, w: Wt, +rg: List<&2, U32>, +ms: Cr.Cir.Cells, +nx: U32) -> Data:
  match w:
    case Wt{+ups, +r, +g, +Pn, +Qn, +zn, +T, +ps}:
      +n = Nat.sub(U32.to_nat(nx), U32.to_nat(F))
      +n0 = Nat.sub(U32.to_nat(N), U32.to_nat(F))
      +hl = Tmp.held(ts)
      +u = Mo.F(mo, t, 0n)
      P2({rg == Ups(ups, Rg.ex(63n, regs, 0n)) : List<&2, U32>},
      P2({Ups.in(ups, scr) == True{} : Bool},
      P2({T.tm.reg(rg, rr) == r : U32},
      P2(Hx(hx, {Tm(g, ms, ks, img, K, F, List.append(&2, U32, Pn, E), nx, r) == Some{u} : Maybe<&2, Bk.Term>}),
      P2({AL(ms, T.tm.reg(rg, 3n), Pn, Qn, zn, K, F, nx) == True{} : Bool},
      P2({Incl(P, N, Pn, nx) == True{} : Bool},
      P2(Tb(ms),
      P2(Rts(ms, ks, img, K, F, List.append(&2, U32, P, E), N, List.append(&2, Rt, rs, hl)),
      P2(Kcs(ms, K, F, List.append(&2, U32, P, E), N, E, kc),
      P2({Cv(n, ms, F, Pn, Con{Rt{g, r, u}, List.append(&2, Rt, rs, hl)}, List.append(&2, U32, Tmp.cells(ts), E)) == True{} : Bool},
      P2({Clo(n, ms, F, Qn, Tmp.cells(ts), Rt.cells(hl), E) == True{} : Bool},
      P2({Made(u, ms, m, r, S, T, ps) == True{} : Bool},
      P2({Tk(T, ms, u, r, Pn) == True{} : Bool},
      P2({Gb(Pn, P, T, Qn, ms) == True{} : Bool},
      P2({Sub(P, List.append(&2, U32, T, Pn)) == True{} : Bool},
      P2({Incl.go(T, P, N) == True{} : Bool},
      P2({In.all(Nat.sub(U32.to_nat(nx), U32.to_nat(N)), N, T) == True{} : Bool},
      P2({Nf(T, ms) == True{} : Bool},
      P2({Tc(T, ms, Pn, Qn, n, F, r) == True{} : Bool},
      P2({Same(U32.to_nat(K), m, ms, 1) == True{} : Bool},
      P2({Kept(n0, m, ms, F, T, Pn, F, n0, n, Q, Qn, Nil{}, [r]) == True{} : Bool},
      P2({Bool.or(U32.is_eq(nx, N), U32.is_le(nx, 214748364)) == True{} : Bool},
      P2({Bool.or(U32.is_eq(nx, N), Nat.is_le(n, Bc)) == True{} : Bool},
        N.Le(Nat.add(U32.to_nat(nx), List.length(&2, U32, P)),
          Nat.add(U32.to_nat(N), Nat.add(List.length(&2, U32, Pn), Pg.Term.size(u)))))))))))))))))))))))))))

# the cells E that the run may not read: machine cells before nx, none garbage
def Ex.ok(xs: List<&2, U32>, +P: List<&2, U32>, +F: U32, +nx: U32) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, rest}:
      Bool.and(Bool.and(Bool.not(Has(P, x)), Bool.and(U32.is_le(F, x), U32.is_lt(x, nx))), Ex.ok(rest, P, F, nx))

# what the state of a run should be at the start: the image's cells, the
# table, next at most 214748364, the pend list and the zombie sizes zs, the
# counts (Cb), the cells E that it may not read, the roots rs, the
# temporaries ts (own cells, none garbage) and the terms that they hold, the
# kept cells kc, the cover and the closure, and its own cells at most B0 and
# the garbage
def Pre(+regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +F: U32, +K: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +P: List<&2, U32>, +Q: List<&2, U32>, +zs: List<&2, Zs>, +E: List<&2, U32>,
  +rs: List<&2, Rt>, +ts: List<&2, Tmp>, +kc: List<&2, Kc>, +B0: Nat) -> Data:
  +n = Nat.sub(U32.to_nat(nx), U32.to_nat(F))
  +hl = Tmp.held(ts)
  P2({List.length(&2, U32, regs) == 63n : Nat},
  P2({U32.is_le(290, K) == True{} : Bool},
  P2({U32.is_lt(K, F) == True{} : Bool},
  P2({U32.is_le(F, nx) == True{} : Bool},
  P2({U32.is_le(nx, 214748364) == True{} : Bool},
  P2(Tb(m),
  P2({AL(m, T.tm.reg(regs, 3n), P, Q, zs, K, F, nx) == True{} : Bool},
  P2({Cb(n, m, F, Q, F, n) == True{} : Bool},
  P2({Ex.ok(E, P, F, nx) == True{} : Bool},
  P2({Ex.ok(Tmp.cells(ts), P, F, nx) == True{} : Bool},
  P2(Rts(m, ks, img, K, F, List.append(&2, U32, P, E), nx, List.append(&2, Rt, rs, hl)),
  P2(Kcs(m, K, F, List.append(&2, U32, P, E), nx, E, kc),
  P2({Cv(n, m, F, P, List.append(&2, Rt, rs, hl), List.append(&2, U32, Tmp.cells(ts), E)) == True{} : Bool},
  P2({Clo(n, m, F, Q, Tmp.cells(ts), Rt.cells(hl), E) == True{} : Bool},
    N.Le(n, Nat.add(B0, List.length(&2, U32, P)))))))))))))))))

# LAW: M.shift(sres, t2): from a state whose register t2 holds a cell of the
# term t (by Tm, with any fuel g, reading neither the garbage P nor the cells
# E), and samt the amount a, below 2 next, with the start's facts (Pre), some
# fuel gives sres a cell of Term.shift(t, a, 0) when hx, with Post's facts, or
# runs out of memory, only when the limit L has fewer bytes than the cells up
# to F + B0, the result's nodes and the root (and Post's own cells are at
# most these cells). When hx, the free variables of t are below 2^31, so that
# no shifted variable wraps (a depth is below 2 next). E is [] for the
# machine; M.copy passes its frames' cells
law Sh.ok:
  for +regs: List<&2, U32>
  for +m: Cr.Cir.Cells
  for +nx: U32
  for +F: U32
  for +K: U32
  for +pg: U32
  for +L: U32
  for +I: List<&2, Word(8n)>
  for +ks: List<&2, List<&2, Word(8n)>>
  for +img: List<&2, Bk.Term>
  for +P: List<&2, U32>
  for +Q: List<&2, U32>
  for +zs: List<&2, Zs>
  for +E: List<&2, U32>
  for +rs: List<&2, Rt>
  for +ts: List<&2, Tmp>
  for +kc: List<&2, Kc>
  for +B0: Nat
  for +hx: Bool
  for +t: Bk.Term
  for +g: Nat
  for +a: U32
  for pre: Pre(regs, m, nx, F, K, ks, img, P, Q, zs, E, rs, ts, kc, B0)
  for ht: {Tm(g, m, ks, img, K, F, List.append(&2, U32, P, E), nx, T.tm.reg(regs, 62n)) == Some{t} : Maybe<&2, Bk.Term>}
  for ha: {T.tm.reg(regs, 60n) == a : U32}
  for hd: N.Le(U32.to_nat(a), Nat.double(U32.to_nat(nx)))
  for hv: Hx(hx, N.Le(Fv(t), N.D(31n, 1n)))
  exs n: Nat
  Ok(Cr.Cir.exec(n, Mc.M.shift(Mc.R.sres(), Mc.R.t2()), S(regs, m, nx, F, K, pg, L, I)), F, K, L, I,
    Cells.bytes(F, Nat.add(B0, 1n+Pg.Term.size(El.Term.shift(t, U32.to_nat(a), 0n)))),
    rg => ms => nx2 => pg2 => Ex(Wt, w => Post(hx, Mo.shift{U32.to_nat(a)}, t, regs, Sh.scratch(), Mc.R.sres(), ks, img, K, F,
      m, P, Q, E, nx, Nat.add(B0, 1n+Pg.Term.size(El.Term.shift(t, U32.to_nat(a), 0n))), rs, ts, kc, [Rt{g, T.tm.reg(regs, 62n), t}],
      w, rg, ms, nx2)))

# the list of locals from the cell l: a cell of each of es, which may be read,
# no term's (tag 19 or more), its field 2 a cell of its term (by Tm, with any
# fuel), its field 1 the next
def Env(+m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +K: U32, +F: U32,
  +X: List<&2, U32>, +N: U32, +l: U32, es: List<&2, Bk.Term>) -> Data:
  match es:
    case Nil{}:
      Unit
    case Con{+e, rest}:
      P2({Al(K, F, X, N, l) == True{} : Bool},
      P2({Nat.is_le(19n, U32.to_nat(U32.and(Fd(0n, m, l), 63))) == True{} : Bool},
      P2(Ex(Nat, g => {Tm(g, m, ks, img, K, F, X, N, Fd(2n, m, l)) == Some{e} : Maybe<&2, Bk.Term>}),
        Env(m, ks, img, K, F, X, N, Fd(1n, m, l), rest))))

# the locals' terms es as roots, at the cells of the list from l
def Env.rts(es: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +l: U32) -> List<&2, Rt>:
  match es:
    case Nil{}:
      Nil{}
    case Con{e, rest}:
      Con{Rt{0n, Fd(2n, m, l), e}, Env.rts(rest, m, Fd(1n, m, l))}

# the free variables of each of es are below b
def Fvs(es: List<&2, Bk.Term>, +b: Nat) -> Data:
  match es:
    case Nil{}:
      Unit
    case Con{e, rest}:
      P2(N.Le(Fv(e), b), Fvs(rest, b))

# the register of the source of M.copy: wt (a call's leaf) or z (a λ's or a
# let's body), the machine's two calls; the copy goes to n
def Cp.src(wt: Bool) -> Nat:
  match wt:
    case True{}:
      Mc.R.wt()
    case False{}:
      Mc.R.z()

# LAW: M.copy(n, src), src wt or z (Cp.src): from a state whose register src
# holds a cell of the term t (by Tm, reading neither the garbage P nor the
# cells E), cenv the list of the locals es (Env) and clen their number, with
# the start's facts (Pre), some fuel gives n a cell of Term.subst(t, es, 0)
# when hx, with Post's facts (S: the source and the locals), or runs out of
# memory, only when the limit L has fewer bytes than the cells up to F + B0,
# the result's nodes, the root and a shift's root (and Post's own cells are
# at most these cells). When hx, the free variables of the locals are below
# 2^31, so that no shifted variable wraps
law Cp.ok:
  for +wt: Bool
  for +regs: List<&2, U32>
  for +m: Cr.Cir.Cells
  for +nx: U32
  for +F: U32
  for +K: U32
  for +pg: U32
  for +L: U32
  for +I: List<&2, Word(8n)>
  for +ks: List<&2, List<&2, Word(8n)>>
  for +img: List<&2, Bk.Term>
  for +P: List<&2, U32>
  for +Q: List<&2, U32>
  for +zs: List<&2, Zs>
  for +E: List<&2, U32>
  for +rs: List<&2, Rt>
  for +ts: List<&2, Tmp>
  for +kc: List<&2, Kc>
  for +B0: Nat
  for +hx: Bool
  for +t: Bk.Term
  for +g: Nat
  for +es: List<&2, Bk.Term>
  for pre: Pre(regs, m, nx, F, K, ks, img, P, Q, zs, E, rs, ts, kc, B0)
  for ht: {Tm(g, m, ks, img, K, F, List.append(&2, U32, P, E), nx, T.tm.reg(regs, Cp.src(wt))) == Some{t} : Maybe<&2, Bk.Term>}
  for he: Env(m, ks, img, K, F, List.append(&2, U32, P, E), nx, T.tm.reg(regs, 36n), es)
  for hl: {U32.to_nat(T.tm.reg(regs, 37n)) == List.length(&2, Bk.Term, es) : Nat}
  for hv: Hx(hx, Fvs(es, N.D(31n, 1n)))
  exs n: Nat
  Ok(Cr.Cir.exec(n, Mc.M.copy(Mc.R.n(), Cp.src(wt)), S(regs, m, nx, F, K, pg, L, I)), F, K, L, I,
    Cells.bytes(F, Nat.add(B0, 2n+Pg.Term.size(El.Term.subst(t, es, 0n)))),
    rg => ms => nx2 => pg2 => Ex(Wt, w => Post(hx, Mo.subst{es}, t, regs, Cp.scratch(Mc.R.n()), Mc.R.n(), ks, img, K, F,
      m, P, Q, E, nx, Nat.add(B0, 2n+Pg.Term.size(El.Term.subst(t, es, 0n))), rs, ts, kc,
      Con{Rt{g, T.tm.reg(regs, Cp.src(wt)), t}, Env.rts(es, m, T.tm.reg(regs, 36n))}, w, rg, ms, nx2)))
