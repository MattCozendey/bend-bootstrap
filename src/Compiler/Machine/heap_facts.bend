# compiler: the shared heap, for M.data and M.walk (layer B)
# ==========================================================
#
# Facts of definitions.bend's heap (Fs, Pc, Ptr, Is) that the phases
# which take cells need, beyond the heap's operations:
#
#   ptr.part: a part of a node c of a term, where c is one of the machine's
#     own cells, has a pointer (Ptr >= 1): c is a term cell, whose mask in
#     the table (Tbl) names the part, and Pc counts c's pointers (Pc.at).
#   part.ne, is.fz: so a cell z that nothing points to (Ptr 0) and that is
#     not STATIC is no node of a term that Is says, and a store to z keeps
#     every such term (is.fz, by induction on the term).
#   The registers: List.get after List.set (rg.*), Kept after a set.
#
# It imports only definitions.bend and what that file imports.

import Base
import ../../Book/impl.bend as Bk
import ../../Eval/impl.bend as El
import ../Cir/impl.bend as Cr
import ./impl.bend as Mc
import ./cell_terms.bend as T
import ../need_big.bend as N
import ./definitions.bend as PM

# Kit
# ---

def and.l(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def and.r(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      PM.bool.ft({b == True{} : Bool}, h)

def or.r(b: Bool, -c: Bool, h: {c == True{} : Bool}) -> {Bool.or(b, c) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      h

# Numbers
# -------

# 2a <= 2b gives a <= b
def dle(a: Nat, b: Nat, h: N.Le(Nat.double(a), Nat.double(b))) -> N.Le(a, b):
  match a:
    case 0n:
      N.le_zero(b)
    case 1n+p:
      match b:
        case 0n:
          Empty.absurd(N.Le(1n+p, 0n), h)
        case 1n+q:
          dle(p, q, h)

# 2 + 2a <= 1 + 2b gives 1 + a <= b
def dle1(a: Nat, b: Nat, h: N.Le(2n+Nat.double(a), 1n+Nat.double(b))) -> N.Le(1n+a, b):
  match a:
    case 0n:
      match b:
        case 0n:
          Empty.absurd(N.Le(1n, 0n), h)
        case 1n+q:
          N.le_zero(q)
    case 1n+p:
      match b:
        case 0n:
          Empty.absurd(N.Le(2n+p, 0n), h)
        case 1n+q:
          dle1(p, q, h)

# a word below another one adds 1 when it grows
def w.inc(+n: Nat, w: Word(n), w2: Word(n), h: N.Le(1n+Word.to_nat(n, w), Word.to_nat(n, w2))) ->
  {Word.to_nat(n, Word.inc(n, w)) == 1n+Word.to_nat(n, w) : Nat}:
  match n:
    case 0n:
      match w w2:
        case WNil{} WNil{}:
          Empty.absurd({0n == 1n : Nat}, h)
    case 1n+p:
      match w w2:
        case WCon{False{}, t} _:
          {==}
        case WCon{True{}, +t} WCon{False{}, +t2}:
          %Equal.sym(Nat, Word.to_nat(p, Word.inc(p, t)), 1n+Word.to_nat(p, t), w.inc(p, t, t2, dle(1n+Word.to_nat(p, t), Word.to_nat(p, t2), h))) :
            {Nat.double(_) == 2n+Nat.double(Word.to_nat(p, t)) : Nat}
          {==}
        case WCon{True{}, +t} WCon{True{}, +t2}:
          %Equal.sym(Nat, Word.to_nat(p, Word.inc(p, t)), 1n+Word.to_nat(p, t), w.inc(p, t, t2, dle1(Word.to_nat(p, t), Word.to_nat(p, t2), h))) :
            {Nat.double(_) == 2n+Nat.double(Word.to_nat(p, t)) : Nat}
          {==}

# a U32 below another one adds 1 when it grows
def u.inc(+a: U32, +b: U32, h: N.Le(1n+U32.to_nat(a), U32.to_nat(b))) -> {U32.to_nat(U32.inc(a)) == 1n+U32.to_nat(a) : Nat}:
  match a b:
    case U32{x} U32{y}:
      w.inc(32n, x, y, h)

# what the comparisons of U32s say of their numbers
def rel.lt(c: Cmp, +x: Nat, +y: Nat, r: N.Rel(c, x, y), e: {Cmp.is_lt(c) == True{} : Bool}) -> N.Le(1n+x, y):
  match c:
    case LT{}:
      r
    case EQ{}:
      PM.bool.ft(N.Le(1n+x, y), e)
    case GT{}:
      PM.bool.ft(N.Le(1n+x, y), e)

def lt.ne(c: Cmp, +x: Nat, +y: Nat, r: N.Rel(c, x, y), ne: {Cmp.is_eq(c) == False{} : Bool}, le: N.Le(x, y)) -> N.Le(1n+x, y):
  match c:
    case LT{}:
      r
    case EQ{}:
      Empty.absurd(N.Le(1n+x, y), N.true_ne_false(ne))
    case GT{}:
      Empty.absurd(N.Le(1n+x, y), N.not_succ_le(y, N.le_trans(1n+y, x, y, r, le)))

def u.le(+a: U32, +b: U32, e: {U32.is_le(a, b) == True{} : Bool}) -> N.Le(U32.to_nat(a), U32.to_nat(b)):
  N.rel_le(U32.cmp(a, b), U32.to_nat(a), U32.to_nat(b), N.U32.rel(a, b), N.toT(U32.is_le(a, b), e))

def u.lt(+a: U32, +b: U32, e: {U32.is_lt(a, b) == True{} : Bool}) -> N.Le(1n+U32.to_nat(a), U32.to_nat(b)):
  rel.lt(U32.cmp(a, b), U32.to_nat(a), U32.to_nat(b), N.U32.rel(a, b), e)

# f + (x - f) = x, when f <= x
def add.sub(f: Nat, x: Nat, h: N.Le(f, x)) -> {Nat.add(f, Nat.sub(x, f)) == x : Nat}:
  match f:
    case 0n:
      match x:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case 1n+p:
      match x:
        case 0n:
          Empty.absurd({1n+Nat.add(p, 0n) == 0n : Nat}, h)
        case 1n+q:
          %add.sub(p, q, h) : {1n+Nat.add(p, Nat.sub(q, p)) == 1n+_ : Nat}
          {==}

# Pointers
# --------

# RcL counts c in a list where c is
def rcl.mem.b(b: Bool, -M: Bool, +r: Nat, hm: {Bool.or(b, M) == True{} : Bool}, ih: {M == True{} : Bool} -> N.Le(1n, r)) ->
  N.Le(1n, Nat.add(PM.Nat.of(b), r)):
  match b:
    case True{}:
      N.le_zero(r)
    case False{}:
      ih(hm)

def rcl.mem(xs: List<&2, U32>, +c: U32, h: {PM.Mem(xs, c) == True{} : Bool}) -> N.Le(1n, PM.RcL(xs, c)):
  match xs:
    case Nil{}:
      PM.bool.ft(N.Le(1n, 0n), h)
    case Con{+x, +rest}:
      rcl.mem.b(U32.is_eq(x, c), PM.Mem(rest, c), PM.RcL(rest, c), h, e => rcl.mem(rest, c, e))

# c is in a list that starts with it
def mem.hd(+x: U32, -rest: List<&2, U32>) -> {PM.Mem(Con{x, rest}, x) == True{} : Bool}:
  %Equal.sym(Bool, U32.is_eq(x, x), True{}, PM.u32.refl(x)) : {Bool.or(_, PM.Mem(rest, x)) == True{} : Bool}
  {==}

def mem.tl(+x: U32, +c: U32, -rest: List<&2, U32>, h: {PM.Mem(rest, c) == True{} : Bool}) -> {PM.Mem(Con{x, rest}, c) == True{} : Bool}:
  or.r(U32.is_eq(x, c), PM.Mem(rest, c), h)

# the cell p, at or after o and before n cells from o, counts its pointers to
# c in Pc
def Pc.at.b(b: Bool, +k: Nat, +m: Cr.Cir.Cells, +ps: List<&2, U32>, +o: U32, +p: U32, +c: U32, eb: {U32.is_eq(o, p) == b : Bool},
  h1: N.Le(U32.to_nat(o), U32.to_nat(p)), h2: N.Le(1n+U32.to_nat(p), Nat.add(U32.to_nat(o), 1n+k)),
  ih: N.Le(U32.to_nat(U32.inc(o)), U32.to_nat(p)) -> N.Le(1n+U32.to_nat(p), Nat.add(U32.to_nat(U32.inc(o)), k)) ->
    N.Le(PM.RcL(PM.Fs(m, ps, p), c), PM.Pc(k, m, ps, U32.inc(o), c))) ->
  N.Le(PM.RcL(PM.Fs(m, ps, p), c), Nat.add(PM.RcL(PM.Fs(m, ps, o), c), PM.Pc(k, m, ps, U32.inc(o), c))):
  match b:
    case True{}:
      %Equal.sym(U32, o, p, PM.u32.eq(o, p, eb)) : N.Le(PM.RcL(PM.Fs(m, ps, p), c), Nat.add(PM.RcL(PM.Fs(m, ps, _), c), PM.Pc(k, m, ps, U32.inc(o), c)))
      N.le_add_r(PM.RcL(PM.Fs(m, ps, p), c), PM.Pc(k, m, ps, U32.inc(o), c))
    case False{}:
      +lt = lt.ne(U32.cmp(o, p), U32.to_nat(o), U32.to_nat(p), N.U32.rel(o, p), eb, h1)
      +ei = u.inc(o, p, lt)
      +h1b = N.le_rw_l(1n+U32.to_nat(o), U32.to_nat(U32.inc(o)), U32.to_nat(p), Equal.sym(Nat, U32.to_nat(U32.inc(o)), 1n+U32.to_nat(o), ei), lt)
      +h2b = N.le_rw_r(1n+U32.to_nat(p), Nat.add(U32.to_nat(o), 1n+k), Nat.add(U32.to_nat(U32.inc(o)), k),
        Equal.trans(Nat, Nat.add(U32.to_nat(o), 1n+k), 1n+Nat.add(U32.to_nat(o), k), Nat.add(U32.to_nat(U32.inc(o)), k),
          N.add_succ_r(U32.to_nat(o), k),
          Equal.sym(Nat, Nat.add(U32.to_nat(U32.inc(o)), k), 1n+Nat.add(U32.to_nat(o), k),
            Equal.cong(Nat, Nat, x => Nat.add(x, k), U32.to_nat(U32.inc(o)), 1n+U32.to_nat(o), ei))), h2)
      N.le_trans(PM.RcL(PM.Fs(m, ps, p), c), PM.Pc(k, m, ps, U32.inc(o), c), Nat.add(PM.RcL(PM.Fs(m, ps, o), c), PM.Pc(k, m, ps, U32.inc(o), c)),
        ih(h1b, h2b), N.le_add_l(PM.RcL(PM.Fs(m, ps, o), c), PM.Pc(k, m, ps, U32.inc(o), c)))

def Pc.at(n: Nat, +m: Cr.Cir.Cells, +ps: List<&2, U32>, +o: U32, +p: U32, +c: U32,
  h1: N.Le(U32.to_nat(o), U32.to_nat(p)), h2: N.Le(1n+U32.to_nat(p), Nat.add(U32.to_nat(o), n))) ->
  N.Le(PM.RcL(PM.Fs(m, ps, p), c), PM.Pc(n, m, ps, o, c)):
  match n:
    case 0n:
      Empty.absurd(N.Le(PM.RcL(PM.Fs(m, ps, p), c), 0n),
        N.not_succ_le(U32.to_nat(p), N.le_trans(1n+U32.to_nat(p), U32.to_nat(o), U32.to_nat(p),
          N.le_rw_r(1n+U32.to_nat(p), Nat.add(U32.to_nat(o), 0n), U32.to_nat(o), N.add_zero(U32.to_nat(o)), h2), h1)))
    case 1n+(+k):
      Pc.at.b(U32.is_eq(o, p), k, m, ps, o, p, c, {==}, h1, h2, x => y => Pc.at(k, m, ps, U32.inc(o), p, c, x, y))

# a cell of the machine's own counts its pointers to c in Ptr
def Ptr.at(+m: Cr.Cir.Cells, +nx: U32, +fi: U32, +ps: List<&2, U32>, +rs: List<&2, U32>, +p: U32, +c: U32,
  own: {PM.Own(fi, nx, p) == True{} : Bool}) ->
  N.Le(PM.RcL(PM.Fs(m, ps, p), c), PM.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, rs, c)):
  +o2 = own
  +h1 = u.le(fi, p, and.l(U32.is_le(fi, p), U32.is_lt(p, nx), o2))
  +hl = u.lt(p, nx, and.r(U32.is_le(fi, p), U32.is_lt(p, nx), o2))
  +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
  +es = add.sub(U32.to_nat(fi), U32.to_nat(nx), N.le_trans(U32.to_nat(fi), U32.to_nat(p), U32.to_nat(nx), h1, N.weaken(U32.to_nat(p), U32.to_nat(nx), hl)))
  N.le_trans(PM.RcL(PM.Fs(m, ps, p), c), PM.Pc(n, m, ps, fi, c), PM.Ptr(n, m, fi, ps, rs, c),
    Pc.at(n, m, ps, fi, p, c, h1, N.le_rw_r(1n+U32.to_nat(p), U32.to_nat(nx), Nat.add(U32.to_nat(fi), n), Equal.sym(Nat, Nat.add(U32.to_nat(fi), n), U32.to_nat(nx), es), hl)),
    N.le_add_r(PM.Pc(n, m, ps, fi, c), PM.RcL(rs, c)))

# The table
# ---------

# the mask of a term's tag: the fields of its parts (1 for field 2, 2 for 3,
# 4 for 4), as I.table holds it
def Mask(t: Bk.Term) -> U32:
  match t:
    case Bk.Term.Var{_}:
      0
    case Bk.Term.Ref{_}:
      0
    case Bk.Term.Ann{_, _}:
      3
    case Bk.Term.Let{_, _, _}:
      3
    case Bk.Term.Typ{_}:
      1
    case Bk.Term.Min{_, _}:
      3
    case Bk.Term.All{_, _, _}:
      3
    case Bk.Term.Lam{_, _}:
      1
    case Bk.Term.App{_, _, _}:
      3
    case Bk.Term.Sig{_, _, _}:
      3
    case Bk.Term.Tup{_, _, _}:
      3
    case Bk.Term.Prj{_}:
      1
    case Bk.Term.Enu{_}:
      0
    case Bk.Term.Lab{_}:
      0
    case Bk.Term.Mat{_, _, _}:
      6
    case Bk.Term.Efq{}:
      0
    case Bk.Term.Eql{_, _, _}:
      7
    case Bk.Term.Rfl{}:
      0
    case Bk.Term.Rwt{_, _, _}:
      7

# the table's mask for the tag of t (Tbl)
def tbl.mask(-m: Cr.Cir.Cells, -im: U32, -fi: U32, -nx: U32, t: Bk.Term, h: PM.Tbl(m, im, fi, nx)) ->
  {PM.Fd(2n, m, U32.add(272, PM.A.tag(t))) == Mask(t) : U32}:
  match t:
    case Bk.Term.Var{_}:
      match h:
        case Tuple{_, Tuple{e, _}}:
          PM.tbl.fd(2n, m, 272, Cr.Cir.Cell{0, 0, 0, 0, 0}, e)
    case Bk.Term.Ref{_}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}:
          PM.tbl.fd(2n, m, 273, Cr.Cir.Cell{0, 0, 0, 0, 0}, e)
    case Bk.Term.Ann{_, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}:
          PM.tbl.fd(2n, m, 274, Cr.Cir.Cell{0, 0, 3, 0, 0}, e)
    case Bk.Term.Let{_, _, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}:
          PM.tbl.fd(2n, m, 275, Cr.Cir.Cell{0, 0, 3, 4, 0}, e)
    case Bk.Term.Typ{_}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}:
          PM.tbl.fd(2n, m, 276, Cr.Cir.Cell{0, 0, 1, 0, 1}, e)
    case Bk.Term.Min{_, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}:
          PM.tbl.fd(2n, m, 277, Cr.Cir.Cell{0, 0, 3, 0, 0}, e)
    case Bk.Term.All{_, _, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}:
          PM.tbl.fd(2n, m, 278, Cr.Cir.Cell{0, 0, 3, 4, 1}, e)
    case Bk.Term.Lam{_, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}:
          PM.tbl.fd(2n, m, 279, Cr.Cir.Cell{0, 0, 1, 1, 1}, e)
    case Bk.Term.App{_, _, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}:
          PM.tbl.fd(2n, m, 280, Cr.Cir.Cell{0, 0, 3, 0, 0}, e)
    case Bk.Term.Sig{_, _, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}:
          PM.tbl.fd(2n, m, 281, Cr.Cir.Cell{0, 0, 3, 4, 1}, e)
    case Bk.Term.Tup{_, _, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}:
          PM.tbl.fd(2n, m, 282, Cr.Cir.Cell{0, 0, 3, 0, 0}, e)
    case Bk.Term.Prj{_}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}:
          PM.tbl.fd(2n, m, 283, Cr.Cir.Cell{0, 0, 1, 0, 1}, e)
    case Bk.Term.Enu{_}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}:
          PM.tbl.fd(2n, m, 284, Cr.Cir.Cell{0, 0, 0, 0, 1}, e)
    case Bk.Term.Lab{_}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          PM.tbl.fd(2n, m, 285, Cr.Cir.Cell{0, 0, 0, 0, 1}, e)
    case Bk.Term.Mat{_, _, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          PM.tbl.fd(2n, m, 286, Cr.Cir.Cell{0, 0, 6, 0, 1}, e)
    case Bk.Term.Efq{}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          PM.tbl.fd(2n, m, 287, Cr.Cir.Cell{0, 0, 0, 0, 1}, e)
    case Bk.Term.Eql{_, _, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          PM.tbl.fd(2n, m, 288, Cr.Cir.Cell{0, 0, 7, 0, 1}, e)
    case Bk.Term.Rfl{}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          PM.tbl.fd(2n, m, 289, Cr.Cir.Cell{0, 0, 0, 0, 1}, e)
    case Bk.Term.Rwt{_, _, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
          PM.tbl.fd(2n, m, 290, Cr.Cir.Cell{0, 0, 7, 8, 0}, e)

# The parts of a node
# -------------------

# Fs, with the test of the tag b and the tag tg apart
def FsP(b: Bool, +m: Cr.Cir.Cells, +ps: List<&2, U32>, +o: U32, +tg: U32) -> List<&2, U32>:
  Bool.pick(List<&2, U32>, b, PM.Fs.term(PM.Fd(2n, m, U32.add(272, tg)), PM.Fd(2n, m, o), PM.Fd(3n, m, o), PM.Fd(4n, m, o)),
    Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_le(32, tg), U32.is_le(tg, 40)), Bool.not(PM.Mem(ps, o))),
      Con{PM.Fd(2n, m, o), PM.Fs.opt(U32.is_eq(tg, 38), PM.Fd(3n, m, o), Nil{})},
      Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_eq(tg, 41), PM.FlW(PM.Fd(0n, m, o), 4096)), Bool.not(PM.Mem(ps, o))),
        [PM.Fd(2n, m, o)], Nil{})))

# the pointers of a term cell of the tag tg, whose mask is mask, are its parts
# by the mask
def fs.term(+m: Cr.Cir.Cells, +ps: List<&2, U32>, +o: U32, +tg: U32, +mask: U32, etag: {PM.TgW(PM.Fd(0n, m, o)) == tg : U32},
  hlt: {U32.is_lt(tg, 19) == True{} : Bool}, emask: {PM.Fd(2n, m, U32.add(272, tg)) == mask : U32}) ->
  {PM.Fs(m, ps, o) == PM.Fs.term(mask, PM.Fd(2n, m, o), PM.Fd(3n, m, o), PM.Fd(4n, m, o)) : List<&2, U32>}:
  %Equal.sym(U32, PM.TgW(PM.Fd(0n, m, o)), tg, etag) :
    {FsP(U32.is_lt(_, 19), m, ps, o, _) == PM.Fs.term(mask, PM.Fd(2n, m, o), PM.Fd(3n, m, o), PM.Fd(4n, m, o)) : List<&2, U32>}
  %Equal.sym(Bool, U32.is_lt(tg, 19), True{}, hlt) :
    {FsP(_, m, ps, o, tg) == PM.Fs.term(mask, PM.Fd(2n, m, o), PM.Fd(3n, m, o), PM.Fd(4n, m, o)) : List<&2, U32>}
  %Equal.sym(U32, PM.Fd(2n, m, U32.add(272, tg)), mask, emask) :
    {PM.Fs.term(_, PM.Fd(2n, m, o), PM.Fd(3n, m, o), PM.Fd(4n, m, o)) == PM.Fs.term(mask, PM.Fd(2n, m, o), PM.Fd(3n, m, o), PM.Fd(4n, m, o)) : List<&2, U32>}
  {==}

# a part y, by the mask, of a term cell c of the machine's own has a pointer
def ptr.part(+m: Cr.Cir.Cells, +nx: U32, +fi: U32, +ps: List<&2, U32>, +rs: List<&2, U32>, +c: U32, +y: U32, +tg: U32, +mask: U32,
  etag: {PM.TgW(PM.Fd(0n, m, c)) == tg : U32}, hlt: {U32.is_lt(tg, 19) == True{} : Bool},
  emask: {PM.Fd(2n, m, U32.add(272, tg)) == mask : U32}, own: {PM.Own(fi, nx, c) == True{} : Bool},
  hm: {PM.Mem(PM.Fs.term(mask, PM.Fd(2n, m, c), PM.Fd(3n, m, c), PM.Fd(4n, m, c)), y) == True{} : Bool}) ->
  N.Le(1n, PM.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, rs, y)):
  +e = fs.term(m, ps, c, tg, mask, etag, hlt, emask)
  N.le_trans(1n, PM.RcL(PM.Fs(m, ps, c), y), PM.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, rs, y),
    (%Equal.sym(List<&2, U32>, PM.Fs(m, ps, c), PM.Fs.term(mask, PM.Fd(2n, m, c), PM.Fd(3n, m, c), PM.Fd(4n, m, c)), e) : N.Le(1n, PM.RcL(_, y));
      rcl.mem(PM.Fs.term(mask, PM.Fd(2n, m, c), PM.Fd(3n, m, c), PM.Fd(4n, m, c)), y, hm)),
    Ptr.at(m, nx, fi, ps, rs, c, y, own))

# a cell with a pointer is not one with none
def ne.ptr(b: Bool, +y: U32, +z: U32, +n: Nat, +m: Cr.Cir.Cells, +fi: U32, +ps: List<&2, U32>, +rs: List<&2, U32>,
  eb: {U32.is_eq(y, z) == b : Bool}, hy: N.Le(1n, PM.Ptr(n, m, fi, ps, rs, y)), hz: {PM.Ptr(n, m, fi, ps, rs, z) == 0n : Nat}) ->
  {U32.is_eq(y, z) == False{} : Bool}:
  match b:
    case False{}:
      eb
    case True{}:
      +e = PM.u32.eq(y, z, eb)
      Empty.absurd({U32.is_eq(y, z) == False{} : Bool},
        N.le_rw_r(1n, PM.Ptr(n, m, fi, ps, rs, z), 0n, hz,
          N.le_rw_r(1n, PM.Ptr(n, m, fi, ps, rs, y), PM.Ptr(n, m, fi, ps, rs, z), Equal.cong(U32, Nat, w => PM.Ptr(n, m, fi, ps, rs, w), y, z, e), hy)))

# a STATIC cell is not one that is not STATIC
def ne.st(b: Bool, +m: Cr.Cir.Cells, +y: U32, +z: U32, eb: {U32.is_eq(y, z) == b : Bool},
  hy: {PM.Fl(m, y, 1024) == True{} : Bool}, hz: {PM.Fl(m, z, 1024) == False{} : Bool}) -> {U32.is_eq(y, z) == False{} : Bool}:
  match b:
    case False{}:
      eb
    case True{}:
      +e = PM.u32.eq(y, z, eb)
      PM.bool.ft({U32.is_eq(y, z) == False{} : Bool}, Equal.trans(Bool, False{}, PM.Fl(m, z, 1024), True{}, Equal.sym(Bool, PM.Fl(m, z, 1024), False{}, hz),
        (%e : {PM.Fl(m, _, 1024) == True{} : Bool}; hy)))

def part.ne.b(o: Bool, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +ps: List<&2, U32>, +rs: List<&2, U32>, +c: U32, +y: U32, +z: U32,
  +tg: U32, +mask: U32, eo: {PM.Own(fi, nx, c) == o : Bool},
  sp: {Bool.or(o, PM.FlW(Cr.Cir.Cell.get(0n, Cr.Cir.Cells.get(m, y)), 1024)) == True{} : Bool},
  etag: {PM.TgW(PM.Fd(0n, m, c)) == tg : U32}, hlt: {U32.is_lt(tg, 19) == True{} : Bool},
  emask: {PM.Fd(2n, m, U32.add(272, tg)) == mask : U32},
  hm: {PM.Mem(PM.Fs.term(mask, PM.Fd(2n, m, c), PM.Fd(3n, m, c), PM.Fd(4n, m, c)), y) == True{} : Bool},
  hz0: {PM.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, rs, z) == 0n : Nat},
  hzs: {PM.Fl(m, z, 1024) == False{} : Bool}) -> {U32.is_eq(y, z) == False{} : Bool}:
  match o:
    case True{}:
      ne.ptr(U32.is_eq(y, z), y, z, Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, rs, {==},
        ptr.part(m, nx, fi, ps, rs, c, y, tg, mask, etag, hlt, emask, eo, hm), hz0)
    case False{}:
      ne.st(U32.is_eq(y, z), m, y, z, {==}, sp, hzs)

# a part y of a node c (by the mask of c's tag tg) is not the cell z, which
# nothing points to and is not STATIC
def part.ne(+m: Cr.Cir.Cells, +nx: U32, +fi: U32, +ps: List<&2, U32>, +rs: List<&2, U32>, +c: U32, +y: U32, +z: U32,
  +tg: U32, +mask: U32, sp: PM.Sp(fi, nx, c, Cr.Cir.Cells.get(m, y)),
  etag: {PM.TgW(PM.Fd(0n, m, c)) == tg : U32}, hlt: {U32.is_lt(tg, 19) == True{} : Bool},
  emask: {PM.Fd(2n, m, U32.add(272, tg)) == mask : U32},
  hm: {PM.Mem(PM.Fs.term(mask, PM.Fd(2n, m, c), PM.Fd(3n, m, c), PM.Fd(4n, m, c)), y) == True{} : Bool},
  hz0: {PM.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, rs, z) == 0n : Nat},
  hzs: {PM.Fl(m, z, 1024) == False{} : Bool}) -> {U32.is_eq(y, z) == False{} : Bool}:
  part.ne.b(PM.Own(fi, nx, c), m, nx, fi, ps, rs, c, y, z, tg, mask, {==}, sp, etag, hlt, emask, hm, hz0, hzs)

# the tag that a node says
def nd.tg(-ds: List<&2, Bk.Def>, -im: U32, -fi: U32, -nx: U32, -c: U32, -x: Cr.Cir.Cell, -t: Bk.Term, -tag: U32,
  h: PM.Nd(ds, im, fi, nx, c, x, t, tag)) -> {PM.TgW(Cr.Cir.Cell.get(0n, x)) == tag : U32}:
  (e0, r0) = h
  (e1, r1) = r0
  (e, r) = r1
  e

# a part of a node, after a store to the cell z, which nothing points to and
# is not STATIC: the part is not z, so the store keeps it (rec)
def part.fz(ty: Bk.Term, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +rs: List<&2, U32>, +z: U32, +x: Cr.Cir.Cell, +c: U32, +y: U32, +tg: U32, +mask: U32,
  hz0: {PM.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, rs, z) == 0n : Nat}, hzs: {PM.Fl(m, z, 1024) == False{} : Bool},
  etag: {PM.TgW(PM.Fd(0n, m, c)) == tg : U32}, hlt: {U32.is_lt(tg, 19) == True{} : Bool},
  emask: {PM.Fd(2n, m, U32.add(272, tg)) == mask : U32},
  hm: {PM.Mem(PM.Fs.term(mask, PM.Fd(2n, m, c), PM.Fd(3n, m, c), PM.Fd(4n, m, c)), y) == True{} : Bool},
  rec: {U32.is_eq(y, z) == False{} : Bool} -> PM.Is(ds, m, im, fi, nx, ks, img, y, ty) -> PM.Is(ds, Cr.Cir.Cells.set(m, z, x), im, fi, nx, ks, img, y, ty),
  hp: PM.P2(PM.Sp(fi, nx, c, Cr.Cir.Cells.get(m, y)), PM.IsC(ds, m, im, fi, nx, ks, img, y, Cr.Cir.Cells.get(m, y), ty))) ->
  PM.P2(PM.Sp(fi, nx, c, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, x), y)),
    PM.IsC(ds, Cr.Cir.Cells.set(m, z, x), im, fi, nx, ks, img, y, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, x), y), ty)):
  (+sp, hy) = hp
  +ne = part.ne(m, nx, fi, ps, rs, c, y, z, tg, mask, sp, etag, hlt, emask, hm, hz0, hzs)
  (PM.sp.at(fi, nx, c, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, x), y), Cr.Cir.Cells.get(m, y), PM.cl.go(m, y, z, x, ne), sp), rec(ne, hy))

# a store to the cell z, which nothing points to (Ptr 0) and is not STATIC,
# keeps the term of every cell c but z
def is.fz(t: Bk.Term, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +rs: List<&2, U32>, +z: U32, +x: Cr.Cir.Cell, +c: U32, +tbl: PM.Tbl(m, im, fi, nx),
  +hz0: {PM.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, rs, z) == 0n : Nat}, +hzs: {PM.Fl(m, z, 1024) == False{} : Bool},
  hc: {U32.is_eq(c, z) == False{} : Bool}, h: PM.Is(ds, m, im, fi, nx, ks, img, c, t)) ->
  PM.Is(ds, Cr.Cir.Cells.set(m, z, x), im, fi, nx, ks, img, c, t):
  match t:
    case Bk.Term.Var{+i}:
      PM.isc.at(ds, Cr.Cir.Cells.set(m, z, x), im, fi, nx, ks, img, c, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, x), c), Cr.Cir.Cells.get(m, c), Bk.Term.Var{i}, PM.cl.go(m, c, z, x, hc),
            h)
    case Bk.Term.Ref{+k}:
      PM.isc.at(ds, Cr.Cir.Cells.set(m, z, x), im, fi, nx, ks, img, c, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, x), c), Cr.Cir.Cells.get(m, c), Bk.Term.Ref{k}, PM.cl.go(m, c, z, x, hc),
            h)
    case Bk.Term.Enu{+e}:
      PM.isc.at(ds, Cr.Cir.Cells.set(m, z, x), im, fi, nx, ks, img, c, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, x), c), Cr.Cir.Cells.get(m, c), Bk.Term.Enu{e}, PM.cl.go(m, c, z, x, hc),
            h)
    case Bk.Term.Lab{+k}:
      PM.isc.at(ds, Cr.Cir.Cells.set(m, z, x), im, fi, nx, ks, img, c, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, x), c), Cr.Cir.Cells.get(m, c), Bk.Term.Lab{k}, PM.cl.go(m, c, z, x, hc),
            h)
    case Bk.Term.Efq{}:
      PM.isc.at(ds, Cr.Cir.Cells.set(m, z, x), im, fi, nx, ks, img, c, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, x), c), Cr.Cir.Cells.get(m, c), Bk.Term.Efq{}, PM.cl.go(m, c, z, x, hc),
            h)
    case Bk.Term.Rfl{}:
      PM.isc.at(ds, Cr.Cir.Cells.set(m, z, x), im, fi, nx, ks, img, c, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, x), c), Cr.Cir.Cells.get(m, c), Bk.Term.Rfl{}, PM.cl.go(m, c, z, x, hc),
            h)
    case Bk.Term.Ann{+a, +b}:
      (+nd, r) = h
      (pa, pb) = r
      PM.isc.at(ds, Cr.Cir.Cells.set(m, z, x), im, fi, nx, ks, img, c, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, x), c), Cr.Cir.Cells.get(m, c), Bk.Term.Ann{a, b}, PM.cl.go(m, c, z, x, hc),
            (nd, (part.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, c, PM.Fd(2n, m, c), 2, 3, hz0, hzs,
              nd.tg(ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Ann{a, b}, 2, nd), {==}, tbl.mask(m, im, fi, nx, Bk.Term.Ann{a, b}, tbl), mem.hd(PM.Fd(2n, m, c), Con{PM.Fd(3n, m, c), Nil{}}),
              e => hh => is.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(2n, m, c), tbl, hz0, hzs, e, hh), pa),
              part.fz(b, ds, m, im, fi, nx, ks, img, ps, rs, z, x, c, PM.Fd(3n, m, c), 2, 3, hz0, hzs,
              nd.tg(ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Ann{a, b}, 2, nd), {==}, tbl.mask(m, im, fi, nx, Bk.Term.Ann{a, b}, tbl), mem.tl(PM.Fd(2n, m, c), PM.Fd(3n, m, c), Con{PM.Fd(3n, m, c), Nil{}}, mem.hd(PM.Fd(3n, m, c), Nil{})),
              e => hh => is.fz(b, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(3n, m, c), tbl, hz0, hzs, e, hh), pb))))
    case Bk.Term.Min{+a, +b}:
      (+nd, r) = h
      (pa, pb) = r
      PM.isc.at(ds, Cr.Cir.Cells.set(m, z, x), im, fi, nx, ks, img, c, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, x), c), Cr.Cir.Cells.get(m, c), Bk.Term.Min{a, b}, PM.cl.go(m, c, z, x, hc),
            (nd, (part.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, c, PM.Fd(2n, m, c), 5, 3, hz0, hzs,
              nd.tg(ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Min{a, b}, 5, nd), {==}, tbl.mask(m, im, fi, nx, Bk.Term.Min{a, b}, tbl), mem.hd(PM.Fd(2n, m, c), Con{PM.Fd(3n, m, c), Nil{}}),
              e => hh => is.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(2n, m, c), tbl, hz0, hzs, e, hh), pa),
              part.fz(b, ds, m, im, fi, nx, ks, img, ps, rs, z, x, c, PM.Fd(3n, m, c), 5, 3, hz0, hzs,
              nd.tg(ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Min{a, b}, 5, nd), {==}, tbl.mask(m, im, fi, nx, Bk.Term.Min{a, b}, tbl), mem.tl(PM.Fd(2n, m, c), PM.Fd(3n, m, c), Con{PM.Fd(3n, m, c), Nil{}}, mem.hd(PM.Fd(3n, m, c), Nil{})),
              e => hh => is.fz(b, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(3n, m, c), tbl, hz0, hzs, e, hh), pb))))
    case Bk.Term.Let{+q, +a, +b}:
      (+nd, r) = h
      (qs, r2) = r
      (pa, pb) = r2
      PM.isc.at(ds, Cr.Cir.Cells.set(m, z, x), im, fi, nx, ks, img, c, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, x), c), Cr.Cir.Cells.get(m, c), Bk.Term.Let{q, a, b}, PM.cl.go(m, c, z, x, hc),
            (nd, (qs, (part.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, c, PM.Fd(2n, m, c), 3, 3, hz0, hzs,
              nd.tg(ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Let{q, a, b}, 3, nd), {==}, tbl.mask(m, im, fi, nx, Bk.Term.Let{q, a, b}, tbl), mem.hd(PM.Fd(2n, m, c), Con{PM.Fd(3n, m, c), Nil{}}),
              e => hh => is.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(2n, m, c), tbl, hz0, hzs, e, hh), pa),
              part.fz(b, ds, m, im, fi, nx, ks, img, ps, rs, z, x, c, PM.Fd(3n, m, c), 3, 3, hz0, hzs,
              nd.tg(ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Let{q, a, b}, 3, nd), {==}, tbl.mask(m, im, fi, nx, Bk.Term.Let{q, a, b}, tbl), mem.tl(PM.Fd(2n, m, c), PM.Fd(3n, m, c), Con{PM.Fd(3n, m, c), Nil{}}, mem.hd(PM.Fd(3n, m, c), Nil{})),
              e => hh => is.fz(b, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(3n, m, c), tbl, hz0, hzs, e, hh), pb)))))
    case Bk.Term.All{+q, +a, +b}:
      (+nd, r) = h
      (qs, r2) = r
      (pa, pb) = r2
      PM.isc.at(ds, Cr.Cir.Cells.set(m, z, x), im, fi, nx, ks, img, c, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, x), c), Cr.Cir.Cells.get(m, c), Bk.Term.All{q, a, b}, PM.cl.go(m, c, z, x, hc),
            (nd, (qs, (part.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, c, PM.Fd(2n, m, c), 6, 3, hz0, hzs,
              nd.tg(ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.All{q, a, b}, 6, nd), {==}, tbl.mask(m, im, fi, nx, Bk.Term.All{q, a, b}, tbl), mem.hd(PM.Fd(2n, m, c), Con{PM.Fd(3n, m, c), Nil{}}),
              e => hh => is.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(2n, m, c), tbl, hz0, hzs, e, hh), pa),
              part.fz(b, ds, m, im, fi, nx, ks, img, ps, rs, z, x, c, PM.Fd(3n, m, c), 6, 3, hz0, hzs,
              nd.tg(ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.All{q, a, b}, 6, nd), {==}, tbl.mask(m, im, fi, nx, Bk.Term.All{q, a, b}, tbl), mem.tl(PM.Fd(2n, m, c), PM.Fd(3n, m, c), Con{PM.Fd(3n, m, c), Nil{}}, mem.hd(PM.Fd(3n, m, c), Nil{})),
              e => hh => is.fz(b, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(3n, m, c), tbl, hz0, hzs, e, hh), pb)))))
    case Bk.Term.App{+q, +a, +b}:
      (+nd, r) = h
      (qs, r2) = r
      (pa, pb) = r2
      PM.isc.at(ds, Cr.Cir.Cells.set(m, z, x), im, fi, nx, ks, img, c, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, x), c), Cr.Cir.Cells.get(m, c), Bk.Term.App{q, a, b}, PM.cl.go(m, c, z, x, hc),
            (nd, (qs, (part.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, c, PM.Fd(2n, m, c), 8, 3, hz0, hzs,
              nd.tg(ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.App{q, a, b}, 8, nd), {==}, tbl.mask(m, im, fi, nx, Bk.Term.App{q, a, b}, tbl), mem.hd(PM.Fd(2n, m, c), Con{PM.Fd(3n, m, c), Nil{}}),
              e => hh => is.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(2n, m, c), tbl, hz0, hzs, e, hh), pa),
              part.fz(b, ds, m, im, fi, nx, ks, img, ps, rs, z, x, c, PM.Fd(3n, m, c), 8, 3, hz0, hzs,
              nd.tg(ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.App{q, a, b}, 8, nd), {==}, tbl.mask(m, im, fi, nx, Bk.Term.App{q, a, b}, tbl), mem.tl(PM.Fd(2n, m, c), PM.Fd(3n, m, c), Con{PM.Fd(3n, m, c), Nil{}}, mem.hd(PM.Fd(3n, m, c), Nil{})),
              e => hh => is.fz(b, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(3n, m, c), tbl, hz0, hzs, e, hh), pb)))))
    case Bk.Term.Sig{+q, +a, +b}:
      (+nd, r) = h
      (qs, r2) = r
      (pa, pb) = r2
      PM.isc.at(ds, Cr.Cir.Cells.set(m, z, x), im, fi, nx, ks, img, c, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, x), c), Cr.Cir.Cells.get(m, c), Bk.Term.Sig{q, a, b}, PM.cl.go(m, c, z, x, hc),
            (nd, (qs, (part.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, c, PM.Fd(2n, m, c), 9, 3, hz0, hzs,
              nd.tg(ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Sig{q, a, b}, 9, nd), {==}, tbl.mask(m, im, fi, nx, Bk.Term.Sig{q, a, b}, tbl), mem.hd(PM.Fd(2n, m, c), Con{PM.Fd(3n, m, c), Nil{}}),
              e => hh => is.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(2n, m, c), tbl, hz0, hzs, e, hh), pa),
              part.fz(b, ds, m, im, fi, nx, ks, img, ps, rs, z, x, c, PM.Fd(3n, m, c), 9, 3, hz0, hzs,
              nd.tg(ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Sig{q, a, b}, 9, nd), {==}, tbl.mask(m, im, fi, nx, Bk.Term.Sig{q, a, b}, tbl), mem.tl(PM.Fd(2n, m, c), PM.Fd(3n, m, c), Con{PM.Fd(3n, m, c), Nil{}}, mem.hd(PM.Fd(3n, m, c), Nil{})),
              e => hh => is.fz(b, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(3n, m, c), tbl, hz0, hzs, e, hh), pb)))))
    case Bk.Term.Tup{+q, +a, +b}:
      (+nd, r) = h
      (qs, r2) = r
      (pa, pb) = r2
      PM.isc.at(ds, Cr.Cir.Cells.set(m, z, x), im, fi, nx, ks, img, c, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, x), c), Cr.Cir.Cells.get(m, c), Bk.Term.Tup{q, a, b}, PM.cl.go(m, c, z, x, hc),
            (nd, (qs, (part.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, c, PM.Fd(2n, m, c), 10, 3, hz0, hzs,
              nd.tg(ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Tup{q, a, b}, 10, nd), {==}, tbl.mask(m, im, fi, nx, Bk.Term.Tup{q, a, b}, tbl), mem.hd(PM.Fd(2n, m, c), Con{PM.Fd(3n, m, c), Nil{}}),
              e => hh => is.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(2n, m, c), tbl, hz0, hzs, e, hh), pa),
              part.fz(b, ds, m, im, fi, nx, ks, img, ps, rs, z, x, c, PM.Fd(3n, m, c), 10, 3, hz0, hzs,
              nd.tg(ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Tup{q, a, b}, 10, nd), {==}, tbl.mask(m, im, fi, nx, Bk.Term.Tup{q, a, b}, tbl), mem.tl(PM.Fd(2n, m, c), PM.Fd(3n, m, c), Con{PM.Fd(3n, m, c), Nil{}}, mem.hd(PM.Fd(3n, m, c), Nil{})),
              e => hh => is.fz(b, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(3n, m, c), tbl, hz0, hzs, e, hh), pb)))))
    case Bk.Term.Typ{+a}:
      (+nd, pa) = h
      PM.isc.at(ds, Cr.Cir.Cells.set(m, z, x), im, fi, nx, ks, img, c, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, x), c), Cr.Cir.Cells.get(m, c), Bk.Term.Typ{a}, PM.cl.go(m, c, z, x, hc),
            (nd, part.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, c, PM.Fd(2n, m, c), 4, 1, hz0, hzs,
              nd.tg(ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Typ{a}, 4, nd), {==}, tbl.mask(m, im, fi, nx, Bk.Term.Typ{a}, tbl), mem.hd(PM.Fd(2n, m, c), Nil{}),
              e => hh => is.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(2n, m, c), tbl, hz0, hzs, e, hh), pa)))
    case Bk.Term.Prj{+a}:
      (+nd, pa) = h
      PM.isc.at(ds, Cr.Cir.Cells.set(m, z, x), im, fi, nx, ks, img, c, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, x), c), Cr.Cir.Cells.get(m, c), Bk.Term.Prj{a}, PM.cl.go(m, c, z, x, hc),
            (nd, part.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, c, PM.Fd(2n, m, c), 11, 1, hz0, hzs,
              nd.tg(ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Prj{a}, 11, nd), {==}, tbl.mask(m, im, fi, nx, Bk.Term.Prj{a}, tbl), mem.hd(PM.Fd(2n, m, c), Nil{}),
              e => hh => is.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(2n, m, c), tbl, hz0, hzs, e, hh), pa)))
    case Bk.Term.Lam{+q, +a}:
      (+nd, r) = h
      (qs, pa) = r
      PM.isc.at(ds, Cr.Cir.Cells.set(m, z, x), im, fi, nx, ks, img, c, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, x), c), Cr.Cir.Cells.get(m, c), Bk.Term.Lam{q, a}, PM.cl.go(m, c, z, x, hc),
            (nd, (qs, part.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, c, PM.Fd(2n, m, c), 7, 1, hz0, hzs,
              nd.tg(ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Lam{q, a}, 7, nd), {==}, tbl.mask(m, im, fi, nx, Bk.Term.Lam{q, a}, tbl), mem.hd(PM.Fd(2n, m, c), Nil{}),
              e => hh => is.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(2n, m, c), tbl, hz0, hzs, e, hh), pa))))
    case Bk.Term.Mat{+k, +a, +b}:
      (+nd, r) = h
      (nm, r2) = r
      (pa, pb) = r2
      PM.isc.at(ds, Cr.Cir.Cells.set(m, z, x), im, fi, nx, ks, img, c, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, x), c), Cr.Cir.Cells.get(m, c), Bk.Term.Mat{k, a, b}, PM.cl.go(m, c, z, x, hc),
            (nd, (nm, (part.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, c, PM.Fd(3n, m, c), 14, 6, hz0, hzs,
              nd.tg(ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Mat{k, a, b}, 14, nd), {==}, tbl.mask(m, im, fi, nx, Bk.Term.Mat{k, a, b}, tbl), mem.hd(PM.Fd(3n, m, c), Con{PM.Fd(4n, m, c), Nil{}}),
              e => hh => is.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(3n, m, c), tbl, hz0, hzs, e, hh), pa),
              part.fz(b, ds, m, im, fi, nx, ks, img, ps, rs, z, x, c, PM.Fd(4n, m, c), 14, 6, hz0, hzs,
              nd.tg(ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Mat{k, a, b}, 14, nd), {==}, tbl.mask(m, im, fi, nx, Bk.Term.Mat{k, a, b}, tbl), mem.tl(PM.Fd(3n, m, c), PM.Fd(4n, m, c), Con{PM.Fd(4n, m, c), Nil{}}, mem.hd(PM.Fd(4n, m, c), Nil{})),
              e => hh => is.fz(b, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(4n, m, c), tbl, hz0, hzs, e, hh), pb)))))
    case Bk.Term.Eql{+a, +b, +d}:
      (+nd, r) = h
      (pa, r2) = r
      (pb, pd) = r2
      PM.isc.at(ds, Cr.Cir.Cells.set(m, z, x), im, fi, nx, ks, img, c, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, x), c), Cr.Cir.Cells.get(m, c), Bk.Term.Eql{a, b, d}, PM.cl.go(m, c, z, x, hc),
            (nd, (part.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, c, PM.Fd(2n, m, c), 16, 7, hz0, hzs,
              nd.tg(ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Eql{a, b, d}, 16, nd), {==}, tbl.mask(m, im, fi, nx, Bk.Term.Eql{a, b, d}, tbl), mem.hd(PM.Fd(2n, m, c), Con{PM.Fd(3n, m, c), Con{PM.Fd(4n, m, c), Nil{}}}),
              e => hh => is.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(2n, m, c), tbl, hz0, hzs, e, hh), pa),
              (part.fz(b, ds, m, im, fi, nx, ks, img, ps, rs, z, x, c, PM.Fd(3n, m, c), 16, 7, hz0, hzs,
              nd.tg(ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Eql{a, b, d}, 16, nd), {==}, tbl.mask(m, im, fi, nx, Bk.Term.Eql{a, b, d}, tbl), mem.tl(PM.Fd(2n, m, c), PM.Fd(3n, m, c), Con{PM.Fd(3n, m, c), Con{PM.Fd(4n, m, c), Nil{}}}, mem.hd(PM.Fd(3n, m, c), Con{PM.Fd(4n, m, c), Nil{}})),
              e => hh => is.fz(b, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(3n, m, c), tbl, hz0, hzs, e, hh), pb),
              part.fz(d, ds, m, im, fi, nx, ks, img, ps, rs, z, x, c, PM.Fd(4n, m, c), 16, 7, hz0, hzs,
              nd.tg(ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Eql{a, b, d}, 16, nd), {==}, tbl.mask(m, im, fi, nx, Bk.Term.Eql{a, b, d}, tbl), mem.tl(PM.Fd(2n, m, c), PM.Fd(4n, m, c), Con{PM.Fd(3n, m, c), Con{PM.Fd(4n, m, c), Nil{}}}, mem.tl(PM.Fd(3n, m, c), PM.Fd(4n, m, c), Con{PM.Fd(4n, m, c), Nil{}}, mem.hd(PM.Fd(4n, m, c), Nil{}))),
              e => hh => is.fz(d, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(4n, m, c), tbl, hz0, hzs, e, hh), pd)))))
    case Bk.Term.Rwt{+a, +b, +d}:
      (+nd, r) = h
      (pa, r2) = r
      (pb, pd) = r2
      PM.isc.at(ds, Cr.Cir.Cells.set(m, z, x), im, fi, nx, ks, img, c, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, x), c), Cr.Cir.Cells.get(m, c), Bk.Term.Rwt{a, b, d}, PM.cl.go(m, c, z, x, hc),
            (nd, (part.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, c, PM.Fd(2n, m, c), 18, 7, hz0, hzs,
              nd.tg(ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Rwt{a, b, d}, 18, nd), {==}, tbl.mask(m, im, fi, nx, Bk.Term.Rwt{a, b, d}, tbl), mem.hd(PM.Fd(2n, m, c), Con{PM.Fd(3n, m, c), Con{PM.Fd(4n, m, c), Nil{}}}),
              e => hh => is.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(2n, m, c), tbl, hz0, hzs, e, hh), pa),
              (part.fz(b, ds, m, im, fi, nx, ks, img, ps, rs, z, x, c, PM.Fd(3n, m, c), 18, 7, hz0, hzs,
              nd.tg(ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Rwt{a, b, d}, 18, nd), {==}, tbl.mask(m, im, fi, nx, Bk.Term.Rwt{a, b, d}, tbl), mem.tl(PM.Fd(2n, m, c), PM.Fd(3n, m, c), Con{PM.Fd(3n, m, c), Con{PM.Fd(4n, m, c), Nil{}}}, mem.hd(PM.Fd(3n, m, c), Con{PM.Fd(4n, m, c), Nil{}})),
              e => hh => is.fz(b, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(3n, m, c), tbl, hz0, hzs, e, hh), pb),
              part.fz(d, ds, m, im, fi, nx, ks, img, ps, rs, z, x, c, PM.Fd(4n, m, c), 18, 7, hz0, hzs,
              nd.tg(ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), Bk.Term.Rwt{a, b, d}, 18, nd), {==}, tbl.mask(m, im, fi, nx, Bk.Term.Rwt{a, b, d}, tbl), mem.tl(PM.Fd(2n, m, c), PM.Fd(4n, m, c), Con{PM.Fd(3n, m, c), Con{PM.Fd(4n, m, c), Nil{}}}, mem.tl(PM.Fd(3n, m, c), PM.Fd(4n, m, c), Con{PM.Fd(4n, m, c), Nil{}}, mem.hd(PM.Fd(4n, m, c), Nil{}))),
              e => hh => is.fz(d, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(4n, m, c), tbl, hz0, hzs, e, hh), pd)))))


# A store to a cell that nothing points to: the heap
# --------------------------------------------------
#
# Fs of a cell o reads o and the table's cell of o's tag. A store to z keeps
# Fs of every other cell o, when z is not the table's cell that o reads
# (TblR); and Fs of z, when z holds no pointer before or after (Nil). So it
# keeps every count Pc and Ptr, and with them Cnt, Pts, PendOK and Chain.

# the term cell o does not read its mask at z
def TblAt(+m: Cr.Cir.Cells, +o: U32, +z: U32) -> Bool:
  Bool.or(Bool.not(U32.is_lt(PM.Tg(m, o), 19)), Bool.not(U32.is_eq(U32.add(272, PM.Tg(m, o)), z)))

# none of the n cells from o reads its mask at z
def TblR(n: Nat, +m: Cr.Cir.Cells, +o: U32, +z: U32) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+k:
      Bool.and(TblAt(m, o, z), TblR(k, m, U32.inc(o), z))

def not.t(b: Bool, h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      PM.bool.ft({True{} == False{} : Bool}, h)
    case False{}:
      {==}

def tbl.ne(l: Bool, e: Bool, ht: {Bool.or(Bool.not(l), Bool.not(e)) == True{} : Bool}, el: {l == True{} : Bool}) -> {e == False{} : Bool}:
  match l:
    case True{}:
      not.t(e, ht)
    case False{}:
      PM.bool.ft({e == False{} : Bool}, el)

# Fs of the cell o, by its value y, with the mask a
def FsK(b: Bool, +a: U32, +y: Cr.Cir.Cell, +ps: List<&2, U32>, +o: U32) -> List<&2, U32>:
  +tg = PM.TgW(Cr.Cir.Cell.get(0n, y))
  Bool.pick(List<&2, U32>, b, PM.Fs.term(a, Cr.Cir.Cell.get(2n, y), Cr.Cir.Cell.get(3n, y), Cr.Cir.Cell.get(4n, y)),
    Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_le(32, tg), U32.is_le(tg, 40)), Bool.not(PM.Mem(ps, o))),
      Con{Cr.Cir.Cell.get(2n, y), PM.Fs.opt(U32.is_eq(tg, 38), Cr.Cir.Cell.get(3n, y), Nil{})},
      Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_eq(tg, 41), PM.FlW(Cr.Cir.Cell.get(0n, y), 4096)), Bool.not(PM.Mem(ps, o))),
        [Cr.Cir.Cell.get(2n, y)], Nil{})))

def fsk.b(b: Bool, +a1: U32, +a2: U32, +y: Cr.Cir.Cell, +ps: List<&2, U32>, +o: U32, h: {b == True{} : Bool} -> {a1 == a2 : U32}) ->
  {FsK(b, a1, y, ps, o) == FsK(b, a2, y, ps, o) : List<&2, U32>}:
  match b:
    case False{}:
      {==}
    case True{}:
      %h({==}) : {FsK(True{}, a1, y, ps, o) == FsK(True{}, _, y, ps, o) : List<&2, U32>}
      {==}

# a store to z keeps Fs of another cell o, that does not read its mask at z
def fs.eq(+m: Cr.Cir.Cells, +z: U32, +x: Cr.Cir.Cell, +ps: List<&2, U32>, +o: U32, ne: {U32.is_eq(o, z) == False{} : Bool},
  ht: {TblAt(m, o, z) == True{} : Bool}) -> {PM.Fs(Cr.Cir.Cells.set(m, z, x), ps, o) == PM.Fs(m, ps, o) : List<&2, U32>}:
  +M2 = Cr.Cir.Cells.set(m, z, x)
  +Y = Cr.Cir.Cells.get(m, o)
  +tg = PM.TgW(Cr.Cir.Cell.get(0n, Y))
  %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M2, o), Y, PM.cl.go(m, o, z, x, ne)) :
    {FsK(U32.is_lt(PM.TgW(Cr.Cir.Cell.get(0n, _)), 19), PM.Fd(2n, M2, U32.add(272, PM.TgW(Cr.Cir.Cell.get(0n, _)))), _, ps, o) ==
      FsK(U32.is_lt(tg, 19), PM.Fd(2n, m, U32.add(272, tg)), Y, ps, o) : List<&2, U32>}
  fsk.b(U32.is_lt(tg, 19), PM.Fd(2n, M2, U32.add(272, tg)), PM.Fd(2n, m, U32.add(272, tg)), Y, ps, o,
    e => Equal.cong(Cr.Cir.Cell, U32, w => Cr.Cir.Cell.get(2n, w), Cr.Cir.Cells.get(M2, U32.add(272, tg)), Cr.Cir.Cells.get(m, U32.add(272, tg)),
      PM.cl.go(m, U32.add(272, tg), z, x, tbl.ne(U32.is_lt(tg, 19), U32.is_eq(U32.add(272, tg), z), ht, e))))

# a store to z keeps Fs of every cell: of z too, when it holds no pointer
# before or after
def fs.eq2(b: Bool, +m: Cr.Cir.Cells, +z: U32, +x: Cr.Cir.Cell, +ps: List<&2, U32>, +o: U32, eb: {U32.is_eq(o, z) == b : Bool},
  ht: {TblAt(m, o, z) == True{} : Bool}, hf0: {PM.Fs(m, ps, z) == Nil{} : List<&2, U32>},
  hf1: {PM.Fs(Cr.Cir.Cells.set(m, z, x), ps, z) == Nil{} : List<&2, U32>}) ->
  {PM.Fs(Cr.Cir.Cells.set(m, z, x), ps, o) == PM.Fs(m, ps, o) : List<&2, U32>}:
  match b:
    case False{}:
      fs.eq(m, z, x, ps, o, eb, ht)
    case True{}:
      %Equal.sym(U32, o, z, PM.u32.eq(o, z, eb)) : {PM.Fs(Cr.Cir.Cells.set(m, z, x), ps, _) == PM.Fs(m, ps, _) : List<&2, U32>}
      Equal.trans(List<&2, U32>, PM.Fs(Cr.Cir.Cells.set(m, z, x), ps, z), Nil{}, PM.Fs(m, ps, z), hf1, Equal.sym(List<&2, U32>, PM.Fs(m, ps, z), Nil{}, hf0))

def fs.all(+m: Cr.Cir.Cells, +z: U32, +x: Cr.Cir.Cell, +ps: List<&2, U32>, +o: U32,
  ht: {TblAt(m, o, z) == True{} : Bool}, hf0: {PM.Fs(m, ps, z) == Nil{} : List<&2, U32>},
  hf1: {PM.Fs(Cr.Cir.Cells.set(m, z, x), ps, z) == Nil{} : List<&2, U32>}) ->
  {PM.Fs(Cr.Cir.Cells.set(m, z, x), ps, o) == PM.Fs(m, ps, o) : List<&2, U32>}:
  fs.eq2(U32.is_eq(o, z), m, z, x, ps, o, {==}, ht, hf0, hf1)

# a store to z keeps the pointers that the n cells from o hold
def Pc.eq(n: Nat, +m: Cr.Cir.Cells, +z: U32, +x: Cr.Cir.Cell, +ps: List<&2, U32>, +o: U32, +c: U32,
  +hf0: {PM.Fs(m, ps, z) == Nil{} : List<&2, U32>}, +hf1: {PM.Fs(Cr.Cir.Cells.set(m, z, x), ps, z) == Nil{} : List<&2, U32>},
  ht: {TblR(n, m, o, z) == True{} : Bool}) -> {PM.Pc(n, Cr.Cir.Cells.set(m, z, x), ps, o, c) == PM.Pc(n, m, ps, o, c) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+(+k):
      +M2 = Cr.Cir.Cells.set(m, z, x)
      +ht2 = ht
      +e1 = fs.all(m, z, x, ps, o, and.l(TblAt(m, o, z), TblR(k, m, U32.inc(o), z), ht2), hf0, hf1)
      +e2 = Pc.eq(k, m, z, x, ps, U32.inc(o), c, hf0, hf1, and.r(TblAt(m, o, z), TblR(k, m, U32.inc(o), z), ht2))
      %Equal.sym(List<&2, U32>, PM.Fs(M2, ps, o), PM.Fs(m, ps, o), e1) :
        {Nat.add(PM.RcL(_, c), PM.Pc(k, M2, ps, U32.inc(o), c)) == Nat.add(PM.RcL(PM.Fs(m, ps, o), c), PM.Pc(k, m, ps, U32.inc(o), c)) : Nat}
      %Equal.sym(Nat, PM.Pc(k, M2, ps, U32.inc(o), c), PM.Pc(k, m, ps, U32.inc(o), c), e2) :
        {Nat.add(PM.RcL(PM.Fs(m, ps, o), c), _) == Nat.add(PM.RcL(PM.Fs(m, ps, o), c), PM.Pc(k, m, ps, U32.inc(o), c)) : Nat}
      {==}

# and every count
def Ptr.eq(+n: Nat, +m: Cr.Cir.Cells, +z: U32, +x: Cr.Cir.Cell, +fi: U32, +ps: List<&2, U32>, +rs: List<&2, U32>, +c: U32,
  hf0: {PM.Fs(m, ps, z) == Nil{} : List<&2, U32>}, hf1: {PM.Fs(Cr.Cir.Cells.set(m, z, x), ps, z) == Nil{} : List<&2, U32>},
  ht: {TblR(n, m, fi, z) == True{} : Bool}) -> {PM.Ptr(n, Cr.Cir.Cells.set(m, z, x), fi, ps, rs, c) == PM.Ptr(n, m, fi, ps, rs, c) : Nat}:
  Equal.cong(Nat, Nat, w => Nat.add(w, PM.RcL(rs, c)), PM.Pc(n, Cr.Cir.Cells.set(m, z, x), ps, fi, c), PM.Pc(n, m, ps, fi, c),
    Pc.eq(n, m, z, x, ps, fi, c, hf0, hf1, ht))

def and.i(a: Bool, -b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      hb
    case False{}:
      PM.bool.ft({False{} == True{} : Bool}, ha)

def or.l(a: Bool, -b: Bool, h: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      PM.bool.ft({b == True{} : Bool}, h)

def or.f.l(a: Bool, -b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, N.true_ne_false(h))
    case False{}:
      {==}

def or.f.r(a: Bool, -b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({b == False{} : Bool}, N.true_ne_false(h))
    case False{}:
      h

def Disc(n: Nat) -> Type:
  match n:
    case 0n:
      Empty
    case 1n+p:
      Unit

def add0.l(a: Nat, -b: Nat, h: {Nat.add(a, b) == 0n : Nat}) -> {a == 0n : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Empty.absurd({1n+p == 0n : Nat}, (%h : Disc(_); Unit{}))

def add0.r(a: Nat, -b: Nat, h: {Nat.add(a, b) == 0n : Nat}) -> {b == 0n : Nat}:
  match a:
    case 0n:
      h
    case 1n+p:
      Empty.absurd({b == 0n : Nat}, (%h : Disc(_); Unit{}))

# Nat.of(b) + r = 0 gives b false
def of.z(b: Bool, -r: Nat, h: {Nat.add(PM.Nat.of(b), r) == 0n : Nat}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, (%h : Disc(_); Unit{}))
    case False{}:
      {==}

def ge.of(c: Cmp, h: {Cmp.is_lt(c) == False{} : Bool}) -> {Cmp.is_ge(c) == True{} : Bool}:
  match c:
    case LT{}:
      Empty.absurd({False{} == True{} : Bool}, N.true_ne_false(h))
    case EQ{}:
      {==}
    case GT{}:
      {==}

# Cnt at a cell, by its value y and its pointers P
def CntC(+y: Cr.Cir.Cell, +P: Nat, +ps: List<&2, U32>, +o: U32) -> Bool:
  Bool.or(Bool.not(U32.is_lt(PM.TgW(Cr.Cir.Cell.get(0n, y)), 19)), Bool.or(PM.FlW(Cr.Cir.Cell.get(0n, y), 1024), Bool.or(PM.Mem(ps, o),
    Nat.is_eq(U32.to_nat(Cr.Cir.Cell.get(1n, y)), P))))

def cnt.at(b: Bool, +m: Cr.Cir.Cells, +z: U32, +x: Cr.Cir.Cell, +o: U32, +n: Nat, +fi: U32, +ps: List<&2, U32>, +rs: List<&2, U32>,
  eb: {U32.is_eq(o, z) == b : Bool}, hxt: {U32.is_lt(PM.TgW(Cr.Cir.Cell.get(0n, x)), 19) == False{} : Bool},
  hP: {PM.Ptr(n, Cr.Cir.Cells.set(m, z, x), fi, ps, rs, o) == PM.Ptr(n, m, fi, ps, rs, o) : Nat},
  h: {CntC(Cr.Cir.Cells.get(m, o), PM.Ptr(n, m, fi, ps, rs, o), ps, o) == True{} : Bool}) ->
  {CntC(Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, x), o), PM.Ptr(n, Cr.Cir.Cells.set(m, z, x), fi, ps, rs, o), ps, o) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(U32, o, z, PM.u32.eq(o, z, eb)) : {CntC(Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, x), _), PM.Ptr(n, Cr.Cir.Cells.set(m, z, x), fi, ps, rs, _), ps, _) == True{} : Bool}
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, x), z), x, PM.cl.gs(m, z, x)) : {CntC(_, PM.Ptr(n, Cr.Cir.Cells.set(m, z, x), fi, ps, rs, z), ps, z) == True{} : Bool}
      or.l(Bool.not(U32.is_lt(PM.TgW(Cr.Cir.Cell.get(0n, x)), 19)), Bool.or(PM.FlW(Cr.Cir.Cell.get(0n, x), 1024), Bool.or(PM.Mem(ps, z),
        Nat.is_eq(U32.to_nat(Cr.Cir.Cell.get(1n, x)), PM.Ptr(n, Cr.Cir.Cells.set(m, z, x), fi, ps, rs, z)))),
        (%Equal.sym(Bool, U32.is_lt(PM.TgW(Cr.Cir.Cell.get(0n, x)), 19), False{}, hxt) : {Bool.not(_) == True{} : Bool}; {==}))
    case False{}:
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, x), o), Cr.Cir.Cells.get(m, o), PM.cl.go(m, o, z, x, eb)) : {CntC(_, PM.Ptr(n, Cr.Cir.Cells.set(m, z, x), fi, ps, rs, o), ps, o) == True{} : Bool}
      %Equal.sym(Nat, PM.Ptr(n, Cr.Cir.Cells.set(m, z, x), fi, ps, rs, o), PM.Ptr(n, m, fi, ps, rs, o), hP) : {CntC(Cr.Cir.Cells.get(m, o), _, ps, o) == True{} : Bool}
      h

# a store to z, which gets a cell of the machine's own kinds (a tag of 32 or
# more), keeps the counts
def Cnt.fz(k: Nat, +m: Cr.Cir.Cells, +z: U32, +x: Cr.Cir.Cell, +o: U32, +n: Nat, +fi: U32, +ps: List<&2, U32>, +rs: List<&2, U32>,
  +hf0: {PM.Fs(m, ps, z) == Nil{} : List<&2, U32>}, +hf1: {PM.Fs(Cr.Cir.Cells.set(m, z, x), ps, z) == Nil{} : List<&2, U32>},
  +htN: {TblR(n, m, fi, z) == True{} : Bool}, +hxt: {U32.is_lt(PM.TgW(Cr.Cir.Cell.get(0n, x)), 19) == False{} : Bool},
  h: {PM.Cnt(k, m, o, n, fi, ps, rs) == True{} : Bool}) -> {PM.Cnt(k, Cr.Cir.Cells.set(m, z, x), o, n, fi, ps, rs) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+(+j):
      +M2 = Cr.Cir.Cells.set(m, z, x)
      +h2 = h
      and.i(CntC(Cr.Cir.Cells.get(M2, o), PM.Ptr(n, M2, fi, ps, rs, o), ps, o), PM.Cnt(j, M2, U32.inc(o), n, fi, ps, rs),
        cnt.at(U32.is_eq(o, z), m, z, x, o, n, fi, ps, rs, {==}, hxt, Ptr.eq(n, m, z, x, fi, ps, rs, o, hf0, hf1, htN),
          and.l(CntC(Cr.Cir.Cells.get(m, o), PM.Ptr(n, m, fi, ps, rs, o), ps, o), PM.Cnt(j, m, U32.inc(o), n, fi, ps, rs), h2)),
        Cnt.fz(j, m, z, x, U32.inc(o), n, fi, ps, rs, hf0, hf1, htN, hxt,
          and.r(CntC(Cr.Cir.Cells.get(m, o), PM.Ptr(n, m, fi, ps, rs, o), ps, o), PM.Cnt(j, m, U32.inc(o), n, fi, ps, rs), h2)))

# the pend list's cells, none of them z
def PendOK.fz(qs: List<&2, U32>, +ps: List<&2, U32>, +m: Cr.Cir.Cells, +z: U32, +x: Cr.Cir.Cell, +fi: U32, +nx: U32, +rs: List<&2, U32>,
  +hf0: {PM.Fs(m, ps, z) == Nil{} : List<&2, U32>}, +hf1: {PM.Fs(Cr.Cir.Cells.set(m, z, x), ps, z) == Nil{} : List<&2, U32>},
  +htN: {TblR(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, z) == True{} : Bool}, hq: {PM.Mem(qs, z) == False{} : Bool},
  h: PM.PendOK(qs, ps, m, fi, nx, rs)) -> PM.PendOK(qs, ps, Cr.Cir.Cells.set(m, z, x), fi, nx, rs):
  match qs:
    case Nil{}:
      Unit{}
    case Con{+p, +rest}:
      (ho, r1) = h
      (hs, r2) = r1
      (htg, r3) = r2
      (hp0, r4) = r3
      +M2 = Cr.Cir.Cells.set(m, z, x)
      +hq2 = hq
      +ne = or.f.l(U32.is_eq(p, z), PM.Mem(rest, z), hq2)
      +ec = PM.cl.go(m, p, z, x, ne)
      (ho, ((%Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M2, p), Cr.Cir.Cells.get(m, p), ec) :
          {U32.is_ne(U32.and(Cr.Cir.Cell.get(0n, _), 1024), 0) == False{} : Bool}; hs),
        ((%Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M2, p), Cr.Cir.Cells.get(m, p), ec) :
          {Bool.or(U32.is_lt(U32.and(Cr.Cir.Cell.get(0n, _), 63), 19), U32.is_le(32, U32.and(Cr.Cir.Cell.get(0n, _), 63))) == True{} : Bool}; htg),
        ((%Equal.sym(Nat, PM.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), M2, fi, ps, rs, p), PM.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, rs, p),
            Ptr.eq(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, z, x, fi, ps, rs, p, hf0, hf1, htN)) : {_ == 0n : Nat}; hp0),
          PendOK.fz(rest, ps, m, z, x, fi, nx, rs, hf0, hf1, htN, or.f.r(U32.is_eq(p, z), PM.Mem(rest, z), hq2), r4)))))

# the pend list's links, none of them at z
def Chain.fz(qs: List<&2, U32>, +m: Cr.Cir.Cells, +z: U32, +x: Cr.Cir.Cell, +p: U32, hq: {PM.Mem(qs, z) == False{} : Bool},
  h: PM.Chain(qs, m, p)) -> PM.Chain(qs, Cr.Cir.Cells.set(m, z, x), p):
  match qs:
    case Nil{}:
      h
    case Con{+y, +rest}:
      (e1, r1) = h
      (e2, r2) = r1
      +M2 = Cr.Cir.Cells.set(m, z, x)
      +hq2 = hq
      +ne = or.f.l(U32.is_eq(y, z), PM.Mem(rest, z), hq2)
      (e1, (e2, (%Equal.sym(U32, PM.Fd(1n, M2, y), PM.Fd(1n, m, y),
          Equal.cong(Cr.Cir.Cell, U32, w => Cr.Cir.Cell.get(1n, w), Cr.Cir.Cells.get(M2, y), Cr.Cir.Cells.get(m, y), PM.cl.go(m, y, z, x, ne))) :
          PM.Chain(rest, M2, _);
        Chain.fz(rest, m, z, x, PM.Fd(1n, m, y), or.f.r(U32.is_eq(y, z), PM.Mem(rest, z), hq2), r2))))

# The nodes of the held terms
# ---------------------------
#
# A node of a term that Is says, at a cell r that is not z, is not z either
# (node.ne): its parts are STATIC or have a pointer (part.ne). So a store to z
# keeps which cells are nodes (Node.fz), and Held.

def node.or2(e: Bool, a: Bool, -G: Type, h: {Bool.or(e, a) == True{} : Bool}, ke: {e == True{} : Bool} -> G, ka: {a == True{} : Bool} -> G) -> G:
  match e:
    case True{}:
      ke({==})
    case False{}:
      ka(h)

def node.or3(e: Bool, a: Bool, b: Bool, -G: Type, h: {Bool.or(e, Bool.or(a, b)) == True{} : Bool}, ke: {e == True{} : Bool} -> G,
  ka: {a == True{} : Bool} -> G, kb: {b == True{} : Bool} -> G) -> G:
  match e:
    case True{}:
      ke({==})
    case False{}:
      node.or2(a, b, G, h, ka, kb)

def node.or4(e: Bool, a: Bool, b: Bool, d: Bool, -G: Type, h: {Bool.or(e, Bool.or(a, Bool.or(b, d))) == True{} : Bool}, ke: {e == True{} : Bool} -> G,
  ka: {a == True{} : Bool} -> G, kb: {b == True{} : Bool} -> G, kd: {d == True{} : Bool} -> G) -> G:
  match e:
    case True{}:
      ke({==})
    case False{}:
      node.or3(a, b, d, G, h, ka, kb, kd)

# the cell c, equal to r, is not z when r is not
def rew.ne(+r: U32, +c: U32, +z: U32, e: {U32.is_eq(r, c) == True{} : Bool}, hr: {U32.is_eq(r, z) == False{} : Bool}) -> {U32.is_eq(c, z) == False{} : Bool}:
  %PM.u32.eq(r, c, e) : {U32.is_eq(_, z) == False{} : Bool}
  hr

# a node c of the term t at r, a cell that is not z, is not z
def node.ne(t: Bk.Term, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +rs: List<&2, U32>, +z: U32, +r: U32, +c: U32, +tbl: PM.Tbl(m, im, fi, nx),
  +hz0: {PM.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, rs, z) == 0n : Nat}, +hzs: {PM.Fl(m, z, 1024) == False{} : Bool},
  hr: {U32.is_eq(r, z) == False{} : Bool}, h: PM.Is(ds, m, im, fi, nx, ks, img, r, t), hn: {PM.Node(t, m, r, c) == True{} : Bool}) ->
  {U32.is_eq(c, z) == False{} : Bool}:
  match t:
    case Bk.Term.Var{_}:
      rew.ne(r, c, z, hn, hr)
    case Bk.Term.Ref{_}:
      rew.ne(r, c, z, hn, hr)
    case Bk.Term.Enu{_}:
      rew.ne(r, c, z, hn, hr)
    case Bk.Term.Lab{_}:
      rew.ne(r, c, z, hn, hr)
    case Bk.Term.Efq{}:
      rew.ne(r, c, z, hn, hr)
    case Bk.Term.Rfl{}:
      rew.ne(r, c, z, hn, hr)
    case Bk.Term.Ann{+a, +b}:
      (+nd, rr) = h
      (pa, pb) = rr
      (spa, ha) = pa
      (spb, hb) = pb
      node.or3(U32.is_eq(r, c), PM.Node(a, m, PM.Fd(2n, m, r), c), PM.Node(b, m, PM.Fd(3n, m, r), c), {U32.is_eq(c, z) == False{} : Bool}, hn,
        e => rew.ne(r, c, z, e, hr),
        e => node.ne(a, ds, m, im, fi, nx, ks, img, ps, rs, z, PM.Fd(2n, m, r), c, tbl, hz0, hzs,
          part.ne(m, nx, fi, ps, rs, r, PM.Fd(2n, m, r), z, 2, 3, spa, nd.tg(ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Ann{a, b}, 2, nd), {==},
            tbl.mask(m, im, fi, nx, Bk.Term.Ann{a, b}, tbl), mem.hd(PM.Fd(2n, m, r), Con{PM.Fd(3n, m, r), Nil{}}), hz0, hzs), ha, e),
        e => node.ne(b, ds, m, im, fi, nx, ks, img, ps, rs, z, PM.Fd(3n, m, r), c, tbl, hz0, hzs,
          part.ne(m, nx, fi, ps, rs, r, PM.Fd(3n, m, r), z, 2, 3, spb, nd.tg(ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Ann{a, b}, 2, nd), {==},
            tbl.mask(m, im, fi, nx, Bk.Term.Ann{a, b}, tbl), mem.tl(PM.Fd(2n, m, r), PM.Fd(3n, m, r), Con{PM.Fd(3n, m, r), Nil{}}, mem.hd(PM.Fd(3n, m, r), Nil{})), hz0, hzs), hb, e))
    case Bk.Term.Min{+a, +b}:
      (+nd, rr) = h
      (pa, pb) = rr
      (spa, ha) = pa
      (spb, hb) = pb
      node.or3(U32.is_eq(r, c), PM.Node(a, m, PM.Fd(2n, m, r), c), PM.Node(b, m, PM.Fd(3n, m, r), c), {U32.is_eq(c, z) == False{} : Bool}, hn,
        e => rew.ne(r, c, z, e, hr),
        e => node.ne(a, ds, m, im, fi, nx, ks, img, ps, rs, z, PM.Fd(2n, m, r), c, tbl, hz0, hzs,
          part.ne(m, nx, fi, ps, rs, r, PM.Fd(2n, m, r), z, 5, 3, spa, nd.tg(ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Min{a, b}, 5, nd), {==},
            tbl.mask(m, im, fi, nx, Bk.Term.Min{a, b}, tbl), mem.hd(PM.Fd(2n, m, r), Con{PM.Fd(3n, m, r), Nil{}}), hz0, hzs), ha, e),
        e => node.ne(b, ds, m, im, fi, nx, ks, img, ps, rs, z, PM.Fd(3n, m, r), c, tbl, hz0, hzs,
          part.ne(m, nx, fi, ps, rs, r, PM.Fd(3n, m, r), z, 5, 3, spb, nd.tg(ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Min{a, b}, 5, nd), {==},
            tbl.mask(m, im, fi, nx, Bk.Term.Min{a, b}, tbl), mem.tl(PM.Fd(2n, m, r), PM.Fd(3n, m, r), Con{PM.Fd(3n, m, r), Nil{}}, mem.hd(PM.Fd(3n, m, r), Nil{})), hz0, hzs), hb, e))
    case Bk.Term.Let{+q, +a, +b}:
      (+nd, rr) = h
      (qs, r2) = rr
      (pa, pb) = r2
      (spa, ha) = pa
      (spb, hb) = pb
      node.or3(U32.is_eq(r, c), PM.Node(a, m, PM.Fd(2n, m, r), c), PM.Node(b, m, PM.Fd(3n, m, r), c), {U32.is_eq(c, z) == False{} : Bool}, hn,
        e => rew.ne(r, c, z, e, hr),
        e => node.ne(a, ds, m, im, fi, nx, ks, img, ps, rs, z, PM.Fd(2n, m, r), c, tbl, hz0, hzs,
          part.ne(m, nx, fi, ps, rs, r, PM.Fd(2n, m, r), z, 3, 3, spa, nd.tg(ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Let{q, a, b}, 3, nd), {==},
            tbl.mask(m, im, fi, nx, Bk.Term.Let{q, a, b}, tbl), mem.hd(PM.Fd(2n, m, r), Con{PM.Fd(3n, m, r), Nil{}}), hz0, hzs), ha, e),
        e => node.ne(b, ds, m, im, fi, nx, ks, img, ps, rs, z, PM.Fd(3n, m, r), c, tbl, hz0, hzs,
          part.ne(m, nx, fi, ps, rs, r, PM.Fd(3n, m, r), z, 3, 3, spb, nd.tg(ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Let{q, a, b}, 3, nd), {==},
            tbl.mask(m, im, fi, nx, Bk.Term.Let{q, a, b}, tbl), mem.tl(PM.Fd(2n, m, r), PM.Fd(3n, m, r), Con{PM.Fd(3n, m, r), Nil{}}, mem.hd(PM.Fd(3n, m, r), Nil{})), hz0, hzs), hb, e))
    case Bk.Term.All{+q, +a, +b}:
      (+nd, rr) = h
      (qs, r2) = rr
      (pa, pb) = r2
      (spa, ha) = pa
      (spb, hb) = pb
      node.or3(U32.is_eq(r, c), PM.Node(a, m, PM.Fd(2n, m, r), c), PM.Node(b, m, PM.Fd(3n, m, r), c), {U32.is_eq(c, z) == False{} : Bool}, hn,
        e => rew.ne(r, c, z, e, hr),
        e => node.ne(a, ds, m, im, fi, nx, ks, img, ps, rs, z, PM.Fd(2n, m, r), c, tbl, hz0, hzs,
          part.ne(m, nx, fi, ps, rs, r, PM.Fd(2n, m, r), z, 6, 3, spa, nd.tg(ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.All{q, a, b}, 6, nd), {==},
            tbl.mask(m, im, fi, nx, Bk.Term.All{q, a, b}, tbl), mem.hd(PM.Fd(2n, m, r), Con{PM.Fd(3n, m, r), Nil{}}), hz0, hzs), ha, e),
        e => node.ne(b, ds, m, im, fi, nx, ks, img, ps, rs, z, PM.Fd(3n, m, r), c, tbl, hz0, hzs,
          part.ne(m, nx, fi, ps, rs, r, PM.Fd(3n, m, r), z, 6, 3, spb, nd.tg(ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.All{q, a, b}, 6, nd), {==},
            tbl.mask(m, im, fi, nx, Bk.Term.All{q, a, b}, tbl), mem.tl(PM.Fd(2n, m, r), PM.Fd(3n, m, r), Con{PM.Fd(3n, m, r), Nil{}}, mem.hd(PM.Fd(3n, m, r), Nil{})), hz0, hzs), hb, e))
    case Bk.Term.App{+q, +a, +b}:
      (+nd, rr) = h
      (qs, r2) = rr
      (pa, pb) = r2
      (spa, ha) = pa
      (spb, hb) = pb
      node.or3(U32.is_eq(r, c), PM.Node(a, m, PM.Fd(2n, m, r), c), PM.Node(b, m, PM.Fd(3n, m, r), c), {U32.is_eq(c, z) == False{} : Bool}, hn,
        e => rew.ne(r, c, z, e, hr),
        e => node.ne(a, ds, m, im, fi, nx, ks, img, ps, rs, z, PM.Fd(2n, m, r), c, tbl, hz0, hzs,
          part.ne(m, nx, fi, ps, rs, r, PM.Fd(2n, m, r), z, 8, 3, spa, nd.tg(ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.App{q, a, b}, 8, nd), {==},
            tbl.mask(m, im, fi, nx, Bk.Term.App{q, a, b}, tbl), mem.hd(PM.Fd(2n, m, r), Con{PM.Fd(3n, m, r), Nil{}}), hz0, hzs), ha, e),
        e => node.ne(b, ds, m, im, fi, nx, ks, img, ps, rs, z, PM.Fd(3n, m, r), c, tbl, hz0, hzs,
          part.ne(m, nx, fi, ps, rs, r, PM.Fd(3n, m, r), z, 8, 3, spb, nd.tg(ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.App{q, a, b}, 8, nd), {==},
            tbl.mask(m, im, fi, nx, Bk.Term.App{q, a, b}, tbl), mem.tl(PM.Fd(2n, m, r), PM.Fd(3n, m, r), Con{PM.Fd(3n, m, r), Nil{}}, mem.hd(PM.Fd(3n, m, r), Nil{})), hz0, hzs), hb, e))
    case Bk.Term.Sig{+q, +a, +b}:
      (+nd, rr) = h
      (qs, r2) = rr
      (pa, pb) = r2
      (spa, ha) = pa
      (spb, hb) = pb
      node.or3(U32.is_eq(r, c), PM.Node(a, m, PM.Fd(2n, m, r), c), PM.Node(b, m, PM.Fd(3n, m, r), c), {U32.is_eq(c, z) == False{} : Bool}, hn,
        e => rew.ne(r, c, z, e, hr),
        e => node.ne(a, ds, m, im, fi, nx, ks, img, ps, rs, z, PM.Fd(2n, m, r), c, tbl, hz0, hzs,
          part.ne(m, nx, fi, ps, rs, r, PM.Fd(2n, m, r), z, 9, 3, spa, nd.tg(ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Sig{q, a, b}, 9, nd), {==},
            tbl.mask(m, im, fi, nx, Bk.Term.Sig{q, a, b}, tbl), mem.hd(PM.Fd(2n, m, r), Con{PM.Fd(3n, m, r), Nil{}}), hz0, hzs), ha, e),
        e => node.ne(b, ds, m, im, fi, nx, ks, img, ps, rs, z, PM.Fd(3n, m, r), c, tbl, hz0, hzs,
          part.ne(m, nx, fi, ps, rs, r, PM.Fd(3n, m, r), z, 9, 3, spb, nd.tg(ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Sig{q, a, b}, 9, nd), {==},
            tbl.mask(m, im, fi, nx, Bk.Term.Sig{q, a, b}, tbl), mem.tl(PM.Fd(2n, m, r), PM.Fd(3n, m, r), Con{PM.Fd(3n, m, r), Nil{}}, mem.hd(PM.Fd(3n, m, r), Nil{})), hz0, hzs), hb, e))
    case Bk.Term.Tup{+q, +a, +b}:
      (+nd, rr) = h
      (qs, r2) = rr
      (pa, pb) = r2
      (spa, ha) = pa
      (spb, hb) = pb
      node.or3(U32.is_eq(r, c), PM.Node(a, m, PM.Fd(2n, m, r), c), PM.Node(b, m, PM.Fd(3n, m, r), c), {U32.is_eq(c, z) == False{} : Bool}, hn,
        e => rew.ne(r, c, z, e, hr),
        e => node.ne(a, ds, m, im, fi, nx, ks, img, ps, rs, z, PM.Fd(2n, m, r), c, tbl, hz0, hzs,
          part.ne(m, nx, fi, ps, rs, r, PM.Fd(2n, m, r), z, 10, 3, spa, nd.tg(ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Tup{q, a, b}, 10, nd), {==},
            tbl.mask(m, im, fi, nx, Bk.Term.Tup{q, a, b}, tbl), mem.hd(PM.Fd(2n, m, r), Con{PM.Fd(3n, m, r), Nil{}}), hz0, hzs), ha, e),
        e => node.ne(b, ds, m, im, fi, nx, ks, img, ps, rs, z, PM.Fd(3n, m, r), c, tbl, hz0, hzs,
          part.ne(m, nx, fi, ps, rs, r, PM.Fd(3n, m, r), z, 10, 3, spb, nd.tg(ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Tup{q, a, b}, 10, nd), {==},
            tbl.mask(m, im, fi, nx, Bk.Term.Tup{q, a, b}, tbl), mem.tl(PM.Fd(2n, m, r), PM.Fd(3n, m, r), Con{PM.Fd(3n, m, r), Nil{}}, mem.hd(PM.Fd(3n, m, r), Nil{})), hz0, hzs), hb, e))
    case Bk.Term.Typ{+a}:
      (+nd, pa) = h
      (spa, ha) = pa
      node.or2(U32.is_eq(r, c), PM.Node(a, m, PM.Fd(2n, m, r), c), {U32.is_eq(c, z) == False{} : Bool}, hn,
        e => rew.ne(r, c, z, e, hr),
        e => node.ne(a, ds, m, im, fi, nx, ks, img, ps, rs, z, PM.Fd(2n, m, r), c, tbl, hz0, hzs,
          part.ne(m, nx, fi, ps, rs, r, PM.Fd(2n, m, r), z, 4, 1, spa, nd.tg(ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Typ{a}, 4, nd), {==},
            tbl.mask(m, im, fi, nx, Bk.Term.Typ{a}, tbl), mem.hd(PM.Fd(2n, m, r), Nil{}), hz0, hzs), ha, e))
    case Bk.Term.Prj{+a}:
      (+nd, pa) = h
      (spa, ha) = pa
      node.or2(U32.is_eq(r, c), PM.Node(a, m, PM.Fd(2n, m, r), c), {U32.is_eq(c, z) == False{} : Bool}, hn,
        e => rew.ne(r, c, z, e, hr),
        e => node.ne(a, ds, m, im, fi, nx, ks, img, ps, rs, z, PM.Fd(2n, m, r), c, tbl, hz0, hzs,
          part.ne(m, nx, fi, ps, rs, r, PM.Fd(2n, m, r), z, 11, 1, spa, nd.tg(ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Prj{a}, 11, nd), {==},
            tbl.mask(m, im, fi, nx, Bk.Term.Prj{a}, tbl), mem.hd(PM.Fd(2n, m, r), Nil{}), hz0, hzs), ha, e))
    case Bk.Term.Lam{+q, +a}:
      (+nd, rr) = h
      (qs, pa) = rr
      (spa, ha) = pa
      node.or2(U32.is_eq(r, c), PM.Node(a, m, PM.Fd(2n, m, r), c), {U32.is_eq(c, z) == False{} : Bool}, hn,
        e => rew.ne(r, c, z, e, hr),
        e => node.ne(a, ds, m, im, fi, nx, ks, img, ps, rs, z, PM.Fd(2n, m, r), c, tbl, hz0, hzs,
          part.ne(m, nx, fi, ps, rs, r, PM.Fd(2n, m, r), z, 7, 1, spa, nd.tg(ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Lam{q, a}, 7, nd), {==},
            tbl.mask(m, im, fi, nx, Bk.Term.Lam{q, a}, tbl), mem.hd(PM.Fd(2n, m, r), Nil{}), hz0, hzs), ha, e))
    case Bk.Term.Mat{+k, +a, +b}:
      (+nd, rr) = h
      (nm, r2) = rr
      (pa, pb) = r2
      (spa, ha) = pa
      (spb, hb) = pb
      node.or3(U32.is_eq(r, c), PM.Node(a, m, PM.Fd(3n, m, r), c), PM.Node(b, m, PM.Fd(4n, m, r), c), {U32.is_eq(c, z) == False{} : Bool}, hn,
        e => rew.ne(r, c, z, e, hr),
        e => node.ne(a, ds, m, im, fi, nx, ks, img, ps, rs, z, PM.Fd(3n, m, r), c, tbl, hz0, hzs,
          part.ne(m, nx, fi, ps, rs, r, PM.Fd(3n, m, r), z, 14, 6, spa, nd.tg(ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Mat{k, a, b}, 14, nd), {==},
            tbl.mask(m, im, fi, nx, Bk.Term.Mat{k, a, b}, tbl), mem.hd(PM.Fd(3n, m, r), Con{PM.Fd(4n, m, r), Nil{}}), hz0, hzs), ha, e),
        e => node.ne(b, ds, m, im, fi, nx, ks, img, ps, rs, z, PM.Fd(4n, m, r), c, tbl, hz0, hzs,
          part.ne(m, nx, fi, ps, rs, r, PM.Fd(4n, m, r), z, 14, 6, spb, nd.tg(ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Mat{k, a, b}, 14, nd), {==},
            tbl.mask(m, im, fi, nx, Bk.Term.Mat{k, a, b}, tbl), mem.tl(PM.Fd(3n, m, r), PM.Fd(4n, m, r), Con{PM.Fd(4n, m, r), Nil{}}, mem.hd(PM.Fd(4n, m, r), Nil{})), hz0, hzs), hb, e))
    case Bk.Term.Eql{+a, +b, +d}:
      (+nd, rr) = h
      (pa, r2) = rr
      (spa, ha) = pa
      (pb, pd) = r2
      (spb, hb) = pb
      (spd, hd) = pd
      node.or4(U32.is_eq(r, c), PM.Node(a, m, PM.Fd(2n, m, r), c), PM.Node(b, m, PM.Fd(3n, m, r), c), PM.Node(d, m, PM.Fd(4n, m, r), c), {U32.is_eq(c, z) == False{} : Bool}, hn,
        e => rew.ne(r, c, z, e, hr),
        e => node.ne(a, ds, m, im, fi, nx, ks, img, ps, rs, z, PM.Fd(2n, m, r), c, tbl, hz0, hzs,
          part.ne(m, nx, fi, ps, rs, r, PM.Fd(2n, m, r), z, 16, 7, spa, nd.tg(ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Eql{a, b, d}, 16, nd), {==},
            tbl.mask(m, im, fi, nx, Bk.Term.Eql{a, b, d}, tbl), mem.hd(PM.Fd(2n, m, r), Con{PM.Fd(3n, m, r), Con{PM.Fd(4n, m, r), Nil{}}}), hz0, hzs), ha, e),
        e => node.ne(b, ds, m, im, fi, nx, ks, img, ps, rs, z, PM.Fd(3n, m, r), c, tbl, hz0, hzs,
          part.ne(m, nx, fi, ps, rs, r, PM.Fd(3n, m, r), z, 16, 7, spb, nd.tg(ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Eql{a, b, d}, 16, nd), {==},
            tbl.mask(m, im, fi, nx, Bk.Term.Eql{a, b, d}, tbl), mem.tl(PM.Fd(2n, m, r), PM.Fd(3n, m, r), Con{PM.Fd(3n, m, r), Con{PM.Fd(4n, m, r), Nil{}}}, mem.hd(PM.Fd(3n, m, r), Con{PM.Fd(4n, m, r), Nil{}})), hz0, hzs), hb, e),
        e => node.ne(d, ds, m, im, fi, nx, ks, img, ps, rs, z, PM.Fd(4n, m, r), c, tbl, hz0, hzs,
          part.ne(m, nx, fi, ps, rs, r, PM.Fd(4n, m, r), z, 16, 7, spd, nd.tg(ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Eql{a, b, d}, 16, nd), {==},
            tbl.mask(m, im, fi, nx, Bk.Term.Eql{a, b, d}, tbl), mem.tl(PM.Fd(2n, m, r), PM.Fd(4n, m, r), Con{PM.Fd(3n, m, r), Con{PM.Fd(4n, m, r), Nil{}}}, mem.tl(PM.Fd(3n, m, r), PM.Fd(4n, m, r), Con{PM.Fd(4n, m, r), Nil{}}, mem.hd(PM.Fd(4n, m, r), Nil{}))), hz0, hzs), hd, e))
    case Bk.Term.Rwt{+a, +b, +d}:
      (+nd, rr) = h
      (pa, r2) = rr
      (spa, ha) = pa
      (pb, pd) = r2
      (spb, hb) = pb
      (spd, hd) = pd
      node.or4(U32.is_eq(r, c), PM.Node(a, m, PM.Fd(2n, m, r), c), PM.Node(b, m, PM.Fd(3n, m, r), c), PM.Node(d, m, PM.Fd(4n, m, r), c), {U32.is_eq(c, z) == False{} : Bool}, hn,
        e => rew.ne(r, c, z, e, hr),
        e => node.ne(a, ds, m, im, fi, nx, ks, img, ps, rs, z, PM.Fd(2n, m, r), c, tbl, hz0, hzs,
          part.ne(m, nx, fi, ps, rs, r, PM.Fd(2n, m, r), z, 18, 7, spa, nd.tg(ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Rwt{a, b, d}, 18, nd), {==},
            tbl.mask(m, im, fi, nx, Bk.Term.Rwt{a, b, d}, tbl), mem.hd(PM.Fd(2n, m, r), Con{PM.Fd(3n, m, r), Con{PM.Fd(4n, m, r), Nil{}}}), hz0, hzs), ha, e),
        e => node.ne(b, ds, m, im, fi, nx, ks, img, ps, rs, z, PM.Fd(3n, m, r), c, tbl, hz0, hzs,
          part.ne(m, nx, fi, ps, rs, r, PM.Fd(3n, m, r), z, 18, 7, spb, nd.tg(ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Rwt{a, b, d}, 18, nd), {==},
            tbl.mask(m, im, fi, nx, Bk.Term.Rwt{a, b, d}, tbl), mem.tl(PM.Fd(2n, m, r), PM.Fd(3n, m, r), Con{PM.Fd(3n, m, r), Con{PM.Fd(4n, m, r), Nil{}}}, mem.hd(PM.Fd(3n, m, r), Con{PM.Fd(4n, m, r), Nil{}})), hz0, hzs), hb, e),
        e => node.ne(d, ds, m, im, fi, nx, ks, img, ps, rs, z, PM.Fd(4n, m, r), c, tbl, hz0, hzs,
          part.ne(m, nx, fi, ps, rs, r, PM.Fd(4n, m, r), z, 18, 7, spd, nd.tg(ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Rwt{a, b, d}, 18, nd), {==},
            tbl.mask(m, im, fi, nx, Bk.Term.Rwt{a, b, d}, tbl), mem.tl(PM.Fd(2n, m, r), PM.Fd(4n, m, r), Con{PM.Fd(3n, m, r), Con{PM.Fd(4n, m, r), Nil{}}}, mem.tl(PM.Fd(3n, m, r), PM.Fd(4n, m, r), Con{PM.Fd(4n, m, r), Nil{}}, mem.hd(PM.Fd(4n, m, r), Nil{}))), hz0, hzs), hd, e))

# a store to z keeps the nodes of a term at a cell r that is not z
def Node.fz(t: Bk.Term, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +rs: List<&2, U32>, +z: U32, +x: Cr.Cir.Cell, +r: U32, +c: U32, +tbl: PM.Tbl(m, im, fi, nx),
  +hz0: {PM.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, rs, z) == 0n : Nat}, +hzs: {PM.Fl(m, z, 1024) == False{} : Bool},
  hr: {U32.is_eq(r, z) == False{} : Bool}, h: PM.Is(ds, m, im, fi, nx, ks, img, r, t)) ->
  {PM.Node(t, Cr.Cir.Cells.set(m, z, x), r, c) == PM.Node(t, m, r, c) : Bool}:
  match t:
    case Bk.Term.Var{_}:
      {==}
    case Bk.Term.Ref{_}:
      {==}
    case Bk.Term.Enu{_}:
      {==}
    case Bk.Term.Lab{_}:
      {==}
    case Bk.Term.Efq{}:
      {==}
    case Bk.Term.Rfl{}:
      {==}
    case Bk.Term.Ann{+a, +b}:
      (+nd, rr) = h
      (pa, pb) = rr
      (spa, ha) = pa
      (spb, hb) = pb
      +ec = PM.cl.go(m, r, z, x, hr)
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, x), r), Cr.Cir.Cells.get(m, r), ec) :
        {Bool.or(U32.is_eq(r, c), Bool.or(PM.Node(a, Cr.Cir.Cells.set(m, z, x), Cr.Cir.Cell.get(2n, _), c), PM.Node(b, Cr.Cir.Cells.set(m, z, x), Cr.Cir.Cell.get(3n, _), c))) == Bool.or(U32.is_eq(r, c), Bool.or(PM.Node(a, m, PM.Fd(2n, m, r), c), PM.Node(b, m, PM.Fd(3n, m, r), c))) : Bool}
      %Equal.sym(Bool, PM.Node(a, Cr.Cir.Cells.set(m, z, x), PM.Fd(2n, m, r), c), PM.Node(a, m, PM.Fd(2n, m, r), c),
        Node.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(2n, m, r), c, tbl, hz0, hzs,
          part.ne(m, nx, fi, ps, rs, r, PM.Fd(2n, m, r), z, 2, 3, spa, nd.tg(ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Ann{a, b}, 2, nd), {==},
            tbl.mask(m, im, fi, nx, Bk.Term.Ann{a, b}, tbl), mem.hd(PM.Fd(2n, m, r), Con{PM.Fd(3n, m, r), Nil{}}), hz0, hzs), ha)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(_, PM.Node(b, Cr.Cir.Cells.set(m, z, x), PM.Fd(3n, m, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(PM.Node(a, m, PM.Fd(2n, m, r), c), PM.Node(b, m, PM.Fd(3n, m, r), c))) : Bool}
      %Equal.sym(Bool, PM.Node(b, Cr.Cir.Cells.set(m, z, x), PM.Fd(3n, m, r), c), PM.Node(b, m, PM.Fd(3n, m, r), c),
        Node.fz(b, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(3n, m, r), c, tbl, hz0, hzs,
          part.ne(m, nx, fi, ps, rs, r, PM.Fd(3n, m, r), z, 2, 3, spb, nd.tg(ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Ann{a, b}, 2, nd), {==},
            tbl.mask(m, im, fi, nx, Bk.Term.Ann{a, b}, tbl), mem.tl(PM.Fd(2n, m, r), PM.Fd(3n, m, r), Con{PM.Fd(3n, m, r), Nil{}}, mem.hd(PM.Fd(3n, m, r), Nil{})), hz0, hzs), hb)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(PM.Node(a, m, PM.Fd(2n, m, r), c), _)) == Bool.or(U32.is_eq(r, c), Bool.or(PM.Node(a, m, PM.Fd(2n, m, r), c), PM.Node(b, m, PM.Fd(3n, m, r), c))) : Bool}
      {==}
    case Bk.Term.Min{+a, +b}:
      (+nd, rr) = h
      (pa, pb) = rr
      (spa, ha) = pa
      (spb, hb) = pb
      +ec = PM.cl.go(m, r, z, x, hr)
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, x), r), Cr.Cir.Cells.get(m, r), ec) :
        {Bool.or(U32.is_eq(r, c), Bool.or(PM.Node(a, Cr.Cir.Cells.set(m, z, x), Cr.Cir.Cell.get(2n, _), c), PM.Node(b, Cr.Cir.Cells.set(m, z, x), Cr.Cir.Cell.get(3n, _), c))) == Bool.or(U32.is_eq(r, c), Bool.or(PM.Node(a, m, PM.Fd(2n, m, r), c), PM.Node(b, m, PM.Fd(3n, m, r), c))) : Bool}
      %Equal.sym(Bool, PM.Node(a, Cr.Cir.Cells.set(m, z, x), PM.Fd(2n, m, r), c), PM.Node(a, m, PM.Fd(2n, m, r), c),
        Node.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(2n, m, r), c, tbl, hz0, hzs,
          part.ne(m, nx, fi, ps, rs, r, PM.Fd(2n, m, r), z, 5, 3, spa, nd.tg(ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Min{a, b}, 5, nd), {==},
            tbl.mask(m, im, fi, nx, Bk.Term.Min{a, b}, tbl), mem.hd(PM.Fd(2n, m, r), Con{PM.Fd(3n, m, r), Nil{}}), hz0, hzs), ha)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(_, PM.Node(b, Cr.Cir.Cells.set(m, z, x), PM.Fd(3n, m, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(PM.Node(a, m, PM.Fd(2n, m, r), c), PM.Node(b, m, PM.Fd(3n, m, r), c))) : Bool}
      %Equal.sym(Bool, PM.Node(b, Cr.Cir.Cells.set(m, z, x), PM.Fd(3n, m, r), c), PM.Node(b, m, PM.Fd(3n, m, r), c),
        Node.fz(b, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(3n, m, r), c, tbl, hz0, hzs,
          part.ne(m, nx, fi, ps, rs, r, PM.Fd(3n, m, r), z, 5, 3, spb, nd.tg(ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Min{a, b}, 5, nd), {==},
            tbl.mask(m, im, fi, nx, Bk.Term.Min{a, b}, tbl), mem.tl(PM.Fd(2n, m, r), PM.Fd(3n, m, r), Con{PM.Fd(3n, m, r), Nil{}}, mem.hd(PM.Fd(3n, m, r), Nil{})), hz0, hzs), hb)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(PM.Node(a, m, PM.Fd(2n, m, r), c), _)) == Bool.or(U32.is_eq(r, c), Bool.or(PM.Node(a, m, PM.Fd(2n, m, r), c), PM.Node(b, m, PM.Fd(3n, m, r), c))) : Bool}
      {==}
    case Bk.Term.Let{+q, +a, +b}:
      (+nd, rr) = h
      (qs, r2) = rr
      (pa, pb) = r2
      (spa, ha) = pa
      (spb, hb) = pb
      +ec = PM.cl.go(m, r, z, x, hr)
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, x), r), Cr.Cir.Cells.get(m, r), ec) :
        {Bool.or(U32.is_eq(r, c), Bool.or(PM.Node(a, Cr.Cir.Cells.set(m, z, x), Cr.Cir.Cell.get(2n, _), c), PM.Node(b, Cr.Cir.Cells.set(m, z, x), Cr.Cir.Cell.get(3n, _), c))) == Bool.or(U32.is_eq(r, c), Bool.or(PM.Node(a, m, PM.Fd(2n, m, r), c), PM.Node(b, m, PM.Fd(3n, m, r), c))) : Bool}
      %Equal.sym(Bool, PM.Node(a, Cr.Cir.Cells.set(m, z, x), PM.Fd(2n, m, r), c), PM.Node(a, m, PM.Fd(2n, m, r), c),
        Node.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(2n, m, r), c, tbl, hz0, hzs,
          part.ne(m, nx, fi, ps, rs, r, PM.Fd(2n, m, r), z, 3, 3, spa, nd.tg(ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Let{q, a, b}, 3, nd), {==},
            tbl.mask(m, im, fi, nx, Bk.Term.Let{q, a, b}, tbl), mem.hd(PM.Fd(2n, m, r), Con{PM.Fd(3n, m, r), Nil{}}), hz0, hzs), ha)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(_, PM.Node(b, Cr.Cir.Cells.set(m, z, x), PM.Fd(3n, m, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(PM.Node(a, m, PM.Fd(2n, m, r), c), PM.Node(b, m, PM.Fd(3n, m, r), c))) : Bool}
      %Equal.sym(Bool, PM.Node(b, Cr.Cir.Cells.set(m, z, x), PM.Fd(3n, m, r), c), PM.Node(b, m, PM.Fd(3n, m, r), c),
        Node.fz(b, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(3n, m, r), c, tbl, hz0, hzs,
          part.ne(m, nx, fi, ps, rs, r, PM.Fd(3n, m, r), z, 3, 3, spb, nd.tg(ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Let{q, a, b}, 3, nd), {==},
            tbl.mask(m, im, fi, nx, Bk.Term.Let{q, a, b}, tbl), mem.tl(PM.Fd(2n, m, r), PM.Fd(3n, m, r), Con{PM.Fd(3n, m, r), Nil{}}, mem.hd(PM.Fd(3n, m, r), Nil{})), hz0, hzs), hb)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(PM.Node(a, m, PM.Fd(2n, m, r), c), _)) == Bool.or(U32.is_eq(r, c), Bool.or(PM.Node(a, m, PM.Fd(2n, m, r), c), PM.Node(b, m, PM.Fd(3n, m, r), c))) : Bool}
      {==}
    case Bk.Term.All{+q, +a, +b}:
      (+nd, rr) = h
      (qs, r2) = rr
      (pa, pb) = r2
      (spa, ha) = pa
      (spb, hb) = pb
      +ec = PM.cl.go(m, r, z, x, hr)
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, x), r), Cr.Cir.Cells.get(m, r), ec) :
        {Bool.or(U32.is_eq(r, c), Bool.or(PM.Node(a, Cr.Cir.Cells.set(m, z, x), Cr.Cir.Cell.get(2n, _), c), PM.Node(b, Cr.Cir.Cells.set(m, z, x), Cr.Cir.Cell.get(3n, _), c))) == Bool.or(U32.is_eq(r, c), Bool.or(PM.Node(a, m, PM.Fd(2n, m, r), c), PM.Node(b, m, PM.Fd(3n, m, r), c))) : Bool}
      %Equal.sym(Bool, PM.Node(a, Cr.Cir.Cells.set(m, z, x), PM.Fd(2n, m, r), c), PM.Node(a, m, PM.Fd(2n, m, r), c),
        Node.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(2n, m, r), c, tbl, hz0, hzs,
          part.ne(m, nx, fi, ps, rs, r, PM.Fd(2n, m, r), z, 6, 3, spa, nd.tg(ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.All{q, a, b}, 6, nd), {==},
            tbl.mask(m, im, fi, nx, Bk.Term.All{q, a, b}, tbl), mem.hd(PM.Fd(2n, m, r), Con{PM.Fd(3n, m, r), Nil{}}), hz0, hzs), ha)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(_, PM.Node(b, Cr.Cir.Cells.set(m, z, x), PM.Fd(3n, m, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(PM.Node(a, m, PM.Fd(2n, m, r), c), PM.Node(b, m, PM.Fd(3n, m, r), c))) : Bool}
      %Equal.sym(Bool, PM.Node(b, Cr.Cir.Cells.set(m, z, x), PM.Fd(3n, m, r), c), PM.Node(b, m, PM.Fd(3n, m, r), c),
        Node.fz(b, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(3n, m, r), c, tbl, hz0, hzs,
          part.ne(m, nx, fi, ps, rs, r, PM.Fd(3n, m, r), z, 6, 3, spb, nd.tg(ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.All{q, a, b}, 6, nd), {==},
            tbl.mask(m, im, fi, nx, Bk.Term.All{q, a, b}, tbl), mem.tl(PM.Fd(2n, m, r), PM.Fd(3n, m, r), Con{PM.Fd(3n, m, r), Nil{}}, mem.hd(PM.Fd(3n, m, r), Nil{})), hz0, hzs), hb)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(PM.Node(a, m, PM.Fd(2n, m, r), c), _)) == Bool.or(U32.is_eq(r, c), Bool.or(PM.Node(a, m, PM.Fd(2n, m, r), c), PM.Node(b, m, PM.Fd(3n, m, r), c))) : Bool}
      {==}
    case Bk.Term.App{+q, +a, +b}:
      (+nd, rr) = h
      (qs, r2) = rr
      (pa, pb) = r2
      (spa, ha) = pa
      (spb, hb) = pb
      +ec = PM.cl.go(m, r, z, x, hr)
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, x), r), Cr.Cir.Cells.get(m, r), ec) :
        {Bool.or(U32.is_eq(r, c), Bool.or(PM.Node(a, Cr.Cir.Cells.set(m, z, x), Cr.Cir.Cell.get(2n, _), c), PM.Node(b, Cr.Cir.Cells.set(m, z, x), Cr.Cir.Cell.get(3n, _), c))) == Bool.or(U32.is_eq(r, c), Bool.or(PM.Node(a, m, PM.Fd(2n, m, r), c), PM.Node(b, m, PM.Fd(3n, m, r), c))) : Bool}
      %Equal.sym(Bool, PM.Node(a, Cr.Cir.Cells.set(m, z, x), PM.Fd(2n, m, r), c), PM.Node(a, m, PM.Fd(2n, m, r), c),
        Node.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(2n, m, r), c, tbl, hz0, hzs,
          part.ne(m, nx, fi, ps, rs, r, PM.Fd(2n, m, r), z, 8, 3, spa, nd.tg(ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.App{q, a, b}, 8, nd), {==},
            tbl.mask(m, im, fi, nx, Bk.Term.App{q, a, b}, tbl), mem.hd(PM.Fd(2n, m, r), Con{PM.Fd(3n, m, r), Nil{}}), hz0, hzs), ha)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(_, PM.Node(b, Cr.Cir.Cells.set(m, z, x), PM.Fd(3n, m, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(PM.Node(a, m, PM.Fd(2n, m, r), c), PM.Node(b, m, PM.Fd(3n, m, r), c))) : Bool}
      %Equal.sym(Bool, PM.Node(b, Cr.Cir.Cells.set(m, z, x), PM.Fd(3n, m, r), c), PM.Node(b, m, PM.Fd(3n, m, r), c),
        Node.fz(b, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(3n, m, r), c, tbl, hz0, hzs,
          part.ne(m, nx, fi, ps, rs, r, PM.Fd(3n, m, r), z, 8, 3, spb, nd.tg(ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.App{q, a, b}, 8, nd), {==},
            tbl.mask(m, im, fi, nx, Bk.Term.App{q, a, b}, tbl), mem.tl(PM.Fd(2n, m, r), PM.Fd(3n, m, r), Con{PM.Fd(3n, m, r), Nil{}}, mem.hd(PM.Fd(3n, m, r), Nil{})), hz0, hzs), hb)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(PM.Node(a, m, PM.Fd(2n, m, r), c), _)) == Bool.or(U32.is_eq(r, c), Bool.or(PM.Node(a, m, PM.Fd(2n, m, r), c), PM.Node(b, m, PM.Fd(3n, m, r), c))) : Bool}
      {==}
    case Bk.Term.Sig{+q, +a, +b}:
      (+nd, rr) = h
      (qs, r2) = rr
      (pa, pb) = r2
      (spa, ha) = pa
      (spb, hb) = pb
      +ec = PM.cl.go(m, r, z, x, hr)
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, x), r), Cr.Cir.Cells.get(m, r), ec) :
        {Bool.or(U32.is_eq(r, c), Bool.or(PM.Node(a, Cr.Cir.Cells.set(m, z, x), Cr.Cir.Cell.get(2n, _), c), PM.Node(b, Cr.Cir.Cells.set(m, z, x), Cr.Cir.Cell.get(3n, _), c))) == Bool.or(U32.is_eq(r, c), Bool.or(PM.Node(a, m, PM.Fd(2n, m, r), c), PM.Node(b, m, PM.Fd(3n, m, r), c))) : Bool}
      %Equal.sym(Bool, PM.Node(a, Cr.Cir.Cells.set(m, z, x), PM.Fd(2n, m, r), c), PM.Node(a, m, PM.Fd(2n, m, r), c),
        Node.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(2n, m, r), c, tbl, hz0, hzs,
          part.ne(m, nx, fi, ps, rs, r, PM.Fd(2n, m, r), z, 9, 3, spa, nd.tg(ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Sig{q, a, b}, 9, nd), {==},
            tbl.mask(m, im, fi, nx, Bk.Term.Sig{q, a, b}, tbl), mem.hd(PM.Fd(2n, m, r), Con{PM.Fd(3n, m, r), Nil{}}), hz0, hzs), ha)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(_, PM.Node(b, Cr.Cir.Cells.set(m, z, x), PM.Fd(3n, m, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(PM.Node(a, m, PM.Fd(2n, m, r), c), PM.Node(b, m, PM.Fd(3n, m, r), c))) : Bool}
      %Equal.sym(Bool, PM.Node(b, Cr.Cir.Cells.set(m, z, x), PM.Fd(3n, m, r), c), PM.Node(b, m, PM.Fd(3n, m, r), c),
        Node.fz(b, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(3n, m, r), c, tbl, hz0, hzs,
          part.ne(m, nx, fi, ps, rs, r, PM.Fd(3n, m, r), z, 9, 3, spb, nd.tg(ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Sig{q, a, b}, 9, nd), {==},
            tbl.mask(m, im, fi, nx, Bk.Term.Sig{q, a, b}, tbl), mem.tl(PM.Fd(2n, m, r), PM.Fd(3n, m, r), Con{PM.Fd(3n, m, r), Nil{}}, mem.hd(PM.Fd(3n, m, r), Nil{})), hz0, hzs), hb)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(PM.Node(a, m, PM.Fd(2n, m, r), c), _)) == Bool.or(U32.is_eq(r, c), Bool.or(PM.Node(a, m, PM.Fd(2n, m, r), c), PM.Node(b, m, PM.Fd(3n, m, r), c))) : Bool}
      {==}
    case Bk.Term.Tup{+q, +a, +b}:
      (+nd, rr) = h
      (qs, r2) = rr
      (pa, pb) = r2
      (spa, ha) = pa
      (spb, hb) = pb
      +ec = PM.cl.go(m, r, z, x, hr)
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, x), r), Cr.Cir.Cells.get(m, r), ec) :
        {Bool.or(U32.is_eq(r, c), Bool.or(PM.Node(a, Cr.Cir.Cells.set(m, z, x), Cr.Cir.Cell.get(2n, _), c), PM.Node(b, Cr.Cir.Cells.set(m, z, x), Cr.Cir.Cell.get(3n, _), c))) == Bool.or(U32.is_eq(r, c), Bool.or(PM.Node(a, m, PM.Fd(2n, m, r), c), PM.Node(b, m, PM.Fd(3n, m, r), c))) : Bool}
      %Equal.sym(Bool, PM.Node(a, Cr.Cir.Cells.set(m, z, x), PM.Fd(2n, m, r), c), PM.Node(a, m, PM.Fd(2n, m, r), c),
        Node.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(2n, m, r), c, tbl, hz0, hzs,
          part.ne(m, nx, fi, ps, rs, r, PM.Fd(2n, m, r), z, 10, 3, spa, nd.tg(ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Tup{q, a, b}, 10, nd), {==},
            tbl.mask(m, im, fi, nx, Bk.Term.Tup{q, a, b}, tbl), mem.hd(PM.Fd(2n, m, r), Con{PM.Fd(3n, m, r), Nil{}}), hz0, hzs), ha)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(_, PM.Node(b, Cr.Cir.Cells.set(m, z, x), PM.Fd(3n, m, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(PM.Node(a, m, PM.Fd(2n, m, r), c), PM.Node(b, m, PM.Fd(3n, m, r), c))) : Bool}
      %Equal.sym(Bool, PM.Node(b, Cr.Cir.Cells.set(m, z, x), PM.Fd(3n, m, r), c), PM.Node(b, m, PM.Fd(3n, m, r), c),
        Node.fz(b, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(3n, m, r), c, tbl, hz0, hzs,
          part.ne(m, nx, fi, ps, rs, r, PM.Fd(3n, m, r), z, 10, 3, spb, nd.tg(ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Tup{q, a, b}, 10, nd), {==},
            tbl.mask(m, im, fi, nx, Bk.Term.Tup{q, a, b}, tbl), mem.tl(PM.Fd(2n, m, r), PM.Fd(3n, m, r), Con{PM.Fd(3n, m, r), Nil{}}, mem.hd(PM.Fd(3n, m, r), Nil{})), hz0, hzs), hb)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(PM.Node(a, m, PM.Fd(2n, m, r), c), _)) == Bool.or(U32.is_eq(r, c), Bool.or(PM.Node(a, m, PM.Fd(2n, m, r), c), PM.Node(b, m, PM.Fd(3n, m, r), c))) : Bool}
      {==}
    case Bk.Term.Typ{+a}:
      (+nd, pa) = h
      (spa, ha) = pa
      +ec = PM.cl.go(m, r, z, x, hr)
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, x), r), Cr.Cir.Cells.get(m, r), ec) :
        {Bool.or(U32.is_eq(r, c), PM.Node(a, Cr.Cir.Cells.set(m, z, x), Cr.Cir.Cell.get(2n, _), c)) == Bool.or(U32.is_eq(r, c), PM.Node(a, m, PM.Fd(2n, m, r), c)) : Bool}
      %Equal.sym(Bool, PM.Node(a, Cr.Cir.Cells.set(m, z, x), PM.Fd(2n, m, r), c), PM.Node(a, m, PM.Fd(2n, m, r), c),
        Node.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(2n, m, r), c, tbl, hz0, hzs,
          part.ne(m, nx, fi, ps, rs, r, PM.Fd(2n, m, r), z, 4, 1, spa, nd.tg(ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Typ{a}, 4, nd), {==},
            tbl.mask(m, im, fi, nx, Bk.Term.Typ{a}, tbl), mem.hd(PM.Fd(2n, m, r), Nil{}), hz0, hzs), ha)) :
        {Bool.or(U32.is_eq(r, c), _) == Bool.or(U32.is_eq(r, c), PM.Node(a, m, PM.Fd(2n, m, r), c)) : Bool}
      {==}
    case Bk.Term.Prj{+a}:
      (+nd, pa) = h
      (spa, ha) = pa
      +ec = PM.cl.go(m, r, z, x, hr)
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, x), r), Cr.Cir.Cells.get(m, r), ec) :
        {Bool.or(U32.is_eq(r, c), PM.Node(a, Cr.Cir.Cells.set(m, z, x), Cr.Cir.Cell.get(2n, _), c)) == Bool.or(U32.is_eq(r, c), PM.Node(a, m, PM.Fd(2n, m, r), c)) : Bool}
      %Equal.sym(Bool, PM.Node(a, Cr.Cir.Cells.set(m, z, x), PM.Fd(2n, m, r), c), PM.Node(a, m, PM.Fd(2n, m, r), c),
        Node.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(2n, m, r), c, tbl, hz0, hzs,
          part.ne(m, nx, fi, ps, rs, r, PM.Fd(2n, m, r), z, 11, 1, spa, nd.tg(ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Prj{a}, 11, nd), {==},
            tbl.mask(m, im, fi, nx, Bk.Term.Prj{a}, tbl), mem.hd(PM.Fd(2n, m, r), Nil{}), hz0, hzs), ha)) :
        {Bool.or(U32.is_eq(r, c), _) == Bool.or(U32.is_eq(r, c), PM.Node(a, m, PM.Fd(2n, m, r), c)) : Bool}
      {==}
    case Bk.Term.Lam{+q, +a}:
      (+nd, rr) = h
      (qs, pa) = rr
      (spa, ha) = pa
      +ec = PM.cl.go(m, r, z, x, hr)
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, x), r), Cr.Cir.Cells.get(m, r), ec) :
        {Bool.or(U32.is_eq(r, c), PM.Node(a, Cr.Cir.Cells.set(m, z, x), Cr.Cir.Cell.get(2n, _), c)) == Bool.or(U32.is_eq(r, c), PM.Node(a, m, PM.Fd(2n, m, r), c)) : Bool}
      %Equal.sym(Bool, PM.Node(a, Cr.Cir.Cells.set(m, z, x), PM.Fd(2n, m, r), c), PM.Node(a, m, PM.Fd(2n, m, r), c),
        Node.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(2n, m, r), c, tbl, hz0, hzs,
          part.ne(m, nx, fi, ps, rs, r, PM.Fd(2n, m, r), z, 7, 1, spa, nd.tg(ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Lam{q, a}, 7, nd), {==},
            tbl.mask(m, im, fi, nx, Bk.Term.Lam{q, a}, tbl), mem.hd(PM.Fd(2n, m, r), Nil{}), hz0, hzs), ha)) :
        {Bool.or(U32.is_eq(r, c), _) == Bool.or(U32.is_eq(r, c), PM.Node(a, m, PM.Fd(2n, m, r), c)) : Bool}
      {==}
    case Bk.Term.Mat{+k, +a, +b}:
      (+nd, rr) = h
      (nm, r2) = rr
      (pa, pb) = r2
      (spa, ha) = pa
      (spb, hb) = pb
      +ec = PM.cl.go(m, r, z, x, hr)
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, x), r), Cr.Cir.Cells.get(m, r), ec) :
        {Bool.or(U32.is_eq(r, c), Bool.or(PM.Node(a, Cr.Cir.Cells.set(m, z, x), Cr.Cir.Cell.get(3n, _), c), PM.Node(b, Cr.Cir.Cells.set(m, z, x), Cr.Cir.Cell.get(4n, _), c))) == Bool.or(U32.is_eq(r, c), Bool.or(PM.Node(a, m, PM.Fd(3n, m, r), c), PM.Node(b, m, PM.Fd(4n, m, r), c))) : Bool}
      %Equal.sym(Bool, PM.Node(a, Cr.Cir.Cells.set(m, z, x), PM.Fd(3n, m, r), c), PM.Node(a, m, PM.Fd(3n, m, r), c),
        Node.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(3n, m, r), c, tbl, hz0, hzs,
          part.ne(m, nx, fi, ps, rs, r, PM.Fd(3n, m, r), z, 14, 6, spa, nd.tg(ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Mat{k, a, b}, 14, nd), {==},
            tbl.mask(m, im, fi, nx, Bk.Term.Mat{k, a, b}, tbl), mem.hd(PM.Fd(3n, m, r), Con{PM.Fd(4n, m, r), Nil{}}), hz0, hzs), ha)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(_, PM.Node(b, Cr.Cir.Cells.set(m, z, x), PM.Fd(4n, m, r), c))) == Bool.or(U32.is_eq(r, c), Bool.or(PM.Node(a, m, PM.Fd(3n, m, r), c), PM.Node(b, m, PM.Fd(4n, m, r), c))) : Bool}
      %Equal.sym(Bool, PM.Node(b, Cr.Cir.Cells.set(m, z, x), PM.Fd(4n, m, r), c), PM.Node(b, m, PM.Fd(4n, m, r), c),
        Node.fz(b, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(4n, m, r), c, tbl, hz0, hzs,
          part.ne(m, nx, fi, ps, rs, r, PM.Fd(4n, m, r), z, 14, 6, spb, nd.tg(ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Mat{k, a, b}, 14, nd), {==},
            tbl.mask(m, im, fi, nx, Bk.Term.Mat{k, a, b}, tbl), mem.tl(PM.Fd(3n, m, r), PM.Fd(4n, m, r), Con{PM.Fd(4n, m, r), Nil{}}, mem.hd(PM.Fd(4n, m, r), Nil{})), hz0, hzs), hb)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(PM.Node(a, m, PM.Fd(3n, m, r), c), _)) == Bool.or(U32.is_eq(r, c), Bool.or(PM.Node(a, m, PM.Fd(3n, m, r), c), PM.Node(b, m, PM.Fd(4n, m, r), c))) : Bool}
      {==}
    case Bk.Term.Eql{+a, +b, +d}:
      (+nd, rr) = h
      (pa, r2) = rr
      (spa, ha) = pa
      (pb, pd) = r2
      (spb, hb) = pb
      (spd, hd) = pd
      +ec = PM.cl.go(m, r, z, x, hr)
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, x), r), Cr.Cir.Cells.get(m, r), ec) :
        {Bool.or(U32.is_eq(r, c), Bool.or(PM.Node(a, Cr.Cir.Cells.set(m, z, x), Cr.Cir.Cell.get(2n, _), c), Bool.or(PM.Node(b, Cr.Cir.Cells.set(m, z, x), Cr.Cir.Cell.get(3n, _), c), PM.Node(d, Cr.Cir.Cells.set(m, z, x), Cr.Cir.Cell.get(4n, _), c)))) == Bool.or(U32.is_eq(r, c), Bool.or(PM.Node(a, m, PM.Fd(2n, m, r), c), Bool.or(PM.Node(b, m, PM.Fd(3n, m, r), c), PM.Node(d, m, PM.Fd(4n, m, r), c)))) : Bool}
      %Equal.sym(Bool, PM.Node(a, Cr.Cir.Cells.set(m, z, x), PM.Fd(2n, m, r), c), PM.Node(a, m, PM.Fd(2n, m, r), c),
        Node.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(2n, m, r), c, tbl, hz0, hzs,
          part.ne(m, nx, fi, ps, rs, r, PM.Fd(2n, m, r), z, 16, 7, spa, nd.tg(ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Eql{a, b, d}, 16, nd), {==},
            tbl.mask(m, im, fi, nx, Bk.Term.Eql{a, b, d}, tbl), mem.hd(PM.Fd(2n, m, r), Con{PM.Fd(3n, m, r), Con{PM.Fd(4n, m, r), Nil{}}}), hz0, hzs), ha)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(_, Bool.or(PM.Node(b, Cr.Cir.Cells.set(m, z, x), PM.Fd(3n, m, r), c), PM.Node(d, Cr.Cir.Cells.set(m, z, x), PM.Fd(4n, m, r), c)))) == Bool.or(U32.is_eq(r, c), Bool.or(PM.Node(a, m, PM.Fd(2n, m, r), c), Bool.or(PM.Node(b, m, PM.Fd(3n, m, r), c), PM.Node(d, m, PM.Fd(4n, m, r), c)))) : Bool}
      %Equal.sym(Bool, PM.Node(b, Cr.Cir.Cells.set(m, z, x), PM.Fd(3n, m, r), c), PM.Node(b, m, PM.Fd(3n, m, r), c),
        Node.fz(b, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(3n, m, r), c, tbl, hz0, hzs,
          part.ne(m, nx, fi, ps, rs, r, PM.Fd(3n, m, r), z, 16, 7, spb, nd.tg(ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Eql{a, b, d}, 16, nd), {==},
            tbl.mask(m, im, fi, nx, Bk.Term.Eql{a, b, d}, tbl), mem.tl(PM.Fd(2n, m, r), PM.Fd(3n, m, r), Con{PM.Fd(3n, m, r), Con{PM.Fd(4n, m, r), Nil{}}}, mem.hd(PM.Fd(3n, m, r), Con{PM.Fd(4n, m, r), Nil{}})), hz0, hzs), hb)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(PM.Node(a, m, PM.Fd(2n, m, r), c), Bool.or(_, PM.Node(d, Cr.Cir.Cells.set(m, z, x), PM.Fd(4n, m, r), c)))) == Bool.or(U32.is_eq(r, c), Bool.or(PM.Node(a, m, PM.Fd(2n, m, r), c), Bool.or(PM.Node(b, m, PM.Fd(3n, m, r), c), PM.Node(d, m, PM.Fd(4n, m, r), c)))) : Bool}
      %Equal.sym(Bool, PM.Node(d, Cr.Cir.Cells.set(m, z, x), PM.Fd(4n, m, r), c), PM.Node(d, m, PM.Fd(4n, m, r), c),
        Node.fz(d, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(4n, m, r), c, tbl, hz0, hzs,
          part.ne(m, nx, fi, ps, rs, r, PM.Fd(4n, m, r), z, 16, 7, spd, nd.tg(ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Eql{a, b, d}, 16, nd), {==},
            tbl.mask(m, im, fi, nx, Bk.Term.Eql{a, b, d}, tbl), mem.tl(PM.Fd(2n, m, r), PM.Fd(4n, m, r), Con{PM.Fd(3n, m, r), Con{PM.Fd(4n, m, r), Nil{}}}, mem.tl(PM.Fd(3n, m, r), PM.Fd(4n, m, r), Con{PM.Fd(4n, m, r), Nil{}}, mem.hd(PM.Fd(4n, m, r), Nil{}))), hz0, hzs), hd)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(PM.Node(a, m, PM.Fd(2n, m, r), c), Bool.or(PM.Node(b, m, PM.Fd(3n, m, r), c), _))) == Bool.or(U32.is_eq(r, c), Bool.or(PM.Node(a, m, PM.Fd(2n, m, r), c), Bool.or(PM.Node(b, m, PM.Fd(3n, m, r), c), PM.Node(d, m, PM.Fd(4n, m, r), c)))) : Bool}
      {==}
    case Bk.Term.Rwt{+a, +b, +d}:
      (+nd, rr) = h
      (pa, r2) = rr
      (spa, ha) = pa
      (pb, pd) = r2
      (spb, hb) = pb
      (spd, hd) = pd
      +ec = PM.cl.go(m, r, z, x, hr)
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, x), r), Cr.Cir.Cells.get(m, r), ec) :
        {Bool.or(U32.is_eq(r, c), Bool.or(PM.Node(a, Cr.Cir.Cells.set(m, z, x), Cr.Cir.Cell.get(2n, _), c), Bool.or(PM.Node(b, Cr.Cir.Cells.set(m, z, x), Cr.Cir.Cell.get(3n, _), c), PM.Node(d, Cr.Cir.Cells.set(m, z, x), Cr.Cir.Cell.get(4n, _), c)))) == Bool.or(U32.is_eq(r, c), Bool.or(PM.Node(a, m, PM.Fd(2n, m, r), c), Bool.or(PM.Node(b, m, PM.Fd(3n, m, r), c), PM.Node(d, m, PM.Fd(4n, m, r), c)))) : Bool}
      %Equal.sym(Bool, PM.Node(a, Cr.Cir.Cells.set(m, z, x), PM.Fd(2n, m, r), c), PM.Node(a, m, PM.Fd(2n, m, r), c),
        Node.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(2n, m, r), c, tbl, hz0, hzs,
          part.ne(m, nx, fi, ps, rs, r, PM.Fd(2n, m, r), z, 18, 7, spa, nd.tg(ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Rwt{a, b, d}, 18, nd), {==},
            tbl.mask(m, im, fi, nx, Bk.Term.Rwt{a, b, d}, tbl), mem.hd(PM.Fd(2n, m, r), Con{PM.Fd(3n, m, r), Con{PM.Fd(4n, m, r), Nil{}}}), hz0, hzs), ha)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(_, Bool.or(PM.Node(b, Cr.Cir.Cells.set(m, z, x), PM.Fd(3n, m, r), c), PM.Node(d, Cr.Cir.Cells.set(m, z, x), PM.Fd(4n, m, r), c)))) == Bool.or(U32.is_eq(r, c), Bool.or(PM.Node(a, m, PM.Fd(2n, m, r), c), Bool.or(PM.Node(b, m, PM.Fd(3n, m, r), c), PM.Node(d, m, PM.Fd(4n, m, r), c)))) : Bool}
      %Equal.sym(Bool, PM.Node(b, Cr.Cir.Cells.set(m, z, x), PM.Fd(3n, m, r), c), PM.Node(b, m, PM.Fd(3n, m, r), c),
        Node.fz(b, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(3n, m, r), c, tbl, hz0, hzs,
          part.ne(m, nx, fi, ps, rs, r, PM.Fd(3n, m, r), z, 18, 7, spb, nd.tg(ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Rwt{a, b, d}, 18, nd), {==},
            tbl.mask(m, im, fi, nx, Bk.Term.Rwt{a, b, d}, tbl), mem.tl(PM.Fd(2n, m, r), PM.Fd(3n, m, r), Con{PM.Fd(3n, m, r), Con{PM.Fd(4n, m, r), Nil{}}}, mem.hd(PM.Fd(3n, m, r), Con{PM.Fd(4n, m, r), Nil{}})), hz0, hzs), hb)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(PM.Node(a, m, PM.Fd(2n, m, r), c), Bool.or(_, PM.Node(d, Cr.Cir.Cells.set(m, z, x), PM.Fd(4n, m, r), c)))) == Bool.or(U32.is_eq(r, c), Bool.or(PM.Node(a, m, PM.Fd(2n, m, r), c), Bool.or(PM.Node(b, m, PM.Fd(3n, m, r), c), PM.Node(d, m, PM.Fd(4n, m, r), c)))) : Bool}
      %Equal.sym(Bool, PM.Node(d, Cr.Cir.Cells.set(m, z, x), PM.Fd(4n, m, r), c), PM.Node(d, m, PM.Fd(4n, m, r), c),
        Node.fz(d, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(4n, m, r), c, tbl, hz0, hzs,
          part.ne(m, nx, fi, ps, rs, r, PM.Fd(4n, m, r), z, 18, 7, spd, nd.tg(ds, im, fi, nx, r, Cr.Cir.Cells.get(m, r), Bk.Term.Rwt{a, b, d}, 18, nd), {==},
            tbl.mask(m, im, fi, nx, Bk.Term.Rwt{a, b, d}, tbl), mem.tl(PM.Fd(2n, m, r), PM.Fd(4n, m, r), Con{PM.Fd(3n, m, r), Con{PM.Fd(4n, m, r), Nil{}}}, mem.tl(PM.Fd(3n, m, r), PM.Fd(4n, m, r), Con{PM.Fd(4n, m, r), Nil{}}, mem.hd(PM.Fd(4n, m, r), Nil{}))), hz0, hzs), hd)) :
        {Bool.or(U32.is_eq(r, c), Bool.or(PM.Node(a, m, PM.Fd(2n, m, r), c), Bool.or(PM.Node(b, m, PM.Fd(3n, m, r), c), _))) == Bool.or(U32.is_eq(r, c), Bool.or(PM.Node(a, m, PM.Fd(2n, m, r), c), Bool.or(PM.Node(b, m, PM.Fd(3n, m, r), c), PM.Node(d, m, PM.Fd(4n, m, r), c)))) : Bool}
      {==}

# A store to a cell that nothing points to: the terms
# --------------------------------------------------

# no cell of cs is z
def NeAll(cs: List<&2, U32>, +z: U32) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{c, rest}:
      Bool.not(U32.is_eq(c, z)) && NeAll(rest, z)

def neall.hd(+c: U32, +z: U32, -rest: List<&2, U32>, h: {NeAll(Con{c, rest}, z) == True{} : Bool}) -> {U32.is_eq(c, z) == False{} : Bool}:
  not.t(U32.is_eq(c, z), and.l(Bool.not(U32.is_eq(c, z)), NeAll(rest, z), h))

def neall.tl(+c: U32, +z: U32, -rest: List<&2, U32>, h: {NeAll(Con{c, rest}, z) == True{} : Bool}) -> {NeAll(rest, z) == True{} : Bool}:
  and.r(Bool.not(U32.is_eq(c, z)), NeAll(rest, z), h)

def neall.cons(+c: U32, +z: U32, -rest: List<&2, U32>, ne: {U32.is_eq(c, z) == False{} : Bool}, h: {NeAll(rest, z) == True{} : Bool}) ->
  {NeAll(Con{c, rest}, z) == True{} : Bool}:
  %Equal.sym(Bool, U32.is_eq(c, z), False{}, ne) : {Bool.and(Bool.not(_), NeAll(rest, z)) == True{} : Bool}
  h

# no root is z, when no root points to z
def neall.rcl(rs: List<&2, U32>, +z: U32, h: {PM.RcL(rs, z) == 0n : Nat}) -> {NeAll(rs, z) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case Con{+r, +rest}:
      +h2 = h
      neall.cons(r, z, rest, of.z(U32.is_eq(r, z), PM.RcL(rest, z), h2),
        neall.rcl(rest, z, add0.r(PM.Nat.of(U32.is_eq(r, z)), PM.RcL(rest, z), h2)))

def lt0.le1(p: Nat, h: {Nat.is_lt(0n, p) == True{} : Bool}) -> N.Le(1n, p):
  match p:
    case 0n:
      PM.bool.ft(N.Le(1n, 0n), h)
    case 1n+q:
      N.le_zero(q)

# a node of an owned root's term is not z
def nodes.ne(os: List<&2, PM.Rt>, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +rs: List<&2, U32>, +z: U32, +c: U32, +tbl: PM.Tbl(m, im, fi, nx),
  +hz0: {PM.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, rs, z) == 0n : Nat}, +hzs: {PM.Fl(m, z, 1024) == False{} : Bool},
  hn: {NeAll(PM.Rt.cells(os), z) == True{} : Bool}, ho: PM.Rts(ds, m, im, fi, nx, ks, img, os), h: {PM.Nodes(os, m, c) == True{} : Bool}) ->
  {U32.is_eq(c, z) == False{} : Bool}:
  match os:
    case Nil{}:
      PM.bool.ft({U32.is_eq(c, z) == False{} : Bool}, h)
    case Con{PM.Rt{+r, +u}, +rest}:
      (hu, hr) = ho
      +hn2 = hn
      node.or2(PM.Node(u, m, r, c), PM.Nodes(rest, m, c), {U32.is_eq(c, z) == False{} : Bool}, h,
        e => node.ne(u, ds, m, im, fi, nx, ks, img, ps, rs, z, r, c, tbl, hz0, hzs, neall.hd(r, z, PM.Rt.cells(rest), hn2), hu, e),
        e => nodes.ne(rest, ds, m, im, fi, nx, ks, img, ps, rs, z, c, tbl, hz0, hzs, neall.tl(r, z, PM.Rt.cells(rest), hn2), hr, e))

def held.ne(f: Bool, +os: List<&2, PM.Rt>, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +rs: List<&2, U32>, +z: U32, +c: U32, +tbl: PM.Tbl(m, im, fi, nx),
  +hz0: {PM.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, rs, z) == 0n : Nat}, +hzs: {PM.Fl(m, z, 1024) == False{} : Bool},
  hn: {NeAll(PM.Rt.cells(os), z) == True{} : Bool}, ho: PM.Rts(ds, m, im, fi, nx, ks, img, os),
  ef: {PM.Fl(m, c, 1024) == f : Bool}, h: {Bool.or(f, PM.Nodes(os, m, c)) == True{} : Bool}) -> {U32.is_eq(c, z) == False{} : Bool}:
  match f:
    case True{}:
      ne.st(U32.is_eq(c, z), m, c, z, {==}, ef, hzs)
    case False{}:
      nodes.ne(os, ds, m, im, fi, nx, ks, img, ps, rs, z, c, tbl, hz0, hzs, hn, ho, h)

# no borrowed cell is z, which is not STATIC and has no pointer
def neall.held(bs: List<&2, PM.Rt>, +os: List<&2, PM.Rt>, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +rs: List<&2, U32>, +z: U32, +tbl: PM.Tbl(m, im, fi, nx),
  +hz0: {PM.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, rs, z) == 0n : Nat}, +hzs: {PM.Fl(m, z, 1024) == False{} : Bool},
  +hn: {NeAll(PM.Rt.cells(os), z) == True{} : Bool}, +ho: PM.Rts(ds, m, im, fi, nx, ks, img, os), h: PM.Held(m, os, bs)) ->
  {NeAll(PM.Rt.cells(bs), z) == True{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case Con{PM.Rt{+c, _}, +rest}:
      (hh, hr) = h
      neall.cons(c, z, PM.Rt.cells(rest), held.ne(PM.Fl(m, c, 1024), os, ds, m, im, fi, nx, ks, img, ps, rs, z, c, tbl, hz0, hzs, hn, ho, {==}, hh),
        neall.held(rest, os, ds, m, im, fi, nx, ks, img, ps, rs, z, tbl, hz0, hzs, hn, ho, hr))

# a store to z keeps the nodes of the owned roots' terms
def Nodes.fz(os: List<&2, PM.Rt>, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +rs: List<&2, U32>, +z: U32, +x: Cr.Cir.Cell, +c: U32, +tbl: PM.Tbl(m, im, fi, nx),
  +hz0: {PM.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, rs, z) == 0n : Nat}, +hzs: {PM.Fl(m, z, 1024) == False{} : Bool},
  hn: {NeAll(PM.Rt.cells(os), z) == True{} : Bool}, ho: PM.Rts(ds, m, im, fi, nx, ks, img, os)) ->
  {PM.Nodes(os, Cr.Cir.Cells.set(m, z, x), c) == PM.Nodes(os, m, c) : Bool}:
  match os:
    case Nil{}:
      {==}
    case Con{PM.Rt{+r, +u}, +rest}:
      (hu, hr) = ho
      +hn2 = hn
      %Equal.sym(Bool, PM.Node(u, Cr.Cir.Cells.set(m, z, x), r, c), PM.Node(u, m, r, c),
        Node.fz(u, ds, m, im, fi, nx, ks, img, ps, rs, z, x, r, c, tbl, hz0, hzs, neall.hd(r, z, PM.Rt.cells(rest), hn2), hu)) :
        {Bool.or(_, PM.Nodes(rest, Cr.Cir.Cells.set(m, z, x), c)) == Bool.or(PM.Node(u, m, r, c), PM.Nodes(rest, m, c)) : Bool}
      %Equal.sym(Bool, PM.Nodes(rest, Cr.Cir.Cells.set(m, z, x), c), PM.Nodes(rest, m, c),
        Nodes.fz(rest, ds, m, im, fi, nx, ks, img, ps, rs, z, x, c, tbl, hz0, hzs, neall.tl(r, z, PM.Rt.cells(rest), hn2), hr)) :
        {Bool.or(PM.Node(u, m, r, c), _) == Bool.or(PM.Node(u, m, r, c), PM.Nodes(rest, m, c)) : Bool}
      {==}

# a store to z keeps the terms of cells that are not z
def Rts.fz(xs: List<&2, PM.Rt>, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +rs: List<&2, U32>, +z: U32, +x: Cr.Cir.Cell, +tbl: PM.Tbl(m, im, fi, nx),
  +hz0: {PM.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, rs, z) == 0n : Nat}, +hzs: {PM.Fl(m, z, 1024) == False{} : Bool},
  hn: {NeAll(PM.Rt.cells(xs), z) == True{} : Bool}, h: PM.Rts(ds, m, im, fi, nx, ks, img, xs)) ->
  PM.Rts(ds, Cr.Cir.Cells.set(m, z, x), im, fi, nx, ks, img, xs):
  match xs:
    case Nil{}:
      Unit{}
    case Con{PM.Rt{+c, +u}, +rest}:
      (hc, hr) = h
      +hn2 = hn
      (is.fz(u, ds, m, im, fi, nx, ks, img, ps, rs, z, x, c, tbl, hz0, hzs, neall.hd(c, z, PM.Rt.cells(rest), hn2), hc),
        Rts.fz(rest, ds, m, im, fi, nx, ks, img, ps, rs, z, x, tbl, hz0, hzs, neall.tl(c, z, PM.Rt.cells(rest), hn2), hr))

# a store to z keeps Held
def Held.fz(bs: List<&2, PM.Rt>, +os: List<&2, PM.Rt>, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +rs: List<&2, U32>, +z: U32, +x: Cr.Cir.Cell,
  +tbl: PM.Tbl(m, im, fi, nx), +hz0: {PM.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, rs, z) == 0n : Nat},
  +hzs: {PM.Fl(m, z, 1024) == False{} : Bool}, +hno: {NeAll(PM.Rt.cells(os), z) == True{} : Bool}, +ho: PM.Rts(ds, m, im, fi, nx, ks, img, os),
  hn: {NeAll(PM.Rt.cells(bs), z) == True{} : Bool}, h: PM.Held(m, os, bs)) -> PM.Held(Cr.Cir.Cells.set(m, z, x), os, bs):
  match bs:
    case Nil{}:
      Unit{}
    case Con{PM.Rt{+c, _}, +rest}:
      (hh, hr) = h
      +hn2 = hn
      +M2 = Cr.Cir.Cells.set(m, z, x)
      ((%Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M2, c), Cr.Cir.Cells.get(m, c), PM.cl.go(m, c, z, x, neall.hd(c, z, PM.Rt.cells(rest), hn2))) :
          {Bool.or(U32.is_ne(U32.and(Cr.Cir.Cell.get(0n, _), 1024), 0), PM.Nodes(os, M2, c)) == True{} : Bool};
        %Equal.sym(Bool, PM.Nodes(os, M2, c), PM.Nodes(os, m, c), Nodes.fz(os, ds, m, im, fi, nx, ks, img, ps, rs, z, x, c, tbl, hz0, hzs, hno, ho)) :
          {Bool.or(PM.Fl(m, c, 1024), _) == True{} : Bool};
        hh),
        Held.fz(rest, os, ds, m, im, fi, nx, ks, img, ps, rs, z, x, tbl, hz0, hzs, hno, ho, neall.tl(c, z, PM.Rt.cells(rest), hn2), hr))

# Fs of a frame, past the test of its tag
def FsR(c: Bool, +m: Cr.Cir.Cells, +ps: List<&2, U32>, +o: U32, +tg: U32) -> List<&2, U32>:
  Bool.pick(List<&2, U32>, c, Con{PM.Fd(2n, m, o), PM.Fs.opt(U32.is_eq(tg, 38), PM.Fd(3n, m, o), Nil{})},
    Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_eq(tg, 41), PM.FlW(PM.Fd(0n, m, o), 4096)), Bool.not(PM.Mem(ps, o))),
      [PM.Fd(2n, m, o)], Nil{}))

# the pointers of a frame out of the pend list: its field 2, and 3 for Rwt
def fs.frame(+m: Cr.Cir.Cells, +ps: List<&2, U32>, +o: U32, +tg: U32, etag: {PM.TgW(PM.Fd(0n, m, o)) == tg : U32},
  hlt: {U32.is_lt(tg, 19) == False{} : Bool}, hge: {U32.is_le(32, tg) == True{} : Bool}, hle: {U32.is_le(tg, 40) == True{} : Bool},
  hm: {PM.Mem(ps, o) == False{} : Bool}) ->
  {PM.Fs(m, ps, o) == Con{PM.Fd(2n, m, o), PM.Fs.opt(U32.is_eq(tg, 38), PM.Fd(3n, m, o), Nil{})} : List<&2, U32>}:
  +R = {Con{PM.Fd(2n, m, o), PM.Fs.opt(U32.is_eq(tg, 38), PM.Fd(3n, m, o), Nil{})} : List<&2, U32>}
  %Equal.sym(U32, PM.TgW(PM.Fd(0n, m, o)), tg, etag) : {FsP(U32.is_lt(_, 19), m, ps, o, _) == R : List<&2, U32>}
  %Equal.sym(Bool, U32.is_lt(tg, 19), False{}, hlt) : {FsP(_, m, ps, o, tg) == R : List<&2, U32>}
  %Equal.sym(Bool, U32.is_le(32, tg), True{}, hge) : {FsR(Bool.and(Bool.and(_, U32.is_le(tg, 40)), Bool.not(PM.Mem(ps, o))), m, ps, o, tg) == R : List<&2, U32>}
  %Equal.sym(Bool, U32.is_le(tg, 40), True{}, hle) : {FsR(Bool.and(Bool.and(True{}, _), Bool.not(PM.Mem(ps, o))), m, ps, o, tg) == R : List<&2, U32>}
  %Equal.sym(Bool, PM.Mem(ps, o), False{}, hm) : {FsR(Bool.not(_), m, ps, o, tg) == R : List<&2, U32>}
  {==}

def fk.lt(kind: PM.FK) -> {U32.is_lt(PM.FK.tag(kind), 19) == False{} : Bool}:
  match kind:
    case PM.FK.arg{}:
      {==}
    case PM.FK.val{}:
      {==}
    case PM.FK.fun{}:
      {==}
    case PM.FK.let{}:
      {==}
    case PM.FK.tupb{}:
      {==}
    case PM.FK.tupa{}:
      {==}
    case PM.FK.rwt{}:
      {==}
    case PM.FK.minb{}:
      {==}
    case PM.FK.mina{}:
      {==}

def fk.ge(kind: PM.FK) -> {U32.is_le(32, PM.FK.tag(kind)) == True{} : Bool}:
  match kind:
    case PM.FK.arg{}:
      {==}
    case PM.FK.val{}:
      {==}
    case PM.FK.fun{}:
      {==}
    case PM.FK.let{}:
      {==}
    case PM.FK.tupb{}:
      {==}
    case PM.FK.tupa{}:
      {==}
    case PM.FK.rwt{}:
      {==}
    case PM.FK.minb{}:
      {==}
    case PM.FK.mina{}:
      {==}

def fk.le(kind: PM.FK) -> {U32.is_le(PM.FK.tag(kind), 40) == True{} : Bool}:
  match kind:
    case PM.FK.arg{}:
      {==}
    case PM.FK.val{}:
      {==}
    case PM.FK.fun{}:
      {==}
    case PM.FK.let{}:
      {==}
    case PM.FK.tupb{}:
      {==}
    case PM.FK.tupa{}:
      {==}
    case PM.FK.rwt{}:
      {==}
    case PM.FK.minb{}:
      {==}
    case PM.FK.mina{}:
      {==}

# a part y of a frame fr is not z, which has no pointer
def fr.ne(+m: Cr.Cir.Cells, +nx: U32, +fi: U32, +ps: List<&2, U32>, +rs: List<&2, U32>, +fr: U32, +y: U32, +z: U32, +tg: U32,
  etag: {PM.TgW(PM.Fd(0n, m, fr)) == tg : U32}, hlt: {U32.is_lt(tg, 19) == False{} : Bool}, hge: {U32.is_le(32, tg) == True{} : Bool},
  hle: {U32.is_le(tg, 40) == True{} : Bool}, em: {PM.Mem(ps, fr) == False{} : Bool}, own: {PM.Own(fi, nx, fr) == True{} : Bool},
  hy: {PM.Mem(Con{PM.Fd(2n, m, fr), PM.Fs.opt(U32.is_eq(tg, 38), PM.Fd(3n, m, fr), Nil{})}, y) == True{} : Bool},
  hz0: {PM.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, rs, z) == 0n : Nat}) -> {U32.is_eq(y, z) == False{} : Bool}:
  +L = {Con{PM.Fd(2n, m, fr), PM.Fs.opt(U32.is_eq(tg, 38), PM.Fd(3n, m, fr), Nil{})} : List<&2, U32>}
  +e = fs.frame(m, ps, fr, tg, etag, hlt, hge, hle, em)
  ne.ptr(U32.is_eq(y, z), y, z, Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, rs, {==},
    N.le_trans(1n, PM.RcL(PM.Fs(m, ps, fr), y), PM.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, rs, y),
      (%Equal.sym(List<&2, U32>, PM.Fs(m, ps, fr), L, e) : N.Le(1n, PM.RcL(_, y)); rcl.mem(L, y, hy)),
      Ptr.at(m, nx, fi, ps, rs, fr, y, own)), hz0)

# the part b of a frame, after a store to z
def Frs.b.fz(kind: PM.FK, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +rs: List<&2, U32>, +z: U32, +x: Cr.Cir.Cell, +fr: U32, +b: Bk.Term,
  +tbl: PM.Tbl(m, im, fi, nx), +hz0: {PM.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, rs, z) == 0n : Nat},
  +hzs: {PM.Fl(m, z, 1024) == False{} : Bool}, etag: {PM.TgW(PM.Fd(0n, m, fr)) == PM.FK.tag(kind) : U32},
  em: {PM.Mem(ps, fr) == False{} : Bool}, own: {PM.Own(fi, nx, fr) == True{} : Bool},
  h: PM.Frs.b(ds, m, im, fi, nx, ks, img, PM.Fd(3n, m, fr), kind, b)) ->
  PM.Frs.b(ds, Cr.Cir.Cells.set(m, z, x), im, fi, nx, ks, img, PM.Fd(3n, m, fr), kind, b):
  match kind:
    case PM.FK.rwt{}:
      is.fz(b, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(3n, m, fr), tbl, hz0, hzs,
        fr.ne(m, nx, fi, ps, rs, fr, PM.Fd(3n, m, fr), z, 38, etag, {==}, {==}, {==}, em, own,
          mem.tl(PM.Fd(2n, m, fr), PM.Fd(3n, m, fr), Con{PM.Fd(3n, m, fr), Nil{}}, mem.hd(PM.Fd(3n, m, fr), Nil{})), hz0), h)
    case PM.FK.arg{}:
      Unit{}
    case PM.FK.val{}:
      Unit{}
    case PM.FK.fun{}:
      Unit{}
    case PM.FK.let{}:
      Unit{}
    case PM.FK.tupb{}:
      Unit{}
    case PM.FK.tupa{}:
      Unit{}
    case PM.FK.minb{}:
      Unit{}
    case PM.FK.mina{}:
      Unit{}

# a store to z, a cell of a tag below 32 with no pointer, keeps the frames
def Frs.fz(fs: List<&2, PM.AF>, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +rs: List<&2, U32>, +z: U32, +x: Cr.Cir.Cell, +fr: U32,
  +tbl: PM.Tbl(m, im, fi, nx), +hz0: {PM.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, rs, z) == 0n : Nat},
  +hzs: {PM.Fl(m, z, 1024) == False{} : Bool}, +hzt: {U32.is_lt(PM.TgW(PM.Fd(0n, m, z)), 32) == True{} : Bool},
  h: PM.Frs(ds, m, im, fi, nx, ks, img, ps, fr, fs)) -> PM.Frs(ds, Cr.Cir.Cells.set(m, z, x), im, fi, nx, ks, img, ps, fr, fs):
  match fs:
    case Nil{}:
      h
    case Con{PM.AF{+kind, +q, +k, +a, +b}, +rest}:
      match h:
        case Tuple{e0, Tuple{ev, Tuple{+eo, Tuple{es, Tuple{+em, Tuple{+etg, Tuple{eq, Tuple{ek, Tuple{ia, Tuple{ib, ir}}}}}}}}}}:
          +M2 = Cr.Cir.Cells.set(m, z, x)
          +ne = PM.ne.fr(U32.is_eq(fr, z), m, fr, z, kind, {==}, etg, hzt)
          PM.frs.uc(ds, M2, im, fi, nx, ks, img, ps, fr, Con{PM.AF{kind, q, k, a, b}, rest},
            PM.frsc.at(ds, M2, im, fi, nx, ks, img, ps, fr, Cr.Cir.Cells.get(M2, fr), Cr.Cir.Cells.get(m, fr), Con{PM.AF{kind, q, k, a, b}, rest},
              PM.cl.go(m, fr, z, x, ne),
              (e0, (ev, (eo, (es, (em, (etg, (eq, (ek,
                (is.fz(a, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(2n, m, fr), tbl, hz0, hzs,
                  fr.ne(m, nx, fi, ps, rs, fr, PM.Fd(2n, m, fr), z, PM.FK.tag(kind), etg, fk.lt(kind), fk.ge(kind), fk.le(kind), em, eo,
                    mem.hd(PM.Fd(2n, m, fr), PM.Fs.opt(U32.is_eq(PM.FK.tag(kind), 38), PM.Fd(3n, m, fr), Nil{})), hz0), ia),
                (Frs.b.fz(kind, ds, m, im, fi, nx, ks, img, ps, rs, z, x, fr, b, tbl, hz0, hzs, etg, em, eo, ib),
                  Frs.fz(rest, ds, m, im, fi, nx, ks, img, ps, rs, z, x, PM.Fd(1n, m, fr), tbl, hz0, hzs, hzt, ir)))))))))))))

# The image, after a store to a cell of the machine's own
# -------------------------------------------------------

# the cells from at, one for each of cs, are at most 290
def TblB(cs: List<&2, Cr.Cir.Cell>, +at: U32) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{_, rest}:
      Bool.and(U32.is_le(at, 290), TblB(rest, U32.inc(at)))

# a cell at most bd is not z, past bd
def lit.ne(b: Bool, +l: U32, +z: U32, +bd: U32, eb: {U32.is_eq(l, z) == b : Bool}, hl: {U32.is_le(l, bd) == True{} : Bool},
  hz: N.Le(1n+U32.to_nat(bd), U32.to_nat(z))) -> {U32.is_eq(l, z) == False{} : Bool}:
  match b:
    case False{}:
      eb
    case True{}:
      +e = PM.u32.eq(l, z, eb)
      Empty.absurd({U32.is_eq(l, z) == False{} : Bool}, N.not_succ_le(U32.to_nat(bd), N.le_trans(1n+U32.to_nat(bd), U32.to_nat(z), U32.to_nat(bd), hz,
        N.le_rw_l(U32.to_nat(l), U32.to_nat(z), U32.to_nat(bd), Equal.cong(U32, Nat, w => U32.to_nat(w), l, z, e), u.le(l, bd, hl)))))

def Tbl.fz(cs: List<&2, Cr.Cir.Cell>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +z: U32, +x: Cr.Cir.Cell, +at: U32,
  +hz: N.Le(1n+U32.to_nat(290), U32.to_nat(z)), hb: {TblB(cs, at) == True{} : Bool}, h: PM.Tbl.go(cs, m, im, fi, nx, at)) ->
  PM.Tbl.go(cs, Cr.Cir.Cells.set(m, z, x), im, fi, nx, at):
  match cs:
    case Nil{}:
      Unit{}
    case Con{+c, +rest}:
      (ec, r1) = h
      (e, r2) = r1
      +hb2 = hb
      +ne = lit.ne(U32.is_eq(at, z), at, z, 290, {==}, and.l(U32.is_le(at, 290), TblB(rest, U32.inc(at)), hb2), hz)
      (ec, (Equal.trans(Cr.Cir.Cell, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, x), at), Cr.Cir.Cells.get(m, at), c, PM.cl.go(m, at, z, x, ne), e),
        Tbl.fz(rest, m, im, fi, nx, z, x, U32.inc(at), hz, and.r(U32.is_le(at, 290), TblB(rest, U32.inc(at)), hb2), r2)))

def Defs.fz(dl: List<&2, Bk.Def>, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +rs: List<&2, U32>, +z: U32, +x: Cr.Cir.Cell, +at: U32, +tbl: PM.Tbl(m, im, fi, nx),
  +hz0: {PM.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, rs, z) == 0n : Nat}, +hzs: {PM.Fl(m, z, 1024) == False{} : Bool},
  +hzi: N.Le(1n+U32.to_nat(im), U32.to_nat(z)), h: PM.Defs(dl, ds, m, im, fi, nx, ks, img, at)) ->
  PM.Defs(dl, ds, Cr.Cir.Cells.set(m, z, x), im, fi, nx, ks, img, at):
  match dl:
    case Nil{}:
      Unit{}
    case Con{Bk.Def{_, _, +v, _}, +rest}:
      (e0, r1) = h
      (ele, r2) = r1
      (hv, r3) = r2
      +ele2 = {ele : {U32.is_le(at, im) == True{} : Bool}}
      (e0, (ele2, (is.fz(v, ds, m, im, fi, nx, ks, img, ps, rs, z, x, at, tbl, hz0, hzs, lit.ne(U32.is_eq(at, z), at, z, im, {==}, ele2, hzi), hv),
        Defs.fz(rest, ds, m, im, fi, nx, ks, img, ps, rs, z, x, U32.add(at, Mc.Img.size(v)), tbl, hz0, hzs, hzi, r3))))

# a store to z, one of the machine's own cells, keeps the image
def ImgOK.fz(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ps: List<&2, U32>, +rs: List<&2, U32>, +z: U32, +x: Cr.Cir.Cell,
  +hz0: {PM.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, rs, z) == 0n : Nat}, +hzs: {PM.Fl(m, z, 1024) == False{} : Bool},
  hzo: {PM.Own(fi, nx, z) == True{} : Bool},
  h: PM.ImgOK(ds, ks, img, m, im, fi, nx)) -> PM.ImgOK(ds, ks, img, Cr.Cir.Cells.set(m, z, x), im, fi, nx):
  (+tbl, r1) = h
  (hd, r2) = r1
  (h8, r3) = r2
  (h9, r4) = r3
  (h10, r5) = r4
  (hks, r6) = r5
  (e290a, eima) = r6
  +e290 = {e290a : {U32.is_le(290, im) == True{} : Bool}}
  +eim = {eima : {U32.is_lt(im, fi) == True{} : Bool}}
  +hzi = N.le_trans(1n+U32.to_nat(im), U32.to_nat(fi), U32.to_nat(z), u.lt(im, fi, eim), u.le(fi, z, and.l(U32.is_le(fi, z), U32.is_lt(z, nx), hzo)))
  +hz = N.le_trans(1n+U32.to_nat(290), 1n+U32.to_nat(im), U32.to_nat(z), u.le(290, im, e290), hzi)
  (Tbl.fz(Mc.Img.table([]), m, im, fi, nx, z, x, 272, hz, {==}, tbl),
    (Defs.fz(ds, ds, m, im, fi, nx, ks, img, ps, rs, z, x, Mc.I.book(), tbl, hz0, hzs, hzi, hd),
    (is.fz(Bk.Term.Lab{El.Quan.name(Bk.Quan.Q0{})}, ds, m, im, fi, nx, ks, img, ps, rs, z, x, 8, tbl, hz0, hzs, lit.ne(U32.is_eq(8, z), 8, z, 290, {==}, {==}, hz), h8),
    (is.fz(Bk.Term.Lab{El.Quan.name(Bk.Quan.Q1{})}, ds, m, im, fi, nx, ks, img, ps, rs, z, x, 9, tbl, hz0, hzs, lit.ne(U32.is_eq(9, z), 9, z, 290, {==}, {==}, hz), h9),
    (is.fz(Bk.Term.Lab{El.Quan.name(Bk.Quan.Q2{})}, ds, m, im, fi, nx, ks, img, ps, rs, z, x, 10, tbl, hz0, hzs, lit.ne(U32.is_eq(10, z), 10, z, 290, {==}, {==}, hz), h10),
    (hks, (e290, eim)))))))

# the table, of the image
def img.tbl(-ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -m: Cr.Cir.Cells, -im: U32,
  -fi: U32, -nx: U32, io: PM.ImgOK(ds, ks, img, m, im, fi, nx)) -> PM.Tbl(m, im, fi, nx):
  (tb, r) = io
  tb

# a tag below 19 reads its mask in the table, at most cell 290
def rel.eqt(c: Cmp, +x: Nat, +y: Nat, r: N.Rel(c, x, y), e: {x == y : Nat}) -> {Cmp.is_eq(c) == True{} : Bool}:
  match c:
    case LT{}:
      Empty.absurd({False{} == True{} : Bool}, N.not_succ_le(y, (%e : N.Le(1n+_, y); r)))
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({False{} == True{} : Bool}, N.not_succ_le(y, (%e : N.Le(1n+y, _); r)))

# U32s of the same number are equal, as is_eq says
def u.nat.eq(+a: U32, +b: U32, e: {U32.to_nat(a) == U32.to_nat(b) : Nat}) -> {U32.is_eq(a, b) == True{} : Bool}:
  rel.eqt(U32.cmp(a, b), U32.to_nat(a), U32.to_nat(b), N.U32.rel(a, b), e)

def tbl.small.at(n0: Nat, +tg: U32, en: {U32.to_nat(tg) == n0 : Nat}, h: N.Le(1n+n0, 19n)) ->
  {U32.is_le(U32.add(272, tg), 290) == True{} : Bool}:
  match n0:
    case 0n:
      %Equal.sym(U32, tg, 0, PM.u32.eq(tg, 0, u.nat.eq(tg, 0, en))) : {U32.is_le(U32.add(272, _), 290) == True{} : Bool}
      {==}
    case 1n+n1:
      match n1:
        case 0n:
          %Equal.sym(U32, tg, 1, PM.u32.eq(tg, 1, u.nat.eq(tg, 1, en))) : {U32.is_le(U32.add(272, _), 290) == True{} : Bool}
          {==}
        case 1n+n2:
          match n2:
            case 0n:
              %Equal.sym(U32, tg, 2, PM.u32.eq(tg, 2, u.nat.eq(tg, 2, en))) : {U32.is_le(U32.add(272, _), 290) == True{} : Bool}
              {==}
            case 1n+n3:
              match n3:
                case 0n:
                  %Equal.sym(U32, tg, 3, PM.u32.eq(tg, 3, u.nat.eq(tg, 3, en))) : {U32.is_le(U32.add(272, _), 290) == True{} : Bool}
                  {==}
                case 1n+n4:
                  match n4:
                    case 0n:
                      %Equal.sym(U32, tg, 4, PM.u32.eq(tg, 4, u.nat.eq(tg, 4, en))) : {U32.is_le(U32.add(272, _), 290) == True{} : Bool}
                      {==}
                    case 1n+n5:
                      match n5:
                        case 0n:
                          %Equal.sym(U32, tg, 5, PM.u32.eq(tg, 5, u.nat.eq(tg, 5, en))) : {U32.is_le(U32.add(272, _), 290) == True{} : Bool}
                          {==}
                        case 1n+n6:
                          match n6:
                            case 0n:
                              %Equal.sym(U32, tg, 6, PM.u32.eq(tg, 6, u.nat.eq(tg, 6, en))) : {U32.is_le(U32.add(272, _), 290) == True{} : Bool}
                              {==}
                            case 1n+n7:
                              match n7:
                                case 0n:
                                  %Equal.sym(U32, tg, 7, PM.u32.eq(tg, 7, u.nat.eq(tg, 7, en))) : {U32.is_le(U32.add(272, _), 290) == True{} : Bool}
                                  {==}
                                case 1n+n8:
                                  match n8:
                                    case 0n:
                                      %Equal.sym(U32, tg, 8, PM.u32.eq(tg, 8, u.nat.eq(tg, 8, en))) : {U32.is_le(U32.add(272, _), 290) == True{} : Bool}
                                      {==}
                                    case 1n+n9:
                                      match n9:
                                        case 0n:
                                          %Equal.sym(U32, tg, 9, PM.u32.eq(tg, 9, u.nat.eq(tg, 9, en))) : {U32.is_le(U32.add(272, _), 290) == True{} : Bool}
                                          {==}
                                        case 1n+n10:
                                          match n10:
                                            case 0n:
                                              %Equal.sym(U32, tg, 10, PM.u32.eq(tg, 10, u.nat.eq(tg, 10, en))) : {U32.is_le(U32.add(272, _), 290) == True{} : Bool}
                                              {==}
                                            case 1n+n11:
                                              match n11:
                                                case 0n:
                                                  %Equal.sym(U32, tg, 11, PM.u32.eq(tg, 11, u.nat.eq(tg, 11, en))) : {U32.is_le(U32.add(272, _), 290) == True{} : Bool}
                                                  {==}
                                                case 1n+n12:
                                                  match n12:
                                                    case 0n:
                                                      %Equal.sym(U32, tg, 12, PM.u32.eq(tg, 12, u.nat.eq(tg, 12, en))) : {U32.is_le(U32.add(272, _), 290) == True{} : Bool}
                                                      {==}
                                                    case 1n+n13:
                                                      match n13:
                                                        case 0n:
                                                          %Equal.sym(U32, tg, 13, PM.u32.eq(tg, 13, u.nat.eq(tg, 13, en))) : {U32.is_le(U32.add(272, _), 290) == True{} : Bool}
                                                          {==}
                                                        case 1n+n14:
                                                          match n14:
                                                            case 0n:
                                                              %Equal.sym(U32, tg, 14, PM.u32.eq(tg, 14, u.nat.eq(tg, 14, en))) : {U32.is_le(U32.add(272, _), 290) == True{} : Bool}
                                                              {==}
                                                            case 1n+n15:
                                                              match n15:
                                                                case 0n:
                                                                  %Equal.sym(U32, tg, 15, PM.u32.eq(tg, 15, u.nat.eq(tg, 15, en))) : {U32.is_le(U32.add(272, _), 290) == True{} : Bool}
                                                                  {==}
                                                                case 1n+n16:
                                                                  match n16:
                                                                    case 0n:
                                                                      %Equal.sym(U32, tg, 16, PM.u32.eq(tg, 16, u.nat.eq(tg, 16, en))) : {U32.is_le(U32.add(272, _), 290) == True{} : Bool}
                                                                      {==}
                                                                    case 1n+n17:
                                                                      match n17:
                                                                        case 0n:
                                                                          %Equal.sym(U32, tg, 17, PM.u32.eq(tg, 17, u.nat.eq(tg, 17, en))) : {U32.is_le(U32.add(272, _), 290) == True{} : Bool}
                                                                          {==}
                                                                        case 1n+n18:
                                                                          match n18:
                                                                            case 0n:
                                                                              %Equal.sym(U32, tg, 18, PM.u32.eq(tg, 18, u.nat.eq(tg, 18, en))) : {U32.is_le(U32.add(272, _), 290) == True{} : Bool}
                                                                              {==}
                                                                            case 1n+n19:
                                                                              Empty.absurd({U32.is_le(U32.add(272, tg), 290) == True{} : Bool}, h)

def tbl.small(+tg: U32, h: {U32.is_lt(tg, 19) == True{} : Bool}) -> {U32.is_le(U32.add(272, tg), 290) == True{} : Bool}:
  tbl.small.at(U32.to_nat(tg), tg, {==}, u.lt(tg, 19, h))

def tblat.b(b: Bool, +m: Cr.Cir.Cells, +o: U32, +z: U32, +eb: {U32.is_lt(PM.Tg(m, o), 19) == b : Bool},
  hz: N.Le(1n+U32.to_nat(290), U32.to_nat(z))) -> {TblAt(m, o, z) == True{} : Bool}:
  match b:
    case False{}:
      %Equal.sym(Bool, U32.is_lt(PM.Tg(m, o), 19), False{}, eb) :
        {Bool.or(Bool.not(_), Bool.not(U32.is_eq(U32.add(272, PM.Tg(m, o)), z))) == True{} : Bool}
      {==}
    case True{}:
      %Equal.sym(Bool, U32.is_lt(PM.Tg(m, o), 19), True{}, eb) :
        {Bool.or(Bool.not(_), Bool.not(U32.is_eq(U32.add(272, PM.Tg(m, o)), z))) == True{} : Bool}
      %Equal.sym(Bool, U32.is_eq(U32.add(272, PM.Tg(m, o)), z), False{},
        lit.ne(U32.is_eq(U32.add(272, PM.Tg(m, o)), z), U32.add(272, PM.Tg(m, o)), z, 290, {==}, tbl.small(PM.Tg(m, o), eb), hz)) :
        {Bool.not(_) == True{} : Bool}
      {==}

# no cell reads its mask at z, past 290
def TblR.of(n: Nat, +m: Cr.Cir.Cells, +o: U32, +z: U32, +hz: N.Le(1n+U32.to_nat(290), U32.to_nat(z))) -> {TblR(n, m, o, z) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+k:
      and.i(TblAt(m, o, z), TblR(k, m, U32.inc(o), z), tblat.b(U32.is_lt(PM.Tg(m, o), 19), m, o, z, {==}, hz), TblR.of(k, m, U32.inc(o), z, hz))

# z is past 290, when it is one of the machine's own
def img.hz(-ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +z: U32,
  io: PM.ImgOK(ds, ks, img, m, im, fi, nx), hzo: {PM.Own(fi, nx, z) == True{} : Bool}) -> N.Le(1n+U32.to_nat(290), U32.to_nat(z)):
  (tb, r1) = io
  (hd, r2) = r1
  (h8, r3) = r2
  (h9, r4) = r3
  (h10, r5) = r4
  (hks, r6) = r5
  (e290, eim) = r6
  N.le_trans(1n+U32.to_nat(290), 1n+U32.to_nat(im), U32.to_nat(z), u.le(290, im, e290),
    N.le_trans(1n+U32.to_nat(im), U32.to_nat(fi), U32.to_nat(z), u.lt(im, fi, eim), u.le(fi, z, and.l(U32.is_le(fi, z), U32.is_lt(z, nx), hzo))))

# A store to a cell that nothing points to: HS
# -------------------------------------------
#
# M.make's stores, after M.alloc: the cell z is one of the machine's own, out
# of the pend list, not STATIC, of a tag below 32, holds no pointer and has
# none; it gets a cell x that is no term cell (a tag of 19 or more) and holds
# no pointer. Then HS holds with the same terms.

def hs.fz(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +os: List<&2, PM.Rt>, +bs: List<&2, PM.Rt>, +fs: List<&2, PM.AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>, +z: U32, +x: Cr.Cir.Cell,
  hs: PM.HS(ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps),
  +hzo: {PM.Own(fi, nx, z) == True{} : Bool}, +hzm: {PM.Mem(ps, z) == False{} : Bool},
  +hz0: {PM.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, PM.Rt.cells(os), z) == 0n : Nat},
  +hzs: {PM.Fl(m, z, 1024) == False{} : Bool}, hzt: {U32.is_lt(PM.TgW(PM.Fd(0n, m, z)), 32) == True{} : Bool},
  +hf0: {PM.Fs(m, ps, z) == Nil{} : List<&2, U32>}, +hf1: {PM.Fs(Cr.Cir.Cells.set(m, z, x), ps, z) == Nil{} : List<&2, U32>},
  hxt: {U32.is_lt(PM.TgW(Cr.Cir.Cell.get(0n, x)), 19) == False{} : Bool}) ->
  PM.HS(ds, ks, img, Cr.Cir.Cells.set(m, z, x), nx, fi, im, os, bs, fs, sp, pend, ps):
  PM.hs.fz(True{}, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps, z, x, hs, hzo, hzm, hz0, hzs, hzt, hf0, hf1, hxt)
