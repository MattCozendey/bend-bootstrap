# compiler: layer B, the swap moves
# =================================
#
# The moves of M.ret that swap the focus into the top frame (M.swap): App q □ a
# with q live and a not known (mv.ret.swap), Tup q □ b (mv.ret.tupb) and
# Min □ b (mv.ret.minb). The frame's cell sp gets a new header and the focus
# in field 2; its old field 2 becomes the focus, to evaluate. An admin move.
#
# The store to sp is one store (sw.mem): the cell {hd, y1, foc, y3, y4}. It
# keeps every term (a frame's tag is 32 or more: is.st), the rest of the
# frames (sp is not in the rest of its own chain, by the chain's length:
# Hops, frs.st), the image (ImgOK.fz: nothing points to a frame) and the heap:
# the pointer of sp's field 2 and the root trade places (Ptr.sw, Heap.sw).

import Base
import ../../Book/impl.bend as Bk
import ../../Eval/impl.bend as El
import ../../Wasm/impl.bend as Wa
import ../Cir/impl.bend as Cr
import ./impl.bend as Mc
import ../need_big.bend as N
import ./definitions.bend as D
import ./statement_runs.bend as X

# Kit
# ---

# Nat algebra (Compiler/Cir/simulation_numbers.bend's, copied)
def add.comm(+a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, N.add_zero(b))
    case 1n+p:
      Equal.trans(Nat, 1n+Nat.add(p, b), 1n+Nat.add(b, p), Nat.add(b, 1n+p),
        Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, b), Nat.add(b, p), add.comm(p, b)),
        Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), N.add_succ_r(b, p)))

def add.assoc(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(Nat.add(p, b), c), Nat.add(p, Nat.add(b, c)), add.assoc(p, b, c))

# (a + b) + c = (c + b) + a
def add.swap3(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(Nat.add(c, b), a) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(a, b), c), Nat.add(c, Nat.add(a, b)), Nat.add(Nat.add(c, b), a),
    add.comm(Nat.add(a, b), c),
    Equal.trans(Nat, Nat.add(c, Nat.add(a, b)), Nat.add(c, Nat.add(b, a)), Nat.add(Nat.add(c, b), a),
      Equal.cong(Nat, Nat, y => Nat.add(c, y), Nat.add(a, b), Nat.add(b, a), add.comm(a, b)),
      Equal.sym(Nat, Nat.add(Nat.add(c, b), a), Nat.add(c, Nat.add(b, a)), add.assoc(c, b, a))))

# the second of a pair
def p2.snd(-A: Data, -B: Data, p: D.P2(A, B)) -> B:
  match p:
    case Tuple{_, b}:
      b

# a number below another one as a U32 comparison (copy_kit.bend's, copied)
def u.lt_t.of(c: Cmp, +x: Nat, +y: Nat, r: N.Rel(c, x, y), h: N.Le(1n+x, y)) -> {Cmp.is_lt(c) == True{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({False{} == True{} : Bool}, N.not_succ_le(y, N.le_rw_l(1n+x, 1n+y, y, Equal.cong(Nat, Nat, z => 1n+z, x, y, r), h)))
    case GT{}:
      Empty.absurd({False{} == True{} : Bool}, N.not_succ_le(y, N.le_trans(1n+y, x, y, r, N.weaken(x, y, h))))

def u.lt_t(+a: U32, +b: U32, h: N.Le(1n+U32.to_nat(a), U32.to_nat(b))) -> {U32.is_lt(a, b) == True{} : Bool}:
  u.lt_t.of(U32.cmp(a, b), U32.to_nat(a), U32.to_nat(b), N.U32.rel(a, b), h)

# a cell past z is not z
def ne.lt.b(b: Bool, +o: U32, +z: U32, eb: {U32.is_eq(o, z) == b : Bool}, h: N.Le(1n+U32.to_nat(z), U32.to_nat(o))) ->
  {U32.is_eq(o, z) == False{} : Bool}:
  match b:
    case False{}:
      eb
    case True{}:
      +e = D.u32.eq(o, z, eb)
      Empty.absurd({U32.is_eq(o, z) == False{} : Bool},
        N.not_succ_le(U32.to_nat(z), (%e : N.Le(1n+U32.to_nat(z), U32.to_nat(_)); h)))

def ne.lt(+o: U32, +z: U32, h: N.Le(1n+U32.to_nat(z), U32.to_nat(o))) -> {U32.is_eq(o, z) == False{} : Bool}:
  ne.lt.b(U32.is_eq(o, z), o, z, {==}, h)

# a cell of a tag below 19 is not z, whose tag is 19 or more
def tg.ne.b(b: Bool, +m: Cr.Cir.Cells, +y: U32, +z: U32, eb: {U32.is_eq(y, z) == b : Bool},
  hy: {U32.is_lt(D.Tg(m, y), 19) == True{} : Bool}, hz: {U32.is_lt(D.Tg(m, z), 19) == False{} : Bool}) ->
  {U32.is_eq(y, z) == False{} : Bool}:
  match b:
    case False{}:
      eb
    case True{}:
      +e = D.u32.eq(y, z, eb)
      +hz2 = {(%Equal.sym(U32, y, z, e) : {U32.is_lt(D.Tg(m, _), 19) == False{} : Bool}; hz) : {U32.is_lt(D.Tg(m, y), 19) == False{} : Bool}}
      D.bool.ft({U32.is_eq(y, z) == False{} : Bool},
        Equal.trans(Bool, False{}, U32.is_lt(D.Tg(m, y), 19), True{}, Equal.sym(Bool, U32.is_lt(D.Tg(m, y), 19), False{}, hz2), hy))

def tg.ne(+m: Cr.Cir.Cells, +y: U32, +z: U32, hy: {U32.is_lt(D.Tg(m, y), 19) == True{} : Bool},
  hz: {U32.is_lt(D.Tg(m, z), 19) == False{} : Bool}) -> {U32.is_eq(y, z) == False{} : Bool}:
  tg.ne.b(U32.is_eq(y, z), m, y, z, {==}, hy, hz)

# A store that trades a pointer
# -----------------------------
#
# A store to the cell z, of the machine's own and of a tag of 19 or more,
# whose pointers go from [b] to [a], while the roots go from [a] to [b]: every
# count Ptr stays (Pc.mv, by induction on the cells from fi, with z among them
# once), and so does the heap (Heap.sw).

# a store to z keeps the pointers of the k cells from o, all past z and below nx
def Pc.out(k: Nat, +m: Cr.Cir.Cells, +z: U32, +x: Cr.Cir.Cell, +ps: List<&2, U32>, +o: U32, +c: U32, +nx: U32,
  hz: N.Le(1n+U32.to_nat(z), U32.to_nat(o)), hb: N.Le(Nat.add(U32.to_nat(o), k), U32.to_nat(nx)),
  ht: {D.TblR(k, m, o, z) == True{} : Bool}) ->
  {D.Pc(k, Cr.Cir.Cells.set(m, z, x), ps, o, c) == D.Pc(k, m, ps, o, c) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+(+j):
      +M2 = Cr.Cir.Cells.set(m, z, x)
      +ht2 = ht
      +hz2 = hz
      +hb2 = hb
      +lt1 = N.le_trans(1n+U32.to_nat(o), Nat.add(U32.to_nat(o), 1n+j), U32.to_nat(nx), N.lt_add(U32.to_nat(o), j), hb2)
      +ei = D.u.inc(o, nx, lt1)
      +hzi = N.le_rw_r(1n+U32.to_nat(z), 1n+U32.to_nat(o), U32.to_nat(U32.inc(o)),
        Equal.sym(Nat, U32.to_nat(U32.inc(o)), 1n+U32.to_nat(o), ei), N.le_succ(1n+U32.to_nat(z), U32.to_nat(o), hz2))
      +hbi = N.le_rw_l(Nat.add(U32.to_nat(o), 1n+j), Nat.add(U32.to_nat(U32.inc(o)), j), U32.to_nat(nx),
        Equal.trans(Nat, Nat.add(U32.to_nat(o), 1n+j), 1n+Nat.add(U32.to_nat(o), j), Nat.add(U32.to_nat(U32.inc(o)), j),
          N.add_succ_r(U32.to_nat(o), j),
          Equal.sym(Nat, Nat.add(U32.to_nat(U32.inc(o)), j), 1n+Nat.add(U32.to_nat(o), j),
            Equal.cong(Nat, Nat, y => Nat.add(y, j), U32.to_nat(U32.inc(o)), 1n+U32.to_nat(o), ei))), hb2)
      +e1 = D.fs.eq(m, z, x, ps, o, ne.lt(o, z, hz2), D.and.l(D.TblAt(m, o, z), D.TblR(j, m, U32.inc(o), z), ht2))
      +e2 = Pc.out(j, m, z, x, ps, U32.inc(o), c, nx, hzi, hbi, D.and.r(D.TblAt(m, o, z), D.TblR(j, m, U32.inc(o), z), ht2))
      %Equal.sym(List<&2, U32>, D.Fs(M2, ps, o), D.Fs(m, ps, o), e1) :
        {Nat.add(D.RcL(_, c), D.Pc(j, M2, ps, U32.inc(o), c)) == Nat.add(D.RcL(D.Fs(m, ps, o), c), D.Pc(j, m, ps, U32.inc(o), c)) : Nat}
      %Equal.sym(Nat, D.Pc(j, M2, ps, U32.inc(o), c), D.Pc(j, m, ps, U32.inc(o), c), e2) :
        {Nat.add(D.RcL(D.Fs(m, ps, o), c), _) == Nat.add(D.RcL(D.Fs(m, ps, o), c), D.Pc(j, m, ps, U32.inc(o), c)) : Nat}
      {==}

# the step of Pc.mv: o is z, or z is past o
def Pc.mv.b(bb: Bool, +j: Nat, +m: Cr.Cir.Cells, +z: U32, +x: Cr.Cir.Cell, +ps: List<&2, U32>, +o: U32, +c: U32, +nx: U32,
  +eb: {U32.is_eq(o, z) == bb : Bool}, +h1: N.Le(U32.to_nat(o), U32.to_nat(z)),
  +h2: N.Le(1n+U32.to_nat(z), Nat.add(U32.to_nat(o), 1n+j)), +hb: N.Le(Nat.add(U32.to_nat(o), 1n+j), U32.to_nat(nx)),
  +ht: {D.TblR(1n+j, m, o, z) == True{} : Bool},
  ih: N.Le(U32.to_nat(U32.inc(o)), U32.to_nat(z)) -> N.Le(1n+U32.to_nat(z), Nat.add(U32.to_nat(U32.inc(o)), j)) ->
    N.Le(Nat.add(U32.to_nat(U32.inc(o)), j), U32.to_nat(nx)) -> {D.TblR(j, m, U32.inc(o), z) == True{} : Bool} ->
    {Nat.add(D.Pc(j, Cr.Cir.Cells.set(m, z, x), ps, U32.inc(o), c), D.RcL(D.Fs(m, ps, z), c)) ==
      Nat.add(D.Pc(j, m, ps, U32.inc(o), c), D.RcL(D.Fs(Cr.Cir.Cells.set(m, z, x), ps, z), c)) : Nat}) ->
  {Nat.add(D.Pc(1n+j, Cr.Cir.Cells.set(m, z, x), ps, o, c), D.RcL(D.Fs(m, ps, z), c)) ==
    Nat.add(D.Pc(1n+j, m, ps, o, c), D.RcL(D.Fs(Cr.Cir.Cells.set(m, z, x), ps, z), c)) : Nat}:
  match bb:
    case True{}:
      +M2 = Cr.Cir.Cells.set(m, z, x)
      +R0 = D.RcL(D.Fs(m, ps, z), c)
      +R1 = D.RcL(D.Fs(M2, ps, z), c)
      +eadd = Equal.trans(Nat, Nat.add(U32.to_nat(o), 1n+j), 1n+Nat.add(U32.to_nat(o), j), Nat.add(1n+U32.to_nat(o), j),
        N.add_succ_r(U32.to_nat(o), j), {==})
      +eo = D.u32.eq(o, z, eb)
      +lt1 = N.le_trans(1n+U32.to_nat(o), Nat.add(U32.to_nat(o), 1n+j), U32.to_nat(nx), N.lt_add(U32.to_nat(o), j), hb)
      +ei = D.u.inc(o, nx, lt1)
      +hzo = {(%eo : N.Le(1n+U32.to_nat(_), U32.to_nat(U32.inc(o)));
        N.le_rw_r(1n+U32.to_nat(o), 1n+U32.to_nat(o), U32.to_nat(U32.inc(o)), Equal.sym(Nat, U32.to_nat(U32.inc(o)), 1n+U32.to_nat(o), ei),
          N.le_refl(1n+U32.to_nat(o)))) : N.Le(1n+U32.to_nat(z), U32.to_nat(U32.inc(o)))}
      +hbi = N.le_rw_l(Nat.add(U32.to_nat(o), 1n+j), Nat.add(U32.to_nat(U32.inc(o)), j), U32.to_nat(nx),
        Equal.trans(Nat, Nat.add(U32.to_nat(o), 1n+j), Nat.add(1n+U32.to_nat(o), j), Nat.add(U32.to_nat(U32.inc(o)), j), eadd,
          Equal.sym(Nat, Nat.add(U32.to_nat(U32.inc(o)), j), Nat.add(1n+U32.to_nat(o), j),
            Equal.cong(Nat, Nat, y => Nat.add(y, j), U32.to_nat(U32.inc(o)), 1n+U32.to_nat(o), ei))), hb)
      +e2 = Pc.out(j, m, z, x, ps, U32.inc(o), c, nx, hzo, hbi, D.and.r(D.TblAt(m, o, z), D.TblR(j, m, U32.inc(o), z), ht))
      %Equal.sym(U32, o, z, eo) :
        {Nat.add(Nat.add(D.RcL(D.Fs(M2, ps, _), c), D.Pc(j, M2, ps, U32.inc(o), c)), R0) ==
          Nat.add(Nat.add(D.RcL(D.Fs(m, ps, _), c), D.Pc(j, m, ps, U32.inc(o), c)), R1) : Nat}
      %Equal.sym(Nat, D.Pc(j, M2, ps, U32.inc(o), c), D.Pc(j, m, ps, U32.inc(o), c), e2) :
        {Nat.add(Nat.add(R1, _), R0) == Nat.add(Nat.add(R0, D.Pc(j, m, ps, U32.inc(o), c)), R1) : Nat}
      add.swap3(R1, D.Pc(j, m, ps, U32.inc(o), c), R0)
    case False{}:
      +M2 = Cr.Cir.Cells.set(m, z, x)
      +R0 = D.RcL(D.Fs(m, ps, z), c)
      +R1 = D.RcL(D.Fs(M2, ps, z), c)
      +eadd = Equal.trans(Nat, Nat.add(U32.to_nat(o), 1n+j), 1n+Nat.add(U32.to_nat(o), j), Nat.add(1n+U32.to_nat(o), j),
        N.add_succ_r(U32.to_nat(o), j), {==})
      +lt = D.lt.ne(U32.cmp(o, z), U32.to_nat(o), U32.to_nat(z), N.U32.rel(o, z), eb, h1)
      +ei = D.u.inc(o, z, lt)
      +ej = Equal.trans(Nat, Nat.add(U32.to_nat(o), 1n+j), Nat.add(1n+U32.to_nat(o), j), Nat.add(U32.to_nat(U32.inc(o)), j), eadd,
        Equal.sym(Nat, Nat.add(U32.to_nat(U32.inc(o)), j), Nat.add(1n+U32.to_nat(o), j),
          Equal.cong(Nat, Nat, y => Nat.add(y, j), U32.to_nat(U32.inc(o)), 1n+U32.to_nat(o), ei)))
      +h1b = N.le_rw_l(1n+U32.to_nat(o), U32.to_nat(U32.inc(o)), U32.to_nat(z), Equal.sym(Nat, U32.to_nat(U32.inc(o)), 1n+U32.to_nat(o), ei), lt)
      +h2b = N.le_rw_r(1n+U32.to_nat(z), Nat.add(U32.to_nat(o), 1n+j), Nat.add(U32.to_nat(U32.inc(o)), j), ej, h2)
      +hbb = N.le_rw_l(Nat.add(U32.to_nat(o), 1n+j), Nat.add(U32.to_nat(U32.inc(o)), j), U32.to_nat(nx), ej, hb)
      +e1 = D.fs.eq(m, z, x, ps, o, eb, D.and.l(D.TblAt(m, o, z), D.TblR(j, m, U32.inc(o), z), ht))
      +e2 = ih(h1b, h2b, hbb, D.and.r(D.TblAt(m, o, z), D.TblR(j, m, U32.inc(o), z), ht))
      +A = D.RcL(D.Fs(m, ps, o), c)
      +P1 = D.Pc(j, M2, ps, U32.inc(o), c)
      +P0 = D.Pc(j, m, ps, U32.inc(o), c)
      %Equal.sym(List<&2, U32>, D.Fs(M2, ps, o), D.Fs(m, ps, o), e1) :
        {Nat.add(Nat.add(D.RcL(_, c), P1), R0) == Nat.add(Nat.add(A, P0), R1) : Nat}
      Equal.trans(Nat, Nat.add(Nat.add(A, P1), R0), Nat.add(A, Nat.add(P1, R0)), Nat.add(Nat.add(A, P0), R1),
        add.assoc(A, P1, R0),
        Equal.trans(Nat, Nat.add(A, Nat.add(P1, R0)), Nat.add(A, Nat.add(P0, R1)), Nat.add(Nat.add(A, P0), R1),
          Equal.cong(Nat, Nat, y => Nat.add(A, y), Nat.add(P1, R0), Nat.add(P0, R1), e2),
          Equal.sym(Nat, Nat.add(Nat.add(A, P0), R1), Nat.add(A, Nat.add(P0, R1)), add.assoc(A, P0, R1))))

# a store to z, one of the k cells from o (below nx), trades z's pointers in Pc
def Pc.mv(k: Nat, +m: Cr.Cir.Cells, +z: U32, +x: Cr.Cir.Cell, +ps: List<&2, U32>, +o: U32, +c: U32, +nx: U32,
  h1: N.Le(U32.to_nat(o), U32.to_nat(z)), h2: N.Le(1n+U32.to_nat(z), Nat.add(U32.to_nat(o), k)),
  hb: N.Le(Nat.add(U32.to_nat(o), k), U32.to_nat(nx)), ht: {D.TblR(k, m, o, z) == True{} : Bool}) ->
  {Nat.add(D.Pc(k, Cr.Cir.Cells.set(m, z, x), ps, o, c), D.RcL(D.Fs(m, ps, z), c)) ==
    Nat.add(D.Pc(k, m, ps, o, c), D.RcL(D.Fs(Cr.Cir.Cells.set(m, z, x), ps, z), c)) : Nat}:
  match k:
    case 0n:
      Empty.absurd({Nat.add(0n, D.RcL(D.Fs(m, ps, z), c)) == Nat.add(0n, D.RcL(D.Fs(Cr.Cir.Cells.set(m, z, x), ps, z), c)) : Nat},
        N.not_succ_le(U32.to_nat(z), N.le_trans(1n+U32.to_nat(z), U32.to_nat(o), U32.to_nat(z),
          N.le_rw_r(1n+U32.to_nat(z), Nat.add(U32.to_nat(o), 0n), U32.to_nat(o), N.add_zero(U32.to_nat(o)), h2), h1)))
    case 1n+(+j):
      Pc.mv.b(U32.is_eq(o, z), j, m, z, x, ps, o, c, nx, {==}, h1, h2, hb, ht,
        a => b => d => e => Pc.mv(j, m, z, x, ps, U32.inc(o), c, nx, a, b, d, e))

# the counts, with the roots [a] and then [b]
def Ptr.sw(+m: Cr.Cir.Cells, +nx: U32, +fi: U32, +ps: List<&2, U32>, +z: U32, +x: Cr.Cir.Cell, +a: U32, +b: U32, +c: U32,
  hf0: {D.Fs(m, ps, z) == [b] : List<&2, U32>}, hf1: {D.Fs(Cr.Cir.Cells.set(m, z, x), ps, z) == [a] : List<&2, U32>},
  hzo: {D.Own(fi, nx, z) == True{} : Bool}, ht: {D.TblR(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, z) == True{} : Bool}) ->
  {D.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), Cr.Cir.Cells.set(m, z, x), fi, ps, [b], c) ==
    D.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, [a], c) : Nat}:
  +o2 = hzo
  +M2 = Cr.Cir.Cells.set(m, z, x)
  +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
  +h1 = D.u.le(fi, z, D.and.l(U32.is_le(fi, z), U32.is_lt(z, nx), o2))
  +hl = D.u.lt(z, nx, D.and.r(U32.is_le(fi, z), U32.is_lt(z, nx), o2))
  +es = D.add.sub(U32.to_nat(fi), U32.to_nat(nx), N.le_trans(U32.to_nat(fi), U32.to_nat(z), U32.to_nat(nx), h1, N.weaken(U32.to_nat(z), U32.to_nat(nx), hl)))
  +es2 = Equal.sym(Nat, Nat.add(U32.to_nat(fi), n), U32.to_nat(nx), es)
  +h2 = N.le_rw_r(1n+U32.to_nat(z), U32.to_nat(nx), Nat.add(U32.to_nat(fi), n), es2, hl)
  +hb = N.le_rw_l(U32.to_nat(nx), Nat.add(U32.to_nat(fi), n), U32.to_nat(nx), es2, N.le_refl(U32.to_nat(nx)))
  %hf0 : {Nat.add(D.Pc(n, M2, ps, fi, c), D.RcL(_, c)) == Nat.add(D.Pc(n, m, ps, fi, c), D.RcL([a], c)) : Nat}
  %hf1 : {Nat.add(D.Pc(n, M2, ps, fi, c), D.RcL(D.Fs(m, ps, z), c)) == Nat.add(D.Pc(n, m, ps, fi, c), D.RcL(_, c)) : Nat}
  Pc.mv(n, m, z, x, ps, fi, c, nx, h1, h2, hb, ht)

# Cnt at the cell o, after the store, from Cnt before it
def cnt.sw.at(b: Bool, +m: Cr.Cir.Cells, +z: U32, +x: Cr.Cir.Cell, +o: U32, +n: Nat, +fi: U32, +ps: List<&2, U32>,
  +rs1: List<&2, U32>, +rs2: List<&2, U32>, eb: {U32.is_eq(o, z) == b : Bool},
  hxt: {U32.is_lt(D.TgW(Cr.Cir.Cell.get(0n, x)), 19) == False{} : Bool},
  hP: {D.Ptr(n, Cr.Cir.Cells.set(m, z, x), fi, ps, rs2, o) == D.Ptr(n, m, fi, ps, rs1, o) : Nat},
  h: {D.CntC(Cr.Cir.Cells.get(m, o), D.Ptr(n, m, fi, ps, rs1, o), ps, o) == True{} : Bool}) ->
  {D.CntC(Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, x), o), D.Ptr(n, Cr.Cir.Cells.set(m, z, x), fi, ps, rs2, o), ps, o) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(U32, o, z, D.u32.eq(o, z, eb)) :
        {D.CntC(Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, x), _), D.Ptr(n, Cr.Cir.Cells.set(m, z, x), fi, ps, rs2, _), ps, _) == True{} : Bool}
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, x), z), x, D.cl.gs(m, z, x)) :
        {D.CntC(_, D.Ptr(n, Cr.Cir.Cells.set(m, z, x), fi, ps, rs2, z), ps, z) == True{} : Bool}
      D.or.l(Bool.not(U32.is_lt(D.TgW(Cr.Cir.Cell.get(0n, x)), 19)), Bool.or(D.FlW(Cr.Cir.Cell.get(0n, x), 1024), Bool.or(D.Mem(ps, z),
        Nat.is_eq(U32.to_nat(Cr.Cir.Cell.get(1n, x)), D.Ptr(n, Cr.Cir.Cells.set(m, z, x), fi, ps, rs2, z)))),
        (%Equal.sym(Bool, U32.is_lt(D.TgW(Cr.Cir.Cell.get(0n, x)), 19), False{}, hxt) : {Bool.not(_) == True{} : Bool}; {==}))
    case False{}:
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, x), o), Cr.Cir.Cells.get(m, o), D.cl.go(m, o, z, x, eb)) :
        {D.CntC(_, D.Ptr(n, Cr.Cir.Cells.set(m, z, x), fi, ps, rs2, o), ps, o) == True{} : Bool}
      %Equal.sym(Nat, D.Ptr(n, Cr.Cir.Cells.set(m, z, x), fi, ps, rs2, o), D.Ptr(n, m, fi, ps, rs1, o), hP) :
        {D.CntC(Cr.Cir.Cells.get(m, o), _, ps, o) == True{} : Bool}
      h

# the counts of k cells from o, after the store
def Cnt.sw(k: Nat, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +ps: List<&2, U32>, +z: U32, +x: Cr.Cir.Cell, +a: U32, +b: U32, +o: U32,
  +hf0: {D.Fs(m, ps, z) == [b] : List<&2, U32>}, +hf1: {D.Fs(Cr.Cir.Cells.set(m, z, x), ps, z) == [a] : List<&2, U32>},
  +hzo: {D.Own(fi, nx, z) == True{} : Bool}, +ht: {D.TblR(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, z) == True{} : Bool},
  +hxt: {U32.is_lt(D.TgW(Cr.Cir.Cell.get(0n, x)), 19) == False{} : Bool},
  h: {D.Cnt(k, m, o, Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), fi, ps, [a]) == True{} : Bool}) ->
  {D.Cnt(k, Cr.Cir.Cells.set(m, z, x), o, Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), fi, ps, [b]) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+(+j):
      +M2 = Cr.Cir.Cells.set(m, z, x)
      +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
      +h2 = h
      D.and.i(D.CntC(Cr.Cir.Cells.get(M2, o), D.Ptr(n, M2, fi, ps, [b], o), ps, o), D.Cnt(j, M2, U32.inc(o), n, fi, ps, [b]),
        cnt.sw.at(U32.is_eq(o, z), m, z, x, o, n, fi, ps, [a], [b], {==}, hxt, Ptr.sw(m, nx, fi, ps, z, x, a, b, o, hf0, hf1, hzo, ht),
          D.and.l(D.CntC(Cr.Cir.Cells.get(m, o), D.Ptr(n, m, fi, ps, [a], o), ps, o), D.Cnt(j, m, U32.inc(o), n, fi, ps, [a]), h2)),
        Cnt.sw(j, m, nx, fi, ps, z, x, a, b, U32.inc(o), hf0, hf1, hzo, ht, hxt,
          D.and.r(D.CntC(Cr.Cir.Cells.get(m, o), D.Ptr(n, m, fi, ps, [a], o), ps, o), D.Cnt(j, m, U32.inc(o), n, fi, ps, [a]), h2)))

# the pend list's cells, none of them z, after the store
def PendOK.sw(qs: List<&2, U32>, +ps: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +z: U32, +x: Cr.Cir.Cell, +a: U32, +b: U32,
  +hf0: {D.Fs(m, ps, z) == [b] : List<&2, U32>}, +hf1: {D.Fs(Cr.Cir.Cells.set(m, z, x), ps, z) == [a] : List<&2, U32>},
  +hzo: {D.Own(fi, nx, z) == True{} : Bool}, +ht: {D.TblR(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, z) == True{} : Bool},
  hq: {D.Mem(qs, z) == False{} : Bool}, h: D.PendOK(qs, ps, m, fi, nx, [a])) -> D.PendOK(qs, ps, Cr.Cir.Cells.set(m, z, x), fi, nx, [b]):
  match qs:
    case Nil{}:
      Unit{}
    case Con{+p, +rest}:
      (ho, r1) = h
      (hs, r2) = r1
      (htg, r3) = r2
      (hp0, r4) = r3
      +M2 = Cr.Cir.Cells.set(m, z, x)
      +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
      +hq2 = hq
      +ne = D.or.f.l(U32.is_eq(p, z), D.Mem(rest, z), hq2)
      +ec = D.cl.go(m, p, z, x, ne)
      (ho, ((%Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M2, p), Cr.Cir.Cells.get(m, p), ec) :
          {U32.is_ne(U32.and(Cr.Cir.Cell.get(0n, _), 1024), 0) == False{} : Bool}; hs),
        ((%Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M2, p), Cr.Cir.Cells.get(m, p), ec) :
          {Bool.or(U32.is_lt(U32.and(Cr.Cir.Cell.get(0n, _), 63), 19), U32.is_le(32, U32.and(Cr.Cir.Cell.get(0n, _), 63))) == True{} : Bool}; htg),
        ((%Equal.sym(Nat, D.Ptr(n, M2, fi, ps, [b], p), D.Ptr(n, m, fi, ps, [a], p), Ptr.sw(m, nx, fi, ps, z, x, a, b, p, hf0, hf1, hzo, ht)) :
            {_ == 0n : Nat}; hp0),
          PendOK.sw(rest, ps, m, nx, fi, z, x, a, b, hf0, hf1, hzo, ht, D.or.f.r(U32.is_eq(p, z), D.Mem(rest, z), hq2), r4)))))

# the tag of a pointer, as LtC says it
def ltc.tg(+y: U32, +c: Cr.Cir.Cell, +im: U32, +fi: U32, +nx: U32, h: {D.LtC(y, c, im, fi, nx) == True{} : Bool}) ->
  {U32.is_lt(D.TgW(Cr.Cir.Cell.get(0n, c)), 19) == True{} : Bool}:
  +f0 = Cr.Cir.Cell.get(0n, c)
  D.and.r(U32.is_lt(y, nx), U32.is_lt(D.TgW(f0), 19),
    D.and.l(Bool.and(U32.is_lt(y, nx), U32.is_lt(D.TgW(f0), 19)),
      Bool.and(Cr.Cir.is_cell(y, im, fi, nx), Bool.or(D.Own(fi, nx, y), D.FlW(f0, 1024))), h))

# no pointer of xs, to a term cell, is z, whose tag is 19 or more
def rcl.none(xs: List<&2, U32>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +z: U32,
  +hz: {U32.is_lt(D.Tg(m, z), 19) == False{} : Bool},
  h: {D.Lt.all(xs, m, im, fi, nx) == True{} : Bool}) -> {D.RcL(xs, z) == 0n : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+y, +rest}:
      +h2 = h
      +hy = D.and.l(D.LtC(y, Cr.Cir.Cells.get(m, y), im, fi, nx), D.Lt.all(rest, m, im, fi, nx), h2)
      +ne = tg.ne(m, y, z, ltc.tg(y, Cr.Cir.Cells.get(m, y), im, fi, nx, hy), hz)
      %Equal.sym(Bool, U32.is_eq(y, z), False{}, ne) : {Nat.add(D.Nat.of(_), D.RcL(rest, z)) == 0n : Nat}
      rcl.none(rest, m, im, fi, nx, z, hz, D.and.r(D.LtC(y, Cr.Cir.Cells.get(m, y), im, fi, nx), D.Lt.all(rest, m, im, fi, nx), h2))

# no cell points to z, whose tag is 19 or more
def pc.none(k: Nat, +m: Cr.Cir.Cells, +ps: List<&2, U32>, +o: U32, +im: U32, +fi: U32, +nx: U32, +z: U32,
  +hz: {U32.is_lt(D.Tg(m, z), 19) == False{} : Bool}, h: {D.Pts(k, m, ps, o, im, fi, nx) == True{} : Bool}) ->
  {D.Pc(k, m, ps, o, z) == 0n : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+(+j):
      +h2 = h
      %Equal.sym(Nat, D.RcL(D.Fs(m, ps, o), z), 0n,
        rcl.none(D.Fs(m, ps, o), m, im, fi, nx, z, hz,
          D.and.l(D.Lt.all(D.Fs(m, ps, o), m, im, fi, nx), D.Pts(j, m, ps, U32.inc(o), im, fi, nx), h2))) :
        {Nat.add(_, D.Pc(j, m, ps, U32.inc(o), z)) == 0n : Nat}
      pc.none(j, m, ps, U32.inc(o), im, fi, nx, z, hz, D.and.r(D.Lt.all(D.Fs(m, ps, o), m, im, fi, nx), D.Pts(j, m, ps, U32.inc(o), im, fi, nx), h2))

# the pointers xs, to term cells, after a store to z, whose tag is 19 or more
def lt.tg(xs: List<&2, U32>, +m: Cr.Cir.Cells, +z: U32, +x: Cr.Cir.Cell, +im: U32, +fi: U32, +nx: U32,
  +hz: {U32.is_lt(D.Tg(m, z), 19) == False{} : Bool},
  h: {D.Lt.all(xs, m, im, fi, nx) == True{} : Bool}) -> {D.Lt.all(xs, Cr.Cir.Cells.set(m, z, x), im, fi, nx) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+y, +rest}:
      +M2 = Cr.Cir.Cells.set(m, z, x)
      +h2 = h
      +hy = D.and.l(D.LtC(y, Cr.Cir.Cells.get(m, y), im, fi, nx), D.Lt.all(rest, m, im, fi, nx), h2)
      +ne = tg.ne(m, y, z, ltc.tg(y, Cr.Cir.Cells.get(m, y), im, fi, nx, hy), hz)
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M2, y), Cr.Cir.Cells.get(m, y), D.cl.go(m, y, z, x, ne)) :
        {Bool.and(D.LtC(y, _, im, fi, nx), D.Lt.all(rest, M2, im, fi, nx)) == True{} : Bool}
      D.and.i(D.LtC(y, Cr.Cir.Cells.get(m, y), im, fi, nx), D.Lt.all(rest, M2, im, fi, nx), hy,
        lt.tg(rest, m, z, x, im, fi, nx, hz, D.and.r(D.LtC(y, Cr.Cir.Cells.get(m, y), im, fi, nx), D.Lt.all(rest, m, im, fi, nx), h2)))

# the pointers of the cell o after the store: z's are [a]
def pts.sw.at(b: Bool, +m: Cr.Cir.Cells, +z: U32, +x: Cr.Cir.Cell, +ps: List<&2, U32>, +o: U32, +im: U32, +fi: U32, +nx: U32, +a: U32,
  eb: {U32.is_eq(o, z) == b : Bool}, hf1: {D.Fs(Cr.Cir.Cells.set(m, z, x), ps, z) == [a] : List<&2, U32>},
  hal: {D.Lt.all([a], Cr.Cir.Cells.set(m, z, x), im, fi, nx) == True{} : Bool}, ht: {D.TblAt(m, o, z) == True{} : Bool},
  hz: {U32.is_lt(D.Tg(m, z), 19) == False{} : Bool}, h: {D.Lt.all(D.Fs(m, ps, o), m, im, fi, nx) == True{} : Bool}) ->
  {D.Lt.all(D.Fs(Cr.Cir.Cells.set(m, z, x), ps, o), Cr.Cir.Cells.set(m, z, x), im, fi, nx) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(U32, o, z, D.u32.eq(o, z, eb)) :
        {D.Lt.all(D.Fs(Cr.Cir.Cells.set(m, z, x), ps, _), Cr.Cir.Cells.set(m, z, x), im, fi, nx) == True{} : Bool}
      %Equal.sym(List<&2, U32>, D.Fs(Cr.Cir.Cells.set(m, z, x), ps, z), [a], hf1) :
        {D.Lt.all(_, Cr.Cir.Cells.set(m, z, x), im, fi, nx) == True{} : Bool}
      hal
    case False{}:
      %Equal.sym(List<&2, U32>, D.Fs(Cr.Cir.Cells.set(m, z, x), ps, o), D.Fs(m, ps, o), D.fs.eq(m, z, x, ps, o, eb, ht)) :
        {D.Lt.all(_, Cr.Cir.Cells.set(m, z, x), im, fi, nx) == True{} : Bool}
      lt.tg(D.Fs(m, ps, o), m, z, x, im, fi, nx, hz, h)

# every pointer points to a term cell, after the store
def Pts.sw(k: Nat, +m: Cr.Cir.Cells, +z: U32, +x: Cr.Cir.Cell, +ps: List<&2, U32>, +o: U32, +im: U32, +fi: U32, +nx: U32, +a: U32,
  +hf1: {D.Fs(Cr.Cir.Cells.set(m, z, x), ps, z) == [a] : List<&2, U32>},
  +hal: {D.Lt.all([a], Cr.Cir.Cells.set(m, z, x), im, fi, nx) == True{} : Bool},
  +hz: {U32.is_lt(D.Tg(m, z), 19) == False{} : Bool}, ht: {D.TblR(k, m, o, z) == True{} : Bool},
  h: {D.Pts(k, m, ps, o, im, fi, nx) == True{} : Bool}) -> {D.Pts(k, Cr.Cir.Cells.set(m, z, x), ps, o, im, fi, nx) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+(+j):
      +M2 = Cr.Cir.Cells.set(m, z, x)
      +ht2 = ht
      +h2 = h
      D.and.i(D.Lt.all(D.Fs(M2, ps, o), M2, im, fi, nx), D.Pts(j, M2, ps, U32.inc(o), im, fi, nx),
        pts.sw.at(U32.is_eq(o, z), m, z, x, ps, o, im, fi, nx, a, {==}, hf1, hal, D.and.l(D.TblAt(m, o, z), D.TblR(j, m, U32.inc(o), z), ht2), hz,
          D.and.l(D.Lt.all(D.Fs(m, ps, o), m, im, fi, nx), D.Pts(j, m, ps, U32.inc(o), im, fi, nx), h2)),
        Pts.sw(j, m, z, x, ps, U32.inc(o), im, fi, nx, a, hf1, hal, hz, D.and.r(D.TblAt(m, o, z), D.TblR(j, m, U32.inc(o), z), ht2),
          D.and.r(D.Lt.all(D.Fs(m, ps, o), m, im, fi, nx), D.Pts(j, m, ps, U32.inc(o), im, fi, nx), h2)))

# the heap after the store: the pointer [b] of z and the root [a] trade places
def Heap.sw(+m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pend: U32, +ps: List<&2, U32>, +z: U32, +x: Cr.Cir.Cell, +a: U32, +b: U32,
  +hf0: {D.Fs(m, ps, z) == [b] : List<&2, U32>}, +hf1: {D.Fs(Cr.Cir.Cells.set(m, z, x), ps, z) == [a] : List<&2, U32>},
  +hzo: {D.Own(fi, nx, z) == True{} : Bool}, +hz290: N.Le(1n+U32.to_nat(290), U32.to_nat(z)), +hzm: {D.Mem(ps, z) == False{} : Bool},
  +hzt: {U32.is_lt(D.Tg(m, z), 19) == False{} : Bool}, +hxt: {U32.is_lt(D.TgW(Cr.Cir.Cell.get(0n, x)), 19) == False{} : Bool},
  +hal: {D.Lt.all([a], Cr.Cir.Cells.set(m, z, x), im, fi, nx) == True{} : Bool},
  h: D.Heap(m, nx, fi, im, [a], pend, ps)) -> D.Heap(Cr.Cir.Cells.set(m, z, x), nx, fi, im, [b], pend, ps):
  (hc, r1) = h
  (hp, r2) = r1
  (hcn, r3) = r2
  (hpt, hr) = r3
  +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
  +ht = D.TblR.of(n, m, fi, z, hz290)
  (D.Chain.fz(ps, m, z, x, pend, hzm, hc), (PendOK.sw(ps, ps, m, nx, fi, z, x, a, b, hf0, hf1, hzo, ht, hzm, hp),
    (Cnt.sw(n, m, nx, fi, ps, z, x, a, b, fi, hf0, hf1, hzo, ht, hxt, hcn),
    (Pts.sw(n, m, z, x, ps, fi, im, fi, nx, a, hf1, hal, hzt, ht, hpt), hr))))

# no pointer to z, of a tag of 19 or more, from the cells or the root [a]
def ptr.none(+m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +ps: List<&2, U32>, +pend: U32, +a: U32, +z: U32,
  +hz: {U32.is_lt(D.Tg(m, z), 19) == False{} : Bool}, ha: {U32.is_lt(D.Tg(m, a), 19) == True{} : Bool},
  h: D.Heap(m, nx, fi, im, [a], pend, ps)) -> {D.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, [a], z) == 0n : Nat}:
  (hc, r1) = h
  (hp, r2) = r1
  (hcn, r3) = r2
  (hpt, hr) = r3
  +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
  %Equal.sym(Nat, D.Pc(n, m, ps, fi, z), 0n, pc.none(n, m, ps, fi, im, fi, nx, z, hz, hpt)) : {Nat.add(_, D.RcL([a], z)) == 0n : Nat}
  %Equal.sym(Bool, U32.is_eq(a, z), False{}, tg.ne(m, a, z, ha, hz)) : {Nat.add(0n, Nat.add(D.Nat.of(_), 0n)) == 0n : Nat}
  {==}

# The frames under a store to the top frame
# -----------------------------------------
#
# The frames from fr, linked by field 1, end in 0 after exactly as many cells
# as there are frames (Hops). So the top frame sp, whose chain has one more
# frame than the rest, is none of the rest's cells (hops.ne), and a store to
# sp keeps the rest (frs.st).

# from fr, n cells that are not 0, linked by field 1, then 0
def Hops(n: Nat, +m: Cr.Cir.Cells, +fr: U32) -> Bool:
  match n:
    case 0n:
      U32.is_eq(fr, 0)
    case 1n+p:
      Bool.and(Bool.not(U32.is_eq(fr, 0)), Hops(p, m, D.Fd(1n, m, fr)))

# the frames from fr are as many as its chain's cells
def frs.hops(fs: List<&2, D.AF>, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +fr: U32, h: D.Frs(ds, m, im, fi, nx, ks, img, ps, fr, fs)) ->
  {Hops(List.length(&2, D.AF, fs), m, fr) == True{} : Bool}:
  match fs:
    case Nil{}:
      %Equal.sym(U32, fr, 0, h) : {Hops(0n, m, _) == True{} : Bool}
      {==}
    case Con{D.AF{+kind, +q, +k, +a, +b}, +rest}:
      match h:
        case Tuple{e0, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, ir}}}}}}}}}}:
          D.and.i(Bool.not(U32.is_eq(fr, 0)), Hops(List.length(&2, D.AF, rest), m, D.Fd(1n, m, fr)),
            (%Equal.sym(Bool, U32.is_eq(fr, 0), False{}, e0) : {Bool.not(_) == True{} : Bool}; {==}),
            frs.hops(rest, ds, m, im, fi, nx, ks, img, ps, D.Fd(1n, m, fr), ir))

# a chain ends after one number of cells only
def hops.lt(a: Nat, b: Nat, +m: Cr.Cir.Cells, +x: U32, ha: {Hops(a, m, x) == True{} : Bool}, hb: {Hops(b, m, x) == True{} : Bool},
  hlt: N.Le(1n+a, b)) -> Empty:
  match a b:
    case 0n 0n:
      hlt
    case 0n 1n+q:
      D.bool.ft(Empty, (%ha : {Bool.not(_) == True{} : Bool};
        D.and.l(Bool.not(U32.is_eq(x, 0)), Hops(q, m, D.Fd(1n, m, x)), hb)))
    case 1n+p 0n:
      hlt
    case 1n+p 1n+q:
      hops.lt(p, q, m, D.Fd(1n, m, x), D.and.r(Bool.not(U32.is_eq(x, 0)), Hops(p, m, D.Fd(1n, m, x)), ha),
        D.and.r(Bool.not(U32.is_eq(x, 0)), Hops(q, m, D.Fd(1n, m, x)), hb), hlt)

def hops.ne.b(bb: Bool, a: Nat, b: Nat, +m: Cr.Cir.Cells, +x: U32, +y: U32, eb: {U32.is_eq(x, y) == bb : Bool},
  hx: {Hops(a, m, x) == True{} : Bool}, hy: {Hops(b, m, y) == True{} : Bool}, hlt: N.Le(1n+a, b)) -> {U32.is_eq(x, y) == False{} : Bool}:
  match bb:
    case False{}:
      eb
    case True{}:
      +e = D.u32.eq(x, y, eb)
      Empty.absurd({U32.is_eq(x, y) == False{} : Bool}, hops.lt(a, b, m, y, (%e : {Hops(a, m, _) == True{} : Bool}; hx), hy, hlt))

# a cell whose chain is shorter than y's is not y
def hops.ne(a: Nat, b: Nat, +m: Cr.Cir.Cells, +x: U32, +y: U32, hx: {Hops(a, m, x) == True{} : Bool},
  hy: {Hops(b, m, y) == True{} : Bool}, hlt: N.Le(1n+a, b)) -> {U32.is_eq(x, y) == False{} : Bool}:
  hops.ne.b(U32.is_eq(x, y), a, b, m, x, y, {==}, hx, hy, hlt)

# a store to sx, of a tag of 32 or more, keeps the term of the cell c
def is.keep(t: Bk.Term, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +sx: U32, +sv: Cr.Cir.Cell, +c: U32, +ht: {U32.is_lt(D.TgW(D.Fd(0n, m, sx)), 32) == False{} : Bool},
  h: D.Is(ds, m, im, fi, nx, ks, img, c, t)) -> D.Is(ds, Cr.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, c, t):
  p2.snd({Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, sx, sv), c) == Cr.Cir.Cells.get(m, c) : Cr.Cir.Cell},
    D.Is(ds, Cr.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, c, t), D.is.st(t, ds, m, im, fi, nx, ks, img, sx, sv, c, ht, h))

def frsb.st(kind: D.FK, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +sx: U32, +sv: Cr.Cir.Cell, +c: U32, +b: Bk.Term, +ht: {U32.is_lt(D.TgW(D.Fd(0n, m, sx)), 32) == False{} : Bool},
  h: D.Frs.b(ds, m, im, fi, nx, ks, img, c, kind, b)) -> D.Frs.b(ds, Cr.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, c, kind, b):
  match kind:
    case D.FK.rwt{}:
      is.keep(b, ds, m, im, fi, nx, ks, img, sx, sv, c, ht, h)
    case D.FK.arg{}:
      Unit{}
    case D.FK.val{}:
      Unit{}
    case D.FK.fun{}:
      Unit{}
    case D.FK.let{}:
      Unit{}
    case D.FK.tupb{}:
      Unit{}
    case D.FK.tupa{}:
      Unit{}
    case D.FK.minb{}:
      Unit{}
    case D.FK.mina{}:
      Unit{}

# a store to sx, of a tag of 32 or more and with a longer chain than fr's,
# keeps the frames from fr (hf: the chain from fr)
def frs.st.c(fs: List<&2, D.AF>, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +sx: U32, +sv: Cr.Cir.Cell, +fr: U32, +n: Nat,
  +ht: {U32.is_lt(D.TgW(D.Fd(0n, m, sx)), 32) == False{} : Bool}, +hn: {Hops(n, m, sx) == True{} : Bool},
  +hf: {Hops(List.length(&2, D.AF, fs), m, fr) == True{} : Bool},
  hl: N.Le(1n+List.length(&2, D.AF, fs), n), h: D.Frs(ds, m, im, fi, nx, ks, img, ps, fr, fs)) ->
  D.Frs(ds, Cr.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, ps, fr, fs):
  match fs:
    case Nil{}:
      h
    case Con{D.AF{+kind, +q, +k, +a, +b}, +rest}:
      match h:
        case Tuple{e0, Tuple{ev, Tuple{eo, Tuple{es, Tuple{em, Tuple{etg, Tuple{eq, Tuple{ek, Tuple{ia, Tuple{ib, ir}}}}}}}}}}:
          +M2 = Cr.Cir.Cells.set(m, sx, sv)
          +hl2 = hl
          +ne = hops.ne(1n+List.length(&2, D.AF, rest), n, m, fr, sx, hf, hn, hl2)
          +ec = D.cl.go(m, fr, sx, sv, ne)
          D.frs.uc(ds, M2, im, fi, nx, ks, img, ps, fr, Con{D.AF{kind, q, k, a, b}, rest},
            D.frsc.at(ds, M2, im, fi, nx, ks, img, ps, fr, Cr.Cir.Cells.get(M2, fr), Cr.Cir.Cells.get(m, fr), Con{D.AF{kind, q, k, a, b}, rest}, ec,
              (e0, (ev, (eo, (es, (em, (etg, (eq, (ek,
                (is.keep(a, ds, m, im, fi, nx, ks, img, sx, sv, D.Fd(2n, m, fr), ht, ia),
                (frsb.st(kind, ds, m, im, fi, nx, ks, img, sx, sv, D.Fd(3n, m, fr), b, ht, ib),
                 frs.st.c(rest, ds, m, im, fi, nx, ks, img, ps, sx, sv, D.Fd(1n, m, fr), n, ht, hn,
                   D.and.r(Bool.not(U32.is_eq(fr, 0)), Hops(List.length(&2, D.AF, rest), m, D.Fd(1n, m, fr)), hf),
                   N.weaken(1n+List.length(&2, D.AF, rest), n, hl2), ir)))))))))))))

def frs.st(+fs: List<&2, D.AF>, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +sx: U32, +sv: Cr.Cir.Cell, +fr: U32, +n: Nat,
  +ht: {U32.is_lt(D.TgW(D.Fd(0n, m, sx)), 32) == False{} : Bool}, +hn: {Hops(n, m, sx) == True{} : Bool},
  hl: N.Le(1n+List.length(&2, D.AF, fs), n), +h: D.Frs(ds, m, im, fi, nx, ks, img, ps, fr, fs)) ->
  D.Frs(ds, Cr.Cir.Cells.set(m, sx, sv), im, fi, nx, ks, img, ps, fr, fs):
  frs.st.c(fs, ds, m, im, fi, nx, ks, img, ps, sx, sv, fr, n, ht, hn, frs.hops(fs, ds, m, im, fi, nx, ks, img, ps, fr, h), hl, h)

# The store to the top frame
# --------------------------

# a frame's tag is 32 or more
def fk.lt32(kind: D.FK) -> {U32.is_lt(D.FK.tag(kind), 32) == False{} : Bool}:
  match kind:
    case D.FK.arg{}:
      {==}
    case D.FK.val{}:
      {==}
    case D.FK.fun{}:
      {==}
    case D.FK.let{}:
      {==}
    case D.FK.tupb{}:
      {==}
    case D.FK.tupa{}:
      {==}
    case D.FK.rwt{}:
      {==}
    case D.FK.minb{}:
      {==}
    case D.FK.mina{}:
      {==}

# a term's tag is below 19
def atag.lt(t: Bk.Term) -> {U32.is_lt(D.A.tag(t), 19) == True{} : Bool}:
  match t:
    case Bk.Term.Var{_}:
      {==}
    case Bk.Term.Ref{_}:
      {==}
    case Bk.Term.Ann{_, _}:
      {==}
    case Bk.Term.Let{_, _, _}:
      {==}
    case Bk.Term.Typ{_}:
      {==}
    case Bk.Term.Min{_, _}:
      {==}
    case Bk.Term.All{_, _, _}:
      {==}
    case Bk.Term.Lam{_, _}:
      {==}
    case Bk.Term.App{_, _, _}:
      {==}
    case Bk.Term.Sig{_, _, _}:
      {==}
    case Bk.Term.Tup{_, _, _}:
      {==}
    case Bk.Term.Prj{_}:
      {==}
    case Bk.Term.Enu{_}:
      {==}
    case Bk.Term.Lab{_}:
      {==}
    case Bk.Term.Mat{_, _, _}:
      {==}
    case Bk.Term.Efq{}:
      {==}
    case Bk.Term.Eql{_, _, _}:
      {==}
    case Bk.Term.Rfl{}:
      {==}
    case Bk.Term.Rwt{_, _, _}:
      {==}

# a cell, of the image or the machine's, is below nx
def cell.lt(+c: U32, +im: U32, +fi: U32, +nx: U32, hc: {Cr.Cir.is_cell(c, im, fi, nx) == True{} : Bool},
  +him: {U32.is_lt(im, fi) == True{} : Bool}, +hfn: N.Le(U32.to_nat(fi), U32.to_nat(nx))) -> {U32.is_lt(c, nx) == True{} : Bool}:
  D.or.cases(Bool.and(Bool.not(U32.is_zero(c)), U32.is_le(c, im)), Bool.and(U32.is_le(fi, c), U32.is_lt(c, nx)),
    {U32.is_lt(c, nx) == True{} : Bool}, hc,
    e => u.lt_t(c, nx, N.le_trans(1n+U32.to_nat(c), U32.to_nat(fi), U32.to_nat(nx),
      N.le_trans(1n+U32.to_nat(c), 1n+U32.to_nat(im), U32.to_nat(fi),
        D.u.le(c, im, D.and.r(Bool.not(U32.is_zero(c)), U32.is_le(c, im), e)), D.u.lt(im, fi, him)), hfn)),
    e => D.and.r(U32.is_le(fi, c), U32.is_lt(c, nx), e))

# the parts of a node's facts
def nd.cell(+dk: Bool, -ds: List<&2, Bk.Def>, -im: U32, -fi: U32, -nx: U32, -c: U32, -x: Cr.Cir.Cell, -t: Bk.Term, -tag: U32,
  nd: D.NdK(dk, ds, im, fi, nx, c, x, t, tag)) -> {Cr.Cir.is_cell(c, im, fi, nx) == True{} : Bool}:
  match nd:
    case Tuple{e, _}:
      e

def nd.tglt(+dk: Bool, -ds: List<&2, Bk.Def>, -im: U32, -fi: U32, -nx: U32, -c: U32, +x: Cr.Cir.Cell, +t: Bk.Term,
  nd: D.NdK(dk, ds, im, fi, nx, c, x, t, D.A.tag(t))) -> {U32.is_lt(D.TgW(Cr.Cir.Cell.get(0n, x)), 19) == True{} : Bool}:
  match nd:
    case Tuple{_, Tuple{_, Tuple{etag, _}}}:
      %Equal.sym(U32, D.TgW(Cr.Cir.Cell.get(0n, x)), D.A.tag(t), etag) : {U32.is_lt(_, 19) == True{} : Bool}
      atag.lt(t)

# a node, below nx, is a pointer as LtC says
def ltc.of.nd(+dk: Bool, -ds: List<&2, Bk.Def>, +im: U32, +fi: U32, +nx: U32, +c: U32, +x: Cr.Cir.Cell, +t: Bk.Term,
  nd: D.NdK(dk, ds, im, fi, nx, c, x, t, D.A.tag(t)), hcn: {U32.is_lt(c, nx) == True{} : Bool}) ->
  {D.LtC(c, x, im, fi, nx) == True{} : Bool}:
  match nd:
    case Tuple{ec, Tuple{eo, Tuple{etag, _}}}:
      +f0 = Cr.Cir.Cell.get(0n, x)
      D.and.i(Bool.and(U32.is_lt(c, nx), U32.is_lt(D.TgW(f0), 19)), Bool.and(Cr.Cir.is_cell(c, im, fi, nx), Bool.or(D.Own(fi, nx, c), D.FlW(f0, 1024))),
        D.and.i(U32.is_lt(c, nx), U32.is_lt(D.TgW(f0), 19), hcn,
          (%Equal.sym(U32, D.TgW(f0), D.A.tag(t), etag) : {U32.is_lt(_, 19) == True{} : Bool}; atag.lt(t))),
        D.and.i(Cr.Cir.is_cell(c, im, fi, nx), Bool.or(D.Own(fi, nx, c), D.FlW(f0, 1024)), ec, eo))

# the image is below the machine's first cell
def img.imfi(-ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -m: Cr.Cir.Cells, -im: U32, -fi: U32,
  -nx: U32, io: D.ImgOK(ds, ks, img, m, im, fi, nx)) -> {U32.is_lt(im, fi) == True{} : Bool}:
  match io:
    case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, e}}}}}}}:
      e

# the pointer of a frame out of the pend list, but Rwt: its field 2
def fs.one(+m: Cr.Cir.Cells, +ps: List<&2, U32>, +o: U32, +tg: U32, etag: {D.TgW(D.Fd(0n, m, o)) == tg : U32},
  hlt: {U32.is_lt(tg, 19) == False{} : Bool}, hge: {U32.is_le(32, tg) == True{} : Bool}, hle: {U32.is_le(tg, 40) == True{} : Bool},
  hm: {D.Mem(ps, o) == False{} : Bool}, h38: {U32.is_eq(tg, 38) == False{} : Bool}) ->
  {D.Fs(m, ps, o) == [D.Fd(2n, m, o)] : List<&2, U32>}:
  %h38 : {D.Fs(m, ps, o) == Con{D.Fd(2n, m, o), D.Fs.opt(_, D.Fd(3n, m, o), Nil{})} : List<&2, U32>}
  D.fs.frame(m, ps, o, tg, etag, hlt, hge, hle, hm)

# the top frame's cell after M.swap: the header hd, the old focus in field 2
def sw.cell(+m: Cr.Cir.Cells, +sp: U32, +hd: U32, +foc: U32) -> Cr.Cir.Cell:
  Cr.Cir.Cell{hd, D.Fd(1n, m, sp), foc, D.Fd(3n, m, sp), D.Fd(4n, m, sp)}

# what Inv says of the cells after the store to the top frame sp, of the kind
# kind1, which becomes one of kind2 with the header hd (hsp: sp's chain)
def sw.core.c(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32,
  +im: U32, +focus: Bk.Term, +fs: List<&2, D.AF>, +foc: U32, +sp: U32, +pend: U32, +ps: List<&2, U32>, +kind1: D.FK, +q: Bk.Quan,
  +k: Bool, +a: Bk.Term, +b: Bk.Term, +kind2: D.FK, +q2: Bk.Quan, +hd: U32,
  +htg2: {D.TgW(hd) == D.FK.tag(kind2) : U32}, +hq2: {D.QnW(hd) == Mc.Img.quan(q2) : U32},
  +hst2: {D.FlW(hd, 1024) == False{} : Bool}, +hk2: {D.FlW(hd, 2048) == False{} : Bool},
  +hb1: {U32.is_eq(D.FK.tag(kind1), 38) == False{} : Bool}, +hb2: {U32.is_eq(D.FK.tag(kind2), 38) == False{} : Bool},
  hfb2: D.Frs.b(ds, Cr.Cir.Cells.set(m, sp, sw.cell(m, sp, hd, foc)), im, fi, nx, ks, img, D.Fd(3n, m, sp), kind2, b),
  +isf: D.Is(ds, m, im, fi, nx, ks, img, foc, focus), +hp: D.Heap(m, nx, fi, im, [foc], pend, ps),
  +io: D.ImgOK(ds, ks, img, m, im, fi, nx),
  +hsp: {Hops(1n+List.length(&2, D.AF, fs), m, sp) == True{} : Bool},
  frs: D.Frs(ds, m, im, fi, nx, ks, img, ps, sp, Con{D.AF{kind1, q, k, a, b}, fs})) ->
  D.P2(D.Is(ds, Cr.Cir.Cells.set(m, sp, sw.cell(m, sp, hd, foc)), im, fi, nx, ks, img, D.Fd(2n, m, sp), a),
  D.P2(D.Frs(ds, Cr.Cir.Cells.set(m, sp, sw.cell(m, sp, hd, foc)), im, fi, nx, ks, img, ps, sp, Con{D.AF{kind2, q2, False{}, focus, b}, fs}),
  D.P2(D.Heap(Cr.Cir.Cells.set(m, sp, sw.cell(m, sp, hd, foc)), nx, fi, im, [D.Fd(2n, m, sp)], pend, ps),
    D.ImgOK(ds, ks, img, Cr.Cir.Cells.set(m, sp, sw.cell(m, sp, hd, foc)), im, fi, nx)))):
  match frs:
    case Tuple{e0, Tuple{ev, Tuple{eo, Tuple{es, Tuple{em, Tuple{etg, Tuple{_, Tuple{_, Tuple{ia, Tuple{_, ir}}}}}}}}}}:
      +SV = sw.cell(m, sp, hd, foc)
      +M2 = Cr.Cir.Cells.set(m, sp, SV)
      +eo2 = eo
      +em2 = em
      +etg2 = etg
      +ht = {(%Equal.sym(U32, D.Tg(m, sp), D.FK.tag(kind1), etg2) : {U32.is_lt(_, 32) == False{} : Bool}; fk.lt32(kind1)) :
        {U32.is_lt(D.TgW(D.Fd(0n, m, sp)), 32) == False{} : Bool}}
      +hzt = {(%Equal.sym(U32, D.Tg(m, sp), D.FK.tag(kind1), etg2) : {U32.is_lt(_, 19) == False{} : Bool}; D.fk.lt(kind1)) :
        {U32.is_lt(D.Tg(m, sp), 19) == False{} : Bool}}
      +egs = D.cl.gs(m, sp, SV)
      +hf0 = fs.one(m, ps, sp, D.FK.tag(kind1), etg2, D.fk.lt(kind1), D.fk.ge(kind1), D.fk.le(kind1), em2, hb1)
      +etag2 = {(%Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M2, sp), SV, egs) : {D.TgW(Cr.Cir.Cell.get(0n, _)) == D.FK.tag(kind2) : U32}; htg2) :
        {D.TgW(D.Fd(0n, M2, sp)) == D.FK.tag(kind2) : U32}}
      +hf1 = {(%egs : {D.Fs(M2, ps, sp) == [Cr.Cir.Cell.get(2n, _)] : List<&2, U32>};
        fs.one(M2, ps, sp, D.FK.tag(kind2), etag2, D.fk.lt(kind2), D.fk.ge(kind2), D.fk.le(kind2), em2, hb2)) :
        {D.Fs(M2, ps, sp) == [foc] : List<&2, U32>}}
      +nd = D.is.nd(ds, m, im, fi, nx, ks, img, foc, focus, isf)
      +hfoc = nd.tglt(True{}, ds, im, fi, nx, foc, Cr.Cir.Cells.get(m, foc), focus, nd)
      +nef = tg.ne(m, foc, sp, hfoc, hzt)
      +hfin = N.le_trans(U32.to_nat(fi), U32.to_nat(sp), U32.to_nat(nx), D.u.le(fi, sp, D.and.l(U32.is_le(fi, sp), U32.is_lt(sp, nx), eo2)),
        N.weaken(U32.to_nat(sp), U32.to_nat(nx), D.u.lt(sp, nx, D.and.r(U32.is_le(fi, sp), U32.is_lt(sp, nx), eo2))))
      +hfn = cell.lt(foc, im, fi, nx, nd.cell(True{}, ds, im, fi, nx, foc, Cr.Cir.Cells.get(m, foc), focus, D.A.tag(focus), nd),
        img.imfi(ds, ks, img, m, im, fi, nx, io), hfin)
      +hal = {(%Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M2, foc), Cr.Cir.Cells.get(m, foc), D.cl.go(m, foc, sp, SV, nef)) :
          {Bool.and(D.LtC(foc, _, im, fi, nx), True{}) == True{} : Bool};
        D.and.i(D.LtC(foc, Cr.Cir.Cells.get(m, foc), im, fi, nx), True{},
          ltc.of.nd(True{}, ds, im, fi, nx, foc, Cr.Cir.Cells.get(m, foc), focus, nd, hfn), {==})) :
        {D.Lt.all([foc], M2, im, fi, nx) == True{} : Bool}}
      +hxt = {(%Equal.sym(U32, D.TgW(hd), D.FK.tag(kind2), htg2) : {U32.is_lt(_, 19) == False{} : Bool}; D.fk.lt(kind2)) :
        {U32.is_lt(D.TgW(Cr.Cir.Cell.get(0n, SV)), 19) == False{} : Bool}}
      +hz290 = D.img.hz(True{}, ds, ks, img, m, im, fi, nx, sp, io, eo2)
      +hz0 = ptr.none(m, nx, fi, im, ps, pend, foc, sp, hzt, hfoc, hp)
      (is.keep(a, ds, m, im, fi, nx, ks, img, sp, SV, D.Fd(2n, m, sp), ht, ia),
      (D.frs.uc(ds, M2, im, fi, nx, ks, img, ps, sp, Con{D.AF{kind2, q2, False{}, focus, b}, fs},
        D.frsc.at(ds, M2, im, fi, nx, ks, img, ps, sp, Cr.Cir.Cells.get(M2, sp), SV, Con{D.AF{kind2, q2, False{}, focus, b}, fs}, egs,
          (e0, (ev, (eo2, (hst2, (em2, (htg2, (hq2, (hk2, (is.keep(focus, ds, m, im, fi, nx, ks, img, sp, SV, foc, ht, isf), (hfb2,
            frs.st.c(fs, ds, m, im, fi, nx, ks, img, ps, sp, SV, D.Fd(1n, m, sp), 1n+List.length(&2, D.AF, fs), ht, hsp,
              D.and.r(Bool.not(U32.is_eq(sp, 0)), Hops(List.length(&2, D.AF, fs), m, D.Fd(1n, m, sp)), hsp),
              N.le_refl(1n+List.length(&2, D.AF, fs)), ir))))))))))))),
      (Heap.sw(m, nx, fi, im, pend, ps, sp, SV, foc, D.Fd(2n, m, sp), hf0, hf1, eo2, hz290, em2, hzt, hxt, hal, hp),
        D.ImgOK.fz(True{}, ds, ks, img, m, im, fi, nx, ps, [foc], sp, SV, hz0, es, eo2, io))))

def sw.core(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32,
  +im: U32, +focus: Bk.Term, +fs: List<&2, D.AF>, +foc: U32, +sp: U32, +pend: U32, +ps: List<&2, U32>, +kind1: D.FK, +q: Bk.Quan,
  +k: Bool, +a: Bk.Term, +b: Bk.Term, +kind2: D.FK, +q2: Bk.Quan, +hd: U32,
  +htg2: {D.TgW(hd) == D.FK.tag(kind2) : U32}, +hq2: {D.QnW(hd) == Mc.Img.quan(q2) : U32},
  +hst2: {D.FlW(hd, 1024) == False{} : Bool}, +hk2: {D.FlW(hd, 2048) == False{} : Bool},
  +hb1: {U32.is_eq(D.FK.tag(kind1), 38) == False{} : Bool}, +hb2: {U32.is_eq(D.FK.tag(kind2), 38) == False{} : Bool},
  hfb2: D.Frs.b(ds, Cr.Cir.Cells.set(m, sp, sw.cell(m, sp, hd, foc)), im, fi, nx, ks, img, D.Fd(3n, m, sp), kind2, b),
  +isf: D.Is(ds, m, im, fi, nx, ks, img, foc, focus), +hp: D.Heap(m, nx, fi, im, [foc], pend, ps),
  +io: D.ImgOK(ds, ks, img, m, im, fi, nx),
  +frs: D.Frs(ds, m, im, fi, nx, ks, img, ps, sp, Con{D.AF{kind1, q, k, a, b}, fs})) ->
  D.P2(D.Is(ds, Cr.Cir.Cells.set(m, sp, sw.cell(m, sp, hd, foc)), im, fi, nx, ks, img, D.Fd(2n, m, sp), a),
  D.P2(D.Frs(ds, Cr.Cir.Cells.set(m, sp, sw.cell(m, sp, hd, foc)), im, fi, nx, ks, img, ps, sp, Con{D.AF{kind2, q2, False{}, focus, b}, fs}),
  D.P2(D.Heap(Cr.Cir.Cells.set(m, sp, sw.cell(m, sp, hd, foc)), nx, fi, im, [D.Fd(2n, m, sp)], pend, ps),
    D.ImgOK(ds, ks, img, Cr.Cir.Cells.set(m, sp, sw.cell(m, sp, hd, foc)), im, fi, nx)))):
  sw.core.c(ds, ks, img, m, nx, fi, im, focus, fs, foc, sp, pend, ps, kind1, q, k, a, b, kind2, q2, hd, htg2, hq2, hst2, hk2, hb1, hb2,
    hfb2, isf, hp, io, frs.hops(Con{D.AF{kind1, q, k, a, b}, fs}, ds, m, im, fi, nx, ks, img, ps, sp, frs), frs)


# The run of M.swap
# -----------------
#
# From mode 1, with the top frame sp: M.ret's tests take the frame's branch,
# then M.swap gives the frame the header hd and the focus foc, and the focus
# and register n the frame's field 2 (sw.hdr, sw.app.E). The registers then
# are those of R59.sw, and the cells one store (sw.mem).

# a frame of App q □ x: app_arg or app_val
def sw.isapp(k: D.FK) -> Bool:
  match k:
    case D.FK.arg{}:
      True{}
    case D.FK.val{}:
      True{}
    case _:
      False{}

# the header of a frame's kind k2, with the quantity qv and no flag
def sw.hd(+k2: U32, +qv: U32) -> U32:
  Wa.Wasm.op(Wa.Wasm.Op.or{}, Wa.Wasm.op(Wa.Wasm.Op.or{}, k2, Wa.Wasm.op(Wa.Wasm.Op.shl{}, qv, 6)), 0)

# the registers after M.ret's tests and M.swap: h, tag, q and n set, the focus n and mode 0
def R59.sw(x: D.R59, +sp: U32, +T: U32, +Q: U32, +n: U32) -> D.R59:
  match x:
    case D.R59{+r4, +r5, +r6, +r7, +r8, +r9, +r10, +r11, +r12, +r13, +r14, +r15, +r16, +r17, +r18, +r19, +r20, +r21, +r22, +r23, +r24, +r25, +r26, +r27, +r28, +r29, +r30, +r31, +r32, +r33, +r34, +r35, +r36, +r37, +r38, +r39, +r40, +r41, +r42, +r43, +r44, +r45, +r46, +r47, +r48, +r49, +r50, +r51, +r52, +r53, +r54, +r55, +r56, +r57, +r58, +r59, +r60, +r61, +r62}:
      D.R59{r4, r5, r6, r7, r8, sp, T, r11, r12, r13, Q, n, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}

def sw.regs(x: D.R59, +foc: U32, +sp: U32, +pend: U32, +T: U32, +Q: U32, +n: U32) ->
  {X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(x)), 9n, sp), 10n, T), 14n, Q), 15n, n), 0n, n), 1n, 0) ==
    D.RG(n, 0, sp, pend, D.R59.list(R59.sw(x, sp, T, Q, n))) : List<&2, U32>}:
  match x:
    case D.R59{+r4, +r5, +r6, +r7, +r8, +r9, +r10, +r11, +r12, +r13, +r14, +r15, +r16, +r17, +r18, +r19, +r20, +r21, +r22, +r23, +r24, +r25, +r26, +r27, +r28, +r29, +r30, +r31, +r32, +r33, +r34, +r35, +r36, +r37, +r38, +r39, +r40, +r41, +r42, +r43, +r44, +r45, +r46, +r47, +r48, +r49, +r50, +r51, +r52, +r53, +r54, +r55, +r56, +r57, +r58, +r59, +r60, +r61, +r62}:
      {==}

def rg.len(x: D.R59, +foc: U32, +md: U32, +sp: U32, +pend: U32) -> {List.length(&2, U32, D.RG(foc, md, sp, pend, D.R59.list(x))) == 63n : Nat}:
  match x:
    case D.R59{+r4, +r5, +r6, +r7, +r8, +r9, +r10, +r11, +r12, +r13, +r14, +r15, +r16, +r17, +r18, +r19, +r20, +r21, +r22, +r23, +r24, +r25, +r26, +r27, +r28, +r29, +r30, +r31, +r32, +r33, +r34, +r35, +r36, +r37, +r38, +r39, +r40, +r41, +r42, +r43, +r44, +r45, +r46, +r47, +r48, +r49, +r50, +r51, +r52, +r53, +r54, +r55, +r56, +r57, +r58, +r59, +r60, +r61, +r62}:
      {==}

# M.swap's two stores to sp are one
def sw.cell.eq(y: Cr.Cir.Cell, +hd: U32, +foc: U32) ->
  {Cr.Cir.Cell.set(2n, Cr.Cir.Cell.set(0n, y, hd), foc) == Cr.Cir.Cell{hd, Cr.Cir.Cell.get(1n, y), foc, Cr.Cir.Cell.get(3n, y), Cr.Cir.Cell.get(4n, y)} : Cr.Cir.Cell}:
  match y:
    case Cr.Cir.Cell{_, _, _, _, _}:
      {==}

def sw.mem(+m: Cr.Cir.Cells, +sp: U32, +hd: U32, +foc: U32) ->
  {X.X.put(X.X.put(m, 0n, sp, hd), 2n, sp, foc) == Cr.Cir.Cells.set(m, sp, sw.cell(m, sp, hd, foc)) : Cr.Cir.Cells}:
  +c1 = Cr.Cir.Cell.set(0n, Cr.Cir.Cells.get(m, sp), hd)
  Equal.trans(Cr.Cir.Cells, X.X.put(X.X.put(m, 0n, sp, hd), 2n, sp, foc), Cr.Cir.Cells.set(m, sp, Cr.Cir.Cell.set(2n, c1, foc)),
    Cr.Cir.Cells.set(m, sp, sw.cell(m, sp, hd, foc)),
    Equal.sym(Cr.Cir.Cells, Cr.Cir.Cells.set(m, sp, Cr.Cir.Cell.set(2n, c1, foc)), X.X.put(X.X.put(m, 0n, sp, hd), 2n, sp, foc),
      X.Ce.put_set(m, sp, c1, 2n, foc)),
    Equal.cong(Cr.Cir.Cell, Cr.Cir.Cells, y => Cr.Cir.Cells.set(m, sp, y), Cr.Cir.Cell.set(2n, c1, foc), sw.cell(m, sp, hd, foc),
      sw.cell.eq(Cr.Cir.Cells.get(m, sp), hd, foc)))

# M.swap with the header of the kind k2 and the frame's quantity (register q)
def sw.hdr(+f: Nat, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>,
  +sp: U32, +foc: U32, +T: U32, +k2: U32, +qv: U32, +hl: {List.length(&2, U32, regs) == 63n : Nat},
  h0: {List.get(&2, U32, regs, 0n) == Some{foc} : Maybe<&2, U32>}, hc: {Cr.Cir.is_cell(sp, im, fi, nx) == True{} : Bool},
  hq: {U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3) == qv : U32}) ->
  {Cr.Cir.exec(f, Mc.M.swap(Mc.M.header(k2, Mc.M.g(14n), Mc.M.c(0))), X.ret.st(regs, m, nx, fi, im, pg, lim, inp, sp, T)) ==
    Cr.Cir.Out.next{X.X.st(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(regs, 9n, sp), 10n, T), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)),
      15n, D.Fd(2n, m, sp)), 0n, D.Fd(2n, m, sp)), 1n, 0), X.X.put(X.X.put(m, 0n, sp, sw.hd(k2, qv)), 2n, sp, foc), nx, fi, im, pg, lim, inp)} : Cr.Cir.Out}:
  +Q = U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)
  +n = D.Fd(2n, m, sp)
  +r1 = X.X.set(regs, 9n, sp)
  +r2 = X.X.set(r1, 10n, T)
  +r3 = X.X.set(r2, 14n, Q)
  +l2 = X.L.len(r1, 10n, T, 63n, X.L.len(regs, 9n, sp, 63n, hl))
  +l3 = X.L.len(r2, 14n, Q, 63n, l2)
  +g0 = X.L.go(r2, 14n, 0n, Q, foc, {==}, X.L.go(r1, 10n, 0n, T, foc, {==}, X.L.go(regs, 9n, 0n, sp, foc, {==}, h0)))
  +g9 = X.L.go(r2, 14n, 9n, Q, sp, {==}, X.L.go(r1, 10n, 9n, T, sp, {==}, X.L.gs(regs, 9n, sp, X.L.lt(regs, 9n, hl, {==}))))
  +g14 = X.L.go(r3, 15n, 14n, n, Q, {==}, X.L.gs(r2, 14n, Q, X.L.lt(r2, 14n, l2, {==})))
  +st15 = X.X.st(X.X.set(r3, 15n, n), m, nx, fi, im, pg, lim, inp)
  +ehd = X.ev.op(Wa.Wasm.Op.or{}, Mc.M.or(Mc.M.c(k2), Mc.M.shl(Mc.M.g(14n), Mc.M.c(6))), Mc.M.c(0), st15,
    Wa.Wasm.op(Wa.Wasm.Op.or{}, k2, Wa.Wasm.op(Wa.Wasm.Op.shl{}, Q, 6)), 0,
    X.ev.op(Wa.Wasm.Op.or{}, Mc.M.c(k2), Mc.M.shl(Mc.M.g(14n), Mc.M.c(6)), st15, k2, Wa.Wasm.op(Wa.Wasm.Op.shl{}, Q, 6), {==},
      X.ev.op(Wa.Wasm.Op.shl{}, Mc.M.g(14n), Mc.M.c(6), st15, Q, 6, g14, {==})), {==})
  %hq : {Cr.Cir.exec(f, Mc.M.swap(Mc.M.header(k2, Mc.M.g(14n), Mc.M.c(0))), X.X.st(r3, m, nx, fi, im, pg, lim, inp)) ==
    Cr.Cir.Out.next{X.X.st(X.X.set(X.X.set(X.X.set(r3, 15n, n), 0n, n), 1n, 0), X.X.put(X.X.put(m, 0n, sp, sw.hd(k2, _)), 2n, sp, foc), nx, fi, im, pg, lim, inp)} : Cr.Cir.Out}
  X.swap.eq(f, r3, m, nx, fi, im, pg, lim, inp, sp, foc, Mc.M.header(k2, Mc.M.g(14n), Mc.M.c(0)), sw.hd(k2, Q), l3, g0, g9, hc, ehd)

# M.ret's tests, to an App q □ x frame: its branch
def sw.disp(+f: Nat, kind: D.FK, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32,
  +inp: List<&2, Word(8n)>, +sp: U32, hk: {sw.isapp(kind) == True{} : Bool}, hl: {List.length(&2, U32, regs) == 63n : Nat},
  h1: {List.get(&2, U32, regs, 1n) == Some{1} : Maybe<&2, U32>}, h2: {List.get(&2, U32, regs, 2n) == Some{sp} : Maybe<&2, U32>},
  hz: {U32.is_eq(sp, 0) == False{} : Bool}, hc: {Cr.Cir.is_cell(sp, im, fi, nx) == True{} : Bool},
  ht: {U32.and(Cr.Cir.Cell.get(0n, Cr.Cir.Cells.get(m, sp)), 63) == D.FK.tag(kind) : U32}) ->
  {Cr.Cir.exec(f, X.X.body(), X.X.st(regs, m, nx, fi, im, pg, lim, inp)) ==
    Cr.Cir.exec(f, X.sel.t(X.X.chain(0n)), X.ret.st(regs, m, nx, fi, im, pg, lim, inp, sp, D.FK.tag(kind))) : Cr.Cir.Out}:
  match kind:
    case D.FK.arg{}:
      X.ret.disp.app(f, regs, m, nx, fi, im, pg, lim, inp, sp, hl, h1, h2, hz, hc, ht)
    case D.FK.val{}:
      X.ret.disp.val(f, regs, m, nx, fi, im, pg, lim, inp, sp, hl, h1, h2, hz, hc, ht)
    case D.FK.fun{}:
      D.bool.ft({Cr.Cir.exec(f, X.X.body(), X.X.st(regs, m, nx, fi, im, pg, lim, inp)) ==
        Cr.Cir.exec(f, X.sel.t(X.X.chain(0n)), X.ret.st(regs, m, nx, fi, im, pg, lim, inp, sp, 34)) : Cr.Cir.Out}, hk)
    case D.FK.let{}:
      D.bool.ft({Cr.Cir.exec(f, X.X.body(), X.X.st(regs, m, nx, fi, im, pg, lim, inp)) ==
        Cr.Cir.exec(f, X.sel.t(X.X.chain(0n)), X.ret.st(regs, m, nx, fi, im, pg, lim, inp, sp, 35)) : Cr.Cir.Out}, hk)
    case D.FK.tupb{}:
      D.bool.ft({Cr.Cir.exec(f, X.X.body(), X.X.st(regs, m, nx, fi, im, pg, lim, inp)) ==
        Cr.Cir.exec(f, X.sel.t(X.X.chain(0n)), X.ret.st(regs, m, nx, fi, im, pg, lim, inp, sp, 36)) : Cr.Cir.Out}, hk)
    case D.FK.tupa{}:
      D.bool.ft({Cr.Cir.exec(f, X.X.body(), X.X.st(regs, m, nx, fi, im, pg, lim, inp)) ==
        Cr.Cir.exec(f, X.sel.t(X.X.chain(0n)), X.ret.st(regs, m, nx, fi, im, pg, lim, inp, sp, 37)) : Cr.Cir.Out}, hk)
    case D.FK.rwt{}:
      D.bool.ft({Cr.Cir.exec(f, X.X.body(), X.X.st(regs, m, nx, fi, im, pg, lim, inp)) ==
        Cr.Cir.exec(f, X.sel.t(X.X.chain(0n)), X.ret.st(regs, m, nx, fi, im, pg, lim, inp, sp, 38)) : Cr.Cir.Out}, hk)
    case D.FK.minb{}:
      D.bool.ft({Cr.Cir.exec(f, X.X.body(), X.X.st(regs, m, nx, fi, im, pg, lim, inp)) ==
        Cr.Cir.exec(f, X.sel.t(X.X.chain(0n)), X.ret.st(regs, m, nx, fi, im, pg, lim, inp, sp, 39)) : Cr.Cir.Out}, hk)
    case D.FK.mina{}:
      D.bool.ft({Cr.Cir.exec(f, X.X.body(), X.X.st(regs, m, nx, fi, im, pg, lim, inp)) ==
        Cr.Cir.exec(f, X.sel.t(X.X.chain(0n)), X.ret.st(regs, m, nx, fi, im, pg, lim, inp, sp, 40)) : Cr.Cir.Out}, hk)

# a round from mode 1 with an App q □ x frame on top, q live, x not known: M.swap
def sw.app.E(+f: Nat, +kind: D.FK, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32,
  +inp: List<&2, Word(8n)>, +sp: U32, +foc: U32, +qv: U32, +hk: {sw.isapp(kind) == True{} : Bool}, +hl: {List.length(&2, U32, regs) == 63n : Nat},
  +h0: {List.get(&2, U32, regs, 0n) == Some{foc} : Maybe<&2, U32>},
  h1: {List.get(&2, U32, regs, 1n) == Some{1} : Maybe<&2, U32>}, h2: {List.get(&2, U32, regs, 2n) == Some{sp} : Maybe<&2, U32>},
  hz: {U32.is_eq(sp, 0) == False{} : Bool}, +hc: {Cr.Cir.is_cell(sp, im, fi, nx) == True{} : Bool},
  ht: {U32.and(Cr.Cir.Cell.get(0n, Cr.Cir.Cells.get(m, sp)), 63) == D.FK.tag(kind) : U32},
  +hq: {U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3) == qv : U32},
  hkn: {U32.is_ne(U32.and(D.Fd(0n, m, sp), 2048), 0) == False{} : Bool},
  nz: {U32.is_zero(Wa.Wasm.op(Wa.Wasm.Op.and{}, Wa.Wasm.op(Wa.Wasm.Op.ne{}, qv, 0), Bool.to_u32(U32.is_zero(Bool.to_u32(False{}))))) == False{} : Bool}) ->
  {Cr.Cir.exec(f, X.X.body(), X.X.st(regs, m, nx, fi, im, pg, lim, inp)) ==
    Cr.Cir.Out.next{X.X.st(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(regs, 9n, sp), 10n, D.FK.tag(kind)), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)),
      15n, D.Fd(2n, m, sp)), 0n, D.Fd(2n, m, sp)), 1n, 0), X.X.put(X.X.put(m, 0n, sp, sw.hd(34, qv)), 2n, sp, foc), nx, fi, im, pg, lim, inp)} : Cr.Cir.Out}:
  +T = D.FK.tag(kind)
  +Q = U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)
  +s3 = X.ret.st(regs, m, nx, fi, im, pg, lim, inp, sp, T)
  +r1 = X.X.set(regs, 9n, sp)
  +r2 = X.X.set(r1, 10n, T)
  +l2 = X.L.len(r1, 10n, T, 63n, X.L.len(regs, 9n, sp, 63n, hl))
  +g9 = X.L.go(r2, 14n, 9n, Q, sp, {==}, X.L.go(r1, 10n, 9n, T, sp, {==}, X.L.gs(regs, 9n, sp, X.L.lt(regs, 9n, hl, {==}))))
  +g14 = X.L.gs(r2, 14n, Q, X.L.lt(r2, 14n, l2, {==}))
  +T0 = X.sel.t(X.X.chain(0n))
  +v = Wa.Wasm.op(Wa.Wasm.Op.and{}, Wa.Wasm.op(Wa.Wasm.Op.ne{}, Q, 0), Bool.to_u32(U32.is_zero(Bool.to_u32(False{}))))
  +ev = X.ev.op(Wa.Wasm.Op.and{}, Mc.M.ne(Mc.M.g(14n), Mc.M.c(0)), Mc.M.not(Mc.M.flag(Mc.M.g(9n), 2048)), s3,
    Wa.Wasm.op(Wa.Wasm.Op.ne{}, Q, 0), Bool.to_u32(U32.is_zero(Bool.to_u32(False{}))),
    X.ev.op(Wa.Wasm.Op.ne{}, Mc.M.g(14n), Mc.M.c(0), s3, Q, 0, g14, {==}),
    X.ev.notflag(9n, s3, sp, 2048, False{}, g9, hc, hkn))
  +nzQ = {(%Equal.sym(U32, Q, qv, hq) : {U32.is_zero(Wa.Wasm.op(Wa.Wasm.Op.and{}, Wa.Wasm.op(Wa.Wasm.Op.ne{}, _, 0), Bool.to_u32(U32.is_zero(Bool.to_u32(False{}))))) == False{} : Bool}; nz) :
    {U32.is_zero(v) == False{} : Bool}}
  +RES = {Cr.Cir.Out.next{X.X.st(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(regs, 9n, sp), 10n, T), 14n, Q),
      15n, D.Fd(2n, m, sp)), 0n, D.Fd(2n, m, sp)), 1n, 0), X.X.put(X.X.put(m, 0n, sp, sw.hd(34, qv)), 2n, sp, foc), nx, fi, im, pg, lim, inp)} : Cr.Cir.Out}
  +SW = Mc.M.swap(Mc.M.header(34, Mc.M.g(14n), Mc.M.c(0)))
  Equal.trans(Cr.Cir.Out, Cr.Cir.exec(f, X.X.body(), X.X.st(regs, m, nx, fi, im, pg, lim, inp)), Cr.Cir.exec(f, T0, s3), RES,
    sw.disp(f, kind, regs, m, nx, fi, im, pg, lim, inp, sp, hk, hl, h1, h2, hz, hc, ht),
    Equal.trans(Cr.Cir.Out, Cr.Cir.exec(f, T0, s3), Cr.Cir.exec(f, SW, s3), RES,
      Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, X.sel.t(T0), s3), Cr.Cir.exec(f, Cr.Cir.Stmt.if{X.sel.c(T0), X.sel.t(T0), X.sel.e(T0)}, s3),
        X.rw.if.t(f, X.sel.c(T0), X.sel.t(T0), X.sel.e(T0), s3, v, ev, nzQ)),
      sw.hdr(f, regs, m, nx, fi, im, pg, lim, inp, sp, foc, T, 34, qv, hl, h0, hc, hq)))

# The moves
# ---------

# a move from st (moves.bend's MV)
def sw.MV(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +st: Cr.Cir.State, +t: Bk.Term, +w: Nat) ->
  Type:
  (@f: Nat -> D.Post(False{}, Cr.Cir.exec(f, D.B.body(), st), s => D.Rnd(ds, ks, img, t, w, s), s => st2 => D.HR(ds, t, s, st2))) &
    D.Ex(Nat, f => D.Ends(Cr.Cir.exec(f, D.B.body(), st)))

# a round that goes to st2, for any fuel, where Inv holds of the same term
# with a smaller measure: an admin move
def sw.adm(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +st: Cr.Cir.State, +st2: Cr.Cir.State,
  +t: Bk.Term, +w: Nat, +w2: Nat, hE: @f: Nat -> {Cr.Cir.exec(f, D.B.body(), st) == Cr.Cir.Out.next{st2} : Cr.Cir.Out},
  hE0: {Cr.Cir.exec(0n, D.B.body(), st) == Cr.Cir.Out.next{st2} : Cr.Cir.Out}, +inv: D.Inv(ds, ks, img, st2, t, w2),
  +lt: N.Le(1n+w2, w)) -> sw.MV(ds, ks, img, st, t, w):
  (f => (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, D.B.body(), st), Cr.Cir.Out.next{st2}, hE(f)) :
      D.Post(False{}, _, s => D.Rnd(ds, ks, img, t, w, s), s => st3 => D.HR(ds, t, s, st3));
      Inl{(w2, (inv, lt))}),
   (0n, (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec(0n, D.B.body(), st), Cr.Cir.Out.next{st2}, hE0) : D.Ends(_); Unit{})))

# the facts of the top frame
def fr.nz(+ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +ps: List<&2, U32>, +sp: U32, +kind: D.FK, +q: Bk.Quan, +k: Bool, +a: Bk.Term, +b: Bk.Term, +fs: List<&2, D.AF>,
  h: D.Frs(ds, m, im, fi, nx, ks, img, ps, sp, Con{D.AF{kind, q, k, a, b}, fs})) -> {U32.is_eq(sp, 0) == False{} : Bool}:
  match h:
    case Tuple{e, _}:
      e

def fr.cell(+ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +ps: List<&2, U32>, +sp: U32, +kind: D.FK, +q: Bk.Quan, +k: Bool, +a: Bk.Term, +b: Bk.Term, +fs: List<&2, D.AF>,
  h: D.Frs(ds, m, im, fi, nx, ks, img, ps, sp, Con{D.AF{kind, q, k, a, b}, fs})) -> {Cr.Cir.is_cell(sp, im, fi, nx) == True{} : Bool}:
  match h:
    case Tuple{_, Tuple{e, _}}:
      e

def fr.tag(+ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +ps: List<&2, U32>, +sp: U32, +kind: D.FK, +q: Bk.Quan, +k: Bool, +a: Bk.Term, +b: Bk.Term, +fs: List<&2, D.AF>,
  h: D.Frs(ds, m, im, fi, nx, ks, img, ps, sp, Con{D.AF{kind, q, k, a, b}, fs})) -> {D.Tg(m, sp) == D.FK.tag(kind) : U32}:
  match h:
    case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}:
      e

def fr.q(+ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +ps: List<&2, U32>, +sp: U32, +kind: D.FK, +q: Bk.Quan, +k: Bool, +a: Bk.Term, +b: Bk.Term, +fs: List<&2, D.AF>,
  h: D.Frs(ds, m, im, fi, nx, ks, img, ps, sp, Con{D.AF{kind, q, k, a, b}, fs})) -> D.Qs(Cr.Cir.Cells.get(m, sp), q):
  match h:
    case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}:
      e

def fr.k(+ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +ps: List<&2, U32>, +sp: U32, +kind: D.FK, +q: Bk.Quan, +k: Bool, +a: Bk.Term, +b: Bk.Term, +fs: List<&2, D.AF>,
  h: D.Frs(ds, m, im, fi, nx, ks, img, ps, sp, Con{D.AF{kind, q, k, a, b}, fs})) -> {D.Fl(m, sp, 2048) == k : Bool}:
  match h:
    case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e, _}}}}}}}}:
      e

# what an App q □ x frame is
def sw.plug(kind: D.FK, hk: {sw.isapp(kind) == True{} : Bool}, +q: Bk.Quan, +k: Bool, +a: Bk.Term, +b: Bk.Term, +v: Bk.Term) ->
  {D.A.plug(D.AF{kind, q, k, a, b}, v) == Bk.Term.App{q, v, a} : Bk.Term}:
  match kind:
    case D.FK.arg{}:
      {==}
    case D.FK.val{}:
      {==}
    case D.FK.fun{}:
      D.bool.ft({Bk.Term.App{q, a, v} == Bk.Term.App{q, v, a} : Bk.Term}, hk)
    case D.FK.let{}:
      D.bool.ft({Bk.Term.Let{q, v, a} == Bk.Term.App{q, v, a} : Bk.Term}, hk)
    case D.FK.tupb{}:
      D.bool.ft({Bk.Term.Tup{q, v, a} == Bk.Term.App{q, v, a} : Bk.Term}, hk)
    case D.FK.tupa{}:
      D.bool.ft({Bk.Term.Tup{q, a, v} == Bk.Term.App{q, v, a} : Bk.Term}, hk)
    case D.FK.rwt{}:
      D.bool.ft({Bk.Term.Rwt{v, a, b} == Bk.Term.App{q, v, a} : Bk.Term}, hk)
    case D.FK.minb{}:
      D.bool.ft({Bk.Term.Min{v, a} == Bk.Term.App{q, v, a} : Bk.Term}, hk)
    case D.FK.mina{}:
      D.bool.ft({Bk.Term.Min{a, v} == Bk.Term.App{q, v, a} : Bk.Term}, hk)

def sw.w(kind: D.FK, hk: {sw.isapp(kind) == True{} : Bool}, +q: Bk.Quan, +a: Bk.Term, +b: Bk.Term, +hlv: {El.Quan.live(q) == True{} : Bool}) ->
  {D.A.w.frame(D.AF{kind, q, False{}, a, b}) == 2n+D.A.w3(a) : Nat}:
  match kind:
    case D.FK.arg{}:
      %Equal.sym(Bool, El.Quan.live(q), True{}, hlv) : {Bool.pick(Nat, Bool.and(_, Bool.not(False{})), 2n+D.A.w3(a), 1n) == 2n+D.A.w3(a) : Nat}
      {==}
    case D.FK.val{}:
      %Equal.sym(Bool, El.Quan.live(q), True{}, hlv) : {Bool.pick(Nat, Bool.and(_, Bool.not(False{})), 2n+D.A.w3(a), 1n) == 2n+D.A.w3(a) : Nat}
      {==}
    case D.FK.fun{}:
      D.bool.ft({1n == 2n+D.A.w3(a) : Nat}, hk)
    case D.FK.let{}:
      D.bool.ft({0n == 2n+D.A.w3(a) : Nat}, hk)
    case D.FK.tupb{}:
      D.bool.ft({2n+D.A.w3(a) == 2n+D.A.w3(a) : Nat}, hk)
    case D.FK.tupa{}:
      D.bool.ft({1n == 2n+D.A.w3(a) : Nat}, hk)
    case D.FK.rwt{}:
      D.bool.ft({0n == 2n+D.A.w3(a) : Nat}, hk)
    case D.FK.minb{}:
      D.bool.ft({1n+D.A.w3(a) == 2n+D.A.w3(a) : Nat}, hk)
    case D.FK.mina{}:
      D.bool.ft({0n == 2n+D.A.w3(a) : Nat}, hk)

def sw.not38(kind: D.FK, hk: {sw.isapp(kind) == True{} : Bool}) -> {U32.is_eq(D.FK.tag(kind), 38) == False{} : Bool}:
  match kind:
    case D.FK.arg{}:
      {==}
    case D.FK.val{}:
      {==}
    case D.FK.fun{}:
      {==}
    case D.FK.let{}:
      {==}
    case D.FK.tupb{}:
      {==}
    case D.FK.tupa{}:
      {==}
    case D.FK.rwt{}:
      D.bool.ft({True{} == False{} : Bool}, hk)
    case D.FK.minb{}:
      {==}
    case D.FK.mina{}:
      {==}

# Inv after a swap: a to evaluate, in the frames fr2, from the facts of the cells m2
def sw.inv(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m2: Cr.Cir.Cells, +nx: U32, +fi: U32,
  +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +a: Bk.Term, +fr2: List<&2, D.AF>, +n: U32, +sp: U32, +pend: U32,
  +ps: List<&2, U32>, +rest2: D.R59, et2: {D.A.plugs(fr2, a) == t : Bk.Term}, afs2: D.AFs.ok(ds, fr2),
  core: D.P2(D.Is(ds, m2, im, fi, nx, ks, img, n, a), D.P2(D.Frs(ds, m2, im, fi, nx, ks, img, ps, sp, fr2),
    D.P2(D.Heap(m2, nx, fi, im, [n], pend, ps), D.ImgOK(ds, ks, img, m2, im, fi, nx))))) ->
  D.Inv(ds, ks, img, D.S(n, 0, sp, pend, rest2, m2, nx, fi, im, pg, lim, inp), t, D.A.w(False{}, a, fr2)):
  match core:
    case Tuple{isa, Tuple{frs2, Tuple{heap2, img2}}}:
      (D.Wit{False{}, a, fr2, n, sp, pend, ps, rest2},
        (et2, ({==}, ({==}, (afs2, ({==}, (isa, (frs2, (heap2, (img2, ({==}, {==})))))))))))

# the round of the App swap, to the state of Inv
def sw.app.E2(+f: Nat, +foc: U32, +sp: U32, +pend: U32, +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32,
  +lim: U32, +inp: List<&2, Word(8n)>, +kind: D.FK, +q: Bk.Quan, +hk: {sw.isapp(kind) == True{} : Bool},
  +hz: {U32.is_eq(sp, 0) == False{} : Bool}, +hc: {Cr.Cir.is_cell(sp, im, fi, nx) == True{} : Bool},
  +ht: {D.Tg(m, sp) == D.FK.tag(kind) : U32}, +hq: D.Qs(Cr.Cir.Cells.get(m, sp), q), +hkn: {D.Fl(m, sp, 2048) == False{} : Bool},
  +nz: {U32.is_zero(Wa.Wasm.op(Wa.Wasm.Op.and{}, Wa.Wasm.op(Wa.Wasm.Op.ne{}, Mc.Img.quan(q), 0), Bool.to_u32(U32.is_zero(Bool.to_u32(False{}))))) == False{} : Bool}) ->
  {Cr.Cir.exec(f, D.B.body(), D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)) ==
    Cr.Cir.Out.next{D.S(D.Fd(2n, m, sp), 0, sp, pend, R59.sw(rest, sp, D.FK.tag(kind), U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3), D.Fd(2n, m, sp)),
      Cr.Cir.Cells.set(m, sp, sw.cell(m, sp, sw.hd(34, Mc.Img.quan(q)), foc)), nx, fi, im, pg, lim, inp)} : Cr.Cir.Out}:
  +regs = D.RG(foc, 1, sp, pend, D.R59.list(rest))
  +T = D.FK.tag(kind)
  +Q = U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)
  +n = D.Fd(2n, m, sp)
  +HD = sw.hd(34, Mc.Img.quan(q))
  +M2 = Cr.Cir.Cells.set(m, sp, sw.cell(m, sp, HD, foc))
  +R2 = X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(regs, 9n, sp), 10n, T), 14n, Q), 15n, n), 0n, n), 1n, 0)
  %sw.regs(rest, foc, sp, pend, T, Q, n) :
    {Cr.Cir.exec(f, D.B.body(), D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)) ==
      Cr.Cir.Out.next{Cr.Cir.State{_, M2, nx, fi, im, pg, lim, inp, Nil{}, 0}} : Cr.Cir.Out}
  %sw.mem(m, sp, HD, foc) :
    {Cr.Cir.exec(f, D.B.body(), D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)) ==
      Cr.Cir.Out.next{Cr.Cir.State{R2, _, nx, fi, im, pg, lim, inp, Nil{}, 0}} : Cr.Cir.Out}
  sw.app.E(f, kind, regs, m, nx, fi, im, pg, lim, inp, sp, foc, Mc.Img.quan(q), hk, rg.len(rest, foc, 1, sp, pend), {==}, {==}, {==},
    hz, hc, ht, hq, hkn, nz)

# mode 1, App q □ a with q live and a not known: a to evaluate, in the frame App q v □
def sw.app.go(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32,
  +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat,
  +fs: List<&2, D.AF>, +ps: List<&2, U32>, +focus: Bk.Term, +kind: D.FK, +q: Bk.Quan, +a: Bk.Term, +b: Bk.Term,
  iv: D.InvOf(ds, ks, img, D.RG(foc, 1, sp, pend, D.R59.list(rest)), m, nx, fi, im, Nil{}, 0, t, w, True{}, focus,
    Con{D.AF{kind, q, False{}, a, b}, fs}, foc, sp, pend, ps, rest),
  +hk: {sw.isapp(kind) == True{} : Bool}, +hlv: {El.Quan.live(q) == True{} : Bool},
  +htg2: {D.TgW(sw.hd(34, Mc.Img.quan(q))) == 34 : U32}, +hq2: {D.QnW(sw.hd(34, Mc.Img.quan(q))) == Mc.Img.quan(q) : U32},
  +hst2: {D.FlW(sw.hd(34, Mc.Img.quan(q)), 1024) == False{} : Bool}, +hk2: {D.FlW(sw.hd(34, Mc.Img.quan(q)), 2048) == False{} : Bool},
  +nz: {U32.is_zero(Wa.Wasm.op(Wa.Wasm.Op.and{}, Wa.Wasm.op(Wa.Wasm.Op.ne{}, Mc.Img.quan(q), 0), Bool.to_u32(U32.is_zero(Bool.to_u32(False{}))))) == False{} : Bool}) ->
  sw.MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  match iv:
    case Tuple{et, Tuple{ew, Tuple{evv, Tuple{afs, Tuple{_, Tuple{+isf, Tuple{+frs, Tuple{+hp, Tuple{+io, Tuple{_, _}}}}}}}}}}:
      +HD = sw.hd(34, Mc.Img.quan(q))
      +n = D.Fd(2n, m, sp)
      +M2 = Cr.Cir.Cells.set(m, sp, sw.cell(m, sp, HD, foc))
      +fr2 = {Con{D.AF{D.FK.fun{}, q, False{}, focus, b}, fs} : List<&2, D.AF>}
      +rest2 = R59.sw(rest, sp, D.FK.tag(kind), U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3), n)
      +ST0 = D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)
      +ST2 = D.S(n, 0, sp, pend, rest2, M2, nx, fi, im, pg, lim, inp)
      +hz = fr.nz(ds, m, im, fi, nx, ks, img, ps, sp, kind, q, False{}, a, b, fs, frs)
      +hc = fr.cell(ds, m, im, fi, nx, ks, img, ps, sp, kind, q, False{}, a, b, fs, frs)
      +ht = fr.tag(ds, m, im, fi, nx, ks, img, ps, sp, kind, q, False{}, a, b, fs, frs)
      +hq = fr.q(ds, m, im, fi, nx, ks, img, ps, sp, kind, q, False{}, a, b, fs, frs)
      +hkn = fr.k(ds, m, im, fi, nx, ks, img, ps, sp, kind, q, False{}, a, b, fs, frs)
      +core = sw.core(ds, ks, img, m, nx, fi, im, focus, fs, foc, sp, pend, ps, kind, q, False{}, a, b, D.FK.fun{}, q, HD,
        htg2, hq2, hst2, hk2, sw.not38(kind, hk), {==}, Unit{}, isf, hp, io, frs)
      +W = D.A.w.frames(fs)
      +w2 = D.A.w(False{}, a, fr2)
      +ewf = sw.w(kind, hk, q, a, b, hlv)
      +e1 = Equal.trans(Nat, Nat.add(2n+D.A.w3(a), W), Nat.add(D.A.w.frame(D.AF{kind, q, False{}, a, b}), W), w,
        Equal.cong(Nat, Nat, x => Nat.add(x, W), 2n+D.A.w3(a), D.A.w.frame(D.AF{kind, q, False{}, a, b}),
          Equal.sym(Nat, D.A.w.frame(D.AF{kind, q, False{}, a, b}), 2n+D.A.w3(a), ewf)), ew)
      +e2 = Equal.sym(Nat, 1n+Nat.add(D.A.w3(a), 1n+W), 2n+Nat.add(D.A.w3(a), W),
        Equal.cong(Nat, Nat, x => 1n+x, Nat.add(D.A.w3(a), 1n+W), 1n+Nat.add(D.A.w3(a), W), N.add_succ_r(D.A.w3(a), W)))
      +lt = N.le_rw_r(1n+w2, Nat.add(2n+D.A.w3(a), W), w, e1,
        N.le_rw_l(Nat.add(2n+D.A.w3(a), W), 1n+w2, Nat.add(2n+D.A.w3(a), W), e2, N.le_refl(Nat.add(2n+D.A.w3(a), W))))
      +et2 = {(%sw.plug(kind, hk, q, False{}, a, b, focus) : {D.A.plugs(fs, _) == t : Bk.Term}; et) : {D.A.plugs(fr2, a) == t : Bk.Term}}
      +afs2 = {((%Equal.sym(Bool, El.Quan.live(q), True{}, hlv) : {Bool.and(_, El.Eval.vals(ds, focus, False{})) == True{} : Bool}; evv),
        p2.snd(D.AF.ok(ds, D.AF{kind, q, False{}, a, b}), D.AFs.ok(ds, fs), afs)) : D.AFs.ok(ds, fr2)}
      +inv = sw.inv(ds, ks, img, M2, nx, fi, im, pg, lim, inp, t, a, fr2, n, sp, pend, ps, rest2, et2, afs2, core)
      sw.adm(ds, ks, img, ST0, ST2, t, w, w2,
        f => sw.app.E2(f, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, kind, q, hk, hz, hc, ht, hq, hkn, nz),
        sw.app.E2(0n, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, kind, q, hk, hz, hc, ht, hq, hkn, nz), inv, lt)

# the App swap, by the frame's quantity and flag K
def sw.app.mv(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32,
  +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat,
  +fs: List<&2, D.AF>, +ps: List<&2, U32>, +focus: Bk.Term, +kind: D.FK, q: Bk.Quan, k: Bool, +a: Bk.Term, +b: Bk.Term,
  iv: D.InvOf(ds, ks, img, D.RG(foc, 1, sp, pend, D.R59.list(rest)), m, nx, fi, im, Nil{}, 0, t, w, True{}, focus,
    Con{D.AF{kind, q, k, a, b}, fs}, foc, sp, pend, ps, rest),
  hk: {sw.isapp(kind) == True{} : Bool}, hs: {Bool.and(El.Quan.live(q), Bool.not(k)) == True{} : Bool}) ->
  sw.MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  match q k:
    case Bk.Quan.Q0{} _:
      D.bool.ft(sw.MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w), hs)
    case Bk.Quan.Q1{} True{}:
      D.bool.ft(sw.MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w), hs)
    case Bk.Quan.Q1{} False{}:
      sw.app.go(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, focus, kind, Bk.Quan.Q1{}, a, b, iv, hk,
        {==}, {==}, {==}, {==}, {==}, {==})
    case Bk.Quan.Q2{} True{}:
      D.bool.ft(sw.MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w), hs)
    case Bk.Quan.Q2{} False{}:
      sw.app.go(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, focus, kind, Bk.Quan.Q2{}, a, b, iv, hk,
        {==}, {==}, {==}, {==}, {==}, {==})
