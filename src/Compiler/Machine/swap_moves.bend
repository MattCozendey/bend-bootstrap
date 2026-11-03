# compiler: layer B, the swap moves
# =================================
#
# The moves of M.ret that swap the focus into the top frame (M.swap): App q □ a
# with q live and a not known (mv.ret.swap), Tup q □ b (mv.ret.tupb) and
# Min □ b (mv.ret.minb). The frame's cell sp gets a new header and the focus
# in field 2; its old field 2 becomes the focus, to evaluate. An admin move
# (sw.go), with no new cell.
#
# The store to sp is one store (sw.mem): the cell {hd, y1, foc, y3, y4}. It
# keeps every term (a frame's tag is 32 or more: is.st), the rest of the
# frames (sp is not in the rest of its own chain, by the chain's length:
# Hops, frs.st), the image (ImgOK.fz: nothing points to a frame) and the heap:
# the pointer of sp's field 2 and the root trade places (Ptr.sw, Heap.sw).
# In the accounting, they trade places as Cov's roots too (sw.acc).
#
# Also here: the step of Ann x y to x (mv.ev.ann, through the heap laws
# inc.post and dec.post), with what the step moves share: a step of the
# focus is a step of the frames' term (step.plugs), a run with no loop ends
# (ends.plain), and two owned roots trade places (hsk.sw2, acc.sw2).

import Base
import ../../Shared/shared.bend as Sd
import ../../Book/impl.bend as Bk
import ../../Eval/impl.bend as El
import ../../Wasm/impl.bend as Wa
import ../Cir/impl.bend as Cr
import ./impl.bend as Mc
import ../need_big.bend as N
import ./definitions.bend as D
import ./accounting.bend as A
import ./statement_runs.bend as X
import ./move_kit.bend as K
import ./cell_terms.bend as T
import ./heap_ops.bend as U2

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
  +inp: List<&2, Word(8n)>, +sp: U32, hk: {K.FK.isapp(kind) == True{} : Bool}, hl: {List.length(&2, U32, regs) == 63n : Nat},
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
  +inp: List<&2, Word(8n)>, +sp: U32, +foc: U32, +qv: U32, +hk: {K.FK.isapp(kind) == True{} : Bool}, +hl: {List.length(&2, U32, regs) == 63n : Nat},
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

# The accounting of a swap
# ------------------------
#
# The store to sp trades the focus' root and the root of the frame's field 2
# (a permutation of Cov's roots, cov.perm), keeps sp a frame (its cell stays
# among Cov's cells), and keeps the term cells, the zombies and the pend
# list's term cells (sp is none of them: its tag is 32 or more). So AccK
# holds after it, with the same zombies (sw.acc).

# the cells of terms that stand are not z, of a tag of 19 or more
def neall.rts(xs: List<&2, D.Rt>, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +z: U32, +hz: {U32.is_lt(D.Tg(m, z), 19) == False{} : Bool},
  h: D.Rts(ds, m, im, fi, nx, ks, img, xs)) -> {D.NeAll(D.Rt.cells(xs), z) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{D.Rt{+c, +u}, +rest}:
      (hc, hr) = h
      +nd = D.is.nd(ds, m, im, fi, nx, ks, img, c, u, hc)
      D.neall.cons(c, z, D.Rt.cells(rest), tg.ne(m, c, z, nd.tglt(True{}, ds, im, fi, nx, c, Cr.Cir.Cells.get(m, c), u, nd), hz),
        neall.rts(rest, ds, m, im, fi, nx, ks, img, z, hz, hr))

# terms that stand, A then B
def rts.app(A: List<&2, D.Rt>, +B: List<&2, D.Rt>, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, ha: D.Rts(ds, m, im, fi, nx, ks, img, A),
  hb: D.Rts(ds, m, im, fi, nx, ks, img, B)) -> D.Rts(ds, m, im, fi, nx, ks, img, List.append(&2, D.Rt, A, B)):
  match A:
    case Nil{}:
      hb
    case Con{D.Rt{+c, +u}, +rest}:
      (hc, hr) = ha
      (hc, rts.app(rest, B, ds, m, im, fi, nx, ks, img, hr, hb))

# the term b of a frame stands, for Rwt
def frb.rts(kind: D.FK, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +fr: U32, +b: Bk.Term, h: D.Frs.b(ds, m, im, fi, nx, ks, img, D.Fd(3n, m, fr), kind, b)) ->
  D.Rts(ds, m, im, fi, nx, ks, img, D.Fr.rts.b(m, fr, kind, b)):
  match kind:
    case D.FK.rwt{}:
      (h, Unit{})
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

# the terms that the frames hold stand
def frs.rts(fs: List<&2, D.AF>, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +fr: U32, h: D.Frs(ds, m, im, fi, nx, ks, img, ps, fr, fs)) ->
  D.Rts(ds, m, im, fi, nx, ks, img, D.Fr.rts(fs, m, fr)):
  match fs:
    case Nil{}:
      Unit{}
    case Con{D.AF{+kind, +q, +k, +a, +b}, +rest}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{ia, Tuple{ib, ir}}}}}}}}}}:
          (ia, rts.app(D.Fr.rts.b(m, fr, kind, b), D.Fr.rts(rest, m, D.Fd(1n, m, fr)), ds, m, im, fi, nx, ks, img,
            frb.rts(kind, ds, m, im, fi, nx, ks, img, fr, b, ib), frs.rts(rest, ds, m, im, fi, nx, ks, img, ps, D.Fd(1n, m, fr), ir)))

# the term cells of the pend list, after a store to z, of a tag of 19 or more before and after
def pend.terms.at(bb: Bool, +m: Cr.Cir.Cells, +z: U32, +x: Cr.Cir.Cell, +p: U32, +rest: List<&2, U32>, eb: {U32.is_eq(p, z) == bb : Bool},
  hz: {U32.is_lt(D.Tg(m, z), 19) == False{} : Bool}, hx: {U32.is_lt(D.TgW(Cr.Cir.Cell.get(0n, x)), 19) == False{} : Bool},
  ih: {D.Pend.terms(rest, Cr.Cir.Cells.set(m, z, x)) == D.Pend.terms(rest, m) : List<&2, U32>}) ->
  {D.Pend.terms(Con{p, rest}, Cr.Cir.Cells.set(m, z, x)) == D.Pend.terms(Con{p, rest}, m) : List<&2, U32>}:
  match bb:
    case True{}:
      +M2 = Cr.Cir.Cells.set(m, z, x)
      +e = D.u32.eq(p, z, eb)
      %Equal.sym(List<&2, U32>, D.Pend.terms(rest, M2), D.Pend.terms(rest, m), ih) :
        {Bool.pick(List<&2, U32>, U32.is_lt(D.Tg(M2, p), 19), Con{p, _}, _) == D.Pend.terms(Con{p, rest}, m) : List<&2, U32>}
      %Equal.sym(U32, p, z, e) :
        {Bool.pick(List<&2, U32>, U32.is_lt(D.Tg(M2, _), 19), Con{_, D.Pend.terms(rest, m)}, D.Pend.terms(rest, m)) ==
          Bool.pick(List<&2, U32>, U32.is_lt(D.Tg(m, _), 19), Con{_, D.Pend.terms(rest, m)}, D.Pend.terms(rest, m)) : List<&2, U32>}
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M2, z), x, D.cl.gs(m, z, x)) :
        {Bool.pick(List<&2, U32>, U32.is_lt(D.TgW(Cr.Cir.Cell.get(0n, _)), 19), Con{z, D.Pend.terms(rest, m)}, D.Pend.terms(rest, m)) ==
          Bool.pick(List<&2, U32>, U32.is_lt(D.Tg(m, z), 19), Con{z, D.Pend.terms(rest, m)}, D.Pend.terms(rest, m)) : List<&2, U32>}
      %Equal.sym(Bool, U32.is_lt(D.TgW(Cr.Cir.Cell.get(0n, x)), 19), False{}, hx) :
        {Bool.pick(List<&2, U32>, _, Con{z, D.Pend.terms(rest, m)}, D.Pend.terms(rest, m)) ==
          Bool.pick(List<&2, U32>, U32.is_lt(D.Tg(m, z), 19), Con{z, D.Pend.terms(rest, m)}, D.Pend.terms(rest, m)) : List<&2, U32>}
      %Equal.sym(Bool, U32.is_lt(D.Tg(m, z), 19), False{}, hz) :
        {D.Pend.terms(rest, m) == Bool.pick(List<&2, U32>, _, Con{z, D.Pend.terms(rest, m)}, D.Pend.terms(rest, m)) : List<&2, U32>}
      {==}
    case False{}:
      +M2 = Cr.Cir.Cells.set(m, z, x)
      %Equal.sym(List<&2, U32>, D.Pend.terms(rest, M2), D.Pend.terms(rest, m), ih) :
        {Bool.pick(List<&2, U32>, U32.is_lt(D.Tg(M2, p), 19), Con{p, _}, _) == D.Pend.terms(Con{p, rest}, m) : List<&2, U32>}
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M2, p), Cr.Cir.Cells.get(m, p), D.cl.go(m, p, z, x, eb)) :
        {Bool.pick(List<&2, U32>, U32.is_lt(D.TgW(Cr.Cir.Cell.get(0n, _)), 19), Con{p, D.Pend.terms(rest, m)}, D.Pend.terms(rest, m)) ==
          D.Pend.terms(Con{p, rest}, m) : List<&2, U32>}
      {==}

def pend.terms.sw(ps: List<&2, U32>, +m: Cr.Cir.Cells, +z: U32, +x: Cr.Cir.Cell,
  +hz: {U32.is_lt(D.Tg(m, z), 19) == False{} : Bool}, +hx: {U32.is_lt(D.TgW(Cr.Cir.Cell.get(0n, x)), 19) == False{} : Bool}) ->
  {D.Pend.terms(ps, Cr.Cir.Cells.set(m, z, x)) == D.Pend.terms(ps, m) : List<&2, U32>}:
  match ps:
    case Nil{}:
      {==}
    case Con{+p, +rest}:
      pend.terms.at(U32.is_eq(p, z), m, z, x, p, rest, {==}, hz, hx, pend.terms.sw(rest, m, z, x, hz, hx))

# the term b of a frame fr that is not z, after a store to z
def frb.st(kind: D.FK, +m: Cr.Cir.Cells, +z: U32, +x: Cr.Cir.Cell, +fr: U32, +b: Bk.Term,
  ec: {Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, x), fr) == Cr.Cir.Cells.get(m, fr) : Cr.Cir.Cell}) ->
  {D.Fr.rts.b(Cr.Cir.Cells.set(m, z, x), fr, kind, b) == D.Fr.rts.b(m, fr, kind, b) : List<&2, D.Rt>}:
  match kind:
    case D.FK.rwt{}:
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, x), fr), Cr.Cir.Cells.get(m, fr), ec) :
        {[D.Rt{Cr.Cir.Cell.get(3n, _), b}] == [D.Rt{D.Fd(3n, m, fr), b}] : List<&2, D.Rt>}
      {==}
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
    case D.FK.minb{}:
      {==}
    case D.FK.mina{}:
      {==}

# the frames' cells and terms from fr, after a store to sx, whose chain is
# longer than fr's (as frs.st.c)
def fr.st(fs: List<&2, D.AF>, +m: Cr.Cir.Cells, +sx: U32, +sv: Cr.Cir.Cell, +fr: U32, +n: Nat,
  +hn: {Hops(n, m, sx) == True{} : Bool}, hf: {Hops(List.length(&2, D.AF, fs), m, fr) == True{} : Bool},
  hl: N.Le(1n+List.length(&2, D.AF, fs), n)) ->
  D.P2({D.Fr.cells(fs, Cr.Cir.Cells.set(m, sx, sv), fr) == D.Fr.cells(fs, m, fr) : List<&2, U32>},
    {D.Fr.rts(fs, Cr.Cir.Cells.set(m, sx, sv), fr) == D.Fr.rts(fs, m, fr) : List<&2, D.Rt>}):
  match fs:
    case Nil{}:
      ({==}, {==})
    case Con{D.AF{+kind, +q, +k, +a, +b}, +rest}:
      +M2 = Cr.Cir.Cells.set(m, sx, sv)
      +hf2 = hf
      +hl2 = hl
      +ec = D.cl.go(m, fr, sx, sv, hops.ne(1n+List.length(&2, D.AF, rest), n, m, fr, sx, hf2, hn, hl2))
      +f1 = D.Fd(1n, m, fr)
      +ih = fr.st(rest, m, sx, sv, f1, n, hn, D.and.r(Bool.not(U32.is_eq(fr, 0)), Hops(List.length(&2, D.AF, rest), m, f1), hf2),
        N.weaken(1n+List.length(&2, D.AF, rest), n, hl2))
      +ihc = D.Ex.fst({D.Fr.cells(rest, M2, f1) == D.Fr.cells(rest, m, f1) : List<&2, U32>}, _ => {D.Fr.rts(rest, M2, f1) == D.Fr.rts(rest, m, f1) : List<&2, D.Rt>}, ih)
      +ihr = D.Ex.snd({D.Fr.cells(rest, M2, f1) == D.Fr.cells(rest, m, f1) : List<&2, U32>}, _ => {D.Fr.rts(rest, M2, f1) == D.Fr.rts(rest, m, f1) : List<&2, D.Rt>}, ih)
      ({(%Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M2, fr), Cr.Cir.Cells.get(m, fr), ec) :
            {Con{fr, D.Fr.cells(rest, M2, Cr.Cir.Cell.get(1n, _))} == Con{fr, D.Fr.cells(rest, m, f1)} : List<&2, U32>};
          %Equal.sym(List<&2, U32>, D.Fr.cells(rest, M2, f1), D.Fr.cells(rest, m, f1), ihc) : {Con{fr, _} == Con{fr, D.Fr.cells(rest, m, f1)} : List<&2, U32>};
          {==}) : {D.Fr.cells(Con{D.AF{kind, q, k, a, b}, rest}, M2, fr) == D.Fr.cells(Con{D.AF{kind, q, k, a, b}, rest}, m, fr) : List<&2, U32>}},
        {(%Equal.sym(List<&2, D.Rt>, D.Fr.rts.b(M2, fr, kind, b), D.Fr.rts.b(m, fr, kind, b), frb.st(kind, m, sx, sv, fr, b, ec)) :
            {Con{D.Rt{D.Fd(2n, M2, fr), a}, List.append(&2, D.Rt, _, D.Fr.rts(rest, M2, D.Fd(1n, M2, fr)))} ==
              Con{D.Rt{D.Fd(2n, m, fr), a}, List.append(&2, D.Rt, D.Fr.rts.b(m, fr, kind, b), D.Fr.rts(rest, m, f1))} : List<&2, D.Rt>};
          %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M2, fr), Cr.Cir.Cells.get(m, fr), ec) :
            {Con{D.Rt{Cr.Cir.Cell.get(2n, _), a}, List.append(&2, D.Rt, D.Fr.rts.b(m, fr, kind, b), D.Fr.rts(rest, M2, Cr.Cir.Cell.get(1n, _)))} ==
              Con{D.Rt{D.Fd(2n, m, fr), a}, List.append(&2, D.Rt, D.Fr.rts.b(m, fr, kind, b), D.Fr.rts(rest, m, f1))} : List<&2, D.Rt>};
          %Equal.sym(List<&2, D.Rt>, D.Fr.rts(rest, M2, f1), D.Fr.rts(rest, m, f1), ihr) :
            {Con{D.Rt{D.Fd(2n, m, fr), a}, List.append(&2, D.Rt, D.Fr.rts.b(m, fr, kind, b), _)} ==
              Con{D.Rt{D.Fd(2n, m, fr), a}, List.append(&2, D.Rt, D.Fr.rts.b(m, fr, kind, b), D.Fr.rts(rest, m, f1))} : List<&2, D.Rt>};
          {==}) : {D.Fr.rts(Con{D.AF{kind, q, k, a, b}, rest}, M2, fr) == D.Fr.rts(Con{D.AF{kind, q, k, a, b}, rest}, m, fr) : List<&2, D.Rt>}})

# Cov at the cell c, after a store to z, one of the cells xs, that keeps the roots' nodes
def cov.st.at(bb: Bool, +m: Cr.Cir.Cells, +z: U32, +x: Cr.Cir.Cell, +c: U32, +rs: List<&2, D.Rt>, +xs: List<&2, U32>,
  eb: {U32.is_eq(c, z) == bb : Bool}, hm: {D.Mem(xs, z) == True{} : Bool},
  hnd: {D.Nodes(rs, Cr.Cir.Cells.set(m, z, x), c) == D.Nodes(rs, m, c) : Bool},
  h: {Bool.or(D.Fl(m, c, 1024), Bool.or(D.Nodes(rs, m, c), D.Mem(xs, c))) == True{} : Bool}) ->
  {Bool.or(D.Fl(Cr.Cir.Cells.set(m, z, x), c, 1024), Bool.or(D.Nodes(rs, Cr.Cir.Cells.set(m, z, x), c), D.Mem(xs, c))) == True{} : Bool}:
  match bb:
    case True{}:
      +M2 = Cr.Cir.Cells.set(m, z, x)
      %Equal.sym(U32, c, z, D.u32.eq(c, z, eb)) :
        {Bool.or(D.Fl(M2, _, 1024), Bool.or(D.Nodes(rs, M2, _), D.Mem(xs, _))) == True{} : Bool}
      %Equal.sym(Bool, D.Mem(xs, z), True{}, hm) : {Bool.or(D.Fl(M2, z, 1024), Bool.or(D.Nodes(rs, M2, z), _)) == True{} : Bool}
      %Equal.sym(Bool, Bool.or(D.Nodes(rs, M2, z), True{}), True{}, A.or.true(D.Nodes(rs, M2, z))) : {Bool.or(D.Fl(M2, z, 1024), _) == True{} : Bool}
      A.or.true(D.Fl(M2, z, 1024))
    case False{}:
      +M2 = Cr.Cir.Cells.set(m, z, x)
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M2, c), Cr.Cir.Cells.get(m, c), D.cl.go(m, c, z, x, eb)) :
        {Bool.or(U32.is_ne(U32.and(Cr.Cir.Cell.get(0n, _), 1024), 0), Bool.or(D.Nodes(rs, M2, c), D.Mem(xs, c))) == True{} : Bool}
      %Equal.sym(Bool, D.Nodes(rs, M2, c), D.Nodes(rs, m, c), hnd) : {Bool.or(D.Fl(m, c, 1024), Bool.or(_, D.Mem(xs, c))) == True{} : Bool}
      h

def cov.st(n: Nat, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +rs0: List<&2, U32>, +z: U32, +x: Cr.Cir.Cell, +c: U32, +rs: List<&2, D.Rt>,
  +xs: List<&2, U32>, +tbl: D.Tbl(m, im, fi, nx),
  +hz0: {D.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, rs0, z) == 0n : Nat}, +hzs: {D.Fl(m, z, 1024) == False{} : Bool},
  +hn: {D.NeAll(D.Rt.cells(rs), z) == True{} : Bool}, +ho: D.Rts(ds, m, im, fi, nx, ks, img, rs), +hm: {D.Mem(xs, z) == True{} : Bool},
  h: {D.Cov(n, m, c, rs, xs) == True{} : Bool}) -> {D.Cov(n, Cr.Cir.Cells.set(m, z, x), c, rs, xs) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+(+k):
      +M2 = Cr.Cir.Cells.set(m, z, x)
      +h2 = h
      +T = Bool.or(D.Fl(m, c, 1024), Bool.or(D.Nodes(rs, m, c), D.Mem(xs, c)))
      D.and.i(Bool.or(D.Fl(M2, c, 1024), Bool.or(D.Nodes(rs, M2, c), D.Mem(xs, c))), D.Cov(k, M2, U32.inc(c), rs, xs),
        cov.st.at(U32.is_eq(c, z), m, z, x, c, rs, xs, {==}, hm,
          D.Nodes.fz(True{}, rs, ds, m, im, fi, nx, ks, img, ps, rs0, z, x, c, tbl, hz0, hzs, hn, ho),
          D.and.l(T, D.Cov(k, m, U32.inc(c), rs, xs), h2)),
        cov.st(k, ds, m, im, fi, nx, ks, img, ps, rs0, z, x, U32.inc(c), rs, xs, tbl, hz0, hzs, hn, ho, hm,
          D.and.r(T, D.Cov(k, m, U32.inc(c), rs, xs), h2)))

# STATIC cells, after a store to z, which was not STATIC
def static.at(bb: Bool, +m: Cr.Cir.Cells, +z: U32, +x: Cr.Cir.Cell, +y: U32, eb: {U32.is_eq(y, z) == bb : Bool},
  hzs: {D.Fl(m, z, 1024) == False{} : Bool}, h: {D.Fl(m, y, 1024) == True{} : Bool}) ->
  {D.Fl(Cr.Cir.Cells.set(m, z, x), y, 1024) == True{} : Bool}:
  match bb:
    case True{}:
      Empty.absurd({D.Fl(Cr.Cir.Cells.set(m, z, x), y, 1024) == True{} : Bool},
        D.bool.ft(Empty, Equal.trans(Bool, False{}, U32.is_eq(y, z), True{}, Equal.sym(Bool, U32.is_eq(y, z), False{},
          D.ne.st(U32.is_eq(y, z), m, y, z, {==}, h, hzs)), eb)))
    case False{}:
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, z, x), y), Cr.Cir.Cells.get(m, y), D.cl.go(m, y, z, x, eb)) :
        {U32.is_ne(U32.and(Cr.Cir.Cell.get(0n, _), 1024), 0) == True{} : Bool}
      h

def static.st(ys: List<&2, U32>, +m: Cr.Cir.Cells, +z: U32, +x: Cr.Cir.Cell, +hzs: {D.Fl(m, z, 1024) == False{} : Bool},
  h: {D.All.static(ys, m) == True{} : Bool}) -> {D.All.static(ys, Cr.Cir.Cells.set(m, z, x)) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +rest}:
      +h2 = h
      D.and.i(D.Fl(Cr.Cir.Cells.set(m, z, x), y, 1024), D.All.static(rest, Cr.Cir.Cells.set(m, z, x)),
        static.at(U32.is_eq(y, z), m, z, x, y, {==}, hzs, D.and.l(D.Fl(m, y, 1024), D.All.static(rest, m), h2)),
        static.st(rest, m, z, x, hzs, D.and.r(D.Fl(m, y, 1024), D.All.static(rest, m), h2)))

# Clo, with no temporary, at the cell c, after a store to z, of a cell that is not STATIC
def clo.st.at(bb: Bool, +m: Cr.Cir.Cells, +z: U32, +x: Cr.Cir.Cell, +c: U32, +ps: List<&2, U32>, +eb: {U32.is_eq(c, z) == bb : Bool},
  ht: {D.TblAt(m, c, z) == True{} : Bool}, hzs: {D.Fl(m, z, 1024) == False{} : Bool},
  hx: {D.FlW(Cr.Cir.Cell.get(0n, x), 1024) == False{} : Bool}, h: {D.Clo.at(m, c, ps, Nil{}, Nil{}) == True{} : Bool}) ->
  {D.Clo.at(Cr.Cir.Cells.set(m, z, x), c, ps, Nil{}, Nil{}) == True{} : Bool}:
  match bb:
    case True{}:
      +M2 = Cr.Cir.Cells.set(m, z, x)
      %Equal.sym(U32, c, z, D.u32.eq(c, z, eb)) :
        {Bool.and(Bool.or(Bool.not(D.Fl(M2, _, 1024)), D.All.static(D.Fs(M2, ps, _), M2)), True{}) == True{} : Bool}
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M2, z), x, D.cl.gs(m, z, x)) :
        {Bool.and(Bool.or(Bool.not(U32.is_ne(U32.and(Cr.Cir.Cell.get(0n, _), 1024), 0)), D.All.static(D.Fs(M2, ps, z), M2)), True{}) == True{} : Bool}
      %Equal.sym(Bool, D.FlW(Cr.Cir.Cell.get(0n, x), 1024), False{}, hx) :
        {Bool.and(Bool.or(Bool.not(_), D.All.static(D.Fs(M2, ps, z), M2)), True{}) == True{} : Bool}
      {==}
    case False{}:
      +M2 = Cr.Cir.Cells.set(m, z, x)
      +S0 = D.All.static(D.Fs(m, ps, c), m)
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M2, c), Cr.Cir.Cells.get(m, c), D.cl.go(m, c, z, x, eb)) :
        {Bool.and(Bool.or(Bool.not(U32.is_ne(U32.and(Cr.Cir.Cell.get(0n, _), 1024), 0)), D.All.static(D.Fs(M2, ps, c), M2)), True{}) == True{} : Bool}
      %Equal.sym(List<&2, U32>, D.Fs(M2, ps, c), D.Fs(m, ps, c), D.fs.eq(m, z, x, ps, c, eb, ht)) :
        {Bool.and(Bool.or(Bool.not(D.Fl(m, c, 1024)), D.All.static(_, M2)), True{}) == True{} : Bool}
      D.and.i(Bool.or(Bool.not(D.Fl(m, c, 1024)), D.All.static(D.Fs(m, ps, c), M2)), True{},
        A.or.mono.r(Bool.not(D.Fl(m, c, 1024)), S0, D.All.static(D.Fs(m, ps, c), M2),
          D.and.l(Bool.or(Bool.not(D.Fl(m, c, 1024)), S0), True{}, h), e => static.st(D.Fs(m, ps, c), m, z, x, hzs, e)), {==})

def clo.st(n: Nat, +m: Cr.Cir.Cells, +z: U32, +x: Cr.Cir.Cell, +c: U32, +ps: List<&2, U32>, ht: {D.TblR(n, m, c, z) == True{} : Bool},
  +hzs: {D.Fl(m, z, 1024) == False{} : Bool}, +hx: {D.FlW(Cr.Cir.Cell.get(0n, x), 1024) == False{} : Bool},
  h: {D.Clo(n, m, c, ps, Nil{}, Nil{}) == True{} : Bool}) -> {D.Clo(n, Cr.Cir.Cells.set(m, z, x), c, ps, Nil{}, Nil{}) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+(+k):
      +M2 = Cr.Cir.Cells.set(m, z, x)
      +h2 = h
      +ht2 = ht
      D.and.i(D.Clo.at(M2, c, ps, Nil{}, Nil{}), D.Clo(k, M2, U32.inc(c), ps, Nil{}, Nil{}),
        clo.st.at(U32.is_eq(c, z), m, z, x, c, ps, {==}, D.and.l(D.TblAt(m, c, z), D.TblR(k, m, U32.inc(c), z), ht2), hzs, hx,
          D.and.l(D.Clo.at(m, c, ps, Nil{}, Nil{}), D.Clo(k, m, U32.inc(c), ps, Nil{}, Nil{}), h2)),
        clo.st(k, m, z, x, U32.inc(c), ps, D.and.r(D.TblAt(m, c, z), D.TblR(k, m, U32.inc(c), z), ht2), hzs, hx,
          D.and.r(D.Clo.at(m, c, ps, Nil{}, Nil{}), D.Clo(k, m, U32.inc(c), ps, Nil{}, Nil{}), h2)))

# AccK after the store to the top frame sp, of the kind kind1, which becomes
# one of kind2 with the header hd: the focus and the frame's field 2 trade
# places as roots (neither kind holds a term in field 3)
def sw.acc(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32,
  +im: U32, +focus: Bk.Term, +fs: List<&2, D.AF>, +foc: U32, +sp: U32, +pend: U32, +ps: List<&2, U32>, +kind1: D.FK, +q: Bk.Quan,
  +k: Bool, +a: Bk.Term, +b: Bk.Term, +kind2: D.FK, +q2: Bk.Quan, +hd: U32, +zs: List<&2, D.Rt>,
  +htg2: {D.TgW(hd) == D.FK.tag(kind2) : U32}, +hst2: {D.FlW(hd, 1024) == False{} : Bool},
  +eb1: {D.Fr.rts.b(m, sp, kind1, b) == Nil{} : List<&2, D.Rt>},
  +eb2: {D.Fr.rts.b(Cr.Cir.Cells.set(m, sp, sw.cell(m, sp, hd, foc)), sp, kind2, b) == Nil{} : List<&2, D.Rt>},
  +isf: D.Is(ds, m, im, fi, nx, ks, img, foc, focus), +hp: D.Heap(m, nx, fi, im, [foc], pend, ps),
  +io: D.ImgOK(ds, ks, img, m, im, fi, nx), +hsp: {Hops(1n+List.length(&2, D.AF, fs), m, sp) == True{} : Bool},
  frs: D.Frs(ds, m, im, fi, nx, ks, img, ps, sp, Con{D.AF{kind1, q, k, a, b}, fs}),
  hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, [D.Rt{foc, focus}], Nil{}, sp, Con{D.AF{kind1, q, k, a, b}, fs}, ps, zs)) ->
  D.AccK(True{}, ds, ks, img, Cr.Cir.Cells.set(m, sp, sw.cell(m, sp, hd, foc)), nx, fi, im, [D.Rt{D.Fd(2n, m, sp), a}], Nil{}, sp,
    Con{D.AF{kind2, q2, False{}, focus, b}, fs}, ps, zs):
  match frs:
    case Tuple{_, Tuple{_, Tuple{eo, Tuple{es, Tuple{_, Tuple{etg, Tuple{_, Tuple{_, Tuple{ia, Tuple{_, ir}}}}}}}}}}:
      (hzr, r1) = hac
      (_, r2) = r1
      (hzc, r3) = r2
      (hcov, r4) = r3
      (hclo, _) = r4
      +hz2 = hzr
      +SV = sw.cell(m, sp, hd, foc)
      +M2 = Cr.Cir.Cells.set(m, sp, SV)
      +N = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
      +eo2 = eo
      +es2 = es
      +etg2 = etg
      +hzt = {(%Equal.sym(U32, D.Tg(m, sp), D.FK.tag(kind1), etg2) : {U32.is_lt(_, 19) == False{} : Bool}; D.fk.lt(kind1)) :
        {U32.is_lt(D.Tg(m, sp), 19) == False{} : Bool}}
      +hxt = {(%Equal.sym(U32, D.TgW(hd), D.FK.tag(kind2), htg2) : {U32.is_lt(_, 19) == False{} : Bool}; D.fk.lt(kind2)) :
        {U32.is_lt(D.TgW(Cr.Cir.Cell.get(0n, SV)), 19) == False{} : Bool}}
      +tbl = D.img.tbl(True{}, ds, ks, img, m, im, fi, nx, io)
      +nd = D.is.nd(ds, m, im, fi, nx, ks, img, foc, focus, isf)
      +hfoc = nd.tglt(True{}, ds, im, fi, nx, foc, Cr.Cir.Cells.get(m, foc), focus, nd)
      +hz0 = ptr.none(m, nx, fi, im, ps, pend, foc, sp, hzt, hfoc, hp)
      +hz290 = D.img.hz(True{}, ds, ks, img, m, im, fi, nx, sp, io, eo2)
      +egs = D.cl.gs(m, sp, SV)
      +f1 = D.Fd(1n, m, sp)
      +n = D.Fd(2n, m, sp)
      +FR = D.Fr.rts(fs, m, f1)
      +FC = D.Fr.cells(fs, m, f1)
      +L = List.length(&2, D.AF, fs)
      +frst = fr.st(fs, m, sp, SV, f1, 1n+L, hsp, D.and.r(Bool.not(U32.is_eq(sp, 0)), Hops(L, m, f1), hsp), N.le_refl(1n+L))
      +frc = D.Ex.fst({D.Fr.cells(fs, M2, f1) == FC : List<&2, U32>}, _ => {D.Fr.rts(fs, M2, f1) == FR : List<&2, D.Rt>}, frst)
      +frr = D.Ex.snd({D.Fr.cells(fs, M2, f1) == FC : List<&2, U32>}, _ => {D.Fr.rts(fs, M2, f1) == FR : List<&2, D.Rt>}, frst)
      +RS1 = {Con{D.Rt{foc, focus}, Con{D.Rt{n, a}, List.append(&2, D.Rt, FR, zs)}} : List<&2, D.Rt>}
      +RS2 = {Con{D.Rt{n, a}, Con{D.Rt{foc, focus}, List.append(&2, D.Rt, FR, zs)}} : List<&2, D.Rt>}
      +XS = {Con{sp, List.append(&2, U32, FC, ps)} : List<&2, U32>}
      +c1 = {(%eb1 : {D.Cov(N, m, fi, Con{D.Rt{foc, focus}, Con{D.Rt{n, a}, List.append(&2, D.Rt, List.append(&2, D.Rt, _, FR), zs)}}, XS) == True{} : Bool};
        hcov) : {D.Cov(N, m, fi, RS1, XS) == True{} : Bool}}
      +c2 = A.cov.mv(D.Cov(N, m, fi, RS1, XS), D.Cov(N, m, fi, RS2, XS),
        A.cov.perm(N, m, fi, Nil{}, [D.Rt{foc, focus}], [D.Rt{n, a}], List.append(&2, D.Rt, FR, zs), XS), c1)
      +hrs2 = {(ia, (isf, rts.app(FR, zs, ds, m, im, fi, nx, ks, img, frs.rts(fs, ds, m, im, fi, nx, ks, img, ps, f1, ir), hz2))) :
        D.Rts(ds, m, im, fi, nx, ks, img, RS2)}
      +hne2 = neall.rts(RS2, ds, m, im, fi, nx, ks, img, sp, hzt, hrs2)
      +hmem = {(%Equal.sym(Bool, U32.is_eq(sp, sp), True{}, D.u32.refl(sp)) : {Bool.or(_, D.Mem(List.append(&2, U32, FC, ps), sp)) == True{} : Bool};
        {==}) : {D.Mem(XS, sp) == True{} : Bool}}
      +c3 = cov.st(N, ds, m, im, fi, nx, ks, img, ps, [foc], sp, SV, fi, RS2, XS, tbl, hz0, es2, hne2, hrs2, hmem, c2)
      +c4 = {(%Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M2, sp), SV, egs) :
            {D.Cov(N, M2, fi, Con{D.Rt{n, a}, Con{D.Rt{Cr.Cir.Cell.get(2n, _), focus},
              List.append(&2, D.Rt, List.append(&2, D.Rt, D.Fr.rts.b(M2, sp, kind2, b), D.Fr.rts(fs, M2, Cr.Cir.Cell.get(1n, _))), zs)}},
              Con{sp, List.append(&2, U32, D.Fr.cells(fs, M2, Cr.Cir.Cell.get(1n, _)), ps)}) == True{} : Bool};
          %Equal.sym(List<&2, D.Rt>, D.Fr.rts.b(M2, sp, kind2, b), Nil{}, eb2) :
            {D.Cov(N, M2, fi, Con{D.Rt{n, a}, Con{D.Rt{foc, focus}, List.append(&2, D.Rt, List.append(&2, D.Rt, _, D.Fr.rts(fs, M2, f1)), zs)}},
              Con{sp, List.append(&2, U32, D.Fr.cells(fs, M2, f1), ps)}) == True{} : Bool};
          %Equal.sym(List<&2, D.Rt>, D.Fr.rts(fs, M2, f1), FR, frr) :
            {D.Cov(N, M2, fi, Con{D.Rt{n, a}, Con{D.Rt{foc, focus}, List.append(&2, D.Rt, _, zs)}},
              Con{sp, List.append(&2, U32, D.Fr.cells(fs, M2, f1), ps)}) == True{} : Bool};
          %Equal.sym(List<&2, U32>, D.Fr.cells(fs, M2, f1), FC, frc) :
            {D.Cov(N, M2, fi, RS2, Con{sp, List.append(&2, U32, _, ps)}) == True{} : Bool};
          c3) :
        {D.Cov(N, M2, fi, List.append(&2, D.Rt, [D.Rt{n, a}], List.append(&2, D.Rt, Nil{}, List.append(&2, D.Rt,
            D.Fr.rts(Con{D.AF{kind2, q2, False{}, focus, b}, fs}, M2, sp), zs))),
          List.append(&2, U32, D.Fr.cells(Con{D.AF{kind2, q2, False{}, focus, b}, fs}, M2, sp), List.append(&2, U32, Nil{}, ps))) == True{} : Bool}}
      (D.Rts.fz(True{}, zs, ds, m, im, fi, nx, ks, img, ps, [foc], sp, SV, tbl, hz0, es2, neall.rts(zs, ds, m, im, fi, nx, ks, img, sp, hzt, hz2), hz2),
        (Unit{},
        (Equal.trans(List<&2, U32>, D.Rt.cells(zs), D.Pend.terms(ps, m), D.Pend.terms(ps, M2), hzc,
          Equal.sym(List<&2, U32>, D.Pend.terms(ps, M2), D.Pend.terms(ps, m), pend.terms.sw(ps, m, sp, SV, hzt, hxt))),
        (c4, (clo.st(N, m, sp, SV, fi, ps, D.TblR.of(N, m, fi, sp, hz290), es2, hst2, hclo), {==})))))

# The moves
# ---------

# a number is at most its max with another
def le.max.l(a: Nat, b: Nat) -> N.Le(a, Nat.max(a, b)):
  match a b:
    case 0n _:
      N.le_zero(b)
    case 1n+p 0n:
      N.le_refl(1n+p)
    case 1n+p 1n+r:
      le.max.l(p, r)

# a round that goes to st2, for any fuel, where Inv holds of the same term
# with a smaller measure, and no more own cells: an admin move
def sw.mv(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +st: Cr.Cir.State, +st2: Cr.Cir.State,
  +t: Bk.Term, +w: Nat, +w2: Nat, hE: @f: Nat -> {Cr.Cir.exec(f, D.B.body(), st) == Cr.Cir.Out.next{st2} : Cr.Cir.Out},
  hE0: {Cr.Cir.exec(0n, D.B.body(), st) == Cr.Cir.Out.next{st2} : Cr.Cir.Out}, +inv: D.Inv(ds, ks, img, st2, t, w2), +lt: N.Le(1n+w2, w), +hm: N.Le(D.Mem.cells(st2), D.Mem.cells(st))) -> K.MV(ds, ks, img, st, t, w):
  +pk = N.le_trans(D.Mem.cells(st2), D.Mem.cells(st), Nat.max(D.Mem.cells(st), D.Need(ds, st, t)), hm,
    le.max.l(D.Mem.cells(st), D.Need(ds, st, t)))
  (f => (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, D.B.body(), st), Cr.Cir.Out.next{st2}, hE(f)) :
      D.PostB(False{}, _, s => K.MV.next(ds, ks, img, st, t, w, s), s => st3 => D.HR(ds, t, s, st3), D.Budget(ds, st, t), D.St.lim(st));
      (Inl{(w2, (inv, lt))}, pk)),
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
def sw.plug(kind: D.FK, hk: {K.FK.isapp(kind) == True{} : Bool}, +q: Bk.Quan, +k: Bool, +a: Bk.Term, +b: Bk.Term, +v: Bk.Term) ->
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

def sw.w(kind: D.FK, hk: {K.FK.isapp(kind) == True{} : Bool}, +q: Bk.Quan, +a: Bk.Term, +b: Bk.Term, +hlv: {El.Quan.live(q) == True{} : Bool}) ->
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

# an App q □ x frame holds no term in field 3
def frb.nil(kind: D.FK, hk: {K.FK.isapp(kind) == True{} : Bool}, +m: Cr.Cir.Cells, +fr: U32, +b: Bk.Term) ->
  {D.Fr.rts.b(m, fr, kind, b) == Nil{} : List<&2, D.Rt>}:
  match kind:
    case D.FK.rwt{}:
      D.bool.ft({[D.Rt{D.Fd(3n, m, fr), b}] == Nil{} : List<&2, D.Rt>}, hk)
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
    case D.FK.minb{}:
      {==}
    case D.FK.mina{}:
      {==}

def sw.not38(kind: D.FK, hk: {K.FK.isapp(kind) == True{} : Bool}) -> {U32.is_eq(D.FK.tag(kind), 38) == False{} : Bool}:
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
# and the accounting of the new state (acc)
def sw.inv(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m2: Cr.Cir.Cells, +nx: U32, +fi: U32,
  +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +a: Bk.Term, +fr2: List<&2, D.AF>, +n: U32, +sp: U32, +pend: U32,
  +ps: List<&2, U32>, +rest2: D.R59, et2: {D.A.plugs(fr2, a) == t : Bk.Term}, afs2: D.AFs.ok(ds, fr2),
  core: D.P2(D.Is(ds, m2, im, fi, nx, ks, img, n, a), D.P2(D.Frs(ds, m2, im, fi, nx, ks, img, ps, sp, fr2),
    D.P2(D.Heap(m2, nx, fi, im, [n], pend, ps), D.ImgOK(ds, ks, img, m2, im, fi, nx)))),
  acc: D.Ex(List<&2, D.Rt>, zs => D.AccK(True{}, ds, ks, img, m2, nx, fi, im, [D.Rt{n, a}], Nil{}, sp, fr2, ps, zs))) ->
  D.Inv(ds, ks, img, D.S(n, 0, sp, pend, rest2, m2, nx, fi, im, pg, lim, inp), t, D.A.w(False{}, a, fr2)):
  match core:
    case Tuple{isa, Tuple{frs2, Tuple{heap2, img2}}}:
      (D.Wit{False{}, a, fr2, n, sp, pend, ps, rest2},
        ((et2, ({==}, ({==}, (afs2, ({==}, (isa, (frs2, (heap2, (img2, ({==}, {==})))))))))), acc))

# the round of a swap, from the run of B.body on the registers (hE), to the
# states that Inv speaks of: the frame's tag T and the header HD
def sw.E2(+f: Nat, +foc: U32, +sp: U32, +pend: U32, +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32,
  +lim: U32, +inp: List<&2, Word(8n)>, +T: U32, +HD: U32,
  hE: {Cr.Cir.exec(f, X.X.body(), X.X.st(D.RG(foc, 1, sp, pend, D.R59.list(rest)), m, nx, fi, im, pg, lim, inp)) ==
    Cr.Cir.Out.next{X.X.st(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, T),
      14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 15n, D.Fd(2n, m, sp)), 0n, D.Fd(2n, m, sp)), 1n, 0),
      X.X.put(X.X.put(m, 0n, sp, HD), 2n, sp, foc), nx, fi, im, pg, lim, inp)} : Cr.Cir.Out}) ->
  {Cr.Cir.exec(f, D.B.body(), D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)) ==
    Cr.Cir.Out.next{D.S(D.Fd(2n, m, sp), 0, sp, pend, R59.sw(rest, sp, T, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3), D.Fd(2n, m, sp)),
      Cr.Cir.Cells.set(m, sp, sw.cell(m, sp, HD, foc)), nx, fi, im, pg, lim, inp)} : Cr.Cir.Out}:
  +regs = D.RG(foc, 1, sp, pend, D.R59.list(rest))
  +Q = U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)
  +n = D.Fd(2n, m, sp)
  +M2 = Cr.Cir.Cells.set(m, sp, sw.cell(m, sp, HD, foc))
  +R2 = X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(regs, 9n, sp), 10n, T), 14n, Q), 15n, n), 0n, n), 1n, 0)
  %sw.regs(rest, foc, sp, pend, T, Q, n) :
    {Cr.Cir.exec(f, D.B.body(), D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)) ==
      Cr.Cir.Out.next{Cr.Cir.State{_, M2, nx, fi, im, pg, lim, inp, Nil{}, 0}} : Cr.Cir.Out}
  %sw.mem(m, sp, HD, foc) :
    {Cr.Cir.exec(f, D.B.body(), D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)) ==
      Cr.Cir.Out.next{Cr.Cir.State{R2, _, nx, fi, im, pg, lim, inp, Nil{}, 0}} : Cr.Cir.Out}
  hE

# 2 + x is 1 + (x + 1)
def w.one(+x: Nat) -> {2n+x == 1n+Nat.add(x, 1n) : Nat}:
  Equal.cong(Nat, Nat, z => 1n+z, 1n+x, Nat.add(x, 1n),
    Equal.sym(Nat, Nat.add(x, 1n), 1n+x, Equal.trans(Nat, Nat.add(x, 1n), 1n+Nat.add(x, 0n), 1n+x, N.add_succ_r(x, 0n),
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(x, 0n), x, N.add_zero(x)))))

# a swap from mode 1, whose top frame sp, of kind1, holds a to evaluate: sp
# becomes a frame of kind2 with the header hd that holds the focus, and a is
# the focus, to evaluate (hE: the round's run); the frame's measure pays for
# a's and the new frame's (ewf), and a frame of kind2 around the value focus
# is what one of kind1 was around a (epl, ok2)
def sw.go(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32,
  +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat,
  +fs: List<&2, D.AF>, +ps: List<&2, U32>, +focus: Bk.Term, +kind1: D.FK, +q: Bk.Quan, +k: Bool, +a: Bk.Term, +b: Bk.Term,
  +kind2: D.FK, +q2: Bk.Quan, +hd: U32,
  iv: D.InvOf(ds, ks, img, D.RG(foc, 1, sp, pend, D.R59.list(rest)), m, nx, fi, im, Nil{}, 0, t, w, True{}, focus,
    Con{D.AF{kind1, q, k, a, b}, fs}, foc, sp, pend, ps, rest),
  +htg2: {D.TgW(hd) == D.FK.tag(kind2) : U32}, +hq2: {D.QnW(hd) == Mc.Img.quan(q2) : U32},
  +hst2: {D.FlW(hd, 1024) == False{} : Bool}, +hk2: {D.FlW(hd, 2048) == False{} : Bool},
  +hb1: {U32.is_eq(D.FK.tag(kind1), 38) == False{} : Bool}, +hb2: {U32.is_eq(D.FK.tag(kind2), 38) == False{} : Bool},
  hfb2: D.Frs.b(ds, Cr.Cir.Cells.set(m, sp, sw.cell(m, sp, hd, foc)), im, fi, nx, ks, img, D.Fd(3n, m, sp), kind2, b),
  +eb1: {D.Fr.rts.b(m, sp, kind1, b) == Nil{} : List<&2, D.Rt>},
  +eb2: {D.Fr.rts.b(Cr.Cir.Cells.set(m, sp, sw.cell(m, sp, hd, foc)), sp, kind2, b) == Nil{} : List<&2, D.Rt>},
  epl: {D.A.plug(D.AF{kind1, q, k, a, b}, focus) == D.A.plug(D.AF{kind2, q2, False{}, focus, b}, a) : Bk.Term},
  ok2: {El.Eval.vals(ds, focus, False{}) == True{} : Bool} -> D.AF.ok(ds, D.AF{kind2, q2, False{}, focus, b}),
  ewf: {D.A.w.frame(D.AF{kind1, q, k, a, b}) == 1n+Nat.add(D.A.w3(a), D.A.w.frame(D.AF{kind2, q2, False{}, focus, b})) : Nat},
  hE: @f: Nat -> {Cr.Cir.exec(f, D.B.body(), D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)) ==
    Cr.Cir.Out.next{D.S(D.Fd(2n, m, sp), 0, sp, pend, R59.sw(rest, sp, D.FK.tag(kind1), U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3), D.Fd(2n, m, sp)),
      Cr.Cir.Cells.set(m, sp, sw.cell(m, sp, hd, foc)), nx, fi, im, pg, lim, inp)} : Cr.Cir.Out},
  hE0: {Cr.Cir.exec(0n, D.B.body(), D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)) ==
    Cr.Cir.Out.next{D.S(D.Fd(2n, m, sp), 0, sp, pend, R59.sw(rest, sp, D.FK.tag(kind1), U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3), D.Fd(2n, m, sp)),
      Cr.Cir.Cells.set(m, sp, sw.cell(m, sp, hd, foc)), nx, fi, im, pg, lim, inp)} : Cr.Cir.Out},
  +zs: List<&2, D.Rt>,
  hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, [D.Rt{foc, focus}], Nil{}, sp, Con{D.AF{kind1, q, k, a, b}, fs}, ps, zs)) ->
  K.MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  match iv:
    case Tuple{et, Tuple{ew, Tuple{evv, Tuple{afs, Tuple{_, Tuple{+isf, Tuple{+frs, Tuple{+hp, Tuple{+io, Tuple{_, _}}}}}}}}}}:
      +AF1 = {D.AF{kind1, q, k, a, b} : D.AF}
      +AF2 = {D.AF{kind2, q2, False{}, focus, b} : D.AF}
      +n = D.Fd(2n, m, sp)
      +M2 = Cr.Cir.Cells.set(m, sp, sw.cell(m, sp, hd, foc))
      +fr2 = {Con{AF2, fs} : List<&2, D.AF>}
      +rest2 = R59.sw(rest, sp, D.FK.tag(kind1), U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3), n)
      +ST0 = D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)
      +ST2 = D.S(n, 0, sp, pend, rest2, M2, nx, fi, im, pg, lim, inp)
      +core = sw.core(ds, ks, img, m, nx, fi, im, focus, fs, foc, sp, pend, ps, kind1, q, k, a, b, kind2, q2, hd,
        htg2, hq2, hst2, hk2, hb1, hb2, hfb2, isf, hp, io, frs)
      +acc = sw.acc(ds, ks, img, m, nx, fi, im, focus, fs, foc, sp, pend, ps, kind1, q, k, a, b, kind2, q2, hd, zs, htg2, hst2,
        eb1, eb2, isf, hp, io, frs.hops(Con{AF1, fs}, ds, m, im, fi, nx, ks, img, ps, sp, frs), frs, hac)
      +W = D.A.w.frames(fs)
      +A3 = D.A.w3(a)
      +F2 = D.A.w.frame(AF2)
      +w2 = D.A.w(False{}, a, fr2)
      +e3 = Equal.trans(Nat, 1n+Nat.add(A3, Nat.add(F2, W)), 1n+Nat.add(Nat.add(A3, F2), W), Nat.add(D.A.w.frame(AF1), W),
        Equal.cong(Nat, Nat, z => 1n+z, Nat.add(A3, Nat.add(F2, W)), Nat.add(Nat.add(A3, F2), W),
          Equal.sym(Nat, Nat.add(Nat.add(A3, F2), W), Nat.add(A3, Nat.add(F2, W)), add.assoc(A3, F2, W))),
        Equal.sym(Nat, Nat.add(D.A.w.frame(AF1), W), Nat.add(1n+Nat.add(A3, F2), W),
          Equal.cong(Nat, Nat, x => Nat.add(x, W), D.A.w.frame(AF1), 1n+Nat.add(A3, F2), ewf)))
      +lt = {(%Equal.trans(Nat, 1n+w2, Nat.add(D.A.w.frame(AF1), W), w, e3, ew) : N.Le(1n+w2, _); N.le_refl(1n+w2)) : N.Le(1n+w2, w)}
      +et2 = {(%epl : {D.A.plugs(fs, _) == t : Bk.Term}; et) : {D.A.plugs(fr2, a) == t : Bk.Term}}
      +afs2 = {(ok2(evv), p2.snd(D.AF.ok(ds, AF1), D.AFs.ok(ds, fs), afs)) : D.AFs.ok(ds, fr2)}
      +inv = sw.inv(ds, ks, img, M2, nx, fi, im, pg, lim, inp, t, a, fr2, n, sp, pend, ps, rest2, et2, afs2, core, (zs, acc))
      sw.mv(ds, ks, img, ST0, ST2, t, w, w2, hE, hE0, inv, lt, N.le_refl(D.Mem.cells(ST0)))

# The App swap
# ------------

# the round of the App swap, to the state of Inv
def sw.app.E2(+f: Nat, +foc: U32, +sp: U32, +pend: U32, +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32,
  +lim: U32, +inp: List<&2, Word(8n)>, +kind: D.FK, +q: Bk.Quan, +hk: {K.FK.isapp(kind) == True{} : Bool},
  +hz: {U32.is_eq(sp, 0) == False{} : Bool}, +hc: {Cr.Cir.is_cell(sp, im, fi, nx) == True{} : Bool},
  +ht: {D.Tg(m, sp) == D.FK.tag(kind) : U32}, +hq: D.Qs(Cr.Cir.Cells.get(m, sp), q), +hkn: {D.Fl(m, sp, 2048) == False{} : Bool},
  +nz: {U32.is_zero(Wa.Wasm.op(Wa.Wasm.Op.and{}, Wa.Wasm.op(Wa.Wasm.Op.ne{}, Mc.Img.quan(q), 0), Bool.to_u32(U32.is_zero(Bool.to_u32(False{}))))) == False{} : Bool}) ->
  {Cr.Cir.exec(f, D.B.body(), D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)) ==
    Cr.Cir.Out.next{D.S(D.Fd(2n, m, sp), 0, sp, pend, R59.sw(rest, sp, D.FK.tag(kind), U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3), D.Fd(2n, m, sp)),
      Cr.Cir.Cells.set(m, sp, sw.cell(m, sp, sw.hd(34, Mc.Img.quan(q)), foc)), nx, fi, im, pg, lim, inp)} : Cr.Cir.Out}:
  sw.E2(f, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, D.FK.tag(kind), sw.hd(34, Mc.Img.quan(q)),
    sw.app.E(f, kind, D.RG(foc, 1, sp, pend, D.R59.list(rest)), m, nx, fi, im, pg, lim, inp, sp, foc, Mc.Img.quan(q), hk,
      rg.len(rest, foc, 1, sp, pend), {==}, {==}, {==}, hz, hc, ht, hq, hkn, nz))

# mode 1, App q □ a with q live and a not known: a to evaluate, in the frame App q v □
def sw.app.go(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32,
  +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat,
  +fs: List<&2, D.AF>, +ps: List<&2, U32>, +focus: Bk.Term, +kind: D.FK, +q: Bk.Quan, +a: Bk.Term, +b: Bk.Term,
  +iv: D.InvOf(ds, ks, img, D.RG(foc, 1, sp, pend, D.R59.list(rest)), m, nx, fi, im, Nil{}, 0, t, w, True{}, focus,
    Con{D.AF{kind, q, False{}, a, b}, fs}, foc, sp, pend, ps, rest),
  +hk: {K.FK.isapp(kind) == True{} : Bool}, +hlv: {El.Quan.live(q) == True{} : Bool},
  +htg2: {D.TgW(sw.hd(34, Mc.Img.quan(q))) == 34 : U32}, +hq2: {D.QnW(sw.hd(34, Mc.Img.quan(q))) == Mc.Img.quan(q) : U32},
  +hst2: {D.FlW(sw.hd(34, Mc.Img.quan(q)), 1024) == False{} : Bool}, +hk2: {D.FlW(sw.hd(34, Mc.Img.quan(q)), 2048) == False{} : Bool},
  +nz: {U32.is_zero(Wa.Wasm.op(Wa.Wasm.Op.and{}, Wa.Wasm.op(Wa.Wasm.Op.ne{}, Mc.Img.quan(q), 0), Bool.to_u32(U32.is_zero(Bool.to_u32(False{}))))) == False{} : Bool},
  +zs: List<&2, D.Rt>,
  hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, [D.Rt{foc, focus}], Nil{}, sp, Con{D.AF{kind, q, False{}, a, b}, fs}, ps, zs)) ->
  K.MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  match iv:
    case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{+frs, _}}}}}}}:
      +hz = fr.nz(ds, m, im, fi, nx, ks, img, ps, sp, kind, q, False{}, a, b, fs, frs)
      +hc = fr.cell(ds, m, im, fi, nx, ks, img, ps, sp, kind, q, False{}, a, b, fs, frs)
      +ht = fr.tag(ds, m, im, fi, nx, ks, img, ps, sp, kind, q, False{}, a, b, fs, frs)
      +hq = fr.q(ds, m, im, fi, nx, ks, img, ps, sp, kind, q, False{}, a, b, fs, frs)
      +hkn = fr.k(ds, m, im, fi, nx, ks, img, ps, sp, kind, q, False{}, a, b, fs, frs)
      sw.go(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, focus, kind, q, False{}, a, b, D.FK.fun{}, q,
        sw.hd(34, Mc.Img.quan(q)), iv, htg2, hq2, hst2, hk2, sw.not38(kind, hk), {==}, Unit{}, frb.nil(kind, hk, m, sp, b), {==},
        sw.plug(kind, hk, q, False{}, a, b, focus),
        e => (%Equal.sym(Bool, El.Quan.live(q), True{}, hlv) : {Bool.and(_, El.Eval.vals(ds, focus, False{})) == True{} : Bool}; e),
        Equal.trans(Nat, D.A.w.frame(D.AF{kind, q, False{}, a, b}), 2n+D.A.w3(a), 1n+Nat.add(D.A.w3(a), 1n), sw.w(kind, hk, q, a, b, hlv),
          w.one(D.A.w3(a))),
        f => sw.app.E2(f, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, kind, q, hk, hz, hc, ht, hq, hkn, nz),
        sw.app.E2(0n, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, kind, q, hk, hz, hc, ht, hq, hkn, nz), zs, hac)

# the App swap, by the frame's quantity and flag K
def sw.app.mv(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32,
  +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat,
  +fs: List<&2, D.AF>, +ps: List<&2, U32>, +focus: Bk.Term, +kind: D.FK, q: Bk.Quan, k: Bool, +a: Bk.Term, +b: Bk.Term,
  iv: D.InvOf(ds, ks, img, D.RG(foc, 1, sp, pend, D.R59.list(rest)), m, nx, fi, im, Nil{}, 0, t, w, True{}, focus,
    Con{D.AF{kind, q, k, a, b}, fs}, foc, sp, pend, ps, rest),
  hk: {K.FK.isapp(kind) == True{} : Bool}, hs: {Bool.and(El.Quan.live(q), Bool.not(k)) == True{} : Bool}, +zs: List<&2, D.Rt>,
  hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, [D.Rt{foc, focus}], Nil{}, sp, Con{D.AF{kind, q, k, a, b}, fs}, ps, zs)) ->
  K.MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  match q k:
    case Bk.Quan.Q0{} _:
      D.bool.ft(K.MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w), hs)
    case Bk.Quan.Q1{} True{}:
      D.bool.ft(K.MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w), hs)
    case Bk.Quan.Q1{} False{}:
      sw.app.go(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, focus, kind, Bk.Quan.Q1{}, a, b, iv, hk,
        {==}, {==}, {==}, {==}, {==}, {==}, zs, hac)
    case Bk.Quan.Q2{} True{}:
      D.bool.ft(K.MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w), hs)
    case Bk.Quan.Q2{} False{}:
      sw.app.go(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, focus, kind, Bk.Quan.Q2{}, a, b, iv, hk,
        {==}, {==}, {==}, {==}, {==}, {==}, zs, hac)

# The Tup and Min swaps
# ---------------------

# a round from mode 1 with a Tup q □ b frame on top: M.swap to Tup q v □
def sw.tupb.E(+f: Nat, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32,
  +inp: List<&2, Word(8n)>, +sp: U32, +foc: U32, +qv: U32, +hl: {List.length(&2, U32, regs) == 63n : Nat},
  +h0: {List.get(&2, U32, regs, 0n) == Some{foc} : Maybe<&2, U32>},
  h1: {List.get(&2, U32, regs, 1n) == Some{1} : Maybe<&2, U32>}, h2: {List.get(&2, U32, regs, 2n) == Some{sp} : Maybe<&2, U32>},
  hz: {U32.is_eq(sp, 0) == False{} : Bool}, +hc: {Cr.Cir.is_cell(sp, im, fi, nx) == True{} : Bool},
  ht: {U32.and(Cr.Cir.Cell.get(0n, Cr.Cir.Cells.get(m, sp)), 63) == 36 : U32},
  hq: {U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3) == qv : U32}) ->
  {Cr.Cir.exec(f, X.X.body(), X.X.st(regs, m, nx, fi, im, pg, lim, inp)) ==
    Cr.Cir.Out.next{X.X.st(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(regs, 9n, sp), 10n, 36), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)),
      15n, D.Fd(2n, m, sp)), 0n, D.Fd(2n, m, sp)), 1n, 0), X.X.put(X.X.put(m, 0n, sp, sw.hd(37, qv)), 2n, sp, foc), nx, fi, im, pg, lim, inp)} : Cr.Cir.Out}:
  +RES = {Cr.Cir.Out.next{X.X.st(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(regs, 9n, sp), 10n, 36), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)),
      15n, D.Fd(2n, m, sp)), 0n, D.Fd(2n, m, sp)), 1n, 0), X.X.put(X.X.put(m, 0n, sp, sw.hd(37, qv)), 2n, sp, foc), nx, fi, im, pg, lim, inp)} : Cr.Cir.Out}
  Equal.trans(Cr.Cir.Out, Cr.Cir.exec(f, X.X.body(), X.X.st(regs, m, nx, fi, im, pg, lim, inp)),
    Cr.Cir.exec(f, Mc.M.swap(Mc.M.header(37, Mc.M.g(14n), Mc.M.c(0))), X.ret.st(regs, m, nx, fi, im, pg, lim, inp, sp, 36)), RES,
    X.ret.disp.tupb(f, regs, m, nx, fi, im, pg, lim, inp, sp, hl, h1, h2, hz, hc, ht),
    sw.hdr(f, regs, m, nx, fi, im, pg, lim, inp, sp, foc, 36, 37, qv, hl, h0, hc, hq))

# the round of the Tup swap, to the state of Inv
def sw.tupb.E2(+f: Nat, +foc: U32, +sp: U32, +pend: U32, +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32,
  +lim: U32, +inp: List<&2, Word(8n)>, +q: Bk.Quan, +hz: {U32.is_eq(sp, 0) == False{} : Bool},
  +hc: {Cr.Cir.is_cell(sp, im, fi, nx) == True{} : Bool}, +ht: {D.Tg(m, sp) == 36 : U32}, +hq: D.Qs(Cr.Cir.Cells.get(m, sp), q)) ->
  {Cr.Cir.exec(f, D.B.body(), D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)) ==
    Cr.Cir.Out.next{D.S(D.Fd(2n, m, sp), 0, sp, pend, R59.sw(rest, sp, 36, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3), D.Fd(2n, m, sp)),
      Cr.Cir.Cells.set(m, sp, sw.cell(m, sp, sw.hd(37, Mc.Img.quan(q)), foc)), nx, fi, im, pg, lim, inp)} : Cr.Cir.Out}:
  sw.E2(f, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, 36, sw.hd(37, Mc.Img.quan(q)),
    sw.tupb.E(f, D.RG(foc, 1, sp, pend, D.R59.list(rest)), m, nx, fi, im, pg, lim, inp, sp, foc, Mc.Img.quan(q),
      rg.len(rest, foc, 1, sp, pend), {==}, {==}, {==}, hz, hc, ht, hq))

# mode 1, Tup q □ b, with the value v: b to evaluate, in the frame Tup q v □
def sw.tupb.go(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32,
  +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat,
  +fs: List<&2, D.AF>, +ps: List<&2, U32>, +focus: Bk.Term, +q: Bk.Quan, +k: Bool, +a: Bk.Term, +b: Bk.Term,
  +iv: D.InvOf(ds, ks, img, D.RG(foc, 1, sp, pend, D.R59.list(rest)), m, nx, fi, im, Nil{}, 0, t, w, True{}, focus,
    Con{D.AF{D.FK.tupb{}, q, k, a, b}, fs}, foc, sp, pend, ps, rest),
  +htg2: {D.TgW(sw.hd(37, Mc.Img.quan(q))) == 37 : U32}, +hq2: {D.QnW(sw.hd(37, Mc.Img.quan(q))) == Mc.Img.quan(q) : U32},
  +hst2: {D.FlW(sw.hd(37, Mc.Img.quan(q)), 1024) == False{} : Bool}, +hk2: {D.FlW(sw.hd(37, Mc.Img.quan(q)), 2048) == False{} : Bool},
  +zs: List<&2, D.Rt>,
  hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, [D.Rt{foc, focus}], Nil{}, sp, Con{D.AF{D.FK.tupb{}, q, k, a, b}, fs}, ps, zs)) ->
  K.MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  match iv:
    case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{+frs, _}}}}}}}:
      +KD = {D.FK.tupb{} : D.FK}
      +hz = fr.nz(ds, m, im, fi, nx, ks, img, ps, sp, KD, q, k, a, b, fs, frs)
      +hc = fr.cell(ds, m, im, fi, nx, ks, img, ps, sp, KD, q, k, a, b, fs, frs)
      +ht = fr.tag(ds, m, im, fi, nx, ks, img, ps, sp, KD, q, k, a, b, fs, frs)
      +hq = fr.q(ds, m, im, fi, nx, ks, img, ps, sp, KD, q, k, a, b, fs, frs)
      +HD = sw.hd(37, Mc.Img.quan(q))
      sw.go(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, focus, KD, q, k, a, b, D.FK.tupa{}, q, HD,
        iv, htg2, hq2, hst2, hk2, {==}, {==}, Unit{}, {==}, {==}, {==},
        e => (%Equal.sym(Bool, El.Eval.vals(ds, focus, False{}), True{}, e) : {Bool.or(Bool.not(El.Quan.live(q)), _) == True{} : Bool};
          A.or.true(Bool.not(El.Quan.live(q)))),
        w.one(D.A.w3(a)),
        f => sw.tupb.E2(f, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, q, hz, hc, ht, hq),
        sw.tupb.E2(0n, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, q, hz, hc, ht, hq), zs, hac)

# the Tup swap, by the frame's quantity
def sw.tupb.mv(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32,
  +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat,
  +fs: List<&2, D.AF>, +ps: List<&2, U32>, +focus: Bk.Term, q: Bk.Quan, +k: Bool, +a: Bk.Term, +b: Bk.Term,
  iv: D.InvOf(ds, ks, img, D.RG(foc, 1, sp, pend, D.R59.list(rest)), m, nx, fi, im, Nil{}, 0, t, w, True{}, focus,
    Con{D.AF{D.FK.tupb{}, q, k, a, b}, fs}, foc, sp, pend, ps, rest),
  +zs: List<&2, D.Rt>,
  hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, [D.Rt{foc, focus}], Nil{}, sp, Con{D.AF{D.FK.tupb{}, q, k, a, b}, fs}, ps, zs)) ->
  K.MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  match q:
    case Bk.Quan.Q0{}:
      sw.tupb.go(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, focus, Bk.Quan.Q0{}, k, a, b, iv,
        {==}, {==}, {==}, {==}, zs, hac)
    case Bk.Quan.Q1{}:
      sw.tupb.go(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, focus, Bk.Quan.Q1{}, k, a, b, iv,
        {==}, {==}, {==}, {==}, zs, hac)
    case Bk.Quan.Q2{}:
      sw.tupb.go(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, focus, Bk.Quan.Q2{}, k, a, b, iv,
        {==}, {==}, {==}, {==}, zs, hac)

# M.swap with the constant header k2
def sw.hdr.c(+f: Nat, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>,
  +sp: U32, +foc: U32, +T: U32, +k2: U32, +hl: {List.length(&2, U32, regs) == 63n : Nat},
  h0: {List.get(&2, U32, regs, 0n) == Some{foc} : Maybe<&2, U32>}, hc: {Cr.Cir.is_cell(sp, im, fi, nx) == True{} : Bool}) ->
  {Cr.Cir.exec(f, Mc.M.swap(Mc.M.c(k2)), X.ret.st(regs, m, nx, fi, im, pg, lim, inp, sp, T)) ==
    Cr.Cir.Out.next{X.X.st(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(regs, 9n, sp), 10n, T), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)),
      15n, D.Fd(2n, m, sp)), 0n, D.Fd(2n, m, sp)), 1n, 0), X.X.put(X.X.put(m, 0n, sp, k2), 2n, sp, foc), nx, fi, im, pg, lim, inp)} : Cr.Cir.Out}:
  +Q = U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)
  +r1 = X.X.set(regs, 9n, sp)
  +r2 = X.X.set(r1, 10n, T)
  +l2 = X.L.len(r1, 10n, T, 63n, X.L.len(regs, 9n, sp, 63n, hl))
  +l3 = X.L.len(r2, 14n, Q, 63n, l2)
  +g0 = X.L.go(r2, 14n, 0n, Q, foc, {==}, X.L.go(r1, 10n, 0n, T, foc, {==}, X.L.go(regs, 9n, 0n, sp, foc, {==}, h0)))
  +g9 = X.L.go(r2, 14n, 9n, Q, sp, {==}, X.L.go(r1, 10n, 9n, T, sp, {==}, X.L.gs(regs, 9n, sp, X.L.lt(regs, 9n, hl, {==}))))
  X.swap.eq(f, X.X.set(r2, 14n, Q), m, nx, fi, im, pg, lim, inp, sp, foc, Mc.M.c(k2), k2, l3, g0, g9, hc, {==})

# a round from mode 1 with a Min □ b frame on top: M.swap to Min v □
def sw.minb.E(+f: Nat, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32,
  +inp: List<&2, Word(8n)>, +sp: U32, +foc: U32, +hl: {List.length(&2, U32, regs) == 63n : Nat},
  +h0: {List.get(&2, U32, regs, 0n) == Some{foc} : Maybe<&2, U32>},
  h1: {List.get(&2, U32, regs, 1n) == Some{1} : Maybe<&2, U32>}, h2: {List.get(&2, U32, regs, 2n) == Some{sp} : Maybe<&2, U32>},
  hz: {U32.is_eq(sp, 0) == False{} : Bool}, +hc: {Cr.Cir.is_cell(sp, im, fi, nx) == True{} : Bool},
  ht: {U32.and(Cr.Cir.Cell.get(0n, Cr.Cir.Cells.get(m, sp)), 63) == 39 : U32}) ->
  {Cr.Cir.exec(f, X.X.body(), X.X.st(regs, m, nx, fi, im, pg, lim, inp)) ==
    Cr.Cir.Out.next{X.X.st(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(regs, 9n, sp), 10n, 39), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)),
      15n, D.Fd(2n, m, sp)), 0n, D.Fd(2n, m, sp)), 1n, 0), X.X.put(X.X.put(m, 0n, sp, 40), 2n, sp, foc), nx, fi, im, pg, lim, inp)} : Cr.Cir.Out}:
  +RES = {Cr.Cir.Out.next{X.X.st(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(regs, 9n, sp), 10n, 39), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)),
      15n, D.Fd(2n, m, sp)), 0n, D.Fd(2n, m, sp)), 1n, 0), X.X.put(X.X.put(m, 0n, sp, 40), 2n, sp, foc), nx, fi, im, pg, lim, inp)} : Cr.Cir.Out}
  Equal.trans(Cr.Cir.Out, Cr.Cir.exec(f, X.X.body(), X.X.st(regs, m, nx, fi, im, pg, lim, inp)),
    Cr.Cir.exec(f, Mc.M.swap(Mc.M.c(40)), X.ret.st(regs, m, nx, fi, im, pg, lim, inp, sp, 39)), RES,
    X.ret.disp.minb(f, regs, m, nx, fi, im, pg, lim, inp, sp, hl, h1, h2, hz, hc, ht),
    sw.hdr.c(f, regs, m, nx, fi, im, pg, lim, inp, sp, foc, 39, 40, hl, h0, hc))

# the round of the Min swap, to the state of Inv
def sw.minb.E2(+f: Nat, +foc: U32, +sp: U32, +pend: U32, +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32,
  +lim: U32, +inp: List<&2, Word(8n)>, +hz: {U32.is_eq(sp, 0) == False{} : Bool},
  +hc: {Cr.Cir.is_cell(sp, im, fi, nx) == True{} : Bool}, +ht: {D.Tg(m, sp) == 39 : U32}) ->
  {Cr.Cir.exec(f, D.B.body(), D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)) ==
    Cr.Cir.Out.next{D.S(D.Fd(2n, m, sp), 0, sp, pend, R59.sw(rest, sp, 39, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3), D.Fd(2n, m, sp)),
      Cr.Cir.Cells.set(m, sp, sw.cell(m, sp, 40, foc)), nx, fi, im, pg, lim, inp)} : Cr.Cir.Out}:
  sw.E2(f, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, 39, 40,
    sw.minb.E(f, D.RG(foc, 1, sp, pend, D.R59.list(rest)), m, nx, fi, im, pg, lim, inp, sp, foc,
      rg.len(rest, foc, 1, sp, pend), {==}, {==}, {==}, hz, hc, ht))

# mode 1, Min □ b, with the value v: b to evaluate, in the frame Min v □
def sw.minb.go(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32,
  +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat,
  +fs: List<&2, D.AF>, +ps: List<&2, U32>, +focus: Bk.Term, +q: Bk.Quan, +k: Bool, +a: Bk.Term, +b: Bk.Term,
  +iv: D.InvOf(ds, ks, img, D.RG(foc, 1, sp, pend, D.R59.list(rest)), m, nx, fi, im, Nil{}, 0, t, w, True{}, focus,
    Con{D.AF{D.FK.minb{}, q, k, a, b}, fs}, foc, sp, pend, ps, rest),
  +zs: List<&2, D.Rt>,
  hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, [D.Rt{foc, focus}], Nil{}, sp, Con{D.AF{D.FK.minb{}, q, k, a, b}, fs}, ps, zs)) ->
  K.MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  match iv:
    case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{+frs, _}}}}}}}:
      +KD = {D.FK.minb{} : D.FK}
      +hz = fr.nz(ds, m, im, fi, nx, ks, img, ps, sp, KD, q, k, a, b, fs, frs)
      +hc = fr.cell(ds, m, im, fi, nx, ks, img, ps, sp, KD, q, k, a, b, fs, frs)
      +ht = fr.tag(ds, m, im, fi, nx, ks, img, ps, sp, KD, q, k, a, b, fs, frs)
      +A3 = D.A.w3(a)
      sw.go(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, focus, KD, q, k, a, b, D.FK.mina{}, Bk.Quan.Q0{}, 40,
        iv, {==}, {==}, {==}, {==}, {==}, {==}, Unit{}, {==}, {==}, {==}, e => e,
        Equal.cong(Nat, Nat, z => 1n+z, A3, Nat.add(A3, 0n), Equal.sym(Nat, Nat.add(A3, 0n), A3, N.add_zero(A3))),
        f => sw.minb.E2(f, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, hz, hc, ht),
        sw.minb.E2(0n, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, hz, hc, ht), zs, hac)

# Runs with no loop end
# ---------------------
#
# A statement with no while, alloc or emit (Plain) ends with no fuel: only
# a while takes fuel. The moves give Ends this way.

# a statement with no while, alloc or emit
def Plain(s: Cr.Cir.Stmt) -> Bool:
  match s:
    case Cr.Cir.Stmt.seq{a, b}:
      Bool.and(Plain(a), Plain(b))
    case Cr.Cir.Stmt.if{_, t, e}:
      Bool.and(Plain(t), Plain(e))
    case Cr.Cir.Stmt.while{_, _}:
      False{}
    case Cr.Cir.Stmt.alloc{_}:
      False{}
    case Cr.Cir.Stmt.emit{_}:
      False{}
    case _:
      True{}

def ends.setof(rs: Maybe<&2, List<&2, U32>>, st: Cr.Cir.State) -> D.Ends(Cr.Cir.exec.set.of(rs, st)):
  match rs st:
    case Some{_} Cr.Cir.State{_, _, _, _, _, _, _, _, _, _}:
      Unit{}
    case None{} _:
      Unit{}

def ends.set(+r: Nat, v: Maybe<&2, U32>, st: Cr.Cir.State) -> D.Ends(Cr.Cir.exec.set(r, v, st)):
  match v st:
    case Some{+x} Cr.Cir.State{+regs, +m, +nx, +fi, +im, +pg, +lim, +inp, +out, +outn}:
      ends.setof(Cr.Cir.regs.set(regs, r, x), Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, out, outn})
    case None{} _:
      Unit{}

def ends.storeif(ok: Bool, +k: Nat, +i: U32, +v: U32, st: Cr.Cir.State) -> D.Ends(Cr.Cir.exec.store.if(ok, k, i, v, st)):
  match ok st:
    case True{} Cr.Cir.State{_, _, _, _, _, _, _, _, _, _}:
      Unit{}
    case False{} _:
      Unit{}

def ends.store(+k: Nat, c: Maybe<&2, U32>, v: Maybe<&2, U32>, st: Cr.Cir.State) -> D.Ends(Cr.Cir.exec.store(k, c, v, st)):
  match c:
    case Some{+i}:
      match v:
        case Some{+x}:
          match st:
            case Cr.Cir.State{+regs, +m, +nx, +fi, +im, +pg, +lim, +inp, +out, +outn}:
              ends.storeif(Cr.Cir.is_cell(i, im, fi, nx), k, i, x, Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, out, outn})
        case None{}:
          Unit{}
    case None{}:
      Unit{}

def ends.then(o: Cr.Cir.Out, -k: Cr.Cir.State -> Cr.Cir.Out, d: D.Ends(o), dk: @t: Cr.Cir.State -> D.Ends(k(t))) ->
  D.Ends(Cr.Cir.exec.then(o, k)):
  match o:
    case Cr.Cir.Out.next{s}:
      dk(s)
    case Cr.Cir.Out.halt{_, _}:
      Unit{}
    case Cr.Cir.Out.out_of_memory{}:
      Unit{}
    case Cr.Cir.Out.trap{}:
      Unit{}
    case Cr.Cir.Out.not_done{}:
      d

def ends.ifof(z: Bool, -yes: Unit -> Cr.Cir.Out, -no: Unit -> Cr.Cir.Out, dy: D.Ends(yes(Unit{})), dn: D.Ends(no(Unit{}))) ->
  D.Ends(Cr.Cir.exec.if.of(z, yes, no)):
  match z:
    case False{}:
      dy
    case True{}:
      dn

def ends.if(c: Maybe<&2, U32>, -yes: Unit -> Cr.Cir.Out, -no: Unit -> Cr.Cir.Out, dy: D.Ends(yes(Unit{})), dn: D.Ends(no(Unit{}))) ->
  D.Ends(Cr.Cir.exec.if(c, yes, no)):
  match c:
    case Some{+x}:
      ends.ifof(U32.is_zero(x), yes, no, dy, dn)
    case None{}:
      Unit{}

# a plain statement ends with no fuel
def ends.plain(s: Cr.Cir.Stmt, +st: Cr.Cir.State, h: {Plain(s) == True{} : Bool}) -> D.Ends(Cr.Cir.exec(0n, s, st)):
  match s:
    case Cr.Cir.Stmt.nop{}:
      Unit{}
    case Cr.Cir.Stmt.set{+r, +e}:
      ends.set(r, Cr.Cir.eval(e, st), st)
    case Cr.Cir.Stmt.store{+k, +c, +v}:
      ends.store(k, Cr.Cir.eval(c, st), Cr.Cir.eval(v, st), st)
    case Cr.Cir.Stmt.alloc{+r}:
      D.bool.ft(D.Ends(Cr.Cir.exec(0n, Cr.Cir.Stmt.alloc{r}, st)), h)
    case Cr.Cir.Stmt.emit{+v}:
      D.bool.ft(D.Ends(Cr.Cir.exec(0n, Cr.Cir.Stmt.emit{v}, st)), h)
    case Cr.Cir.Stmt.seq{+a, +b}:
      +h2 = h
      ends.then(Cr.Cir.exec(0n, a, st), t => Cr.Cir.exec(0n, b, t), ends.plain(a, st, D.and.l(Plain(a), Plain(b), h2)),
        t => ends.plain(b, t, D.and.r(Plain(a), Plain(b), h2)))
    case Cr.Cir.Stmt.if{+c, +t, +e}:
      +h2 = h
      ends.if(Cr.Cir.eval(c, st), u => Cr.Cir.exec(0n, t, st), u => Cr.Cir.exec(0n, e, st),
        ends.plain(t, st, D.and.l(Plain(t), Plain(e), h2)), ends.plain(e, st, D.and.r(Plain(t), Plain(e), h2)))
    case Cr.Cir.Stmt.while{+c, +b}:
      D.bool.ft(D.Ends(Cr.Cir.exec(0n, Cr.Cir.Stmt.while{c, b}, st)), h)
    case Cr.Cir.Stmt.halt{_}:
      Unit{}

# Eval under frames
# -----------------
#
# A step of the focus is a step of the frames' term (Lean's step_plug): each
# frame's own test (AF.ok) lets the step of its hole through.

def app.some(+q: Bk.Quan, +f: Bk.Term, +x: Bk.Term, sf: Maybe<Bk.Term>, +vf: Bool, +live: Bool, sx: Maybe<Bk.Term>, +vx: Bool,
  r: Maybe<Bk.Term>, +f2: Bk.Term, e: {sf == Some{f2} : Maybe<Bk.Term>}) ->
  {El.Eval.step.app(q, f, x, sf, vf, live, sx, vx, r) == Some{Bk.Term.App{q, f2, x}} : Maybe<Bk.Term>}:
  %Equal.sym(Maybe<Bk.Term>, sf, Some{f2}, e) :
    {El.Eval.step.app(q, f, x, _, vf, live, sx, vx, r) == Some{Bk.Term.App{q, f2, x}} : Maybe<Bk.Term>}
  {==}

def appx.some(+q: Bk.Quan, +f: Bk.Term, +x: Bk.Term, sf: Maybe<Bk.Term>, vf: Bool, live: Bool, sx: Maybe<Bk.Term>, +vx: Bool,
  r: Maybe<Bk.Term>, +x2: Bk.Term, esf: {sf == None{} : Maybe<Bk.Term>}, evf: {vf == True{} : Bool}, el: {live == True{} : Bool},
  e: {sx == Some{x2} : Maybe<Bk.Term>}) ->
  {El.Eval.step.app(q, f, x, sf, vf, live, sx, vx, r) == Some{Bk.Term.App{q, f, x2}} : Maybe<Bk.Term>}:
  %Equal.sym(Maybe<Bk.Term>, sf, None{}, esf) :
    {El.Eval.step.app(q, f, x, _, vf, live, sx, vx, r) == Some{Bk.Term.App{q, f, x2}} : Maybe<Bk.Term>}
  %Equal.sym(Bool, vf, True{}, evf) :
    {El.Eval.step.app(q, f, x, None{}, _, live, sx, vx, r) == Some{Bk.Term.App{q, f, x2}} : Maybe<Bk.Term>}
  %Equal.sym(Bool, live, True{}, el) :
    {El.Eval.step.app(q, f, x, None{}, True{}, _, sx, vx, r) == Some{Bk.Term.App{q, f, x2}} : Maybe<Bk.Term>}
  %Equal.sym(Maybe<Bk.Term>, sx, Some{x2}, e) :
    {El.Eval.step.app(q, f, x, None{}, True{}, True{}, _, vx, r) == Some{Bk.Term.App{q, f, x2}} : Maybe<Bk.Term>}
  {==}

def let.some(+q: Bk.Quan, +v: Bk.Term, +f: Bk.Term, live: Bool, sv: Maybe<Bk.Term>, +vv: Bool, +fits: Bool, +v2: Bk.Term,
  el: {live == True{} : Bool}, e: {sv == Some{v2} : Maybe<Bk.Term>}) ->
  {El.Eval.step.let(q, v, f, live, sv, vv, fits) == Some{Bk.Term.Let{q, v2, f}} : Maybe<Bk.Term>}:
  %Equal.sym(Bool, live, True{}, el) : {El.Eval.step.let(q, v, f, _, sv, vv, fits) == Some{Bk.Term.Let{q, v2, f}} : Maybe<Bk.Term>}
  %Equal.sym(Maybe<Bk.Term>, sv, Some{v2}, e) : {El.Eval.step.let(q, v, f, True{}, _, vv, fits) == Some{Bk.Term.Let{q, v2, f}} : Maybe<Bk.Term>}
  {==}

def tupb.some(+q: Bk.Quan, +a: Bk.Term, +b: Bk.Term, live: Bool, sa: Maybe<Bk.Term>, +va: Bool, sb: Maybe<Bk.Term>, +a2: Bk.Term,
  el: {live == True{} : Bool}, e: {sa == Some{a2} : Maybe<Bk.Term>}) ->
  {El.Eval.step.tup(q, a, b, live, sa, va, sb) == Some{Bk.Term.Tup{q, a2, b}} : Maybe<Bk.Term>}:
  %Equal.sym(Bool, live, True{}, el) : {El.Eval.step.tup(q, a, b, _, sa, va, sb) == Some{Bk.Term.Tup{q, a2, b}} : Maybe<Bk.Term>}
  %Equal.sym(Maybe<Bk.Term>, sa, Some{a2}, e) : {El.Eval.step.tup(q, a, b, True{}, _, va, sb) == Some{Bk.Term.Tup{q, a2, b}} : Maybe<Bk.Term>}
  {==}

def tupab.some(+q: Bk.Quan, +a: Bk.Term, sb: Maybe<Bk.Term>, +b2: Bk.Term, e: {sb == Some{b2} : Maybe<Bk.Term>}) ->
  {El.Eval.step.tup_b(q, a, sb) == Some{Bk.Term.Tup{q, a, b2}} : Maybe<Bk.Term>}:
  %Equal.sym(Maybe<Bk.Term>, sb, Some{b2}, e) : {El.Eval.step.tup_b(q, a, _) == Some{Bk.Term.Tup{q, a, b2}} : Maybe<Bk.Term>}
  {==}

def tupa.some(+q: Bk.Quan, +a: Bk.Term, +b: Bk.Term, live: Bool, sa: Maybe<Bk.Term>, va: Bool, sb: Maybe<Bk.Term>, +b2: Bk.Term,
  +ok: {Bool.or(Bool.not(live), va) == True{} : Bool}, ha: {va == True{} : Bool} -> {sa == None{} : Maybe<Bk.Term>},
  e: {sb == Some{b2} : Maybe<Bk.Term>}) ->
  {El.Eval.step.tup(q, a, b, live, sa, va, sb) == Some{Bk.Term.Tup{q, a, b2}} : Maybe<Bk.Term>}:
  match live:
    case False{}:
      tupab.some(q, a, sb, b2, e)
    case True{}:
      %Equal.sym(Maybe<Bk.Term>, sa, None{}, ha(ok)) :
        {El.Eval.step.tup(q, a, b, True{}, _, va, sb) == Some{Bk.Term.Tup{q, a, b2}} : Maybe<Bk.Term>}
      %Equal.sym(Bool, va, True{}, ok) :
        {El.Eval.step.tup(q, a, b, True{}, None{}, _, sb) == Some{Bk.Term.Tup{q, a, b2}} : Maybe<Bk.Term>}
      tupab.some(q, a, sb, b2, e)

def rwt.some(+e: Bk.Term, +p: Bk.Term, +f: Bk.Term, se: Maybe<Bk.Term>, +ve: Bool, +e2: Bk.Term, h: {se == Some{e2} : Maybe<Bk.Term>}) ->
  {El.Eval.step.rwt(e, p, f, se, ve) == Some{Bk.Term.Rwt{e2, p, f}} : Maybe<Bk.Term>}:
  %Equal.sym(Maybe<Bk.Term>, se, Some{e2}, h) : {El.Eval.step.rwt(e, p, f, _, ve) == Some{Bk.Term.Rwt{e2, p, f}} : Maybe<Bk.Term>}
  {==}

def minb.some(+a: Bk.Term, +b: Bk.Term, sa: Maybe<Bk.Term>, +va: Bool, sb: Maybe<Bk.Term>, +vb: Bool, mt: Maybe<Bk.Term>, +a2: Bk.Term,
  e: {sa == Some{a2} : Maybe<Bk.Term>}) ->
  {El.Eval.step.min(a, b, sa, va, sb, vb, mt) == Some{Bk.Term.Min{a2, b}} : Maybe<Bk.Term>}:
  %Equal.sym(Maybe<Bk.Term>, sa, Some{a2}, e) : {El.Eval.step.min(a, b, _, va, sb, vb, mt) == Some{Bk.Term.Min{a2, b}} : Maybe<Bk.Term>}
  {==}

def mina.some(+a: Bk.Term, +b: Bk.Term, sa: Maybe<Bk.Term>, va: Bool, sb: Maybe<Bk.Term>, +vb: Bool, mt: Maybe<Bk.Term>, +b2: Bk.Term,
  esa: {sa == None{} : Maybe<Bk.Term>}, eva: {va == True{} : Bool}, e: {sb == Some{b2} : Maybe<Bk.Term>}) ->
  {El.Eval.step.min(a, b, sa, va, sb, vb, mt) == Some{Bk.Term.Min{a, b2}} : Maybe<Bk.Term>}:
  %Equal.sym(Maybe<Bk.Term>, sa, None{}, esa) : {El.Eval.step.min(a, b, _, va, sb, vb, mt) == Some{Bk.Term.Min{a, b2}} : Maybe<Bk.Term>}
  %Equal.sym(Bool, va, True{}, eva) : {El.Eval.step.min(a, b, None{}, _, sb, vb, mt) == Some{Bk.Term.Min{a, b2}} : Maybe<Bk.Term>}
  %Equal.sym(Maybe<Bk.Term>, sb, Some{b2}, e) : {El.Eval.step.min(a, b, None{}, True{}, _, vb, mt) == Some{Bk.Term.Min{a, b2}} : Maybe<Bk.Term>}
  {==}

# one frame around a focus with a step
def step1(+ds: List<&2, Bk.Def>, fr: D.AF, +u: Bk.Term, +u2: Bk.Term, +ok: D.AF.ok(ds, fr),
  +e: {El.Eval.step(ds, u) == Some{u2} : Maybe<Bk.Term>}) ->
  {El.Eval.step(ds, D.A.plug(fr, u)) == Some{D.A.plug(fr, u2)} : Maybe<Bk.Term>}:
  match fr:
    case D.AF{+kind, +q, +k, +a, +b}:
      match kind:
        case D.FK.arg{}:
          app.some(q, u, a, El.Eval.step(ds, u), El.Eval.vals(ds, u, False{}), El.Quan.live(q), El.Eval.step(ds, a), El.Eval.vals(ds, a, False{}),
            El.Eval.redex(ds, q, u, a), u2, e)
        case D.FK.val{}:
          app.some(q, u, a, El.Eval.step(ds, u), El.Eval.vals(ds, u, False{}), El.Quan.live(q), El.Eval.step(ds, a), El.Eval.vals(ds, a, False{}),
            El.Eval.redex(ds, q, u, a), u2, e)
        case D.FK.fun{}:
          +el = D.and.l(El.Quan.live(q), El.Eval.vals(ds, a, False{}), ok)
          +ea = D.and.r(El.Quan.live(q), El.Eval.vals(ds, a, False{}), ok)
          appx.some(q, a, u, El.Eval.step(ds, a), El.Eval.vals(ds, a, False{}), El.Quan.live(q), El.Eval.step(ds, u), El.Eval.vals(ds, u, False{}),
            El.Eval.redex(ds, q, a, u), u2, K.ev.stops(ds, a, ea), ea, el, e)
        case D.FK.let{}:
          let.some(q, u, a, El.Quan.live(q), El.Eval.step(ds, u), El.Eval.vals(ds, u, False{}), El.Quan.fits(q, u), u2, ok, e)
        case D.FK.tupb{}:
          tupb.some(q, u, a, El.Quan.live(q), El.Eval.step(ds, u), El.Eval.vals(ds, u, False{}), El.Eval.step(ds, a), u2, ok, e)
        case D.FK.tupa{}:
          tupa.some(q, a, u, El.Quan.live(q), El.Eval.step(ds, a), El.Eval.vals(ds, a, False{}), El.Eval.step(ds, u), u2, ok,
            h => K.ev.stops(ds, a, h), e)
        case D.FK.rwt{}:
          rwt.some(u, a, b, El.Eval.step(ds, u), El.Eval.vals(ds, u, False{}), u2, e)
        case D.FK.minb{}:
          minb.some(u, a, El.Eval.step(ds, u), El.Eval.vals(ds, u, False{}), El.Eval.step(ds, a), El.Eval.vals(ds, a, False{}), El.Eval.meet(u, a), u2, e)
        case D.FK.mina{}:
          mina.some(a, u, El.Eval.step(ds, a), El.Eval.vals(ds, a, False{}), El.Eval.step(ds, u), El.Eval.vals(ds, u, False{}), El.Eval.meet(a, u), u2,
            K.ev.stops(ds, a, ok), ok, e)

# the frames around a focus with a step
def step.plugs(+ds: List<&2, Bk.Def>, fs: List<&2, D.AF>, +u: Bk.Term, +u2: Bk.Term, hfs: D.AFs.ok(ds, fs),
  e: {El.Eval.step(ds, u) == Some{u2} : Maybe<Bk.Term>}) ->
  {El.Eval.step(ds, D.A.plugs(fs, u)) == Some{D.A.plugs(fs, u2)} : Maybe<Bk.Term>}:
  match fs:
    case Nil{}:
      e
    case Con{+fr, +rest}:
      (ok, oks) = hfs
      step.plugs(ds, rest, D.A.plug(fr, u), D.A.plug(fr, u2), oks, step1(ds, fr, u, u2, ok, e))

# Two roots trade places
# ----------------------
#
# The heap and the accounting see the owned roots as a set: after M.inc of a
# part, the new root is first, and M.dec of the old one wants it first.

# x + (y + z) = y + (x + z)
def add.sw(+x: Nat, +y: Nat, +z: Nat) -> {Nat.add(x, Nat.add(y, z)) == Nat.add(y, Nat.add(x, z)) : Nat}:
  Equal.trans(Nat, Nat.add(x, Nat.add(y, z)), Nat.add(Nat.add(x, y), z), Nat.add(y, Nat.add(x, z)),
    Equal.sym(Nat, Nat.add(Nat.add(x, y), z), Nat.add(x, Nat.add(y, z)), add.assoc(x, y, z)),
    Equal.trans(Nat, Nat.add(Nat.add(x, y), z), Nat.add(Nat.add(y, x), z), Nat.add(y, Nat.add(x, z)),
      Equal.cong(Nat, Nat, w => Nat.add(w, z), Nat.add(x, y), Nat.add(y, x), add.comm(x, y)), add.assoc(y, x, z)))

def ptr.sw2(+N: Nat, +m: Cr.Cir.Cells, +fi: U32, +ps: List<&2, U32>, +a: U32, +b: U32, +rs: List<&2, U32>, +c: U32) ->
  {D.Ptr(N, m, fi, ps, Con{a, Con{b, rs}}, c) == D.Ptr(N, m, fi, ps, Con{b, Con{a, rs}}, c) : Nat}:
  Equal.cong(Nat, Nat, z => Nat.add(D.Pc(N, m, ps, fi, c), z), D.RcL(Con{a, Con{b, rs}}, c), D.RcL(Con{b, Con{a, rs}}, c),
    add.sw(D.Nat.of(U32.is_eq(a, c)), D.Nat.of(U32.is_eq(b, c)), D.RcL(rs, c)))

def pendok.sw2(qs: List<&2, U32>, +ps: List<&2, U32>, +m: Cr.Cir.Cells, +fi: U32, +nx: U32, +a: U32, +b: U32, +rs: List<&2, U32>,
  h: D.PendOK(qs, ps, m, fi, nx, Con{a, Con{b, rs}})) -> D.PendOK(qs, ps, m, fi, nx, Con{b, Con{a, rs}}):
  match qs:
    case Nil{}:
      Unit{}
    case Con{+p, +rest}:
      (ho, r1) = h
      (hs, r2) = r1
      (ht, r3) = r2
      (h0, hr) = r3
      +N = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
      (ho, (hs, (ht, ((%ptr.sw2(N, m, fi, ps, a, b, rs, p) : {_ == 0n : Nat}; h0), pendok.sw2(rest, ps, m, fi, nx, a, b, rs, hr)))))

def cnt.sw2(k: Nat, +m: Cr.Cir.Cells, +c: U32, +N: Nat, +fi: U32, +ps: List<&2, U32>, +a: U32, +b: U32, +rs: List<&2, U32>,
  h: {D.Cnt(k, m, c, N, fi, ps, Con{a, Con{b, rs}}) == True{} : Bool}) -> {D.Cnt(k, m, c, N, fi, ps, Con{b, Con{a, rs}}) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+(+j):
      +h2 = h
      +P1 = D.Ptr(N, m, fi, ps, Con{a, Con{b, rs}}, c)
      +P2 = D.Ptr(N, m, fi, ps, Con{b, Con{a, rs}}, c)
      +V = U32.to_nat(D.Fd(1n, m, c))
      +A0 = Bool.or(Bool.not(U32.is_lt(D.Tg(m, c), 19)), Bool.or(D.Fl(m, c, 1024), Bool.or(D.Mem(ps, c), Nat.is_eq(V, P1))))
      D.and.i(Bool.or(Bool.not(U32.is_lt(D.Tg(m, c), 19)), Bool.or(D.Fl(m, c, 1024), Bool.or(D.Mem(ps, c), Nat.is_eq(V, P2)))),
        D.Cnt(j, m, U32.inc(c), N, fi, ps, Con{b, Con{a, rs}}),
        (%ptr.sw2(N, m, fi, ps, a, b, rs, c) :
            {Bool.or(Bool.not(U32.is_lt(D.Tg(m, c), 19)), Bool.or(D.Fl(m, c, 1024), Bool.or(D.Mem(ps, c), Nat.is_eq(V, _)))) == True{} : Bool};
          D.and.l(A0, D.Cnt(j, m, U32.inc(c), N, fi, ps, Con{a, Con{b, rs}}), h2)),
        cnt.sw2(j, m, U32.inc(c), N, fi, ps, a, b, rs, D.and.r(A0, D.Cnt(j, m, U32.inc(c), N, fi, ps, Con{a, Con{b, rs}}), h2)))

def heap.sw2(+m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +a: U32, +b: U32, +rs: List<&2, U32>, +pend: U32, +ps: List<&2, U32>,
  h: D.Heap(m, nx, fi, im, Con{a, Con{b, rs}}, pend, ps)) -> D.Heap(m, nx, fi, im, Con{b, Con{a, rs}}, pend, ps):
  (hc, r1) = h
  (hp, r2) = r1
  (hcn, r3) = r2
  +N = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
  (hc, (pendok.sw2(ps, ps, m, fi, nx, a, b, rs, hp), (cnt.sw2(N, m, fi, N, fi, ps, a, b, rs, hcn), r3)))

# HS with the first two roots traded, and no borrowed term
def hsk.sw2(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32,
  +fi: U32, +im: U32, +c1: U32, +u1: Bk.Term, +c2: U32, +u2: Bk.Term, +R: List<&2, D.Rt>, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>,
  +sp: U32, +pend: U32, +ps: List<&2, U32>, h: D.HS(ds, ks, img, m, nx, fi, im, Con{D.Rt{c1, u1}, Con{D.Rt{c2, u2}, R}}, bs, fs, sp, pend, ps)) ->
  D.HS(ds, ks, img, m, nx, fi, im, Con{D.Rt{c2, u2}, Con{D.Rt{c1, u1}, R}}, Nil{}, fs, sp, pend, ps):
  match h:
    case Tuple{Tuple{i1, Tuple{i2, ir}}, Tuple{_, Tuple{_, Tuple{hf, Tuple{hp, hi}}}}}:
      ((i2, (i1, ir)), (Unit{}, (Unit{}, (hf, (heap.sw2(m, nx, fi, im, c1, c2, D.Rt.cells(R), pend, ps, hp), hi)))))

# Acc with the first two roots traded (no temporary)
def acc.sw2(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32,
  +fi: U32, +im: U32, +c1: U32, +u1: Bk.Term, +c2: U32, +u2: Bk.Term, +R: List<&2, D.Rt>, +sp: U32, +fs: List<&2, D.AF>,
  +ps: List<&2, U32>, +zs: List<&2, D.Rt>,
  h: D.AccK(True{}, ds, ks, img, m, nx, fi, im, Con{D.Rt{c1, u1}, Con{D.Rt{c2, u2}, R}}, Nil{}, sp, fs, ps, zs)) ->
  D.AccK(True{}, ds, ks, img, m, nx, fi, im, Con{D.Rt{c2, u2}, Con{D.Rt{c1, u1}, R}}, Nil{}, sp, fs, ps, zs):
  (h1, r1) = h
  (h2, r2) = r1
  (h3, r3) = r2
  (hcov, r4) = r3
  (hclo, _) = r4
  +N = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
  +C = List.append(&2, D.Rt, R, List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs))
  +XS = List.append(&2, U32, D.Fr.cells(fs, m, sp), ps)
  (h1, (h2, (h3, (A.cov.mv(D.Cov(N, m, fi, Con{D.Rt{c1, u1}, Con{D.Rt{c2, u2}, C}}, XS), D.Cov(N, m, fi, Con{D.Rt{c2, u2}, Con{D.Rt{c1, u1}, C}}, XS),
    A.cov.perm(N, m, fi, Nil{}, [D.Rt{c1, u1}], [D.Rt{c2, u2}], C, XS), hcov), (hclo, {==})))))

# a term's root is a node of it
def node.root(t: Bk.Term, +m: Cr.Cir.Cells, +r: U32) -> {D.Node(t, m, r, r) == True{} : Bool}:
  match t:
    case Bk.Term.Var{_}:
      D.u32.refl(r)
    case Bk.Term.Ref{_}:
      D.u32.refl(r)
    case Bk.Term.Ann{+y, +z}:
      D.or.l(U32.is_eq(r, r), Bool.or(D.Node(y, m, D.Fd(2n, m, r), r), D.Node(z, m, D.Fd(3n, m, r), r)), D.u32.refl(r))
    case Bk.Term.Let{_, +v, +f}:
      D.or.l(U32.is_eq(r, r), Bool.or(D.Node(v, m, D.Fd(2n, m, r), r), D.Node(f, m, D.Fd(3n, m, r), r)), D.u32.refl(r))
    case Bk.Term.Typ{+y}:
      D.or.l(U32.is_eq(r, r), D.Node(y, m, D.Fd(2n, m, r), r), D.u32.refl(r))
    case Bk.Term.Min{+a, +b}:
      D.or.l(U32.is_eq(r, r), Bool.or(D.Node(a, m, D.Fd(2n, m, r), r), D.Node(b, m, D.Fd(3n, m, r), r)), D.u32.refl(r))
    case Bk.Term.All{_, +a, +b}:
      D.or.l(U32.is_eq(r, r), Bool.or(D.Node(a, m, D.Fd(2n, m, r), r), D.Node(b, m, D.Fd(3n, m, r), r)), D.u32.refl(r))
    case Bk.Term.Lam{_, +f}:
      D.or.l(U32.is_eq(r, r), D.Node(f, m, D.Fd(2n, m, r), r), D.u32.refl(r))
    case Bk.Term.App{_, +f, +y}:
      D.or.l(U32.is_eq(r, r), Bool.or(D.Node(f, m, D.Fd(2n, m, r), r), D.Node(y, m, D.Fd(3n, m, r), r)), D.u32.refl(r))
    case Bk.Term.Sig{_, +a, +b}:
      D.or.l(U32.is_eq(r, r), Bool.or(D.Node(a, m, D.Fd(2n, m, r), r), D.Node(b, m, D.Fd(3n, m, r), r)), D.u32.refl(r))
    case Bk.Term.Tup{_, +a, +b}:
      D.or.l(U32.is_eq(r, r), Bool.or(D.Node(a, m, D.Fd(2n, m, r), r), D.Node(b, m, D.Fd(3n, m, r), r)), D.u32.refl(r))
    case Bk.Term.Prj{+h}:
      D.or.l(U32.is_eq(r, r), D.Node(h, m, D.Fd(2n, m, r), r), D.u32.refl(r))
    case Bk.Term.Enu{_}:
      D.u32.refl(r)
    case Bk.Term.Lab{_}:
      D.u32.refl(r)
    case Bk.Term.Mat{_, +h, +n}:
      D.or.l(U32.is_eq(r, r), Bool.or(D.Node(h, m, D.Fd(3n, m, r), r), D.Node(n, m, D.Fd(4n, m, r), r)), D.u32.refl(r))
    case Bk.Term.Efq{}:
      D.u32.refl(r)
    case Bk.Term.Eql{+a, +b, +y}:
      D.or.l(U32.is_eq(r, r), Bool.or(D.Node(a, m, D.Fd(2n, m, r), r), Bool.or(D.Node(b, m, D.Fd(3n, m, r), r), D.Node(y, m, D.Fd(4n, m, r), r))),
        D.u32.refl(r))
    case Bk.Term.Rfl{}:
      D.u32.refl(r)
    case Bk.Term.Rwt{+e, +y, +f}:
      D.or.l(U32.is_eq(r, r), Bool.or(D.Node(e, m, D.Fd(2n, m, r), r), Bool.or(D.Node(y, m, D.Fd(3n, m, r), r), D.Node(f, m, D.Fd(4n, m, r), r))),
        D.u32.refl(r))

# a then b, when a's run is another's
def seq.cong(+f: Nat, a: Cr.Cir.Stmt, a2: Cr.Cir.Stmt, +b: Cr.Cir.Stmt, +st: Cr.Cir.State,
  e: {Cr.Cir.exec(f, a, st) == Cr.Cir.exec(f, a2, st) : Cr.Cir.Out}) ->
  {Cr.Cir.exec(f, Cr.Cir.Stmt.seq{a, b}, st) == Cr.Cir.exec(f, Cr.Cir.Stmt.seq{a2, b}, st) : Cr.Cir.Out}:
  match f:
    case 0n:
      %e : {Cr.Cir.exec.then(Cr.Cir.exec(0n, a, st), u => Cr.Cir.exec(0n, b, u)) == Cr.Cir.exec.then(_, u => Cr.Cir.exec(0n, b, u)) : Cr.Cir.Out}
      {==}
    case 1n+g:
      %e : {Cr.Cir.exec.then(Cr.Cir.exec(1n+g, a, st), u => Cr.Cir.exec(1n+g, b, u)) == Cr.Cir.exec.then(_, u => Cr.Cir.exec(1n+g, b, u)) : Cr.Cir.Out}
      {==}

# The Ann step
# ------------
#
# Ann x y steps to x (M.ev.ann): register n gets x's cell, a part of the
# focus' cell, M.inc makes it a root, M.dec drops the focus' cell, and x is
# the focus. Eval's step of the focus is the step of the whole term
# (step.plugs).

# the registers after M.ev.ann: c, tag, n, dr set, the focus n
def R59.ann(x: D.R59, +foc: U32, +tg: U32, +n: U32, +d: U32) -> D.R59:
  match x:
    case D.R59{+r4, +r5, +r6, +r7, +r8, +r9, +r10, +r11, +r12, +r13, +r14, +r15, +r16, +r17, +r18, +r19, +r20, +r21, +r22, +r23, +r24, +r25, +r26, +r27, +r28, +r29, +r30, +r31, +r32, +r33, +r34, +r35, +r36, +r37, +r38, +r39, +r40, +r41, +r42, +r43, +r44, +r45, +r46, +r47, +r48, +r49, +r50, +r51, +r52, +r53, +r54, +r55, +r56, +r57, +r58, +r59, +r60, +r61, +r62}:
      D.R59{r4, d, r6, r7, foc, r9, tg, r11, r12, r13, r14, n, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}

def ann.regs(x: D.R59, +foc: U32, +sp: U32, +pend: U32, +tg: U32, +n: U32, +d: U32, +pend2: U32) ->
  {X.X.set(List.set(&2, U32, List.set(&2, U32, X.X.set(X.X.set(X.X.set(D.RG(foc, 0, sp, pend, D.R59.list(x)), 8n, foc), 10n, tg), 15n, n), 5n, d), 3n, pend2), 0n, n) ==
    D.RG(n, 0, sp, pend2, D.R59.list(R59.ann(x, foc, tg, n, d))) : List<&2, U32>}:
  match x:
    case D.R59{+r4, +r5, +r6, +r7, +r8, +r9, +r10, +r11, +r12, +r13, +r14, +r15, +r16, +r17, +r18, +r19, +r20, +r21, +r22, +r23, +r24, +r25, +r26, +r27, +r28, +r29, +r30, +r31, +r32, +r33, +r34, +r35, +r36, +r37, +r38, +r39, +r40, +r41, +r42, +r43, +r44, +r45, +r46, +r47, +r48, +r49, +r50, +r51, +r52, +r53, +r54, +r55, +r56, +r57, +r58, +r59, +r60, +r61, +r62}:
      {==}

# M.ev.ann then nop is plain
def plain.ann() -> {Plain(Cr.Cir.Stmt.seq{Mc.M.ev.ann(), Cr.Cir.Stmt.nop{}}) == True{} : Bool}:
  {==}

# a round from mode 0 whose focus is Ann x y: c and tag are set, and
# M.ev's tests take the Ann branch
def ann.E(+f: Nat, +ds: List<&2, Bk.Def>, +foc: U32, +sp: U32, +pend: U32, +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +x: Bk.Term, +y: Bk.Term,
  +nd: D.Nd(ds, im, fi, nx, foc, Cr.Cir.Cells.get(m, foc), Bk.Term.Ann{x, y}, 2),
  +tb: D.Tbl(m, im, fi, nx), +hv: {D.Fl(m, foc, 256) == False{} : Bool}) ->
  {Cr.Cir.exec(f, D.B.body(), D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp)) ==
    Cr.Cir.exec(f, Cr.Cir.Stmt.seq{Mc.M.ev.ann(), Cr.Cir.Stmt.nop{}},
      X.X.st(X.X.set(X.X.set(D.RG(foc, 0, sp, pend, D.R59.list(rest)), 8n, foc), 10n, D.TgW(D.Fd(0n, m, foc))), m, nx, fi, im, pg, lim, inp)) : Cr.Cir.Out}:
  match nd:
    case Tuple{+valid, Tuple{_, Tuple{+etag, _}}}:
      +AN = {Bk.Term.Ann{x, y} : Bk.Term}
      +R0 = D.RG(foc, 0, sp, pend, D.R59.list(rest))
      +hl0 = rg.len(rest, foc, 0, sp, pend)
      +f0 = D.Fd(0n, m, foc)
      +TG = D.TgW(f0)
      +R1 = X.X.set(R0, 8n, foc)
      +R2 = X.X.set(R1, 10n, TG)
      +hl1 = X.L.len(R0, 8n, foc, 63n, hl0)
      +S0 = D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp)
      +st1 = X.X.st(R1, m, nx, fi, im, pg, lim, inp)
      +st2 = X.X.st(R2, m, nx, fi, im, pg, lim, inp)
      +eg8 = X.L.gs(R0, 8n, foc, X.L.lt(R0, 8n, hl0, {==}))
      +eg8b = X.L.go(R1, 10n, 8n, TG, foc, {==}, eg8)
      +er = X.L.gs(R1, 10n, TG, X.L.lt(R1, 10n, hl1, {==}))
      +ef1 = D.ev.fld(0n, Mc.M.g(Mc.R.c()), R1, m, nx, fi, im, pg, lim, inp, Nil{}, 0, foc, eg8, valid)
      +ef2 = D.ev.fld(0n, Mc.M.g(Mc.R.c()), R2, m, nx, fi, im, pg, lim, inp, Nil{}, 0, foc, eg8b, valid)
      +etg = D.ev.op(Wa.Wasm.Op.and{}, Mc.M.f(0n, Mc.M.g(Mc.R.c())), Mc.M.c(63), st1, f0, 63, ef1, {==})
      +etg2 = D.ev.op(Wa.Wasm.Op.and{}, Mc.M.f(0n, Mc.M.g(Mc.R.c())), Mc.M.c(63), st2, f0, 63, ef2, {==})
      +efl = D.ev.op(Wa.Wasm.Op.ne{}, Mc.M.and(Mc.M.f(0n, Mc.M.g(Mc.R.c())), Mc.M.c(256)), Mc.M.c(0), st2, Wa.Wasm.op(Wa.Wasm.Op.and{}, f0, 256), 0,
        D.ev.op(Wa.Wasm.Op.and{}, Mc.M.f(0n, Mc.M.g(Mc.R.c())), Mc.M.c(256), st2, f0, 256, ef2, {==}), {==})
      +addr = Wa.Wasm.op(Wa.Wasm.Op.add{}, 272, Wa.Wasm.op(Wa.Wasm.Op.and{}, f0, 63))
      +eadr = D.ev.op(Wa.Wasm.Op.add{}, Mc.M.c(272), Mc.M.tag(Mc.M.g(Mc.R.c())), st2, 272, Wa.Wasm.op(Wa.Wasm.Op.and{}, f0, 63), {==}, etg2)
      +vt = K.vt.of(m, im, fi, nx, f0, AN, etag, tb)
      +e4 = Cr.Cir.Cell.get(4n, Cr.Cir.Cells.get(m, addr))
      +ee4 = D.ev.fld(4n, Mc.M.add(Mc.M.c(272), Mc.M.tag(Mc.M.g(Mc.R.c()))), R2, m, nx, fi, im, pg, lim, inp, Nil{}, 0, addr, eadr, vt)
      +ene = D.ev.op(Wa.Wasm.Op.ne{}, Mc.M.entry(4n, Mc.M.g(Mc.R.c())), Mc.M.c(0), st2, e4, 0, ee4, {==})
      +flv = Wa.Wasm.op(Wa.Wasm.Op.ne{}, Wa.Wasm.op(Wa.Wasm.Op.and{}, f0, 256), 0)
      +nev = Wa.Wasm.op(Wa.Wasm.Op.ne{}, e4, 0)
      +ec2 = D.ev.op(Wa.Wasm.Op.or{}, Mc.M.flag(Mc.M.g(Mc.R.c()), Mc.F.value()), Mc.M.ne(Mc.M.entry(4n, Mc.M.g(Mc.R.c())), Mc.M.c(0)), st2, flv, nev, efl, ene)
      +z2 = K.z.of(m, im, fi, nx, f0, AN, etag, tb, hv, {==})
      +EA = Mc.M.ev.ann()
      +IF = {Cr.Cir.Stmt.if{K.B.cond2(), Mc.M.set(Mc.R.mode(), Mc.M.c(1)), K.B.else()} : Cr.Cir.Stmt}
      +nz2 = {(%Equal.sym(U32, TG, 2, etag) : {U32.is_zero(Wa.Wasm.op(Wa.Wasm.Op.eq{}, _, 2)) == False{} : Bool}; {==}) :
        {U32.is_zero(Wa.Wasm.op(Wa.Wasm.Op.eq{}, TG, 2)) == False{} : Bool}}
      +e_e2 = D.eq.if.t(f, Mc.M.eq(Mc.M.g(Mc.R.tag()), Mc.M.c(2)), EA, K.B.e3(), st2, Wa.Wasm.op(Wa.Wasm.Op.eq{}, TG, 2),
        D.ev.op(Wa.Wasm.Op.eq{}, Mc.M.g(Mc.R.tag()), Mc.M.c(2), st2, TG, 2, er, {==}), nz2)
      +e_e1 = D.eq.if.e(f, Mc.M.eq(Mc.M.g(Mc.R.tag()), Mc.M.c(1)), Mc.M.ev.ref(), K.B.e2(), st2, Wa.Wasm.op(Wa.Wasm.Op.eq{}, TG, 1),
        D.ev.op(Wa.Wasm.Op.eq{}, Mc.M.g(Mc.R.tag()), Mc.M.c(1), st2, TG, 1, er, {==}), K.tag.ne(f0, 2, 1, etag, {==}))
      +e_el = D.eq.if.e(f, Mc.M.eq(Mc.M.g(Mc.R.tag()), Mc.M.c(8)), Mc.M.ev.app(), K.B.e1(), st2, Wa.Wasm.op(Wa.Wasm.Op.eq{}, TG, 8),
        D.ev.op(Wa.Wasm.Op.eq{}, Mc.M.g(Mc.R.tag()), Mc.M.c(8), st2, TG, 8, er, {==}), K.tag.ne(f0, 2, 8, etag, {==}))
      +e_if = D.eq.if.e(f, K.B.cond2(), Mc.M.set(Mc.R.mode(), Mc.M.c(1)), K.B.else(), st2, Wa.Wasm.op(Wa.Wasm.Op.or{}, flv, nev), ec2, z2)
      +e_all = Equal.trans(Cr.Cir.Out, Cr.Cir.exec(f, IF, st2), Cr.Cir.exec(f, K.B.else(), st2), Cr.Cir.exec(f, EA, st2), e_if,
        Equal.trans(Cr.Cir.Out, Cr.Cir.exec(f, K.B.else(), st2), Cr.Cir.exec(f, K.B.e1(), st2), Cr.Cir.exec(f, EA, st2), e_el,
          Equal.trans(Cr.Cir.Out, Cr.Cir.exec(f, K.B.e1(), st2), Cr.Cir.exec(f, K.B.e2(), st2), Cr.Cir.exec(f, EA, st2), e_e1, e_e2)))
      +RHS = Cr.Cir.exec(f, Cr.Cir.Stmt.seq{EA, Cr.Cir.Stmt.nop{}}, st2)
      %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, D.B.body(), S0), Cr.Cir.exec(f, Mc.M.ev(), S0),
        D.eq.if.t(f, Mc.M.eq(Mc.M.g(Mc.R.mode()), Mc.M.c(0)), Mc.M.ev(), Mc.M.ret(), S0, 1, {==}, {==})) : {_ == RHS : Cr.Cir.Out}
      %D.rw.seq(f, Mc.M.set(Mc.R.c(), Mc.M.g(Mc.R.focus())), K.B.ev2(), S0, st1,
        D.eq.set(f, 8n, Mc.M.g(Mc.R.focus()), S0, foc, {==}, X.L.lt(R0, 8n, hl0, {==}))) : {_ == RHS : Cr.Cir.Out}
      %D.rw.seq(f, Mc.M.set(Mc.R.tag(), Mc.M.tag(Mc.M.g(Mc.R.c()))), K.B.ev3(), st1, st2,
        D.eq.set(f, 10n, Mc.M.tag(Mc.M.g(Mc.R.c())), st1, TG, etg, X.L.lt(R1, 10n, hl1, {==}))) : {_ == RHS : Cr.Cir.Out}
      seq.cong(f, IF, EA, Cr.Cir.Stmt.nop{}, st2, e_all)

# x of Ann x y stands
def ann.x(-ds: List<&2, Bk.Def>, -m: Cr.Cir.Cells, -im: U32, -fi: U32, -nx: U32, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>,
  -foc: U32, +x: Bk.Term, +y: Bk.Term, h: D.Is(ds, m, im, fi, nx, ks, img, foc, Bk.Term.Ann{x, y})) -> D.Is(ds, m, im, fi, nx, ks, img, D.Fd(2n, m, foc), x):
  match h:
    case Tuple{_, Tuple{Tuple{_, i}, _}}:
      i

# M.ev.ann's last statement: the focus is n; a step to the frames around x
def ann.fin(+f: Nat, +m2: Cr.Cir.Cells, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32,
  +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat,
  +fs: List<&2, D.AF>, +ps: List<&2, U32>, +x: Bk.Term, +y: Bk.Term, +zs: List<&2, D.Rt>,
  +et: {D.A.plugs(fs, Bk.Term.Ann{x, y}) == t : Bk.Term}, +afs: D.AFs.ok(ds, fs), +s2: Cr.Cir.State,
  q2: (st2 => D.Ex(Cr.Cir.Cells, m3 => D.Ex(U32, d => D.Ex(U32, pend2 => D.Ex(List<&2, U32>, ps2 => D.P2({st2 == Cr.Cir.State{List.set(&2, U32, List.set(&2, U32, X.X.set(X.X.set(X.X.set(D.RG(foc, 0, sp, pend, D.R59.list(rest)), 8n, foc), 10n, D.TgW(D.Fd(0n, m, foc))), 15n, D.Fd(2n, m, foc)), 5n, d), 3n, pend2), m3, nx, fi, im, pg, lim, inp, Nil{}, 0} : Cr.Cir.State}, D.P2({D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m3, fi) == D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m2, fi) : Nat}, D.P2(D.HSK(True{}, ds, ks, img, m3, nx, fi, im, [D.Rt{D.Fd(2n, m, foc), x}], Nil{}, fs, sp, pend2, ps2), D.Ex(List<&2, D.Rt>, zs2 => D.AccK(True{}, ds, ks, img, m3, nx, fi, im, [D.Rt{D.Fd(2n, m, foc), x}], Nil{}, sp, fs, ps2, zs2))))))))))(s2)) -> D.PostB(False{}, Cr.Cir.exec(f, X.sel.b(X.sel.b(X.sel.b(Mc.M.ev.ann()))), s2), s => K.MV.next(ds, ks, img, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), s => st3 => D.HR(ds, t, s, st3), D.Budget(ds, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp))):
  match q2:
    case Tuple{+m3, Tuple{+d, Tuple{+pend2, Tuple{+ps2, Tuple{es, Tuple{_, Tuple{Tuple{Tuple{isx3, _}, Tuple{_, Tuple{_, Tuple{frs3, Tuple{heap3, img3}}}}}, Tuple{+zs2, hac3}}}}}}}}:
      +n = D.Fd(2n, m, foc)
      +TG = D.TgW(D.Fd(0n, m, foc))
      +R0 = D.RG(foc, 0, sp, pend, D.R59.list(rest))
      +R1 = X.X.set(R0, 8n, foc)
      +R2 = X.X.set(R1, 10n, TG)
      +R3 = X.X.set(R2, 15n, n)
      +hl0 = rg.len(rest, foc, 0, sp, pend)
      +hl1 = X.L.len(R0, 8n, foc, 63n, hl0)
      +hl2 = X.L.len(R1, 10n, TG, 63n, hl1)
      +hl3 = X.L.len(R2, 15n, n, 63n, hl2)
      +eg8 = X.L.gs(R0, 8n, foc, X.L.lt(R0, 8n, hl0, {==}))
      +eg8b = X.L.go(R1, 10n, 8n, TG, foc, {==}, eg8)
      +R4 = List.set(&2, U32, List.set(&2, U32, R3, 5n, d), 3n, pend2)
      +hl4 = X.L.len(List.set(&2, U32, R3, 5n, d), 3n, pend2, 63n, X.L.len(R3, 5n, d, 63n, hl3))
      +st4 = X.X.st(R4, m3, nx, fi, im, pg, lim, inp)
      +st5 = X.X.st(X.X.set(R4, 0n, n), m3, nx, fi, im, pg, lim, inp)
      +S0 = D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp)
      +eg15 = X.L.go(List.set(&2, U32, R3, 5n, d), 3n, 15n, pend2, n, {==}, X.L.go(R3, 5n, 15n, d, n, {==}, X.L.gs(R2, 15n, n, X.L.lt(R2, 15n, hl2, {==}))))
      +e_s4 = D.eq.set(f, 0n, Mc.M.g(Mc.R.n()), st4, n, eg15, X.L.lt(R4, 0n, hl4, {==}))
      +u = D.A.plugs(fs, x)
      +w2 = D.A.w(False{}, x, fs)
      +estep = {(%et : {El.Eval.step(ds, _) == Some{u} : Maybe<Bk.Term>}; step.plugs(ds, fs, Bk.Term.Ann{x, y}, x, afs, {==})) :
        {El.Eval.step(ds, t) == Some{u} : Maybe<Bk.Term>}}
      +pk = le.max.l(D.Mem.cells(S0), D.Need(ds, S0, t))
      +inv5 = {(D.Wit{False{}, x, fs, n, sp, pend2, ps2, R59.ann(rest, foc, TG, n, d)},
        (({==}, ({==}, ({==}, (afs, (ann.regs(rest, foc, sp, pend, TG, n, d, pend2), (isx3, (frs3, (heap3, (img3, ({==}, {==})))))))))), (zs2, hac3))) :
        D.Inv(ds, ks, img, st5, u, w2)}
      %Equal.sym(Cr.Cir.State, s2, st4, es) : D.PostB(False{}, Cr.Cir.exec(f, X.sel.b(X.sel.b(X.sel.b(Mc.M.ev.ann()))), _), s => K.MV.next(ds, ks, img, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), s => st3 => D.HR(ds, t, s, st3), D.Budget(ds, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp)))
      %D.rw.seq(f, X.sel.a(X.sel.b(X.sel.b(X.sel.b(Mc.M.ev.ann())))), X.sel.b(X.sel.b(X.sel.b(X.sel.b(Mc.M.ev.ann())))), st4, st5, e_s4) : D.PostB(False{}, _, s => K.MV.next(ds, ks, img, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), s => st3 => D.HR(ds, t, s, st3), D.Budget(ds, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp)))
      %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, X.sel.b(X.sel.b(X.sel.b(X.sel.b(Mc.M.ev.ann())))), st5), Cr.Cir.Out.next{st5}, D.eq.nop(f, st5)) : D.PostB(False{}, _, s => K.MV.next(ds, ks, img, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), s => st3 => D.HR(ds, t, s, st3), D.Budget(ds, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp)))
      (Inr{(u, (estep, (w2, inv5)))}, pk)

# M.ev.ann's M.dec of the focus' cell, after its M.inc of n (the roots trade places)
def ann.dec(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32,
  +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat,
  +fs: List<&2, D.AF>, +ps: List<&2, U32>, +x: Bk.Term, +y: Bk.Term, +zs: List<&2, D.Rt>,
  +et: {D.A.plugs(fs, Bk.Term.Ann{x, y}) == t : Bk.Term}, +afs: D.AFs.ok(ds, fs), +s: Cr.Cir.State,
  q: (st2 => D.Ex(Cr.Cir.Cells, m2 => D.P2({st2 == Cr.Cir.State{X.X.set(X.X.set(X.X.set(D.RG(foc, 0, sp, pend, D.R59.list(rest)), 8n, foc), 10n, D.TgW(D.Fd(0n, m, foc))), 15n, D.Fd(2n, m, foc)), m2, nx, fi, im, pg, lim, inp, Nil{}, 0} : Cr.Cir.State}, D.P2({D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m2, fi) == D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi) : Nat}, D.P2(D.HSK(True{}, ds, ks, img, m2, nx, fi, im, Con{D.Rt{D.Fd(2n, m, foc), x}, Con{D.Rt{foc, Bk.Term.Ann{x, y}}, Nil{}}}, Con{D.Rt{D.Fd(2n, m, foc), x}, Nil{}}, fs, sp, pend, ps), D.AccK(True{}, ds, ks, img, m2, nx, fi, im, Con{D.Rt{D.Fd(2n, m, foc), x}, Con{D.Rt{foc, Bk.Term.Ann{x, y}}, Nil{}}}, Nil{}, sp, fs, ps, zs))))))(s)) -> D.PostB(False{}, Cr.Cir.exec(f, X.sel.b(X.sel.b(Mc.M.ev.ann())), s), s => K.MV.next(ds, ks, img, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), s => st3 => D.HR(ds, t, s, st3), D.Budget(ds, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp))):
  match q:
    case Tuple{+m2, Tuple{es, Tuple{_, Tuple{hs1, hac1}}}}:
      +n = D.Fd(2n, m, foc)
      +TG = D.TgW(D.Fd(0n, m, foc))
      +R0 = D.RG(foc, 0, sp, pend, D.R59.list(rest))
      +R1 = X.X.set(R0, 8n, foc)
      +R2 = X.X.set(R1, 10n, TG)
      +R3 = X.X.set(R2, 15n, n)
      +hl0 = rg.len(rest, foc, 0, sp, pend)
      +hl1 = X.L.len(R0, 8n, foc, 63n, hl0)
      +hl2 = X.L.len(R1, 10n, TG, 63n, hl1)
      +hl3 = X.L.len(R2, 15n, n, 63n, hl2)
      +eg8 = X.L.gs(R0, 8n, foc, X.L.lt(R0, 8n, hl0, {==}))
      +eg8b = X.L.go(R1, 10n, 8n, TG, foc, {==}, eg8)
      +AN = {Bk.Term.Ann{x, y} : Bk.Term}
      +stA = X.X.st(R3, m2, nx, fi, im, pg, lim, inp)
      +hc8 = X.L.go(R2, 15n, 8n, n, foc, {==}, eg8b)
      +hp3 = X.L.go(R2, 15n, 3n, n, pend, {==}, X.L.go(R1, 10n, 3n, TG, pend, {==}, X.L.go(R0, 8n, 3n, foc, pend, {==}, {==})))
      +hs2 = hsk.sw2(ds, ks, img, m2, nx, fi, im, n, x, foc, AN, Nil{}, [D.Rt{n, x}], fs, sp, pend, ps, hs1)
      +hac2 = acc.sw2(ds, ks, img, m2, nx, fi, im, n, x, foc, AN, Nil{}, sp, fs, ps, zs, hac1)
      hdec = D.dec.post(f, True{}, ds, ks, img, R3, m2, nx, fi, im, pg, lim, inp, 8n, [D.Rt{n, x}], Nil{}, fs, sp, pend, ps, foc, AN, Nil{}, zs,
        hs2, hac2, Unit{}, hl3, hc8, hp3, {==})
      +B = D.Budget(ds, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t)
      %Equal.sym(Cr.Cir.State, s, stA, es) : D.PostB(False{}, Cr.Cir.exec(f, X.sel.b(X.sel.b(Mc.M.ev.ann())), _), s => K.MV.next(ds, ks, img, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), s => st3 => D.HR(ds, t, s, st3), D.Budget(ds, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp)))
      D.postb.seq(f, False{}, X.sel.a(X.sel.b(X.sel.b(Mc.M.ev.ann()))), X.sel.b(X.sel.b(X.sel.b(Mc.M.ev.ann()))), stA, st2 => D.Ex(Cr.Cir.Cells, m3 => D.Ex(U32, d => D.Ex(U32, pend2 => D.Ex(List<&2, U32>, ps2 => D.P2({st2 == Cr.Cir.State{List.set(&2, U32, List.set(&2, U32, X.X.set(X.X.set(X.X.set(D.RG(foc, 0, sp, pend, D.R59.list(rest)), 8n, foc), 10n, D.TgW(D.Fd(0n, m, foc))), 15n, D.Fd(2n, m, foc)), 5n, d), 3n, pend2), m3, nx, fi, im, pg, lim, inp, Nil{}, 0} : Cr.Cir.State}, D.P2({D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m3, fi) == D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m2, fi) : Nat}, D.P2(D.HSK(True{}, ds, ks, img, m3, nx, fi, im, [D.Rt{D.Fd(2n, m, foc), x}], Nil{}, fs, sp, pend2, ps2), D.Ex(List<&2, D.Rt>, zs2 => D.AccK(True{}, ds, ks, img, m3, nx, fi, im, [D.Rt{D.Fd(2n, m, foc), x}], Nil{}, sp, fs, ps2, zs2))))))))), s => K.MV.next(ds, ks, img, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), s => st2 => Empty, s => st3 => D.HR(ds, t, s, st3), B, D.St.lim(D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp)),
        D.postb.wk(False{}, Cr.Cir.exec(f, X.sel.a(X.sel.b(X.sel.b(Mc.M.ev.ann()))), stA), st2 => D.Ex(Cr.Cir.Cells, m3 => D.Ex(U32, d => D.Ex(U32, pend2 => D.Ex(List<&2, U32>, ps2 => D.P2({st2 == Cr.Cir.State{List.set(&2, U32, List.set(&2, U32, X.X.set(X.X.set(X.X.set(D.RG(foc, 0, sp, pend, D.R59.list(rest)), 8n, foc), 10n, D.TgW(D.Fd(0n, m, foc))), 15n, D.Fd(2n, m, foc)), 5n, d), 3n, pend2), m3, nx, fi, im, pg, lim, inp, Nil{}, 0} : Cr.Cir.State}, D.P2({D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m3, fi) == D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m2, fi) : Nat}, D.P2(D.HSK(True{}, ds, ks, img, m3, nx, fi, im, [D.Rt{D.Fd(2n, m, foc), x}], Nil{}, fs, sp, pend2, ps2), D.Ex(List<&2, D.Rt>, zs2 => D.AccK(True{}, ds, ks, img, m3, nx, fi, im, [D.Rt{D.Fd(2n, m, foc), x}], Nil{}, sp, fs, ps2, zs2))))))))), s => st2 => Empty, 0n, B, D.St.lim(D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp)), hdec, N.le_zero(B)),
        s => st3 => e => Empty.absurd(D.HR(ds, t, s, st3), e), s2 => q2 => ann.fin(f, m2, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, x, y, zs, et, afs, s2, q2))

# the round of the Ann step, from the state after M.ev's tests
def ann.post(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32,
  +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat,
  +fs: List<&2, D.AF>, +ps: List<&2, U32>, +x: Bk.Term, +y: Bk.Term, +zs: List<&2, D.Rt>,
  +et: {D.A.plugs(fs, Bk.Term.Ann{x, y}) == t : Bk.Term}, +afs: D.AFs.ok(ds, fs), +isf: D.Is(ds, m, im, fi, nx, ks, img, foc, Bk.Term.Ann{x, y}),
  +frs: D.Frs(ds, m, im, fi, nx, ks, img, ps, sp, fs), +hp: D.Heap(m, nx, fi, im, [foc], pend, ps), +io: D.ImgOK(ds, ks, img, m, im, fi, nx),
  hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, [D.Rt{foc, Bk.Term.Ann{x, y}}], Nil{}, sp, fs, ps, zs)) ->
  D.PostB(False{}, Cr.Cir.exec(f, Cr.Cir.Stmt.seq{Mc.M.ev.ann(), Cr.Cir.Stmt.nop{}}, X.X.st(X.X.set(X.X.set(D.RG(foc, 0, sp, pend, D.R59.list(rest)), 8n, foc), 10n, D.TgW(D.Fd(0n, m, foc))), m, nx, fi, im, pg, lim, inp)), s => K.MV.next(ds, ks, img, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), s => st3 => D.HR(ds, t, s, st3), D.Budget(ds, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp))):
  +n = D.Fd(2n, m, foc)
  +TG = D.TgW(D.Fd(0n, m, foc))
  +R0 = D.RG(foc, 0, sp, pend, D.R59.list(rest))
  +R1 = X.X.set(R0, 8n, foc)
  +R2 = X.X.set(R1, 10n, TG)
  +R3 = X.X.set(R2, 15n, n)
  +hl0 = rg.len(rest, foc, 0, sp, pend)
  +hl1 = X.L.len(R0, 8n, foc, 63n, hl0)
  +hl2 = X.L.len(R1, 10n, TG, 63n, hl1)
  +hl3 = X.L.len(R2, 15n, n, 63n, hl2)
  +eg8 = X.L.gs(R0, 8n, foc, X.L.lt(R0, 8n, hl0, {==}))
  +eg8b = X.L.go(R1, 10n, 8n, TG, foc, {==}, eg8)
  +AN = {Bk.Term.Ann{x, y} : Bk.Term}
  +os0 = {Con{D.Rt{foc, Bk.Term.Ann{x, y}}, Nil{}} : List<&2, D.Rt>}
  +st2 = X.X.st(R2, m, nx, fi, im, pg, lim, inp)
  +st3 = X.X.st(R3, m, nx, fi, im, pg, lim, inp)
  +valid = nd.cell(True{}, ds, im, fi, nx, foc, Cr.Cir.Cells.get(m, foc), AN, 2, D.is.nd(ds, m, im, fi, nx, ks, img, foc, AN, isf))
  +e_s1 = D.eq.set(f, 15n, Mc.M.f(2n, Mc.M.g(Mc.R.c())), st2, n,
    D.ev.fld(2n, Mc.M.g(Mc.R.c()), R2, m, nx, fi, im, pg, lim, inp, Nil{}, 0, foc, eg8b, valid), X.L.lt(R2, 15n, hl2, {==}))
  +hheld = D.or.r(D.Fl(m, n, 1024), D.Nodes(os0, m, n), D.or.l(D.Node(AN, m, foc, n), False{},
    D.or.r(U32.is_eq(foc, n), Bool.or(D.Node(x, m, n, n), D.Node(y, m, D.Fd(3n, m, foc), n)),
      D.or.l(D.Node(x, m, n, n), D.Node(y, m, D.Fd(3n, m, foc), n), node.root(x, m, n)))))
  +hs0 = {((isf, Unit{}), ((ann.x(ds, m, im, fi, nx, ks, img, foc, x, y, isf), Unit{}), ((hheld, Unit{}), (frs, (hp, io))))) :
    D.HS(ds, ks, img, m, nx, fi, im, os0, [D.Rt{n, x}], fs, sp, pend, ps)}
  +hc15 = X.L.gs(R2, 15n, n, X.L.lt(R2, 15n, hl2, {==}))
  hinc = D.inc.post(f, True{}, ds, ks, img, R3, m, nx, fi, im, pg, lim, inp, 15n, os0, Nil{}, fs, sp, pend, ps, n, x, Nil{}, zs, hs0, hac, Unit{}, hc15)
  +B = D.Budget(ds, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t)
  hEA = {(%D.rw.seq(f, X.sel.a(Mc.M.ev.ann()), X.sel.b(Mc.M.ev.ann()), st2, st3, e_s1) : D.PostB(False{}, _, s => K.MV.next(ds, ks, img, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), s => st3 => D.HR(ds, t, s, st3), D.Budget(ds, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp)));
      D.postb.seq(f, False{}, X.sel.a(X.sel.b(Mc.M.ev.ann())), X.sel.b(X.sel.b(Mc.M.ev.ann())), st3, st2 => D.Ex(Cr.Cir.Cells, m2 => D.P2({st2 == Cr.Cir.State{X.X.set(X.X.set(X.X.set(D.RG(foc, 0, sp, pend, D.R59.list(rest)), 8n, foc), 10n, D.TgW(D.Fd(0n, m, foc))), 15n, D.Fd(2n, m, foc)), m2, nx, fi, im, pg, lim, inp, Nil{}, 0} : Cr.Cir.State}, D.P2({D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m2, fi) == D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi) : Nat}, D.P2(D.HSK(True{}, ds, ks, img, m2, nx, fi, im, Con{D.Rt{D.Fd(2n, m, foc), x}, Con{D.Rt{foc, Bk.Term.Ann{x, y}}, Nil{}}}, Con{D.Rt{D.Fd(2n, m, foc), x}, Nil{}}, fs, sp, pend, ps), D.AccK(True{}, ds, ks, img, m2, nx, fi, im, Con{D.Rt{D.Fd(2n, m, foc), x}, Con{D.Rt{foc, Bk.Term.Ann{x, y}}, Nil{}}}, Nil{}, sp, fs, ps, zs))))), s => K.MV.next(ds, ks, img, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), s => st2 => Empty, s => st3 => D.HR(ds, t, s, st3), B, D.St.lim(D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp)),
        D.postb.wk(False{}, Cr.Cir.exec(f, X.sel.a(X.sel.b(Mc.M.ev.ann())), st3), st2 => D.Ex(Cr.Cir.Cells, m2 => D.P2({st2 == Cr.Cir.State{X.X.set(X.X.set(X.X.set(D.RG(foc, 0, sp, pend, D.R59.list(rest)), 8n, foc), 10n, D.TgW(D.Fd(0n, m, foc))), 15n, D.Fd(2n, m, foc)), m2, nx, fi, im, pg, lim, inp, Nil{}, 0} : Cr.Cir.State}, D.P2({D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m2, fi) == D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi) : Nat}, D.P2(D.HSK(True{}, ds, ks, img, m2, nx, fi, im, Con{D.Rt{D.Fd(2n, m, foc), x}, Con{D.Rt{foc, Bk.Term.Ann{x, y}}, Nil{}}}, Con{D.Rt{D.Fd(2n, m, foc), x}, Nil{}}, fs, sp, pend, ps), D.AccK(True{}, ds, ks, img, m2, nx, fi, im, Con{D.Rt{D.Fd(2n, m, foc), x}, Con{D.Rt{foc, Bk.Term.Ann{x, y}}, Nil{}}}, Nil{}, sp, fs, ps, zs))))), s => st2 => Empty, 0n, B, D.St.lim(D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp)), hinc, N.le_zero(B)),
        s => st3 => e => Empty.absurd(D.HR(ds, t, s, st3), e), s => q => ann.dec(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, x, y, zs, et, afs, s, q))) :
    D.PostB(False{}, Cr.Cir.exec(f, Mc.M.ev.ann(), st2), s => K.MV.next(ds, ks, img, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), s => st3 => D.HR(ds, t, s, st3), D.Budget(ds, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp)))}
  D.postb.seq(f, False{}, Mc.M.ev.ann(), Cr.Cir.Stmt.nop{}, st2, s => K.MV.next(ds, ks, img, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), s => K.MV.next(ds, ks, img, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), s => st3 => D.HR(ds, t, s, st3), s => st3 => D.HR(ds, t, s, st3), B, D.St.lim(D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp)), hEA, s => st3 => h => h,
    s => q => (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, Cr.Cir.Stmt.nop{}, s), Cr.Cir.Out.next{s}, D.eq.nop(f, s)) : D.PostB(False{}, _, s => K.MV.next(ds, ks, img, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), s => st3 => D.HR(ds, t, s, st3), D.Budget(ds, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp))); q))

# the round, for any fuel
def ann.round(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32,
  +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat,
  +fs: List<&2, D.AF>, +ps: List<&2, U32>, +x: Bk.Term, +y: Bk.Term, +zs: List<&2, D.Rt>,
  +et: {D.A.plugs(fs, Bk.Term.Ann{x, y}) == t : Bk.Term}, +afs: D.AFs.ok(ds, fs), +isf: D.Is(ds, m, im, fi, nx, ks, img, foc, Bk.Term.Ann{x, y}),
  +frs: D.Frs(ds, m, im, fi, nx, ks, img, ps, sp, fs), +hp: D.Heap(m, nx, fi, im, [foc], pend, ps), +io: D.ImgOK(ds, ks, img, m, im, fi, nx),
  +hv: {D.Fl(m, foc, 256) == False{} : Bool},
  hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, [D.Rt{foc, Bk.Term.Ann{x, y}}], Nil{}, sp, fs, ps, zs)) ->
  D.PostB(False{}, Cr.Cir.exec(f, D.B.body(), D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp)), s => K.MV.next(ds, ks, img, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), s => st3 => D.HR(ds, t, s, st3), D.Budget(ds, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp))):
  +S0 = D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp)
  +st2 = X.X.st(X.X.set(X.X.set(D.RG(foc, 0, sp, pend, D.R59.list(rest)), 8n, foc), 10n, D.TgW(D.Fd(0n, m, foc))), m, nx, fi, im, pg, lim, inp)
  +nd = D.is.nd(ds, m, im, fi, nx, ks, img, foc, Bk.Term.Ann{x, y}, isf)
  +tb = D.img.tbl(True{}, ds, ks, img, m, im, fi, nx, io)
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, D.B.body(), S0), Cr.Cir.exec(f, Cr.Cir.Stmt.seq{Mc.M.ev.ann(), Cr.Cir.Stmt.nop{}}, st2),
    ann.E(f, ds, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, x, y, nd, tb, hv)) : D.PostB(False{}, _, s => K.MV.next(ds, ks, img, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), s => st3 => D.HR(ds, t, s, st3), D.Budget(ds, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp)))
  ann.post(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, x, y, zs, et, afs, isf, frs, hp, io, hac)

# mode 0, Ann x y: x, a step
def ann.go(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32,
  +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat,
  +fs: List<&2, D.AF>, +ps: List<&2, U32>, +x: Bk.Term, +y: Bk.Term, +zs: List<&2, D.Rt>,
  +iv: D.InvOf(ds, ks, img, D.RG(foc, 0, sp, pend, D.R59.list(rest)), m, nx, fi, im, Nil{}, 0, t, w, False{}, Bk.Term.Ann{x, y}, fs, foc, sp, pend, ps, rest),
  +hv: {D.Fl(m, foc, 256) == False{} : Bool},
  +hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, [D.Rt{foc, Bk.Term.Ann{x, y}}], Nil{}, sp, fs, ps, zs)) ->
  K.MV(ds, ks, img, D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  match iv:
    case Tuple{+et, Tuple{_, Tuple{_, Tuple{+afs, Tuple{_, Tuple{+isf, Tuple{+frs, Tuple{+hp, Tuple{+io, _}}}}}}}}}:
      +S0 = D.S(foc, 0, sp, pend, rest, m, nx, fi, im, pg, lim, inp)
      +st2 = X.X.st(X.X.set(X.X.set(D.RG(foc, 0, sp, pend, D.R59.list(rest)), 8n, foc), 10n, D.TgW(D.Fd(0n, m, foc))), m, nx, fi, im, pg, lim, inp)
      +nd = D.is.nd(ds, m, im, fi, nx, ks, img, foc, Bk.Term.Ann{x, y}, isf)
      +tb = D.img.tbl(True{}, ds, ks, img, m, im, fi, nx, io)
      (f => ann.round(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, x, y, zs, et, afs, isf, frs, hp, io, hv, hac),
        (0n, (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec(0n, D.B.body(), S0), Cr.Cir.exec(0n, Cr.Cir.Stmt.seq{Mc.M.ev.ann(), Cr.Cir.Stmt.nop{}}, st2),
            ann.E(0n, ds, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, x, y, nd, tb, hv)) : D.Ends(_);
          ends.plain(Cr.Cir.Stmt.seq{Mc.M.ev.ann(), Cr.Cir.Stmt.nop{}}, st2, plain.ann()))))

# The pop of a frame
# ------------------
#
# M.pop moves the top frame sp to the pend list: register sp gets its next
# frame, its field 1 the old pend, and pend gets sp (pop.eq). A frame in the
# pend list holds no pointer, so the pointers of sp (its field 2, and 3 for
# Rwt) become owned roots: every count Ptr stays (ptr.pop), and the heap
# holds with those roots (heap.pop). The store to field 1 changes nothing
# that HS or Acc read but the chains (Put1), and sp leaves the frames for
# the pend list in Cov's cells (acc.pop).

# a cell z of no term kind, in the pend list, holds no pointer
def fs.inpend(+m: Cr.Cir.Cells, +ps: List<&2, U32>, +z: U32, hnt: {U32.is_lt(D.Tg(m, z), 19) == False{} : Bool}) ->
  {D.Fs(m, Con{z, ps}, z) == Nil{} : List<&2, U32>}:
  +T = D.TgW(D.Fd(0n, m, z))
  %Equal.sym(Bool, U32.is_lt(D.Tg(m, z), 19), False{}, hnt) : {A.FsM(_, D.Mem(Con{z, ps}, z), m, z, T) == Nil{} : List<&2, U32>}
  %Equal.sym(Bool, U32.is_eq(z, z), True{}, D.u32.refl(z)) : {A.FsM(False{}, Bool.or(_, D.Mem(ps, z)), m, z, T) == Nil{} : List<&2, U32>}
  %Equal.sym(Bool, Bool.and(Bool.and(U32.is_le(32, T), U32.is_le(T, 40)), False{}), False{}, A.and.false(Bool.and(U32.is_le(32, T), U32.is_le(T, 40)))) :
    {Bool.pick(List<&2, U32>, _, Con{D.Fd(2n, m, z), D.Fs.opt(U32.is_eq(T, 38), D.Fd(3n, m, z), Nil{})},
      Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_eq(T, 41), D.FlW(D.Fd(0n, m, z), 4096)), False{}), [D.Fd(2n, m, z)], Nil{})) == Nil{} : List<&2, U32>}
  %Equal.sym(Bool, Bool.and(Bool.and(U32.is_eq(T, 41), D.FlW(D.Fd(0n, m, z), 4096)), False{}), False{}, A.and.false(Bool.and(U32.is_eq(T, 41), D.FlW(D.Fd(0n, m, z), 4096)))) :
    {Bool.pick(List<&2, U32>, _, [D.Fd(2n, m, z)], Nil{}) == Nil{} : List<&2, U32>}
  {==}

# and the other cells' pointers stay
def fs.pend.ne(+m: Cr.Cir.Cells, +ps: List<&2, U32>, +z: U32, +o: U32, eb: {U32.is_eq(z, o) == False{} : Bool}) ->
  {D.Fs(m, Con{z, ps}, o) == D.Fs(m, ps, o) : List<&2, U32>}:
  %Equal.sym(Bool, U32.is_eq(z, o), False{}, eb) :
    {A.FsM(U32.is_lt(D.TgW(D.Fd(0n, m, o)), 19), Bool.or(_, D.Mem(ps, o)), m, o, D.TgW(D.Fd(0n, m, o))) == D.Fs(m, ps, o) : List<&2, U32>}
  {==}

# z joins the pend list: the pointers of the k cells from o, all past z
def Pc.out.p(k: Nat, +m: Cr.Cir.Cells, +z: U32, +ps: List<&2, U32>, +o: U32, +c: U32, +nx: U32,
  hz: N.Le(1n+U32.to_nat(z), U32.to_nat(o)), hb: N.Le(Nat.add(U32.to_nat(o), k), U32.to_nat(nx))) ->
  {D.Pc(k, m, Con{z, ps}, o, c) == D.Pc(k, m, ps, o, c) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+(+j):
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
      +e1 = fs.pend.ne(m, ps, z, o, D.ne.sym(o, z, ne.lt(o, z, hz2)))
      +e2 = Pc.out.p(j, m, z, ps, U32.inc(o), c, nx, hzi, hbi)
      %Equal.sym(List<&2, U32>, D.Fs(m, Con{z, ps}, o), D.Fs(m, ps, o), e1) :
        {Nat.add(D.RcL(_, c), D.Pc(j, m, Con{z, ps}, U32.inc(o), c)) == Nat.add(D.RcL(D.Fs(m, ps, o), c), D.Pc(j, m, ps, U32.inc(o), c)) : Nat}
      %Equal.sym(Nat, D.Pc(j, m, Con{z, ps}, U32.inc(o), c), D.Pc(j, m, ps, U32.inc(o), c), e2) :
        {Nat.add(D.RcL(D.Fs(m, ps, o), c), _) == Nat.add(D.RcL(D.Fs(m, ps, o), c), D.Pc(j, m, ps, U32.inc(o), c)) : Nat}
      {==}

# the step of Pc.pop: o is z, or z is past o
def Pc.pop.b(bb: Bool, +j: Nat, +m: Cr.Cir.Cells, +z: U32, +ps: List<&2, U32>, +o: U32, +c: U32, +nx: U32,
  +eb: {U32.is_eq(o, z) == bb : Bool}, +h1: N.Le(U32.to_nat(o), U32.to_nat(z)),
  +h2: N.Le(1n+U32.to_nat(z), Nat.add(U32.to_nat(o), 1n+j)), +hb: N.Le(Nat.add(U32.to_nat(o), 1n+j), U32.to_nat(nx)),
  +hnt: {U32.is_lt(D.Tg(m, z), 19) == False{} : Bool},
  ih: N.Le(U32.to_nat(U32.inc(o)), U32.to_nat(z)) -> N.Le(1n+U32.to_nat(z), Nat.add(U32.to_nat(U32.inc(o)), j)) ->
    N.Le(Nat.add(U32.to_nat(U32.inc(o)), j), U32.to_nat(nx)) ->
    {Nat.add(D.Pc(j, m, Con{z, ps}, U32.inc(o), c), D.RcL(D.Fs(m, ps, z), c)) == D.Pc(j, m, ps, U32.inc(o), c) : Nat}) ->
  {Nat.add(D.Pc(1n+j, m, Con{z, ps}, o, c), D.RcL(D.Fs(m, ps, z), c)) == D.Pc(1n+j, m, ps, o, c) : Nat}:
  match bb:
    case True{}:
      +R0 = D.RcL(D.Fs(m, ps, z), c)
      +eo = D.u32.eq(o, z, eb)
      +lt1 = N.le_trans(1n+U32.to_nat(o), Nat.add(U32.to_nat(o), 1n+j), U32.to_nat(nx), N.lt_add(U32.to_nat(o), j), hb)
      +ei = D.u.inc(o, nx, lt1)
      +hzo = {(%eo : N.Le(1n+U32.to_nat(_), U32.to_nat(U32.inc(o)));
        N.le_rw_r(1n+U32.to_nat(o), 1n+U32.to_nat(o), U32.to_nat(U32.inc(o)), Equal.sym(Nat, U32.to_nat(U32.inc(o)), 1n+U32.to_nat(o), ei),
          N.le_refl(1n+U32.to_nat(o)))) : N.Le(1n+U32.to_nat(z), U32.to_nat(U32.inc(o)))}
      +hbi = N.le_rw_l(Nat.add(U32.to_nat(o), 1n+j), Nat.add(U32.to_nat(U32.inc(o)), j), U32.to_nat(nx),
        Equal.trans(Nat, Nat.add(U32.to_nat(o), 1n+j), 1n+Nat.add(U32.to_nat(o), j), Nat.add(U32.to_nat(U32.inc(o)), j),
          N.add_succ_r(U32.to_nat(o), j),
          Equal.sym(Nat, Nat.add(U32.to_nat(U32.inc(o)), j), 1n+Nat.add(U32.to_nat(o), j),
            Equal.cong(Nat, Nat, y => Nat.add(y, j), U32.to_nat(U32.inc(o)), 1n+U32.to_nat(o), ei))), hb)
      +e2 = Pc.out.p(j, m, z, ps, U32.inc(o), c, nx, hzo, hbi)
      +P0 = D.Pc(j, m, ps, U32.inc(o), c)
      %Equal.sym(U32, o, z, eo) :
        {Nat.add(Nat.add(D.RcL(D.Fs(m, Con{z, ps}, _), c), D.Pc(j, m, Con{z, ps}, U32.inc(o), c)), R0) ==
          Nat.add(D.RcL(D.Fs(m, ps, _), c), P0) : Nat}
      %Equal.sym(List<&2, U32>, D.Fs(m, Con{z, ps}, z), Nil{}, fs.inpend(m, ps, z, hnt)) :
        {Nat.add(Nat.add(D.RcL(_, c), D.Pc(j, m, Con{z, ps}, U32.inc(o), c)), R0) == Nat.add(R0, P0) : Nat}
      %Equal.sym(Nat, D.Pc(j, m, Con{z, ps}, U32.inc(o), c), P0, e2) : {Nat.add(_, R0) == Nat.add(R0, P0) : Nat}
      add.comm(P0, R0)
    case False{}:
      +R0 = D.RcL(D.Fs(m, ps, z), c)
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
      +e1 = fs.pend.ne(m, ps, z, o, D.ne.sym(o, z, eb))
      +e2 = ih(h1b, h2b, hbb)
      +A0 = D.RcL(D.Fs(m, ps, o), c)
      +P1 = D.Pc(j, m, Con{z, ps}, U32.inc(o), c)
      +P0 = D.Pc(j, m, ps, U32.inc(o), c)
      %Equal.sym(List<&2, U32>, D.Fs(m, Con{z, ps}, o), D.Fs(m, ps, o), e1) :
        {Nat.add(Nat.add(D.RcL(_, c), P1), R0) == Nat.add(A0, P0) : Nat}
      Equal.trans(Nat, Nat.add(Nat.add(A0, P1), R0), Nat.add(A0, Nat.add(P1, R0)), Nat.add(A0, P0), add.assoc(A0, P1, R0),
        Equal.cong(Nat, Nat, y => Nat.add(A0, y), Nat.add(P1, R0), P0, e2))

# z, one of the k cells from o (below nx), joins the pend list: its pointers leave Pc
def Pc.pop(k: Nat, +m: Cr.Cir.Cells, +z: U32, +ps: List<&2, U32>, +o: U32, +c: U32, +nx: U32,
  h1: N.Le(U32.to_nat(o), U32.to_nat(z)), h2: N.Le(1n+U32.to_nat(z), Nat.add(U32.to_nat(o), k)),
  hb: N.Le(Nat.add(U32.to_nat(o), k), U32.to_nat(nx)), +hnt: {U32.is_lt(D.Tg(m, z), 19) == False{} : Bool}) ->
  {Nat.add(D.Pc(k, m, Con{z, ps}, o, c), D.RcL(D.Fs(m, ps, z), c)) == D.Pc(k, m, ps, o, c) : Nat}:
  match k:
    case 0n:
      Empty.absurd({Nat.add(0n, D.RcL(D.Fs(m, ps, z), c)) == 0n : Nat},
        N.not_succ_le(U32.to_nat(z), N.le_trans(1n+U32.to_nat(z), U32.to_nat(o), U32.to_nat(z),
          N.le_rw_r(1n+U32.to_nat(z), Nat.add(U32.to_nat(o), 0n), U32.to_nat(o), N.add_zero(U32.to_nat(o)), h2), h1)))
    case 1n+(+j):
      Pc.pop.b(U32.is_eq(o, z), j, m, z, ps, o, c, nx, {==}, h1, h2, hb, hnt,
        a => b => d => Pc.pop(j, m, z, ps, U32.inc(o), c, nx, a, b, d, hnt))

# p + (a + r) = (p + r) + (a + 0)
def ar1(+p: Nat, +a: Nat, +r: Nat) -> {Nat.add(p, Nat.add(a, r)) == Nat.add(Nat.add(p, r), Nat.add(a, 0n)) : Nat}:
  Equal.trans(Nat, Nat.add(p, Nat.add(a, r)), Nat.add(p, Nat.add(r, a)), Nat.add(Nat.add(p, r), Nat.add(a, 0n)),
    Equal.cong(Nat, Nat, y => Nat.add(p, y), Nat.add(a, r), Nat.add(r, a), add.comm(a, r)),
    Equal.trans(Nat, Nat.add(p, Nat.add(r, a)), Nat.add(Nat.add(p, r), a), Nat.add(Nat.add(p, r), Nat.add(a, 0n)),
      Equal.sym(Nat, Nat.add(Nat.add(p, r), a), Nat.add(p, Nat.add(r, a)), add.assoc(p, r, a)),
      Equal.cong(Nat, Nat, y => Nat.add(Nat.add(p, r), y), a, Nat.add(a, 0n), Equal.sym(Nat, Nat.add(a, 0n), a, N.add_zero(a)))))

# the counts, after z (no term kind, of the machine's own) joins the pend list
# and its pointers join the roots
def ptr.pop(+m: Cr.Cir.Cells, +nx: U32, +fi: U32, +ps: List<&2, U32>, +z: U32, +r0: U32, +c: U32,
  hzo: {D.Own(fi, nx, z) == True{} : Bool}, +hnt: {U32.is_lt(D.Tg(m, z), 19) == False{} : Bool}) ->
  {D.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, Con{z, ps}, Con{r0, D.Fs(m, ps, z)}, c) ==
    D.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, [r0], c) : Nat}:
  +o2 = hzo
  +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
  +h1 = D.u.le(fi, z, D.and.l(U32.is_le(fi, z), U32.is_lt(z, nx), o2))
  +hl = D.u.lt(z, nx, D.and.r(U32.is_le(fi, z), U32.is_lt(z, nx), o2))
  +es = D.add.sub(U32.to_nat(fi), U32.to_nat(nx), N.le_trans(U32.to_nat(fi), U32.to_nat(z), U32.to_nat(nx), h1, N.weaken(U32.to_nat(z), U32.to_nat(nx), hl)))
  +es2 = Equal.sym(Nat, Nat.add(U32.to_nat(fi), n), U32.to_nat(nx), es)
  +h2 = N.le_rw_r(1n+U32.to_nat(z), U32.to_nat(nx), Nat.add(U32.to_nat(fi), n), es2, hl)
  +hb = N.le_rw_l(U32.to_nat(nx), Nat.add(U32.to_nat(fi), n), U32.to_nat(nx), es2, N.le_refl(U32.to_nat(nx)))
  +P1 = D.Pc(n, m, Con{z, ps}, fi, c)
  +R = D.RcL(D.Fs(m, ps, z), c)
  +A0 = D.Nat.of(U32.is_eq(r0, c))
  %Pc.pop(n, m, z, ps, fi, c, nx, h1, h2, hb, hnt) :
    {Nat.add(P1, Nat.add(A0, R)) == Nat.add(_, Nat.add(A0, 0n)) : Nat}
  ar1(P1, A0, R)

# the counts after the pop: z in the pend list, with the store to its field 1
def ptr.pop1(+m: Cr.Cir.Cells, +nx: U32, +fi: U32, +ps: List<&2, U32>, +z: U32, +pv: U32, +r0: U32, +c: U32,
  +hzo: {D.Own(fi, nx, z) == True{} : Bool}, +hnt: {U32.is_lt(D.Tg(m, z), 19) == False{} : Bool}) ->
  {D.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), D.Put1([D.W1{z, pv}], m), fi, Con{z, ps}, Con{r0, D.Fs(D.Put1([D.W1{z, pv}], m), ps, z)}, c) ==
    D.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, [r0], c) : Nat}:
  +ws = {[D.W1{z, pv}] : List<&2, D.W1>}
  +M1 = D.Put1(ws, m)
  +N = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
  +hnt1 = {(%Equal.sym(U32, D.Fd(0n, M1, z), D.Fd(0n, m, z), D.put1.f0(ws, m, z)) : {U32.is_lt(U32.and(_, 63), 19) == False{} : Bool}; hnt) :
    {U32.is_lt(D.Tg(M1, z), 19) == False{} : Bool}}
  Equal.trans(Nat, D.Ptr(N, M1, fi, Con{z, ps}, Con{r0, D.Fs(M1, ps, z)}, c), D.Ptr(N, M1, fi, ps, [r0], c), D.Ptr(N, m, fi, ps, [r0], c),
    ptr.pop(M1, nx, fi, ps, z, r0, c, hzo, hnt1), D.ptr.put1(N, ws, m, fi, ps, [r0], c))

def pendok.pop(qs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +ps: List<&2, U32>, +z: U32, +pv: U32, +r0: U32,
  +hzo: {D.Own(fi, nx, z) == True{} : Bool}, +hnt: {U32.is_lt(D.Tg(m, z), 19) == False{} : Bool},
  h: D.PendOK(qs, ps, m, fi, nx, [r0])) ->
  D.PendOK(qs, Con{z, ps}, D.Put1([D.W1{z, pv}], m), fi, nx, Con{r0, D.Fs(D.Put1([D.W1{z, pv}], m), ps, z)}):
  match qs:
    case Nil{}:
      Unit{}
    case Con{+p, +rest}:
      (ho, r1) = h
      (hs, r2) = r1
      (ht, r3) = r2
      (h0, hr) = r3
      +ws = {[D.W1{z, pv}] : List<&2, D.W1>}
      +M1 = D.Put1(ws, m)
      +N = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
      +e0 = D.put1.f0(ws, m, p)
      (ho, ((%Equal.sym(U32, D.Fd(0n, M1, p), D.Fd(0n, m, p), e0) : {U32.is_ne(U32.and(_, 1024), 0) == False{} : Bool}; hs),
        ((%Equal.sym(U32, D.Fd(0n, M1, p), D.Fd(0n, m, p), e0) :
            {Bool.or(U32.is_lt(U32.and(_, 63), 19), U32.is_le(32, U32.and(_, 63))) == True{} : Bool}; ht),
        (Equal.trans(Nat, D.Ptr(N, M1, fi, Con{z, ps}, Con{r0, D.Fs(M1, ps, z)}, p), D.Ptr(N, m, fi, ps, [r0], p), 0n,
            ptr.pop1(m, nx, fi, ps, z, pv, r0, p, hzo, hnt), h0),
          pendok.pop(rest, m, nx, fi, ps, z, pv, r0, hzo, hnt, hr)))))

def cnt.pop.at(bb: Bool, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +ps: List<&2, U32>, +z: U32, +pv: U32, +r0: U32, +o: U32,
  +eb: {U32.is_eq(o, z) == bb : Bool}, +hzo: {D.Own(fi, nx, z) == True{} : Bool}, +hnt: {U32.is_lt(D.Tg(m, z), 19) == False{} : Bool},
  h: {D.CntC(Cr.Cir.Cells.get(m, o), D.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, [r0], o), ps, o) == True{} : Bool}) ->
  {D.CntC(Cr.Cir.Cells.get(D.Put1([D.W1{z, pv}], m), o),
    D.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), D.Put1([D.W1{z, pv}], m), fi, Con{z, ps}, Con{r0, D.Fs(D.Put1([D.W1{z, pv}], m), ps, z)}, o),
    Con{z, ps}, o) == True{} : Bool}:
  match bb:
    case True{}:
      +ws = {[D.W1{z, pv}] : List<&2, D.W1>}
      +M1 = D.Put1(ws, m)
      +N = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
      +P1 = D.Ptr(N, M1, fi, Con{z, ps}, Con{r0, D.Fs(M1, ps, z)}, o)
      +X1 = Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, z), pv)
      %Equal.sym(U32, o, z, D.u32.eq(o, z, eb)) :
        {D.CntC(Cr.Cir.Cells.get(M1, _), D.Ptr(N, M1, fi, Con{z, ps}, Con{r0, D.Fs(M1, ps, z)}, _), Con{z, ps}, _) == True{} : Bool}
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M1, z), X1, D.cl.gs(m, z, X1)) :
        {D.CntC(_, D.Ptr(N, M1, fi, Con{z, ps}, Con{r0, D.Fs(M1, ps, z)}, z), Con{z, ps}, z) == True{} : Bool}
      +PZ = D.Ptr(N, M1, fi, Con{z, ps}, Con{r0, D.Fs(M1, ps, z)}, z)
      D.or.l(Bool.not(U32.is_lt(D.TgW(Cr.Cir.Cell.get(0n, X1)), 19)), Bool.or(D.FlW(Cr.Cir.Cell.get(0n, X1), 1024), Bool.or(D.Mem(Con{z, ps}, z),
        Nat.is_eq(U32.to_nat(Cr.Cir.Cell.get(1n, X1)), PZ))),
        (%Equal.sym(U32, Cr.Cir.Cell.get(0n, X1), D.Fd(0n, m, z), D.cg0(Cr.Cir.Cells.get(m, z), pv)) : {Bool.not(U32.is_lt(D.TgW(_), 19)) == True{} : Bool};
          %Equal.sym(Bool, U32.is_lt(D.Tg(m, z), 19), False{}, hnt) : {Bool.not(_) == True{} : Bool};
          {==}))
    case False{}:
      +ws = {[D.W1{z, pv}] : List<&2, D.W1>}
      +M1 = D.Put1(ws, m)
      +N = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
      +P1 = D.Ptr(N, M1, fi, Con{z, ps}, Con{r0, D.Fs(M1, ps, z)}, o)
      +X1 = Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, z), pv)
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(M1, o), Cr.Cir.Cells.get(m, o), D.cl.go(m, o, z, X1, eb)) :
        {D.CntC(_, P1, Con{z, ps}, o) == True{} : Bool}
      %Equal.sym(Nat, P1, D.Ptr(N, m, fi, ps, [r0], o), ptr.pop1(m, nx, fi, ps, z, pv, r0, o, hzo, hnt)) :
        {D.CntC(Cr.Cir.Cells.get(m, o), _, Con{z, ps}, o) == True{} : Bool}
      %Equal.sym(Bool, U32.is_eq(z, o), False{}, D.ne.sym(o, z, eb)) :
        {Bool.or(Bool.not(U32.is_lt(D.TgW(Cr.Cir.Cell.get(0n, Cr.Cir.Cells.get(m, o))), 19)), Bool.or(D.FlW(Cr.Cir.Cell.get(0n, Cr.Cir.Cells.get(m, o)), 1024),
          Bool.or(Bool.or(_, D.Mem(ps, o)), Nat.is_eq(U32.to_nat(Cr.Cir.Cell.get(1n, Cr.Cir.Cells.get(m, o))), D.Ptr(N, m, fi, ps, [r0], o))))) == True{} : Bool}
      h

def cnt.pop(k: Nat, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +ps: List<&2, U32>, +z: U32, +pv: U32, +r0: U32, +o: U32,
  +hzo: {D.Own(fi, nx, z) == True{} : Bool}, +hnt: {U32.is_lt(D.Tg(m, z), 19) == False{} : Bool},
  h: {D.Cnt(k, m, o, Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), fi, ps, [r0]) == True{} : Bool}) ->
  {D.Cnt(k, D.Put1([D.W1{z, pv}], m), o, Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), fi, Con{z, ps}, Con{r0, D.Fs(D.Put1([D.W1{z, pv}], m), ps, z)}) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+(+j):
      +M1 = D.Put1([D.W1{z, pv}], m)
      +N = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
      +RS = {Con{r0, D.Fs(M1, ps, z)} : List<&2, U32>}
      +h2 = h
      D.and.i(D.CntC(Cr.Cir.Cells.get(M1, o), D.Ptr(N, M1, fi, Con{z, ps}, RS, o), Con{z, ps}, o), D.Cnt(j, M1, U32.inc(o), N, fi, Con{z, ps}, RS),
        cnt.pop.at(U32.is_eq(o, z), m, nx, fi, ps, z, pv, r0, o, {==}, hzo, hnt,
          D.and.l(D.CntC(Cr.Cir.Cells.get(m, o), D.Ptr(N, m, fi, ps, [r0], o), ps, o), D.Cnt(j, m, U32.inc(o), N, fi, ps, [r0]), h2)),
        cnt.pop(j, m, nx, fi, ps, z, pv, r0, U32.inc(o), hzo, hnt,
          D.and.r(D.CntC(Cr.Cir.Cells.get(m, o), D.Ptr(N, m, fi, ps, [r0], o), ps, o), D.Cnt(j, m, U32.inc(o), N, fi, ps, [r0]), h2)))

def pts.pop.at(bb: Bool, +m: Cr.Cir.Cells, +ps: List<&2, U32>, +z: U32, +pv: U32, +o: U32, +im: U32, +fi: U32, +nx: U32,
  +eb: {U32.is_eq(o, z) == bb : Bool}, +hnt: {U32.is_lt(D.Tg(m, z), 19) == False{} : Bool},
  h: {D.Lt.all(D.Fs(m, ps, o), m, im, fi, nx) == True{} : Bool}) ->
  {D.Lt.all(D.Fs(D.Put1([D.W1{z, pv}], m), Con{z, ps}, o), D.Put1([D.W1{z, pv}], m), im, fi, nx) == True{} : Bool}:
  match bb:
    case True{}:
      +ws = {[D.W1{z, pv}] : List<&2, D.W1>}
      +M1 = D.Put1(ws, m)
      +hnt1 = {(%Equal.sym(U32, D.Fd(0n, M1, z), D.Fd(0n, m, z), D.put1.f0(ws, m, z)) : {U32.is_lt(U32.and(_, 63), 19) == False{} : Bool}; hnt) :
        {U32.is_lt(D.Tg(M1, z), 19) == False{} : Bool}}
      %Equal.sym(U32, o, z, D.u32.eq(o, z, eb)) : {D.Lt.all(D.Fs(M1, Con{z, ps}, _), M1, im, fi, nx) == True{} : Bool}
      %Equal.sym(List<&2, U32>, D.Fs(M1, Con{z, ps}, z), Nil{}, fs.inpend(M1, ps, z, hnt1)) : {D.Lt.all(_, M1, im, fi, nx) == True{} : Bool}
      {==}
    case False{}:
      +ws = {[D.W1{z, pv}] : List<&2, D.W1>}
      +M1 = D.Put1(ws, m)
      %Equal.sym(List<&2, U32>, D.Fs(M1, Con{z, ps}, o), D.Fs(M1, ps, o), fs.pend.ne(M1, ps, z, o, D.ne.sym(o, z, eb))) :
        {D.Lt.all(_, M1, im, fi, nx) == True{} : Bool}
      %Equal.sym(List<&2, U32>, D.Fs(M1, ps, o), D.Fs(m, ps, o), D.fs.put1(ws, m, ps, o)) : {D.Lt.all(_, M1, im, fi, nx) == True{} : Bool}
      %Equal.sym(Bool, D.Lt.all(D.Fs(m, ps, o), M1, im, fi, nx), D.Lt.all(D.Fs(m, ps, o), m, im, fi, nx), D.lt.put1(D.Fs(m, ps, o), ws, m, im, fi, nx)) :
        {_ == True{} : Bool}
      h

def pts.pop(k: Nat, +m: Cr.Cir.Cells, +ps: List<&2, U32>, +z: U32, +pv: U32, +o: U32, +im: U32, +fi: U32, +nx: U32,
  +hnt: {U32.is_lt(D.Tg(m, z), 19) == False{} : Bool}, h: {D.Pts(k, m, ps, o, im, fi, nx) == True{} : Bool}) ->
  {D.Pts(k, D.Put1([D.W1{z, pv}], m), Con{z, ps}, o, im, fi, nx) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+(+j):
      +M1 = D.Put1([D.W1{z, pv}], m)
      +h2 = h
      D.and.i(D.Lt.all(D.Fs(M1, Con{z, ps}, o), M1, im, fi, nx), D.Pts(j, M1, Con{z, ps}, U32.inc(o), im, fi, nx),
        pts.pop.at(U32.is_eq(o, z), m, ps, z, pv, o, im, fi, nx, {==}, hnt,
          D.and.l(D.Lt.all(D.Fs(m, ps, o), m, im, fi, nx), D.Pts(j, m, ps, U32.inc(o), im, fi, nx), h2)),
        pts.pop(j, m, ps, z, pv, U32.inc(o), im, fi, nx, hnt,
          D.and.r(D.Lt.all(D.Fs(m, ps, o), m, im, fi, nx), D.Pts(j, m, ps, U32.inc(o), im, fi, nx), h2)))

# the heap after the pop of the frame z: z heads the pend list, its pointers are roots
def heap.pop(+m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +r0: U32, +pend: U32, +ps: List<&2, U32>, +z: U32,
  +hzo: {D.Own(fi, nx, z) == True{} : Bool}, +hnt: {U32.is_lt(D.Tg(m, z), 19) == False{} : Bool},
  +hge: {U32.is_le(32, D.Tg(m, z)) == True{} : Bool}, +hst: {D.Fl(m, z, 1024) == False{} : Bool}, +hm: {D.Mem(ps, z) == False{} : Bool},
  +hnz: {U32.is_eq(z, 0) == False{} : Bool},
  +hz0: {D.Ptr(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, [r0], z) == 0n : Nat},
  h: D.Heap(m, nx, fi, im, [r0], pend, ps)) ->
  D.Heap(D.Put1([D.W1{z, pend}], m), nx, fi, im, Con{r0, D.Fs(D.Put1([D.W1{z, pend}], m), ps, z)}, z, Con{z, ps}):
  (hc, r1) = h
  (hp, r2) = r1
  (hcn, r3) = r2
  (hpt, hr) = r3
  +ws = {[D.W1{z, pend}] : List<&2, D.W1>}
  +M1 = D.Put1(ws, m)
  +N = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
  +X1 = Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, z), pend)
  +e0 = D.put1.f0(ws, m, z)
  +ef1 = Equal.trans(U32, D.Fd(1n, M1, z), Cr.Cir.Cell.get(1n, X1), pend,
    Equal.cong(Cr.Cir.Cell, U32, y => Cr.Cir.Cell.get(1n, y), Cr.Cir.Cells.get(M1, z), X1, D.cl.gs(m, z, X1)), D.cg1(Cr.Cir.Cells.get(m, z), pend))
  +chain = {(%Equal.sym(U32, D.Fd(1n, M1, z), pend, ef1) : D.Chain(ps, M1, _); D.Chain.fz(ps, m, z, X1, pend, hm, hc)) :
    D.Chain(ps, M1, D.Fd(1n, M1, z))}
  +hst1 = {(%Equal.sym(U32, D.Fd(0n, M1, z), D.Fd(0n, m, z), e0) : {U32.is_ne(U32.and(_, 1024), 0) == False{} : Bool}; hst) :
    {D.Fl(M1, z, 1024) == False{} : Bool}}
  +htg1 = {(%Equal.sym(U32, D.Fd(0n, M1, z), D.Fd(0n, m, z), e0) : {Bool.or(U32.is_lt(U32.and(_, 63), 19), U32.is_le(32, U32.and(_, 63))) == True{} : Bool};
      %Equal.sym(Bool, U32.is_lt(D.Tg(m, z), 19), False{}, hnt) : {Bool.or(_, U32.is_le(32, D.Tg(m, z))) == True{} : Bool};
      hge) :
    {Bool.or(U32.is_lt(D.Tg(M1, z), 19), U32.is_le(32, D.Tg(M1, z))) == True{} : Bool}}
  +h01 = Equal.trans(Nat, D.Ptr(N, M1, fi, Con{z, ps}, Con{r0, D.Fs(M1, ps, z)}, z), D.Ptr(N, m, fi, ps, [r0], z), 0n,
    ptr.pop1(m, nx, fi, ps, z, pend, r0, z, hzo, hnt), hz0)
  (({==}, (hnz, chain)),
    ((hzo, (hst1, (htg1, (h01, pendok.pop(ps, m, nx, fi, ps, z, pend, r0, hzo, hnt, hp))))),
    (cnt.pop(N, m, nx, fi, ps, z, pend, r0, fi, hzo, hnt, hcn),
    (pts.pop(N, m, ps, z, pend, fi, im, fi, nx, hnt, hpt), hr))))


# the frames from fr after the pop of sx, whose chain is longer than fr's:
# their cells are not sx, so the store to sx's field 1 and sx in the pend
# list keep them (as frs.st.c)
def frs.pop.c(fs: List<&2, D.AF>, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +sx: U32, +pv: U32, +fr: U32, +n: Nat,
  +ht: {U32.is_lt(D.TgW(D.Fd(0n, m, sx)), 32) == False{} : Bool}, +hn: {Hops(n, m, sx) == True{} : Bool},
  +hf: {Hops(List.length(&2, D.AF, fs), m, fr) == True{} : Bool},
  hl: N.Le(1n+List.length(&2, D.AF, fs), n), h: D.Frs(ds, m, im, fi, nx, ks, img, ps, fr, fs)) ->
  D.Frs(ds, D.Put1([D.W1{sx, pv}], m), im, fi, nx, ks, img, Con{sx, ps}, fr, fs):
  match fs:
    case Nil{}:
      h
    case Con{D.AF{+kind, +q, +k, +a, +b}, +rest}:
      match h:
        case Tuple{e0, Tuple{ev, Tuple{eo, Tuple{es, Tuple{em, Tuple{etg, Tuple{eq, Tuple{ek, Tuple{ia, Tuple{ib, ir}}}}}}}}}}:
          +SV = Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, sx), pv)
          +M2 = Cr.Cir.Cells.set(m, sx, SV)
          +hl2 = hl
          +ne = hops.ne(1n+List.length(&2, D.AF, rest), n, m, fr, sx, hf, hn, hl2)
          +ec = D.cl.go(m, fr, sx, SV, ne)
          +em2 = {(%Equal.sym(Bool, U32.is_eq(sx, fr), False{}, D.ne.sym(fr, sx, ne)) : {Bool.or(_, D.Mem(ps, fr)) == False{} : Bool}; em) :
            {D.Mem(Con{sx, ps}, fr) == False{} : Bool}}
          D.frs.uc(ds, M2, im, fi, nx, ks, img, Con{sx, ps}, fr, Con{D.AF{kind, q, k, a, b}, rest},
            D.frsc.at(ds, M2, im, fi, nx, ks, img, Con{sx, ps}, fr, Cr.Cir.Cells.get(M2, fr), Cr.Cir.Cells.get(m, fr), Con{D.AF{kind, q, k, a, b}, rest}, ec,
              (e0, (ev, (eo, (es, (em2, (etg, (eq, (ek,
                (is.keep(a, ds, m, im, fi, nx, ks, img, sx, SV, D.Fd(2n, m, fr), ht, ia),
                (frsb.st(kind, ds, m, im, fi, nx, ks, img, sx, SV, D.Fd(3n, m, fr), b, ht, ib),
                 frs.pop.c(rest, ds, m, im, fi, nx, ks, img, ps, sx, pv, D.Fd(1n, m, fr), n, ht, hn,
                   D.and.r(Bool.not(U32.is_eq(fr, 0)), Hops(List.length(&2, D.AF, rest), m, D.Fd(1n, m, fr)), hf),
                   N.weaken(1n+List.length(&2, D.AF, rest), n, hl2), ir)))))))))))))

# sx, whose chain is longer, is none of the frames' cells from fr
def mem.frc(fs: List<&2, D.AF>, +m: Cr.Cir.Cells, +sx: U32, +fr: U32, +n: Nat, +hn: {Hops(n, m, sx) == True{} : Bool},
  hf: {Hops(List.length(&2, D.AF, fs), m, fr) == True{} : Bool}, hl: N.Le(1n+List.length(&2, D.AF, fs), n)) ->
  {D.Mem(D.Fr.cells(fs, m, fr), sx) == False{} : Bool}:
  match fs:
    case Nil{}:
      {==}
    case Con{_, +rest}:
      +hf2 = hf
      +hl2 = hl
      %Equal.sym(Bool, U32.is_eq(fr, sx), False{}, hops.ne(1n+List.length(&2, D.AF, rest), n, m, fr, sx, hf2, hn, hl2)) :
        {Bool.or(_, D.Mem(D.Fr.cells(rest, m, D.Fd(1n, m, fr)), sx)) == False{} : Bool}
      mem.frc(rest, m, sx, D.Fd(1n, m, fr), n, hn, D.and.r(Bool.not(U32.is_eq(fr, 0)), Hops(List.length(&2, D.AF, rest), m, D.Fd(1n, m, fr)), hf2),
        N.weaken(1n+List.length(&2, D.AF, rest), n, hl2))

# Clo with no temporary, after z (not STATIC) joins the pend list
def clo.pop.at(bb: Bool, +m: Cr.Cir.Cells, +c: U32, +ps: List<&2, U32>, +z: U32, +eb: {U32.is_eq(c, z) == bb : Bool},
  +hz: {D.Fl(m, z, 1024) == False{} : Bool}, h: {D.Clo.at(m, c, ps, Nil{}, Nil{}) == True{} : Bool}) ->
  {D.Clo.at(m, c, Con{z, ps}, Nil{}, Nil{}) == True{} : Bool}:
  match bb:
    case True{}:
      %Equal.sym(U32, c, z, D.u32.eq(c, z, eb)) :
        {Bool.and(Bool.or(Bool.not(D.Fl(m, _, 1024)), D.All.static(D.Fs(m, Con{z, ps}, _), m)), True{}) == True{} : Bool}
      %Equal.sym(Bool, D.Fl(m, z, 1024), False{}, hz) :
        {Bool.and(Bool.or(Bool.not(_), D.All.static(D.Fs(m, Con{z, ps}, z), m)), True{}) == True{} : Bool}
      {==}
    case False{}:
      %Equal.sym(List<&2, U32>, D.Fs(m, Con{z, ps}, c), D.Fs(m, ps, c), fs.pend.ne(m, ps, z, c, D.ne.sym(c, z, eb))) :
        {Bool.and(Bool.or(Bool.not(D.Fl(m, c, 1024)), D.All.static(_, m)), True{}) == True{} : Bool}
      h

def clo.pop(k: Nat, +m: Cr.Cir.Cells, +c: U32, +ps: List<&2, U32>, +z: U32, +hz: {D.Fl(m, z, 1024) == False{} : Bool},
  h: {D.Clo(k, m, c, ps, Nil{}, Nil{}) == True{} : Bool}) -> {D.Clo(k, m, c, Con{z, ps}, Nil{}, Nil{}) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+(+j):
      +h2 = h
      D.and.i(D.Clo.at(m, c, Con{z, ps}, Nil{}, Nil{}), D.Clo(j, m, U32.inc(c), Con{z, ps}, Nil{}, Nil{}),
        clo.pop.at(U32.is_eq(c, z), m, c, ps, z, {==}, hz, D.and.l(D.Clo.at(m, c, ps, Nil{}, Nil{}), D.Clo(j, m, U32.inc(c), ps, Nil{}, Nil{}), h2)),
        clo.pop(j, m, U32.inc(c), ps, z, hz, D.and.r(D.Clo.at(m, c, ps, Nil{}, Nil{}), D.Clo(j, m, U32.inc(c), ps, Nil{}, Nil{}), h2)))

# the cells of the term b that a frame holds in field 3: those Fs reads past field 2
def frb.cells(kind: D.FK, +m: Cr.Cir.Cells, +fr: U32, +b: Bk.Term) ->
  {D.Rt.cells(D.Fr.rts.b(m, fr, kind, b)) == D.Fs.opt(U32.is_eq(D.FK.tag(kind), 38), D.Fd(3n, m, fr), Nil{}) : List<&2, U32>}:
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

# HS and Acc after the pop of the top frame sp, of the kind kind: the frame
# sp heads the pend list, the next frame is the top, and the frame's terms
# (a, and b for Rwt) are owned roots after the focus' (OS)
def pop.post(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32,
  +im: U32, +focus: Bk.Term, +fs: List<&2, D.AF>, +foc: U32, +sp: U32, +pend: U32, +ps: List<&2, U32>, +kind: D.FK, +q: Bk.Quan,
  +k: Bool, +a: Bk.Term, +b: Bk.Term, +zs: List<&2, D.Rt>,
  +isf: D.Is(ds, m, im, fi, nx, ks, img, foc, focus), +hp: D.Heap(m, nx, fi, im, [foc], pend, ps),
  +io: D.ImgOK(ds, ks, img, m, im, fi, nx),
  +frs: D.Frs(ds, m, im, fi, nx, ks, img, ps, sp, Con{D.AF{kind, q, k, a, b}, fs}),
  hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, [D.Rt{foc, focus}], Nil{}, sp, Con{D.AF{kind, q, k, a, b}, fs}, ps, zs)) ->
  D.P2(D.HS(ds, ks, img, D.Put1([D.W1{sp, pend}], m), nx, fi, im, Con{D.Rt{foc, focus}, Con{D.Rt{D.Fd(2n, m, sp), a}, D.Fr.rts.b(m, sp, kind, b)}},
      Nil{}, fs, D.Fd(1n, m, sp), sp, Con{sp, ps}),
    D.AccK(True{}, ds, ks, img, D.Put1([D.W1{sp, pend}], m), nx, fi, im, Con{D.Rt{foc, focus}, Con{D.Rt{D.Fd(2n, m, sp), a}, D.Fr.rts.b(m, sp, kind, b)}},
      Nil{}, D.Fd(1n, m, sp), fs, Con{sp, ps}, zs)):
  match frs:
    case Tuple{+e0, Tuple{_, Tuple{+eo, Tuple{+es, Tuple{+em, Tuple{+etg, Tuple{_, Tuple{_, Tuple{ia, Tuple{ib, ir}}}}}}}}}}:
      (hzr, r1) = hac
      (_, r2) = r1
      (hzc, r3) = r2
      (hcov, r4) = r3
      (hclo, _) = r4
      +ws = {[D.W1{sp, pend}] : List<&2, D.W1>}
      +M1 = D.Put1(ws, m)
      +X1 = Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, sp), pend)
      +N = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
      +f1 = D.Fd(1n, m, sp)
      +n = D.Fd(2n, m, sp)
      +Frb = D.Fr.rts.b(m, sp, kind, b)
      +OS = {Con{D.Rt{foc, focus}, Con{D.Rt{n, a}, Frb}} : List<&2, D.Rt>}
      +FR = D.Fr.rts(fs, m, f1)
      +FC = D.Fr.cells(fs, m, f1)
      +L = List.length(&2, D.AF, fs)
      +T = D.FK.tag(kind)
      +etg2 = etg
      +hnt = {(%Equal.sym(U32, D.Tg(m, sp), T, etg2) : {U32.is_lt(_, 19) == False{} : Bool}; D.fk.lt(kind)) : {U32.is_lt(D.Tg(m, sp), 19) == False{} : Bool}}
      +hge = {(%Equal.sym(U32, D.Tg(m, sp), T, etg2) : {U32.is_le(32, _) == True{} : Bool}; D.fk.ge(kind)) : {U32.is_le(32, D.Tg(m, sp)) == True{} : Bool}}
      +ht32 = {(%Equal.sym(U32, D.Tg(m, sp), T, etg2) : {U32.is_lt(_, 32) == False{} : Bool}; fk.lt32(kind)) :
        {U32.is_lt(D.TgW(D.Fd(0n, m, sp)), 32) == False{} : Bool}}
      +nd = D.is.nd(ds, m, im, fi, nx, ks, img, foc, focus, isf)
      +hfoc = nd.tglt(True{}, ds, im, fi, nx, foc, Cr.Cir.Cells.get(m, foc), focus, nd)
      +hz0 = ptr.none(m, nx, fi, im, ps, pend, foc, sp, hnt, hfoc, hp)
      +hsp = frs.hops(Con{D.AF{kind, q, k, a, b}, fs}, ds, m, im, fi, nx, ks, img, ps, sp, frs)
      +hf1 = D.and.r(Bool.not(U32.is_eq(sp, 0)), Hops(L, m, f1), hsp)
      +e0m = D.put1.f0(ws, m, sp)
      +hst1 = {(%Equal.sym(U32, D.Fd(0n, M1, sp), D.Fd(0n, m, sp), e0m) : {U32.is_ne(U32.and(_, 1024), 0) == False{} : Bool}; es) :
        {D.Fl(M1, sp, 1024) == False{} : Bool}}
      +heap1 = heap.pop(m, nx, fi, im, foc, pend, ps, sp, eo, hnt, hge, es, em, e0, hz0, hp)
      +ers = Equal.trans(List<&2, U32>, Con{foc, D.Fs(M1, ps, sp)}, Con{foc, D.Fs(m, ps, sp)}, D.Rt.cells(OS),
        Equal.cong(List<&2, U32>, List<&2, U32>, y => Con{foc, y}, D.Fs(M1, ps, sp), D.Fs(m, ps, sp), D.fs.put1(ws, m, ps, sp)),
        Equal.trans(List<&2, U32>, Con{foc, D.Fs(m, ps, sp)}, Con{foc, Con{n, D.Fs.opt(U32.is_eq(T, 38), D.Fd(3n, m, sp), Nil{})}}, D.Rt.cells(OS),
          Equal.cong(List<&2, U32>, List<&2, U32>, y => Con{foc, y}, D.Fs(m, ps, sp), Con{n, D.Fs.opt(U32.is_eq(T, 38), D.Fd(3n, m, sp), Nil{})},
            D.fs.frame(m, ps, sp, T, etg2, D.fk.lt(kind), D.fk.ge(kind), D.fk.le(kind), em)),
          Equal.cong(List<&2, U32>, List<&2, U32>, y => Con{foc, Con{n, y}}, D.Fs.opt(U32.is_eq(T, 38), D.Fd(3n, m, sp), Nil{}), D.Rt.cells(Frb),
            Equal.sym(List<&2, U32>, D.Rt.cells(Frb), D.Fs.opt(U32.is_eq(T, 38), D.Fd(3n, m, sp), Nil{}), frb.cells(kind, m, sp, b)))))
      +heap2 = {(%ers : D.Heap(M1, nx, fi, im, _, sp, Con{sp, ps}); heap1) : D.Heap(M1, nx, fi, im, D.Rt.cells(OS), sp, Con{sp, ps})}
      +rts1 = A.rts.put1(True{}, OS, ds, ws, m, im, fi, nx, ks, img, (isf, (ia, frb.rts(kind, ds, m, im, fi, nx, ks, img, sp, b, ib))))
      +frs1 = frs.pop.c(fs, ds, m, im, fi, nx, ks, img, ps, sp, pend, f1, 1n+L, ht32, hsp, hf1, N.le_refl(1n+L), ir)
      +img1 = D.ImgOK.fz(True{}, ds, ks, img, m, im, fi, nx, ps, [foc], sp, X1, hz0, es, eo, io)
      +PT1 = D.Pend.terms(ps, M1)
      +ept = {(%Equal.sym(U32, D.Fd(0n, M1, sp), D.Fd(0n, m, sp), e0m) :
            {Bool.pick(List<&2, U32>, U32.is_lt(U32.and(_, 63), 19), Con{sp, PT1}, PT1) == D.Pend.terms(ps, m) : List<&2, U32>};
          %Equal.sym(Bool, U32.is_lt(D.Tg(m, sp), 19), False{}, hnt) :
            {Bool.pick(List<&2, U32>, _, Con{sp, PT1}, PT1) == D.Pend.terms(ps, m) : List<&2, U32>};
          A.pend.terms.put1(ps, ws, m)) : {D.Pend.terms(Con{sp, ps}, M1) == D.Pend.terms(ps, m) : List<&2, U32>}}
      +RSo = {Con{D.Rt{foc, focus}, Con{D.Rt{n, a}, List.append(&2, D.Rt, List.append(&2, D.Rt, Frb, FR), zs)}} : List<&2, D.Rt>}
      +RS2 = {Con{D.Rt{foc, focus}, Con{D.Rt{n, a}, List.append(&2, D.Rt, Frb, List.append(&2, D.Rt, FR, zs))}} : List<&2, D.Rt>}
      +XSo = {Con{sp, List.append(&2, U32, FC, ps)} : List<&2, U32>}
      +c1 = Equal.trans(Bool, D.Cov(N, M1, fi, RSo, XSo), D.Cov(N, m, fi, RSo, XSo), True{}, A.cov.put1(N, ws, m, fi, RSo, XSo), hcov)
      +c2 = {(%A.app.assoc(Frb, FR, zs) : {D.Cov(N, M1, fi, Con{D.Rt{foc, focus}, Con{D.Rt{n, a}, _}}, XSo) == True{} : Bool}; c1) :
        {D.Cov(N, M1, fi, RS2, XSo) == True{} : Bool}}
      +c3 = A.cov.mv(D.Cov(N, M1, fi, RS2, XSo), D.Cov(N, M1, fi, RS2, List.append(&2, U32, FC, Con{sp, ps})),
        A.cov.perm.x(N, M1, fi, RS2, Nil{}, [sp], FC, ps), c2)
      +frp = A.fr.put1(fs, ws, m, f1, A.outs.one(FC, sp, mem.frc(fs, m, sp, f1, 1n+L, hsp, hf1, N.le_refl(1n+L))))
      +frc = D.Ex.fst({D.Fr.cells(fs, M1, f1) == FC : List<&2, U32>}, _ => {D.Fr.rts(fs, M1, f1) == FR : List<&2, D.Rt>}, frp)
      +frr = D.Ex.snd({D.Fr.cells(fs, M1, f1) == FC : List<&2, U32>}, _ => {D.Fr.rts(fs, M1, f1) == FR : List<&2, D.Rt>}, frp)
      +c4 = {(%Equal.sym(List<&2, D.Rt>, D.Fr.rts(fs, M1, f1), FR, frr) :
            {D.Cov(N, M1, fi, Con{D.Rt{foc, focus}, Con{D.Rt{n, a}, List.append(&2, D.Rt, Frb, List.append(&2, D.Rt, _, zs))}},
              List.append(&2, U32, D.Fr.cells(fs, M1, f1), Con{sp, ps})) == True{} : Bool};
          %Equal.sym(List<&2, U32>, D.Fr.cells(fs, M1, f1), FC, frc) :
            {D.Cov(N, M1, fi, RS2, List.append(&2, U32, _, Con{sp, ps})) == True{} : Bool};
          c3) :
        {D.Cov(N, M1, fi, List.append(&2, D.Rt, OS, List.append(&2, D.Rt, Nil{}, List.append(&2, D.Rt, D.Fr.rts(fs, M1, f1), zs))),
          List.append(&2, U32, D.Fr.cells(fs, M1, f1), List.append(&2, U32, Nil{}, Con{sp, ps}))) == True{} : Bool}}
      +clo1 = clo.pop(N, M1, fi, ps, sp, hst1,
        Equal.trans(Bool, D.Clo(N, M1, fi, ps, Nil{}, Nil{}), D.Clo(N, m, fi, ps, Nil{}, Nil{}), True{}, A.clo.put1(N, ws, m, fi, ps, Nil{}, Nil{}), hclo))
      ((rts1, (Unit{}, (Unit{}, (frs1, (heap2, img1))))),
        (A.rts.put1(True{}, zs, ds, ws, m, im, fi, nx, ks, img, hzr), (Unit{},
          (Equal.trans(List<&2, U32>, D.Rt.cells(zs), D.Pend.terms(ps, m), D.Pend.terms(Con{sp, ps}, M1), hzc,
            Equal.sym(List<&2, U32>, D.Pend.terms(Con{sp, ps}, M1), D.Pend.terms(ps, m), ept)),
          (c4, (clo1, {==}))))))


# Rwt □ P f
# ---------
#
# mode 1, Rwt □ P f with the value v: when v is Rfl (its tag is rfl), y and
# n get P's and f's cells, M.pop moves the frame to the pend list (its
# terms become roots, pop.post), M.dec drops P and v, and f is the focus: a
# step (Rwt Rfl P f steps to f). Else a halt with 2: Rwt v P f is stuck.

# a node's tag
def nd.tag(-ds: List<&2, Bk.Def>, -im: U32, -fi: U32, -nx: U32, -c: U32, -x: Cr.Cir.Cell, -t: Bk.Term, -tag: U32,
  nd: D.Nd(ds, im, fi, nx, c, x, t, tag)) -> {D.TgW(Cr.Cir.Cell.get(0n, x)) == tag : U32}:
  match nd:
    case Tuple{_, Tuple{_, Tuple{e, _}}}:
      e

# the registers after the Rwt step
def R59.rwt(x: D.R59, +sp: U32, +Q: U32, +y: U32, +n: U32, +d: U32) -> D.R59:
  match x:
    case D.R59{+r4, +r5, +r6, +r7, +r8, +r9, +r10, +r11, +r12, +r13, +r14, +r15, +r16, +r17, +r18, +r19, +r20, +r21, +r22, +r23, +r24, +r25, +r26, +r27, +r28, +r29, +r30, +r31, +r32, +r33, +r34, +r35, +r36, +r37, +r38, +r39, +r40, +r41, +r42, +r43, +r44, +r45, +r46, +r47, +r48, +r49, +r50, +r51, +r52, +r53, +r54, +r55, +r56, +r57, +r58, +r59, +r60, +r61, +r62}:
      D.R59{r4, d, r6, r7, r8, sp, 38, r11, y, r13, Q, n, sp, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}

def rwt.regs(x: D.R59, +foc: U32, +sp: U32, +pend: U32, +Q: U32, +y: U32, +n: U32, +f1: U32, +d1: U32, +p1: U32, +d2: U32, +p2: U32) ->
  {X.X.set(X.X.set(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32,
      X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(x)), 9n, sp), 10n, 38), 14n, Q), 12n, y), 15n, n),
        16n, sp), 2n, f1), 3n, sp), 5n, d1), 3n, p1), 5n, d2), 3n, p2), 0n, n), 1n, 0) ==
    D.RG(n, 0, f1, p2, D.R59.list(R59.rwt(x, sp, Q, y, n, d2))) : List<&2, U32>}:
  match x:
    case D.R59{+r4, +r5, +r6, +r7, +r8, +r9, +r10, +r11, +r12, +r13, +r14, +r15, +r16, +r17, +r18, +r19, +r20, +r21, +r22, +r23, +r24, +r25, +r26, +r27, +r28, +r29, +r30, +r31, +r32, +r33, +r34, +r35, +r36, +r37, +r38, +r39, +r40, +r41, +r42, +r43, +r44, +r45, +r46, +r47, +r48, +r49, +r50, +r51, +r52, +r53, +r54, +r55, +r56, +r57, +r58, +r59, +r60, +r61, +r62}:
      {==}

def plain.rwt() -> {Plain(Mc.M.ret.rwt()) == True{} : Bool}:
  {==}

# Eval: Rwt v P f with a value v that is not Rfl has no cast
def cast.none(v: Bk.Term, +f: Bk.Term, hne: {U32.is_eq(D.A.tag(v), 17) == False{} : Bool}) -> {El.Eval.step.cast(v, f) == None{} : Maybe<Bk.Term>}:
  match v:
    case Bk.Term.Rfl{}:
      D.bool.ft({Some{f} == None{} : Maybe<Bk.Term>}, Equal.sym(Bool, True{}, False{}, hne))
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
    case Bk.Term.Rwt{_, _, _}:
      {==}

# a round from mode 1 with a Rwt □ P f frame on top: M.ret.rwt
def rwt.E(+f: Nat, +foc: U32, +sp: U32, +pend: U32, +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32,
  +lim: U32, +inp: List<&2, Word(8n)>, hz: {U32.is_eq(sp, 0) == False{} : Bool}, +hc: {Cr.Cir.is_cell(sp, im, fi, nx) == True{} : Bool},
  ht: {D.Tg(m, sp) == 38 : U32}) ->
  {Cr.Cir.exec(f, D.B.body(), D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)) == Cr.Cir.exec(f, Mc.M.ret.rwt(), X.X.st(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 38), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), m, nx, fi, im, pg, lim, inp)) : Cr.Cir.Out}:
  X.ret.disp.rwt(f, D.RG(foc, 1, sp, pend, D.R59.list(rest)), m, nx, fi, im, pg, lim, inp, sp, rg.len(rest, foc, 1, sp, pend), {==}, {==}, hz, hc, ht)

# the Rwt step's last statements, after the M.dec of v: f is the focus, mode 0
def rwt.fin(+f: Nat, +m2: Cr.Cir.Cells, +d1: U32, +p1: U32, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32,
  +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat,
  +fs: List<&2, D.AF>, +ps: List<&2, U32>, +q: Bk.Quan, +k: Bool, +a: Bk.Term, +b: Bk.Term, +zs: List<&2, D.Rt>,
  +et: {D.A.plugs(Con{D.AF{D.FK.rwt{}, q, k, a, b}, fs}, Bk.Term.Rfl{}) == t : Bk.Term}, +afs: D.AFs.ok(ds, fs), +s2: Cr.Cir.State,
  q2: (st2 => D.Ex(Cr.Cir.Cells, m3 => D.Ex(U32, d => D.Ex(U32, pend2 => D.Ex(List<&2, U32>, ps2 => D.P2({st2 == Cr.Cir.State{List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 38), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 12n, D.Fd(2n, m, sp)), 15n, D.Fd(3n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 5n, d1), 3n, p1), 5n, d), 3n, pend2), m3, nx, fi, im, pg, lim, inp, Nil{}, 0} : Cr.Cir.State}, D.P2({D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m3, fi) == D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m2, fi) : Nat}, D.P2(D.HSK(True{}, ds, ks, img, m3, nx, fi, im, [D.Rt{D.Fd(3n, m, sp), b}], Nil{}, fs, D.Fd(1n, m, sp), pend2, ps2), D.Ex(List<&2, D.Rt>, zs2 => D.AccK(True{}, ds, ks, img, m3, nx, fi, im, [D.Rt{D.Fd(3n, m, sp), b}], Nil{}, D.Fd(1n, m, sp), fs, ps2, zs2))))))))))(s2)) -> D.PostB(False{}, Cr.Cir.exec(f, X.sel.b(X.sel.b(X.sel.b(X.sel.b(X.sel.b(K.stmt.then(Mc.M.ret.rwt())))))), s2), s => K.MV.next(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), s => st3 => D.HR(ds, t, s, st3), D.Budget(ds, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp))):
  match q2:
    case Tuple{+m3, Tuple{+d2, Tuple{+p2, Tuple{+ps2, Tuple{es, Tuple{_, Tuple{Tuple{Tuple{isn, _}, Tuple{_, Tuple{_, Tuple{frs3, Tuple{heap3, img3}}}}}, Tuple{+zs2, hac3}}}}}}}}:
      +n2 = D.Fd(2n, m, sp)
      +n3 = D.Fd(3n, m, sp)
      +f1 = D.Fd(1n, m, sp)
      +QQ = U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)
      +RG0 = D.RG(foc, 1, sp, pend, D.R59.list(rest))
      +R3 = X.X.set(X.X.set(X.X.set(RG0, 9n, sp), 10n, 38), 14n, QQ)
      +R4 = X.X.set(R3, 12n, n2)
      +R5 = X.X.set(R4, 15n, n3)
      +R6 = X.X.set(X.X.set(X.X.set(R5, 16n, sp), 2n, f1), 3n, sp)
      +hl0 = rg.len(rest, foc, 1, sp, pend)
      +hl3 = X.L.len(X.X.set(X.X.set(RG0, 9n, sp), 10n, 38), 14n, QQ, 63n, X.L.len(X.X.set(RG0, 9n, sp), 10n, 38, 63n, X.L.len(RG0, 9n, sp, 63n, hl0)))
      +hl5 = X.L.len(R4, 15n, n3, 63n, X.L.len(R3, 12n, n2, 63n, hl3))
      +hl6 = X.L.len(X.X.set(X.X.set(R5, 16n, sp), 2n, f1), 3n, sp, 63n, X.L.len(X.X.set(R5, 16n, sp), 2n, f1, 63n, X.L.len(R5, 16n, sp, 63n, hl5)))
      +eg0 = X.L.go(X.X.set(X.X.set(RG0, 9n, sp), 10n, 38), 14n, 0n, QQ, foc, {==}, X.L.go(X.X.set(RG0, 9n, sp), 10n, 0n, 38, foc, {==},
        X.L.go(RG0, 9n, 0n, sp, foc, {==}, {==})))
      +eg9 = X.L.go(X.X.set(X.X.set(RG0, 9n, sp), 10n, 38), 14n, 9n, QQ, sp, {==}, X.L.go(X.X.set(RG0, 9n, sp), 10n, 9n, 38, sp, {==},
        X.L.gs(RG0, 9n, sp, X.L.lt(RG0, 9n, hl0, {==}))))
      +R7 = List.set(&2, U32, List.set(&2, U32, R6, 5n, d1), 3n, p1)
      +R8 = List.set(&2, U32, List.set(&2, U32, R7, 5n, d2), 3n, p2)
      +hl8 = X.L.len(List.set(&2, U32, R7, 5n, d2), 3n, p2, 63n, X.L.len(R7, 5n, d2, 63n,
        X.L.len(List.set(&2, U32, R6, 5n, d1), 3n, p1, 63n, X.L.len(R6, 5n, d1, 63n, hl6))))
      +R9 = X.X.set(R8, 0n, n3)
      +st8 = X.X.st(R8, m3, nx, fi, im, pg, lim, inp)
      +st9 = X.X.st(R9, m3, nx, fi, im, pg, lim, inp)
      +st10 = X.X.st(X.X.set(R9, 1n, 0), m3, nx, fi, im, pg, lim, inp)
      +S0 = D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)
      +g15a = X.L.go(X.X.set(X.X.set(R5, 16n, sp), 2n, f1), 3n, 15n, sp, n3, {==}, X.L.go(X.X.set(R5, 16n, sp), 2n, 15n, f1, n3, {==},
        X.L.go(R5, 16n, 15n, sp, n3, {==}, X.L.gs(R4, 15n, n3, X.L.lt(R4, 15n, X.L.len(R3, 12n, n2, 63n, hl3), {==})))))
      +g15 = X.L.go(List.set(&2, U32, R7, 5n, d2), 3n, 15n, p2, n3, {==}, X.L.go(R7, 5n, 15n, d2, n3, {==},
        X.L.go(List.set(&2, U32, R6, 5n, d1), 3n, 15n, p1, n3, {==}, X.L.go(R6, 5n, 15n, d1, n3, {==}, g15a))))
      +e_s0 = D.eq.set(f, 0n, Mc.M.g(Mc.R.n()), st8, n3, g15, X.L.lt(R8, 0n, hl8, {==}))
      +e_s1 = D.eq.set(f, 1n, Mc.M.c(0), st9, 0, {==}, X.L.lt(R9, 1n, X.L.len(R8, 0n, n3, 63n, hl8), {==}))
      +u = D.A.plugs(fs, b)
      +w2 = D.A.w(False{}, b, fs)
      +estep = {(%et : {El.Eval.step(ds, _) == Some{u} : Maybe<Bk.Term>}; step.plugs(ds, fs, Bk.Term.Rwt{Bk.Term.Rfl{}, a, b}, b, afs, {==})) :
        {El.Eval.step(ds, t) == Some{u} : Maybe<Bk.Term>}}
      +pk = le.max.l(D.Mem.cells(S0), D.Need(ds, S0, t))
      +inv = {(D.Wit{False{}, b, fs, n3, f1, p2, ps2, R59.rwt(rest, sp, QQ, n2, n3, d2)},
        (({==}, ({==}, ({==}, (afs, (rwt.regs(rest, foc, sp, pend, QQ, n2, n3, f1, d1, p1, d2, p2), (isn, (frs3, (heap3, (img3, ({==}, {==})))))))))), (zs2, hac3))) :
        D.Inv(ds, ks, img, st10, u, w2)}
      %Equal.sym(Cr.Cir.State, s2, st8, es) : D.PostB(False{}, Cr.Cir.exec(f, X.sel.b(X.sel.b(X.sel.b(X.sel.b(X.sel.b(K.stmt.then(Mc.M.ret.rwt())))))), _), s => K.MV.next(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), s => st3 => D.HR(ds, t, s, st3), D.Budget(ds, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)))
      %D.rw.seq(f, X.sel.a(X.sel.b(X.sel.b(X.sel.b(X.sel.b(X.sel.b(K.stmt.then(Mc.M.ret.rwt()))))))), X.sel.b(X.sel.b(X.sel.b(X.sel.b(X.sel.b(X.sel.b(K.stmt.then(Mc.M.ret.rwt()))))))), st8, st9, e_s0) : D.PostB(False{}, _, s => K.MV.next(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), s => st3 => D.HR(ds, t, s, st3), D.Budget(ds, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)))
      %D.rw.seq(f, X.sel.a(X.sel.b(X.sel.b(X.sel.b(X.sel.b(X.sel.b(X.sel.b(K.stmt.then(Mc.M.ret.rwt())))))))), X.sel.b(X.sel.b(X.sel.b(X.sel.b(X.sel.b(X.sel.b(X.sel.b(K.stmt.then(Mc.M.ret.rwt())))))))), st9, st10, e_s1) : D.PostB(False{}, _, s => K.MV.next(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), s => st3 => D.HR(ds, t, s, st3), D.Budget(ds, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)))
      %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, X.sel.b(X.sel.b(X.sel.b(X.sel.b(X.sel.b(X.sel.b(X.sel.b(K.stmt.then(Mc.M.ret.rwt())))))))), st10), Cr.Cir.Out.next{st10}, D.eq.nop(f, st10)) : D.PostB(False{}, _, s => K.MV.next(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), s => st3 => D.HR(ds, t, s, st3), D.Budget(ds, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)))
      (Inr{(u, (estep, (w2, inv)))}, pk)

# the M.dec of v, after the M.dec of P
def rwt.dec2(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32,
  +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat,
  +fs: List<&2, D.AF>, +ps: List<&2, U32>, +q: Bk.Quan, +k: Bool, +a: Bk.Term, +b: Bk.Term, +zs: List<&2, D.Rt>,
  +et: {D.A.plugs(Con{D.AF{D.FK.rwt{}, q, k, a, b}, fs}, Bk.Term.Rfl{}) == t : Bk.Term}, +afs: D.AFs.ok(ds, fs), +s: Cr.Cir.State,
  qd: (st2 => D.Ex(Cr.Cir.Cells, m2 => D.Ex(U32, d => D.Ex(U32, pend2 => D.Ex(List<&2, U32>, ps2 => D.P2({st2 == Cr.Cir.State{List.set(&2, U32, List.set(&2, U32, X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 38), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 12n, D.Fd(2n, m, sp)), 15n, D.Fd(3n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 5n, d), 3n, pend2), m2, nx, fi, im, pg, lim, inp, Nil{}, 0} : Cr.Cir.State}, D.P2({D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m2, fi) == D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), D.Put1([D.W1{sp, pend}], m), fi) : Nat}, D.P2(D.HSK(True{}, ds, ks, img, m2, nx, fi, im, Con{D.Rt{foc, Bk.Term.Rfl{}}, [D.Rt{D.Fd(3n, m, sp), b}]}, Nil{}, fs, D.Fd(1n, m, sp), pend2, ps2), D.Ex(List<&2, D.Rt>, zs2 => D.AccK(True{}, ds, ks, img, m2, nx, fi, im, Con{D.Rt{foc, Bk.Term.Rfl{}}, [D.Rt{D.Fd(3n, m, sp), b}]}, Nil{}, D.Fd(1n, m, sp), fs, ps2, zs2))))))))))(s)) -> D.PostB(False{}, Cr.Cir.exec(f, X.sel.b(X.sel.b(X.sel.b(X.sel.b(K.stmt.then(Mc.M.ret.rwt()))))), s), s => K.MV.next(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), s => st3 => D.HR(ds, t, s, st3), D.Budget(ds, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp))):
  match qd:
    case Tuple{+m2, Tuple{+d1, Tuple{+p1, Tuple{+ps1, Tuple{es, Tuple{_, Tuple{hs1, Tuple{+zs1, hac1}}}}}}}}:
      +n2 = D.Fd(2n, m, sp)
      +n3 = D.Fd(3n, m, sp)
      +f1 = D.Fd(1n, m, sp)
      +QQ = U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)
      +RG0 = D.RG(foc, 1, sp, pend, D.R59.list(rest))
      +R3 = X.X.set(X.X.set(X.X.set(RG0, 9n, sp), 10n, 38), 14n, QQ)
      +R4 = X.X.set(R3, 12n, n2)
      +R5 = X.X.set(R4, 15n, n3)
      +R6 = X.X.set(X.X.set(X.X.set(R5, 16n, sp), 2n, f1), 3n, sp)
      +hl0 = rg.len(rest, foc, 1, sp, pend)
      +hl3 = X.L.len(X.X.set(X.X.set(RG0, 9n, sp), 10n, 38), 14n, QQ, 63n, X.L.len(X.X.set(RG0, 9n, sp), 10n, 38, 63n, X.L.len(RG0, 9n, sp, 63n, hl0)))
      +hl5 = X.L.len(R4, 15n, n3, 63n, X.L.len(R3, 12n, n2, 63n, hl3))
      +hl6 = X.L.len(X.X.set(X.X.set(R5, 16n, sp), 2n, f1), 3n, sp, 63n, X.L.len(X.X.set(R5, 16n, sp), 2n, f1, 63n, X.L.len(R5, 16n, sp, 63n, hl5)))
      +eg0 = X.L.go(X.X.set(X.X.set(RG0, 9n, sp), 10n, 38), 14n, 0n, QQ, foc, {==}, X.L.go(X.X.set(RG0, 9n, sp), 10n, 0n, 38, foc, {==},
        X.L.go(RG0, 9n, 0n, sp, foc, {==}, {==})))
      +eg9 = X.L.go(X.X.set(X.X.set(RG0, 9n, sp), 10n, 38), 14n, 9n, QQ, sp, {==}, X.L.go(X.X.set(RG0, 9n, sp), 10n, 9n, 38, sp, {==},
        X.L.gs(RG0, 9n, sp, X.L.lt(RG0, 9n, hl0, {==}))))
      +R7 = List.set(&2, U32, List.set(&2, U32, R6, 5n, d1), 3n, p1)
      +hl7 = X.L.len(List.set(&2, U32, R6, 5n, d1), 3n, p1, 63n, X.L.len(R6, 5n, d1, 63n, hl6))
      +st7 = X.X.st(R7, m2, nx, fi, im, pg, lim, inp)
      +g0 = X.L.go(List.set(&2, U32, R6, 5n, d1), 3n, 0n, p1, foc, {==}, X.L.go(R6, 5n, 0n, d1, foc, {==},
        X.L.go(X.X.set(X.X.set(R5, 16n, sp), 2n, f1), 3n, 0n, sp, foc, {==}, X.L.go(X.X.set(R5, 16n, sp), 2n, 0n, f1, foc, {==},
          X.L.go(R5, 16n, 0n, sp, foc, {==}, X.L.go(R4, 15n, 0n, n3, foc, {==}, X.L.go(R3, 12n, 0n, n2, foc, {==}, eg0)))))))
      +g3 = X.L.gs(List.set(&2, U32, R6, 5n, d1), 3n, p1, X.L.lt(List.set(&2, U32, R6, 5n, d1), 3n, X.L.len(R6, 5n, d1, 63n, hl6), {==}))
      hdec = D.dec.post(f, True{}, ds, ks, img, R7, m2, nx, fi, im, pg, lim, inp, 0n, [D.Rt{D.Fd(3n, m, sp), b}], Nil{}, fs, f1, p1, ps1, foc, Bk.Term.Rfl{}, Nil{}, zs1,
        hs1, hac1, Unit{}, hl7, g0, g3, {==})
      +B = D.Budget(ds, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t)
      %Equal.sym(Cr.Cir.State, s, st7, es) : D.PostB(False{}, Cr.Cir.exec(f, X.sel.b(X.sel.b(X.sel.b(X.sel.b(K.stmt.then(Mc.M.ret.rwt()))))), _), s => K.MV.next(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), s => st3 => D.HR(ds, t, s, st3), D.Budget(ds, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)))
      D.postb.seq(f, False{}, X.sel.a(X.sel.b(X.sel.b(X.sel.b(X.sel.b(K.stmt.then(Mc.M.ret.rwt())))))), X.sel.b(X.sel.b(X.sel.b(X.sel.b(X.sel.b(K.stmt.then(Mc.M.ret.rwt())))))), st7, st2 => D.Ex(Cr.Cir.Cells, m3 => D.Ex(U32, d => D.Ex(U32, pend2 => D.Ex(List<&2, U32>, ps2 => D.P2({st2 == Cr.Cir.State{List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 38), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 12n, D.Fd(2n, m, sp)), 15n, D.Fd(3n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 5n, d1), 3n, p1), 5n, d), 3n, pend2), m3, nx, fi, im, pg, lim, inp, Nil{}, 0} : Cr.Cir.State}, D.P2({D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m3, fi) == D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m2, fi) : Nat}, D.P2(D.HSK(True{}, ds, ks, img, m3, nx, fi, im, [D.Rt{D.Fd(3n, m, sp), b}], Nil{}, fs, D.Fd(1n, m, sp), pend2, ps2), D.Ex(List<&2, D.Rt>, zs2 => D.AccK(True{}, ds, ks, img, m3, nx, fi, im, [D.Rt{D.Fd(3n, m, sp), b}], Nil{}, D.Fd(1n, m, sp), fs, ps2, zs2))))))))), s => K.MV.next(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), s => st2 => Empty, s => st3 => D.HR(ds, t, s, st3), B, D.St.lim(D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)),
        D.postb.wk(False{}, Cr.Cir.exec(f, X.sel.a(X.sel.b(X.sel.b(X.sel.b(X.sel.b(K.stmt.then(Mc.M.ret.rwt())))))), st7), st2 => D.Ex(Cr.Cir.Cells, m3 => D.Ex(U32, d => D.Ex(U32, pend2 => D.Ex(List<&2, U32>, ps2 => D.P2({st2 == Cr.Cir.State{List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 38), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 12n, D.Fd(2n, m, sp)), 15n, D.Fd(3n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 5n, d1), 3n, p1), 5n, d), 3n, pend2), m3, nx, fi, im, pg, lim, inp, Nil{}, 0} : Cr.Cir.State}, D.P2({D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m3, fi) == D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m2, fi) : Nat}, D.P2(D.HSK(True{}, ds, ks, img, m3, nx, fi, im, [D.Rt{D.Fd(3n, m, sp), b}], Nil{}, fs, D.Fd(1n, m, sp), pend2, ps2), D.Ex(List<&2, D.Rt>, zs2 => D.AccK(True{}, ds, ks, img, m3, nx, fi, im, [D.Rt{D.Fd(3n, m, sp), b}], Nil{}, D.Fd(1n, m, sp), fs, ps2, zs2))))))))), s => st2 => Empty, 0n, B, D.St.lim(D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)), hdec, N.le_zero(B)),
        s => st3 => e => Empty.absurd(D.HR(ds, t, s, st3), e), s2 => q2 => rwt.fin(f, m2, d1, p1, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, a, b, zs, et, afs, s2, q2))

# Rfl: y and n set, M.pop, the M.dec of P
def rwt.yes(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32,
  +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat,
  +fs: List<&2, D.AF>, +ps: List<&2, U32>, +q: Bk.Quan, +k: Bool, +a: Bk.Term, +b: Bk.Term, +zs: List<&2, D.Rt>,
  +iv: D.InvOf(ds, ks, img, D.RG(foc, 1, sp, pend, D.R59.list(rest)), m, nx, fi, im, Nil{}, 0, t, w, True{}, Bk.Term.Rfl{}, Con{D.AF{D.FK.rwt{}, q, k, a, b}, fs}, foc, sp, pend, ps, rest),
  hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, [D.Rt{foc, Bk.Term.Rfl{}}], Nil{}, sp, Con{D.AF{D.FK.rwt{}, q, k, a, b}, fs}, ps, zs)) ->
  D.PostB(False{}, Cr.Cir.exec(f, D.B.body(), D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)), s => K.MV.next(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), s => st3 => D.HR(ds, t, s, st3), D.Budget(ds, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp))):
  match iv:
    case Tuple{+et, Tuple{_, Tuple{_, Tuple{+afs, Tuple{_, Tuple{+isf, Tuple{+frs, Tuple{+hp, Tuple{+io, _}}}}}}}}}:
      +n2 = D.Fd(2n, m, sp)
      +n3 = D.Fd(3n, m, sp)
      +f1 = D.Fd(1n, m, sp)
      +QQ = U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)
      +RG0 = D.RG(foc, 1, sp, pend, D.R59.list(rest))
      +R3 = X.X.set(X.X.set(X.X.set(RG0, 9n, sp), 10n, 38), 14n, QQ)
      +R4 = X.X.set(R3, 12n, n2)
      +R5 = X.X.set(R4, 15n, n3)
      +R6 = X.X.set(X.X.set(X.X.set(R5, 16n, sp), 2n, f1), 3n, sp)
      +hl0 = rg.len(rest, foc, 1, sp, pend)
      +hl3 = X.L.len(X.X.set(X.X.set(RG0, 9n, sp), 10n, 38), 14n, QQ, 63n, X.L.len(X.X.set(RG0, 9n, sp), 10n, 38, 63n, X.L.len(RG0, 9n, sp, 63n, hl0)))
      +hl5 = X.L.len(R4, 15n, n3, 63n, X.L.len(R3, 12n, n2, 63n, hl3))
      +hl6 = X.L.len(X.X.set(X.X.set(R5, 16n, sp), 2n, f1), 3n, sp, 63n, X.L.len(X.X.set(R5, 16n, sp), 2n, f1, 63n, X.L.len(R5, 16n, sp, 63n, hl5)))
      +eg0 = X.L.go(X.X.set(X.X.set(RG0, 9n, sp), 10n, 38), 14n, 0n, QQ, foc, {==}, X.L.go(X.X.set(RG0, 9n, sp), 10n, 0n, 38, foc, {==},
        X.L.go(RG0, 9n, 0n, sp, foc, {==}, {==})))
      +eg9 = X.L.go(X.X.set(X.X.set(RG0, 9n, sp), 10n, 38), 14n, 9n, QQ, sp, {==}, X.L.go(X.X.set(RG0, 9n, sp), 10n, 9n, 38, sp, {==},
        X.L.gs(RG0, 9n, sp, X.L.lt(RG0, 9n, hl0, {==}))))
      +S0 = D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)
      +st3 = X.X.st(R3, m, nx, fi, im, pg, lim, inp)
      +st4 = X.X.st(R4, m, nx, fi, im, pg, lim, inp)
      +st5 = X.X.st(R5, m, nx, fi, im, pg, lim, inp)
      +st6 = X.X.st(R6, D.Put1([D.W1{sp, pend}], m), nx, fi, im, pg, lim, inp)
      +KD = {D.FK.rwt{} : D.FK}
      +hz = fr.nz(ds, m, im, fi, nx, ks, img, ps, sp, KD, q, k, a, b, fs, frs)
      +hc = fr.cell(ds, m, im, fi, nx, ks, img, ps, sp, KD, q, k, a, b, fs, frs)
      +ht = fr.tag(ds, m, im, fi, nx, ks, img, ps, sp, KD, q, k, a, b, fs, frs)
      +nd = D.is.nd(ds, m, im, fi, nx, ks, img, foc, Bk.Term.Rfl{}, isf)
      +valid = nd.cell(True{}, ds, im, fi, nx, foc, Cr.Cir.Cells.get(m, foc), Bk.Term.Rfl{}, 17, nd)
      +etag = nd.tag(ds, im, fi, nx, foc, Cr.Cir.Cells.get(m, foc), Bk.Term.Rfl{}, 17, nd)
      +f0 = D.Fd(0n, m, foc)
      +ef = D.ev.fld(0n, Mc.M.g(Mc.R.focus()), R3, m, nx, fi, im, pg, lim, inp, Nil{}, 0, foc, eg0, valid)
      +etg = D.ev.op(Wa.Wasm.Op.and{}, Mc.M.f(0n, Mc.M.g(Mc.R.focus())), Mc.M.c(63), st3, f0, 63, ef, {==})
      +ec = D.ev.op(Wa.Wasm.Op.eq{}, Mc.M.tag(Mc.M.g(Mc.R.focus())), Mc.M.c(17), st3, Wa.Wasm.op(Wa.Wasm.Op.and{}, f0, 63), 17, etg, {==})
      +nz = {(%Equal.sym(U32, D.TgW(f0), 17, etag) : {U32.is_zero(Wa.Wasm.op(Wa.Wasm.Op.eq{}, _, 17)) == False{} : Bool}; {==}) :
        {U32.is_zero(Wa.Wasm.op(Wa.Wasm.Op.eq{}, D.TgW(f0), 17)) == False{} : Bool}}
      +e_if = D.eq.if.t(f, K.stmt.cond(Mc.M.ret.rwt()), K.stmt.then(Mc.M.ret.rwt()), K.stmt.else(Mc.M.ret.rwt()), st3, Wa.Wasm.op(Wa.Wasm.Op.eq{}, D.TgW(f0), 17), ec, nz)
      +e_y = D.eq.set(f, 12n, Mc.M.f(2n, Mc.M.g(Mc.R.h())), st3, n2, D.ev.fld(2n, Mc.M.g(Mc.R.h()), R3, m, nx, fi, im, pg, lim, inp, Nil{}, 0, sp, eg9, hc),
        X.L.lt(R3, 12n, hl3, {==}))
      +eg9b = X.L.go(R3, 12n, 9n, n2, sp, {==}, eg9)
      +e_n = D.eq.set(f, 15n, Mc.M.f(3n, Mc.M.g(Mc.R.h())), st4, n3, D.ev.fld(3n, Mc.M.g(Mc.R.h()), R4, m, nx, fi, im, pg, lim, inp, Nil{}, 0, sp, eg9b, hc),
        X.L.lt(R4, 15n, X.L.len(R3, 12n, n2, 63n, hl3), {==}))
      +g2 = X.L.go(R4, 15n, 2n, n3, sp, {==}, X.L.go(R3, 12n, 2n, n2, sp, {==}, X.L.go(X.X.set(X.X.set(RG0, 9n, sp), 10n, 38), 14n, 2n, QQ, sp, {==},
        X.L.go(X.X.set(RG0, 9n, sp), 10n, 2n, 38, sp, {==}, X.L.go(RG0, 9n, 2n, sp, sp, {==}, {==})))))
      +g3 = X.L.go(R4, 15n, 3n, n3, pend, {==}, X.L.go(R3, 12n, 3n, n2, pend, {==}, X.L.go(X.X.set(X.X.set(RG0, 9n, sp), 10n, 38), 14n, 3n, QQ, pend, {==},
        X.L.go(X.X.set(RG0, 9n, sp), 10n, 3n, 38, pend, {==}, X.L.go(RG0, 9n, 3n, sp, pend, {==}, {==})))))
      +e_pop = X.pop.eq(f, R5, m, nx, fi, im, pg, lim, inp, sp, pend, hl5, g2, g3, hc)
      +pp = pop.post(ds, ks, img, m, nx, fi, im, Bk.Term.Rfl{}, fs, foc, sp, pend, ps, KD, q, k, a, b, zs, isf, hp, io, frs, hac)
      +hs6 = hsk.sw2(ds, ks, img, D.Put1([D.W1{sp, pend}], m), nx, fi, im, foc, Bk.Term.Rfl{}, n2, a, [D.Rt{n3, b}], Nil{}, fs, f1, sp, Con{sp, ps},
        D.Ex.fst(D.HS(ds, ks, img, D.Put1([D.W1{sp, pend}], m), nx, fi, im, Con{D.Rt{foc, Bk.Term.Rfl{}}, Con{D.Rt{n2, a}, [D.Rt{n3, b}]}}, Nil{}, fs, f1, sp, Con{sp, ps}),
          _ => D.AccK(True{}, ds, ks, img, D.Put1([D.W1{sp, pend}], m), nx, fi, im, Con{D.Rt{foc, Bk.Term.Rfl{}}, Con{D.Rt{n2, a}, [D.Rt{n3, b}]}}, Nil{}, f1, fs, Con{sp, ps}, zs), pp))
      +hac6 = acc.sw2(ds, ks, img, D.Put1([D.W1{sp, pend}], m), nx, fi, im, foc, Bk.Term.Rfl{}, n2, a, [D.Rt{n3, b}], f1, fs, Con{sp, ps}, zs,
        D.Ex.snd(D.HS(ds, ks, img, D.Put1([D.W1{sp, pend}], m), nx, fi, im, Con{D.Rt{foc, Bk.Term.Rfl{}}, Con{D.Rt{n2, a}, [D.Rt{n3, b}]}}, Nil{}, fs, f1, sp, Con{sp, ps}),
          _ => D.AccK(True{}, ds, ks, img, D.Put1([D.W1{sp, pend}], m), nx, fi, im, Con{D.Rt{foc, Bk.Term.Rfl{}}, Con{D.Rt{n2, a}, [D.Rt{n3, b}]}}, Nil{}, f1, fs, Con{sp, ps}, zs), pp))
      +g12 = X.L.go(X.X.set(X.X.set(R5, 16n, sp), 2n, f1), 3n, 12n, sp, n2, {==}, X.L.go(X.X.set(R5, 16n, sp), 2n, 12n, f1, n2, {==},
        X.L.go(R5, 16n, 12n, sp, n2, {==}, X.L.go(R4, 15n, 12n, n3, n2, {==}, X.L.gs(R3, 12n, n2, X.L.lt(R3, 12n, hl3, {==}))))))
      +g3b = X.L.gs(X.X.set(X.X.set(R5, 16n, sp), 2n, f1), 3n, sp, X.L.lt(X.X.set(X.X.set(R5, 16n, sp), 2n, f1), 3n,
        X.L.len(X.X.set(R5, 16n, sp), 2n, f1, 63n, X.L.len(R5, 16n, sp, 63n, hl5)), {==}))
      hdec = D.dec.post(f, True{}, ds, ks, img, R6, D.Put1([D.W1{sp, pend}], m), nx, fi, im, pg, lim, inp, 12n, Con{D.Rt{foc, Bk.Term.Rfl{}}, [D.Rt{D.Fd(3n, m, sp), b}]}, Nil{}, fs, f1, sp, Con{sp, ps}, n2, a, Nil{}, zs,
        hs6, hac6, Unit{}, hl6, g12, g3b, {==})
      +B = D.Budget(ds, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t)
      +afs2 = p2.snd(D.AF.ok(ds, D.AF{D.FK.rwt{}, q, k, a, b}), D.AFs.ok(ds, fs), afs)
      %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, D.B.body(), S0), Cr.Cir.exec(f, Mc.M.ret.rwt(), st3), rwt.E(f, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, hz, hc, ht)) :
        D.PostB(False{}, _, s => K.MV.next(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), s => st3 => D.HR(ds, t, s, st3), D.Budget(ds, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)))
      %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, Mc.M.ret.rwt(), st3), Cr.Cir.exec(f, K.stmt.then(Mc.M.ret.rwt()), st3), e_if) : D.PostB(False{}, _, s => K.MV.next(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), s => st3 => D.HR(ds, t, s, st3), D.Budget(ds, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)))
      %D.rw.seq(f, X.sel.a(K.stmt.then(Mc.M.ret.rwt())), X.sel.b(K.stmt.then(Mc.M.ret.rwt())), st3, st4, e_y) : D.PostB(False{}, _, s => K.MV.next(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), s => st3 => D.HR(ds, t, s, st3), D.Budget(ds, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)))
      %D.rw.seq(f, X.sel.a(X.sel.b(K.stmt.then(Mc.M.ret.rwt()))), X.sel.b(X.sel.b(K.stmt.then(Mc.M.ret.rwt()))), st4, st5, e_n) : D.PostB(False{}, _, s => K.MV.next(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), s => st3 => D.HR(ds, t, s, st3), D.Budget(ds, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)))
      %D.rw.seq(f, X.sel.a(X.sel.b(X.sel.b(K.stmt.then(Mc.M.ret.rwt())))), X.sel.b(X.sel.b(X.sel.b(K.stmt.then(Mc.M.ret.rwt())))), st5, st6, e_pop) : D.PostB(False{}, _, s => K.MV.next(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), s => st3 => D.HR(ds, t, s, st3), D.Budget(ds, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)))
      D.postb.seq(f, False{}, X.sel.a(X.sel.b(X.sel.b(X.sel.b(K.stmt.then(Mc.M.ret.rwt()))))), X.sel.b(X.sel.b(X.sel.b(X.sel.b(K.stmt.then(Mc.M.ret.rwt()))))), st6, st2 => D.Ex(Cr.Cir.Cells, m2 => D.Ex(U32, d => D.Ex(U32, pend2 => D.Ex(List<&2, U32>, ps2 => D.P2({st2 == Cr.Cir.State{List.set(&2, U32, List.set(&2, U32, X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 38), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 12n, D.Fd(2n, m, sp)), 15n, D.Fd(3n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 5n, d), 3n, pend2), m2, nx, fi, im, pg, lim, inp, Nil{}, 0} : Cr.Cir.State}, D.P2({D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m2, fi) == D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), D.Put1([D.W1{sp, pend}], m), fi) : Nat}, D.P2(D.HSK(True{}, ds, ks, img, m2, nx, fi, im, Con{D.Rt{foc, Bk.Term.Rfl{}}, [D.Rt{D.Fd(3n, m, sp), b}]}, Nil{}, fs, D.Fd(1n, m, sp), pend2, ps2), D.Ex(List<&2, D.Rt>, zs2 => D.AccK(True{}, ds, ks, img, m2, nx, fi, im, Con{D.Rt{foc, Bk.Term.Rfl{}}, [D.Rt{D.Fd(3n, m, sp), b}]}, Nil{}, D.Fd(1n, m, sp), fs, ps2, zs2))))))))), s => K.MV.next(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), s => st2 => Empty, s => st3 => D.HR(ds, t, s, st3), B, D.St.lim(D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)),
        D.postb.wk(False{}, Cr.Cir.exec(f, X.sel.a(X.sel.b(X.sel.b(X.sel.b(K.stmt.then(Mc.M.ret.rwt()))))), st6), st2 => D.Ex(Cr.Cir.Cells, m2 => D.Ex(U32, d => D.Ex(U32, pend2 => D.Ex(List<&2, U32>, ps2 => D.P2({st2 == Cr.Cir.State{List.set(&2, U32, List.set(&2, U32, X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 38), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 12n, D.Fd(2n, m, sp)), 15n, D.Fd(3n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 5n, d), 3n, pend2), m2, nx, fi, im, pg, lim, inp, Nil{}, 0} : Cr.Cir.State}, D.P2({D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m2, fi) == D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), D.Put1([D.W1{sp, pend}], m), fi) : Nat}, D.P2(D.HSK(True{}, ds, ks, img, m2, nx, fi, im, Con{D.Rt{foc, Bk.Term.Rfl{}}, [D.Rt{D.Fd(3n, m, sp), b}]}, Nil{}, fs, D.Fd(1n, m, sp), pend2, ps2), D.Ex(List<&2, D.Rt>, zs2 => D.AccK(True{}, ds, ks, img, m2, nx, fi, im, Con{D.Rt{foc, Bk.Term.Rfl{}}, [D.Rt{D.Fd(3n, m, sp), b}]}, Nil{}, D.Fd(1n, m, sp), fs, ps2, zs2))))))))), s => st2 => Empty, 0n, B, D.St.lim(D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)), hdec, N.le_zero(B)),
        s => st3 => e => Empty.absurd(D.HR(ds, t, s, st3), e), s => q2 => rwt.dec2(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, a, b, zs, et, afs2, s, q2))

# v is no Rfl: the round halts with 2, as Rwt v P f is stuck
def rwt.no.E(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32,
  +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat,
  +fs: List<&2, D.AF>, +ps: List<&2, U32>, +q: Bk.Quan, +k: Bool, +a: Bk.Term, +b: Bk.Term, +zs: List<&2, D.Rt>, +v: Bk.Term,
  +nd: D.Nd(ds, im, fi, nx, foc, Cr.Cir.Cells.get(m, foc), v, D.A.tag(v)),
  +hz: {U32.is_eq(sp, 0) == False{} : Bool}, +hc: {Cr.Cir.is_cell(sp, im, fi, nx) == True{} : Bool}, +ht: {D.Tg(m, sp) == 38 : U32},
  +hne: {U32.is_eq(D.A.tag(v), 17) == False{} : Bool}) ->
  {Cr.Cir.exec(f, D.B.body(), D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)) == Cr.Cir.Out.halt{2, X.X.st(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 38), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), m, nx, fi, im, pg, lim, inp)} : Cr.Cir.Out}:
  match nd:
    case Tuple{+valid, Tuple{_, Tuple{+etag, _}}}:
      +RG0 = D.RG(foc, 1, sp, pend, D.R59.list(rest))
      +QQ = U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)
      +st3 = X.X.st(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 38), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), m, nx, fi, im, pg, lim, inp)
      +f0 = D.Fd(0n, m, foc)
      +eg0 = X.L.go(X.X.set(X.X.set(RG0, 9n, sp), 10n, 38), 14n, 0n, QQ, foc, {==}, X.L.go(X.X.set(RG0, 9n, sp), 10n, 0n, 38, foc, {==},
        X.L.go(RG0, 9n, 0n, sp, foc, {==}, {==})))
      +ef = D.ev.fld(0n, Mc.M.g(Mc.R.focus()), X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 38), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), m, nx, fi, im, pg, lim, inp, Nil{}, 0, foc, eg0, valid)
      +etg = D.ev.op(Wa.Wasm.Op.and{}, Mc.M.f(0n, Mc.M.g(Mc.R.focus())), Mc.M.c(63), st3, f0, 63, ef, {==})
      +ec = D.ev.op(Wa.Wasm.Op.eq{}, Mc.M.tag(Mc.M.g(Mc.R.focus())), Mc.M.c(17), st3, Wa.Wasm.op(Wa.Wasm.Op.and{}, f0, 63), 17, etg, {==})
      Equal.trans(Cr.Cir.Out, Cr.Cir.exec(f, D.B.body(), D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)), Cr.Cir.exec(f, Mc.M.ret.rwt(), st3), Cr.Cir.Out.halt{2, st3},
        rwt.E(f, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, hz, hc, ht),
        Equal.trans(Cr.Cir.Out, Cr.Cir.exec(f, Mc.M.ret.rwt(), st3), Cr.Cir.exec(f, K.stmt.else(Mc.M.ret.rwt()), st3), Cr.Cir.Out.halt{2, st3},
          D.eq.if.e(f, K.stmt.cond(Mc.M.ret.rwt()), K.stmt.then(Mc.M.ret.rwt()), K.stmt.else(Mc.M.ret.rwt()), st3, Wa.Wasm.op(Wa.Wasm.Op.eq{}, D.TgW(f0), 17), ec,
            K.tag.ne(f0, D.A.tag(v), 17, etag, hne)),
          K.eq.halt(f, 2, st3)))

def rwt.no(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32,
  +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat,
  +fs: List<&2, D.AF>, +ps: List<&2, U32>, +q: Bk.Quan, +k: Bool, +a: Bk.Term, +b: Bk.Term, +zs: List<&2, D.Rt>, +v: Bk.Term,
  +iv: D.InvOf(ds, ks, img, D.RG(foc, 1, sp, pend, D.R59.list(rest)), m, nx, fi, im, Nil{}, 0, t, w, True{}, v, Con{D.AF{D.FK.rwt{}, q, k, a, b}, fs}, foc, sp, pend, ps, rest),
  +hne: {U32.is_eq(D.A.tag(v), 17) == False{} : Bool}) -> D.PostB(False{}, Cr.Cir.exec(f, D.B.body(), D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)), s => K.MV.next(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), s => st3 => D.HR(ds, t, s, st3), D.Budget(ds, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp))):
  match iv:
    case Tuple{+et, Tuple{_, Tuple{+evv, Tuple{+afs, Tuple{_, Tuple{+isf, Tuple{+frs, _}}}}}}}:
      +KD = {D.FK.rwt{} : D.FK}
      +hz = fr.nz(ds, m, im, fi, nx, ks, img, ps, sp, KD, q, k, a, b, fs, frs)
      +hc = fr.cell(ds, m, im, fi, nx, ks, img, ps, sp, KD, q, k, a, b, fs, frs)
      +ht = fr.tag(ds, m, im, fi, nx, ks, img, ps, sp, KD, q, k, a, b, fs, frs)
      +nd = D.is.nd(ds, m, im, fi, nx, ks, img, foc, v, isf)
      +st3 = X.X.st(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 38), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), m, nx, fi, im, pg, lim, inp)
      +RW = {Bk.Term.Rwt{v, a, b} : Bk.Term}
      +hs = {(%Equal.sym(Maybe<Bk.Term>, El.Eval.step(ds, v), None{}, K.ev.stops(ds, v, evv)) :
            {El.Eval.step.rwt(v, a, b, _, El.Eval.vals(ds, v, False{})) == None{} : Maybe<Bk.Term>};
          %Equal.sym(Bool, El.Eval.vals(ds, v, False{}), True{}, evv) : {El.Eval.step.rwt(v, a, b, None{}, _) == None{} : Maybe<Bk.Term>};
          cast.none(v, b, hne)) : {El.Eval.step(ds, RW) == None{} : Maybe<Bk.Term>}}
      +stk = K.ev.stuck(ds, fs, RW, p2.snd(D.AF.ok(ds, D.AF{D.FK.rwt{}, q, k, a, b}), D.AFs.ok(ds, fs), afs), hs, {==})
      %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, D.B.body(), D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)), Cr.Cir.Out.halt{2, st3},
        rwt.no.E(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, a, b, zs, v, nd, hz, hc, ht, hne)) : D.PostB(False{}, _, s => K.MV.next(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), s => st3 => D.HR(ds, t, s, st3), D.Budget(ds, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)))
      K.hr.stuck(ds, t, st3, (%et : D.P2({El.Eval.step(ds, _) == None{} : Maybe<Bk.Term>}, {El.Eval.vals(ds, _, False{}) == False{} : Bool}); stk))

# the round from a Rwt □ P f frame, for any fuel, by the focus' form
def rwt.round(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32,
  +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat,
  +fs: List<&2, D.AF>, +ps: List<&2, U32>, +q: Bk.Quan, +k: Bool, +a: Bk.Term, +b: Bk.Term, +zs: List<&2, D.Rt>, v: Bk.Term,
  +iv: D.InvOf(ds, ks, img, D.RG(foc, 1, sp, pend, D.R59.list(rest)), m, nx, fi, im, Nil{}, 0, t, w, True{}, v, Con{D.AF{D.FK.rwt{}, q, k, a, b}, fs}, foc, sp, pend, ps, rest),
  hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, [D.Rt{foc, v}], Nil{}, sp, Con{D.AF{D.FK.rwt{}, q, k, a, b}, fs}, ps, zs)) ->
  D.PostB(False{}, Cr.Cir.exec(f, D.B.body(), D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)), s => K.MV.next(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), s => st3 => D.HR(ds, t, s, st3), D.Budget(ds, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp))):
  match v:
    case Bk.Term.Var{+i}:
      rwt.no(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, a, b, zs, Bk.Term.Var{i}, iv, {==})
    case Bk.Term.Ref{+k2}:
      rwt.no(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, a, b, zs, Bk.Term.Ref{k2}, iv, {==})
    case Bk.Term.Ann{+x, +y}:
      rwt.no(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, a, b, zs, Bk.Term.Ann{x, y}, iv, {==})
    case Bk.Term.Let{+q2, +x, +y}:
      rwt.no(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, a, b, zs, Bk.Term.Let{q2, x, y}, iv, {==})
    case Bk.Term.Typ{+y}:
      rwt.no(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, a, b, zs, Bk.Term.Typ{y}, iv, {==})
    case Bk.Term.Min{+x, +y}:
      rwt.no(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, a, b, zs, Bk.Term.Min{x, y}, iv, {==})
    case Bk.Term.All{+q2, +x, +y}:
      rwt.no(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, a, b, zs, Bk.Term.All{q2, x, y}, iv, {==})
    case Bk.Term.Lam{+q2, +y}:
      rwt.no(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, a, b, zs, Bk.Term.Lam{q2, y}, iv, {==})
    case Bk.Term.App{+q2, +x, +y}:
      rwt.no(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, a, b, zs, Bk.Term.App{q2, x, y}, iv, {==})
    case Bk.Term.Sig{+q2, +x, +y}:
      rwt.no(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, a, b, zs, Bk.Term.Sig{q2, x, y}, iv, {==})
    case Bk.Term.Tup{+q2, +x, +y}:
      rwt.no(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, a, b, zs, Bk.Term.Tup{q2, x, y}, iv, {==})
    case Bk.Term.Prj{+y}:
      rwt.no(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, a, b, zs, Bk.Term.Prj{y}, iv, {==})
    case Bk.Term.Enu{+e}:
      rwt.no(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, a, b, zs, Bk.Term.Enu{e}, iv, {==})
    case Bk.Term.Lab{+k2}:
      rwt.no(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, a, b, zs, Bk.Term.Lab{k2}, iv, {==})
    case Bk.Term.Mat{+k2, +x, +y}:
      rwt.no(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, a, b, zs, Bk.Term.Mat{k2, x, y}, iv, {==})
    case Bk.Term.Efq{}:
      rwt.no(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, a, b, zs, Bk.Term.Efq{}, iv, {==})
    case Bk.Term.Eql{+x, +y, +z}:
      rwt.no(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, a, b, zs, Bk.Term.Eql{x, y, z}, iv, {==})
    case Bk.Term.Rwt{+x, +y, +z}:
      rwt.no(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, a, b, zs, Bk.Term.Rwt{x, y, z}, iv, {==})
    case Bk.Term.Rfl{}:
      rwt.yes(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, a, b, zs, iv, hac)

# mode 1, Rwt □ P f, with the value v: f when v is Rfl, a step; else halt 2
def rwt.go(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32,
  +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat,
  +fs: List<&2, D.AF>, +ps: List<&2, U32>, +q: Bk.Quan, +k: Bool, +a: Bk.Term, +b: Bk.Term, +zs: List<&2, D.Rt>, v: Bk.Term,
  +iv: D.InvOf(ds, ks, img, D.RG(foc, 1, sp, pend, D.R59.list(rest)), m, nx, fi, im, Nil{}, 0, t, w, True{}, v, Con{D.AF{D.FK.rwt{}, q, k, a, b}, fs}, foc, sp, pend, ps, rest),
  +hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, [D.Rt{foc, v}], Nil{}, sp, Con{D.AF{D.FK.rwt{}, q, k, a, b}, fs}, ps, zs)) ->
  K.MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  match iv:
    case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{+frs, _}}}}}}}:
      +KD = {D.FK.rwt{} : D.FK}
      +hz = fr.nz(ds, m, im, fi, nx, ks, img, ps, sp, KD, q, k, a, b, fs, frs)
      +hc = fr.cell(ds, m, im, fi, nx, ks, img, ps, sp, KD, q, k, a, b, fs, frs)
      +ht = fr.tag(ds, m, im, fi, nx, ks, img, ps, sp, KD, q, k, a, b, fs, frs)
      +st3 = X.X.st(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 38), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), m, nx, fi, im, pg, lim, inp)
      (f => rwt.round(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, a, b, zs, v, iv, hac),
        (0n, (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec(0n, D.B.body(), D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)), Cr.Cir.exec(0n, Mc.M.ret.rwt(), st3),
            rwt.E(0n, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, hz, hc, ht)) : D.Ends(_);
          ends.plain(Mc.M.ret.rwt(), st3, plain.rwt()))))

# Quantity labels
# ---------------
#
# The image's names start with the machine's (Img.known): Q0, Q1 and Q2 are
# the names 7, 8 and 9, and the image's cells 8, 9 and 10 are their labels
# (ImgOK). A label's cell holds its name's number (Nm), so the machine's
# test 7 <= p <= 9 holds exactly of the labels that Quan.read reads.

# equal bytes, by Byte.is_eq
def byte.eq(+x: Word(8n), +y: Word(8n), h: {Sd.Byte.is_eq(x, y) == True{} : Bool}) -> {x == y : Word(8n)}:
  D.weq.eq(8n, x, y, Equal.trans(Bool, D.Weq(8n, x, y), Cmp.is_eq(Word.cmp(8n, x, y)), True{},
    Equal.sym(Bool, Cmp.is_eq(Word.cmp(8n, x, y)), D.Weq(8n, x, y), D.weq.cmp(8n, x, y)), h))

# equal names, by Name.is_eq
def name.eq(a: List<&2, Word(8n)>, b: List<&2, Word(8n)>, h: {Sd.Name.is_eq(a, b) == True{} : Bool}) -> {a == b : List<&2, Word(8n)>}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Con{+x, +xs} Con{+y, +ys}:
      +h2 = h
      +ex = byte.eq(x, y, D.and.l(Sd.Byte.is_eq(x, y), Sd.Name.is_eq(xs, ys), h2))
      +ets = name.eq(xs, ys, D.and.r(Sd.Byte.is_eq(x, y), Sd.Name.is_eq(xs, ys), h2))
      %ex : {Con{x, xs} == Con{_, ys} : List<&2, Word(8n)>}
      %ets : {Con{x, xs} == Con{x, _} : List<&2, Word(8n)>}
      {==}
    case Nil{} Con{+y, +ys}:
      D.bool.ft({Nil{} == Con{y, ys} : List<&2, Word(8n)>}, h)
    case Con{+x, +xs} Nil{}:
      D.bool.ft({Con{x, xs} == Nil{} : List<&2, Word(8n)>}, h)

def mq.none(x: Maybe<Bk.Quan>) -> Type:
  match x:
    case None{}:
      Unit
    case Some{_}:
      Empty

def mq.ne(-q: Bk.Quan, e: {None{} == Some{q} : Maybe<Bk.Quan>}) -> Empty:
  %e : mq.none(_)
  Unit{}

def mq.get(x: Maybe<Bk.Quan>, +d: Bk.Quan) -> Bk.Quan:
  match x:
    case Some{y}:
      y
    case None{}:
      d

def read.some.b(b0: Bool, b1: Bool, b2: Bool, +i: List<&2, Word(8n)>, +q: Bk.Quan,
  e0: {Sd.Name.is_eq(i, El.Quan.name(Bk.Quan.Q0{})) == b0 : Bool}, e1: {Sd.Name.is_eq(i, El.Quan.name(Bk.Quan.Q1{})) == b1 : Bool},
  e2: {Sd.Name.is_eq(i, El.Quan.name(Bk.Quan.Q2{})) == b2 : Bool},
  h: {El.Quan.read.if(b0, Bk.Quan.Q0{}, El.Quan.read.if(b1, Bk.Quan.Q1{}, El.Quan.read.if(b2, Bk.Quan.Q2{}, None{}))) == Some{q} : Maybe<Bk.Quan>}) ->
  {i == El.Quan.name(q) : List<&2, Word(8n)>}:
  match b0:
    case True{}:
      %Equal.cong(Maybe<Bk.Quan>, Bk.Quan, x => mq.get(x, Bk.Quan.Q0{}), Some{Bk.Quan.Q0{}}, Some{q}, h) : {i == El.Quan.name(_) : List<&2, Word(8n)>}
      name.eq(i, El.Quan.name(Bk.Quan.Q0{}), e0)
    case False{}:
      match b1:
        case True{}:
          %Equal.cong(Maybe<Bk.Quan>, Bk.Quan, x => mq.get(x, Bk.Quan.Q1{}), Some{Bk.Quan.Q1{}}, Some{q}, h) : {i == El.Quan.name(_) : List<&2, Word(8n)>}
          name.eq(i, El.Quan.name(Bk.Quan.Q1{}), e1)
        case False{}:
          match b2:
            case True{}:
              %Equal.cong(Maybe<Bk.Quan>, Bk.Quan, x => mq.get(x, Bk.Quan.Q2{}), Some{Bk.Quan.Q2{}}, Some{q}, h) : {i == El.Quan.name(_) : List<&2, Word(8n)>}
              name.eq(i, El.Quan.name(Bk.Quan.Q2{}), e2)
            case False{}:
              Empty.absurd({i == El.Quan.name(q) : List<&2, Word(8n)>},
                mq.ne(q, h))

# a name that Quan.read reads is the quantity's name
def read.some(+i: List<&2, Word(8n)>, +q: Bk.Quan, h: {El.Quan.read(i) == Some{q} : Maybe<Bk.Quan>}) -> {i == El.Quan.name(q) : List<&2, Word(8n)>}:
  read.some.b(Sd.Name.is_eq(i, El.Quan.name(Bk.Quan.Q0{})), Sd.Name.is_eq(i, El.Quan.name(Bk.Quan.Q1{})), Sd.Name.is_eq(i, El.Quan.name(Bk.Quan.Q2{})),
    i, q, {==}, {==}, {==}, h)

# the number of a quantity's name
def qid(q: Bk.Quan) -> U32:
  match q:
    case Bk.Quan.Q0{}:
      7
    case Bk.Quan.Q1{}:
      8
    case Bk.Quan.Q2{}:
      9

def id.q(+ks2: List<&2, List<&2, Word(8n)>>, q: Bk.Quan) -> {Mc.Img.id(Mc.Img.known(ks2), El.Quan.name(q), 0) == qid(q) : U32}:
  match q:
    case Bk.Quan.Q0{}:
      {==}
    case Bk.Quan.Q1{}:
      {==}
    case Bk.Quan.Q2{}:
      {==}

# the name of the number n of the image's names, for n = 7, 8, 9
def name.q(+ks2: List<&2, List<&2, Word(8n)>>, q: Bk.Quan) ->
  {List.get(&2, List<&2, Word(8n)>, Mc.Img.known(ks2), U32.to_nat(qid(q))) == Some{El.Quan.name(q)} : Maybe<&2, List<&2, Word(8n)>>}:
  match q:
    case Bk.Quan.Q0{}:
      {==}
    case Bk.Quan.Q1{}:
      {==}
    case Bk.Quan.Q2{}:
      {==}

def read.q(q: Bk.Quan) -> {El.Quan.read(El.Quan.name(q)) == Some{q} : Maybe<Bk.Quan>}:
  match q:
    case Bk.Quan.Q0{}:
      {==}
    case Bk.Quan.Q1{}:
      {==}
    case Bk.Quan.Q2{}:
      {==}


# ge as Le
def rel.ge(c: Cmp, +x: Nat, +y: Nat, r: N.Rel(c, x, y), h: N.T(Cmp.is_ge(c))) -> N.Le(y, x):
  match c:
    case LT{}:
      Empty.absurd(N.Le(y, x), h)
    case EQ{}:
      %r : N.Le(_, x)
      N.le_refl(x)
    case GT{}:
      N.weaken(y, x, r)

def u.ge(+a: U32, +b: U32, e: {U32.is_ge(a, b) == True{} : Bool}) -> N.Le(U32.to_nat(b), U32.to_nat(a)):
  rel.ge(U32.cmp(a, b), U32.to_nat(a), U32.to_nat(b), N.U32.rel(a, b), N.toT(U32.is_ge(a, b), e))

# a name number p between 7 and 9 names a quantity: Quan.read reads its name
def quan.at(+ks2: List<&2, List<&2, Word(8n)>>, +i: List<&2, Word(8n)>, +p: U32, +q: Bk.Quan,
  en: {T.tm.name(Mc.Img.known(ks2), p) == Some{i} : Maybe<&2, List<&2, Word(8n)>>}, ep: {U32.to_nat(p) == U32.to_nat(qid(q)) : Nat},
  hr: {El.Quan.read(i) == None{} : Maybe<Bk.Quan>}) -> Empty:
  +ei = D.mb.inj(El.Quan.name(q), i, Equal.trans(Maybe<&2, List<&2, Word(8n)>>, Some{El.Quan.name(q)},
    List.get(&2, List<&2, Word(8n)>, Mc.Img.known(ks2), U32.to_nat(qid(q))), Some{i},
    Equal.sym(Maybe<&2, List<&2, Word(8n)>>, List.get(&2, List<&2, Word(8n)>, Mc.Img.known(ks2), U32.to_nat(qid(q))), Some{El.Quan.name(q)}, name.q(ks2, q)),
    (%ep : {List.get(&2, List<&2, Word(8n)>, Mc.Img.known(ks2), _) == Some{i} : Maybe<&2, List<&2, Word(8n)>>}; en)))
  mq.ne(q, Equal.trans(Maybe<Bk.Quan>, None{}, El.Quan.read(i), Some{q}, Equal.sym(Maybe<Bk.Quan>, El.Quan.read(i), None{}, hr),
    (%ei : {El.Quan.read(_) == Some{q} : Maybe<Bk.Quan>}; read.q(q))))

def quan.rng(x: Nat, +ks2: List<&2, List<&2, Word(8n)>>, +i: List<&2, Word(8n)>, +p: U32, ex: {U32.to_nat(p) == x : Nat},
  +en: {T.tm.name(Mc.Img.known(ks2), p) == Some{i} : Maybe<&2, List<&2, Word(8n)>>}, +hr: {El.Quan.read(i) == None{} : Maybe<Bk.Quan>},
  h1: N.Le(7n, x), h2: N.Le(x, 9n)) -> Empty:
  match x:
    case 0n:
      h1
    case 1n+x1:
      match x1:
        case 0n:
          h1
        case 1n+x2:
          match x2:
            case 0n:
              h1
            case 1n+x3:
              match x3:
                case 0n:
                  h1
                case 1n+x4:
                  match x4:
                    case 0n:
                      h1
                    case 1n+x5:
                      match x5:
                        case 0n:
                          h1
                        case 1n+x6:
                          match x6:
                            case 0n:
                              h1
                            case 1n+x7:
                              match x7:
                                case 0n:
                                  quan.at(ks2, i, p, Bk.Quan.Q0{}, en, ex, hr)
                                case 1n+x8:
                                  match x8:
                                    case 0n:
                                      quan.at(ks2, i, p, Bk.Quan.Q1{}, en, ex, hr)
                                    case 1n+x9:
                                      match x9:
                                        case 0n:
                                          quan.at(ks2, i, p, Bk.Quan.Q2{}, en, ex, hr)
                                        case 1n+x10:
                                          h2

# so the machine's test on a name that Quan.read does not read fails
def quan.no.b(bb: Bool, +ks2: List<&2, List<&2, Word(8n)>>, +i: List<&2, Word(8n)>, +p: U32,
  +eb: {Bool.and(U32.is_ge(p, 7), U32.is_le(p, 9)) == bb : Bool},
  en: {T.tm.name(Mc.Img.known(ks2), p) == Some{i} : Maybe<&2, List<&2, Word(8n)>>}, hr: {El.Quan.read(i) == None{} : Maybe<Bk.Quan>}) ->
  {Bool.and(U32.is_ge(p, 7), U32.is_le(p, 9)) == False{} : Bool}:
  match bb:
    case False{}:
      eb
    case True{}:
      Empty.absurd({Bool.and(U32.is_ge(p, 7), U32.is_le(p, 9)) == False{} : Bool},
        quan.rng(U32.to_nat(p), ks2, i, p, {==}, en, hr, u.ge(p, 7, D.and.l(U32.is_ge(p, 7), U32.is_le(p, 9), eb)),
          D.u.le(p, 9, D.and.r(U32.is_ge(p, 7), U32.is_le(p, 9), eb))))

def quan.no(+ks2: List<&2, List<&2, Word(8n)>>, +i: List<&2, Word(8n)>, +p: U32,
  en: {T.tm.name(Mc.Img.known(ks2), p) == Some{i} : Maybe<&2, List<&2, Word(8n)>>}, hr: {El.Quan.read(i) == None{} : Maybe<Bk.Quan>}) ->
  {Bool.and(U32.is_ge(p, 7), U32.is_le(p, 9)) == False{} : Bool}:
  quan.no.b(Bool.and(U32.is_ge(p, 7), U32.is_le(p, 9)), ks2, i, p, {==}, en, hr)

# 0 or 1 and 0 or 1
def and.u32(a: Bool, b: Bool) -> {U32.and(Bool.to_u32(a), Bool.to_u32(b)) == Bool.to_u32(Bool.and(a, b)) : U32}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# The Min step
# ------------
#
# Min a □, with the value v (M.ret.min): the frame pops, and when a and v are
# labels of quantities the focus becomes the image's label of their least
# (M.qmin), a step; else the round halts with 2, as Min a v is stuck. The
# image's labels are STATIC, so the new root changes no count (heap.st).

# a STATIC cell is no other cell of the pend list
def st.ne(b: Bool, +m: Cr.Cir.Cells, +n: U32, +c: U32, eb: {U32.is_eq(n, c) == b : Bool}, hs: {D.Fl(m, n, 1024) == True{} : Bool},
  hc: {D.Fl(m, c, 1024) == False{} : Bool}) -> {U32.is_eq(n, c) == False{} : Bool}:
  match b:
    case False{}:
      eb
    case True{}:
      +e = D.u32.eq(n, c, eb)
      D.bool.ft({U32.is_eq(n, c) == False{} : Bool}, Equal.trans(Bool, False{}, D.Fl(m, c, 1024), True{}, Equal.sym(Bool, D.Fl(m, c, 1024), False{}, hc),
        (%e : {D.Fl(m, _, 1024) == True{} : Bool}; hs)))

def pendok.st(qs: List<&2, U32>, +ps: List<&2, U32>, +m: Cr.Cir.Cells, +fi: U32, +nx: U32, +n: U32, +rs: List<&2, U32>,
  +hs: {D.Fl(m, n, 1024) == True{} : Bool}, h: D.PendOK(qs, ps, m, fi, nx, rs)) -> D.PendOK(qs, ps, m, fi, nx, Con{n, rs}):
  match qs:
    case Nil{}:
      Unit{}
    case Con{+p, +rest}:
      (ho, r1) = h
      (hsp, r2) = r1
      (ht, r3) = r2
      (h0, hr) = r3
      +hsp2 = hsp
      +N = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
      +ne = st.ne(U32.is_eq(n, p), m, n, p, {==}, hs, hsp2)
      (ho, (hsp2, (ht, ((%Equal.sym(Bool, U32.is_eq(n, p), False{}, ne) : {Nat.add(D.Pc(N, m, ps, fi, p), Nat.add(D.Nat.of(_), D.RcL(rs, p))) == 0n : Nat}; h0),
        pendok.st(rest, ps, m, fi, nx, n, rs, hs, hr)))))

def cnt.st.at(bb: Bool, +m: Cr.Cir.Cells, +c: U32, +N: Nat, +fi: U32, +ps: List<&2, U32>, +n: U32, +rs: List<&2, U32>,
  eb: {U32.is_eq(n, c) == bb : Bool}, hs: {D.Fl(m, n, 1024) == True{} : Bool},
  h: {Bool.or(Bool.not(U32.is_lt(D.Tg(m, c), 19)), Bool.or(D.Fl(m, c, 1024), Bool.or(D.Mem(ps, c), Nat.is_eq(U32.to_nat(D.Fd(1n, m, c)), D.Ptr(N, m, fi, ps, rs, c))))) == True{} : Bool}) ->
  {Bool.or(Bool.not(U32.is_lt(D.Tg(m, c), 19)), Bool.or(D.Fl(m, c, 1024), Bool.or(D.Mem(ps, c), Nat.is_eq(U32.to_nat(D.Fd(1n, m, c)), D.Ptr(N, m, fi, ps, Con{n, rs}, c))))) == True{} : Bool}:
  match bb:
    case False{}:
      %Equal.sym(Bool, U32.is_eq(n, c), False{}, eb) : {Bool.or(Bool.not(U32.is_lt(D.Tg(m, c), 19)), Bool.or(D.Fl(m, c, 1024), Bool.or(D.Mem(ps, c), Nat.is_eq(U32.to_nat(D.Fd(1n, m, c)), Nat.add(D.Pc(N, m, ps, fi, c), Nat.add(D.Nat.of(_), D.RcL(rs, c))))))) == True{} : Bool}
      h
    case True{}:
      +e = D.u32.eq(n, c, eb)
      D.or.r(Bool.not(U32.is_lt(D.Tg(m, c), 19)), Bool.or(D.Fl(m, c, 1024), Bool.or(D.Mem(ps, c), Nat.is_eq(U32.to_nat(D.Fd(1n, m, c)), D.Ptr(N, m, fi, ps, Con{n, rs}, c)))),
        D.or.l(D.Fl(m, c, 1024), Bool.or(D.Mem(ps, c), Nat.is_eq(U32.to_nat(D.Fd(1n, m, c)), D.Ptr(N, m, fi, ps, Con{n, rs}, c))), (%e : {D.Fl(m, _, 1024) == True{} : Bool}; hs)))

def cnt.st(k: Nat, +m: Cr.Cir.Cells, +c: U32, +N: Nat, +fi: U32, +ps: List<&2, U32>, +n: U32, +rs: List<&2, U32>,
  +hs: {D.Fl(m, n, 1024) == True{} : Bool}, h: {D.Cnt(k, m, c, N, fi, ps, rs) == True{} : Bool}) ->
  {D.Cnt(k, m, c, N, fi, ps, Con{n, rs}) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+(+j):
      +h2 = h
      +A0 = Bool.or(Bool.not(U32.is_lt(D.Tg(m, c), 19)), Bool.or(D.Fl(m, c, 1024), Bool.or(D.Mem(ps, c), Nat.is_eq(U32.to_nat(D.Fd(1n, m, c)), D.Ptr(N, m, fi, ps, rs, c)))))
      D.and.i(Bool.or(Bool.not(U32.is_lt(D.Tg(m, c), 19)), Bool.or(D.Fl(m, c, 1024), Bool.or(D.Mem(ps, c), Nat.is_eq(U32.to_nat(D.Fd(1n, m, c)), D.Ptr(N, m, fi, ps, Con{n, rs}, c))))), D.Cnt(j, m, U32.inc(c), N, fi, ps, Con{n, rs}),
        cnt.st.at(U32.is_eq(n, c), m, c, N, fi, ps, n, rs, {==}, hs, D.and.l(A0, D.Cnt(j, m, U32.inc(c), N, fi, ps, rs), h2)),
        cnt.st(j, m, U32.inc(c), N, fi, ps, n, rs, hs, D.and.r(A0, D.Cnt(j, m, U32.inc(c), N, fi, ps, rs), h2)))

# one more root, to a STATIC cell, keeps the heap
def heap.st(+m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +n: U32, +rs: List<&2, U32>, +pend: U32, +ps: List<&2, U32>,
  +hs: {D.Fl(m, n, 1024) == True{} : Bool}, h: D.Heap(m, nx, fi, im, rs, pend, ps)) -> D.Heap(m, nx, fi, im, Con{n, rs}, pend, ps):
  (hc, r1) = h
  (hp, r2) = r1
  (hcn, r3) = r2
  +N = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
  (hc, (pendok.st(ps, ps, m, fi, nx, n, rs, hs, hp), (cnt.st(N, m, fi, N, fi, ps, n, rs, hs, hcn), r3)))

# one root, where there was none, keeps the accounting
def acc.root(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32,
  +fi: U32, +im: U32, +r: D.Rt, +sp: U32, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +zs: List<&2, D.Rt>,
  h: D.AccK(True{}, ds, ks, img, m, nx, fi, im, Nil{}, Nil{}, sp, fs, ps, zs)) ->
  D.AccK(True{}, ds, ks, img, m, nx, fi, im, [r], Nil{}, sp, fs, ps, zs):
  (h1, r1) = h
  (h2, r2) = r1
  (h3, r3) = r2
  (hcov, r4) = r3
  (hclo, _) = r4
  +N = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
  (h1, (h2, (h3, (A.cov.root(N, m, fi, r, List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs), List.append(&2, U32, D.Fr.cells(fs, m, sp), ps), hcov),
    (hclo, {==})))))

# a cell at most 290 is the image's, not the machine's
def own.img(b: Bool, +l: U32, +fi: U32, +nx: U32, eb: {U32.is_le(fi, l) == b : Bool}, hl: {U32.is_le(l, 290) == True{} : Bool},
  hz: N.Le(1n+U32.to_nat(290), U32.to_nat(fi))) -> {D.Own(fi, nx, l) == False{} : Bool}:
  match b:
    case False{}:
      %Equal.sym(Bool, U32.is_le(fi, l), False{}, eb) : {Bool.and(_, U32.is_lt(l, nx)) == False{} : Bool}
      {==}
    case True{}:
      Empty.absurd({D.Own(fi, nx, l) == False{} : Bool}, N.not_succ_le(U32.to_nat(290), N.le_trans(1n+U32.to_nat(290), U32.to_nat(fi), U32.to_nat(290), hz,
        N.le_trans(U32.to_nat(fi), U32.to_nat(l), U32.to_nat(290), D.u.le(fi, l, eb), D.u.le(l, 290, hl)))))

# so a label there is STATIC
def lab.st(+ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +l: U32, +i: List<&2, Word(8n)>, hi: D.Is(ds, m, im, fi, nx, ks, img, l, Bk.Term.Lab{i}),
  hl: {U32.is_le(l, 290) == True{} : Bool}, hz: N.Le(1n+U32.to_nat(290), U32.to_nat(fi))) -> {D.Fl(m, l, 1024) == True{} : Bool}:
  match hi:
    case Tuple{Tuple{_, Tuple{ho, _}}, _}:
      (%own.img(U32.is_le(fi, l), l, fi, nx, {==}, hl, hz) : {Bool.or(_, D.FlW(D.Fd(0n, m, l), 1024)) == True{} : Bool}; ho)

# the image's cells are below fi, past 290
def img.hz(-ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -m: Cr.Cir.Cells, +im: U32, +fi: U32,
  -nx: U32, io: D.ImgOK(ds, ks, img, m, im, fi, nx)) -> N.Le(1n+U32.to_nat(290), U32.to_nat(fi)):
  match io:
    case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{e290, eim}}}}}}}:
      N.le_trans(1n+U32.to_nat(290), 1n+U32.to_nat(im), U32.to_nat(fi), D.u.le(290, im, e290), D.u.lt(im, fi, eim))

# the label of a quantity: the image's cell past its name's number
def img.lab(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +im: U32, +fi: U32,
  +nx: U32, q: Bk.Quan, io: D.ImgOK(ds, ks, img, m, im, fi, nx)) ->
  D.Is(ds, m, im, fi, nx, ks, img, U32.add(qid(q), 1), Bk.Term.Lab{El.Quan.name(q)}):
  match q:
    case Bk.Quan.Q0{}:
      match io:
        case Tuple{_, Tuple{_, Tuple{h8, _}}}:
          h8
    case Bk.Quan.Q1{}:
      match io:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{h9, _}}}}:
          h9
    case Bk.Quan.Q2{}:
      match io:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{h10, _}}}}}:
          h10

def lab.le(q: Bk.Quan) -> {U32.is_le(U32.add(qid(q), 1), 290) == True{} : Bool}:
  match q:
    case Bk.Quan.Q0{}:
      {==}
    case Bk.Quan.Q1{}:
      {==}
    case Bk.Quan.Q2{}:
      {==}

# M.qmin's value, on the names i and j
def qm.pick(+c: U32, a: U32, b: U32) -> U32:
  U32.or(U32.and(a, U32.sub(0, c)), U32.and(b, U32.sub(c, 1)))

def qm.v(+i: U32, +j: U32) -> U32:
  qm.pick(Bool.to_u32(U32.is_eq(i, 9)), j, qm.pick(Bool.to_u32(U32.is_eq(j, 9)), i,
    qm.pick(U32.or(Bool.to_u32(U32.is_eq(i, 7)), Bool.to_u32(U32.is_eq(j, 7))), 7, 8)))

def ev.pick(+c: Cr.Cir.Expr, +a: Cr.Cir.Expr, +b: Cr.Cir.Expr, +st: Cr.Cir.State, +cv: U32, +av: U32, +bv: U32,
  +ec: {Cr.Cir.eval(c, st) == Some{cv} : Maybe<&2, U32>}, ea: {Cr.Cir.eval(a, st) == Some{av} : Maybe<&2, U32>},
  eb: {Cr.Cir.eval(b, st) == Some{bv} : Maybe<&2, U32>}) -> {Cr.Cir.eval(Mc.M.pick(c, a, b), st) == Some{qm.pick(cv, av, bv)} : Maybe<&2, U32>}:
  D.ev.op(Wa.Wasm.Op.or{}, Mc.M.and(a, Mc.M.sub(Mc.M.c(0), c)), Mc.M.and(b, Mc.M.sub(c, Mc.M.c(1))), st,
    Wa.Wasm.op(Wa.Wasm.Op.and{}, av, Wa.Wasm.op(Wa.Wasm.Op.sub{}, 0, cv)), Wa.Wasm.op(Wa.Wasm.Op.and{}, bv, Wa.Wasm.op(Wa.Wasm.Op.sub{}, cv, 1)),
    D.ev.op(Wa.Wasm.Op.and{}, a, Mc.M.sub(Mc.M.c(0), c), st, av, Wa.Wasm.op(Wa.Wasm.Op.sub{}, 0, cv), ea,
      D.ev.op(Wa.Wasm.Op.sub{}, Mc.M.c(0), c, st, 0, cv, {==}, ec)),
    D.ev.op(Wa.Wasm.Op.and{}, b, Mc.M.sub(c, Mc.M.c(1)), st, bv, Wa.Wasm.op(Wa.Wasm.Op.sub{}, cv, 1), eb,
      D.ev.op(Wa.Wasm.Op.sub{}, c, Mc.M.c(1), st, cv, 1, ec, {==})))

# M.qmin's run, on the names P and K in registers p and k, and 1 more
def ev.qmin(+st: Cr.Cir.State, +P: U32, +K: U32, +e18: {Cr.Cir.eval(Mc.M.g(Mc.R.p()), st) == Some{P} : Maybe<&2, U32>},
  +e17: {Cr.Cir.eval(Mc.M.g(Mc.R.k()), st) == Some{K} : Maybe<&2, U32>}) ->
  {Cr.Cir.eval(Mc.M.add(Mc.M.qmin(Mc.M.g(Mc.R.p()), Mc.M.g(Mc.R.k())), Mc.M.c(1)), st) == Some{U32.add(qm.v(P, K), 1)} : Maybe<&2, U32>}:
  +ei7 = D.ev.op(Wa.Wasm.Op.eq{}, Mc.M.g(Mc.R.p()), Mc.M.c(Mc.N.q0()), st, P, 7, e18, {==})
  +ej7 = D.ev.op(Wa.Wasm.Op.eq{}, Mc.M.g(Mc.R.k()), Mc.M.c(Mc.N.q0()), st, K, 7, e17, {==})
  +eo = D.ev.op(Wa.Wasm.Op.or{}, Mc.M.eq(Mc.M.g(Mc.R.p()), Mc.M.c(Mc.N.q0())), Mc.M.eq(Mc.M.g(Mc.R.k()), Mc.M.c(Mc.N.q0())), st, Bool.to_u32(U32.is_eq(P, 7)), Bool.to_u32(U32.is_eq(K, 7)), ei7, ej7)
  +e3 = ev.pick(Mc.M.or(Mc.M.eq(Mc.M.g(Mc.R.p()), Mc.M.c(Mc.N.q0())), Mc.M.eq(Mc.M.g(Mc.R.k()), Mc.M.c(Mc.N.q0()))), Mc.M.c(Mc.N.q0()), Mc.M.c(Mc.N.q1()), st, U32.or(Bool.to_u32(U32.is_eq(P, 7)), Bool.to_u32(U32.is_eq(K, 7))), 7, 8, eo, {==}, {==})
  +e2 = ev.pick(Mc.M.eq(Mc.M.g(Mc.R.k()), Mc.M.c(Mc.N.q2())), Mc.M.g(Mc.R.p()), Mc.M.pick(Mc.M.or(Mc.M.eq(Mc.M.g(Mc.R.p()), Mc.M.c(Mc.N.q0())), Mc.M.eq(Mc.M.g(Mc.R.k()), Mc.M.c(Mc.N.q0()))), Mc.M.c(Mc.N.q0()), Mc.M.c(Mc.N.q1())), st, Bool.to_u32(U32.is_eq(K, 9)), P, qm.pick(U32.or(Bool.to_u32(U32.is_eq(P, 7)), Bool.to_u32(U32.is_eq(K, 7))), 7, 8),
    D.ev.op(Wa.Wasm.Op.eq{}, Mc.M.g(Mc.R.k()), Mc.M.c(Mc.N.q2()), st, K, 9, e17, {==}), e18, e3)
  +e1 = ev.pick(Mc.M.eq(Mc.M.g(Mc.R.p()), Mc.M.c(Mc.N.q2())), Mc.M.g(Mc.R.k()), Mc.M.pick(Mc.M.eq(Mc.M.g(Mc.R.k()), Mc.M.c(Mc.N.q2())), Mc.M.g(Mc.R.p()), Mc.M.pick(Mc.M.or(Mc.M.eq(Mc.M.g(Mc.R.p()), Mc.M.c(Mc.N.q0())), Mc.M.eq(Mc.M.g(Mc.R.k()), Mc.M.c(Mc.N.q0()))), Mc.M.c(Mc.N.q0()), Mc.M.c(Mc.N.q1()))), st, Bool.to_u32(U32.is_eq(P, 9)), K, qm.pick(Bool.to_u32(U32.is_eq(K, 9)), P, qm.pick(U32.or(Bool.to_u32(U32.is_eq(P, 7)), Bool.to_u32(U32.is_eq(K, 7))), 7, 8)),
    D.ev.op(Wa.Wasm.Op.eq{}, Mc.M.g(Mc.R.p()), Mc.M.c(Mc.N.q2()), st, P, 9, e18, {==}), e17, e2)
  D.ev.op(Wa.Wasm.Op.add{}, Mc.M.qmin(Mc.M.g(Mc.R.p()), Mc.M.g(Mc.R.k())), Mc.M.c(1), st, qm.v(P, K), 1, e1, {==})

def qm.q77() -> {U32.add(qm.v(7, 7), 1) == 8 : U32}:
  {==}

def qm.q78() -> {U32.add(qm.v(7, 8), 1) == 8 : U32}:
  {==}

def qm.q79() -> {U32.add(qm.v(7, 9), 1) == 8 : U32}:
  {==}

def qm.q87() -> {U32.add(qm.v(8, 7), 1) == 8 : U32}:
  {==}

def qm.q88() -> {U32.add(qm.v(8, 8), 1) == 9 : U32}:
  {==}

def qm.q89() -> {U32.add(qm.v(8, 9), 1) == 9 : U32}:
  {==}

def qm.q97() -> {U32.add(qm.v(9, 7), 1) == 8 : U32}:
  {==}

def qm.q98() -> {U32.add(qm.v(9, 8), 1) == 9 : U32}:
  {==}

def qm.q99() -> {U32.add(qm.v(9, 9), 1) == 10 : U32}:
  {==}

# M.qmin's value is one less than the least quantity's label
def qm.q(qi: Bk.Quan, qj: Bk.Quan) -> {U32.add(qm.v(qid(qi), qid(qj)), 1) == U32.add(qid(El.Quan.min(qi, qj)), 1) : U32}:
  match qi qj:
    case Bk.Quan.Q0{} Bk.Quan.Q0{}:
      qm.q77()
    case Bk.Quan.Q0{} Bk.Quan.Q1{}:
      qm.q78()
    case Bk.Quan.Q0{} Bk.Quan.Q2{}:
      qm.q79()
    case Bk.Quan.Q1{} Bk.Quan.Q0{}:
      qm.q87()
    case Bk.Quan.Q1{} Bk.Quan.Q1{}:
      qm.q88()
    case Bk.Quan.Q1{} Bk.Quan.Q2{}:
      qm.q89()
    case Bk.Quan.Q2{} Bk.Quan.Q0{}:
      qm.q97()
    case Bk.Quan.Q2{} Bk.Quan.Q1{}:
      qm.q98()
    case Bk.Quan.Q2{} Bk.Quan.Q2{}:
      qm.q99()

# the machine's test of the quantities' names holds of quantities' names
def qq.q(qi: Bk.Quan, qj: Bk.Quan) ->
  {U32.is_zero(Bool.to_u32(Bool.and(Bool.and(U32.is_ge(qid(qi), 7), U32.is_le(qid(qi), 9)), Bool.and(U32.is_ge(qid(qj), 7), U32.is_le(qid(qj), 9))))) == False{} : Bool}:
  match qi qj:
    case Bk.Quan.Q0{} Bk.Quan.Q0{}:
      {==}
    case Bk.Quan.Q0{} Bk.Quan.Q1{}:
      {==}
    case Bk.Quan.Q0{} Bk.Quan.Q2{}:
      {==}
    case Bk.Quan.Q1{} Bk.Quan.Q0{}:
      {==}
    case Bk.Quan.Q1{} Bk.Quan.Q1{}:
      {==}
    case Bk.Quan.Q1{} Bk.Quan.Q2{}:
      {==}
    case Bk.Quan.Q2{} Bk.Quan.Q0{}:
      {==}
    case Bk.Quan.Q2{} Bk.Quan.Q1{}:
      {==}
    case Bk.Quan.Q2{} Bk.Quan.Q2{}:
      {==}

# four tests, each 0 or 1, and-ed
def and4(+a: Bool, +b: Bool, +c: Bool, +d: Bool) ->
  {U32.and(U32.and(Bool.to_u32(a), Bool.to_u32(b)), U32.and(Bool.to_u32(c), Bool.to_u32(d))) == Bool.to_u32(Bool.and(Bool.and(a, b), Bool.and(c, d))) : U32}:
  %Equal.sym(U32, U32.and(Bool.to_u32(a), Bool.to_u32(b)), Bool.to_u32(Bool.and(a, b)), and.u32(a, b)) :
    {U32.and(_, U32.and(Bool.to_u32(c), Bool.to_u32(d))) == Bool.to_u32(Bool.and(Bool.and(a, b), Bool.and(c, d))) : U32}
  %Equal.sym(U32, U32.and(Bool.to_u32(c), Bool.to_u32(d)), Bool.to_u32(Bool.and(c, d)), and.u32(c, d)) :
    {U32.and(Bool.to_u32(Bool.and(a, b)), _) == Bool.to_u32(Bool.and(Bool.and(a, b), Bool.and(c, d))) : U32}
  and.u32(Bool.and(a, b), Bool.and(c, d))

def and.f(b: Bool) -> {Bool.and(b, False{}) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# Eval: Min a v of two values steps to their meet
def min.eq(+ds: List<&2, Bk.Def>, +a: Bk.Term, +v: Bk.Term, +ha: {El.Eval.vals(ds, a, False{}) == True{} : Bool},
  +hv: {El.Eval.vals(ds, v, False{}) == True{} : Bool}, r: Maybe<Bk.Term>, hm: {El.Eval.meet(a, v) == r : Maybe<Bk.Term>}) ->
  {El.Eval.step(ds, Bk.Term.Min{a, v}) == r : Maybe<Bk.Term>}:
  %Equal.sym(Maybe<Bk.Term>, El.Eval.step(ds, a), None{}, K.ev.stops(ds, a, ha)) :
    {El.Eval.step.min(a, v, _, El.Eval.vals(ds, a, False{}), El.Eval.step(ds, v), El.Eval.vals(ds, v, False{}), El.Eval.meet(a, v)) == r : Maybe<Bk.Term>}
  %Equal.sym(Bool, El.Eval.vals(ds, a, False{}), True{}, ha) :
    {El.Eval.step.min(a, v, None{}, _, El.Eval.step(ds, v), El.Eval.vals(ds, v, False{}), El.Eval.meet(a, v)) == r : Maybe<Bk.Term>}
  %Equal.sym(Maybe<Bk.Term>, El.Eval.step(ds, v), None{}, K.ev.stops(ds, v, hv)) :
    {El.Eval.step.min(a, v, None{}, True{}, _, El.Eval.vals(ds, v, False{}), El.Eval.meet(a, v)) == r : Maybe<Bk.Term>}
  %Equal.sym(Bool, El.Eval.vals(ds, v, False{}), True{}, hv) :
    {El.Eval.step.min(a, v, None{}, True{}, None{}, _, El.Eval.meet(a, v)) == r : Maybe<Bk.Term>}
  %Equal.sym(Maybe<Bk.Term>, El.Eval.meet(a, v), r, hm) :
    {El.Eval.step.min(a, v, None{}, True{}, None{}, True{}, _) == r : Maybe<Bk.Term>}
  {==}

# Min a v with no meet is stuck: so is t
def mn.stk(+ds: List<&2, Bk.Def>, +fs: List<&2, D.AF>, +q: Bk.Quan, +k: Bool, +a: Bk.Term, +b: Bk.Term, +v: Bk.Term, -t: Bk.Term,
  et: {D.A.plugs(Con{D.AF{D.FK.mina{}, q, k, a, b}, fs}, v) == t : Bk.Term}, afs: D.AFs.ok(ds, Con{D.AF{D.FK.mina{}, q, k, a, b}, fs}), hv: {Bool.or(Bool.not(True{}), El.Eval.vals(ds, v, False{})) == True{} : Bool},
  hm: {El.Eval.meet(a, v) == None{} : Maybe<Bk.Term>}) ->
  D.P2({El.Eval.step(ds, t) == None{} : Maybe<Bk.Term>}, {El.Eval.vals(ds, t, False{}) == False{} : Bool}):
  match afs:
    case Tuple{ha, hfs}:
      %et : D.P2({El.Eval.step(ds, _) == None{} : Maybe<Bk.Term>}, {El.Eval.vals(ds, _, False{}) == False{} : Bool})
      K.ev.stuck(ds, fs, Bk.Term.Min{a, v}, hfs, min.eq(ds, a, v, ha, hv, None{}, hm), {==})

# a run that halts with 2, from a stuck term
def mn.halt(+f: Nat, +ds: List<&2, Bk.Def>, +t: Bk.Term, x: Cr.Cir.Stmt, +st: Cr.Cir.State, -Q: Cr.Cir.State -> Type, -B: Nat, -lim: U32,
  e: {Cr.Cir.exec(f, x, st) == Cr.Cir.Out.halt{2, st} : Cr.Cir.Out},
  stk: D.P2({El.Eval.step(ds, t) == None{} : Maybe<Bk.Term>}, {El.Eval.vals(ds, t, False{}) == False{} : Bool})) ->
  D.PostB(False{}, Cr.Cir.exec(f, x, st), Q, s => st3 => D.HR(ds, t, s, st3), B, lim):
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, x, st), Cr.Cir.Out.halt{2, st}, e) : D.PostB(False{}, _, Q, s => st3 => D.HR(ds, t, s, st3), B, lim)
  K.hr.stuck(ds, t, st, stk)

# a then nop
def pb.nop(+f: Nat, a: Cr.Cir.Stmt, +st: Cr.Cir.State, -Q: Cr.Cir.State -> Type, -H: U32 -> Cr.Cir.State -> Type, -B: Nat, -lim: U32,
  h: D.PostB(False{}, Cr.Cir.exec(f, a, st), Q, H, B, lim)) -> D.PostB(False{}, Cr.Cir.exec(f, Cr.Cir.Stmt.seq{a, Cr.Cir.Stmt.nop{}}, st), Q, H, B, lim):
  D.postb.seq(f, False{}, a, Cr.Cir.Stmt.nop{}, st, Q, Q, H, H, B, lim, h, s => s2 => e => e,
    s2 => q2 => (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, Cr.Cir.Stmt.nop{}, s2), Cr.Cir.Out.next{s2}, D.eq.nop(f, s2)) : D.PostB(False{}, _, Q, H, B, lim); q2))

# the registers after the Min step
def R59.mina(x: D.R59, +sp: U32, +QQ: U32, +xa: U32, +P: U32, +K: U32, +n: U32, +d: U32) -> D.R59:
  match x:
    case D.R59{+r4, +r5, +r6, +r7, +r8, +r9, +r10, +r11, +r12, +r13, +r14, +r15, +r16, +r17, +r18, +r19, +r20, +r21, +r22, +r23, +r24, +r25, +r26, +r27, +r28, +r29, +r30, +r31, +r32, +r33, +r34, +r35, +r36, +r37, +r38, +r39, +r40, +r41, +r42, +r43, +r44, +r45, +r46, +r47, +r48, +r49, +r50, +r51, +r52, +r53, +r54, +r55, +r56, +r57, +r58, +r59, +r60, +r61, +r62}:
      D.R59{r4, d, r6, r7, r8, sp, 40, xa, r12, r13, QQ, n, sp, K, P, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}

def mina.regs(x: D.R59, +foc: U32, +sp: U32, +pend: U32, +QQ: U32, +xa: U32, +f1: U32, +P: U32, +K: U32, +n: U32, +d1: U32, +p1: U32,
  +d2: U32, +p2: U32) ->
  {X.X.set(X.X.set(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(x)), 9n, sp), 10n, 40), 14n, QQ), 11n, xa), 16n, sp), 2n, f1), 3n, sp), 18n, P), 17n, K), 15n, n), 5n, d1), 3n, p1), 5n, d2), 3n, p2), 0n, n), 1n, 0) ==
    D.RG(n, 0, f1, p2, D.R59.list(R59.mina(x, sp, QQ, xa, P, K, n, d2))) : List<&2, U32>}:
  match x:
    case D.R59{+r4, +r5, +r6, +r7, +r8, +r9, +r10, +r11, +r12, +r13, +r14, +r15, +r16, +r17, +r18, +r19, +r20, +r21, +r22, +r23, +r24, +r25, +r26, +r27, +r28, +r29, +r30, +r31, +r32, +r33, +r34, +r35, +r36, +r37, +r38, +r39, +r40, +r41, +r42, +r43, +r44, +r45, +r46, +r47, +r48, +r49, +r50, +r51, +r52, +r53, +r54, +r55, +r56, +r57, +r58, +r59, +r60, +r61, +r62}:
      {==}

def plain.min() -> {Plain(Mc.M.ret.min()) == True{} : Bool}:
  {==}

# a round from mode 1 with a Min a □ frame on top: M.ret.min
def mina.E(+f: Nat, +foc: U32, +sp: U32, +pend: U32, +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32,
  +lim: U32, +inp: List<&2, Word(8n)>, hz: {U32.is_eq(sp, 0) == False{} : Bool}, +hc: {Cr.Cir.is_cell(sp, im, fi, nx) == True{} : Bool},
  ht: {D.Tg(m, sp) == 40 : U32}) ->
  {Cr.Cir.exec(f, D.B.body(), D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)) == Cr.Cir.exec(f, Mc.M.ret.min(), X.X.st(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), m, nx, fi, im, pg, lim, inp)) : Cr.Cir.Out}:
  X.ret.disp.mina(f, D.RG(foc, 1, sp, pend, D.R59.list(rest)), m, nx, fi, im, pg, lim, inp, sp, rg.len(rest, foc, 1, sp, pend), {==}, {==}, hz, hc, ht)

# the Min step's last statements, after the M.dec of v: the label of the
# least quantity is the focus, mode 0
def mn.fin(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32,
  +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat,
  +fs: List<&2, D.AF>, +ps: List<&2, U32>, +q: Bk.Quan, +k: Bool, +i: List<&2, Word(8n)>, +j: List<&2, Word(8n)>, +b: Bk.Term, +zs: List<&2, D.Rt>, +m2: Cr.Cir.Cells, +d1: U32, +p1: U32, +qi: Bk.Quan, +qj: Bk.Quan,
  +eP: {D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)) == qid(qi) : U32}, +eK: {D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc) == qid(qj) : U32},
  eri: {El.Quan.read(i) == Some{qi} : Maybe<Bk.Quan>}, erj: {El.Quan.read(j) == Some{qj} : Maybe<Bk.Quan>},
  +et: {D.A.plugs(Con{D.AF{D.FK.mina{}, q, k, Bk.Term.Lab{i}, b}, fs}, Bk.Term.Lab{j}) == t : Bk.Term}, +afs: D.AFs.ok(ds, Con{D.AF{D.FK.mina{}, q, k, Bk.Term.Lab{i}, b}, fs}), +s2: Cr.Cir.State,
  q2: (st2 => D.Ex(Cr.Cir.Cells, m3 => D.Ex(U32, d => D.Ex(U32, pend2 => D.Ex(List<&2, U32>, ps2 => D.P2({st2 == Cr.Cir.State{List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 15n, U32.add(qm.v(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 1)), 5n, d1), 3n, p1), 5n, d), 3n, pend2), m3, nx, fi, im, pg, lim, inp, Nil{}, 0} : Cr.Cir.State}, D.P2({D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m3, fi) == D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m2, fi) : Nat}, D.P2(D.HSK(True{}, ds, ks, img, m3, nx, fi, im, Nil{}, Nil{}, fs, D.Fd(1n, m, sp), pend2, ps2), D.Ex(List<&2, D.Rt>, zs2 => D.AccK(True{}, ds, ks, img, m3, nx, fi, im, Nil{}, Nil{}, D.Fd(1n, m, sp), fs, ps2, zs2))))))))))(s2)) -> D.PostB(False{}, Cr.Cir.exec(f, X.sel.b(X.sel.b(X.sel.b(K.stmt.then(X.sel.a(X.sel.b(X.sel.b(K.stmt.then(X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min()))))))))))), s2), s => K.MV.next(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), s => st3 => D.HR(ds, t, s, st3), D.Budget(ds, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp))):
  match q2:
    case Tuple{+m3, Tuple{+d2, Tuple{+p2, Tuple{+ps2, Tuple{es, Tuple{_, Tuple{Tuple{_, Tuple{_, Tuple{_, Tuple{frs3, Tuple{heap3, img0}}}}}, Tuple{+zs2, hac3}}}}}}}}:
      +RG0 = D.RG(foc, 1, sp, pend, D.R59.list(rest))
      +QQ = U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)
      +xa = D.Fd(2n, m, sp)
      +f1 = D.Fd(1n, m, sp)
      +hl0 = rg.len(rest, foc, 1, sp, pend)
      +hl3 = X.L.len(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3), 63n, X.L.len(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40, 63n, X.L.len(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp, 63n, rg.len(rest, foc, 1, sp, pend))))
      +hl4 = X.L.len(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp), 63n, hl3)
      +hl5 = X.L.len(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp, 63n, X.L.len(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp), 63n, X.L.len(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp, 63n, hl4)))
      +hl6a = X.L.len(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), 63n, hl5)
      +hl6 = X.L.len(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc), 63n, hl6a)
      +img3 = {img0 : D.ImgOK(ds, ks, img, m3, im, fi, nx)}
      +hl7 = X.L.len(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 15n, U32.add(qm.v(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 1), 63n, hl6)
      +hl8 = X.L.len(List.set(&2, U32, X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 15n, U32.add(qm.v(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 1)), 5n, d1), 3n, p1, 63n, X.L.len(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 15n, U32.add(qm.v(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 1)), 5n, d1, 63n, hl7))
      +hl9 = X.L.len(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 15n, U32.add(qm.v(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 1)), 5n, d1), 3n, p1), 5n, d2), 3n, p2, 63n, X.L.len(List.set(&2, U32, List.set(&2, U32, X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 15n, U32.add(qm.v(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 1)), 5n, d1), 3n, p1), 5n, d2, 63n, hl8))
      +N0 = U32.add(qm.v(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 1)
      +st9 = X.X.st(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 15n, U32.add(qm.v(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 1)), 5n, d1), 3n, p1), 5n, d2), 3n, p2), m3, nx, fi, im, pg, lim, inp)
      +st10 = X.X.st(X.X.set(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 15n, U32.add(qm.v(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 1)), 5n, d1), 3n, p1), 5n, d2), 3n, p2), 0n, U32.add(qm.v(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 1)), m3, nx, fi, im, pg, lim, inp)
      +st11 = X.X.st(X.X.set(X.X.set(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 15n, U32.add(qm.v(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 1)), 5n, d1), 3n, p1), 5n, d2), 3n, p2), 0n, U32.add(qm.v(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 1)), 1n, 0), m3, nx, fi, im, pg, lim, inp)
      +e_s0 = D.eq.set(f, 0n, Mc.M.g(Mc.R.n()), st9, N0, X.L.go(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 15n, U32.add(qm.v(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 1)), 5n, d1), 3n, p1), 5n, d2), 3n, 15n, p2, U32.add(qm.v(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 1), {==}, X.L.go(List.set(&2, U32, List.set(&2, U32, X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 15n, U32.add(qm.v(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 1)), 5n, d1), 3n, p1), 5n, 15n, d2, U32.add(qm.v(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 1), {==}, X.L.go(List.set(&2, U32, X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 15n, U32.add(qm.v(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 1)), 5n, d1), 3n, 15n, p1, U32.add(qm.v(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 1), {==}, X.L.go(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 15n, U32.add(qm.v(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 1)), 5n, 15n, d1, U32.add(qm.v(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 1), {==}, X.L.gs(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 15n, U32.add(qm.v(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 1), X.L.lt(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 15n, hl6, {==})))))), X.L.lt(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 15n, U32.add(qm.v(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 1)), 5n, d1), 3n, p1), 5n, d2), 3n, p2), 0n, hl9, {==}))
      +e_s1 = D.eq.set(f, 1n, Mc.M.c(0), st10, 0, {==}, X.L.lt(X.X.set(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 15n, U32.add(qm.v(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 1)), 5n, d1), 3n, p1), 5n, d2), 3n, p2), 0n, U32.add(qm.v(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 1)), 1n, X.L.len(List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 15n, U32.add(qm.v(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 1)), 5n, d1), 3n, p1), 5n, d2), 3n, p2), 0n, N0, 63n, hl9), {==}))
      +S0 = D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)
      +mq = El.Quan.min(qi, qj)
      +lb = {Bk.Term.Lab{El.Quan.name(El.Quan.min(qi, qj))} : Bk.Term}
      +u = D.A.plugs(fs, lb)
      +w2 = D.A.w(False{}, lb, fs)
      +afs2 = p2.snd(D.AF.ok(ds, D.AF{D.FK.mina{}, q, k, Bk.Term.Lab{i}, b}), D.AFs.ok(ds, fs), afs)
      +hm = {(%Equal.sym(Maybe<Bk.Quan>, El.Quan.read(i), Some{qi}, eri) : {El.Eval.meet.of(_, El.Quan.read(j)) == Some{lb} : Maybe<Bk.Term>};
          %Equal.sym(Maybe<Bk.Quan>, El.Quan.read(j), Some{qj}, erj) : {El.Eval.meet.of(Some{qi}, _) == Some{lb} : Maybe<Bk.Term>};
          {==}) : {El.Eval.meet(Bk.Term.Lab{i}, Bk.Term.Lab{j}) == Some{lb} : Maybe<Bk.Term>}}
      +estep = {(%et : {El.Eval.step(ds, _) == Some{u} : Maybe<Bk.Term>};
          step.plugs(ds, fs, Bk.Term.Min{Bk.Term.Lab{i}, Bk.Term.Lab{j}}, lb, afs2, min.eq(ds, Bk.Term.Lab{i}, Bk.Term.Lab{j}, {==}, {==}, Some{lb}, hm))) :
        {El.Eval.step(ds, t) == Some{u} : Maybe<Bk.Term>}}
      +eN = {Equal.trans(U32, N0, U32.add(qm.v(qid(qi), qid(qj)), 1), U32.add(qid(mq), 1),
          (%eP : {U32.add(qm.v(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 1) == U32.add(qm.v(_, qid(qj)), 1) : U32};
            %eK : {U32.add(qm.v(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 1) == U32.add(qm.v(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), _), 1) : U32};
            {==}),
          qm.q(qi, qj)) : {N0 == U32.add(qid(mq), 1) : U32}}
      +isn = {(%Equal.sym(U32, N0, U32.add(qid(mq), 1), eN) : D.Is(ds, m3, im, fi, nx, ks, img, _, lb);
          img.lab(ds, ks, img, m3, im, fi, nx, mq, img3)) : D.Is(ds, m3, im, fi, nx, ks, img, N0, lb)}
      +hlN = {(%Equal.sym(U32, N0, U32.add(qid(mq), 1), eN) : {U32.is_le(_, 290) == True{} : Bool}; lab.le(mq)) :
        {U32.is_le(N0, 290) == True{} : Bool}}
      +hsN = lab.st(ds, m3, im, fi, nx, ks, img, N0, El.Quan.name(mq), isn, hlN, img.hz(ds, ks, img, m3, im, fi, nx, img3))
      +heapN = heap.st(m3, nx, fi, im, N0, Nil{}, p2, ps2, hsN, heap3)
      +hacN = acc.root(ds, ks, img, m3, nx, fi, im, D.Rt{N0, lb}, f1, fs, ps2, zs2, hac3)
      +pk = le.max.l(D.Mem.cells(S0), D.Need(ds, S0, t))
      +inv = {(D.Wit{False{}, lb, fs, N0, f1, p2, ps2, R59.mina(rest, sp, QQ, xa, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc), N0, d2)},
        (({==}, ({==}, ({==}, (afs2, (mina.regs(rest, foc, sp, pend, QQ, xa, f1, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc), N0, d1, p1, d2, p2),
          (isn, (frs3, (heapN, (img3, ({==}, {==})))))))))), (zs2, hacN))) : D.Inv(ds, ks, img, st11, u, w2)}
      %Equal.sym(Cr.Cir.State, s2, st9, es) : D.PostB(False{}, Cr.Cir.exec(f, X.sel.b(X.sel.b(X.sel.b(K.stmt.then(X.sel.a(X.sel.b(X.sel.b(K.stmt.then(X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min()))))))))))), _), s => K.MV.next(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), s => st3 => D.HR(ds, t, s, st3), D.Budget(ds, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)))
      %D.rw.seq(f, X.sel.a(X.sel.b(X.sel.b(X.sel.b(K.stmt.then(X.sel.a(X.sel.b(X.sel.b(K.stmt.then(X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min())))))))))))), X.sel.b(X.sel.b(X.sel.b(X.sel.b(K.stmt.then(X.sel.a(X.sel.b(X.sel.b(K.stmt.then(X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min())))))))))))), st9, st10, e_s0) : D.PostB(False{}, _, s => K.MV.next(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), s => st3 => D.HR(ds, t, s, st3), D.Budget(ds, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)))
      %D.rw.seq(f, X.sel.a(X.sel.b(X.sel.b(X.sel.b(X.sel.b(K.stmt.then(X.sel.a(X.sel.b(X.sel.b(K.stmt.then(X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min()))))))))))))), X.sel.b(X.sel.b(X.sel.b(X.sel.b(X.sel.b(K.stmt.then(X.sel.a(X.sel.b(X.sel.b(K.stmt.then(X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min()))))))))))))), st10, st11, e_s1) : D.PostB(False{}, _, s => K.MV.next(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), s => st3 => D.HR(ds, t, s, st3), D.Budget(ds, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)))
      %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, X.sel.b(X.sel.b(X.sel.b(X.sel.b(X.sel.b(K.stmt.then(X.sel.a(X.sel.b(X.sel.b(K.stmt.then(X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min()))))))))))))), st11), Cr.Cir.Out.next{st11}, D.eq.nop(f, st11)) : D.PostB(False{}, _, s => K.MV.next(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), s => st3 => D.HR(ds, t, s, st3), D.Budget(ds, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)))
      (Inr{(u, (estep, (w2, inv)))}, pk)

# the M.dec of v, after the M.dec of a
def mn.dec0(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32,
  +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat,
  +fs: List<&2, D.AF>, +ps: List<&2, U32>, +q: Bk.Quan, +k: Bool, +i: List<&2, Word(8n)>, +j: List<&2, Word(8n)>, +b: Bk.Term, +zs: List<&2, D.Rt>, +qi: Bk.Quan, +qj: Bk.Quan,
  +eP: {D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)) == qid(qi) : U32}, +eK: {D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc) == qid(qj) : U32},
  eri: {El.Quan.read(i) == Some{qi} : Maybe<Bk.Quan>}, erj: {El.Quan.read(j) == Some{qj} : Maybe<Bk.Quan>},
  +et: {D.A.plugs(Con{D.AF{D.FK.mina{}, q, k, Bk.Term.Lab{i}, b}, fs}, Bk.Term.Lab{j}) == t : Bk.Term}, +afs: D.AFs.ok(ds, Con{D.AF{D.FK.mina{}, q, k, Bk.Term.Lab{i}, b}, fs}), +s: Cr.Cir.State,
  qd: (st2 => D.Ex(Cr.Cir.Cells, m2 => D.Ex(U32, d => D.Ex(U32, pend2 => D.Ex(List<&2, U32>, ps2 => D.P2({st2 == Cr.Cir.State{List.set(&2, U32, List.set(&2, U32, X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 15n, U32.add(qm.v(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 1)), 5n, d), 3n, pend2), m2, nx, fi, im, pg, lim, inp, Nil{}, 0} : Cr.Cir.State}, D.P2({D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m2, fi) == D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), D.Put1([D.W1{sp, pend}], m), fi) : Nat}, D.P2(D.HSK(True{}, ds, ks, img, m2, nx, fi, im, [D.Rt{foc, Bk.Term.Lab{j}}], Nil{}, fs, D.Fd(1n, m, sp), pend2, ps2), D.Ex(List<&2, D.Rt>, zs2 => D.AccK(True{}, ds, ks, img, m2, nx, fi, im, [D.Rt{foc, Bk.Term.Lab{j}}], Nil{}, D.Fd(1n, m, sp), fs, ps2, zs2))))))))))(s)) -> D.PostB(False{}, Cr.Cir.exec(f, X.sel.b(X.sel.b(K.stmt.then(X.sel.a(X.sel.b(X.sel.b(K.stmt.then(X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min())))))))))), s), s => K.MV.next(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), s => st3 => D.HR(ds, t, s, st3), D.Budget(ds, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp))):
  match qd:
    case Tuple{+m2, Tuple{+d1, Tuple{+p1, Tuple{+ps1, Tuple{es, Tuple{_, Tuple{hs1, Tuple{+zs1, hac1}}}}}}}}:
      +RG0 = D.RG(foc, 1, sp, pend, D.R59.list(rest))
      +QQ = U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)
      +xa = D.Fd(2n, m, sp)
      +f1 = D.Fd(1n, m, sp)
      +hl0 = rg.len(rest, foc, 1, sp, pend)
      +hl3 = X.L.len(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3), 63n, X.L.len(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40, 63n, X.L.len(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp, 63n, rg.len(rest, foc, 1, sp, pend))))
      +hl4 = X.L.len(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp), 63n, hl3)
      +hl5 = X.L.len(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp, 63n, X.L.len(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp), 63n, X.L.len(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp, 63n, hl4)))
      +hl6a = X.L.len(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), 63n, hl5)
      +hl6 = X.L.len(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc), 63n, hl6a)
      +hl7 = X.L.len(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 15n, U32.add(qm.v(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 1), 63n, hl6)
      +hl8 = X.L.len(List.set(&2, U32, X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 15n, U32.add(qm.v(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 1)), 5n, d1), 3n, p1, 63n, X.L.len(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 15n, U32.add(qm.v(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 1)), 5n, d1, 63n, hl7))
      +eg0 = X.L.go(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, 0n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3), foc, {==}, X.L.go(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 0n, 40, foc, {==}, X.L.go(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, 0n, sp, foc, {==}, {==})))
      +g0_5 = X.L.go(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, 0n, sp, foc, {==}, X.L.go(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, 0n, D.Fd(1n, m, sp), foc, {==}, X.L.go(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, 0n, sp, foc, {==}, X.L.go(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, 0n, D.Fd(2n, m, sp), foc, {==}, eg0))))
      +st8 = X.X.st(List.set(&2, U32, List.set(&2, U32, X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 15n, U32.add(qm.v(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 1)), 5n, d1), 3n, p1), m2, nx, fi, im, pg, lim, inp)
      hdec = D.dec.post(f, True{}, ds, ks, img, List.set(&2, U32, List.set(&2, U32, X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 15n, U32.add(qm.v(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 1)), 5n, d1), 3n, p1), m2, nx, fi, im, pg, lim, inp, 0n, Nil{}, Nil{}, fs, f1, p1, ps1, foc, Bk.Term.Lab{j}, Nil{}, zs1,
        hs1, hac1, Unit{}, hl8, X.L.go(List.set(&2, U32, X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 15n, U32.add(qm.v(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 1)), 5n, d1), 3n, 0n, p1, foc, {==}, X.L.go(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 15n, U32.add(qm.v(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 1)), 5n, 0n, d1, foc, {==}, X.L.go(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 15n, 0n, U32.add(qm.v(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 1), foc, {==}, X.L.go(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, 0n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc), foc, {==}, X.L.go(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, 0n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), foc, {==}, g0_5))))), X.L.gs(List.set(&2, U32, X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 15n, U32.add(qm.v(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 1)), 5n, d1), 3n, p1, X.L.lt(List.set(&2, U32, X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 15n, U32.add(qm.v(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 1)), 5n, d1), 3n, X.L.len(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 15n, U32.add(qm.v(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 1)), 5n, d1, 63n, hl7), {==})), {==})
      +B = D.Budget(ds, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t)
      %Equal.sym(Cr.Cir.State, s, st8, es) : D.PostB(False{}, Cr.Cir.exec(f, X.sel.b(X.sel.b(K.stmt.then(X.sel.a(X.sel.b(X.sel.b(K.stmt.then(X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min())))))))))), _), s => K.MV.next(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), s => st3 => D.HR(ds, t, s, st3), D.Budget(ds, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)))
      D.postb.seq(f, False{}, X.sel.a(X.sel.b(X.sel.b(K.stmt.then(X.sel.a(X.sel.b(X.sel.b(K.stmt.then(X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min()))))))))))), X.sel.b(X.sel.b(X.sel.b(K.stmt.then(X.sel.a(X.sel.b(X.sel.b(K.stmt.then(X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min()))))))))))), st8, st2 => D.Ex(Cr.Cir.Cells, m3 => D.Ex(U32, d => D.Ex(U32, pend2 => D.Ex(List<&2, U32>, ps2 => D.P2({st2 == Cr.Cir.State{List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 15n, U32.add(qm.v(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 1)), 5n, d1), 3n, p1), 5n, d), 3n, pend2), m3, nx, fi, im, pg, lim, inp, Nil{}, 0} : Cr.Cir.State}, D.P2({D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m3, fi) == D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m2, fi) : Nat}, D.P2(D.HSK(True{}, ds, ks, img, m3, nx, fi, im, Nil{}, Nil{}, fs, D.Fd(1n, m, sp), pend2, ps2), D.Ex(List<&2, D.Rt>, zs2 => D.AccK(True{}, ds, ks, img, m3, nx, fi, im, Nil{}, Nil{}, D.Fd(1n, m, sp), fs, ps2, zs2))))))))), s => K.MV.next(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), s => st2 => Empty, s => st3 => D.HR(ds, t, s, st3), B, D.St.lim(D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)),
        D.postb.wk(False{}, Cr.Cir.exec(f, X.sel.a(X.sel.b(X.sel.b(K.stmt.then(X.sel.a(X.sel.b(X.sel.b(K.stmt.then(X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min()))))))))))), st8), st2 => D.Ex(Cr.Cir.Cells, m3 => D.Ex(U32, d => D.Ex(U32, pend2 => D.Ex(List<&2, U32>, ps2 => D.P2({st2 == Cr.Cir.State{List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 15n, U32.add(qm.v(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 1)), 5n, d1), 3n, p1), 5n, d), 3n, pend2), m3, nx, fi, im, pg, lim, inp, Nil{}, 0} : Cr.Cir.State}, D.P2({D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m3, fi) == D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m2, fi) : Nat}, D.P2(D.HSK(True{}, ds, ks, img, m3, nx, fi, im, Nil{}, Nil{}, fs, D.Fd(1n, m, sp), pend2, ps2), D.Ex(List<&2, D.Rt>, zs2 => D.AccK(True{}, ds, ks, img, m3, nx, fi, im, Nil{}, Nil{}, D.Fd(1n, m, sp), fs, ps2, zs2))))))))), s => st2 => Empty, 0n, B, D.St.lim(D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)), hdec, N.le_zero(B)),
        s => st3 => e => Empty.absurd(D.HR(ds, t, s, st3), e),
        s2 => q2 => mn.fin(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, i, j, b, zs, m2, d1, p1, qi, qj, eP, eK, eri, erj, et, afs, s2, q2))

# both are labels of quantities: register n gets the least's name, the M.dec
# of a, then of v
def mn.ok(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32,
  +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat,
  +fs: List<&2, D.AF>, +ps: List<&2, U32>, +q: Bk.Quan, +k: Bool, +i: List<&2, Word(8n)>, +j: List<&2, Word(8n)>, +b: Bk.Term, +zs: List<&2, D.Rt>, +qi: Bk.Quan, +qj: Bk.Quan,
  +eP: {D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)) == qid(qi) : U32}, +eK: {D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc) == qid(qj) : U32},
  eri: {El.Quan.read(i) == Some{qi} : Maybe<Bk.Quan>}, erj: {El.Quan.read(j) == Some{qj} : Maybe<Bk.Quan>},
  +et: {D.A.plugs(Con{D.AF{D.FK.mina{}, q, k, Bk.Term.Lab{i}, b}, fs}, Bk.Term.Lab{j}) == t : Bk.Term}, +afs: D.AFs.ok(ds, Con{D.AF{D.FK.mina{}, q, k, Bk.Term.Lab{i}, b}, fs}), +pp: D.P2(D.HS(ds, ks, img, D.Put1([D.W1{sp, pend}], m), nx, fi, im, Con{D.Rt{foc, Bk.Term.Lab{j}}, Con{D.Rt{D.Fd(2n, m, sp), Bk.Term.Lab{i}}, D.Fr.rts.b(m, sp, D.FK.mina{}, b)}},
      Nil{}, fs, D.Fd(1n, m, sp), sp, Con{sp, ps}),
    D.AccK(True{}, ds, ks, img, D.Put1([D.W1{sp, pend}], m), nx, fi, im, Con{D.Rt{foc, Bk.Term.Lab{j}}, Con{D.Rt{D.Fd(2n, m, sp), Bk.Term.Lab{i}}, D.Fr.rts.b(m, sp, D.FK.mina{}, b)}},
      Nil{}, D.Fd(1n, m, sp), fs, Con{sp, ps}, zs))) ->
  D.PostB(False{}, Cr.Cir.exec(f, K.stmt.then(X.sel.a(X.sel.b(X.sel.b(K.stmt.then(X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min())))))))), X.X.st(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), D.Put1([D.W1{sp, pend}], m), nx, fi, im, pg, lim, inp)), s => K.MV.next(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), s => st3 => D.HR(ds, t, s, st3), D.Budget(ds, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp))):
  +RG0 = D.RG(foc, 1, sp, pend, D.R59.list(rest))
  +QQ = U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)
  +xa = D.Fd(2n, m, sp)
  +f1 = D.Fd(1n, m, sp)
  +hl0 = rg.len(rest, foc, 1, sp, pend)
  +hl3 = X.L.len(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3), 63n, X.L.len(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40, 63n, X.L.len(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp, 63n, rg.len(rest, foc, 1, sp, pend))))
  +hl4 = X.L.len(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp), 63n, hl3)
  +hl5 = X.L.len(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp, 63n, X.L.len(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp), 63n, X.L.len(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp, 63n, hl4)))
  +hl6a = X.L.len(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), 63n, hl5)
  +hl6 = X.L.len(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc), 63n, hl6a)
  +hl7 = X.L.len(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 15n, U32.add(qm.v(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 1), 63n, hl6)
  +eg0 = X.L.go(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, 0n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3), foc, {==}, X.L.go(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 0n, 40, foc, {==}, X.L.go(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, 0n, sp, foc, {==}, {==})))
  +g11_5 = X.L.go(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, 11n, sp, D.Fd(2n, m, sp), {==}, X.L.go(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, 11n, D.Fd(1n, m, sp), D.Fd(2n, m, sp), {==}, X.L.go(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, 11n, sp, D.Fd(2n, m, sp), {==}, X.L.gs(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp), X.L.lt(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, hl3, {==})))))
  +N0 = U32.add(qm.v(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 1)
  +st7 = X.X.st(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), D.Put1([D.W1{sp, pend}], m), nx, fi, im, pg, lim, inp)
  +st8 = X.X.st(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 15n, U32.add(qm.v(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 1)), D.Put1([D.W1{sp, pend}], m), nx, fi, im, pg, lim, inp)
  +e_n = D.eq.set(f, 15n, Mc.M.add(Mc.M.qmin(Mc.M.g(Mc.R.p()), Mc.M.g(Mc.R.k())), Mc.M.c(1)), st7, N0, ev.qmin(st7, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc), X.L.go(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc), D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), {==}, X.L.gs(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), X.L.lt(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, hl5, {==}))), X.L.gs(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc), X.L.lt(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, hl6a, {==}))), X.L.lt(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 15n, hl6, {==}))
  +OS = {Con{D.Rt{foc, Bk.Term.Lab{j}}, Con{D.Rt{xa, Bk.Term.Lab{i}}, Nil{}}} : List<&2, D.Rt>}
  +hs6 = hsk.sw2(ds, ks, img, D.Put1([D.W1{sp, pend}], m), nx, fi, im, foc, Bk.Term.Lab{j}, xa, Bk.Term.Lab{i}, Nil{}, Nil{}, fs, f1, sp, Con{sp, ps},
    D.Ex.fst(D.HS(ds, ks, img, D.Put1([D.W1{sp, pend}], m), nx, fi, im, OS, Nil{}, fs, f1, sp, Con{sp, ps}),
      _ => D.AccK(True{}, ds, ks, img, D.Put1([D.W1{sp, pend}], m), nx, fi, im, OS, Nil{}, f1, fs, Con{sp, ps}, zs), pp))
  +hac6 = acc.sw2(ds, ks, img, D.Put1([D.W1{sp, pend}], m), nx, fi, im, foc, Bk.Term.Lab{j}, xa, Bk.Term.Lab{i}, Nil{}, f1, fs, Con{sp, ps}, zs,
    D.Ex.snd(D.HS(ds, ks, img, D.Put1([D.W1{sp, pend}], m), nx, fi, im, OS, Nil{}, fs, f1, sp, Con{sp, ps}),
      _ => D.AccK(True{}, ds, ks, img, D.Put1([D.W1{sp, pend}], m), nx, fi, im, OS, Nil{}, f1, fs, Con{sp, ps}, zs), pp))
  hdec = D.dec.post(f, True{}, ds, ks, img, X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 15n, U32.add(qm.v(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 1)), D.Put1([D.W1{sp, pend}], m), nx, fi, im, pg, lim, inp, 11n, [D.Rt{foc, Bk.Term.Lab{j}}], Nil{}, fs, f1, sp, Con{sp, ps},
    xa, Bk.Term.Lab{i}, Nil{}, zs, hs6, hac6, Unit{}, hl7, X.L.go(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 15n, 11n, U32.add(qm.v(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 1), D.Fd(2n, m, sp), {==}, X.L.go(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, 11n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc), D.Fd(2n, m, sp), {==}, X.L.go(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, 11n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), D.Fd(2n, m, sp), {==}, g11_5))), X.L.go(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 15n, 3n, U32.add(qm.v(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 1), sp, {==}, X.L.go(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, 3n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc), sp, {==}, X.L.go(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, 3n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), sp, {==}, X.L.gs(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp, X.L.lt(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, X.L.len(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp), 63n, X.L.len(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp, 63n, hl4)), {==}))))), {==})
  +B = D.Budget(ds, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t)
  %D.rw.seq(f, X.sel.a(K.stmt.then(X.sel.a(X.sel.b(X.sel.b(K.stmt.then(X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min()))))))))), X.sel.b(K.stmt.then(X.sel.a(X.sel.b(X.sel.b(K.stmt.then(X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min()))))))))), st7, st8, e_n) : D.PostB(False{}, _, s => K.MV.next(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), s => st3 => D.HR(ds, t, s, st3), D.Budget(ds, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)))
  D.postb.seq(f, False{}, X.sel.a(X.sel.b(K.stmt.then(X.sel.a(X.sel.b(X.sel.b(K.stmt.then(X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min())))))))))), X.sel.b(X.sel.b(K.stmt.then(X.sel.a(X.sel.b(X.sel.b(K.stmt.then(X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min())))))))))), st8, st2 => D.Ex(Cr.Cir.Cells, m2 => D.Ex(U32, d => D.Ex(U32, pend2 => D.Ex(List<&2, U32>, ps2 => D.P2({st2 == Cr.Cir.State{List.set(&2, U32, List.set(&2, U32, X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 15n, U32.add(qm.v(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 1)), 5n, d), 3n, pend2), m2, nx, fi, im, pg, lim, inp, Nil{}, 0} : Cr.Cir.State}, D.P2({D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m2, fi) == D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), D.Put1([D.W1{sp, pend}], m), fi) : Nat}, D.P2(D.HSK(True{}, ds, ks, img, m2, nx, fi, im, [D.Rt{foc, Bk.Term.Lab{j}}], Nil{}, fs, D.Fd(1n, m, sp), pend2, ps2), D.Ex(List<&2, D.Rt>, zs2 => D.AccK(True{}, ds, ks, img, m2, nx, fi, im, [D.Rt{foc, Bk.Term.Lab{j}}], Nil{}, D.Fd(1n, m, sp), fs, ps2, zs2))))))))), s => K.MV.next(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), s => st2 => Empty, s => st3 => D.HR(ds, t, s, st3), B, D.St.lim(D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)),
    D.postb.wk(False{}, Cr.Cir.exec(f, X.sel.a(X.sel.b(K.stmt.then(X.sel.a(X.sel.b(X.sel.b(K.stmt.then(X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min())))))))))), st8), st2 => D.Ex(Cr.Cir.Cells, m2 => D.Ex(U32, d => D.Ex(U32, pend2 => D.Ex(List<&2, U32>, ps2 => D.P2({st2 == Cr.Cir.State{List.set(&2, U32, List.set(&2, U32, X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 15n, U32.add(qm.v(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), 1)), 5n, d), 3n, pend2), m2, nx, fi, im, pg, lim, inp, Nil{}, 0} : Cr.Cir.State}, D.P2({D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m2, fi) == D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), D.Put1([D.W1{sp, pend}], m), fi) : Nat}, D.P2(D.HSK(True{}, ds, ks, img, m2, nx, fi, im, [D.Rt{foc, Bk.Term.Lab{j}}], Nil{}, fs, D.Fd(1n, m, sp), pend2, ps2), D.Ex(List<&2, D.Rt>, zs2 => D.AccK(True{}, ds, ks, img, m2, nx, fi, im, [D.Rt{foc, Bk.Term.Lab{j}}], Nil{}, D.Fd(1n, m, sp), fs, ps2, zs2))))))))), s => st2 => Empty, 0n, B, D.St.lim(D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)), hdec, N.le_zero(B)),
    s => st3 => e => Empty.absurd(D.HR(ds, t, s, st3), e),
    s => qd => mn.dec0(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, i, j, b, zs, qi, qj, eP, eK, eri, erj, et, afs, s, qd))

# the machine's test of the names' quantities: it fails when Quan.read
# reads none
def mn.c2(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32,
  +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat,
  +fs: List<&2, D.AF>, +ps: List<&2, U32>, +q: Bk.Quan, +k: Bool, +i: List<&2, Word(8n)>, +j: List<&2, Word(8n)>, +b: Bk.Term, +zs: List<&2, D.Rt>, ri: Maybe<Bk.Quan>, rj: Maybe<Bk.Quan>, +ks2: List<&2, List<&2, Word(8n)>>,
  +eri: {El.Quan.read(i) == ri : Maybe<Bk.Quan>}, +erj: {El.Quan.read(j) == rj : Maybe<Bk.Quan>},
  +eni: {T.tm.name(Mc.Img.known(ks2), D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))) == Some{i} : Maybe<&2, List<&2, Word(8n)>>},
  +enj: {T.tm.name(Mc.Img.known(ks2), D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)) == Some{j} : Maybe<&2, List<&2, Word(8n)>>},
  +eii: {D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)) == Mc.Img.id(Mc.Img.known(ks2), i, 0) : U32}, +eij: {D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc) == Mc.Img.id(Mc.Img.known(ks2), j, 0) : U32},
  +et: {D.A.plugs(Con{D.AF{D.FK.mina{}, q, k, Bk.Term.Lab{i}, b}, fs}, Bk.Term.Lab{j}) == t : Bk.Term}, +afs: D.AFs.ok(ds, Con{D.AF{D.FK.mina{}, q, k, Bk.Term.Lab{i}, b}, fs}), +pp: D.P2(D.HS(ds, ks, img, D.Put1([D.W1{sp, pend}], m), nx, fi, im, Con{D.Rt{foc, Bk.Term.Lab{j}}, Con{D.Rt{D.Fd(2n, m, sp), Bk.Term.Lab{i}}, D.Fr.rts.b(m, sp, D.FK.mina{}, b)}},
      Nil{}, fs, D.Fd(1n, m, sp), sp, Con{sp, ps}),
    D.AccK(True{}, ds, ks, img, D.Put1([D.W1{sp, pend}], m), nx, fi, im, Con{D.Rt{foc, Bk.Term.Lab{j}}, Con{D.Rt{D.Fd(2n, m, sp), Bk.Term.Lab{i}}, D.Fr.rts.b(m, sp, D.FK.mina{}, b)}},
      Nil{}, D.Fd(1n, m, sp), fs, Con{sp, ps}, zs)), +ec2: {Cr.Cir.eval(K.stmt.cond(X.sel.a(X.sel.b(X.sel.b(K.stmt.then(X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min())))))))), X.X.st(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), D.Put1([D.W1{sp, pend}], m), nx, fi, im, pg, lim, inp)) == Some{Bool.to_u32(Bool.and(Bool.and(U32.is_ge(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), 7), U32.is_le(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), 9)), Bool.and(U32.is_ge(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc), 7), U32.is_le(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc), 9))))} : Maybe<&2, U32>}) ->
  D.PostB(False{}, Cr.Cir.exec(f, X.sel.a(X.sel.b(X.sel.b(K.stmt.then(X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min()))))))), X.X.st(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), D.Put1([D.W1{sp, pend}], m), nx, fi, im, pg, lim, inp)), s => K.MV.next(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), s => st3 => D.HR(ds, t, s, st3), D.Budget(ds, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp))):
  match ri:
    case None{}:
      +z = {(%Equal.sym(Bool, Bool.and(U32.is_ge(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), 7), U32.is_le(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), 9)), False{}, quan.no(ks2, i, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), eni, eri)) : {U32.is_zero(Bool.to_u32(Bool.and(_, Bool.and(U32.is_ge(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc), 7), U32.is_le(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc), 9))))) == True{} : Bool}; {==}) :
        {U32.is_zero(Bool.to_u32(Bool.and(Bool.and(U32.is_ge(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), 7), U32.is_le(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), 9)), Bool.and(U32.is_ge(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc), 7), U32.is_le(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc), 9))))) == True{} : Bool}}
      +hm = {(%Equal.sym(Maybe<Bk.Quan>, El.Quan.read(i), None{}, eri) : {El.Eval.meet.of(_, El.Quan.read(j)) == None{} : Maybe<Bk.Term>}; {==}) :
        {El.Eval.meet(Bk.Term.Lab{i}, Bk.Term.Lab{j}) == None{} : Maybe<Bk.Term>}}
      mn.halt(f, ds, t, X.sel.a(X.sel.b(X.sel.b(K.stmt.then(X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min()))))))), X.X.st(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), D.Put1([D.W1{sp, pend}], m), nx, fi, im, pg, lim, inp), s => K.MV.next(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), D.Budget(ds, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)),
        Equal.trans(Cr.Cir.Out, Cr.Cir.exec(f, X.sel.a(X.sel.b(X.sel.b(K.stmt.then(X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min()))))))), X.X.st(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), D.Put1([D.W1{sp, pend}], m), nx, fi, im, pg, lim, inp)), Cr.Cir.exec(f, K.stmt.else(X.sel.a(X.sel.b(X.sel.b(K.stmt.then(X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min())))))))), X.X.st(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), D.Put1([D.W1{sp, pend}], m), nx, fi, im, pg, lim, inp)), Cr.Cir.Out.halt{2, X.X.st(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), D.Put1([D.W1{sp, pend}], m), nx, fi, im, pg, lim, inp)},
        D.eq.if.e(f, K.stmt.cond(X.sel.a(X.sel.b(X.sel.b(K.stmt.then(X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min())))))))), K.stmt.then(X.sel.a(X.sel.b(X.sel.b(K.stmt.then(X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min())))))))), K.stmt.else(X.sel.a(X.sel.b(X.sel.b(K.stmt.then(X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min())))))))), X.X.st(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), D.Put1([D.W1{sp, pend}], m), nx, fi, im, pg, lim, inp), Bool.to_u32(Bool.and(Bool.and(U32.is_ge(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), 7), U32.is_le(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), 9)), Bool.and(U32.is_ge(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc), 7), U32.is_le(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc), 9)))), ec2, z), K.eq.halt(f, 2, X.X.st(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), D.Put1([D.W1{sp, pend}], m), nx, fi, im, pg, lim, inp))),
        mn.stk(ds, fs, q, k, Bk.Term.Lab{i}, b, Bk.Term.Lab{j}, t, et, afs, {==}, hm))
    case Some{+qi}:
      match rj:
        case None{}:
          +z = {(%Equal.sym(Bool, Bool.and(U32.is_ge(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc), 7), U32.is_le(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc), 9)), False{}, quan.no(ks2, j, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc), enj, erj)) : {U32.is_zero(Bool.to_u32(Bool.and(Bool.and(U32.is_ge(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), 7), U32.is_le(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), 9)), _))) == True{} : Bool};
              %Equal.sym(Bool, Bool.and(Bool.and(U32.is_ge(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), 7), U32.is_le(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), 9)), False{}), False{}, and.f(Bool.and(U32.is_ge(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), 7), U32.is_le(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), 9)))) : {U32.is_zero(Bool.to_u32(_)) == True{} : Bool};
              {==}) :
            {U32.is_zero(Bool.to_u32(Bool.and(Bool.and(U32.is_ge(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), 7), U32.is_le(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), 9)), Bool.and(U32.is_ge(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc), 7), U32.is_le(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc), 9))))) == True{} : Bool}}
          +hm = {(%Equal.sym(Maybe<Bk.Quan>, El.Quan.read(i), Some{qi}, eri) : {El.Eval.meet.of(_, El.Quan.read(j)) == None{} : Maybe<Bk.Term>};
              %Equal.sym(Maybe<Bk.Quan>, El.Quan.read(j), None{}, erj) : {El.Eval.meet.of(Some{qi}, _) == None{} : Maybe<Bk.Term>};
              {==}) :
            {El.Eval.meet(Bk.Term.Lab{i}, Bk.Term.Lab{j}) == None{} : Maybe<Bk.Term>}}
          mn.halt(f, ds, t, X.sel.a(X.sel.b(X.sel.b(K.stmt.then(X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min()))))))), X.X.st(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), D.Put1([D.W1{sp, pend}], m), nx, fi, im, pg, lim, inp), s => K.MV.next(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), D.Budget(ds, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)),
            Equal.trans(Cr.Cir.Out, Cr.Cir.exec(f, X.sel.a(X.sel.b(X.sel.b(K.stmt.then(X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min()))))))), X.X.st(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), D.Put1([D.W1{sp, pend}], m), nx, fi, im, pg, lim, inp)), Cr.Cir.exec(f, K.stmt.else(X.sel.a(X.sel.b(X.sel.b(K.stmt.then(X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min())))))))), X.X.st(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), D.Put1([D.W1{sp, pend}], m), nx, fi, im, pg, lim, inp)), Cr.Cir.Out.halt{2, X.X.st(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), D.Put1([D.W1{sp, pend}], m), nx, fi, im, pg, lim, inp)},
        D.eq.if.e(f, K.stmt.cond(X.sel.a(X.sel.b(X.sel.b(K.stmt.then(X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min())))))))), K.stmt.then(X.sel.a(X.sel.b(X.sel.b(K.stmt.then(X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min())))))))), K.stmt.else(X.sel.a(X.sel.b(X.sel.b(K.stmt.then(X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min())))))))), X.X.st(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), D.Put1([D.W1{sp, pend}], m), nx, fi, im, pg, lim, inp), Bool.to_u32(Bool.and(Bool.and(U32.is_ge(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), 7), U32.is_le(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), 9)), Bool.and(U32.is_ge(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc), 7), U32.is_le(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc), 9)))), ec2, z), K.eq.halt(f, 2, X.X.st(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), D.Put1([D.W1{sp, pend}], m), nx, fi, im, pg, lim, inp))),
            mn.stk(ds, fs, q, k, Bk.Term.Lab{i}, b, Bk.Term.Lab{j}, t, et, afs, {==}, hm))
        case Some{+qj}:
          +eri2 = eri
          +erj2 = erj
          +eP = {Equal.trans(U32, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), Mc.Img.id(Mc.Img.known(ks2), i, 0), qid(qi), eii,
              (%Equal.sym(List<&2, Word(8n)>, i, El.Quan.name(qi), read.some(i, qi, eri2)) : {Mc.Img.id(Mc.Img.known(ks2), _, 0) == qid(qi) : U32};
                id.q(ks2, qi))) : {D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)) == qid(qi) : U32}}
          +eK = {Equal.trans(U32, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc), Mc.Img.id(Mc.Img.known(ks2), j, 0), qid(qj), eij,
              (%Equal.sym(List<&2, Word(8n)>, j, El.Quan.name(qj), read.some(j, qj, erj2)) : {Mc.Img.id(Mc.Img.known(ks2), _, 0) == qid(qj) : U32};
                id.q(ks2, qj))) : {D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc) == qid(qj) : U32}}
          +nz = {(%Equal.sym(U32, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), qid(qi), eP) :
                {U32.is_zero(Bool.to_u32(Bool.and(Bool.and(U32.is_ge(_, 7), U32.is_le(_, 9)), Bool.and(U32.is_ge(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc), 7), U32.is_le(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc), 9))))) == False{} : Bool};
              %Equal.sym(U32, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc), qid(qj), eK) :
                {U32.is_zero(Bool.to_u32(Bool.and(Bool.and(U32.is_ge(qid(qi), 7), U32.is_le(qid(qi), 9)), Bool.and(U32.is_ge(_, 7), U32.is_le(_, 9))))) == False{} : Bool};
              qq.q(qi, qj)) :
            {U32.is_zero(Bool.to_u32(Bool.and(Bool.and(U32.is_ge(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), 7), U32.is_le(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), 9)), Bool.and(U32.is_ge(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc), 7), U32.is_le(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc), 9))))) == False{} : Bool}}
          +e_if = D.eq.if.t(f, K.stmt.cond(X.sel.a(X.sel.b(X.sel.b(K.stmt.then(X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min())))))))), K.stmt.then(X.sel.a(X.sel.b(X.sel.b(K.stmt.then(X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min())))))))), K.stmt.else(X.sel.a(X.sel.b(X.sel.b(K.stmt.then(X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min())))))))), X.X.st(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), D.Put1([D.W1{sp, pend}], m), nx, fi, im, pg, lim, inp), Bool.to_u32(Bool.and(Bool.and(U32.is_ge(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), 7), U32.is_le(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), 9)), Bool.and(U32.is_ge(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc), 7), U32.is_le(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc), 9)))), ec2, nz)
          %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, X.sel.a(X.sel.b(X.sel.b(K.stmt.then(X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min()))))))), X.X.st(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), D.Put1([D.W1{sp, pend}], m), nx, fi, im, pg, lim, inp)), Cr.Cir.exec(f, K.stmt.then(X.sel.a(X.sel.b(X.sel.b(K.stmt.then(X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min())))))))), X.X.st(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), D.Put1([D.W1{sp, pend}], m), nx, fi, im, pg, lim, inp)), e_if) : D.PostB(False{}, _, s => K.MV.next(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), s => st3 => D.HR(ds, t, s, st3), D.Budget(ds, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)))
          mn.ok(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, i, j, b, zs, qi, qj, eP, eK, eri2, erj2, et, afs, pp)

# both are labels: registers p and k get their names
def mn.lab(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32,
  +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat,
  +fs: List<&2, D.AF>, +ps: List<&2, U32>, +q: Bk.Quan, +k: Bool, +i: List<&2, Word(8n)>, +j: List<&2, Word(8n)>, +b: Bk.Term, +zs: List<&2, D.Rt>, +et: {D.A.plugs(Con{D.AF{D.FK.mina{}, q, k, Bk.Term.Lab{i}, b}, fs}, Bk.Term.Lab{j}) == t : Bk.Term}, +afs: D.AFs.ok(ds, Con{D.AF{D.FK.mina{}, q, k, Bk.Term.Lab{i}, b}, fs}),
  +pp: D.P2(D.HS(ds, ks, img, D.Put1([D.W1{sp, pend}], m), nx, fi, im, Con{D.Rt{foc, Bk.Term.Lab{j}}, Con{D.Rt{D.Fd(2n, m, sp), Bk.Term.Lab{i}}, D.Fr.rts.b(m, sp, D.FK.mina{}, b)}},
      Nil{}, fs, D.Fd(1n, m, sp), sp, Con{sp, ps}),
    D.AccK(True{}, ds, ks, img, D.Put1([D.W1{sp, pend}], m), nx, fi, im, Con{D.Rt{foc, Bk.Term.Lab{j}}, Con{D.Rt{D.Fd(2n, m, sp), Bk.Term.Lab{i}}, D.Fr.rts.b(m, sp, D.FK.mina{}, b)}},
      Nil{}, D.Fd(1n, m, sp), fs, Con{sp, ps}, zs)), +ec1: {Cr.Cir.eval(K.stmt.cond(X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min())))), X.X.st(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), D.Put1([D.W1{sp, pend}], m), nx, fi, im, pg, lim, inp)) == Some{Bool.to_u32(Bool.and(U32.is_eq(D.A.tag(Bk.Term.Lab{i}), 13), U32.is_eq(D.A.tag(Bk.Term.Lab{j}), 13)))} : Maybe<&2, U32>}) ->
  D.PostB(False{}, Cr.Cir.exec(f, X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min()))), X.X.st(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), D.Put1([D.W1{sp, pend}], m), nx, fi, im, pg, lim, inp)), s => K.MV.next(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), s => st3 => D.HR(ds, t, s, st3), D.Budget(ds, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp))):
  match pp:
    case Tuple{Tuple{Tuple{Tuple{+ndv, Tuple{enj0, eij0}}, Tuple{Tuple{+nda, Tuple{eni0, eii0}}, _}}, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{Tuple{+ks2, +hks}, _}}}}}}}}}}}, _}:
      +RG0 = D.RG(foc, 1, sp, pend, D.R59.list(rest))
      +QQ = U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)
      +xa = D.Fd(2n, m, sp)
      +f1 = D.Fd(1n, m, sp)
      +hl0 = rg.len(rest, foc, 1, sp, pend)
      +hl3 = X.L.len(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3), 63n, X.L.len(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40, 63n, X.L.len(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp, 63n, rg.len(rest, foc, 1, sp, pend))))
      +hl4 = X.L.len(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp), 63n, hl3)
      +hl5 = X.L.len(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp, 63n, X.L.len(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp), 63n, X.L.len(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp, 63n, hl4)))
      +hl6a = X.L.len(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), 63n, hl5)
      +hl6 = X.L.len(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc), 63n, hl6a)
      +eg0 = X.L.go(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, 0n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3), foc, {==}, X.L.go(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 0n, 40, foc, {==}, X.L.go(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, 0n, sp, foc, {==}, {==})))
      +g11_5 = X.L.go(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, 11n, sp, D.Fd(2n, m, sp), {==}, X.L.go(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, 11n, D.Fd(1n, m, sp), D.Fd(2n, m, sp), {==}, X.L.go(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, 11n, sp, D.Fd(2n, m, sp), {==}, X.L.gs(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp), X.L.lt(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, hl3, {==})))))
      +g0_5 = X.L.go(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, 0n, sp, foc, {==}, X.L.go(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, 0n, D.Fd(1n, m, sp), foc, {==}, X.L.go(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, 0n, sp, foc, {==}, X.L.go(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, 0n, D.Fd(2n, m, sp), foc, {==}, eg0))))
      +st5 = X.X.st(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), D.Put1([D.W1{sp, pend}], m), nx, fi, im, pg, lim, inp)
      +st6a = X.X.st(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), D.Put1([D.W1{sp, pend}], m), nx, fi, im, pg, lim, inp)
      +st7 = X.X.st(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), D.Put1([D.W1{sp, pend}], m), nx, fi, im, pg, lim, inp)
      +vx = nd.cell(True{}, ds, im, fi, nx, xa, Cr.Cir.Cells.get(D.Put1([D.W1{sp, pend}], m), xa), Bk.Term.Lab{i}, 13, nda)
      +vf = nd.cell(True{}, ds, im, fi, nx, foc, Cr.Cir.Cells.get(D.Put1([D.W1{sp, pend}], m), foc), Bk.Term.Lab{j}, 13, ndv)
      +e_p = D.eq.set(f, 18n, Mc.M.f(2n, Mc.M.g(Mc.R.x())), st5, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)),
        D.ev.fld(2n, Mc.M.g(Mc.R.x()), X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), D.Put1([D.W1{sp, pend}], m), nx, fi, im, pg, lim, inp, Nil{}, 0, xa, g11_5, vx), X.L.lt(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, hl5, {==}))
      +e_k = D.eq.set(f, 17n, Mc.M.f(2n, Mc.M.g(Mc.R.focus())), st6a, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc),
        D.ev.fld(2n, Mc.M.g(Mc.R.focus()), X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), D.Put1([D.W1{sp, pend}], m), nx, fi, im, pg, lim, inp, Nil{}, 0, foc, X.L.go(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, 0n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), foc, {==}, g0_5), vf), X.L.lt(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, hl6a, {==}))
      +e18 = X.L.go(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc), D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), {==}, X.L.gs(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), X.L.lt(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, hl5, {==})))
      +e17 = X.L.gs(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc), X.L.lt(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, hl6a, {==}))
      +eqp = D.ev.op(Wa.Wasm.Op.and{}, Mc.M.ge(Mc.M.g(Mc.R.p()), Mc.M.c(Mc.N.q0())), Mc.M.le(Mc.M.g(Mc.R.p()), Mc.M.c(Mc.N.q2())), st7,
        Bool.to_u32(U32.is_ge(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), 7)), Bool.to_u32(U32.is_le(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), 9)),
        D.ev.op(Wa.Wasm.Op.ge_u{}, Mc.M.g(Mc.R.p()), Mc.M.c(Mc.N.q0()), st7, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), 7, e18, {==}),
        D.ev.op(Wa.Wasm.Op.le_u{}, Mc.M.g(Mc.R.p()), Mc.M.c(Mc.N.q2()), st7, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), 9, e18, {==}))
      +eqk = D.ev.op(Wa.Wasm.Op.and{}, Mc.M.ge(Mc.M.g(Mc.R.k()), Mc.M.c(Mc.N.q0())), Mc.M.le(Mc.M.g(Mc.R.k()), Mc.M.c(Mc.N.q2())), st7,
        Bool.to_u32(U32.is_ge(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc), 7)), Bool.to_u32(U32.is_le(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc), 9)),
        D.ev.op(Wa.Wasm.Op.ge_u{}, Mc.M.g(Mc.R.k()), Mc.M.c(Mc.N.q0()), st7, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc), 7, e17, {==}),
        D.ev.op(Wa.Wasm.Op.le_u{}, Mc.M.g(Mc.R.k()), Mc.M.c(Mc.N.q2()), st7, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc), 9, e17, {==}))
      +ec2 = {(%and4(U32.is_ge(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), 7), U32.is_le(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), 9), U32.is_ge(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc), 7), U32.is_le(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc), 9)) :
          {Cr.Cir.eval(K.stmt.cond(X.sel.a(X.sel.b(X.sel.b(K.stmt.then(X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min())))))))), st7) == Some{_} : Maybe<&2, U32>};
        D.ev.op(Wa.Wasm.Op.and{}, Mc.M.quan(Mc.M.g(Mc.R.p())), Mc.M.quan(Mc.M.g(Mc.R.k())), st7,
          U32.and(Bool.to_u32(U32.is_ge(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), 7)), Bool.to_u32(U32.is_le(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), 9))),
          U32.and(Bool.to_u32(U32.is_ge(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc), 7)), Bool.to_u32(U32.is_le(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc), 9))), eqp, eqk)) : {Cr.Cir.eval(K.stmt.cond(X.sel.a(X.sel.b(X.sel.b(K.stmt.then(X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min())))))))), X.X.st(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)), D.Put1([D.W1{sp, pend}], m), nx, fi, im, pg, lim, inp)) == Some{Bool.to_u32(Bool.and(Bool.and(U32.is_ge(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), 7), U32.is_le(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), 9)), Bool.and(U32.is_ge(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc), 7), U32.is_le(D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc), 9))))} : Maybe<&2, U32>}}
      +eni = {(%hks : {T.tm.name(_, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))) == Some{i} : Maybe<&2, List<&2, Word(8n)>>}; eni0) :
        {T.tm.name(Mc.Img.known(ks2), D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))) == Some{i} : Maybe<&2, List<&2, Word(8n)>>}}
      +enj = {(%hks : {T.tm.name(_, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)) == Some{j} : Maybe<&2, List<&2, Word(8n)>>}; enj0) :
        {T.tm.name(Mc.Img.known(ks2), D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc)) == Some{j} : Maybe<&2, List<&2, Word(8n)>>}}
      +eii = {(%hks : {D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)) == Mc.Img.id(_, i, 0) : U32}; eii0) : {D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)) == Mc.Img.id(Mc.Img.known(ks2), i, 0) : U32}}
      +eij = {(%hks : {D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc) == Mc.Img.id(_, j, 0) : U32}; eij0) : {D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc) == Mc.Img.id(Mc.Img.known(ks2), j, 0) : U32}}
      +e_if = D.eq.if.t(f, K.stmt.cond(X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min())))), K.stmt.then(X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min())))), K.stmt.else(X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min())))), st5, Bool.to_u32(Bool.and(U32.is_eq(D.A.tag(Bk.Term.Lab{i}), 13), U32.is_eq(D.A.tag(Bk.Term.Lab{j}), 13))), ec1, {==})
      %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min()))), st5), Cr.Cir.exec(f, K.stmt.then(X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min())))), st5), e_if) : D.PostB(False{}, _, s => K.MV.next(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), s => st3 => D.HR(ds, t, s, st3), D.Budget(ds, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)))
      %D.rw.seq(f, X.sel.a(K.stmt.then(X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min()))))), X.sel.b(K.stmt.then(X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min()))))), st5, st6a, e_p) : D.PostB(False{}, _, s => K.MV.next(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), s => st3 => D.HR(ds, t, s, st3), D.Budget(ds, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)))
      %D.rw.seq(f, X.sel.a(X.sel.b(K.stmt.then(X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min())))))), X.sel.b(X.sel.b(K.stmt.then(X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min())))))), st6a, st7, e_k) : D.PostB(False{}, _, s => K.MV.next(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), s => st3 => D.HR(ds, t, s, st3), D.Budget(ds, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)))
      pb.nop(f, X.sel.a(X.sel.b(X.sel.b(K.stmt.then(X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min()))))))), st7, s => K.MV.next(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), s => st3 => D.HR(ds, t, s, st3), D.Budget(ds, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)),
        mn.c2(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, i, j, b, zs, El.Quan.read(i), El.Quan.read(j), ks2, {==}, {==}, eni, enj, eii, eij, et, afs, pp, ec2))

# a or v is no label: the round halts with 2, as Min a v is stuck
def mn.no1(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32,
  +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat,
  +fs: List<&2, D.AF>, +ps: List<&2, U32>, +q: Bk.Quan, +k: Bool, +a: Bk.Term, +b: Bk.Term, +zs: List<&2, D.Rt>, +v: Bk.Term, +et: {D.A.plugs(Con{D.AF{D.FK.mina{}, q, k, a, b}, fs}, v) == t : Bk.Term}, +evv: {Bool.or(Bool.not(True{}), El.Eval.vals(ds, v, False{})) == True{} : Bool},
  +afs: D.AFs.ok(ds, Con{D.AF{D.FK.mina{}, q, k, a, b}, fs}), ec1: {Cr.Cir.eval(K.stmt.cond(X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min())))), X.X.st(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), D.Put1([D.W1{sp, pend}], m), nx, fi, im, pg, lim, inp)) == Some{Bool.to_u32(Bool.and(U32.is_eq(D.A.tag(a), 13), U32.is_eq(D.A.tag(v), 13)))} : Maybe<&2, U32>}, z: {U32.is_zero(Bool.to_u32(Bool.and(U32.is_eq(D.A.tag(a), 13), U32.is_eq(D.A.tag(v), 13)))) == True{} : Bool},
  hm: {El.Eval.meet(a, v) == None{} : Maybe<Bk.Term>}) ->
  D.PostB(False{}, Cr.Cir.exec(f, X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min()))), X.X.st(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), D.Put1([D.W1{sp, pend}], m), nx, fi, im, pg, lim, inp)), s => K.MV.next(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), s => st3 => D.HR(ds, t, s, st3), D.Budget(ds, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp))):
  mn.halt(f, ds, t, X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min()))), X.X.st(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), D.Put1([D.W1{sp, pend}], m), nx, fi, im, pg, lim, inp), s => K.MV.next(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), D.Budget(ds, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)),
    Equal.trans(Cr.Cir.Out, Cr.Cir.exec(f, X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min()))), X.X.st(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), D.Put1([D.W1{sp, pend}], m), nx, fi, im, pg, lim, inp)), Cr.Cir.exec(f, K.stmt.else(X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min())))), X.X.st(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), D.Put1([D.W1{sp, pend}], m), nx, fi, im, pg, lim, inp)), Cr.Cir.Out.halt{2, X.X.st(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), D.Put1([D.W1{sp, pend}], m), nx, fi, im, pg, lim, inp)},
      D.eq.if.e(f, K.stmt.cond(X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min())))), K.stmt.then(X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min())))), K.stmt.else(X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min())))), X.X.st(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), D.Put1([D.W1{sp, pend}], m), nx, fi, im, pg, lim, inp), Bool.to_u32(Bool.and(U32.is_eq(D.A.tag(a), 13), U32.is_eq(D.A.tag(v), 13))), ec1, z), K.eq.halt(f, 2, X.X.st(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), D.Put1([D.W1{sp, pend}], m), nx, fi, im, pg, lim, inp))),
    mn.stk(ds, fs, q, k, a, b, v, t, et, afs, evv, hm))

# the label test on a and v, by their forms
def mn.split(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32,
  +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat,
  +fs: List<&2, D.AF>, +ps: List<&2, U32>, +q: Bk.Quan, +k: Bool, +a: Bk.Term, +b: Bk.Term, +zs: List<&2, D.Rt>, v: Bk.Term, +et: {D.A.plugs(Con{D.AF{D.FK.mina{}, q, k, a, b}, fs}, v) == t : Bk.Term}, +evv: {Bool.or(Bool.not(True{}), El.Eval.vals(ds, v, False{})) == True{} : Bool},
  +afs: D.AFs.ok(ds, Con{D.AF{D.FK.mina{}, q, k, a, b}, fs}), +pp: D.P2(D.HS(ds, ks, img, D.Put1([D.W1{sp, pend}], m), nx, fi, im, Con{D.Rt{foc, v}, Con{D.Rt{D.Fd(2n, m, sp), a}, D.Fr.rts.b(m, sp, D.FK.mina{}, b)}},
      Nil{}, fs, D.Fd(1n, m, sp), sp, Con{sp, ps}),
    D.AccK(True{}, ds, ks, img, D.Put1([D.W1{sp, pend}], m), nx, fi, im, Con{D.Rt{foc, v}, Con{D.Rt{D.Fd(2n, m, sp), a}, D.Fr.rts.b(m, sp, D.FK.mina{}, b)}},
      Nil{}, D.Fd(1n, m, sp), fs, Con{sp, ps}, zs)), ec1: {Cr.Cir.eval(K.stmt.cond(X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min())))), X.X.st(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), D.Put1([D.W1{sp, pend}], m), nx, fi, im, pg, lim, inp)) == Some{Bool.to_u32(Bool.and(U32.is_eq(D.A.tag(a), 13), U32.is_eq(D.A.tag(v), 13)))} : Maybe<&2, U32>}) ->
  D.PostB(False{}, Cr.Cir.exec(f, X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min()))), X.X.st(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), D.Put1([D.W1{sp, pend}], m), nx, fi, im, pg, lim, inp)), s => K.MV.next(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), s => st3 => D.HR(ds, t, s, st3), D.Budget(ds, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp))):
  match a:
    case Bk.Term.Var{+ax0}:
      mn.no1(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, Bk.Term.Var{ax0}, b, zs, v, et, evv, afs, ec1, {==}, {==})
    case Bk.Term.Ref{+ax0}:
      mn.no1(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, Bk.Term.Ref{ax0}, b, zs, v, et, evv, afs, ec1, {==}, {==})
    case Bk.Term.Ann{+ax0, +ax1}:
      mn.no1(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, Bk.Term.Ann{ax0, ax1}, b, zs, v, et, evv, afs, ec1, {==}, {==})
    case Bk.Term.Let{+ax0, +ax1, +ax2}:
      mn.no1(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, Bk.Term.Let{ax0, ax1, ax2}, b, zs, v, et, evv, afs, ec1, {==}, {==})
    case Bk.Term.Typ{+ax0}:
      mn.no1(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, Bk.Term.Typ{ax0}, b, zs, v, et, evv, afs, ec1, {==}, {==})
    case Bk.Term.Min{+ax0, +ax1}:
      mn.no1(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, Bk.Term.Min{ax0, ax1}, b, zs, v, et, evv, afs, ec1, {==}, {==})
    case Bk.Term.All{+ax0, +ax1, +ax2}:
      mn.no1(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, Bk.Term.All{ax0, ax1, ax2}, b, zs, v, et, evv, afs, ec1, {==}, {==})
    case Bk.Term.Lam{+ax0, +ax1}:
      mn.no1(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, Bk.Term.Lam{ax0, ax1}, b, zs, v, et, evv, afs, ec1, {==}, {==})
    case Bk.Term.App{+ax0, +ax1, +ax2}:
      mn.no1(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, Bk.Term.App{ax0, ax1, ax2}, b, zs, v, et, evv, afs, ec1, {==}, {==})
    case Bk.Term.Sig{+ax0, +ax1, +ax2}:
      mn.no1(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, Bk.Term.Sig{ax0, ax1, ax2}, b, zs, v, et, evv, afs, ec1, {==}, {==})
    case Bk.Term.Tup{+ax0, +ax1, +ax2}:
      mn.no1(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, Bk.Term.Tup{ax0, ax1, ax2}, b, zs, v, et, evv, afs, ec1, {==}, {==})
    case Bk.Term.Prj{+ax0}:
      mn.no1(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, Bk.Term.Prj{ax0}, b, zs, v, et, evv, afs, ec1, {==}, {==})
    case Bk.Term.Enu{+ax0}:
      mn.no1(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, Bk.Term.Enu{ax0}, b, zs, v, et, evv, afs, ec1, {==}, {==})
    case Bk.Term.Lab{+ax0}:
      match v:
        case Bk.Term.Var{+vx0}:
          mn.no1(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, Bk.Term.Lab{ax0}, b, zs, Bk.Term.Var{vx0}, et, evv, afs, ec1, {==}, {==})
        case Bk.Term.Ref{+vx0}:
          mn.no1(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, Bk.Term.Lab{ax0}, b, zs, Bk.Term.Ref{vx0}, et, evv, afs, ec1, {==}, {==})
        case Bk.Term.Ann{+vx0, +vx1}:
          mn.no1(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, Bk.Term.Lab{ax0}, b, zs, Bk.Term.Ann{vx0, vx1}, et, evv, afs, ec1, {==}, {==})
        case Bk.Term.Let{+vx0, +vx1, +vx2}:
          mn.no1(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, Bk.Term.Lab{ax0}, b, zs, Bk.Term.Let{vx0, vx1, vx2}, et, evv, afs, ec1, {==}, {==})
        case Bk.Term.Typ{+vx0}:
          mn.no1(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, Bk.Term.Lab{ax0}, b, zs, Bk.Term.Typ{vx0}, et, evv, afs, ec1, {==}, {==})
        case Bk.Term.Min{+vx0, +vx1}:
          mn.no1(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, Bk.Term.Lab{ax0}, b, zs, Bk.Term.Min{vx0, vx1}, et, evv, afs, ec1, {==}, {==})
        case Bk.Term.All{+vx0, +vx1, +vx2}:
          mn.no1(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, Bk.Term.Lab{ax0}, b, zs, Bk.Term.All{vx0, vx1, vx2}, et, evv, afs, ec1, {==}, {==})
        case Bk.Term.Lam{+vx0, +vx1}:
          mn.no1(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, Bk.Term.Lab{ax0}, b, zs, Bk.Term.Lam{vx0, vx1}, et, evv, afs, ec1, {==}, {==})
        case Bk.Term.App{+vx0, +vx1, +vx2}:
          mn.no1(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, Bk.Term.Lab{ax0}, b, zs, Bk.Term.App{vx0, vx1, vx2}, et, evv, afs, ec1, {==}, {==})
        case Bk.Term.Sig{+vx0, +vx1, +vx2}:
          mn.no1(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, Bk.Term.Lab{ax0}, b, zs, Bk.Term.Sig{vx0, vx1, vx2}, et, evv, afs, ec1, {==}, {==})
        case Bk.Term.Tup{+vx0, +vx1, +vx2}:
          mn.no1(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, Bk.Term.Lab{ax0}, b, zs, Bk.Term.Tup{vx0, vx1, vx2}, et, evv, afs, ec1, {==}, {==})
        case Bk.Term.Prj{+vx0}:
          mn.no1(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, Bk.Term.Lab{ax0}, b, zs, Bk.Term.Prj{vx0}, et, evv, afs, ec1, {==}, {==})
        case Bk.Term.Enu{+vx0}:
          mn.no1(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, Bk.Term.Lab{ax0}, b, zs, Bk.Term.Enu{vx0}, et, evv, afs, ec1, {==}, {==})
        case Bk.Term.Lab{+vx0}:
          mn.lab(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, ax0, vx0, b, zs, et, afs, pp, ec1)
        case Bk.Term.Mat{+vx0, +vx1, +vx2}:
          mn.no1(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, Bk.Term.Lab{ax0}, b, zs, Bk.Term.Mat{vx0, vx1, vx2}, et, evv, afs, ec1, {==}, {==})
        case Bk.Term.Efq{}:
          mn.no1(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, Bk.Term.Lab{ax0}, b, zs, Bk.Term.Efq{}, et, evv, afs, ec1, {==}, {==})
        case Bk.Term.Eql{+vx0, +vx1, +vx2}:
          mn.no1(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, Bk.Term.Lab{ax0}, b, zs, Bk.Term.Eql{vx0, vx1, vx2}, et, evv, afs, ec1, {==}, {==})
        case Bk.Term.Rfl{}:
          mn.no1(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, Bk.Term.Lab{ax0}, b, zs, Bk.Term.Rfl{}, et, evv, afs, ec1, {==}, {==})
        case Bk.Term.Rwt{+vx0, +vx1, +vx2}:
          mn.no1(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, Bk.Term.Lab{ax0}, b, zs, Bk.Term.Rwt{vx0, vx1, vx2}, et, evv, afs, ec1, {==}, {==})
    case Bk.Term.Mat{+ax0, +ax1, +ax2}:
      mn.no1(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, Bk.Term.Mat{ax0, ax1, ax2}, b, zs, v, et, evv, afs, ec1, {==}, {==})
    case Bk.Term.Efq{}:
      mn.no1(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, Bk.Term.Efq{}, b, zs, v, et, evv, afs, ec1, {==}, {==})
    case Bk.Term.Eql{+ax0, +ax1, +ax2}:
      mn.no1(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, Bk.Term.Eql{ax0, ax1, ax2}, b, zs, v, et, evv, afs, ec1, {==}, {==})
    case Bk.Term.Rfl{}:
      mn.no1(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, Bk.Term.Rfl{}, b, zs, v, et, evv, afs, ec1, {==}, {==})
    case Bk.Term.Rwt{+ax0, +ax1, +ax2}:
      mn.no1(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, Bk.Term.Rwt{ax0, ax1, ax2}, b, zs, v, et, evv, afs, ec1, {==}, {==})

# after the pop: the label test's value, from the cells of a and v
def mn.if1(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32,
  +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat,
  +fs: List<&2, D.AF>, +ps: List<&2, U32>, +q: Bk.Quan, +k: Bool, +a: Bk.Term, +b: Bk.Term, +zs: List<&2, D.Rt>, +v: Bk.Term, +et: {D.A.plugs(Con{D.AF{D.FK.mina{}, q, k, a, b}, fs}, v) == t : Bk.Term}, +evv: {Bool.or(Bool.not(True{}), El.Eval.vals(ds, v, False{})) == True{} : Bool},
  +afs: D.AFs.ok(ds, Con{D.AF{D.FK.mina{}, q, k, a, b}, fs}), +pp: D.P2(D.HS(ds, ks, img, D.Put1([D.W1{sp, pend}], m), nx, fi, im, Con{D.Rt{foc, v}, Con{D.Rt{D.Fd(2n, m, sp), a}, D.Fr.rts.b(m, sp, D.FK.mina{}, b)}},
      Nil{}, fs, D.Fd(1n, m, sp), sp, Con{sp, ps}),
    D.AccK(True{}, ds, ks, img, D.Put1([D.W1{sp, pend}], m), nx, fi, im, Con{D.Rt{foc, v}, Con{D.Rt{D.Fd(2n, m, sp), a}, D.Fr.rts.b(m, sp, D.FK.mina{}, b)}},
      Nil{}, D.Fd(1n, m, sp), fs, Con{sp, ps}, zs))) ->
  D.PostB(False{}, Cr.Cir.exec(f, X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min()))), X.X.st(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), D.Put1([D.W1{sp, pend}], m), nx, fi, im, pg, lim, inp)), s => K.MV.next(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), s => st3 => D.HR(ds, t, s, st3), D.Budget(ds, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp))):
  match pp:
    case Tuple{Tuple{Tuple{+isv, Tuple{+isa, _}}, _}, _}:
      +RG0 = D.RG(foc, 1, sp, pend, D.R59.list(rest))
      +QQ = U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)
      +xa = D.Fd(2n, m, sp)
      +f1 = D.Fd(1n, m, sp)
      +hl0 = rg.len(rest, foc, 1, sp, pend)
      +hl3 = X.L.len(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3), 63n, X.L.len(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40, 63n, X.L.len(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp, 63n, rg.len(rest, foc, 1, sp, pend))))
      +hl4 = X.L.len(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp), 63n, hl3)
      +hl5 = X.L.len(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp, 63n, X.L.len(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp), 63n, X.L.len(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp, 63n, hl4)))
      +hl6a = X.L.len(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), 63n, hl5)
      +hl6 = X.L.len(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc), 63n, hl6a)
      +eg0 = X.L.go(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, 0n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3), foc, {==}, X.L.go(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 0n, 40, foc, {==}, X.L.go(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, 0n, sp, foc, {==}, {==})))
      +g11_5 = X.L.go(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, 11n, sp, D.Fd(2n, m, sp), {==}, X.L.go(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, 11n, D.Fd(1n, m, sp), D.Fd(2n, m, sp), {==}, X.L.go(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, 11n, sp, D.Fd(2n, m, sp), {==}, X.L.gs(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp), X.L.lt(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, hl3, {==})))))
      +g0_5 = X.L.go(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, 0n, sp, foc, {==}, X.L.go(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, 0n, D.Fd(1n, m, sp), foc, {==}, X.L.go(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, 0n, sp, foc, {==}, X.L.go(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, 0n, D.Fd(2n, m, sp), foc, {==}, eg0))))
      +st5 = X.X.st(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), D.Put1([D.W1{sp, pend}], m), nx, fi, im, pg, lim, inp)
      +nda = D.is.nd(ds, D.Put1([D.W1{sp, pend}], m), im, fi, nx, ks, img, xa, a, isa)
      +ndv = D.is.nd(ds, D.Put1([D.W1{sp, pend}], m), im, fi, nx, ks, img, foc, v, isv)
      +F0x = D.Fd(0n, D.Put1([D.W1{sp, pend}], m), xa)
      +F0f = D.Fd(0n, D.Put1([D.W1{sp, pend}], m), foc)
      +etx = nd.tag(ds, im, fi, nx, xa, Cr.Cir.Cells.get(D.Put1([D.W1{sp, pend}], m), xa), a, D.A.tag(a), nda)
      +etf = nd.tag(ds, im, fi, nx, foc, Cr.Cir.Cells.get(D.Put1([D.W1{sp, pend}], m), foc), v, D.A.tag(v), ndv)
      +vx = nd.cell(True{}, ds, im, fi, nx, xa, Cr.Cir.Cells.get(D.Put1([D.W1{sp, pend}], m), xa), a, D.A.tag(a), nda)
      +vf = nd.cell(True{}, ds, im, fi, nx, foc, Cr.Cir.Cells.get(D.Put1([D.W1{sp, pend}], m), foc), v, D.A.tag(v), ndv)
      +eqx = D.ev.op(Wa.Wasm.Op.eq{}, Mc.M.tag(Mc.M.g(Mc.R.x())), Mc.M.c(Mc.T.lab()), st5, Wa.Wasm.op(Wa.Wasm.Op.and{}, F0x, 63), 13,
        D.ev.op(Wa.Wasm.Op.and{}, Mc.M.f(0n, Mc.M.g(Mc.R.x())), Mc.M.c(63), st5, F0x, 63,
          D.ev.fld(0n, Mc.M.g(Mc.R.x()), X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), D.Put1([D.W1{sp, pend}], m), nx, fi, im, pg, lim, inp, Nil{}, 0, xa, g11_5, vx), {==}), {==})
      +eqf = D.ev.op(Wa.Wasm.Op.eq{}, Mc.M.tag(Mc.M.g(Mc.R.focus())), Mc.M.c(Mc.T.lab()), st5, Wa.Wasm.op(Wa.Wasm.Op.and{}, F0f, 63), 13,
        D.ev.op(Wa.Wasm.Op.and{}, Mc.M.f(0n, Mc.M.g(Mc.R.focus())), Mc.M.c(63), st5, F0f, 63,
          D.ev.fld(0n, Mc.M.g(Mc.R.focus()), X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), D.Put1([D.W1{sp, pend}], m), nx, fi, im, pg, lim, inp, Nil{}, 0, foc, g0_5, vf), {==}), {==})
      +ec1 = {(%etx : {Cr.Cir.eval(K.stmt.cond(X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min())))), st5) == Some{Bool.to_u32(Bool.and(U32.is_eq(_, 13), U32.is_eq(D.A.tag(v), 13)))} : Maybe<&2, U32>};
          %etf : {Cr.Cir.eval(K.stmt.cond(X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min())))), st5) == Some{Bool.to_u32(Bool.and(U32.is_eq(D.TgW(F0x), 13), U32.is_eq(_, 13)))} : Maybe<&2, U32>};
          %and.u32(U32.is_eq(D.TgW(F0x), 13), U32.is_eq(D.TgW(F0f), 13)) : {Cr.Cir.eval(K.stmt.cond(X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min())))), st5) == Some{_} : Maybe<&2, U32>};
          D.ev.op(Wa.Wasm.Op.and{}, Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.x())), Mc.M.c(Mc.T.lab())), Mc.M.eq(Mc.M.tag(Mc.M.g(Mc.R.focus())), Mc.M.c(Mc.T.lab())), st5,
            Wa.Wasm.op(Wa.Wasm.Op.eq{}, Wa.Wasm.op(Wa.Wasm.Op.and{}, F0x, 63), 13), Wa.Wasm.op(Wa.Wasm.Op.eq{}, Wa.Wasm.op(Wa.Wasm.Op.and{}, F0f, 63), 13), eqx, eqf)) :
        {Cr.Cir.eval(K.stmt.cond(X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min())))), X.X.st(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), D.Put1([D.W1{sp, pend}], m), nx, fi, im, pg, lim, inp)) == Some{Bool.to_u32(Bool.and(U32.is_eq(D.A.tag(a), 13), U32.is_eq(D.A.tag(v), 13)))} : Maybe<&2, U32>}}
      mn.split(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, a, b, zs, v, et, evv, afs, pp, ec1)

# the round from a Min a □ frame, for any fuel: M.ret.min's first two
# statements, then the label test
def mn.round(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32,
  +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat,
  +fs: List<&2, D.AF>, +ps: List<&2, U32>, +q: Bk.Quan, +k: Bool, +a: Bk.Term, +b: Bk.Term, +zs: List<&2, D.Rt>, +v: Bk.Term,
  +iv: D.InvOf(ds, ks, img, D.RG(foc, 1, sp, pend, D.R59.list(rest)), m, nx, fi, im, Nil{}, 0, t, w, True{}, v, Con{D.AF{D.FK.mina{}, q, k, a, b}, fs}, foc, sp, pend, ps, rest),
  hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, [D.Rt{foc, v}], Nil{}, sp, Con{D.AF{D.FK.mina{}, q, k, a, b}, fs}, ps, zs)) ->
  D.PostB(False{}, Cr.Cir.exec(f, D.B.body(), D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)), s => K.MV.next(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), s => st3 => D.HR(ds, t, s, st3), D.Budget(ds, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp))):
  match iv:
    case Tuple{+et, Tuple{_, Tuple{+evv, Tuple{+afs, Tuple{_, Tuple{+isf, Tuple{+frs, Tuple{+hp, Tuple{+io, _}}}}}}}}}:
      +KD = {D.FK.mina{} : D.FK}
      +hz = fr.nz(ds, m, im, fi, nx, ks, img, ps, sp, KD, q, k, a, b, fs, frs)
      +hc = fr.cell(ds, m, im, fi, nx, ks, img, ps, sp, KD, q, k, a, b, fs, frs)
      +ht = fr.tag(ds, m, im, fi, nx, ks, img, ps, sp, KD, q, k, a, b, fs, frs)
      +RG0 = D.RG(foc, 1, sp, pend, D.R59.list(rest))
      +QQ = U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)
      +xa = D.Fd(2n, m, sp)
      +f1 = D.Fd(1n, m, sp)
      +hl0 = rg.len(rest, foc, 1, sp, pend)
      +hl3 = X.L.len(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3), 63n, X.L.len(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40, 63n, X.L.len(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp, 63n, rg.len(rest, foc, 1, sp, pend))))
      +hl4 = X.L.len(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp), 63n, hl3)
      +hl5 = X.L.len(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp, 63n, X.L.len(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp), 63n, X.L.len(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp, 63n, hl4)))
      +hl6a = X.L.len(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp)), 63n, hl5)
      +hl6 = X.L.len(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), 18n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), D.Fd(2n, m, sp))), 17n, D.Fd(2n, D.Put1([D.W1{sp, pend}], m), foc), 63n, hl6a)
      +eg9 = X.L.go(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, 9n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3), sp, {==}, X.L.go(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 9n, 40, sp, {==}, X.L.gs(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp, X.L.lt(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, hl0, {==}))))
      +S0 = D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)
      +st3 = X.X.st(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), m, nx, fi, im, pg, lim, inp)
      +st4 = X.X.st(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), m, nx, fi, im, pg, lim, inp)
      +st5 = X.X.st(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), 16n, sp), 2n, D.Fd(1n, m, sp)), 3n, sp), D.Put1([D.W1{sp, pend}], m), nx, fi, im, pg, lim, inp)
      +e_x = D.eq.set(f, 11n, Mc.M.f(2n, Mc.M.g(Mc.R.h())), st3, xa, D.ev.fld(2n, Mc.M.g(Mc.R.h()), X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), m, nx, fi, im, pg, lim, inp, Nil{}, 0, sp, eg9, hc),
        X.L.lt(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, hl3, {==}))
      +e_pop = X.pop.eq(f, X.X.set(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, D.Fd(2n, m, sp)), m, nx, fi, im, pg, lim, inp, sp, pend, hl4, X.L.go(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, 2n, D.Fd(2n, m, sp), sp, {==}, X.L.go(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, 2n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3), sp, {==}, X.L.go(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 2n, 40, sp, {==}, X.L.go(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, 2n, sp, sp, {==}, {==})))), X.L.go(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), 11n, 3n, D.Fd(2n, m, sp), pend, {==}, X.L.go(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, 3n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3), pend, {==}, X.L.go(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 3n, 40, pend, {==}, X.L.go(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, 3n, sp, pend, {==}, {==})))), hc)
      +pp = pop.post(ds, ks, img, m, nx, fi, im, v, fs, foc, sp, pend, ps, KD, q, k, a, b, zs, isf, hp, io, frs, hac)
      %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, D.B.body(), S0), Cr.Cir.exec(f, Mc.M.ret.min(), st3), mina.E(f, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, hz, hc, ht)) :
        D.PostB(False{}, _, s => K.MV.next(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), s => st3 => D.HR(ds, t, s, st3), D.Budget(ds, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)))
      %D.rw.seq(f, X.sel.a(Mc.M.ret.min()), X.sel.b(Mc.M.ret.min()), st3, st4, e_x) : D.PostB(False{}, _, s => K.MV.next(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), s => st3 => D.HR(ds, t, s, st3), D.Budget(ds, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)))
      %D.rw.seq(f, X.sel.a(X.sel.b(Mc.M.ret.min())), X.sel.b(X.sel.b(Mc.M.ret.min())), st4, st5, e_pop) : D.PostB(False{}, _, s => K.MV.next(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), s => st3 => D.HR(ds, t, s, st3), D.Budget(ds, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)))
      pb.nop(f, X.sel.a(X.sel.b(X.sel.b(Mc.M.ret.min()))), st5, s => K.MV.next(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w, s), s => st3 => D.HR(ds, t, s, st3), D.Budget(ds, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)), mn.if1(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, a, b, zs, v, et, evv, afs, pp))

# mode 1, Min a □, with the value v: a step to the meet when both are labels
# of quantities; else halt 2
def mn.go(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32,
  +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat,
  +fs: List<&2, D.AF>, +ps: List<&2, U32>, +q: Bk.Quan, +k: Bool, +a: Bk.Term, +b: Bk.Term, +zs: List<&2, D.Rt>, +v: Bk.Term,
  +iv: D.InvOf(ds, ks, img, D.RG(foc, 1, sp, pend, D.R59.list(rest)), m, nx, fi, im, Nil{}, 0, t, w, True{}, v, Con{D.AF{D.FK.mina{}, q, k, a, b}, fs}, foc, sp, pend, ps, rest),
  +hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, [D.Rt{foc, v}], Nil{}, sp, Con{D.AF{D.FK.mina{}, q, k, a, b}, fs}, ps, zs)) ->
  K.MV(ds, ks, img, D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp), t, w):
  match iv:
    case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{+frs, _}}}}}}}:
      +KD = {D.FK.mina{} : D.FK}
      +hz = fr.nz(ds, m, im, fi, nx, ks, img, ps, sp, KD, q, k, a, b, fs, frs)
      +hc = fr.cell(ds, m, im, fi, nx, ks, img, ps, sp, KD, q, k, a, b, fs, frs)
      +ht = fr.tag(ds, m, im, fi, nx, ks, img, ps, sp, KD, q, k, a, b, fs, frs)
      +st3 = X.X.st(X.X.set(X.X.set(X.X.set(D.RG(foc, 1, sp, pend, D.R59.list(rest)), 9n, sp), 10n, 40), 14n, U32.and(U32.shrn(D.Fd(0n, m, sp), 6n), 3)), m, nx, fi, im, pg, lim, inp)
      (f => mn.round(f, ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, a, b, zs, v, iv, hac),
        (0n, (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec(0n, D.B.body(), D.S(foc, 1, sp, pend, rest, m, nx, fi, im, pg, lim, inp)), Cr.Cir.exec(0n, Mc.M.ret.min(), st3),
            mina.E(0n, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, hz, hc, ht)) : D.Ends(_);
          ends.plain(Mc.M.ret.min(), st3, plain.min()))))

# The moves of move_kit.bend that this file proves (U11; U0 left them as ?TODO)
# --------------------------------------------------------------------------

def K.mv.ev.ann(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, x, y, iv, hv):
  match iv:
    case Tuple{io, Tuple{zs, hac}}:
      ann.go(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, x, y, zs, io, hv, hac)

def K.mv.ret.swap(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, focus, kind, q, k, a, b, iv, hk, hs):
  match iv:
    case Tuple{io, Tuple{zs, hac}}:
      sw.app.mv(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, focus, kind, q, k, a, b, io, hk, hs, zs, hac)

def K.mv.ret.tupb(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, focus, q, k, a, b, iv):
  match iv:
    case Tuple{io, Tuple{zs, hac}}:
      sw.tupb.mv(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, focus, q, k, a, b, io, zs, hac)

def K.mv.ret.tupa(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, focus, q, k, a, b, iv):
  ?TODO

def K.mv.ret.rwt(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, focus, q, k, a, b, iv):
  match iv:
    case Tuple{io, Tuple{zs, hac}}:
      rwt.go(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, a, b, zs, focus, io, hac)

def K.mv.ret.minb(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, focus, q, k, a, b, iv):
  match iv:
    case Tuple{io, Tuple{zs, hac}}:
      sw.minb.go(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, focus, q, k, a, b, io, zs, hac)

def K.mv.ret.mina(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, focus, q, k, a, b, iv):
  match iv:
    case Tuple{io, Tuple{zs, hac}}:
      mn.go(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, k, a, b, zs, focus, io, hac)
