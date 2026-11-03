# compiler: layer B, the moves that push a frame, and the moves to mode 1 (U10)
# =============================================================================
#
# mv.ev.val, mv.ev.former, mv.ev.var (mode 1, or a halt), and mv.ev.app, mv.ev.let, mv.ev.tup,
# mv.ev.tup0, mv.ev.rwt, mv.ev.min (a frame pushed, an admin move) of move_kit.bend.

import Base
import ../../Book/impl.bend as Bk
import ../../Eval/impl.bend as El
import ../../Wasm/impl.bend as Wa
import ../../Program/impl.bend as Pg
import ../Cir/impl.bend as Cr
import ./impl.bend as Mc
import ../need_big.bend as N
import ./definitions.bend as D
import ./statement_runs.bend as X
import ./accounting.bend as A
import ./heap_ops.bend as HO
import ./move_kit.bend as K

# Kit
# ---

# a <= max(a, b)
def le.max(a: Nat, +b: Nat) -> N.Le(a, Nat.max(a, b)):
  match a:
    case 0n:
      N.le_zero(b)
    case 1n+p:
      match b:
        case 0n:
          N.le_refl(1n+p)
        case 1n+q:
          le.max(p, q)

# a round that keeps the cells: within the round's peak
def le.peak(+ds: List<&2, Bk.Def>, +st: Cr.Cir.State, +t: Bk.Term) ->
  N.Le(D.Mem.cells(st), Nat.max(D.Mem.cells(st), D.Need(ds, st, t))):
  le.max(D.Mem.cells(st), D.Need(ds, st, t))

# The frames' headers
# --------------------

# a frame's header: the kind k, the quantity qv, no flag (M.header(k, qv, 0))
def Hd(+k: U32, +qv: U32) -> U32:
  Wa.Wasm.op(Wa.Wasm.Op.or{}, Wa.Wasm.op(Wa.Wasm.Op.or{}, k, Wa.Wasm.op(Wa.Wasm.Op.shl{}, qv, 6)), 0)

# what a frame's cell needs of its header hv: the tag of its kind, its
# quantity q, not STATIC, no flag K
def HdOK(+hv: U32, kind: D.FK, q: Bk.Quan) -> Data:
  D.P2({D.TgW(hv) == D.FK.tag(kind) : U32}, D.P2({D.QnW(hv) == Mc.Img.quan(q) : U32},
    D.P2({D.FlW(hv, 1024) == False{} : Bool}, {D.FlW(hv, 2048) == False{} : Bool})))

def hd.ok(kind: D.FK, q: Bk.Quan) -> HdOK(Hd(D.FK.tag(kind), Mc.Img.quan(q)), kind, q):
  match kind:
    case D.FK.arg{}:
      match q:
        case Bk.Quan.Q0{}:
          ({==}, ({==}, ({==}, {==})))
        case Bk.Quan.Q1{}:
          ({==}, ({==}, ({==}, {==})))
        case Bk.Quan.Q2{}:
          ({==}, ({==}, ({==}, {==})))
    case D.FK.val{}:
      match q:
        case Bk.Quan.Q0{}:
          ({==}, ({==}, ({==}, {==})))
        case Bk.Quan.Q1{}:
          ({==}, ({==}, ({==}, {==})))
        case Bk.Quan.Q2{}:
          ({==}, ({==}, ({==}, {==})))
    case D.FK.fun{}:
      match q:
        case Bk.Quan.Q0{}:
          ({==}, ({==}, ({==}, {==})))
        case Bk.Quan.Q1{}:
          ({==}, ({==}, ({==}, {==})))
        case Bk.Quan.Q2{}:
          ({==}, ({==}, ({==}, {==})))
    case D.FK.let{}:
      match q:
        case Bk.Quan.Q0{}:
          ({==}, ({==}, ({==}, {==})))
        case Bk.Quan.Q1{}:
          ({==}, ({==}, ({==}, {==})))
        case Bk.Quan.Q2{}:
          ({==}, ({==}, ({==}, {==})))
    case D.FK.tupb{}:
      match q:
        case Bk.Quan.Q0{}:
          ({==}, ({==}, ({==}, {==})))
        case Bk.Quan.Q1{}:
          ({==}, ({==}, ({==}, {==})))
        case Bk.Quan.Q2{}:
          ({==}, ({==}, ({==}, {==})))
    case D.FK.tupa{}:
      match q:
        case Bk.Quan.Q0{}:
          ({==}, ({==}, ({==}, {==})))
        case Bk.Quan.Q1{}:
          ({==}, ({==}, ({==}, {==})))
        case Bk.Quan.Q2{}:
          ({==}, ({==}, ({==}, {==})))
    case D.FK.rwt{}:
      match q:
        case Bk.Quan.Q0{}:
          ({==}, ({==}, ({==}, {==})))
        case Bk.Quan.Q1{}:
          ({==}, ({==}, ({==}, {==})))
        case Bk.Quan.Q2{}:
          ({==}, ({==}, ({==}, {==})))
    case D.FK.minb{}:
      match q:
        case Bk.Quan.Q0{}:
          ({==}, ({==}, ({==}, {==})))
        case Bk.Quan.Q1{}:
          ({==}, ({==}, ({==}, {==})))
        case Bk.Quan.Q2{}:
          ({==}, ({==}, ({==}, {==})))
    case D.FK.mina{}:
      match q:
        case Bk.Quan.Q0{}:
          ({==}, ({==}, ({==}, {==})))
        case Bk.Quan.Q1{}:
          ({==}, ({==}, ({==}, {==})))
        case Bk.Quan.Q2{}:
          ({==}, ({==}, ({==}, {==})))

# the headers of Rwt □ P f and Min □ b (quantity 0)
def hd.rwt() -> HdOK(38, D.FK.rwt{}, Bk.Quan.Q0{}):
  ({==}, ({==}, ({==}, {==})))

def hd.min() -> HdOK(39, D.FK.minb{}, Bk.Quan.Q0{}):
  ({==}, ({==}, ({==}, {==})))

# Nodes
# -----

# the cell r is a node of its own term
def node.self(t: Bk.Term, +m: Cr.Cir.Cells, +r: U32) -> {D.Node(t, m, r, r) == True{} : Bool}:
  match t:
    case Bk.Term.Var{_}:
      D.u32.refl(r)
    case Bk.Term.Ref{_}:
      D.u32.refl(r)
    case Bk.Term.Ann{y, z}:
      D.or.l(U32.is_eq(r, r), Bool.or(D.Node(y, m, D.Fd(2n, m, r), r), D.Node(z, m, D.Fd(3n, m, r), r)), D.u32.refl(r))
    case Bk.Term.Let{_, v, f}:
      D.or.l(U32.is_eq(r, r), Bool.or(D.Node(v, m, D.Fd(2n, m, r), r), D.Node(f, m, D.Fd(3n, m, r), r)), D.u32.refl(r))
    case Bk.Term.Typ{y}:
      D.or.l(U32.is_eq(r, r), D.Node(y, m, D.Fd(2n, m, r), r), D.u32.refl(r))
    case Bk.Term.Min{a, b}:
      D.or.l(U32.is_eq(r, r), Bool.or(D.Node(a, m, D.Fd(2n, m, r), r), D.Node(b, m, D.Fd(3n, m, r), r)), D.u32.refl(r))
    case Bk.Term.All{_, a, b}:
      D.or.l(U32.is_eq(r, r), Bool.or(D.Node(a, m, D.Fd(2n, m, r), r), D.Node(b, m, D.Fd(3n, m, r), r)), D.u32.refl(r))
    case Bk.Term.Lam{_, f}:
      D.or.l(U32.is_eq(r, r), D.Node(f, m, D.Fd(2n, m, r), r), D.u32.refl(r))
    case Bk.Term.App{_, f, y}:
      D.or.l(U32.is_eq(r, r), Bool.or(D.Node(f, m, D.Fd(2n, m, r), r), D.Node(y, m, D.Fd(3n, m, r), r)), D.u32.refl(r))
    case Bk.Term.Sig{_, a, b}:
      D.or.l(U32.is_eq(r, r), Bool.or(D.Node(a, m, D.Fd(2n, m, r), r), D.Node(b, m, D.Fd(3n, m, r), r)), D.u32.refl(r))
    case Bk.Term.Tup{_, a, b}:
      D.or.l(U32.is_eq(r, r), Bool.or(D.Node(a, m, D.Fd(2n, m, r), r), D.Node(b, m, D.Fd(3n, m, r), r)), D.u32.refl(r))
    case Bk.Term.Prj{h}:
      D.or.l(U32.is_eq(r, r), D.Node(h, m, D.Fd(2n, m, r), r), D.u32.refl(r))
    case Bk.Term.Enu{_}:
      D.u32.refl(r)
    case Bk.Term.Lab{_}:
      D.u32.refl(r)
    case Bk.Term.Mat{_, h, n}:
      D.or.l(U32.is_eq(r, r), Bool.or(D.Node(h, m, D.Fd(3n, m, r), r), D.Node(n, m, D.Fd(4n, m, r), r)), D.u32.refl(r))
    case Bk.Term.Efq{}:
      D.u32.refl(r)
    case Bk.Term.Eql{a, b, y}:
      D.or.l(U32.is_eq(r, r), Bool.or(D.Node(a, m, D.Fd(2n, m, r), r), Bool.or(D.Node(b, m, D.Fd(3n, m, r), r), D.Node(y, m, D.Fd(4n, m, r), r))), D.u32.refl(r))
    case Bk.Term.Rfl{}:
      D.u32.refl(r)
    case Bk.Term.Rwt{e, y, f}:
      D.or.l(U32.is_eq(r, r), Bool.or(D.Node(e, m, D.Fd(2n, m, r), r), Bool.or(D.Node(y, m, D.Fd(3n, m, r), r), D.Node(f, m, D.Fd(4n, m, r), r))), D.u32.refl(r))

# HS's heaps
# ----------

# a borrowed term less
def hsk.drop(+dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells,
  +nx: U32, +fi: U32, +im: U32, +os: List<&2, D.Rt>, b: D.Rt, +bs: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32,
  +ps: List<&2, U32>, h: D.HSK(dk, ds, ks, img, m, nx, fi, im, os, Con{b, bs}, fs, sp, pend, ps)) ->
  D.HSK(dk, ds, ks, img, m, nx, fi, im, os, bs, fs, sp, pend, ps):
  match b:
    case D.Rt{c, u}:
      match h:
        case Tuple{ho, Tuple{Tuple{_, hb}, Tuple{Tuple{_, hh}, r}}}:
          (ho, (hb, (hh, r)))

# Nat algebra
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

# a + (b + c) = b + (a + c)
def add.lc(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(a, Nat.add(b, c)) == Nat.add(b, Nat.add(a, c)) : Nat}:
  Equal.trans(Nat, Nat.add(a, Nat.add(b, c)), Nat.add(Nat.add(a, b), c), Nat.add(b, Nat.add(a, c)),
    Equal.sym(Nat, Nat.add(Nat.add(a, b), c), Nat.add(a, Nat.add(b, c)), add.assoc(a, b, c)),
    Equal.trans(Nat, Nat.add(Nat.add(a, b), c), Nat.add(Nat.add(b, a), c), Nat.add(b, Nat.add(a, c)),
      Equal.cong(Nat, Nat, z => Nat.add(z, c), Nat.add(a, b), Nat.add(b, a), add.comm(a, b)), add.assoc(b, a, c)))

# the first two roots trade places: each cell has as many pointers
def ptr.sw(+n: Nat, +m: Cr.Cir.Cells, +fi: U32, +ps: List<&2, U32>, +a: U32, +b: U32, +rs: List<&2, U32>, +c: U32) ->
  {D.Ptr(n, m, fi, ps, Con{a, Con{b, rs}}, c) == D.Ptr(n, m, fi, ps, Con{b, Con{a, rs}}, c) : Nat}:
  Equal.cong(Nat, Nat, z => Nat.add(D.Pc(n, m, ps, fi, c), z), D.RcL(Con{a, Con{b, rs}}, c), D.RcL(Con{b, Con{a, rs}}, c),
    add.lc(D.Nat.of(U32.is_eq(a, c)), D.Nat.of(U32.is_eq(b, c)), D.RcL(rs, c)))

def pendok.sw(qs: List<&2, U32>, +ps: List<&2, U32>, +m: Cr.Cir.Cells, +fi: U32, +nx: U32, +a: U32, +b: U32, +rs: List<&2, U32>,
  h: D.PendOK(qs, ps, m, fi, nx, Con{a, Con{b, rs}})) -> D.PendOK(qs, ps, m, fi, nx, Con{b, Con{a, rs}}):
  match qs:
    case Nil{}:
      h
    case Con{+p, +rest}:
      match h:
        case Tuple{h1, Tuple{h2, Tuple{h3, Tuple{h4, hr}}}}:
          +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
          (h1, (h2, (h3, ((%ptr.sw(n, m, fi, ps, a, b, rs, p) : {_ == 0n : Nat}; h4), pendok.sw(rest, ps, m, fi, nx, a, b, rs, hr)))))

def cnt.sw(n: Nat, +m: Cr.Cir.Cells, +c: U32, +N: Nat, +fi: U32, +ps: List<&2, U32>, +a: U32, +b: U32, +rs: List<&2, U32>) ->
  {D.Cnt(n, m, c, N, fi, ps, Con{a, Con{b, rs}}) == D.Cnt(n, m, c, N, fi, ps, Con{b, Con{a, rs}}) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      +rs1 = {Con{a, Con{b, rs}} : List<&2, U32>}
      +rs2 = {Con{b, Con{a, rs}} : List<&2, U32>}
      %ptr.sw(N, m, fi, ps, a, b, rs, c) :
        {Bool.and(Bool.or(Bool.not(U32.is_lt(D.Tg(m, c), 19)), Bool.or(D.Fl(m, c, 1024), Bool.or(D.Mem(ps, c),
          Nat.is_eq(U32.to_nat(D.Fd(1n, m, c)), D.Ptr(N, m, fi, ps, rs1, c))))), D.Cnt(p, m, U32.inc(c), N, fi, ps, rs1)) ==
        Bool.and(Bool.or(Bool.not(U32.is_lt(D.Tg(m, c), 19)), Bool.or(D.Fl(m, c, 1024), Bool.or(D.Mem(ps, c),
          Nat.is_eq(U32.to_nat(D.Fd(1n, m, c)), _)))), D.Cnt(p, m, U32.inc(c), N, fi, ps, rs2)) : Bool}
      %cnt.sw(p, m, U32.inc(c), N, fi, ps, a, b, rs) :
        {Bool.and(Bool.or(Bool.not(U32.is_lt(D.Tg(m, c), 19)), Bool.or(D.Fl(m, c, 1024), Bool.or(D.Mem(ps, c),
          Nat.is_eq(U32.to_nat(D.Fd(1n, m, c)), D.Ptr(N, m, fi, ps, rs1, c))))), D.Cnt(p, m, U32.inc(c), N, fi, ps, rs1)) ==
        Bool.and(Bool.or(Bool.not(U32.is_lt(D.Tg(m, c), 19)), Bool.or(D.Fl(m, c, 1024), Bool.or(D.Mem(ps, c),
          Nat.is_eq(U32.to_nat(D.Fd(1n, m, c)), D.Ptr(N, m, fi, ps, rs1, c))))), _) : Bool}
      {==}

def heap.sw(+m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +a: U32, +b: U32, +rs: List<&2, U32>, +pend: U32,
  +ps: List<&2, U32>, h: D.Heap(m, nx, fi, im, Con{a, Con{b, rs}}, pend, ps)) -> D.Heap(m, nx, fi, im, Con{b, Con{a, rs}}, pend, ps):
  match h:
    case Tuple{hc, Tuple{hpk, Tuple{hn, r}}}:
      +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
      (hc, (pendok.sw(ps, ps, m, fi, nx, a, b, rs, hpk),
        (Equal.trans(Bool, D.Cnt(n, m, fi, n, fi, ps, Con{b, Con{a, rs}}), D.Cnt(n, m, fi, n, fi, ps, Con{a, Con{b, rs}}), True{},
          Equal.sym(Bool, D.Cnt(n, m, fi, n, fi, ps, Con{a, Con{b, rs}}), D.Cnt(n, m, fi, n, fi, ps, Con{b, Con{a, rs}}),
            cnt.sw(n, m, fi, n, fi, ps, a, b, rs)), hn), r)))

# the first two roots trade places (no borrowed term)
def hsk.swap(+dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells,
  +nx: U32, +fi: U32, +im: U32, a: D.Rt, b: D.Rt, +os: List<&2, D.Rt>, +fs: List<&2, D.AF>, +sp: U32, +pend: U32,
  +ps: List<&2, U32>, h: D.HSK(dk, ds, ks, img, m, nx, fi, im, Con{a, Con{b, os}}, Nil{}, fs, sp, pend, ps)) ->
  D.HSK(dk, ds, ks, img, m, nx, fi, im, Con{b, Con{a, os}}, Nil{}, fs, sp, pend, ps):
  match a b:
    case D.Rt{+ca, +ua} D.Rt{+cb, +ub}:
      match h:
        case Tuple{Tuple{ia, Tuple{ib, ir}}, Tuple{hb, Tuple{_, Tuple{hf, Tuple{hp, hi}}}}}:
          ((ib, (ia, ir)), (hb, (Unit{}, (hf, (heap.sw(m, nx, fi, im, ca, cb, D.Rt.cells(os), pend, ps, hp), hi)))))

# a list of 63 registers is RG of its first four and the rest
def rg.of(xs: List<&2, U32>, h: {List.length(&2, U32, xs) == 63n : Nat}) ->
  {xs == D.RG(Maybe.default(&2, U32, List.get(&2, U32, xs, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 1n), 0),
    Maybe.default(&2, U32, List.get(&2, U32, xs, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, xs, 3n), 0),
    D.R59.list(D.R59.of(xs))) : List<&2, U32>}:
  match xs:
    case Nil{}:
      D.bool.ft({Nil{} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Nil{}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Nil{}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Nil{}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Nil{}, 3n), 0), D.R59.list(D.R59.of(Nil{}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 0n, 63n, h))
    case Con{+a0, +x1}:
      match x1:
        case Nil{}:
          D.bool.ft({Con{a0, Nil{}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Nil{}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Nil{}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Nil{}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Nil{}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Nil{}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 1n, 63n, h))
        case Con{+a1, +x2}:
          match x2:
            case Nil{}:
              D.bool.ft({Con{a0, Con{a1, Nil{}}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Nil{}}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Nil{}}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Nil{}}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Nil{}}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Con{a1, Nil{}}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 2n, 63n, h))
            case Con{+a2, +x3}:
              match x3:
                case Nil{}:
                  D.bool.ft({Con{a0, Con{a1, Con{a2, Nil{}}}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Nil{}}}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Nil{}}}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Nil{}}}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Nil{}}}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Con{a1, Con{a2, Nil{}}}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 3n, 63n, h))
                case Con{+a3, +x4}:
                  match x4:
                    case Nil{}:
                      D.bool.ft({Con{a0, Con{a1, Con{a2, Con{a3, Nil{}}}}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Nil{}}}}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Nil{}}}}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Nil{}}}}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Nil{}}}}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Con{a1, Con{a2, Con{a3, Nil{}}}}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 4n, 63n, h))
                    case Con{+a4, +x5}:
                      match x5:
                        case Nil{}:
                          D.bool.ft({Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Nil{}}}}}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Nil{}}}}}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Nil{}}}}}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Nil{}}}}}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Nil{}}}}}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Nil{}}}}}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 5n, 63n, h))
                        case Con{+a5, +x6}:
                          match x6:
                            case Nil{}:
                              D.bool.ft({Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Nil{}}}}}}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Nil{}}}}}}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Nil{}}}}}}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Nil{}}}}}}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Nil{}}}}}}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Nil{}}}}}}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 6n, 63n, h))
                            case Con{+a6, +x7}:
                              match x7:
                                case Nil{}:
                                  D.bool.ft({Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Nil{}}}}}}}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Nil{}}}}}}}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Nil{}}}}}}}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Nil{}}}}}}}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Nil{}}}}}}}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Nil{}}}}}}}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 7n, 63n, h))
                                case Con{+a7, +x8}:
                                  match x8:
                                    case Nil{}:
                                      D.bool.ft({Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Nil{}}}}}}}}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Nil{}}}}}}}}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Nil{}}}}}}}}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Nil{}}}}}}}}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Nil{}}}}}}}}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Nil{}}}}}}}}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 8n, 63n, h))
                                    case Con{+a8, +x9}:
                                      match x9:
                                        case Nil{}:
                                          D.bool.ft({Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Nil{}}}}}}}}}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Nil{}}}}}}}}}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Nil{}}}}}}}}}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Nil{}}}}}}}}}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Nil{}}}}}}}}}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Nil{}}}}}}}}}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 9n, 63n, h))
                                        case Con{+a9, +x10}:
                                          match x10:
                                            case Nil{}:
                                              D.bool.ft({Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Nil{}}}}}}}}}}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Nil{}}}}}}}}}}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Nil{}}}}}}}}}}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Nil{}}}}}}}}}}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Nil{}}}}}}}}}}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Nil{}}}}}}}}}}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 10n, 63n, h))
                                            case Con{+a10, +x11}:
                                              match x11:
                                                case Nil{}:
                                                  D.bool.ft({Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Nil{}}}}}}}}}}}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Nil{}}}}}}}}}}}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Nil{}}}}}}}}}}}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Nil{}}}}}}}}}}}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Nil{}}}}}}}}}}}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Nil{}}}}}}}}}}}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 11n, 63n, h))
                                                case Con{+a11, +x12}:
                                                  match x12:
                                                    case Nil{}:
                                                      D.bool.ft({Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Nil{}}}}}}}}}}}}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Nil{}}}}}}}}}}}}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Nil{}}}}}}}}}}}}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Nil{}}}}}}}}}}}}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Nil{}}}}}}}}}}}}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Nil{}}}}}}}}}}}}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 12n, 63n, h))
                                                    case Con{+a12, +x13}:
                                                      match x13:
                                                        case Nil{}:
                                                          D.bool.ft({Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Nil{}}}}}}}}}}}}}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Nil{}}}}}}}}}}}}}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Nil{}}}}}}}}}}}}}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Nil{}}}}}}}}}}}}}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Nil{}}}}}}}}}}}}}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Nil{}}}}}}}}}}}}}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 13n, 63n, h))
                                                        case Con{+a13, +x14}:
                                                          match x14:
                                                            case Nil{}:
                                                              D.bool.ft({Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Nil{}}}}}}}}}}}}}}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Nil{}}}}}}}}}}}}}}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Nil{}}}}}}}}}}}}}}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Nil{}}}}}}}}}}}}}}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Nil{}}}}}}}}}}}}}}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Nil{}}}}}}}}}}}}}}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 14n, 63n, h))
                                                            case Con{+a14, +x15}:
                                                              match x15:
                                                                case Nil{}:
                                                                  D.bool.ft({Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Nil{}}}}}}}}}}}}}}}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Nil{}}}}}}}}}}}}}}}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Nil{}}}}}}}}}}}}}}}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Nil{}}}}}}}}}}}}}}}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Nil{}}}}}}}}}}}}}}}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Nil{}}}}}}}}}}}}}}}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 15n, 63n, h))
                                                                case Con{+a15, +x16}:
                                                                  match x16:
                                                                    case Nil{}:
                                                                      D.bool.ft({Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Nil{}}}}}}}}}}}}}}}}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Nil{}}}}}}}}}}}}}}}}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Nil{}}}}}}}}}}}}}}}}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Nil{}}}}}}}}}}}}}}}}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Nil{}}}}}}}}}}}}}}}}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Nil{}}}}}}}}}}}}}}}}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 16n, 63n, h))
                                                                    case Con{+a16, +x17}:
                                                                      match x17:
                                                                        case Nil{}:
                                                                          D.bool.ft({Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Nil{}}}}}}}}}}}}}}}}}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Nil{}}}}}}}}}}}}}}}}}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Nil{}}}}}}}}}}}}}}}}}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Nil{}}}}}}}}}}}}}}}}}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Nil{}}}}}}}}}}}}}}}}}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Nil{}}}}}}}}}}}}}}}}}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 17n, 63n, h))
                                                                        case Con{+a17, +x18}:
                                                                          match x18:
                                                                            case Nil{}:
                                                                              D.bool.ft({Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Nil{}}}}}}}}}}}}}}}}}}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Nil{}}}}}}}}}}}}}}}}}}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Nil{}}}}}}}}}}}}}}}}}}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Nil{}}}}}}}}}}}}}}}}}}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Nil{}}}}}}}}}}}}}}}}}}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Nil{}}}}}}}}}}}}}}}}}}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 18n, 63n, h))
                                                                            case Con{+a18, +x19}:
                                                                              match x19:
                                                                                case Nil{}:
                                                                                  D.bool.ft({Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Nil{}}}}}}}}}}}}}}}}}}}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Nil{}}}}}}}}}}}}}}}}}}}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Nil{}}}}}}}}}}}}}}}}}}}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Nil{}}}}}}}}}}}}}}}}}}}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Nil{}}}}}}}}}}}}}}}}}}}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Nil{}}}}}}}}}}}}}}}}}}}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 19n, 63n, h))
                                                                                case Con{+a19, +x20}:
                                                                                  match x20:
                                                                                    case Nil{}:
                                                                                      D.bool.ft({Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Nil{}}}}}}}}}}}}}}}}}}}}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Nil{}}}}}}}}}}}}}}}}}}}}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Nil{}}}}}}}}}}}}}}}}}}}}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Nil{}}}}}}}}}}}}}}}}}}}}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Nil{}}}}}}}}}}}}}}}}}}}}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Nil{}}}}}}}}}}}}}}}}}}}}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 20n, 63n, h))
                                                                                    case Con{+a20, +x21}:
                                                                                      match x21:
                                                                                        case Nil{}:
                                                                                          D.bool.ft({Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Nil{}}}}}}}}}}}}}}}}}}}}}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Nil{}}}}}}}}}}}}}}}}}}}}}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Nil{}}}}}}}}}}}}}}}}}}}}}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Nil{}}}}}}}}}}}}}}}}}}}}}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Nil{}}}}}}}}}}}}}}}}}}}}}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Nil{}}}}}}}}}}}}}}}}}}}}}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 21n, 63n, h))
                                                                                        case Con{+a21, +x22}:
                                                                                          match x22:
                                                                                            case Nil{}:
                                                                                              D.bool.ft({Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Nil{}}}}}}}}}}}}}}}}}}}}}}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Nil{}}}}}}}}}}}}}}}}}}}}}}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Nil{}}}}}}}}}}}}}}}}}}}}}}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Nil{}}}}}}}}}}}}}}}}}}}}}}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Nil{}}}}}}}}}}}}}}}}}}}}}}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Nil{}}}}}}}}}}}}}}}}}}}}}}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 22n, 63n, h))
                                                                                            case Con{+a22, +x23}:
                                                                                              match x23:
                                                                                                case Nil{}:
                                                                                                  D.bool.ft({Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Nil{}}}}}}}}}}}}}}}}}}}}}}}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Nil{}}}}}}}}}}}}}}}}}}}}}}}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Nil{}}}}}}}}}}}}}}}}}}}}}}}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Nil{}}}}}}}}}}}}}}}}}}}}}}}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Nil{}}}}}}}}}}}}}}}}}}}}}}}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Nil{}}}}}}}}}}}}}}}}}}}}}}}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 23n, 63n, h))
                                                                                                case Con{+a23, +x24}:
                                                                                                  match x24:
                                                                                                    case Nil{}:
                                                                                                      D.bool.ft({Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Nil{}}}}}}}}}}}}}}}}}}}}}}}}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 24n, 63n, h))
                                                                                                    case Con{+a24, +x25}:
                                                                                                      match x25:
                                                                                                        case Nil{}:
                                                                                                          D.bool.ft({Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 25n, 63n, h))
                                                                                                        case Con{+a25, +x26}:
                                                                                                          match x26:
                                                                                                            case Nil{}:
                                                                                                              D.bool.ft({Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 26n, 63n, h))
                                                                                                            case Con{+a26, +x27}:
                                                                                                              match x27:
                                                                                                                case Nil{}:
                                                                                                                  D.bool.ft({Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 27n, 63n, h))
                                                                                                                case Con{+a27, +x28}:
                                                                                                                  match x28:
                                                                                                                    case Nil{}:
                                                                                                                      D.bool.ft({Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 28n, 63n, h))
                                                                                                                    case Con{+a28, +x29}:
                                                                                                                      match x29:
                                                                                                                        case Nil{}:
                                                                                                                          D.bool.ft({Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 29n, 63n, h))
                                                                                                                        case Con{+a29, +x30}:
                                                                                                                          match x30:
                                                                                                                            case Nil{}:
                                                                                                                              D.bool.ft({Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 30n, 63n, h))
                                                                                                                            case Con{+a30, +x31}:
                                                                                                                              match x31:
                                                                                                                                case Nil{}:
                                                                                                                                  D.bool.ft({Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 31n, 63n, h))
                                                                                                                                case Con{+a31, +x32}:
                                                                                                                                  match x32:
                                                                                                                                    case Nil{}:
                                                                                                                                      D.bool.ft({Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 32n, 63n, h))
                                                                                                                                    case Con{+a32, +x33}:
                                                                                                                                      match x33:
                                                                                                                                        case Nil{}:
                                                                                                                                          D.bool.ft({Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 33n, 63n, h))
                                                                                                                                        case Con{+a33, +x34}:
                                                                                                                                          match x34:
                                                                                                                                            case Nil{}:
                                                                                                                                              D.bool.ft({Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 34n, 63n, h))
                                                                                                                                            case Con{+a34, +x35}:
                                                                                                                                              match x35:
                                                                                                                                                case Nil{}:
                                                                                                                                                  D.bool.ft({Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 35n, 63n, h))
                                                                                                                                                case Con{+a35, +x36}:
                                                                                                                                                  match x36:
                                                                                                                                                    case Nil{}:
                                                                                                                                                      D.bool.ft({Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 36n, 63n, h))
                                                                                                                                                    case Con{+a36, +x37}:
                                                                                                                                                      match x37:
                                                                                                                                                        case Nil{}:
                                                                                                                                                          D.bool.ft({Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 37n, 63n, h))
                                                                                                                                                        case Con{+a37, +x38}:
                                                                                                                                                          match x38:
                                                                                                                                                            case Nil{}:
                                                                                                                                                              D.bool.ft({Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 38n, 63n, h))
                                                                                                                                                            case Con{+a38, +x39}:
                                                                                                                                                              match x39:
                                                                                                                                                                case Nil{}:
                                                                                                                                                                  D.bool.ft({Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 39n, 63n, h))
                                                                                                                                                                case Con{+a39, +x40}:
                                                                                                                                                                  match x40:
                                                                                                                                                                    case Nil{}:
                                                                                                                                                                      D.bool.ft({Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 40n, 63n, h))
                                                                                                                                                                    case Con{+a40, +x41}:
                                                                                                                                                                      match x41:
                                                                                                                                                                        case Nil{}:
                                                                                                                                                                          D.bool.ft({Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 41n, 63n, h))
                                                                                                                                                                        case Con{+a41, +x42}:
                                                                                                                                                                          match x42:
                                                                                                                                                                            case Nil{}:
                                                                                                                                                                              D.bool.ft({Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 42n, 63n, h))
                                                                                                                                                                            case Con{+a42, +x43}:
                                                                                                                                                                              match x43:
                                                                                                                                                                                case Nil{}:
                                                                                                                                                                                  D.bool.ft({Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 43n, 63n, h))
                                                                                                                                                                                case Con{+a43, +x44}:
                                                                                                                                                                                  match x44:
                                                                                                                                                                                    case Nil{}:
                                                                                                                                                                                      D.bool.ft({Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 44n, 63n, h))
                                                                                                                                                                                    case Con{+a44, +x45}:
                                                                                                                                                                                      match x45:
                                                                                                                                                                                        case Nil{}:
                                                                                                                                                                                          D.bool.ft({Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 45n, 63n, h))
                                                                                                                                                                                        case Con{+a45, +x46}:
                                                                                                                                                                                          match x46:
                                                                                                                                                                                            case Nil{}:
                                                                                                                                                                                              D.bool.ft({Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 46n, 63n, h))
                                                                                                                                                                                            case Con{+a46, +x47}:
                                                                                                                                                                                              match x47:
                                                                                                                                                                                                case Nil{}:
                                                                                                                                                                                                  D.bool.ft({Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 47n, 63n, h))
                                                                                                                                                                                                case Con{+a47, +x48}:
                                                                                                                                                                                                  match x48:
                                                                                                                                                                                                    case Nil{}:
                                                                                                                                                                                                      D.bool.ft({Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 48n, 63n, h))
                                                                                                                                                                                                    case Con{+a48, +x49}:
                                                                                                                                                                                                      match x49:
                                                                                                                                                                                                        case Nil{}:
                                                                                                                                                                                                          D.bool.ft({Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 49n, 63n, h))
                                                                                                                                                                                                        case Con{+a49, +x50}:
                                                                                                                                                                                                          match x50:
                                                                                                                                                                                                            case Nil{}:
                                                                                                                                                                                                              D.bool.ft({Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 50n, 63n, h))
                                                                                                                                                                                                            case Con{+a50, +x51}:
                                                                                                                                                                                                              match x51:
                                                                                                                                                                                                                case Nil{}:
                                                                                                                                                                                                                  D.bool.ft({Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 51n, 63n, h))
                                                                                                                                                                                                                case Con{+a51, +x52}:
                                                                                                                                                                                                                  match x52:
                                                                                                                                                                                                                    case Nil{}:
                                                                                                                                                                                                                      D.bool.ft({Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 52n, 63n, h))
                                                                                                                                                                                                                    case Con{+a52, +x53}:
                                                                                                                                                                                                                      match x53:
                                                                                                                                                                                                                        case Nil{}:
                                                                                                                                                                                                                          D.bool.ft({Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 53n, 63n, h))
                                                                                                                                                                                                                        case Con{+a53, +x54}:
                                                                                                                                                                                                                          match x54:
                                                                                                                                                                                                                            case Nil{}:
                                                                                                                                                                                                                              D.bool.ft({Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Con{a53, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Con{a53, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Con{a53, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Con{a53, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Con{a53, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Con{a53, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 54n, 63n, h))
                                                                                                                                                                                                                            case Con{+a54, +x55}:
                                                                                                                                                                                                                              match x55:
                                                                                                                                                                                                                                case Nil{}:
                                                                                                                                                                                                                                  D.bool.ft({Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Con{a53, Con{a54, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Con{a53, Con{a54, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Con{a53, Con{a54, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Con{a53, Con{a54, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Con{a53, Con{a54, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Con{a53, Con{a54, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 55n, 63n, h))
                                                                                                                                                                                                                                case Con{+a55, +x56}:
                                                                                                                                                                                                                                  match x56:
                                                                                                                                                                                                                                    case Nil{}:
                                                                                                                                                                                                                                      D.bool.ft({Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Con{a53, Con{a54, Con{a55, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Con{a53, Con{a54, Con{a55, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Con{a53, Con{a54, Con{a55, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Con{a53, Con{a54, Con{a55, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Con{a53, Con{a54, Con{a55, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Con{a53, Con{a54, Con{a55, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 56n, 63n, h))
                                                                                                                                                                                                                                    case Con{+a56, +x57}:
                                                                                                                                                                                                                                      match x57:
                                                                                                                                                                                                                                        case Nil{}:
                                                                                                                                                                                                                                          D.bool.ft({Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Con{a53, Con{a54, Con{a55, Con{a56, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Con{a53, Con{a54, Con{a55, Con{a56, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Con{a53, Con{a54, Con{a55, Con{a56, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Con{a53, Con{a54, Con{a55, Con{a56, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Con{a53, Con{a54, Con{a55, Con{a56, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Con{a53, Con{a54, Con{a55, Con{a56, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 57n, 63n, h))
                                                                                                                                                                                                                                        case Con{+a57, +x58}:
                                                                                                                                                                                                                                          match x58:
                                                                                                                                                                                                                                            case Nil{}:
                                                                                                                                                                                                                                              D.bool.ft({Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Con{a53, Con{a54, Con{a55, Con{a56, Con{a57, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Con{a53, Con{a54, Con{a55, Con{a56, Con{a57, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Con{a53, Con{a54, Con{a55, Con{a56, Con{a57, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Con{a53, Con{a54, Con{a55, Con{a56, Con{a57, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Con{a53, Con{a54, Con{a55, Con{a56, Con{a57, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Con{a53, Con{a54, Con{a55, Con{a56, Con{a57, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 58n, 63n, h))
                                                                                                                                                                                                                                            case Con{+a58, +x59}:
                                                                                                                                                                                                                                              match x59:
                                                                                                                                                                                                                                                case Nil{}:
                                                                                                                                                                                                                                                  D.bool.ft({Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Con{a53, Con{a54, Con{a55, Con{a56, Con{a57, Con{a58, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Con{a53, Con{a54, Con{a55, Con{a56, Con{a57, Con{a58, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Con{a53, Con{a54, Con{a55, Con{a56, Con{a57, Con{a58, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Con{a53, Con{a54, Con{a55, Con{a56, Con{a57, Con{a58, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Con{a53, Con{a54, Con{a55, Con{a56, Con{a57, Con{a58, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Con{a53, Con{a54, Con{a55, Con{a56, Con{a57, Con{a58, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 59n, 63n, h))
                                                                                                                                                                                                                                                case Con{+a59, +x60}:
                                                                                                                                                                                                                                                  match x60:
                                                                                                                                                                                                                                                    case Nil{}:
                                                                                                                                                                                                                                                      D.bool.ft({Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Con{a53, Con{a54, Con{a55, Con{a56, Con{a57, Con{a58, Con{a59, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Con{a53, Con{a54, Con{a55, Con{a56, Con{a57, Con{a58, Con{a59, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Con{a53, Con{a54, Con{a55, Con{a56, Con{a57, Con{a58, Con{a59, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Con{a53, Con{a54, Con{a55, Con{a56, Con{a57, Con{a58, Con{a59, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Con{a53, Con{a54, Con{a55, Con{a56, Con{a57, Con{a58, Con{a59, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Con{a53, Con{a54, Con{a55, Con{a56, Con{a57, Con{a58, Con{a59, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 60n, 63n, h))
                                                                                                                                                                                                                                                    case Con{+a60, +x61}:
                                                                                                                                                                                                                                                      match x61:
                                                                                                                                                                                                                                                        case Nil{}:
                                                                                                                                                                                                                                                          D.bool.ft({Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Con{a53, Con{a54, Con{a55, Con{a56, Con{a57, Con{a58, Con{a59, Con{a60, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Con{a53, Con{a54, Con{a55, Con{a56, Con{a57, Con{a58, Con{a59, Con{a60, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Con{a53, Con{a54, Con{a55, Con{a56, Con{a57, Con{a58, Con{a59, Con{a60, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Con{a53, Con{a54, Con{a55, Con{a56, Con{a57, Con{a58, Con{a59, Con{a60, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Con{a53, Con{a54, Con{a55, Con{a56, Con{a57, Con{a58, Con{a59, Con{a60, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Con{a53, Con{a54, Con{a55, Con{a56, Con{a57, Con{a58, Con{a59, Con{a60, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 61n, 63n, h))
                                                                                                                                                                                                                                                        case Con{+a61, +x62}:
                                                                                                                                                                                                                                                          match x62:
                                                                                                                                                                                                                                                            case Nil{}:
                                                                                                                                                                                                                                                              D.bool.ft({Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Con{a53, Con{a54, Con{a55, Con{a56, Con{a57, Con{a58, Con{a59, Con{a60, Con{a61, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Con{a53, Con{a54, Con{a55, Con{a56, Con{a57, Con{a58, Con{a59, Con{a60, Con{a61, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Con{a53, Con{a54, Con{a55, Con{a56, Con{a57, Con{a58, Con{a59, Con{a60, Con{a61, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Con{a53, Con{a54, Con{a55, Con{a56, Con{a57, Con{a58, Con{a59, Con{a60, Con{a61, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Con{a53, Con{a54, Con{a55, Con{a56, Con{a57, Con{a58, Con{a59, Con{a60, Con{a61, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Con{a53, Con{a54, Con{a55, Con{a56, Con{a57, Con{a58, Con{a59, Con{a60, Con{a61, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 62n, 63n, h))
                                                                                                                                                                                                                                                            case Con{+a62, +x63}:
                                                                                                                                                                                                                                                              match x63:
                                                                                                                                                                                                                                                                case Nil{}:
                                                                                                                                                                                                                                                                  {==}
                                                                                                                                                                                                                                                                case Con{b, r}:
                                                                                                                                                                                                                                                                  D.bool.ft({Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Con{a53, Con{a54, Con{a55, Con{a56, Con{a57, Con{a58, Con{a59, Con{a60, Con{a61, Con{a62, Con{b, r}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == D.RG(Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Con{a53, Con{a54, Con{a55, Con{a56, Con{a57, Con{a58, Con{a59, Con{a60, Con{a61, Con{a62, Con{b, r}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Con{a53, Con{a54, Con{a55, Con{a56, Con{a57, Con{a58, Con{a59, Con{a60, Con{a61, Con{a62, Con{b, r}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 1n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Con{a53, Con{a54, Con{a55, Con{a56, Con{a57, Con{a58, Con{a59, Con{a60, Con{a61, Con{a62, Con{b, r}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2n), 0), Maybe.default(&2, U32, List.get(&2, U32, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Con{a53, Con{a54, Con{a55, Con{a56, Con{a57, Con{a58, Con{a59, Con{a60, Con{a61, Con{a62, Con{b, r}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 3n), 0), D.R59.list(D.R59.of(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, Con{a17, Con{a18, Con{a19, Con{a20, Con{a21, Con{a22, Con{a23, Con{a24, Con{a25, Con{a26, Con{a27, Con{a28, Con{a29, Con{a30, Con{a31, Con{a32, Con{a33, Con{a34, Con{a35, Con{a36, Con{a37, Con{a38, Con{a39, Con{a40, Con{a41, Con{a42, Con{a43, Con{a44, Con{a45, Con{a46, Con{a47, Con{a48, Con{a49, Con{a50, Con{a51, Con{a52, Con{a53, Con{a54, Con{a55, Con{a56, Con{a57, Con{a58, Con{a59, Con{a60, Con{a61, Con{a62, Con{b, r}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}))) : List<&2, U32>}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, 63n), 64n+List.length(&2, U32, r), 63n, h))

# M.push's four stores on a cell of zeros: the frame's cell, at once
def push.cells(+m: Cr.Cir.Cells, +z: U32, +hv: U32, +sp: U32, +av: U32, +bv: U32,
  hz: {Cr.Cir.Cells.get(m, z) == Cr.Cir.Cell.zero() : Cr.Cir.Cell}) ->
  {X.X.put(X.X.put(X.X.put(X.X.put(m, 0n, z, hv), 1n, z, sp), 2n, z, av), 3n, z, bv) ==
    Cr.Cir.Cells.set(m, z, Cr.Cir.Cell{hv, sp, av, bv, 0}) : Cr.Cir.Cells}:
  +c1 = {Cr.Cir.Cell{hv, 0, 0, 0, 0} : Cr.Cir.Cell}
  +c2 = {Cr.Cir.Cell{hv, sp, 0, 0, 0} : Cr.Cir.Cell}
  +c3 = {Cr.Cir.Cell{hv, sp, av, 0, 0} : Cr.Cir.Cell}
  +e1 = {(%Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(m, z), Cr.Cir.Cell.zero(), hz) :
      {Cr.Cir.Cells.set(m, z, Cr.Cir.Cell.set(0n, _, hv)) == Cr.Cir.Cells.set(m, z, c1) : Cr.Cir.Cells}; {==}) :
    {X.X.put(m, 0n, z, hv) == Cr.Cir.Cells.set(m, z, c1) : Cr.Cir.Cells}}
  +e2 = Equal.trans(Cr.Cir.Cells, X.X.put(X.X.put(m, 0n, z, hv), 1n, z, sp), X.X.put(Cr.Cir.Cells.set(m, z, c1), 1n, z, sp),
    Cr.Cir.Cells.set(m, z, c2),
    Equal.cong(Cr.Cir.Cells, Cr.Cir.Cells, y => X.X.put(y, 1n, z, sp), X.X.put(m, 0n, z, hv), Cr.Cir.Cells.set(m, z, c1), e1),
    Equal.sym(Cr.Cir.Cells, Cr.Cir.Cells.set(m, z, c2), X.X.put(Cr.Cir.Cells.set(m, z, c1), 1n, z, sp), X.Ce.put_set(m, z, c1, 1n, sp)))
  +e3 = Equal.trans(Cr.Cir.Cells, X.X.put(X.X.put(X.X.put(m, 0n, z, hv), 1n, z, sp), 2n, z, av),
    X.X.put(Cr.Cir.Cells.set(m, z, c2), 2n, z, av), Cr.Cir.Cells.set(m, z, c3),
    Equal.cong(Cr.Cir.Cells, Cr.Cir.Cells, y => X.X.put(y, 2n, z, av), X.X.put(X.X.put(m, 0n, z, hv), 1n, z, sp),
      Cr.Cir.Cells.set(m, z, c2), e2),
    Equal.sym(Cr.Cir.Cells, Cr.Cir.Cells.set(m, z, c3), X.X.put(Cr.Cir.Cells.set(m, z, c2), 2n, z, av), X.Ce.put_set(m, z, c2, 2n, av)))
  Equal.trans(Cr.Cir.Cells, X.X.put(X.X.put(X.X.put(X.X.put(m, 0n, z, hv), 1n, z, sp), 2n, z, av), 3n, z, bv),
    X.X.put(Cr.Cir.Cells.set(m, z, c3), 3n, z, bv), Cr.Cir.Cells.set(m, z, Cr.Cir.Cell{hv, sp, av, bv, 0}),
    Equal.cong(Cr.Cir.Cells, Cr.Cir.Cells, y => X.X.put(y, 3n, z, bv), X.X.put(X.X.put(X.X.put(m, 0n, z, hv), 1n, z, sp), 2n, z, av),
      Cr.Cir.Cells.set(m, z, c3), e3),
    Equal.sym(Cr.Cir.Cells, Cr.Cir.Cells.set(m, z, Cr.Cir.Cell{hv, sp, av, bv, 0}), X.X.put(Cr.Cir.Cells.set(m, z, c3), 3n, z, bv),
      X.Ce.put_set(m, z, c3, 3n, bv)))

# a state that Same finds: its first cell, image, limit and input, no output
def St.pg(st: Cr.Cir.State) -> U32:
  match st:
    case Cr.Cir.State{_, _, _, _, _, pg, _, _, _, _}:
      pg

def same.st(+regs: List<&2, U32>, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +keep: List<&2, Nat>,
  st: Cr.Cir.State, h: D.Same(regs, fi, im, lim, inp, keep, st)) ->
  {st == Cr.Cir.State{D.St.regs(st), D.St.cells(st), D.St.next(st), fi, im, St.pg(st), lim, inp, Nil{}, 0} : Cr.Cir.State}:
  match st:
    case Cr.Cir.State{+regs2, +m2, +nx2, +fi2, +im2, +pg2, +lim2, +inp2, +out2, +outn2}:
      match h:
        case Tuple{efi, Tuple{eim, Tuple{elim, Tuple{einp, Tuple{eout, Tuple{eoutn, _}}}}}}:
          %Equal.sym(U32, fi2, fi, efi) :
            {Cr.Cir.State{regs2, m2, nx2, _, im2, pg2, lim2, inp2, out2, outn2} == Cr.Cir.State{regs2, m2, nx2, fi, im, pg2, lim, inp, Nil{}, 0} : Cr.Cir.State}
          %Equal.sym(U32, im2, im, eim) :
            {Cr.Cir.State{regs2, m2, nx2, fi, _, pg2, lim2, inp2, out2, outn2} == Cr.Cir.State{regs2, m2, nx2, fi, im, pg2, lim, inp, Nil{}, 0} : Cr.Cir.State}
          %Equal.sym(U32, lim2, lim, elim) :
            {Cr.Cir.State{regs2, m2, nx2, fi, im, pg2, _, inp2, out2, outn2} == Cr.Cir.State{regs2, m2, nx2, fi, im, pg2, lim, inp, Nil{}, 0} : Cr.Cir.State}
          %Equal.sym(List<&2, Word(8n)>, inp2, inp, einp) :
            {Cr.Cir.State{regs2, m2, nx2, fi, im, pg2, lim, _, out2, outn2} == Cr.Cir.State{regs2, m2, nx2, fi, im, pg2, lim, inp, Nil{}, 0} : Cr.Cir.State}
          %Equal.sym(List<&2, Word(8n)>, out2, Nil{}, eout) :
            {Cr.Cir.State{regs2, m2, nx2, fi, im, pg2, lim, inp, _, outn2} == Cr.Cir.State{regs2, m2, nx2, fi, im, pg2, lim, inp, Nil{}, 0} : Cr.Cir.State}
          %Equal.sym(U32, outn2, 0, eoutn) :
            {Cr.Cir.State{regs2, m2, nx2, fi, im, pg2, lim, inp, Nil{}, _} == Cr.Cir.State{regs2, m2, nx2, fi, im, pg2, lim, inp, Nil{}, 0} : Cr.Cir.State}
          {==}

# the frames with a new one on top: the cell z, of the header hv, the link
# sp and the parts av (and bv, for Rwt), one of the machine's own, out of the
# pend list
def frs.push(+dk: Bool, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +ps: List<&2, U32>, +z: U32, +sp: U32, +fs: List<&2, D.AF>, +kind: D.FK, +q: Bk.Quan, +va: Bk.Term,
  +vb: Bk.Term, +hv: U32, +av: U32, +bv: U32, hz: {Cr.Cir.Cells.get(m, z) == Cr.Cir.Cell{hv, sp, av, bv, 0} : Cr.Cir.Cell},
  hok: HdOK(hv, kind, q), h0: {U32.is_eq(z, 0) == False{} : Bool}, hc: {Cr.Cir.is_cell(z, im, fi, nx) == True{} : Bool},
  ho: {D.Own(fi, nx, z) == True{} : Bool}, hm: {D.Mem(ps, z) == False{} : Bool},
  ha: D.IsK(dk, ds, m, im, fi, nx, ks, img, av, va), hb: D.Frs.bK(dk, ds, m, im, fi, nx, ks, img, bv, kind, vb),
  hf: D.FrsK(dk, ds, m, im, fi, nx, ks, img, ps, sp, fs)) ->
  D.FrsK(dk, ds, m, im, fi, nx, ks, img, ps, z, Con{D.AF{kind, q, False{}, va, vb}, fs}):
  match hok:
    case Tuple{htg, Tuple{hq, Tuple{hst, hk}}}:
      +ez = Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(m, z), Cr.Cir.Cell{hv, sp, av, bv, 0}, hz)
      (h0, (hc, (ho, ((%ez : {U32.is_ne(U32.and(Cr.Cir.Cell.get(0n, _), 1024), 0) == False{} : Bool}; hst), (hm,
        ((%ez : {U32.and(Cr.Cir.Cell.get(0n, _), 63) == D.FK.tag(kind) : U32}; htg),
        ((%ez : D.Qs(_, q); hq),
        ((%ez : {U32.is_ne(U32.and(Cr.Cir.Cell.get(0n, _), 2048), 0) == False{} : Bool}; hk),
        ((%ez : D.IsK(dk, ds, m, im, fi, nx, ks, img, Cr.Cir.Cell.get(2n, _), va); ha),
        ((%ez : D.Frs.bK(dk, ds, m, im, fi, nx, ks, img, Cr.Cir.Cell.get(3n, _), kind, vb); hb),
        (%ez : D.FrsK(dk, ds, m, im, fi, nx, ks, img, ps, Cr.Cir.Cell.get(1n, _), fs); hf)))))))))))

# A frame's cell
# --------------

# the term that a frame of the kind holds in field 3: Rwt's b
def UB(kind: D.FK, +bv: U32, vb: Bk.Term) -> List<&2, D.Rt>:
  match kind:
    case D.FK.arg{}:
      Nil{}
    case D.FK.val{}:
      Nil{}
    case D.FK.fun{}:
      Nil{}
    case D.FK.let{}:
      Nil{}
    case D.FK.tupb{}:
      Nil{}
    case D.FK.tupa{}:
      Nil{}
    case D.FK.rwt{}:
      [D.Rt{bv, vb}]
    case D.FK.minb{}:
      Nil{}
    case D.FK.mina{}:
      Nil{}

# the terms of UB, after a list: Frs.bK of field 3
def ub.frsb(kind: D.FK, +dk: Bool, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +bv: U32, +vb: Bk.Term,
  h: D.RtsK(dk, ds, m, im, fi, nx, ks, img, List.append(&2, D.Rt, List.append(&2, D.Rt, UB(kind, bv, vb), Nil{}), Nil{}))) ->
  D.Frs.bK(dk, ds, m, im, fi, nx, ks, img, bv, kind, vb):
  match kind:
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
    case D.FK.rwt{}:
      match h:
        case Tuple{i, _}:
          i
    case D.FK.minb{}:
      Unit{}
    case D.FK.mina{}:
      Unit{}

# a frame's tag is of the machine's kinds, not a term's
def fk.lo(kind: D.FK) -> {U32.is_le(32, D.FK.tag(kind)) == True{} : Bool}:
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

# the pointers of a frame's cell, out of the pend list: its field 2, and
# Rwt's field 3
def fs.frame(kind: D.FK, +m: Cr.Cir.Cells, +ps: List<&2, U32>, +z: U32, +hv: U32, +sp: U32, +yc: U32, +bv: U32, +vb: Bk.Term,
  hz: {Cr.Cir.Cells.get(m, z) == Cr.Cir.Cell{hv, sp, yc, bv, 0} : Cr.Cir.Cell}, htg: {D.TgW(hv) == D.FK.tag(kind) : U32},
  hm: {D.Mem(ps, z) == False{} : Bool}) ->
  {D.Fs(m, ps, z) == Con{yc, D.Rt.cells(UB(kind, bv, vb))} : List<&2, U32>}:
  match kind:
    case D.FK.arg{}:
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(m, z), Cr.Cir.Cell{hv, sp, yc, bv, 0}, hz) :
        {Bool.pick(List<&2, U32>, U32.is_lt(U32.and(Cr.Cir.Cell.get(0n, _), 63), 19),
            D.Fs.term(D.Fd(2n, m, U32.add(272, U32.and(Cr.Cir.Cell.get(0n, _), 63))), Cr.Cir.Cell.get(2n, _), Cr.Cir.Cell.get(3n, _), Cr.Cir.Cell.get(4n, _)),
            Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_le(32, U32.and(Cr.Cir.Cell.get(0n, _), 63)), U32.is_le(U32.and(Cr.Cir.Cell.get(0n, _), 63), 40)), Bool.not(D.Mem(ps, z))),
              Con{Cr.Cir.Cell.get(2n, _), D.Fs.opt(U32.is_eq(U32.and(Cr.Cir.Cell.get(0n, _), 63), 38), Cr.Cir.Cell.get(3n, _), Nil{})},
              Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_eq(U32.and(Cr.Cir.Cell.get(0n, _), 63), 41), D.FlW(Cr.Cir.Cell.get(0n, _), 4096)), Bool.not(D.Mem(ps, z))),
                [Cr.Cir.Cell.get(2n, _)], Nil{}))) == Con{yc, D.Rt.cells(UB(D.FK.arg{}, bv, vb))} : List<&2, U32>}
      %Equal.sym(U32, U32.and(hv, 63), 32, htg) :
        {Bool.pick(List<&2, U32>, U32.is_lt(_, 19), D.Fs.term(D.Fd(2n, m, U32.add(272, _)), yc, bv, 0),
          Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_le(32, _), U32.is_le(_, 40)), Bool.not(D.Mem(ps, z))),
            Con{yc, D.Fs.opt(U32.is_eq(_, 38), bv, Nil{})},
            Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_eq(_, 41), D.FlW(hv, 4096)), Bool.not(D.Mem(ps, z))), [yc], Nil{}))) ==
          Con{yc, D.Rt.cells(UB(D.FK.arg{}, bv, vb))} : List<&2, U32>}
      %Equal.sym(Bool, D.Mem(ps, z), False{}, hm) :
        {Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_le(32, 32), U32.is_le(32, 40)), Bool.not(_)),
            Con{yc, D.Fs.opt(U32.is_eq(32, 38), bv, Nil{})},
            Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_eq(32, 41), D.FlW(hv, 4096)), Bool.not(_)), [yc], Nil{})) ==
          Con{yc, D.Rt.cells(UB(D.FK.arg{}, bv, vb))} : List<&2, U32>}
      {==}
    case D.FK.val{}:
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(m, z), Cr.Cir.Cell{hv, sp, yc, bv, 0}, hz) :
        {Bool.pick(List<&2, U32>, U32.is_lt(U32.and(Cr.Cir.Cell.get(0n, _), 63), 19),
            D.Fs.term(D.Fd(2n, m, U32.add(272, U32.and(Cr.Cir.Cell.get(0n, _), 63))), Cr.Cir.Cell.get(2n, _), Cr.Cir.Cell.get(3n, _), Cr.Cir.Cell.get(4n, _)),
            Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_le(32, U32.and(Cr.Cir.Cell.get(0n, _), 63)), U32.is_le(U32.and(Cr.Cir.Cell.get(0n, _), 63), 40)), Bool.not(D.Mem(ps, z))),
              Con{Cr.Cir.Cell.get(2n, _), D.Fs.opt(U32.is_eq(U32.and(Cr.Cir.Cell.get(0n, _), 63), 38), Cr.Cir.Cell.get(3n, _), Nil{})},
              Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_eq(U32.and(Cr.Cir.Cell.get(0n, _), 63), 41), D.FlW(Cr.Cir.Cell.get(0n, _), 4096)), Bool.not(D.Mem(ps, z))),
                [Cr.Cir.Cell.get(2n, _)], Nil{}))) == Con{yc, D.Rt.cells(UB(D.FK.val{}, bv, vb))} : List<&2, U32>}
      %Equal.sym(U32, U32.and(hv, 63), 33, htg) :
        {Bool.pick(List<&2, U32>, U32.is_lt(_, 19), D.Fs.term(D.Fd(2n, m, U32.add(272, _)), yc, bv, 0),
          Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_le(32, _), U32.is_le(_, 40)), Bool.not(D.Mem(ps, z))),
            Con{yc, D.Fs.opt(U32.is_eq(_, 38), bv, Nil{})},
            Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_eq(_, 41), D.FlW(hv, 4096)), Bool.not(D.Mem(ps, z))), [yc], Nil{}))) ==
          Con{yc, D.Rt.cells(UB(D.FK.val{}, bv, vb))} : List<&2, U32>}
      %Equal.sym(Bool, D.Mem(ps, z), False{}, hm) :
        {Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_le(32, 33), U32.is_le(33, 40)), Bool.not(_)),
            Con{yc, D.Fs.opt(U32.is_eq(33, 38), bv, Nil{})},
            Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_eq(33, 41), D.FlW(hv, 4096)), Bool.not(_)), [yc], Nil{})) ==
          Con{yc, D.Rt.cells(UB(D.FK.val{}, bv, vb))} : List<&2, U32>}
      {==}
    case D.FK.fun{}:
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(m, z), Cr.Cir.Cell{hv, sp, yc, bv, 0}, hz) :
        {Bool.pick(List<&2, U32>, U32.is_lt(U32.and(Cr.Cir.Cell.get(0n, _), 63), 19),
            D.Fs.term(D.Fd(2n, m, U32.add(272, U32.and(Cr.Cir.Cell.get(0n, _), 63))), Cr.Cir.Cell.get(2n, _), Cr.Cir.Cell.get(3n, _), Cr.Cir.Cell.get(4n, _)),
            Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_le(32, U32.and(Cr.Cir.Cell.get(0n, _), 63)), U32.is_le(U32.and(Cr.Cir.Cell.get(0n, _), 63), 40)), Bool.not(D.Mem(ps, z))),
              Con{Cr.Cir.Cell.get(2n, _), D.Fs.opt(U32.is_eq(U32.and(Cr.Cir.Cell.get(0n, _), 63), 38), Cr.Cir.Cell.get(3n, _), Nil{})},
              Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_eq(U32.and(Cr.Cir.Cell.get(0n, _), 63), 41), D.FlW(Cr.Cir.Cell.get(0n, _), 4096)), Bool.not(D.Mem(ps, z))),
                [Cr.Cir.Cell.get(2n, _)], Nil{}))) == Con{yc, D.Rt.cells(UB(D.FK.fun{}, bv, vb))} : List<&2, U32>}
      %Equal.sym(U32, U32.and(hv, 63), 34, htg) :
        {Bool.pick(List<&2, U32>, U32.is_lt(_, 19), D.Fs.term(D.Fd(2n, m, U32.add(272, _)), yc, bv, 0),
          Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_le(32, _), U32.is_le(_, 40)), Bool.not(D.Mem(ps, z))),
            Con{yc, D.Fs.opt(U32.is_eq(_, 38), bv, Nil{})},
            Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_eq(_, 41), D.FlW(hv, 4096)), Bool.not(D.Mem(ps, z))), [yc], Nil{}))) ==
          Con{yc, D.Rt.cells(UB(D.FK.fun{}, bv, vb))} : List<&2, U32>}
      %Equal.sym(Bool, D.Mem(ps, z), False{}, hm) :
        {Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_le(32, 34), U32.is_le(34, 40)), Bool.not(_)),
            Con{yc, D.Fs.opt(U32.is_eq(34, 38), bv, Nil{})},
            Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_eq(34, 41), D.FlW(hv, 4096)), Bool.not(_)), [yc], Nil{})) ==
          Con{yc, D.Rt.cells(UB(D.FK.fun{}, bv, vb))} : List<&2, U32>}
      {==}
    case D.FK.let{}:
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(m, z), Cr.Cir.Cell{hv, sp, yc, bv, 0}, hz) :
        {Bool.pick(List<&2, U32>, U32.is_lt(U32.and(Cr.Cir.Cell.get(0n, _), 63), 19),
            D.Fs.term(D.Fd(2n, m, U32.add(272, U32.and(Cr.Cir.Cell.get(0n, _), 63))), Cr.Cir.Cell.get(2n, _), Cr.Cir.Cell.get(3n, _), Cr.Cir.Cell.get(4n, _)),
            Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_le(32, U32.and(Cr.Cir.Cell.get(0n, _), 63)), U32.is_le(U32.and(Cr.Cir.Cell.get(0n, _), 63), 40)), Bool.not(D.Mem(ps, z))),
              Con{Cr.Cir.Cell.get(2n, _), D.Fs.opt(U32.is_eq(U32.and(Cr.Cir.Cell.get(0n, _), 63), 38), Cr.Cir.Cell.get(3n, _), Nil{})},
              Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_eq(U32.and(Cr.Cir.Cell.get(0n, _), 63), 41), D.FlW(Cr.Cir.Cell.get(0n, _), 4096)), Bool.not(D.Mem(ps, z))),
                [Cr.Cir.Cell.get(2n, _)], Nil{}))) == Con{yc, D.Rt.cells(UB(D.FK.let{}, bv, vb))} : List<&2, U32>}
      %Equal.sym(U32, U32.and(hv, 63), 35, htg) :
        {Bool.pick(List<&2, U32>, U32.is_lt(_, 19), D.Fs.term(D.Fd(2n, m, U32.add(272, _)), yc, bv, 0),
          Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_le(32, _), U32.is_le(_, 40)), Bool.not(D.Mem(ps, z))),
            Con{yc, D.Fs.opt(U32.is_eq(_, 38), bv, Nil{})},
            Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_eq(_, 41), D.FlW(hv, 4096)), Bool.not(D.Mem(ps, z))), [yc], Nil{}))) ==
          Con{yc, D.Rt.cells(UB(D.FK.let{}, bv, vb))} : List<&2, U32>}
      %Equal.sym(Bool, D.Mem(ps, z), False{}, hm) :
        {Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_le(32, 35), U32.is_le(35, 40)), Bool.not(_)),
            Con{yc, D.Fs.opt(U32.is_eq(35, 38), bv, Nil{})},
            Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_eq(35, 41), D.FlW(hv, 4096)), Bool.not(_)), [yc], Nil{})) ==
          Con{yc, D.Rt.cells(UB(D.FK.let{}, bv, vb))} : List<&2, U32>}
      {==}
    case D.FK.tupb{}:
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(m, z), Cr.Cir.Cell{hv, sp, yc, bv, 0}, hz) :
        {Bool.pick(List<&2, U32>, U32.is_lt(U32.and(Cr.Cir.Cell.get(0n, _), 63), 19),
            D.Fs.term(D.Fd(2n, m, U32.add(272, U32.and(Cr.Cir.Cell.get(0n, _), 63))), Cr.Cir.Cell.get(2n, _), Cr.Cir.Cell.get(3n, _), Cr.Cir.Cell.get(4n, _)),
            Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_le(32, U32.and(Cr.Cir.Cell.get(0n, _), 63)), U32.is_le(U32.and(Cr.Cir.Cell.get(0n, _), 63), 40)), Bool.not(D.Mem(ps, z))),
              Con{Cr.Cir.Cell.get(2n, _), D.Fs.opt(U32.is_eq(U32.and(Cr.Cir.Cell.get(0n, _), 63), 38), Cr.Cir.Cell.get(3n, _), Nil{})},
              Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_eq(U32.and(Cr.Cir.Cell.get(0n, _), 63), 41), D.FlW(Cr.Cir.Cell.get(0n, _), 4096)), Bool.not(D.Mem(ps, z))),
                [Cr.Cir.Cell.get(2n, _)], Nil{}))) == Con{yc, D.Rt.cells(UB(D.FK.tupb{}, bv, vb))} : List<&2, U32>}
      %Equal.sym(U32, U32.and(hv, 63), 36, htg) :
        {Bool.pick(List<&2, U32>, U32.is_lt(_, 19), D.Fs.term(D.Fd(2n, m, U32.add(272, _)), yc, bv, 0),
          Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_le(32, _), U32.is_le(_, 40)), Bool.not(D.Mem(ps, z))),
            Con{yc, D.Fs.opt(U32.is_eq(_, 38), bv, Nil{})},
            Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_eq(_, 41), D.FlW(hv, 4096)), Bool.not(D.Mem(ps, z))), [yc], Nil{}))) ==
          Con{yc, D.Rt.cells(UB(D.FK.tupb{}, bv, vb))} : List<&2, U32>}
      %Equal.sym(Bool, D.Mem(ps, z), False{}, hm) :
        {Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_le(32, 36), U32.is_le(36, 40)), Bool.not(_)),
            Con{yc, D.Fs.opt(U32.is_eq(36, 38), bv, Nil{})},
            Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_eq(36, 41), D.FlW(hv, 4096)), Bool.not(_)), [yc], Nil{})) ==
          Con{yc, D.Rt.cells(UB(D.FK.tupb{}, bv, vb))} : List<&2, U32>}
      {==}
    case D.FK.tupa{}:
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(m, z), Cr.Cir.Cell{hv, sp, yc, bv, 0}, hz) :
        {Bool.pick(List<&2, U32>, U32.is_lt(U32.and(Cr.Cir.Cell.get(0n, _), 63), 19),
            D.Fs.term(D.Fd(2n, m, U32.add(272, U32.and(Cr.Cir.Cell.get(0n, _), 63))), Cr.Cir.Cell.get(2n, _), Cr.Cir.Cell.get(3n, _), Cr.Cir.Cell.get(4n, _)),
            Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_le(32, U32.and(Cr.Cir.Cell.get(0n, _), 63)), U32.is_le(U32.and(Cr.Cir.Cell.get(0n, _), 63), 40)), Bool.not(D.Mem(ps, z))),
              Con{Cr.Cir.Cell.get(2n, _), D.Fs.opt(U32.is_eq(U32.and(Cr.Cir.Cell.get(0n, _), 63), 38), Cr.Cir.Cell.get(3n, _), Nil{})},
              Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_eq(U32.and(Cr.Cir.Cell.get(0n, _), 63), 41), D.FlW(Cr.Cir.Cell.get(0n, _), 4096)), Bool.not(D.Mem(ps, z))),
                [Cr.Cir.Cell.get(2n, _)], Nil{}))) == Con{yc, D.Rt.cells(UB(D.FK.tupa{}, bv, vb))} : List<&2, U32>}
      %Equal.sym(U32, U32.and(hv, 63), 37, htg) :
        {Bool.pick(List<&2, U32>, U32.is_lt(_, 19), D.Fs.term(D.Fd(2n, m, U32.add(272, _)), yc, bv, 0),
          Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_le(32, _), U32.is_le(_, 40)), Bool.not(D.Mem(ps, z))),
            Con{yc, D.Fs.opt(U32.is_eq(_, 38), bv, Nil{})},
            Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_eq(_, 41), D.FlW(hv, 4096)), Bool.not(D.Mem(ps, z))), [yc], Nil{}))) ==
          Con{yc, D.Rt.cells(UB(D.FK.tupa{}, bv, vb))} : List<&2, U32>}
      %Equal.sym(Bool, D.Mem(ps, z), False{}, hm) :
        {Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_le(32, 37), U32.is_le(37, 40)), Bool.not(_)),
            Con{yc, D.Fs.opt(U32.is_eq(37, 38), bv, Nil{})},
            Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_eq(37, 41), D.FlW(hv, 4096)), Bool.not(_)), [yc], Nil{})) ==
          Con{yc, D.Rt.cells(UB(D.FK.tupa{}, bv, vb))} : List<&2, U32>}
      {==}
    case D.FK.rwt{}:
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(m, z), Cr.Cir.Cell{hv, sp, yc, bv, 0}, hz) :
        {Bool.pick(List<&2, U32>, U32.is_lt(U32.and(Cr.Cir.Cell.get(0n, _), 63), 19),
            D.Fs.term(D.Fd(2n, m, U32.add(272, U32.and(Cr.Cir.Cell.get(0n, _), 63))), Cr.Cir.Cell.get(2n, _), Cr.Cir.Cell.get(3n, _), Cr.Cir.Cell.get(4n, _)),
            Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_le(32, U32.and(Cr.Cir.Cell.get(0n, _), 63)), U32.is_le(U32.and(Cr.Cir.Cell.get(0n, _), 63), 40)), Bool.not(D.Mem(ps, z))),
              Con{Cr.Cir.Cell.get(2n, _), D.Fs.opt(U32.is_eq(U32.and(Cr.Cir.Cell.get(0n, _), 63), 38), Cr.Cir.Cell.get(3n, _), Nil{})},
              Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_eq(U32.and(Cr.Cir.Cell.get(0n, _), 63), 41), D.FlW(Cr.Cir.Cell.get(0n, _), 4096)), Bool.not(D.Mem(ps, z))),
                [Cr.Cir.Cell.get(2n, _)], Nil{}))) == Con{yc, D.Rt.cells(UB(D.FK.rwt{}, bv, vb))} : List<&2, U32>}
      %Equal.sym(U32, U32.and(hv, 63), 38, htg) :
        {Bool.pick(List<&2, U32>, U32.is_lt(_, 19), D.Fs.term(D.Fd(2n, m, U32.add(272, _)), yc, bv, 0),
          Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_le(32, _), U32.is_le(_, 40)), Bool.not(D.Mem(ps, z))),
            Con{yc, D.Fs.opt(U32.is_eq(_, 38), bv, Nil{})},
            Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_eq(_, 41), D.FlW(hv, 4096)), Bool.not(D.Mem(ps, z))), [yc], Nil{}))) ==
          Con{yc, D.Rt.cells(UB(D.FK.rwt{}, bv, vb))} : List<&2, U32>}
      %Equal.sym(Bool, D.Mem(ps, z), False{}, hm) :
        {Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_le(32, 38), U32.is_le(38, 40)), Bool.not(_)),
            Con{yc, D.Fs.opt(U32.is_eq(38, 38), bv, Nil{})},
            Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_eq(38, 41), D.FlW(hv, 4096)), Bool.not(_)), [yc], Nil{})) ==
          Con{yc, D.Rt.cells(UB(D.FK.rwt{}, bv, vb))} : List<&2, U32>}
      {==}
    case D.FK.minb{}:
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(m, z), Cr.Cir.Cell{hv, sp, yc, bv, 0}, hz) :
        {Bool.pick(List<&2, U32>, U32.is_lt(U32.and(Cr.Cir.Cell.get(0n, _), 63), 19),
            D.Fs.term(D.Fd(2n, m, U32.add(272, U32.and(Cr.Cir.Cell.get(0n, _), 63))), Cr.Cir.Cell.get(2n, _), Cr.Cir.Cell.get(3n, _), Cr.Cir.Cell.get(4n, _)),
            Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_le(32, U32.and(Cr.Cir.Cell.get(0n, _), 63)), U32.is_le(U32.and(Cr.Cir.Cell.get(0n, _), 63), 40)), Bool.not(D.Mem(ps, z))),
              Con{Cr.Cir.Cell.get(2n, _), D.Fs.opt(U32.is_eq(U32.and(Cr.Cir.Cell.get(0n, _), 63), 38), Cr.Cir.Cell.get(3n, _), Nil{})},
              Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_eq(U32.and(Cr.Cir.Cell.get(0n, _), 63), 41), D.FlW(Cr.Cir.Cell.get(0n, _), 4096)), Bool.not(D.Mem(ps, z))),
                [Cr.Cir.Cell.get(2n, _)], Nil{}))) == Con{yc, D.Rt.cells(UB(D.FK.minb{}, bv, vb))} : List<&2, U32>}
      %Equal.sym(U32, U32.and(hv, 63), 39, htg) :
        {Bool.pick(List<&2, U32>, U32.is_lt(_, 19), D.Fs.term(D.Fd(2n, m, U32.add(272, _)), yc, bv, 0),
          Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_le(32, _), U32.is_le(_, 40)), Bool.not(D.Mem(ps, z))),
            Con{yc, D.Fs.opt(U32.is_eq(_, 38), bv, Nil{})},
            Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_eq(_, 41), D.FlW(hv, 4096)), Bool.not(D.Mem(ps, z))), [yc], Nil{}))) ==
          Con{yc, D.Rt.cells(UB(D.FK.minb{}, bv, vb))} : List<&2, U32>}
      %Equal.sym(Bool, D.Mem(ps, z), False{}, hm) :
        {Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_le(32, 39), U32.is_le(39, 40)), Bool.not(_)),
            Con{yc, D.Fs.opt(U32.is_eq(39, 38), bv, Nil{})},
            Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_eq(39, 41), D.FlW(hv, 4096)), Bool.not(_)), [yc], Nil{})) ==
          Con{yc, D.Rt.cells(UB(D.FK.minb{}, bv, vb))} : List<&2, U32>}
      {==}
    case D.FK.mina{}:
      %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(m, z), Cr.Cir.Cell{hv, sp, yc, bv, 0}, hz) :
        {Bool.pick(List<&2, U32>, U32.is_lt(U32.and(Cr.Cir.Cell.get(0n, _), 63), 19),
            D.Fs.term(D.Fd(2n, m, U32.add(272, U32.and(Cr.Cir.Cell.get(0n, _), 63))), Cr.Cir.Cell.get(2n, _), Cr.Cir.Cell.get(3n, _), Cr.Cir.Cell.get(4n, _)),
            Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_le(32, U32.and(Cr.Cir.Cell.get(0n, _), 63)), U32.is_le(U32.and(Cr.Cir.Cell.get(0n, _), 63), 40)), Bool.not(D.Mem(ps, z))),
              Con{Cr.Cir.Cell.get(2n, _), D.Fs.opt(U32.is_eq(U32.and(Cr.Cir.Cell.get(0n, _), 63), 38), Cr.Cir.Cell.get(3n, _), Nil{})},
              Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_eq(U32.and(Cr.Cir.Cell.get(0n, _), 63), 41), D.FlW(Cr.Cir.Cell.get(0n, _), 4096)), Bool.not(D.Mem(ps, z))),
                [Cr.Cir.Cell.get(2n, _)], Nil{}))) == Con{yc, D.Rt.cells(UB(D.FK.mina{}, bv, vb))} : List<&2, U32>}
      %Equal.sym(U32, U32.and(hv, 63), 40, htg) :
        {Bool.pick(List<&2, U32>, U32.is_lt(_, 19), D.Fs.term(D.Fd(2n, m, U32.add(272, _)), yc, bv, 0),
          Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_le(32, _), U32.is_le(_, 40)), Bool.not(D.Mem(ps, z))),
            Con{yc, D.Fs.opt(U32.is_eq(_, 38), bv, Nil{})},
            Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_eq(_, 41), D.FlW(hv, 4096)), Bool.not(D.Mem(ps, z))), [yc], Nil{}))) ==
          Con{yc, D.Rt.cells(UB(D.FK.mina{}, bv, vb))} : List<&2, U32>}
      %Equal.sym(Bool, D.Mem(ps, z), False{}, hm) :
        {Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_le(32, 40), U32.is_le(40, 40)), Bool.not(_)),
            Con{yc, D.Fs.opt(U32.is_eq(40, 38), bv, Nil{})},
            Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_eq(40, 41), D.FlW(hv, 4096)), Bool.not(_)), [yc], Nil{})) ==
          Con{yc, D.Rt.cells(UB(D.FK.mina{}, bv, vb))} : List<&2, U32>}
      {==}

# a cell of zeros holds no pointer (the table's cell of the tag 0 has no part)
def fs.zero(+m: Cr.Cir.Cells, +ps: List<&2, U32>, +z: U32, hz: {Cr.Cir.Cells.get(m, z) == Cr.Cir.Cell.zero() : Cr.Cir.Cell},
  ht: {Cr.Cir.Cells.get(m, 272) == Cr.Cir.Cell{0, 0, 0, 0, 0} : Cr.Cir.Cell}) -> {D.Fs(m, ps, z) == Nil{} : List<&2, U32>}:
  %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(m, z), Cr.Cir.Cell.zero(), hz) :
    {Bool.pick(List<&2, U32>, U32.is_lt(U32.and(Cr.Cir.Cell.get(0n, _), 63), 19),
            D.Fs.term(D.Fd(2n, m, U32.add(272, U32.and(Cr.Cir.Cell.get(0n, _), 63))), Cr.Cir.Cell.get(2n, _), Cr.Cir.Cell.get(3n, _), Cr.Cir.Cell.get(4n, _)),
            Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_le(32, U32.and(Cr.Cir.Cell.get(0n, _), 63)), U32.is_le(U32.and(Cr.Cir.Cell.get(0n, _), 63), 40)), Bool.not(D.Mem(ps, z))),
              Con{Cr.Cir.Cell.get(2n, _), D.Fs.opt(U32.is_eq(U32.and(Cr.Cir.Cell.get(0n, _), 63), 38), Cr.Cir.Cell.get(3n, _), Nil{})},
              Bool.pick(List<&2, U32>, Bool.and(Bool.and(U32.is_eq(U32.and(Cr.Cir.Cell.get(0n, _), 63), 41), D.FlW(Cr.Cir.Cell.get(0n, _), 4096)), Bool.not(D.Mem(ps, z))),
                [Cr.Cir.Cell.get(2n, _)], Nil{}))) == Nil{} : List<&2, U32>}
  %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(m, 272), Cr.Cir.Cell{0, 0, 0, 0, 0}, ht) :
    {D.Fs.term(Cr.Cir.Cell.get(2n, _), 0, 0, 0) == Nil{} : List<&2, U32>}
  {==}

# the table's cell of the tag 0
def tbl.z(-m: Cr.Cir.Cells, -im: U32, -fi: U32, -nx: U32, h: D.Tbl(m, im, fi, nx)) ->
  {Cr.Cir.Cells.get(m, 272) == Cr.Cir.Cell{0, 0, 0, 0, 0} : Cr.Cir.Cell}:
  match h:
    case Tuple{_, Tuple{e, _}}:
      e

# a cell of zeros: not STATIC, of the tag 0
def zero.st(+m: Cr.Cir.Cells, +z: U32, hz: {Cr.Cir.Cells.get(m, z) == Cr.Cir.Cell.zero() : Cr.Cir.Cell}) ->
  {D.Fl(m, z, 1024) == False{} : Bool}:
  %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(m, z), Cr.Cir.Cell.zero(), hz) :
    {U32.is_ne(U32.and(Cr.Cir.Cell.get(0n, _), 1024), 0) == False{} : Bool}
  {==}

def zero.tg(+m: Cr.Cir.Cells, +z: U32, hz: {Cr.Cir.Cells.get(m, z) == Cr.Cir.Cell.zero() : Cr.Cir.Cell}) ->
  {Bool.or(U32.is_lt(D.Tg(m, z), 32), U32.is_le(41, D.Tg(m, z))) == True{} : Bool}:
  %Equal.sym(Cr.Cir.Cell, Cr.Cir.Cells.get(m, z), Cr.Cir.Cell.zero(), hz) :
    {Bool.or(U32.is_lt(U32.and(Cr.Cir.Cell.get(0n, _), 63), 32), U32.is_le(41, U32.and(Cr.Cir.Cell.get(0n, _), 63))) == True{} : Bool}
  {==}

# U32 order
def ne.lt.b(b: Bool, +o: U32, +z: U32, eb: {U32.is_eq(o, z) == b : Bool}, h: N.Le(1n+U32.to_nat(z), U32.to_nat(o))) ->
  {U32.is_eq(o, z) == False{} : Bool}:
  match b:
    case False{}:
      eb
    case True{}:
      +e = D.u32.eq(o, z, eb)
      Empty.absurd({U32.is_eq(o, z) == False{} : Bool}, N.not_succ_le(U32.to_nat(z), (%e : N.Le(1n+U32.to_nat(z), U32.to_nat(_)); h)))

# a cell past z is not z
def ne.lt(+o: U32, +z: U32, h: N.Le(1n+U32.to_nat(z), U32.to_nat(o))) -> {U32.is_eq(o, z) == False{} : Bool}:
  ne.lt.b(U32.is_eq(o, z), o, z, {==}, h)

# an own cell is not 0 (the image's cells come first, from 290)
def own.nz(+fi: U32, +nx: U32, +im: U32, +z: U32, h290: {U32.is_le(290, im) == True{} : Bool}, him: {U32.is_lt(im, fi) == True{} : Bool},
  ho: {D.Own(fi, nx, z) == True{} : Bool}) -> {U32.is_eq(z, 0) == False{} : Bool}:
  ne.lt(z, 0, N.le_trans(1n, U32.to_nat(fi), U32.to_nat(z),
    N.le_trans(1n, 1n+U32.to_nat(im), U32.to_nat(fi), N.le_zero(U32.to_nat(im)), D.u.lt(im, fi, him)),
    D.u.le(fi, z, D.and.l(U32.is_le(fi, z), U32.is_lt(z, nx), ho))))

# a cell of the machine's own is a cell
def own.cell(+fi: U32, +nx: U32, +im: U32, +z: U32, ho: {D.Own(fi, nx, z) == True{} : Bool}) ->
  {Cr.Cir.is_cell(z, im, fi, nx) == True{} : Bool}:
  D.or.r(Bool.and(Bool.not(U32.is_zero(z)), U32.is_le(z, im)), D.Own(fi, nx, z), ho)

# M.header of the kind k and the quantity of the cell in register c: Hd of
# its quantity q
def eh.q(+k: U32, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32,
  +inp: List<&2, Word(8n)>, +foc: U32, +f0: U32, +q: Bk.Quan, h8: {List.get(&2, U32, regs, 8n) == Some{foc} : Maybe<&2, U32>},
  hc: {Cr.Cir.is_cell(foc, im, fi, nx) == True{} : Bool}, hf: {D.Fd(0n, m, foc) == f0 : U32},
  hq: {D.QnW(f0) == Mc.Img.quan(q) : U32}) ->
  {Cr.Cir.eval(Mc.M.header(k, Mc.M.q(Mc.M.g(Mc.R.c())), Mc.M.c(0)), Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, Nil{}, 0}) ==
    Some{Hd(k, Mc.Img.quan(q))} : Maybe<&2, U32>}:
  +st = {Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, Nil{}, 0} : Cr.Cir.State}
  +f1 = D.Fd(0n, m, foc)
  +ef = X.ev.fld(0n, Mc.M.g(8n), st, foc, h8, hc)
  +esh = X.ev.op(Wa.Wasm.Op.shr_u{}, Mc.M.f(0n, Mc.M.g(8n)), Mc.M.c(6), st, f1, 6, ef, {==})
  +qv = Wa.Wasm.op(Wa.Wasm.Op.and{}, Wa.Wasm.op(Wa.Wasm.Op.shr_u{}, f1, 6), 3)
  +eand = X.ev.op(Wa.Wasm.Op.and{}, Mc.M.shr(Mc.M.f(0n, Mc.M.g(8n)), Mc.M.c(6)), Mc.M.c(3), st, Wa.Wasm.op(Wa.Wasm.Op.shr_u{}, f1, 6), 3, esh, {==})
  +eshl = X.ev.op(Wa.Wasm.Op.shl{}, Mc.M.q(Mc.M.g(8n)), Mc.M.c(6), st, qv, 6, eand, {==})
  +eor1 = X.ev.op(Wa.Wasm.Op.or{}, Mc.M.c(k), Mc.M.shl(Mc.M.q(Mc.M.g(8n)), Mc.M.c(6)), st, k, Wa.Wasm.op(Wa.Wasm.Op.shl{}, qv, 6), {==}, eshl)
  +eor2 = X.ev.op(Wa.Wasm.Op.or{}, Mc.M.or(Mc.M.c(k), Mc.M.shl(Mc.M.q(Mc.M.g(8n)), Mc.M.c(6))), Mc.M.c(0), st,
    Wa.Wasm.op(Wa.Wasm.Op.or{}, k, Wa.Wasm.op(Wa.Wasm.Op.shl{}, qv, 6)), 0, eor1, {==})
  Equal.trans(Maybe<&2, U32>, Cr.Cir.eval(Mc.M.header(k, Mc.M.q(Mc.M.g(Mc.R.c())), Mc.M.c(0)), st), Some{Hd(k, qv)}, Some{Hd(k, Mc.Img.quan(q))},
    eor2,
    Equal.trans(Maybe<&2, U32>, Some{Hd(k, qv)}, Some{Hd(k, D.QnW(f0))}, Some{Hd(k, Mc.Img.quan(q))},
      Equal.cong(U32, Maybe<&2, U32>, y => Some{Hd(k, D.QnW(y))}, f1, f0, hf),
      Equal.cong(U32, Maybe<&2, U32>, y => Some{Hd(k, y)}, D.QnW(f0), Mc.Img.quan(q), hq)))

# The accounting of a frame push
# ------------------------------

# Clo of no temporary
def clo.nil(n: Nat, +m: Cr.Cir.Cells, +c: U32, +ps: List<&2, U32>, +cs: List<&2, U32>, +hc: List<&2, U32>,
  h: {D.Clo(n, m, c, ps, cs, hc) == True{} : Bool}) -> {D.Clo(n, m, c, ps, Nil{}, Nil{}) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      +h2 = h
      +X = Bool.or(Bool.not(D.Fl(m, c, 1024)), D.All.static(D.Fs(m, ps, c), m))
      +Y = Bool.or(Bool.not(D.Mem(cs, c)), D.All.held(D.Fs(m, ps, c), m, cs, hc))
      +ha = D.and.l(Bool.and(X, Y), D.Clo(p, m, U32.inc(c), ps, cs, hc), h2)
      D.and.i(D.Clo.at(m, c, ps, Nil{}, Nil{}), D.Clo(p, m, U32.inc(c), ps, Nil{}, Nil{}),
        D.and.i(X, True{}, D.and.l(X, Y, ha), {==}),
        clo.nil(p, m, U32.inc(c), ps, cs, hc, D.and.r(Bool.and(X, Y), D.Clo(p, m, U32.inc(c), ps, cs, hc), h2)))

# the first two roots trade places (no temporary)
def acc.swap(+dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells,
  +nx: U32, +fi: U32, +im: U32, a: D.Rt, b: D.Rt, +os: List<&2, D.Rt>, +sp: U32, +fs: List<&2, D.AF>, +ps: List<&2, U32>,
  +zs: List<&2, D.Rt>, h: D.AccK(dk, ds, ks, img, m, nx, fi, im, Con{a, Con{b, os}}, Nil{}, sp, fs, ps, zs)) ->
  D.AccK(dk, ds, ks, img, m, nx, fi, im, Con{b, Con{a, os}}, Nil{}, sp, fs, ps, zs):
  match h:
    case Tuple{hz, Tuple{hh, Tuple{hc, Tuple{hcov, Tuple{hclo, _}}}}}:
      +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
      +C = List.append(&2, D.Rt, os, List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs))
      +XS = List.append(&2, U32, D.Fr.cells(fs, m, sp), ps)
      (hz, (hh, (hc, (Equal.trans(Bool, D.Cov(n, m, fi, Con{b, Con{a, C}}, XS), D.Cov(n, m, fi, Con{a, Con{b, C}}, XS), True{},
        Equal.sym(Bool, D.Cov(n, m, fi, Con{a, Con{b, C}}, XS), D.Cov(n, m, fi, Con{b, Con{a, C}}, XS), A.cov.perm(n, m, fi, Nil{}, [a], [b], C, XS)),
        hcov), (hclo, {==})))))

# the temporary z that holds the frame's terms becomes the top frame
def acc.frame(kind: D.FK, +dk: Bool, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +os: List<&2, D.Rt>, +z: U32, +yc: U32, +va: Bk.Term, +bv: U32, +vb: Bk.Term,
  +q: Bk.Quan, +sp: U32, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +zs: List<&2, D.Rt>,
  h1: {D.Fd(1n, m, z) == sp : U32}, h2: {D.Fd(2n, m, z) == yc : U32}, h3: {D.Fd(3n, m, z) == bv : U32},
  hz: D.RtsK(dk, ds, m, im, fi, nx, ks, img, zs), hc: {D.Rt.cells(zs) == D.Pend.terms(ps, m) : List<&2, U32>},
  hcov: {D.Cov(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, List.append(&2, D.Rt, os, List.append(&2, D.Rt,
    D.Tmp.held([D.TmpE{z, List.append(&2, D.Rt, Con{D.Rt{yc, va}, UB(kind, bv, vb)}, Nil{})}]), List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs))),
    List.append(&2, U32, D.Fr.cells(fs, m, sp), List.append(&2, U32, D.Tmp.cells([D.TmpE{z, List.append(&2, D.Rt, Con{D.Rt{yc, va}, UB(kind, bv, vb)}, Nil{})}]), ps))) == True{} : Bool},
  hclo: {D.Clo(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi, ps, D.Tmp.cells([D.TmpE{z, List.append(&2, D.Rt, Con{D.Rt{yc, va}, UB(kind, bv, vb)}, Nil{})}]),
    D.Rt.cells(D.Tmp.held([D.TmpE{z, List.append(&2, D.Rt, Con{D.Rt{yc, va}, UB(kind, bv, vb)}, Nil{})}]))) == True{} : Bool}) ->
  D.AccK(dk, ds, ks, img, m, nx, fi, im, os, Nil{}, z, Con{D.AF{kind, q, False{}, va, vb}, fs}, ps, zs):
  match kind:
    case D.FK.arg{}:
      +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
      +FC = D.Fr.cells(fs, m, sp)
      +cv = Equal.trans(Bool, D.Cov(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{yc, va}, List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)}), Con{z, List.append(&2, U32, FC, ps)}),
        D.Cov(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{yc, va}, List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)}), List.append(&2, U32, FC, Con{z, ps})), True{},
        Equal.sym(Bool, D.Cov(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{yc, va}, List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)}), List.append(&2, U32, FC, Con{z, ps})),
          D.Cov(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{yc, va}, List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)}), Con{z, List.append(&2, U32, FC, ps)}), A.cov.perm.x(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{yc, va}, List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)}), Nil{}, FC, [z], ps)), hcov)
      (hz, (Unit{}, (hc, ((%Equal.sym(U32, D.Fd(1n, m, z), sp, h1) : {D.Cov(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{D.Fd(2n, m, z), va}, List.append(&2, D.Rt, D.Fr.rts(fs, m, _), zs)}), Con{z, List.append(&2, U32, D.Fr.cells(fs, m, _), ps)}) == True{} : Bool};
        %Equal.sym(U32, D.Fd(2n, m, z), yc, h2) : {D.Cov(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{_, va}, List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)}), Con{z, List.append(&2, U32, D.Fr.cells(fs, m, sp), ps)}) == True{} : Bool};
        cv), (clo.nil(n, m, fi, ps, [z], [yc], hclo), {==})))))
    case D.FK.val{}:
      +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
      +FC = D.Fr.cells(fs, m, sp)
      +cv = Equal.trans(Bool, D.Cov(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{yc, va}, List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)}), Con{z, List.append(&2, U32, FC, ps)}),
        D.Cov(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{yc, va}, List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)}), List.append(&2, U32, FC, Con{z, ps})), True{},
        Equal.sym(Bool, D.Cov(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{yc, va}, List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)}), List.append(&2, U32, FC, Con{z, ps})),
          D.Cov(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{yc, va}, List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)}), Con{z, List.append(&2, U32, FC, ps)}), A.cov.perm.x(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{yc, va}, List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)}), Nil{}, FC, [z], ps)), hcov)
      (hz, (Unit{}, (hc, ((%Equal.sym(U32, D.Fd(1n, m, z), sp, h1) : {D.Cov(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{D.Fd(2n, m, z), va}, List.append(&2, D.Rt, D.Fr.rts(fs, m, _), zs)}), Con{z, List.append(&2, U32, D.Fr.cells(fs, m, _), ps)}) == True{} : Bool};
        %Equal.sym(U32, D.Fd(2n, m, z), yc, h2) : {D.Cov(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{_, va}, List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)}), Con{z, List.append(&2, U32, D.Fr.cells(fs, m, sp), ps)}) == True{} : Bool};
        cv), (clo.nil(n, m, fi, ps, [z], [yc], hclo), {==})))))
    case D.FK.fun{}:
      +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
      +FC = D.Fr.cells(fs, m, sp)
      +cv = Equal.trans(Bool, D.Cov(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{yc, va}, List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)}), Con{z, List.append(&2, U32, FC, ps)}),
        D.Cov(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{yc, va}, List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)}), List.append(&2, U32, FC, Con{z, ps})), True{},
        Equal.sym(Bool, D.Cov(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{yc, va}, List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)}), List.append(&2, U32, FC, Con{z, ps})),
          D.Cov(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{yc, va}, List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)}), Con{z, List.append(&2, U32, FC, ps)}), A.cov.perm.x(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{yc, va}, List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)}), Nil{}, FC, [z], ps)), hcov)
      (hz, (Unit{}, (hc, ((%Equal.sym(U32, D.Fd(1n, m, z), sp, h1) : {D.Cov(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{D.Fd(2n, m, z), va}, List.append(&2, D.Rt, D.Fr.rts(fs, m, _), zs)}), Con{z, List.append(&2, U32, D.Fr.cells(fs, m, _), ps)}) == True{} : Bool};
        %Equal.sym(U32, D.Fd(2n, m, z), yc, h2) : {D.Cov(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{_, va}, List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)}), Con{z, List.append(&2, U32, D.Fr.cells(fs, m, sp), ps)}) == True{} : Bool};
        cv), (clo.nil(n, m, fi, ps, [z], [yc], hclo), {==})))))
    case D.FK.let{}:
      +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
      +FC = D.Fr.cells(fs, m, sp)
      +cv = Equal.trans(Bool, D.Cov(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{yc, va}, List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)}), Con{z, List.append(&2, U32, FC, ps)}),
        D.Cov(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{yc, va}, List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)}), List.append(&2, U32, FC, Con{z, ps})), True{},
        Equal.sym(Bool, D.Cov(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{yc, va}, List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)}), List.append(&2, U32, FC, Con{z, ps})),
          D.Cov(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{yc, va}, List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)}), Con{z, List.append(&2, U32, FC, ps)}), A.cov.perm.x(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{yc, va}, List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)}), Nil{}, FC, [z], ps)), hcov)
      (hz, (Unit{}, (hc, ((%Equal.sym(U32, D.Fd(1n, m, z), sp, h1) : {D.Cov(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{D.Fd(2n, m, z), va}, List.append(&2, D.Rt, D.Fr.rts(fs, m, _), zs)}), Con{z, List.append(&2, U32, D.Fr.cells(fs, m, _), ps)}) == True{} : Bool};
        %Equal.sym(U32, D.Fd(2n, m, z), yc, h2) : {D.Cov(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{_, va}, List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)}), Con{z, List.append(&2, U32, D.Fr.cells(fs, m, sp), ps)}) == True{} : Bool};
        cv), (clo.nil(n, m, fi, ps, [z], [yc], hclo), {==})))))
    case D.FK.tupb{}:
      +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
      +FC = D.Fr.cells(fs, m, sp)
      +cv = Equal.trans(Bool, D.Cov(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{yc, va}, List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)}), Con{z, List.append(&2, U32, FC, ps)}),
        D.Cov(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{yc, va}, List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)}), List.append(&2, U32, FC, Con{z, ps})), True{},
        Equal.sym(Bool, D.Cov(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{yc, va}, List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)}), List.append(&2, U32, FC, Con{z, ps})),
          D.Cov(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{yc, va}, List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)}), Con{z, List.append(&2, U32, FC, ps)}), A.cov.perm.x(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{yc, va}, List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)}), Nil{}, FC, [z], ps)), hcov)
      (hz, (Unit{}, (hc, ((%Equal.sym(U32, D.Fd(1n, m, z), sp, h1) : {D.Cov(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{D.Fd(2n, m, z), va}, List.append(&2, D.Rt, D.Fr.rts(fs, m, _), zs)}), Con{z, List.append(&2, U32, D.Fr.cells(fs, m, _), ps)}) == True{} : Bool};
        %Equal.sym(U32, D.Fd(2n, m, z), yc, h2) : {D.Cov(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{_, va}, List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)}), Con{z, List.append(&2, U32, D.Fr.cells(fs, m, sp), ps)}) == True{} : Bool};
        cv), (clo.nil(n, m, fi, ps, [z], [yc], hclo), {==})))))
    case D.FK.tupa{}:
      +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
      +FC = D.Fr.cells(fs, m, sp)
      +cv = Equal.trans(Bool, D.Cov(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{yc, va}, List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)}), Con{z, List.append(&2, U32, FC, ps)}),
        D.Cov(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{yc, va}, List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)}), List.append(&2, U32, FC, Con{z, ps})), True{},
        Equal.sym(Bool, D.Cov(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{yc, va}, List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)}), List.append(&2, U32, FC, Con{z, ps})),
          D.Cov(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{yc, va}, List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)}), Con{z, List.append(&2, U32, FC, ps)}), A.cov.perm.x(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{yc, va}, List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)}), Nil{}, FC, [z], ps)), hcov)
      (hz, (Unit{}, (hc, ((%Equal.sym(U32, D.Fd(1n, m, z), sp, h1) : {D.Cov(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{D.Fd(2n, m, z), va}, List.append(&2, D.Rt, D.Fr.rts(fs, m, _), zs)}), Con{z, List.append(&2, U32, D.Fr.cells(fs, m, _), ps)}) == True{} : Bool};
        %Equal.sym(U32, D.Fd(2n, m, z), yc, h2) : {D.Cov(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{_, va}, List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)}), Con{z, List.append(&2, U32, D.Fr.cells(fs, m, sp), ps)}) == True{} : Bool};
        cv), (clo.nil(n, m, fi, ps, [z], [yc], hclo), {==})))))
    case D.FK.rwt{}:
      +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
      +FC = D.Fr.cells(fs, m, sp)
      +cv = Equal.trans(Bool, D.Cov(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{yc, va}, Con{D.Rt{bv, vb}, List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)}}), Con{z, List.append(&2, U32, FC, ps)}),
        D.Cov(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{yc, va}, Con{D.Rt{bv, vb}, List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)}}), List.append(&2, U32, FC, Con{z, ps})), True{},
        Equal.sym(Bool, D.Cov(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{yc, va}, Con{D.Rt{bv, vb}, List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)}}), List.append(&2, U32, FC, Con{z, ps})),
          D.Cov(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{yc, va}, Con{D.Rt{bv, vb}, List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)}}), Con{z, List.append(&2, U32, FC, ps)}), A.cov.perm.x(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{yc, va}, Con{D.Rt{bv, vb}, List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)}}), Nil{}, FC, [z], ps)), hcov)
      (hz, (Unit{}, (hc, ((%Equal.sym(U32, D.Fd(1n, m, z), sp, h1) : {D.Cov(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{D.Fd(2n, m, z), va}, Con{D.Rt{D.Fd(3n, m, z), vb}, List.append(&2, D.Rt, D.Fr.rts(fs, m, _), zs)}}), Con{z, List.append(&2, U32, D.Fr.cells(fs, m, _), ps)}) == True{} : Bool};
        %Equal.sym(U32, D.Fd(2n, m, z), yc, h2) : {D.Cov(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{_, va}, Con{D.Rt{D.Fd(3n, m, z), vb}, List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)}}), Con{z, List.append(&2, U32, D.Fr.cells(fs, m, sp), ps)}) == True{} : Bool};
        %Equal.sym(U32, D.Fd(3n, m, z), bv, h3) : {D.Cov(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{yc, va}, Con{D.Rt{_, vb}, List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)}}), Con{z, List.append(&2, U32, D.Fr.cells(fs, m, sp), ps)}) == True{} : Bool};
        cv), (clo.nil(n, m, fi, ps, [z], [yc, bv], hclo), {==})))))
    case D.FK.minb{}:
      +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
      +FC = D.Fr.cells(fs, m, sp)
      +cv = Equal.trans(Bool, D.Cov(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{yc, va}, List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)}), Con{z, List.append(&2, U32, FC, ps)}),
        D.Cov(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{yc, va}, List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)}), List.append(&2, U32, FC, Con{z, ps})), True{},
        Equal.sym(Bool, D.Cov(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{yc, va}, List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)}), List.append(&2, U32, FC, Con{z, ps})),
          D.Cov(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{yc, va}, List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)}), Con{z, List.append(&2, U32, FC, ps)}), A.cov.perm.x(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{yc, va}, List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)}), Nil{}, FC, [z], ps)), hcov)
      (hz, (Unit{}, (hc, ((%Equal.sym(U32, D.Fd(1n, m, z), sp, h1) : {D.Cov(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{D.Fd(2n, m, z), va}, List.append(&2, D.Rt, D.Fr.rts(fs, m, _), zs)}), Con{z, List.append(&2, U32, D.Fr.cells(fs, m, _), ps)}) == True{} : Bool};
        %Equal.sym(U32, D.Fd(2n, m, z), yc, h2) : {D.Cov(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{_, va}, List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)}), Con{z, List.append(&2, U32, D.Fr.cells(fs, m, sp), ps)}) == True{} : Bool};
        cv), (clo.nil(n, m, fi, ps, [z], [yc], hclo), {==})))))
    case D.FK.mina{}:
      +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
      +FC = D.Fr.cells(fs, m, sp)
      +cv = Equal.trans(Bool, D.Cov(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{yc, va}, List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)}), Con{z, List.append(&2, U32, FC, ps)}),
        D.Cov(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{yc, va}, List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)}), List.append(&2, U32, FC, Con{z, ps})), True{},
        Equal.sym(Bool, D.Cov(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{yc, va}, List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)}), List.append(&2, U32, FC, Con{z, ps})),
          D.Cov(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{yc, va}, List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)}), Con{z, List.append(&2, U32, FC, ps)}), A.cov.perm.x(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{yc, va}, List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)}), Nil{}, FC, [z], ps)), hcov)
      (hz, (Unit{}, (hc, ((%Equal.sym(U32, D.Fd(1n, m, z), sp, h1) : {D.Cov(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{D.Fd(2n, m, z), va}, List.append(&2, D.Rt, D.Fr.rts(fs, m, _), zs)}), Con{z, List.append(&2, U32, D.Fr.cells(fs, m, _), ps)}) == True{} : Bool};
        %Equal.sym(U32, D.Fd(2n, m, z), yc, h2) : {D.Cov(n, m, fi, List.append(&2, D.Rt, os, Con{D.Rt{_, va}, List.append(&2, D.Rt, D.Fr.rts(fs, m, sp), zs)}), Con{z, List.append(&2, U32, D.Fr.cells(fs, m, sp), ps)}) == True{} : Bool};
        cv), (clo.nil(n, m, fi, ps, [z], [yc], hclo), {==})))))

# Runs that end, runs with no new cell
# ------------------------------------
#
# A statement with no while ends with any fuel (NW, ends.nw); one with no
# alloc, no emit and no while never runs out of memory (NA, noom.na).

def NW(s: Cr.Cir.Stmt) -> Bool:
  match s:
    case Cr.Cir.Stmt.nop{}:
      True{}
    case Cr.Cir.Stmt.set{_, _}:
      True{}
    case Cr.Cir.Stmt.store{_, _, _}:
      True{}
    case Cr.Cir.Stmt.alloc{_}:
      True{}
    case Cr.Cir.Stmt.emit{_}:
      False{}
    case Cr.Cir.Stmt.seq{a, b}:
      Bool.and(NW(a), NW(b))
    case Cr.Cir.Stmt.if{_, a, b}:
      Bool.and(NW(a), NW(b))
    case Cr.Cir.Stmt.while{_, _}:
      False{}
    case Cr.Cir.Stmt.halt{_}:
      True{}

def NA(s: Cr.Cir.Stmt) -> Bool:
  match s:
    case Cr.Cir.Stmt.nop{}:
      True{}
    case Cr.Cir.Stmt.set{_, _}:
      True{}
    case Cr.Cir.Stmt.store{_, _, _}:
      True{}
    case Cr.Cir.Stmt.alloc{_}:
      False{}
    case Cr.Cir.Stmt.emit{_}:
      False{}
    case Cr.Cir.Stmt.seq{a, b}:
      Bool.and(NA(a), NA(b))
    case Cr.Cir.Stmt.if{_, a, b}:
      Bool.and(NA(a), NA(b))
    case Cr.Cir.Stmt.while{_, _}:
      False{}
    case Cr.Cir.Stmt.halt{_}:
      True{}

# an outcome that ends and does not run out of memory
def Calm(o: Cr.Cir.Out) -> Data:
  D.P2(D.Ends(o), D.NoOom(o))

def calm.set.of(regs: Maybe<&2, List<&2, U32>>, st: Cr.Cir.State) -> Calm(Cr.Cir.exec.set.of(regs, st)):
  match regs st:
    case Some{_} Cr.Cir.State{_, _, _, _, _, _, _, _, _, _}:
      (Unit{}, Unit{})
    case None{} _:
      (Unit{}, Unit{})

def calm.set(r: Nat, v: Maybe<&2, U32>, +st: Cr.Cir.State) -> Calm(Cr.Cir.exec.set(r, v, st)):
  match v st:
    case Some{+x} Cr.Cir.State{+regs, +m, +nx, +fi, +im, +pg, +lim, +inp, +out, +outn}:
      calm.set.of(Cr.Cir.regs.set(regs, r, x), Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, out, outn})
    case None{} _:
      (Unit{}, Unit{})

def calm.store.if(ok: Bool, k: Nat, +i: U32, v: U32, st: Cr.Cir.State) -> Calm(Cr.Cir.exec.store.if(ok, k, i, v, st)):
  match ok st:
    case True{} Cr.Cir.State{_, _, _, _, _, _, _, _, _, _}:
      (Unit{}, Unit{})
    case False{} _:
      (Unit{}, Unit{})

def calm.store(k: Nat, c: Maybe<&2, U32>, v: Maybe<&2, U32>, +st: Cr.Cir.State) -> Calm(Cr.Cir.exec.store(k, c, v, st)):
  match c v st:
    case Some{+i} Some{+x} Cr.Cir.State{+regs, +m, +nx, +fi, +im, +pg, +lim, +inp, +out, +outn}:
      calm.store.if(Cr.Cir.is_cell(i, im, fi, nx), k, i, x, Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, out, outn})
    case Some{_} None{} _:
      (Unit{}, Unit{})
    case None{} _ _:
      (Unit{}, Unit{})

def ends.then(o: Cr.Cir.Out, -k: Cr.Cir.State -> Cr.Cir.Out, d: D.Ends(o), g: @st: Cr.Cir.State -> D.Ends(k(st))) ->
  D.Ends(Cr.Cir.exec.then(o, k)):
  match o:
    case Cr.Cir.Out.next{st}:
      g(st)
    case Cr.Cir.Out.halt{_, _}:
      Unit{}
    case Cr.Cir.Out.out_of_memory{}:
      Unit{}
    case Cr.Cir.Out.trap{}:
      Unit{}
    case Cr.Cir.Out.not_done{}:
      d

def noom.then(o: Cr.Cir.Out, -k: Cr.Cir.State -> Cr.Cir.Out, d: D.NoOom(o), g: @st: Cr.Cir.State -> D.NoOom(k(st))) ->
  D.NoOom(Cr.Cir.exec.then(o, k)):
  match o:
    case Cr.Cir.Out.next{st}:
      g(st)
    case Cr.Cir.Out.halt{_, _}:
      Unit{}
    case Cr.Cir.Out.out_of_memory{}:
      d
    case Cr.Cir.Out.trap{}:
      Unit{}
    case Cr.Cir.Out.not_done{}:
      Unit{}

def ends.if.of(zero: Bool, -yes: Unit -> Cr.Cir.Out, -no: Unit -> Cr.Cir.Out, dy: D.Ends(yes(Unit{})), dn: D.Ends(no(Unit{}))) ->
  D.Ends(Cr.Cir.exec.if.of(zero, yes, no)):
  match zero:
    case False{}:
      dy
    case True{}:
      dn

def ends.if(c: Maybe<&2, U32>, -yes: Unit -> Cr.Cir.Out, -no: Unit -> Cr.Cir.Out, dy: D.Ends(yes(Unit{})), dn: D.Ends(no(Unit{}))) ->
  D.Ends(Cr.Cir.exec.if(c, yes, no)):
  match c:
    case Some{x}:
      ends.if.of(U32.is_zero(x), yes, no, dy, dn)
    case None{}:
      Unit{}

def noom.if.of(zero: Bool, -yes: Unit -> Cr.Cir.Out, -no: Unit -> Cr.Cir.Out, dy: D.NoOom(yes(Unit{})), dn: D.NoOom(no(Unit{}))) ->
  D.NoOom(Cr.Cir.exec.if.of(zero, yes, no)):
  match zero:
    case False{}:
      dy
    case True{}:
      dn

def noom.if(c: Maybe<&2, U32>, -yes: Unit -> Cr.Cir.Out, -no: Unit -> Cr.Cir.Out, dy: D.NoOom(yes(Unit{})), dn: D.NoOom(no(Unit{}))) ->
  D.NoOom(Cr.Cir.exec.if(c, yes, no)):
  match c:
    case Some{x}:
      noom.if.of(U32.is_zero(x), yes, no, dy, dn)
    case None{}:
      Unit{}

def ends.took(r: Nat, +i: U32, st: Cr.Cir.State, next: U32, pages: U32) -> D.Ends(Cr.Cir.exec.took(r, i, st, next, pages)):
  match st:
    case Cr.Cir.State{+regs, +m, _, +fi, +im, _, +lim, +inp, +out, +outn}:
      D.Ex.fst(D.Ends(Cr.Cir.exec.set(r, Some{i}, Cr.Cir.State{regs, Cr.Cir.Cells.set(m, i, Cr.Cir.Cell.zero()), next, fi, im, pages, lim, inp, out, outn})),
        _ => D.NoOom(Cr.Cir.exec.set(r, Some{i}, Cr.Cir.State{regs, Cr.Cir.Cells.set(m, i, Cr.Cir.Cell.zero()), next, fi, im, pages, lim, inp, out, outn})),
        calm.set(r, Some{i}, Cr.Cir.State{regs, Cr.Cir.Cells.set(m, i, Cr.Cir.Cell.zero()), next, fi, im, pages, lim, inp, out, outn}))

def ends.bump.of(r: Nat, +next: U32, st: Cr.Cir.State, pages: Maybe<&2, U32>) -> D.Ends(Cr.Cir.exec.bump.of(r, next, st, pages)):
  match pages:
    case Some{p}:
      ends.took(r, next, st, U32.inc(next), p)
    case None{}:
      Unit{}

def ends.bump.if(fits: Bool, r: Nat, +next: U32, +pages: U32, lim: U32, st: Cr.Cir.State) -> D.Ends(Cr.Cir.exec.bump.if(fits, r, next, pages, lim, st)):
  match fits:
    case True{}:
      ends.bump.of(r, next, st, Cr.Cir.room(U32.add(Cr.Cir.at(next), 19), pages, lim))
    case False{}:
      Unit{}

def ends.alloc.if(no_out: Bool, r: Nat, +st: Cr.Cir.State) -> D.Ends(Cr.Cir.exec.alloc.if(no_out, r, st)):
  match no_out st:
    case True{} Cr.Cir.State{+regs, +m, +nx, +fi, +im, +pg, +lim, +inp, +out, +outn}:
      ends.bump.if(U32.is_lt(nx, 214748364), r, nx, pg, lim, Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, out, outn})
    case False{} _:
      Unit{}

def ends.alloc(r: Nat, +st: Cr.Cir.State) -> D.Ends(Cr.Cir.exec.alloc(r, st)):
  match st:
    case Cr.Cir.State{+regs, +m, +nx, +fi, +im, +pg, +lim, +inp, +out, +outn}:
      ends.alloc.if(U32.is_zero(outn), r, Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, out, outn})

# a statement with no while ends
def ends.nw(+f: Nat, s: Cr.Cir.Stmt, +st: Cr.Cir.State, +h: {NW(s) == True{} : Bool}) -> D.Ends(Cr.Cir.exec(f, s, st)):
  match f:
    case 0n:
      match s:
        case Cr.Cir.Stmt.nop{}:
          Unit{}
        case Cr.Cir.Stmt.set{+r, +e}:
          D.Ex.fst(D.Ends(Cr.Cir.exec.set(r, Cr.Cir.eval(e, st), st)), _ => D.NoOom(Cr.Cir.exec.set(r, Cr.Cir.eval(e, st), st)),
            calm.set(r, Cr.Cir.eval(e, st), st))
        case Cr.Cir.Stmt.store{+k, +c, +v}:
          D.Ex.fst(D.Ends(Cr.Cir.exec.store(k, Cr.Cir.eval(c, st), Cr.Cir.eval(v, st), st)),
            _ => D.NoOom(Cr.Cir.exec.store(k, Cr.Cir.eval(c, st), Cr.Cir.eval(v, st), st)),
            calm.store(k, Cr.Cir.eval(c, st), Cr.Cir.eval(v, st), st))
        case Cr.Cir.Stmt.alloc{r}:
          ends.alloc(r, st)
        case Cr.Cir.Stmt.emit{v}:
          D.bool.ft(D.Ends(Cr.Cir.exec(0n, Cr.Cir.Stmt.emit{v}, st)), h)
        case Cr.Cir.Stmt.seq{+a, +b}:
          +ha = D.and.l(NW(a), NW(b), h)
          +hb = D.and.r(NW(a), NW(b), h)
          ends.then(Cr.Cir.exec(0n, a, st), t => Cr.Cir.exec(0n, b, t), ends.nw(0n, a, st, ha), t => ends.nw(0n, b, t, hb))
        case Cr.Cir.Stmt.if{+c, +a, +b}:
          +ha = D.and.l(NW(a), NW(b), h)
          +hb = D.and.r(NW(a), NW(b), h)
          ends.if(Cr.Cir.eval(c, st), u => Cr.Cir.exec(0n, a, st), u => Cr.Cir.exec(0n, b, st), ends.nw(0n, a, st, ha), ends.nw(0n, b, st, hb))
        case Cr.Cir.Stmt.while{c, b}:
          D.bool.ft(D.Ends(Cr.Cir.exec(0n, Cr.Cir.Stmt.while{c, b}, st)), h)
        case Cr.Cir.Stmt.halt{_}:
          Unit{}
    case 1n+g:
      match s:
        case Cr.Cir.Stmt.nop{}:
          Unit{}
        case Cr.Cir.Stmt.set{+r, +e}:
          D.Ex.fst(D.Ends(Cr.Cir.exec.set(r, Cr.Cir.eval(e, st), st)), _ => D.NoOom(Cr.Cir.exec.set(r, Cr.Cir.eval(e, st), st)),
            calm.set(r, Cr.Cir.eval(e, st), st))
        case Cr.Cir.Stmt.store{+k, +c, +v}:
          D.Ex.fst(D.Ends(Cr.Cir.exec.store(k, Cr.Cir.eval(c, st), Cr.Cir.eval(v, st), st)),
            _ => D.NoOom(Cr.Cir.exec.store(k, Cr.Cir.eval(c, st), Cr.Cir.eval(v, st), st)),
            calm.store(k, Cr.Cir.eval(c, st), Cr.Cir.eval(v, st), st))
        case Cr.Cir.Stmt.alloc{r}:
          ends.alloc(r, st)
        case Cr.Cir.Stmt.emit{v}:
          D.bool.ft(D.Ends(Cr.Cir.exec(1n+g, Cr.Cir.Stmt.emit{v}, st)), h)
        case Cr.Cir.Stmt.seq{+a, +b}:
          +ha = D.and.l(NW(a), NW(b), h)
          +hb = D.and.r(NW(a), NW(b), h)
          ends.then(Cr.Cir.exec(1n+g, a, st), t => Cr.Cir.exec(1n+g, b, t), ends.nw(1n+g, a, st, ha), t => ends.nw(1n+g, b, t, hb))
        case Cr.Cir.Stmt.if{+c, +a, +b}:
          +ha = D.and.l(NW(a), NW(b), h)
          +hb = D.and.r(NW(a), NW(b), h)
          ends.if(Cr.Cir.eval(c, st), u => Cr.Cir.exec(1n+g, a, st), u => Cr.Cir.exec(1n+g, b, st), ends.nw(1n+g, a, st, ha),
            ends.nw(1n+g, b, st, hb))
        case Cr.Cir.Stmt.while{c, b}:
          D.bool.ft(D.Ends(Cr.Cir.exec(1n+g, Cr.Cir.Stmt.while{c, b}, st)), h)
        case Cr.Cir.Stmt.halt{_}:
          Unit{}

# a statement with no alloc, emit or while never runs out of memory
def noom.na(+f: Nat, s: Cr.Cir.Stmt, +st: Cr.Cir.State, +h: {NA(s) == True{} : Bool}) -> D.NoOom(Cr.Cir.exec(f, s, st)):
  match f:
    case 0n:
      match s:
        case Cr.Cir.Stmt.nop{}:
          Unit{}
        case Cr.Cir.Stmt.set{+r, +e}:
          D.Ex.snd(D.Ends(Cr.Cir.exec.set(r, Cr.Cir.eval(e, st), st)), _ => D.NoOom(Cr.Cir.exec.set(r, Cr.Cir.eval(e, st), st)),
            calm.set(r, Cr.Cir.eval(e, st), st))
        case Cr.Cir.Stmt.store{+k, +c, +v}:
          D.Ex.snd(D.Ends(Cr.Cir.exec.store(k, Cr.Cir.eval(c, st), Cr.Cir.eval(v, st), st)),
            _ => D.NoOom(Cr.Cir.exec.store(k, Cr.Cir.eval(c, st), Cr.Cir.eval(v, st), st)),
            calm.store(k, Cr.Cir.eval(c, st), Cr.Cir.eval(v, st), st))
        case Cr.Cir.Stmt.alloc{r}:
          D.bool.ft(D.NoOom(Cr.Cir.exec(0n, Cr.Cir.Stmt.alloc{r}, st)), h)
        case Cr.Cir.Stmt.emit{v}:
          D.bool.ft(D.NoOom(Cr.Cir.exec(0n, Cr.Cir.Stmt.emit{v}, st)), h)
        case Cr.Cir.Stmt.seq{+a, +b}:
          +ha = D.and.l(NA(a), NA(b), h)
          +hb = D.and.r(NA(a), NA(b), h)
          noom.then(Cr.Cir.exec(0n, a, st), t => Cr.Cir.exec(0n, b, t), noom.na(0n, a, st, ha), t => noom.na(0n, b, t, hb))
        case Cr.Cir.Stmt.if{+c, +a, +b}:
          +ha = D.and.l(NA(a), NA(b), h)
          +hb = D.and.r(NA(a), NA(b), h)
          noom.if(Cr.Cir.eval(c, st), u => Cr.Cir.exec(0n, a, st), u => Cr.Cir.exec(0n, b, st), noom.na(0n, a, st, ha), noom.na(0n, b, st, hb))
        case Cr.Cir.Stmt.while{c, b}:
          D.bool.ft(D.NoOom(Cr.Cir.exec(0n, Cr.Cir.Stmt.while{c, b}, st)), h)
        case Cr.Cir.Stmt.halt{_}:
          Unit{}
    case 1n+g:
      match s:
        case Cr.Cir.Stmt.nop{}:
          Unit{}
        case Cr.Cir.Stmt.set{+r, +e}:
          D.Ex.snd(D.Ends(Cr.Cir.exec.set(r, Cr.Cir.eval(e, st), st)), _ => D.NoOom(Cr.Cir.exec.set(r, Cr.Cir.eval(e, st), st)),
            calm.set(r, Cr.Cir.eval(e, st), st))
        case Cr.Cir.Stmt.store{+k, +c, +v}:
          D.Ex.snd(D.Ends(Cr.Cir.exec.store(k, Cr.Cir.eval(c, st), Cr.Cir.eval(v, st), st)),
            _ => D.NoOom(Cr.Cir.exec.store(k, Cr.Cir.eval(c, st), Cr.Cir.eval(v, st), st)),
            calm.store(k, Cr.Cir.eval(c, st), Cr.Cir.eval(v, st), st))
        case Cr.Cir.Stmt.alloc{r}:
          D.bool.ft(D.NoOom(Cr.Cir.exec(1n+g, Cr.Cir.Stmt.alloc{r}, st)), h)
        case Cr.Cir.Stmt.emit{v}:
          D.bool.ft(D.NoOom(Cr.Cir.exec(1n+g, Cr.Cir.Stmt.emit{v}, st)), h)
        case Cr.Cir.Stmt.seq{+a, +b}:
          +ha = D.and.l(NA(a), NA(b), h)
          +hb = D.and.r(NA(a), NA(b), h)
          noom.then(Cr.Cir.exec(1n+g, a, st), t => Cr.Cir.exec(1n+g, b, t), noom.na(1n+g, a, st, ha), t => noom.na(1n+g, b, t, hb))
        case Cr.Cir.Stmt.if{+c, +a, +b}:
          +ha = D.and.l(NA(a), NA(b), h)
          +hb = D.and.r(NA(a), NA(b), h)
          noom.if(Cr.Cir.eval(c, st), u => Cr.Cir.exec(1n+g, a, st), u => Cr.Cir.exec(1n+g, b, st), noom.na(1n+g, a, st, ha),
            noom.na(1n+g, b, st, hb))
        case Cr.Cir.Stmt.while{c, b}:
          D.bool.ft(D.NoOom(Cr.Cir.exec(1n+g, Cr.Cir.Stmt.while{c, b}, st)), h)
        case Cr.Cir.Stmt.halt{_}:
          Unit{}

# a budget that a run that never runs out of memory needs not
def postb.noom(dn: Bool, o: Cr.Cir.Out, -Q: Cr.Cir.State -> Type, -H: U32 -> Cr.Cir.State -> Type, -B: Nat, -B2: Nat, -lim: U32,
  h: D.PostB(dn, o, Q, H, B, lim), hn: D.NoOom(o)) -> D.PostB(dn, o, Q, H, B2, lim):
  match o:
    case Cr.Cir.Out.next{_}:
      h
    case Cr.Cir.Out.halt{_, _}:
      h
    case Cr.Cir.Out.out_of_memory{}:
      Empty.absurd(D.PostB(dn, Cr.Cir.Out.out_of_memory{}, Q, H, B2, lim), hn)
    case Cr.Cir.Out.trap{}:
      h
    case Cr.Cir.Out.not_done{}:
      h

# M.alloc with a cell in the pend list takes no new cell
def na.alloc() -> {NA(K.stmt.then(Mc.M.alloc(16n))) == True{} : Bool}:
  {==}

def noom.alloc(+f: Nat, +regs: List<&2, U32>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32,
  +inp: List<&2, Word(8n)>, +pend: U32, h3: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>},
  hne: {U32.is_eq(pend, 0) == False{} : Bool}) ->
  D.NoOom(Cr.Cir.exec(f, Mc.M.alloc(16n), Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, Nil{}, 0})):
  +st = {Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, Nil{}, 0} : Cr.Cir.State}
  +ec = X.ev.op(Wa.Wasm.Op.ne{}, Mc.M.g(3n), Mc.M.c(0), st, pend, 0, h3, {==})
  +nz = {(%Equal.sym(Bool, U32.is_eq(pend, 0), False{}, hne) : {U32.is_zero(Bool.to_u32(Bool.not(_))) == False{} : Bool}; {==}) :
    {U32.is_zero(Wa.Wasm.op(Wa.Wasm.Op.ne{}, pend, 0)) == False{} : Bool}}
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, Mc.M.alloc(16n), st), Cr.Cir.exec(f, K.stmt.then(Mc.M.alloc(16n)), st),
    D.eq.if.t(f, K.stmt.cond(Mc.M.alloc(16n)), K.stmt.then(Mc.M.alloc(16n)), K.stmt.else(Mc.M.alloc(16n)), st, Wa.Wasm.op(Wa.Wasm.Op.ne{}, pend, 0), ec, nz)) :
    D.NoOom(_)
  noom.na(f, K.stmt.then(Mc.M.alloc(16n)), st, na.alloc())

# The frame push
# --------------
#
# M.push(h, y, b) after the incs: M.alloc gives the frame's cell z, of
# zeros; its four stores make it the cell {hv, sp, y, b, 0} (store.post:
# the roots of its terms leave the roots, z holds them), and z becomes the
# top frame (frs.push, acc.frame); sp gets z.

# a header with no STATIC bit
def hd.st(+hv: U32, kind: D.FK, q: Bk.Quan, h: HdOK(hv, kind, q)) -> {D.FlW(hv, 1024) == False{} : Bool}:
  match h:
    case Tuple{_, Tuple{_, Tuple{e, _}}}:
      e

# a next that alloc.post gives: the same, or one more with no pend list
def next.of(a: Bool, b: Bool, c: Bool, d: Bool, e: Bool, h: {Bool.or(Bool.and(a, b), Bool.and(c, Bool.and(d, e))) == True{} : Bool}) ->
  {Bool.or(b, Bool.and(c, e)) == True{} : Bool}:
  match a b c d e:
    case True{} True{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} False{} False{}:
      {==}
    case True{} True{} False{} True{} True{}:
      {==}
    case True{} True{} False{} True{} False{}:
      {==}
    case True{} True{} False{} False{} True{}:
      {==}
    case True{} True{} False{} False{} False{}:
      {==}
    case True{} False{} True{} True{} True{}:
      {==}
    case True{} False{} True{} True{} False{}:
      D.bool.ft({Bool.or(False{}, Bool.and(True{}, False{})) == True{} : Bool}, h)
    case True{} False{} True{} False{} True{}:
      D.bool.ft({Bool.or(False{}, Bool.and(True{}, True{})) == True{} : Bool}, h)
    case True{} False{} True{} False{} False{}:
      D.bool.ft({Bool.or(False{}, Bool.and(True{}, False{})) == True{} : Bool}, h)
    case True{} False{} False{} True{} True{}:
      D.bool.ft({Bool.or(False{}, Bool.and(False{}, True{})) == True{} : Bool}, h)
    case True{} False{} False{} True{} False{}:
      D.bool.ft({Bool.or(False{}, Bool.and(False{}, False{})) == True{} : Bool}, h)
    case True{} False{} False{} False{} True{}:
      D.bool.ft({Bool.or(False{}, Bool.and(False{}, True{})) == True{} : Bool}, h)
    case True{} False{} False{} False{} False{}:
      D.bool.ft({Bool.or(False{}, Bool.and(False{}, False{})) == True{} : Bool}, h)
    case False{} True{} True{} True{} True{}:
      {==}
    case False{} True{} True{} True{} False{}:
      D.bool.ft({Bool.or(True{}, Bool.and(True{}, False{})) == True{} : Bool}, h)
    case False{} True{} True{} False{} True{}:
      D.bool.ft({Bool.or(True{}, Bool.and(True{}, True{})) == True{} : Bool}, h)
    case False{} True{} True{} False{} False{}:
      D.bool.ft({Bool.or(True{}, Bool.and(True{}, False{})) == True{} : Bool}, h)
    case False{} True{} False{} True{} True{}:
      D.bool.ft({Bool.or(True{}, Bool.and(False{}, True{})) == True{} : Bool}, h)
    case False{} True{} False{} True{} False{}:
      D.bool.ft({Bool.or(True{}, Bool.and(False{}, False{})) == True{} : Bool}, h)
    case False{} True{} False{} False{} True{}:
      D.bool.ft({Bool.or(True{}, Bool.and(False{}, True{})) == True{} : Bool}, h)
    case False{} True{} False{} False{} False{}:
      D.bool.ft({Bool.or(True{}, Bool.and(False{}, False{})) == True{} : Bool}, h)
    case False{} False{} True{} True{} True{}:
      {==}
    case False{} False{} True{} True{} False{}:
      D.bool.ft({Bool.or(False{}, Bool.and(True{}, False{})) == True{} : Bool}, h)
    case False{} False{} True{} False{} True{}:
      D.bool.ft({Bool.or(False{}, Bool.and(True{}, True{})) == True{} : Bool}, h)
    case False{} False{} True{} False{} False{}:
      D.bool.ft({Bool.or(False{}, Bool.and(True{}, False{})) == True{} : Bool}, h)
    case False{} False{} False{} True{} True{}:
      D.bool.ft({Bool.or(False{}, Bool.and(False{}, True{})) == True{} : Bool}, h)
    case False{} False{} False{} True{} False{}:
      D.bool.ft({Bool.or(False{}, Bool.and(False{}, False{})) == True{} : Bool}, h)
    case False{} False{} False{} False{} True{}:
      D.bool.ft({Bool.or(False{}, Bool.and(False{}, True{})) == True{} : Bool}, h)
    case False{} False{} False{} False{} False{}:
      D.bool.ft({Bool.or(False{}, Bool.and(False{}, False{})) == True{} : Bool}, h)
# the two Bool facts of a pair
def p2.fst.b(-a: Bool, -b: Bool, h: D.P2({a == True{} : Bool}, {b == True{} : Bool})) -> {a == True{} : Bool}:
  match h:
    case Tuple{x, _}:
      x

def p2.snd.b(-a: Bool, -b: Bool, h: D.P2({a == True{} : Bool}, {b == True{} : Bool})) -> {b == True{} : Bool}:
  match h:
    case Tuple{_, y}:
      y

# the image's cells: from 290, below fi
def img.lo(+dk: Bool, -ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -m: Cr.Cir.Cells, +im: U32, +fi: U32,
  -nx: U32, io: D.ImgOKK(dk, ds, ks, img, m, im, fi, nx)) -> D.P2({U32.is_le(290, im) == True{} : Bool}, {U32.is_lt(im, fi) == True{} : Bool}):
  match io:
    case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, r}}}}}}:
      r

# the last root's term is a node of the frame's terms' roots: its IsK
def rts.foc.go(L: List<&2, D.Rt>, +dk: Bool, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32,
  +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +xc: U32, +vf: Bk.Term, +foc: U32, +F: Bk.Term,
  h: D.RtsK(dk, ds, m, im, fi, nx, ks, img, List.append(&2, D.Rt, L, [D.Rt{xc, vf}, D.Rt{foc, F}]))) -> D.IsK(dk, ds, m, im, fi, nx, ks, img, foc, F):
  match L:
    case Nil{}:
      match h:
        case Tuple{_, Tuple{i, _}}:
          i
    case Con{D.Rt{+c, +u}, +rest}:
      match h:
        case Tuple{_, r}:
          rts.foc.go(rest, dk, ds, m, im, fi, nx, ks, img, xc, vf, foc, F, r)

def rts.foc(+dk: Bool, +ds: List<&2, Bk.Def>, +m: Cr.Cir.Cells, +im: U32, +fi: U32, +nx: U32, +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>, +yc: U32, +va: Bk.Term, +L: List<&2, D.Rt>, +xc: U32, +vf: Bk.Term, +foc: U32, +F: Bk.Term,
  h: D.RtsK(dk, ds, m, im, fi, nx, ks, img, Con{D.Rt{yc, va}, List.append(&2, D.Rt, L, [D.Rt{xc, vf}, D.Rt{foc, F}])})) ->
  D.IsK(dk, ds, m, im, fi, nx, ks, img, foc, F):
  match h:
    case Tuple{_, r}:
      rts.foc.go(L, dk, ds, m, im, fi, nx, ks, img, xc, vf, foc, F, r)

# what alloc.post gives for the frame's cell (register fr)
def AlQ(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>, +m: Cr.Cir.Cells,
  +nx: U32, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +foc: U32, +F: Bk.Term, +xc: U32, +vf: Bk.Term, +yc: U32,
  +va: Bk.Term, +bv: U32, +vb: Bk.Term, +kind: D.FK, +q: Bk.Quan, +hv: U32, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, st2: Cr.Cir.State) -> Type:
  D.P2(D.Same(regs, fi, im, lim, inp, [1n, 2n, 8n, 11n, 12n, 13n], st2),
    D.Ex(U32, z => D.Ex(U32, pend2 => D.Ex(List<&2, U32>, ps2 =>
      D.P2(D.Reg(st2, 16n, z), D.P2(D.Reg(st2, 3n, pend2),
      D.P2({Cr.Cir.Cells.get(D.St.cells(st2), z) == Cr.Cir.Cell.zero() : Cr.Cir.Cell},
      D.P2({D.Own(fi, D.St.next(st2), z) == True{} : Bool}, D.P2({D.Mem(ps2, z) == False{} : Bool},
      D.P2({Bool.or(D.Mem(ps, z), U32.is_eq(z, nx)) == True{} : Bool},
      D.P2({Bool.or(Bool.and(D.Mem(ps, z), U32.is_eq(D.St.next(st2), nx)),
           Bool.and(D.Pend.none(ps), Bool.and(U32.is_eq(z, nx), U32.is_eq(D.St.next(st2), U32.inc(nx))))) == True{} : Bool},
      D.P2(D.Ex(List<&2, D.W1>, ws => D.P2({D.St.cells(st2) == Cr.Cir.Cells.set(D.Put1(ws, m), z, Cr.Cir.Cell.zero()) : Cr.Cir.Cells},
        {D.Took(ws, ps, m) == True{} : Bool})),
      D.P2({D.PsSub(ps2, ps, m) == True{} : Bool},
      D.P2({D.Ptr(Nat.sub(U32.to_nat(D.St.next(st2)), U32.to_nat(fi)), D.St.cells(st2), fi, ps2, D.Rt.cells(Con{D.Rt{yc, va}, List.append(&2, D.Rt, UB(kind, bv, vb), [D.Rt{xc, vf}, D.Rt{foc, F}])}), z) == 0n : Nat},
      D.P2(D.HSK(True{}, ds, ks, img, D.St.cells(st2), D.St.next(st2), fi, im, Con{D.Rt{yc, va}, List.append(&2, D.Rt, UB(kind, bv, vb), [D.Rt{xc, vf}, D.Rt{foc, F}])}, Nil{}, fs, sp, pend2, ps2),
        D.Ex(List<&2, D.Rt>, zs2 => D.AccK(True{}, ds, ks, img, D.St.cells(st2), D.St.next(st2), fi, im, Con{D.Rt{yc, va}, List.append(&2, D.Rt, UB(kind, bv, vb), [D.Rt{xc, vf}, D.Rt{foc, F}])}, Con{D.TmpE{z, Nil{}}, Nil{}}, sp, fs, ps2, zs2))))))))))))))))) & D.AlFr(m, ps, nx, st2)

# the state after M.push: the frame z on top, its terms the frame's; the
# registers of the push's keep, then sp gets z
def PushQ(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>, +m: Cr.Cir.Cells,
  +nx: U32, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +foc: U32, +F: Bk.Term, +xc: U32, +vf: Bk.Term, +yc: U32,
  +va: Bk.Term, +bv: U32, +vb: Bk.Term, +kind: D.FK, +q: Bk.Quan, +hv: U32, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, st: Cr.Cir.State) -> Data:
  D.Ex(List<&2, U32>, regs1 => D.Ex(Cr.Cir.Cells, m3 => D.Ex(U32, nx3 => D.Ex(U32, pg3 => D.Ex(U32, z => D.Ex(U32, pend3 =>
  D.Ex(List<&2, U32>, ps3 => D.Ex(List<&2, D.Rt>, zs3 =>
    D.P2({st == Cr.Cir.State{List.set(&2, U32, regs1, 2n, z), m3, nx3, fi, im, pg3, lim, inp, Nil{}, 0} : Cr.Cir.State},
    D.P2({List.length(&2, U32, regs1) == 63n : Nat},
    D.P2(D.Kept(regs, regs1, [1n, 2n, 8n, 11n, 12n, 13n]),
    D.P2({List.get(&2, U32, regs1, 3n) == Some{pend3} : Maybe<&2, U32>},
    D.P2({Bool.or(U32.is_eq(nx3, nx), Bool.and(D.Pend.none(ps), U32.is_eq(nx3, U32.inc(nx)))) == True{} : Bool},
    D.P2(D.HS(ds, ks, img, m3, nx3, fi, im, [D.Rt{xc, vf}, D.Rt{foc, F}], Nil{}, Con{D.AF{kind, q, False{}, va, vb}, fs}, z, pend3, ps3),
      D.AccK(True{}, ds, ks, img, m3, nx3, fi, im, [D.Rt{xc, vf}, D.Rt{foc, F}], Nil{}, z, Con{D.AF{kind, q, False{}, va, vb}, fs}, ps3, zs3)))))))))))))))

# the state after M.push, from store.post's heap
def push.fin(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>, +m: Cr.Cir.Cells,
  +nx: U32, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +foc: U32, +F: Bk.Term, +xc: U32, +vf: Bk.Term, +yc: U32,
  +va: Bk.Term, +bv: U32, +vb: Bk.Term, +kind: D.FK, +q: Bk.Quan, +hv: U32, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +regs1: List<&2, U32>, +m1: Cr.Cir.Cells, +nx1: U32, +pg1: U32, +z: U32, +pend2: U32, +ps2: List<&2, U32>,
  +zs2: List<&2, D.Rt>, +t5: Cr.Cir.State,
  est: {t5 == Cr.Cir.State{List.set(&2, U32, regs1, 2n, z), Cr.Cir.Cells.set(m1, z, Cr.Cir.Cell{hv, sp, yc, bv, 0}), nx1, fi, im, pg1, lim, inp, Nil{}, 0} : Cr.Cir.State},
  hl1: {List.length(&2, U32, regs1) == 63n : Nat}, hkept: D.Kept(regs, regs1, [1n, 2n, 8n, 11n, 12n, 13n]), h3b: {List.get(&2, U32, regs1, 3n) == Some{pend2} : Maybe<&2, U32>},
  hn2: {Bool.or(U32.is_eq(nx1, nx), Bool.and(D.Pend.none(ps), U32.is_eq(nx1, U32.inc(nx)))) == True{} : Bool},
  +hok: HdOK(hv, kind, q), +hown: {D.Own(fi, nx1, z) == True{} : Bool}, +hmz: {D.Mem(ps2, z) == False{} : Bool},
  +h290: {U32.is_le(290, im) == True{} : Bool}, +him: {U32.is_lt(im, fi) == True{} : Bool},
  hst: D.P2(D.HSK(True{}, ds, ks, img, Cr.Cir.Cells.set(m1, z, Cr.Cir.Cell{hv, sp, yc, bv, 0}), nx1, fi, im, [D.Rt{xc, vf}, D.Rt{foc, F}], Nil{}, fs, sp, pend2, ps2),
    D.AccK(True{}, ds, ks, img, Cr.Cir.Cells.set(m1, z, Cr.Cir.Cell{hv, sp, yc, bv, 0}), nx1, fi, im, [D.Rt{xc, vf}, D.Rt{foc, F}], D.Tmp.hold(Con{D.Rt{yc, va}, UB(kind, bv, vb)}, [D.TmpE{z, Nil{}}]), sp, fs, ps2, zs2))) ->
  PushQ(ds, ks, img, regs, m, nx, fi, im, lim, inp, foc, F, xc, vf, yc, va, bv, vb, kind, q, hv, fs, sp, ps, t5):
  match hst:
    case Tuple{Tuple{+hro, Tuple{+hrb, Tuple{+hhd, Tuple{+hfrs, Tuple{+hhp, hio}}}}}, Tuple{+a1, Tuple{Tuple{+iy, iub}, Tuple{+a3, Tuple{+a4, Tuple{+a5, _}}}}}}:
      +M3 = Cr.Cir.Cells.set(m1, z, Cr.Cir.Cell{hv, sp, yc, bv, 0})
      +ef = X.Ce.get_set(m1, z, Cr.Cir.Cell{hv, sp, yc, bv, 0})
      +hfp = frs.push(True{}, ds, M3, im, fi, nx1, ks, img, ps2, z, sp, fs, kind, q, va, vb, hv, yc, bv, ef, hok,
        own.nz(fi, nx1, im, z, h290, him, hown), own.cell(fi, nx1, im, z, hown), hown, hmz, iy,
        ub.frsb(kind, True{}, ds, M3, im, fi, nx1, ks, img, bv, vb, iub), hfrs)
      +f1 = Equal.cong(Cr.Cir.Cell, U32, c => Cr.Cir.Cell.get(1n, c), Cr.Cir.Cells.get(M3, z), Cr.Cir.Cell{hv, sp, yc, bv, 0}, ef)
      +f2 = Equal.cong(Cr.Cir.Cell, U32, c => Cr.Cir.Cell.get(2n, c), Cr.Cir.Cells.get(M3, z), Cr.Cir.Cell{hv, sp, yc, bv, 0}, ef)
      +f3 = Equal.cong(Cr.Cir.Cell, U32, c => Cr.Cir.Cell.get(3n, c), Cr.Cir.Cells.get(M3, z), Cr.Cir.Cell{hv, sp, yc, bv, 0}, ef)
      +hacf = acc.frame(kind, True{}, ds, ks, img, M3, nx1, fi, im, [D.Rt{xc, vf}, D.Rt{foc, F}], z, yc, va, bv, vb, q, sp, fs, ps2, zs2, f1, f2, f3, a1, a3, a4, a5)
      +hs4 = {(hro, (hrb, (hhd, (hfp, (hhp, hio))))) :
        D.HS(ds, ks, img, M3, nx1, fi, im, [D.Rt{xc, vf}, D.Rt{foc, F}], Nil{}, Con{D.AF{kind, q, False{}, va, vb}, fs}, z, pend2, ps2)}
      (regs1, (M3, (nx1, (pg1, (z, (pend2, (ps2, (zs2, (est, (hl1, (hkept, (h3b, (hn2, (hs4, hacf))))))))))))))

# the registers that Same finds
def same.parts(+regs: List<&2, U32>, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +keep: List<&2, Nat>,
  st: Cr.Cir.State, h: D.Same(regs, fi, im, lim, inp, keep, st)) ->
  D.P2({List.length(&2, U32, D.St.regs(st)) == 63n : Nat}, D.Kept(regs, D.St.regs(st), keep)):
  match st:
    case Cr.Cir.State{_, _, _, _, _, _, _, _, _, _}:
      match h:
        case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{hl, hk}}}}}}}:
          (hl, hk)

# push.k's run, from alloc.post's facts
def push.k2(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>, +m: Cr.Cir.Cells,
  +nx: U32, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +foc: U32, +F: Bk.Term, +xc: U32, +vf: Bk.Term, +yc: U32,
  +va: Bk.Term, +bv: U32, +vb: Bk.Term, +kind: D.FK, +q: Bk.Quan, +hv: U32, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +hexp: Cr.Cir.Expr, +bexp: Cr.Cir.Expr, +B: Nat,
  +h8: {List.get(&2, U32, regs, 8n) == Some{foc} : Maybe<&2, U32>}, +h2: {List.get(&2, U32, regs, 2n) == Some{sp} : Maybe<&2, U32>},
  +h12: {List.get(&2, U32, regs, 12n) == Some{yc} : Maybe<&2, U32>},
  eh: @regs2: List<&2, U32> -> @m2: Cr.Cir.Cells -> @nx2: U32 -> @pg2: U32 -> {List.get(&2, U32, regs2, 8n) == Some{foc} : Maybe<&2, U32>} ->
    D.IsK(True{}, ds, m2, im, fi, nx2, ks, img, foc, F) ->
    {Cr.Cir.eval(hexp, Cr.Cir.State{regs2, m2, nx2, fi, im, pg2, lim, inp, Nil{}, 0}) == Some{hv} : Maybe<&2, U32>},
  eb: @regs2: List<&2, U32> -> @m2: Cr.Cir.Cells -> @nx2: U32 -> @pg2: U32 -> {List.get(&2, U32, regs2, 13n) == List.get(&2, U32, regs, 13n) : Maybe<&2, U32>} ->
    {Cr.Cir.eval(bexp, Cr.Cir.State{regs2, m2, nx2, fi, im, pg2, lim, inp, Nil{}, 0}) == Some{bv} : Maybe<&2, U32>},
  +htg: {D.TgW(hv) == D.FK.tag(kind) : U32}, +hrest: D.P2({D.QnW(hv) == Mc.Img.quan(q) : U32},
    D.P2({D.FlW(hv, 1024) == False{} : Bool}, {D.FlW(hv, 2048) == False{} : Bool})),
  +st1: Cr.Cir.State,
  hparts: D.P2({List.length(&2, U32, D.St.regs(st1)) == 63n : Nat}, D.Kept(regs, D.St.regs(st1), [1n, 2n, 8n, 11n, 12n, 13n])),
  +hsame: D.Same(regs, fi, im, lim, inp, [1n, 2n, 8n, 11n, 12n, 13n], st1), +z: U32, +pend2: U32, +ps2: List<&2, U32>,
  +h16: D.Reg(st1, 16n, z), +h3b: D.Reg(st1, 3n, pend2), +hzero: {Cr.Cir.Cells.get(D.St.cells(st1), z) == Cr.Cir.Cell.zero() : Cr.Cir.Cell},
  +hown: {D.Own(fi, D.St.next(st1), z) == True{} : Bool}, +hmz: {D.Mem(ps2, z) == False{} : Bool},
  +hnx: {Bool.or(Bool.and(D.Mem(ps, z), U32.is_eq(D.St.next(st1), nx)),
    Bool.and(D.Pend.none(ps), Bool.and(U32.is_eq(z, nx), U32.is_eq(D.St.next(st1), U32.inc(nx))))) == True{} : Bool},
  +hptr: {D.Ptr(Nat.sub(U32.to_nat(D.St.next(st1)), U32.to_nat(fi)), D.St.cells(st1), fi, ps2, D.Rt.cells(Con{D.Rt{yc, va}, List.append(&2, D.Rt, UB(kind, bv, vb), [D.Rt{xc, vf}, D.Rt{foc, F}])}), z) == 0n : Nat},
  +s1: D.RtsK(True{}, ds, D.St.cells(st1), im, fi, D.St.next(st1), ks, img, Con{D.Rt{yc, va}, List.append(&2, D.Rt, UB(kind, bv, vb), [D.Rt{xc, vf}, D.Rt{foc, F}])}),
  +s2: D.RtsK(True{}, ds, D.St.cells(st1), im, fi, D.St.next(st1), ks, img, Nil{}),
  +s3: D.Held(D.St.cells(st1), Con{D.Rt{yc, va}, List.append(&2, D.Rt, UB(kind, bv, vb), [D.Rt{xc, vf}, D.Rt{foc, F}])}, Nil{}),
  +s4: D.FrsK(True{}, ds, D.St.cells(st1), im, fi, D.St.next(st1), ks, img, ps2, sp, fs),
  +s5: D.Heap(D.St.cells(st1), D.St.next(st1), fi, im, D.Rt.cells(Con{D.Rt{yc, va}, List.append(&2, D.Rt, UB(kind, bv, vb), [D.Rt{xc, vf}, D.Rt{foc, F}])}), pend2, ps2),
  +io: D.ImgOKK(True{}, ds, ks, img, D.St.cells(st1), im, fi, D.St.next(st1)), +zs2: List<&2, D.Rt>,
  +hac2: D.AccK(True{}, ds, ks, img, D.St.cells(st1), D.St.next(st1), fi, im, Con{D.Rt{yc, va}, List.append(&2, D.Rt, UB(kind, bv, vb), [D.Rt{xc, vf}, D.Rt{foc, F}])}, Con{D.TmpE{z, Nil{}}, Nil{}}, sp, fs, ps2, zs2),
  +hle: {U32.is_le(nx, D.St.next(st1)) == True{} : Bool}) ->
  D.PostB(False{}, Cr.Cir.exec(f, X.sel.b(Mc.M.push(hexp, Mc.M.g(Mc.R.y()), bexp)), st1), st3 => PushQ(ds, ks, img, regs, m, nx, fi, im, lim, inp, foc, F, xc, vf, yc, va, bv, vb, kind, q, hv, fs, sp, ps, st3), s => st2 => Empty, B, lim):
  match hparts:
    case Tuple{+hl1, Tuple{+k1, Tuple{+k2, Tuple{+k8, Tuple{+k11, Tuple{+k12, Tuple{+k13, _}}}}}}}:
          +regs1 = D.St.regs(st1)
          +m1 = D.St.cells(st1)
          +nx1 = D.St.next(st1)
          +pg1 = St.pg(st1)
          +t0 = {Cr.Cir.State{regs1, m1, nx1, fi, im, pg1, lim, inp, Nil{}, 0} : Cr.Cir.State}
          +g = h16
          +hc = own.cell(fi, nx1, im, z, hown)
          +h8b = Equal.trans(Maybe<&2, U32>, List.get(&2, U32, regs1, 8n), List.get(&2, U32, regs, 8n), Some{foc}, k8, h8)
          +ehv = eh(regs1, m1, nx1, pg1, h8b, rts.foc(True{}, ds, m1, im, fi, nx1, ks, img, yc, va, UB(kind, bv, vb), xc, vf, foc, F, s1))
          +t1 = X.X.store(t0, 0n, z, hv)
          +t2 = X.X.store(t1, 1n, z, sp)
          +t3 = X.X.store(t2, 2n, z, yc)
          +t4 = X.X.store(t3, 3n, z, bv)
          +t5 = X.X.setst(t4, 2n, z)
          +esp = Equal.trans(Maybe<&2, U32>, List.get(&2, U32, regs1, 2n), List.get(&2, U32, regs, 2n), Some{sp}, k2, h2)
          +ey = Equal.trans(Maybe<&2, U32>, List.get(&2, U32, regs1, 12n), List.get(&2, U32, regs, 12n), Some{yc}, k12, h12)
          +ebv = eb(regs1, X.X.put(X.X.put(X.X.put(m1, 0n, z, hv), 1n, z, sp), 2n, z, yc), nx1, pg1, k13)
          +q1 = X.sel.b(Mc.M.push(hexp, Mc.M.g(Mc.R.y()), bexp))
          +q2 = X.sel.b(q1)
          +q3 = X.sel.b(q2)
          +q4 = X.sel.b(q3)
          +q5 = X.sel.b(q4)
          +e1 = X.run.store(f, 0n, Mc.M.g(16n), hexp, t0, z, hv, g, ehv, hc)
          +e2 = X.run.store(f, 1n, Mc.M.g(16n), Mc.M.g(2n), t1, z, sp, g, esp, hc)
          +e3 = X.run.store(f, 2n, Mc.M.g(16n), Mc.M.g(12n), t2, z, yc, g, ey, hc)
          +e4 = X.run.store(f, 3n, Mc.M.g(16n), bexp, t3, z, bv, g, ebv, hc)
          +e5 = X.run.set(f, 2n, Mc.M.g(16n), t4, z, g, hl1, {==})
          +eq = {(%X.rw.seq(f, X.sel.a(q1), q2, t0, t1, e1) : {_ == Cr.Cir.Out.next{t5} : Cr.Cir.Out};
            %X.rw.seq(f, X.sel.a(q2), q3, t1, t2, e2) : {_ == Cr.Cir.Out.next{t5} : Cr.Cir.Out};
            %X.rw.seq(f, X.sel.a(q3), q4, t2, t3, e3) : {_ == Cr.Cir.Out.next{t5} : Cr.Cir.Out};
            %X.rw.seq(f, X.sel.a(q4), q5, t3, t4, e4) : {_ == Cr.Cir.Out.next{t5} : Cr.Cir.Out};
            %X.rw.seq(f, X.sel.a(q5), X.sel.b(q5), t4, t5, e5) : {_ == Cr.Cir.Out.next{t5} : Cr.Cir.Out};
            X.run.nop(f, t5)) : {Cr.Cir.exec(f, q1, t0) == Cr.Cir.Out.next{t5} : Cr.Cir.Out}}
          +M3 = Cr.Cir.Cells.set(m1, z, Cr.Cir.Cell{hv, sp, yc, bv, 0})
          +ef = X.Ce.get_set(m1, z, Cr.Cir.Cell{hv, sp, yc, bv, 0})
          +est = Equal.cong(Cr.Cir.Cells, Cr.Cir.State, y => Cr.Cir.State{List.set(&2, U32, regs1, 2n, z), y, nx1, fi, im, pg1, lim, inp, Nil{}, 0},
            X.X.put(X.X.put(X.X.put(X.X.put(m1, 0n, z, hv), 1n, z, sp), 2n, z, yc), 3n, z, bv), M3, push.cells(m1, z, hv, sp, yc, bv, hzero))
          +hn2 = next.of(D.Mem(ps, z), U32.is_eq(nx1, nx), D.Pend.none(ps), U32.is_eq(z, nx), U32.is_eq(nx1, U32.inc(nx)), hnx)
          +hst = D.store.post(True{}, ds, ks, img, m1, nx1, fi, im, Con{D.Rt{yc, va}, UB(kind, bv, vb)}, [D.Rt{xc, vf}, D.Rt{foc, F}], Nil{}, fs, sp, pend2, ps2, z, Cr.Cir.Cell{hv, sp, yc, bv, 0},
            [D.TmpE{z, Nil{}}], zs2, (s1, (s2, (s3, (s4, (s5, io))))), hac2, {==}, Unit{}, hown, hmz, zero.st(m1, z, hzero),
            zero.tg(m1, z, hzero), hptr, fs.zero(m1, ps2, z, hzero, tbl.z(m1, im, fi, nx1, D.img.tbl(True{}, ds, ks, img, m1, im, fi, nx1, io))),
            (%Equal.sym(U32, D.TgW(hv), D.FK.tag(kind), htg) : {U32.is_le(32, _) == True{} : Bool}; fk.lo(kind)),
            hd.st(hv, kind, q, (htg, hrest)), fs.frame(kind, M3, ps2, z, hv, sp, yc, bv, vb, ef, htg, hmz))
          %Equal.sym(Cr.Cir.State, st1, t0, same.st(regs, fi, im, lim, inp, [1n, 2n, 8n, 11n, 12n, 13n], st1, hsame)) :
            D.PostB(False{}, Cr.Cir.exec(f, X.sel.b(Mc.M.push(hexp, Mc.M.g(Mc.R.y()), bexp)), _), st3 => PushQ(ds, ks, img, regs, m, nx, fi, im, lim, inp, foc, F, xc, vf, yc, va, bv, vb, kind, q, hv, fs, sp, ps, st3), s => st2 => Empty, B, lim)
          %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, q1, t0), Cr.Cir.Out.next{t5}, eq) :
            D.PostB(False{}, _, st3 => PushQ(ds, ks, img, regs, m, nx, fi, im, lim, inp, foc, F, xc, vf, yc, va, bv, vb, kind, q, hv, fs, sp, ps, st3), s => st2 => Empty, B, lim)
          push.fin(ds, ks, img, regs, m, nx, fi, im, lim, inp, foc, F, xc, vf, yc, va, bv, vb, kind, q, hv, fs, sp, ps, regs1, m1, nx1, pg1, z, pend2, ps2, zs2, t5, est, hl1, (k1, (k2, (k8, (k11, (k12, (k13, Unit{})))))),
            h3b, hn2, (htg, hrest), hown, hmz, p2.fst.b(U32.is_le(290, im), U32.is_lt(im, fi), img.lo(True{}, ds, ks, img, m1, im, fi, nx1, io)),
            p2.snd.b(U32.is_le(290, im), U32.is_lt(im, fi), img.lo(True{}, ds, ks, img, m1, im, fi, nx1, io)), hst)

# the frame's cell, after the stores of M.push
def push.k(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>, +m: Cr.Cir.Cells,
  +nx: U32, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +foc: U32, +F: Bk.Term, +xc: U32, +vf: Bk.Term, +yc: U32,
  +va: Bk.Term, +bv: U32, +vb: Bk.Term, +kind: D.FK, +q: Bk.Quan, +hv: U32, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +hexp: Cr.Cir.Expr, +bexp: Cr.Cir.Expr, +B: Nat,
  +h8: {List.get(&2, U32, regs, 8n) == Some{foc} : Maybe<&2, U32>}, +h2: {List.get(&2, U32, regs, 2n) == Some{sp} : Maybe<&2, U32>},
  +h12: {List.get(&2, U32, regs, 12n) == Some{yc} : Maybe<&2, U32>},
  eh: @regs2: List<&2, U32> -> @m2: Cr.Cir.Cells -> @nx2: U32 -> @pg2: U32 -> {List.get(&2, U32, regs2, 8n) == Some{foc} : Maybe<&2, U32>} ->
    D.IsK(True{}, ds, m2, im, fi, nx2, ks, img, foc, F) ->
    {Cr.Cir.eval(hexp, Cr.Cir.State{regs2, m2, nx2, fi, im, pg2, lim, inp, Nil{}, 0}) == Some{hv} : Maybe<&2, U32>},
  eb: @regs2: List<&2, U32> -> @m2: Cr.Cir.Cells -> @nx2: U32 -> @pg2: U32 -> {List.get(&2, U32, regs2, 13n) == List.get(&2, U32, regs, 13n) : Maybe<&2, U32>} ->
    {Cr.Cir.eval(bexp, Cr.Cir.State{regs2, m2, nx2, fi, im, pg2, lim, inp, Nil{}, 0}) == Some{bv} : Maybe<&2, U32>},
  +hok: HdOK(hv, kind, q), +st1: Cr.Cir.State, qa: AlQ(ds, ks, img, regs, m, nx, fi, im, lim, inp, foc, F, xc, vf, yc, va, bv, vb, kind, q, hv, fs, sp, ps, st1)) ->
  D.PostB(False{}, Cr.Cir.exec(f, X.sel.b(Mc.M.push(hexp, Mc.M.g(Mc.R.y()), bexp)), st1), st3 => PushQ(ds, ks, img, regs, m, nx, fi, im, lim, inp, foc, F, xc, vf, yc, va, bv, vb, kind, q, hv, fs, sp, ps, st3), s => st2 => Empty, B, lim):
  match hok:
    case Tuple{+htg, hrest}:
      match qa:
        case Tuple{Tuple{+hsame, Tuple{+z, Tuple{+pend2, Tuple{+ps2, Tuple{+h16, Tuple{+h3b, Tuple{+hzero, Tuple{+hown, Tuple{+hmz, Tuple{_, Tuple{+hnx, Tuple{_, Tuple{_, Tuple{+hptr, Tuple{Tuple{+s1, Tuple{+s2, Tuple{+s3, Tuple{+s4, Tuple{+s5, io}}}}}, Tuple{+zs2, hac2}}}}}}}}}}}}}}}}, Tuple{+hle, _}}:
          push.k2(f, ds, ks, img, regs, m, nx, fi, im, lim, inp, foc, F, xc, vf, yc, va, bv, vb, kind, q, hv, fs, sp, ps, hexp, bexp, B, h8, h2, h12, eh, eb, htg, hrest, st1, same.parts(regs, fi, im, lim, inp, [1n, 2n, 8n, 11n, 12n, 13n], st1, hsame), hsame,
            z, pend2, ps2, h16, h3b, hzero, hown, hmz, hnx, hptr, s1, s2, s3, s4, s5, io, zs2, hac2, hle)


# Nat order kit
def le.max.r(a: Nat, +b: Nat) -> N.Le(b, Nat.max(a, b)):
  match a:
    case 0n:
      N.le_refl(b)
    case 1n+p:
      match b:
        case 0n:
          N.le_zero(1n+p)
        case 1n+q:
          le.max.r(p, q)

def sub.mono(c: Nat, a: Nat, b: Nat, h: N.Le(a, b)) -> N.Le(Nat.sub(a, c), Nat.sub(b, c)):
  match c:
    case 0n:
      match a:
        case 0n:
          N.le_zero(Nat.sub(b, 0n))
        case 1n+ap:
          match b:
            case 0n:
              Empty.absurd(N.Le(1n+ap, 0n), h)
            case 1n+bp:
              h
    case 1n+cp:
      match a:
        case 0n:
          N.le_zero(Nat.sub(b, 1n+cp))
        case 1n+ap:
          match b:
            case 0n:
              Empty.absurd(N.Le(Nat.sub(1n+ap, 1n+cp), Nat.sub(0n, 1n+cp)), h)
            case 1n+bp:
              sub.mono(cp, ap, bp, h)

def sub.succ(c: Nat, n: Nat) -> N.Le(Nat.sub(1n+n, c), 1n+Nat.sub(n, c)):
  match c:
    case 0n:
      match n:
        case 0n:
          Unit{}
        case 1n+p:
          N.le_refl(1n+p)
    case 1n+cp:
      match n:
        case 0n:
          N.le_zero(1n+Nat.sub(0n, 1n+cp))
        case 1n+p:
          sub.succ(cp, p)

# the own cells after a push: within the round's peak
def peak.fin(+ds: List<&2, Bk.Def>, +st0: Cr.Cir.State, +t: Bk.Term, +nx: U32, +nx3: U32, +fi: U32, +ps: List<&2, U32>,
  hmc: {D.Mem.cells(st0) == Nat.sub(U32.to_nat(nx), U32.to_nat(fi)) : Nat},
  hnd: {D.Pend.none(ps) == True{} : Bool} -> N.Le(1n+Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), D.Need(ds, st0, t)),
  hn: {Bool.or(U32.is_eq(nx3, nx), Bool.and(D.Pend.none(ps), U32.is_eq(nx3, U32.inc(nx)))) == True{} : Bool}) ->
  N.Le(Nat.sub(U32.to_nat(nx3), U32.to_nat(fi)), Nat.max(D.Mem.cells(st0), D.Need(ds, st0, t))):
  +MX = Nat.max(D.Mem.cells(st0), D.Need(ds, st0, t))
  D.or.cases(U32.is_eq(nx3, nx), Bool.and(D.Pend.none(ps), U32.is_eq(nx3, U32.inc(nx))),
    N.Le(Nat.sub(U32.to_nat(nx3), U32.to_nat(fi)), MX), hn,
    e => (%Equal.sym(U32, nx3, nx, D.u32.eq(nx3, nx, e)) : N.Le(Nat.sub(U32.to_nat(_), U32.to_nat(fi)), MX);
      %hmc : N.Le(_, MX);
      le.max(D.Mem.cells(st0), D.Need(ds, st0, t))),
    +e => (%Equal.sym(U32, nx3, U32.inc(nx), D.u32.eq(nx3, U32.inc(nx), D.and.r(D.Pend.none(ps), U32.is_eq(nx3, U32.inc(nx)), e))) :
        N.Le(Nat.sub(U32.to_nat(_), U32.to_nat(fi)), MX);
      N.le_trans(Nat.sub(U32.to_nat(U32.inc(nx)), U32.to_nat(fi)), 1n+Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), MX,
        N.le_trans(Nat.sub(U32.to_nat(U32.inc(nx)), U32.to_nat(fi)), Nat.sub(1n+U32.to_nat(nx), U32.to_nat(fi)),
          1n+Nat.sub(U32.to_nat(nx), U32.to_nat(fi)),
          sub.mono(U32.to_nat(fi), U32.to_nat(U32.inc(nx)), 1n+U32.to_nat(nx), N.U32.inc_le(nx)), sub.succ(U32.to_nat(fi), U32.to_nat(nx))),
        N.le_trans(1n+Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), D.Need(ds, st0, t), MX,
          hnd(D.and.l(D.Pend.none(ps), U32.is_eq(nx3, U32.inc(nx)), e)), le.max.r(D.Mem.cells(st0), D.Need(ds, st0, t))))))

# what dec.post gives for the focus' old cell
def DecQ(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>, +m: Cr.Cir.Cells,
  +nx: U32, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +foc: U32, +F: Bk.Term, +xc: U32, +vf: Bk.Term, +yc: U32,
  +va: Bk.Term, +bv: U32, +vb: Bk.Term, +kind: D.FK, +q: Bk.Quan, +hv: U32, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +regsP: List<&2, U32>, +m3: Cr.Cir.Cells, +nx3: U32, +pg3: U32, +z: U32, +pend3: U32, st2: Cr.Cir.State) -> Data:
  D.Ex(Cr.Cir.Cells, m2 => D.Ex(U32, d => D.Ex(U32, pend2 => D.Ex(List<&2, U32>, ps2 =>
    D.P2({st2 == Cr.Cir.State{List.set(&2, U32, List.set(&2, U32, regsP, 5n, d), 3n, pend2), m2, nx3, fi, im, pg3, lim, inp, Nil{}, 0} : Cr.Cir.State},
    D.P2({D.Stat(Nat.sub(U32.to_nat(nx3), U32.to_nat(fi)), m2, fi) == D.Stat(Nat.sub(U32.to_nat(nx3), U32.to_nat(fi)), m3, fi) : Nat},
    D.P2(D.HSK(True{}, ds, ks, img, m2, nx3, fi, im, [D.Rt{xc, vf}], Nil{}, Con{D.AF{kind, q, False{}, va, vb}, fs}, z, pend2, ps2),
      D.Ex(List<&2, D.Rt>, zs2 => D.AccK(True{}, ds, ks, img, m2, nx3, fi, im, [D.Rt{xc, vf}], Nil{}, z, Con{D.AF{kind, q, False{}, va, vb}, fs}, ps2, zs2)))))))))

# the round's end: the focus gets the frame's hole, the state stands for t
def fin.k(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>, +m: Cr.Cir.Cells,
  +nx: U32, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +foc: U32, +F: Bk.Term, +xc: U32, +vf: Bk.Term, +yc: U32,
  +va: Bk.Term, +bv: U32, +vb: Bk.Term, +kind: D.FK, +q: Bk.Quan, +hv: U32, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +st0: Cr.Cir.State, +t: Bk.Term, +w: Nat, +B: Nat,
  +hmc: {D.Mem.cells(st0) == Nat.sub(U32.to_nat(nx), U32.to_nat(fi)) : Nat},
  hnd: {D.Pend.none(ps) == True{} : Bool} -> N.Le(1n+Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), D.Need(ds, st0, t)),
  +et2: {D.A.plugs(Con{D.AF{kind, q, False{}, va, vb}, fs}, vf) == t : Bk.Term}, +ew2: N.Le(1n+D.A.w(False{}, vf, Con{D.AF{kind, q, False{}, va, vb}, fs}), w), +afs2: D.AFs.ok(ds, Con{D.AF{kind, q, False{}, va, vb}, fs}),
  +h1: {List.get(&2, U32, regs, 1n) == Some{0} : Maybe<&2, U32>}, +h11: {List.get(&2, U32, regs, 11n) == Some{xc} : Maybe<&2, U32>},
  +regs1: List<&2, U32>, +nx3: U32, +pg3: U32, +z: U32, +pend3: U32, +hl1: {List.length(&2, U32, regs1) == 63n : Nat},
  +k1: {List.get(&2, U32, regs1, 1n) == List.get(&2, U32, regs, 1n) : Maybe<&2, U32>},
  +k11: {List.get(&2, U32, regs1, 11n) == List.get(&2, U32, regs, 11n) : Maybe<&2, U32>},
  +hnext: {Bool.or(U32.is_eq(nx3, nx), Bool.and(D.Pend.none(ps), U32.is_eq(nx3, U32.inc(nx)))) == True{} : Bool},
  +m3: Cr.Cir.Cells, +st4: Cr.Cir.State, qd: DecQ(ds, ks, img, regs, m, nx, fi, im, lim, inp, foc, F, xc, vf, yc, va, bv, vb, kind, q, hv, fs, sp, ps, List.set(&2, U32, regs1, 2n, z), m3, nx3, pg3, z, pend3, st4)) ->
  D.PostB(False{}, Cr.Cir.exec(f, Cr.Cir.Stmt.seq{Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.x())), Cr.Cir.Stmt.nop{}}, st4), s => K.MV.next(ds, ks, img, st0, t, w, s), s => st2 => D.HR(ds, t, s, st2), B, lim):
  match qd:
    case Tuple{+m4, Tuple{+d, Tuple{+pend4, Tuple{+ps4, Tuple{+est4, Tuple{_, Tuple{Tuple{Tuple{+isx, _}, Tuple{_, Tuple{_, Tuple{+hfr4, Tuple{+hp4, hio4}}}}}, Tuple{+zs4, hac4}}}}}}}}:
      +regsP = List.set(&2, U32, regs1, 2n, z)
      +regs5 = List.set(&2, U32, regsP, 5n, d)
      +regsD = List.set(&2, U32, regs5, 3n, pend4)
      +regsF = List.set(&2, U32, regsD, 0n, xc)
      +S4 = {Cr.Cir.State{regsD, m4, nx3, fi, im, pg3, lim, inp, Nil{}, 0} : Cr.Cir.State}
      +S5 = {Cr.Cir.State{regsF, m4, nx3, fi, im, pg3, lim, inp, Nil{}, 0} : Cr.Cir.State}
      +hlP = X.L.len(regs1, 2n, z, 63n, hl1)
      +hl5 = X.L.len(regsP, 5n, d, 63n, hlP)
      +hlD = X.L.len(regs5, 3n, pend4, 63n, hl5)
      +hlF = X.L.len(regsD, 0n, xc, 63n, hlD)
      +ev11 = X.L.go(regs5, 3n, 11n, pend4, xc, {==}, X.L.go(regsP, 5n, 11n, d, xc, {==}, X.L.go(regs1, 2n, 11n, z, xc, {==},
        Equal.trans(Maybe<&2, U32>, List.get(&2, U32, regs1, 11n), List.get(&2, U32, regs, 11n), Some{xc}, k11, h11))))
      +eqr = Equal.trans(Cr.Cir.Out, Cr.Cir.exec(f, Cr.Cir.Stmt.seq{Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.x())), Cr.Cir.Stmt.nop{}}, S4), Cr.Cir.exec(f, Cr.Cir.Stmt.nop{}, S5), Cr.Cir.Out.next{S5},
        Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, Cr.Cir.Stmt.nop{}, S5), Cr.Cir.exec(f, Cr.Cir.Stmt.seq{Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.x())), Cr.Cir.Stmt.nop{}}, S4),
          X.rw.seq(f, Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.x())), Cr.Cir.Stmt.nop{}, S4, S5, X.run.set(f, 0n, Mc.M.g(11n), S4, xc, ev11, hlD, {==}))),
        X.run.nop(f, S5))
      +g0 = X.L.gs(regsD, 0n, xc, X.L.lt(regsD, 0n, hlD, {==}))
      +g1 = X.L.go(regsD, 0n, 1n, xc, 0, {==}, X.L.go(regs5, 3n, 1n, pend4, 0, {==}, X.L.go(regsP, 5n, 1n, d, 0, {==}, X.L.go(regs1, 2n, 1n, z, 0, {==},
        Equal.trans(Maybe<&2, U32>, List.get(&2, U32, regs1, 1n), List.get(&2, U32, regs, 1n), Some{0}, k1, h1)))))
      +g2 = X.L.go(regsD, 0n, 2n, xc, z, {==}, X.L.go(regs5, 3n, 2n, pend4, z, {==}, X.L.go(regsP, 5n, 2n, d, z, {==},
        X.L.gs(regs1, 2n, z, X.L.lt(regs1, 2n, hl1, {==})))))
      +g3 = X.L.go(regsD, 0n, 3n, xc, pend4, {==}, X.L.gs(regs5, 3n, pend4, X.L.lt(regs5, 3n, hl5, {==})))
      +RL = D.R59.list(D.R59.of(regsF))
      +eRG = {(%g0 : {regsF == D.RG(Maybe.default(&2, U32, _, 0), 0, z, pend4, RL) : List<&2, U32>};
        %g1 : {regsF == D.RG(Maybe.default(&2, U32, List.get(&2, U32, regsF, 0n), 0), Maybe.default(&2, U32, _, 0), z, pend4, RL) : List<&2, U32>};
        %g2 : {regsF == D.RG(Maybe.default(&2, U32, List.get(&2, U32, regsF, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, regsF, 1n), 0),
          Maybe.default(&2, U32, _, 0), pend4, RL) : List<&2, U32>};
        %g3 : {regsF == D.RG(Maybe.default(&2, U32, List.get(&2, U32, regsF, 0n), 0), Maybe.default(&2, U32, List.get(&2, U32, regsF, 1n), 0),
          Maybe.default(&2, U32, List.get(&2, U32, regsF, 2n), 0), Maybe.default(&2, U32, _, 0), RL) : List<&2, U32>};
        rg.of(regsF, hlF)) : {regsF == D.RG(xc, 0, z, pend4, RL) : List<&2, U32>}}
      +w2 = D.A.w(False{}, vf, Con{D.AF{kind, q, False{}, va, vb}, fs})
      +inv = {(D.Wit{False{}, vf, Con{D.AF{kind, q, False{}, va, vb}, fs}, xc, z, pend4, ps4, D.R59.of(regsF)}, ((et2, ({==}, ({==}, (afs2, (eRG, (isx, (hfr4, (hp4, (hio4, ({==}, {==})))))))))),
        (zs4, hac4))) : D.Inv(ds, ks, img, S5, t, w2)}
      %Equal.sym(Cr.Cir.State, st4, S4, est4) : D.PostB(False{}, Cr.Cir.exec(f, Cr.Cir.Stmt.seq{Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.x())), Cr.Cir.Stmt.nop{}}, _), s => K.MV.next(ds, ks, img, st0, t, w, s), s => st2 => D.HR(ds, t, s, st2), B, lim)
      %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, Cr.Cir.Stmt.seq{Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.x())), Cr.Cir.Stmt.nop{}}, S4), Cr.Cir.Out.next{S5}, eqr) : D.PostB(False{}, _, s => K.MV.next(ds, ks, img, st0, t, w, s), s => st2 => D.HR(ds, t, s, st2), B, lim)
      (Inl{(w2, (inv, ew2))}, peak.fin(ds, st0, t, nx, nx3, fi, ps, hmc, hnd, hnext))

# M.dec of the focus' old cell, then the round's end
def dec.k(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>, +m: Cr.Cir.Cells,
  +nx: U32, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +foc: U32, +F: Bk.Term, +xc: U32, +vf: Bk.Term, +yc: U32,
  +va: Bk.Term, +bv: U32, +vb: Bk.Term, +kind: D.FK, +q: Bk.Quan, +hv: U32, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +st0: Cr.Cir.State, +t: Bk.Term, +w: Nat, +B: Nat,
  +hmc: {D.Mem.cells(st0) == Nat.sub(U32.to_nat(nx), U32.to_nat(fi)) : Nat},
  hnd: {D.Pend.none(ps) == True{} : Bool} -> N.Le(1n+Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), D.Need(ds, st0, t)),
  +et2: {D.A.plugs(Con{D.AF{kind, q, False{}, va, vb}, fs}, vf) == t : Bk.Term}, +ew2: N.Le(1n+D.A.w(False{}, vf, Con{D.AF{kind, q, False{}, va, vb}, fs}), w), +afs2: D.AFs.ok(ds, Con{D.AF{kind, q, False{}, va, vb}, fs}),
  +h1: {List.get(&2, U32, regs, 1n) == Some{0} : Maybe<&2, U32>}, +h11: {List.get(&2, U32, regs, 11n) == Some{xc} : Maybe<&2, U32>},
  +h8: {List.get(&2, U32, regs, 8n) == Some{foc} : Maybe<&2, U32>}, +st3: Cr.Cir.State, pq: PushQ(ds, ks, img, regs, m, nx, fi, im, lim, inp, foc, F, xc, vf, yc, va, bv, vb, kind, q, hv, fs, sp, ps, st3)) ->
  D.PostB(False{}, Cr.Cir.exec(f, Cr.Cir.Stmt.seq{Mc.M.dec(Mc.R.c()), Cr.Cir.Stmt.seq{Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.x())), Cr.Cir.Stmt.nop{}}}, st3), s => K.MV.next(ds, ks, img, st0, t, w, s), s => st2 => D.HR(ds, t, s, st2), B, lim):
  match pq:
    case Tuple{+regs1, Tuple{+m3, Tuple{+nx3, Tuple{+pg3, Tuple{+z, Tuple{+pend3, Tuple{+ps3, Tuple{+zs3, Tuple{+est, Tuple{+hl1,
      Tuple{Tuple{+k1, Tuple{+k2, Tuple{+k8, Tuple{+k11, Tuple{+k12, Tuple{+k13, _}}}}}}, Tuple{+h3p, Tuple{+hnext, Tuple{+hs3, hac3}}}}}}}}}}}}}}:
      +regsP = List.set(&2, U32, regs1, 2n, z)
      +S3 = {Cr.Cir.State{regsP, m3, nx3, fi, im, pg3, lim, inp, Nil{}, 0} : Cr.Cir.State}
      +h81 = Equal.trans(Maybe<&2, U32>, List.get(&2, U32, regs1, 8n), List.get(&2, U32, regs, 8n), Some{foc}, k8, h8)
      +hlP = X.L.len(regs1, 2n, z, 63n, hl1)
      +h8P = X.L.go(regs1, 2n, 8n, z, foc, {==}, h81)
      +h3P = X.L.go(regs1, 2n, 3n, z, pend3, {==}, h3p)
      +hsw = hsk.swap(True{}, ds, ks, img, m3, nx3, fi, im, D.Rt{xc, vf}, D.Rt{foc, F}, Nil{}, Con{D.AF{kind, q, False{}, va, vb}, fs}, z, pend3, ps3, hs3)
      +acw = acc.swap(True{}, ds, ks, img, m3, nx3, fi, im, D.Rt{xc, vf}, D.Rt{foc, F}, Nil{}, z, Con{D.AF{kind, q, False{}, va, vb}, fs}, ps3, zs3, hac3)
      hd = D.dec.post(f, True{}, ds, ks, img, regsP, m3, nx3, fi, im, pg3, lim, inp, 8n, [D.Rt{xc, vf}], Nil{}, Con{D.AF{kind, q, False{}, va, vb}, fs}, z, pend3, ps3,
        foc, F, Nil{}, zs3, hsw, acw, Unit{}, hlP, h8P, h3P, {==})
      %Equal.sym(Cr.Cir.State, st3, S3, est) : D.PostB(False{}, Cr.Cir.exec(f, Cr.Cir.Stmt.seq{Mc.M.dec(Mc.R.c()), Cr.Cir.Stmt.seq{Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.x())), Cr.Cir.Stmt.nop{}}}, _), s => K.MV.next(ds, ks, img, st0, t, w, s), s => st2 => D.HR(ds, t, s, st2), B, lim)
      D.postb.seq(f, False{}, Mc.M.dec(Mc.R.c()), Cr.Cir.Stmt.seq{Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.x())), Cr.Cir.Stmt.nop{}}, S3, st2 => DecQ(ds, ks, img, regs, m, nx, fi, im, lim, inp, foc, F, xc, vf, yc, va, bv, vb, kind, q, hv, fs, sp, ps, regsP, m3, nx3, pg3, z, pend3, st2), s => K.MV.next(ds, ks, img, st0, t, w, s), s => st2 => Empty, s => st2 => D.HR(ds, t, s, st2), B, lim,
        D.postb.wk(False{}, Cr.Cir.exec(f, Mc.M.dec(Mc.R.c()), S3), st2 => DecQ(ds, ks, img, regs, m, nx, fi, im, lim, inp, foc, F, xc, vf, yc, va, bv, vb, kind, q, hv, fs, sp, ps, regsP, m3, nx3, pg3, z, pend3, st2), s => st2 => Empty, 0n, B, lim, hd,
          N.le_zero(B)),
        s => st2 => e => Empty.absurd(D.HR(ds, t, s, st2), e),
        +st4 => qd => fin.k(f, ds, ks, img, regs, m, nx, fi, im, lim, inp, foc, F, xc, vf, yc, va, bv, vb, kind, q, hv, fs, sp, ps, st0, t, w, B, hmc, hnd, et2, ew2, afs2, h1, h11, regs1, nx3, pg3, z, pend3, hl1, k1, k11, hnext, m3, st4, qd))

# M.alloc of the frame's cell, within the budget: a new cell only when the
# pend list is empty (pend 0), when the budget has room for it
def alloc.run(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>, +m: Cr.Cir.Cells,
  +nx: U32, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +foc: U32, +F: Bk.Term, +xc: U32, +vf: Bk.Term, +yc: U32,
  +va: Bk.Term, +bv: U32, +vb: Bk.Term, +kind: D.FK, +q: Bk.Quan, +hv: U32, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +pg: U32, +pend: U32, +zs: List<&2, D.Rt>, +B: Nat,
  hroom: Or(N.Le(Nat.mul(20n, Nat.add(U32.to_nat(nx), 1n)), B), {U32.is_eq(pend, 0) == False{} : Bool}),
  +hs: D.HS(ds, ks, img, m, nx, fi, im, Con{D.Rt{yc, va}, List.append(&2, D.Rt, UB(kind, bv, vb), [D.Rt{xc, vf}, D.Rt{foc, F}])}, Nil{}, fs, sp, pend, ps),
  +hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, Con{D.Rt{yc, va}, List.append(&2, D.Rt, UB(kind, bv, vb), [D.Rt{xc, vf}, D.Rt{foc, F}])}, Nil{}, sp, fs, ps, zs),
  +hl: {List.length(&2, U32, regs) == 63n : Nat}, +h3: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>}) ->
  D.PostB(False{}, Cr.Cir.exec(f, Mc.M.alloc(16n), Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, Nil{}, 0}), st2 => AlQ(ds, ks, img, regs, m, nx, fi, im, lim, inp, foc, F, xc, vf, yc, va, bv, vb, kind, q, hv, fs, sp, ps, st2), s => st2 => Empty, B, lim):
  match hroom:
    case Inl{hle}:
      D.postb.wk(False{}, Cr.Cir.exec(f, Mc.M.alloc(16n), Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, Nil{}, 0}), st2 => AlQ(ds, ks, img, regs, m, nx, fi, im, lim, inp, foc, F, xc, vf, yc, va, bv, vb, kind, q, hv, fs, sp, ps, st2), s => st2 => Empty, Nat.mul(20n, Nat.add(U32.to_nat(nx), 1n)), B, lim,
        D.alloc.post(f, True{}, ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, 16n, [1n, 2n, 8n, 11n, 12n, 13n], Con{D.Rt{yc, va}, List.append(&2, D.Rt, UB(kind, bv, vb), [D.Rt{xc, vf}, D.Rt{foc, F}])}, Nil{}, fs, sp, pend, ps, Nil{}, zs,
          hs, hac, hl, h3, {==}, {==}), hle)
    case Inr{hne}:
      postb.noom(False{}, Cr.Cir.exec(f, Mc.M.alloc(16n), Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, Nil{}, 0}), st2 => AlQ(ds, ks, img, regs, m, nx, fi, im, lim, inp, foc, F, xc, vf, yc, va, bv, vb, kind, q, hv, fs, sp, ps, st2), s => st2 => Empty, Nat.mul(20n, Nat.add(U32.to_nat(nx), 1n)), B, lim,
        D.alloc.post(f, True{}, ds, ks, img, regs, m, nx, fi, im, pg, lim, inp, 16n, [1n, 2n, 8n, 11n, 12n, 13n], Con{D.Rt{yc, va}, List.append(&2, D.Rt, UB(kind, bv, vb), [D.Rt{xc, vf}, D.Rt{foc, F}])}, Nil{}, fs, sp, pend, ps, Nil{}, zs,
          hs, hac, hl, h3, {==}, {==}), noom.alloc(f, regs, m, nx, fi, im, pg, lim, inp, pend, h3, hne))

# the push of a frame after the incs: M.push, M.dec of the old focus, the
# focus gets the frame's hole; an admin move within the round's peak
def tail.mv(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>, +m: Cr.Cir.Cells,
  +nx: U32, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +foc: U32, +F: Bk.Term, +xc: U32, +vf: Bk.Term, +yc: U32,
  +va: Bk.Term, +bv: U32, +vb: Bk.Term, +kind: D.FK, +q: Bk.Quan, +hv: U32, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +pg: U32, +st0: Cr.Cir.State, +t: Bk.Term, +w: Nat, +hexp: Cr.Cir.Expr, +bexp: Cr.Cir.Expr, +B: Nat,
  +pend: U32, +zs: List<&2, D.Rt>,
  hroom: Or(N.Le(Nat.mul(20n, Nat.add(U32.to_nat(nx), 1n)), B), {U32.is_eq(pend, 0) == False{} : Bool}),
  hnd: {D.Pend.none(ps) == True{} : Bool} -> N.Le(1n+Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), D.Need(ds, st0, t)),
  +hmc: {D.Mem.cells(st0) == Nat.sub(U32.to_nat(nx), U32.to_nat(fi)) : Nat},
  +et2: {D.A.plugs(Con{D.AF{kind, q, False{}, va, vb}, fs}, vf) == t : Bk.Term}, +ew2: N.Le(1n+D.A.w(False{}, vf, Con{D.AF{kind, q, False{}, va, vb}, fs}), w), +afs2: D.AFs.ok(ds, Con{D.AF{kind, q, False{}, va, vb}, fs}),
  +hs: D.HS(ds, ks, img, m, nx, fi, im, Con{D.Rt{yc, va}, List.append(&2, D.Rt, UB(kind, bv, vb), [D.Rt{xc, vf}, D.Rt{foc, F}])}, Nil{}, fs, sp, pend, ps),
  +hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, Con{D.Rt{yc, va}, List.append(&2, D.Rt, UB(kind, bv, vb), [D.Rt{xc, vf}, D.Rt{foc, F}])}, Nil{}, sp, fs, ps, zs),
  +hl: {List.length(&2, U32, regs) == 63n : Nat}, +h1: {List.get(&2, U32, regs, 1n) == Some{0} : Maybe<&2, U32>},
  +h2: {List.get(&2, U32, regs, 2n) == Some{sp} : Maybe<&2, U32>}, +h3: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>},
  +h8: {List.get(&2, U32, regs, 8n) == Some{foc} : Maybe<&2, U32>}, +h11: {List.get(&2, U32, regs, 11n) == Some{xc} : Maybe<&2, U32>},
  +h12: {List.get(&2, U32, regs, 12n) == Some{yc} : Maybe<&2, U32>},
  eh: @regs2: List<&2, U32> -> @m2: Cr.Cir.Cells -> @nx2: U32 -> @pg2: U32 -> {List.get(&2, U32, regs2, 8n) == Some{foc} : Maybe<&2, U32>} ->
    D.IsK(True{}, ds, m2, im, fi, nx2, ks, img, foc, F) ->
    {Cr.Cir.eval(hexp, Cr.Cir.State{regs2, m2, nx2, fi, im, pg2, lim, inp, Nil{}, 0}) == Some{hv} : Maybe<&2, U32>},
  eb: @regs2: List<&2, U32> -> @m2: Cr.Cir.Cells -> @nx2: U32 -> @pg2: U32 -> {List.get(&2, U32, regs2, 13n) == List.get(&2, U32, regs, 13n) : Maybe<&2, U32>} ->
    {Cr.Cir.eval(bexp, Cr.Cir.State{regs2, m2, nx2, fi, im, pg2, lim, inp, Nil{}, 0}) == Some{bv} : Maybe<&2, U32>},
  +hok: HdOK(hv, kind, q)) ->
  D.PostB(False{}, Cr.Cir.exec(f, Cr.Cir.Stmt.seq{Mc.M.push(hexp, Mc.M.g(Mc.R.y()), bexp), Cr.Cir.Stmt.seq{Mc.M.dec(Mc.R.c()), Cr.Cir.Stmt.seq{Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.x())), Cr.Cir.Stmt.nop{}}}}, Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, Nil{}, 0}), s => K.MV.next(ds, ks, img, st0, t, w, s), s => st2 => D.HR(ds, t, s, st2), B, lim):
  D.postb.seq(f, False{}, Mc.M.push(hexp, Mc.M.g(Mc.R.y()), bexp), Cr.Cir.Stmt.seq{Mc.M.dec(Mc.R.c()), Cr.Cir.Stmt.seq{Mc.M.set(Mc.R.focus(), Mc.M.g(Mc.R.x())), Cr.Cir.Stmt.nop{}}}, Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, Nil{}, 0}, st3 => PushQ(ds, ks, img, regs, m, nx, fi, im, lim, inp, foc, F, xc, vf, yc, va, bv, vb, kind, q, hv, fs, sp, ps, st3), s => K.MV.next(ds, ks, img, st0, t, w, s), s => st2 => Empty, s => st2 => D.HR(ds, t, s, st2), B, lim,
    D.postb.seq(f, False{}, Mc.M.alloc(16n), X.sel.b(Mc.M.push(hexp, Mc.M.g(Mc.R.y()), bexp)), Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, Nil{}, 0}, st2 => AlQ(ds, ks, img, regs, m, nx, fi, im, lim, inp, foc, F, xc, vf, yc, va, bv, vb, kind, q, hv, fs, sp, ps, st2), st3 => PushQ(ds, ks, img, regs, m, nx, fi, im, lim, inp, foc, F, xc, vf, yc, va, bv, vb, kind, q, hv, fs, sp, ps, st3), s => st2 => Empty, s => st2 => Empty, B, lim,
      alloc.run(f, ds, ks, img, regs, m, nx, fi, im, lim, inp, foc, F, xc, vf, yc, va, bv, vb, kind, q, hv, fs, sp, ps, pg, pend, zs, B, hroom, hs, hac, hl, h3), s => st2 => e => e,
      +st1 => qa => push.k(f, ds, ks, img, regs, m, nx, fi, im, lim, inp, foc, F, xc, vf, yc, va, bv, vb, kind, q, hv, fs, sp, ps, hexp, bexp, B, h8, h2, h12, eh, eb, hok, st1, qa)),
    s => st2 => e => Empty.absurd(D.HR(ds, t, s, st2), e),
    +st3 => pq => dec.k(f, ds, ks, img, regs, m, nx, fi, im, lim, inp, foc, F, xc, vf, yc, va, bv, vb, kind, q, hv, fs, sp, ps, st0, t, w, B, hmc, hnd, et2, ew2, afs2, h1, h11, h8, st3, pq))

# a round from mode 0 whose focus is no value: M.ev's first statements, then
# its tests of the tag (B.else)
def ev.pre.E(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32,
  +pend: U32, +r4: U32, +r5: U32, +r6: U32, +r7: U32, +r8: U32, +r9: U32, +r10: U32, +r11: U32, +r12: U32, +r13: U32, +r14: U32, +r15: U32, +r16: U32, +r17: U32, +r18: U32, +r19: U32, +r20: U32, +r21: U32, +r22: U32, +r23: U32, +r24: U32, +r25: U32, +r26: U32, +r27: U32, +r28: U32, +r29: U32, +r30: U32, +r31: U32, +r32: U32, +r33: U32, +r34: U32, +r35: U32, +r36: U32, +r37: U32, +r38: U32, +r39: U32, +r40: U32, +r41: U32, +r42: U32, +r43: U32, +r44: U32, +r45: U32, +r46: U32, +r47: U32, +r48: U32, +r49: U32, +r50: U32, +r51: U32, +r52: U32, +r53: U32, +r54: U32, +r55: U32, +r56: U32, +r57: U32, +r58: U32, +r59: U32, +r60: U32, +r61: U32, +r62: U32, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32,
  +inp: List<&2, Word(8n)>, +focus: Bk.Term,
  +nd: D.Nd(ds, im, fi, nx, foc, Cr.Cir.Cells.get(m, foc), focus, D.A.tag(focus)),
  +tb: D.Tbl(m, im, fi, nx), +hv: {D.Fl(m, foc, 256) == False{} : Bool}, +h0: {K.A.f4(focus) == 0 : U32}) ->
  {Cr.Cir.exec(f, D.B.body(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)) == Cr.Cir.exec(f, K.B.else(), K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)) : Cr.Cir.Out}:
  match nd:
    case Tuple{+valid, Tuple{_, Tuple{+etag, _}}}:
      +st1 = K.ev.st1(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)
      +st2 = K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)
      +f0 = D.Fd(0n, m, foc)
      +ef1 = D.ev.fld(0n, Mc.M.g(Mc.R.c()), D.St.regs(st1), m, nx, fi, im, pg, lim, inp, Nil{}, 0, foc, {==}, valid)
      +ef2 = D.ev.fld(0n, Mc.M.g(Mc.R.c()), D.St.regs(st2), m, nx, fi, im, pg, lim, inp, Nil{}, 0, foc, {==}, valid)
      +etg = D.ev.op(Wa.Wasm.Op.and{}, Mc.M.f(0n, Mc.M.g(Mc.R.c())), Mc.M.c(63), st1, f0, 63, ef1, {==})
      +etg2 = D.ev.op(Wa.Wasm.Op.and{}, Mc.M.f(0n, Mc.M.g(Mc.R.c())), Mc.M.c(63), st2, f0, 63, ef2, {==})
      +efl = D.ev.op(Wa.Wasm.Op.ne{}, Mc.M.and(Mc.M.f(0n, Mc.M.g(Mc.R.c())), Mc.M.c(256)), Mc.M.c(0), st2, Wa.Wasm.op(Wa.Wasm.Op.and{}, f0, 256), 0,
        D.ev.op(Wa.Wasm.Op.and{}, Mc.M.f(0n, Mc.M.g(Mc.R.c())), Mc.M.c(256), st2, f0, 256, ef2, {==}), {==})
      +addr = Wa.Wasm.op(Wa.Wasm.Op.add{}, 272, Wa.Wasm.op(Wa.Wasm.Op.and{}, f0, 63))
      +eadr = D.ev.op(Wa.Wasm.Op.add{}, Mc.M.c(272), Mc.M.tag(Mc.M.g(Mc.R.c())), st2, 272, Wa.Wasm.op(Wa.Wasm.Op.and{}, f0, 63), {==}, etg2)
      +vt = K.vt.of(m, im, fi, nx, f0, focus, etag, tb)
      +e4 = Cr.Cir.Cell.get(4n, Cr.Cir.Cells.get(m, addr))
      +ee4 = D.ev.fld(4n, Mc.M.add(Mc.M.c(272), Mc.M.tag(Mc.M.g(Mc.R.c()))), D.St.regs(st2), m, nx, fi, im, pg, lim, inp, Nil{}, 0, addr, eadr, vt)
      +ene = D.ev.op(Wa.Wasm.Op.ne{}, Mc.M.entry(4n, Mc.M.g(Mc.R.c())), Mc.M.c(0), st2, e4, 0, ee4, {==})
      +flv = Wa.Wasm.op(Wa.Wasm.Op.ne{}, Wa.Wasm.op(Wa.Wasm.Op.and{}, f0, 256), 0)
      +nev = Wa.Wasm.op(Wa.Wasm.Op.ne{}, e4, 0)
      +ec2 = D.ev.op(Wa.Wasm.Op.or{}, Mc.M.flag(Mc.M.g(Mc.R.c()), Mc.F.value()), Mc.M.ne(Mc.M.entry(4n, Mc.M.g(Mc.R.c())), Mc.M.c(0)), st2, flv, nev, efl, ene)
      +z2 = K.z.of(m, im, fi, nx, f0, focus, etag, tb, hv, h0)
      +ez = D.eq.if.e(f, K.B.cond2(), Mc.M.set(Mc.R.mode(), Mc.M.c(1)), K.B.else(), st2, Wa.Wasm.op(Wa.Wasm.Op.or{}, flv, nev), ec2, z2)
      %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, D.B.body(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)), Cr.Cir.exec(f, Mc.M.ev(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)),
        D.eq.if.t(f, Mc.M.eq(Mc.M.g(Mc.R.mode()), Mc.M.c(0)), Mc.M.ev(), Mc.M.ret(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), 1, {==}, {==})) :
        {_ == Cr.Cir.exec(f, K.B.else(), st2) : Cr.Cir.Out}
      %D.rw.seq(f, Mc.M.set(Mc.R.c(), Mc.M.g(Mc.R.focus())), K.B.ev2(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), st1,
        D.eq.set(f, 8n, Mc.M.g(Mc.R.focus()), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), foc, {==}, {==})) : {_ == Cr.Cir.exec(f, K.B.else(), st2) : Cr.Cir.Out}
      %D.rw.seq(f, Mc.M.set(Mc.R.tag(), Mc.M.tag(Mc.M.g(Mc.R.c()))), K.B.ev3(), st1, st2,
        D.eq.set(f, 10n, Mc.M.tag(Mc.M.g(Mc.R.c())), st1, D.TgW(f0), etg, {==})) : {_ == Cr.Cir.exec(f, K.B.else(), st2) : Cr.Cir.Out}
      %X.rw.seq_nop(f, Cr.Cir.Stmt.if{K.B.cond2(), Mc.M.set(Mc.R.mode(), Mc.M.c(1)), K.B.else()}, st2) : {_ == Cr.Cir.exec(f, K.B.else(), st2) : Cr.Cir.Out}
      ez

# the parts of an if, to name the parts of a statement of impl.bend without
# copying them


# M.ev's tests of the tag: the branch of each tag
def br.app(+f: Nat, +st: Cr.Cir.State, +f0: U32, +etag: {D.TgW(f0) == 8 : U32},
  +er: {Cr.Cir.eval(Mc.M.g(Mc.R.tag()), st) == Some{D.TgW(f0)} : Maybe<&2, U32>}) ->
  {Cr.Cir.exec(f, K.B.else(), st) == Cr.Cir.exec(f, Mc.M.ev.app(), st) : Cr.Cir.Out}:
  D.eq.if.t(f, Mc.M.eq(Mc.M.g(Mc.R.tag()), Mc.M.c(8)), Mc.M.ev.app(), K.B.e1(), st, Wa.Wasm.op(Wa.Wasm.Op.eq{}, D.TgW(f0), 8),
    D.ev.op(Wa.Wasm.Op.eq{}, Mc.M.g(Mc.R.tag()), Mc.M.c(8), st, D.TgW(f0), 8, er, {==}),
    (%Equal.sym(U32, D.TgW(f0), 8, etag) : {U32.is_zero(Wa.Wasm.op(Wa.Wasm.Op.eq{}, _, 8)) == False{} : Bool}; {==}))

def br.let(+f: Nat, +st: Cr.Cir.State, +f0: U32, +etag: {D.TgW(f0) == 3 : U32},
  +er: {Cr.Cir.eval(Mc.M.g(Mc.R.tag()), st) == Some{D.TgW(f0)} : Maybe<&2, U32>}) ->
  {Cr.Cir.exec(f, K.B.else(), st) == Cr.Cir.exec(f, Mc.M.ev.let(), st) : Cr.Cir.Out}:
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, K.B.else(), st), Cr.Cir.exec(f, K.B.e1(), st),
    D.eq.if.e(f, Mc.M.eq(Mc.M.g(Mc.R.tag()), Mc.M.c(8)), Mc.M.ev.app(), K.B.e1(), st, Wa.Wasm.op(Wa.Wasm.Op.eq{}, D.TgW(f0), 8),
      D.ev.op(Wa.Wasm.Op.eq{}, Mc.M.g(Mc.R.tag()), Mc.M.c(8), st, D.TgW(f0), 8, er, {==}), K.tag.ne(f0, 3, 8, etag, {==}))) :
    {_ == Cr.Cir.exec(f, Mc.M.ev.let(), st) : Cr.Cir.Out}
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, K.B.e1(), st), Cr.Cir.exec(f, K.B.e2(), st),
    D.eq.if.e(f, Mc.M.eq(Mc.M.g(Mc.R.tag()), Mc.M.c(1)), Mc.M.ev.ref(), K.B.e2(), st, Wa.Wasm.op(Wa.Wasm.Op.eq{}, D.TgW(f0), 1),
      D.ev.op(Wa.Wasm.Op.eq{}, Mc.M.g(Mc.R.tag()), Mc.M.c(1), st, D.TgW(f0), 1, er, {==}), K.tag.ne(f0, 3, 1, etag, {==}))) :
    {_ == Cr.Cir.exec(f, Mc.M.ev.let(), st) : Cr.Cir.Out}
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, K.B.e2(), st), Cr.Cir.exec(f, K.B.e3(), st),
    D.eq.if.e(f, Mc.M.eq(Mc.M.g(Mc.R.tag()), Mc.M.c(2)), Mc.M.ev.ann(), K.B.e3(), st, Wa.Wasm.op(Wa.Wasm.Op.eq{}, D.TgW(f0), 2),
      D.ev.op(Wa.Wasm.Op.eq{}, Mc.M.g(Mc.R.tag()), Mc.M.c(2), st, D.TgW(f0), 2, er, {==}), K.tag.ne(f0, 3, 2, etag, {==}))) :
    {_ == Cr.Cir.exec(f, Mc.M.ev.let(), st) : Cr.Cir.Out}
  D.eq.if.t(f, Mc.M.eq(Mc.M.g(Mc.R.tag()), Mc.M.c(3)), Mc.M.ev.let(), K.B.e4(), st, Wa.Wasm.op(Wa.Wasm.Op.eq{}, D.TgW(f0), 3),
    D.ev.op(Wa.Wasm.Op.eq{}, Mc.M.g(Mc.R.tag()), Mc.M.c(3), st, D.TgW(f0), 3, er, {==}),
    (%Equal.sym(U32, D.TgW(f0), 3, etag) : {U32.is_zero(Wa.Wasm.op(Wa.Wasm.Op.eq{}, _, 3)) == False{} : Bool}; {==}))

def br.tup(+f: Nat, +st: Cr.Cir.State, +f0: U32, +etag: {D.TgW(f0) == 10 : U32},
  +er: {Cr.Cir.eval(Mc.M.g(Mc.R.tag()), st) == Some{D.TgW(f0)} : Maybe<&2, U32>}) ->
  {Cr.Cir.exec(f, K.B.else(), st) == Cr.Cir.exec(f, Mc.M.ev.tup(), st) : Cr.Cir.Out}:
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, K.B.else(), st), Cr.Cir.exec(f, K.B.e1(), st),
    D.eq.if.e(f, Mc.M.eq(Mc.M.g(Mc.R.tag()), Mc.M.c(8)), Mc.M.ev.app(), K.B.e1(), st, Wa.Wasm.op(Wa.Wasm.Op.eq{}, D.TgW(f0), 8),
      D.ev.op(Wa.Wasm.Op.eq{}, Mc.M.g(Mc.R.tag()), Mc.M.c(8), st, D.TgW(f0), 8, er, {==}), K.tag.ne(f0, 10, 8, etag, {==}))) :
    {_ == Cr.Cir.exec(f, Mc.M.ev.tup(), st) : Cr.Cir.Out}
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, K.B.e1(), st), Cr.Cir.exec(f, K.B.e2(), st),
    D.eq.if.e(f, Mc.M.eq(Mc.M.g(Mc.R.tag()), Mc.M.c(1)), Mc.M.ev.ref(), K.B.e2(), st, Wa.Wasm.op(Wa.Wasm.Op.eq{}, D.TgW(f0), 1),
      D.ev.op(Wa.Wasm.Op.eq{}, Mc.M.g(Mc.R.tag()), Mc.M.c(1), st, D.TgW(f0), 1, er, {==}), K.tag.ne(f0, 10, 1, etag, {==}))) :
    {_ == Cr.Cir.exec(f, Mc.M.ev.tup(), st) : Cr.Cir.Out}
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, K.B.e2(), st), Cr.Cir.exec(f, K.B.e3(), st),
    D.eq.if.e(f, Mc.M.eq(Mc.M.g(Mc.R.tag()), Mc.M.c(2)), Mc.M.ev.ann(), K.B.e3(), st, Wa.Wasm.op(Wa.Wasm.Op.eq{}, D.TgW(f0), 2),
      D.ev.op(Wa.Wasm.Op.eq{}, Mc.M.g(Mc.R.tag()), Mc.M.c(2), st, D.TgW(f0), 2, er, {==}), K.tag.ne(f0, 10, 2, etag, {==}))) :
    {_ == Cr.Cir.exec(f, Mc.M.ev.tup(), st) : Cr.Cir.Out}
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, K.B.e3(), st), Cr.Cir.exec(f, K.B.e4(), st),
    D.eq.if.e(f, Mc.M.eq(Mc.M.g(Mc.R.tag()), Mc.M.c(3)), Mc.M.ev.let(), K.B.e4(), st, Wa.Wasm.op(Wa.Wasm.Op.eq{}, D.TgW(f0), 3),
      D.ev.op(Wa.Wasm.Op.eq{}, Mc.M.g(Mc.R.tag()), Mc.M.c(3), st, D.TgW(f0), 3, er, {==}), K.tag.ne(f0, 10, 3, etag, {==}))) :
    {_ == Cr.Cir.exec(f, Mc.M.ev.tup(), st) : Cr.Cir.Out}
  D.eq.if.t(f, Mc.M.eq(Mc.M.g(Mc.R.tag()), Mc.M.c(10)), Mc.M.ev.tup(), K.B.e5(), st, Wa.Wasm.op(Wa.Wasm.Op.eq{}, D.TgW(f0), 10),
    D.ev.op(Wa.Wasm.Op.eq{}, Mc.M.g(Mc.R.tag()), Mc.M.c(10), st, D.TgW(f0), 10, er, {==}),
    (%Equal.sym(U32, D.TgW(f0), 10, etag) : {U32.is_zero(Wa.Wasm.op(Wa.Wasm.Op.eq{}, _, 10)) == False{} : Bool}; {==}))

def br.rwt(+f: Nat, +st: Cr.Cir.State, +f0: U32, +etag: {D.TgW(f0) == 18 : U32},
  +er: {Cr.Cir.eval(Mc.M.g(Mc.R.tag()), st) == Some{D.TgW(f0)} : Maybe<&2, U32>}) ->
  {Cr.Cir.exec(f, K.B.else(), st) == Cr.Cir.exec(f, Mc.M.ev.rwt(), st) : Cr.Cir.Out}:
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, K.B.else(), st), Cr.Cir.exec(f, K.B.e1(), st),
    D.eq.if.e(f, Mc.M.eq(Mc.M.g(Mc.R.tag()), Mc.M.c(8)), Mc.M.ev.app(), K.B.e1(), st, Wa.Wasm.op(Wa.Wasm.Op.eq{}, D.TgW(f0), 8),
      D.ev.op(Wa.Wasm.Op.eq{}, Mc.M.g(Mc.R.tag()), Mc.M.c(8), st, D.TgW(f0), 8, er, {==}), K.tag.ne(f0, 18, 8, etag, {==}))) :
    {_ == Cr.Cir.exec(f, Mc.M.ev.rwt(), st) : Cr.Cir.Out}
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, K.B.e1(), st), Cr.Cir.exec(f, K.B.e2(), st),
    D.eq.if.e(f, Mc.M.eq(Mc.M.g(Mc.R.tag()), Mc.M.c(1)), Mc.M.ev.ref(), K.B.e2(), st, Wa.Wasm.op(Wa.Wasm.Op.eq{}, D.TgW(f0), 1),
      D.ev.op(Wa.Wasm.Op.eq{}, Mc.M.g(Mc.R.tag()), Mc.M.c(1), st, D.TgW(f0), 1, er, {==}), K.tag.ne(f0, 18, 1, etag, {==}))) :
    {_ == Cr.Cir.exec(f, Mc.M.ev.rwt(), st) : Cr.Cir.Out}
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, K.B.e2(), st), Cr.Cir.exec(f, K.B.e3(), st),
    D.eq.if.e(f, Mc.M.eq(Mc.M.g(Mc.R.tag()), Mc.M.c(2)), Mc.M.ev.ann(), K.B.e3(), st, Wa.Wasm.op(Wa.Wasm.Op.eq{}, D.TgW(f0), 2),
      D.ev.op(Wa.Wasm.Op.eq{}, Mc.M.g(Mc.R.tag()), Mc.M.c(2), st, D.TgW(f0), 2, er, {==}), K.tag.ne(f0, 18, 2, etag, {==}))) :
    {_ == Cr.Cir.exec(f, Mc.M.ev.rwt(), st) : Cr.Cir.Out}
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, K.B.e3(), st), Cr.Cir.exec(f, K.B.e4(), st),
    D.eq.if.e(f, Mc.M.eq(Mc.M.g(Mc.R.tag()), Mc.M.c(3)), Mc.M.ev.let(), K.B.e4(), st, Wa.Wasm.op(Wa.Wasm.Op.eq{}, D.TgW(f0), 3),
      D.ev.op(Wa.Wasm.Op.eq{}, Mc.M.g(Mc.R.tag()), Mc.M.c(3), st, D.TgW(f0), 3, er, {==}), K.tag.ne(f0, 18, 3, etag, {==}))) :
    {_ == Cr.Cir.exec(f, Mc.M.ev.rwt(), st) : Cr.Cir.Out}
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, K.B.e4(), st), Cr.Cir.exec(f, K.B.e5(), st),
    D.eq.if.e(f, Mc.M.eq(Mc.M.g(Mc.R.tag()), Mc.M.c(10)), Mc.M.ev.tup(), K.B.e5(), st, Wa.Wasm.op(Wa.Wasm.Op.eq{}, D.TgW(f0), 10),
      D.ev.op(Wa.Wasm.Op.eq{}, Mc.M.g(Mc.R.tag()), Mc.M.c(10), st, D.TgW(f0), 10, er, {==}), K.tag.ne(f0, 18, 10, etag, {==}))) :
    {_ == Cr.Cir.exec(f, Mc.M.ev.rwt(), st) : Cr.Cir.Out}
  D.eq.if.t(f, Mc.M.eq(Mc.M.g(Mc.R.tag()), Mc.M.c(18)), Mc.M.ev.rwt(), K.B.e6(), st, Wa.Wasm.op(Wa.Wasm.Op.eq{}, D.TgW(f0), 18),
    D.ev.op(Wa.Wasm.Op.eq{}, Mc.M.g(Mc.R.tag()), Mc.M.c(18), st, D.TgW(f0), 18, er, {==}),
    (%Equal.sym(U32, D.TgW(f0), 18, etag) : {U32.is_zero(Wa.Wasm.op(Wa.Wasm.Op.eq{}, _, 18)) == False{} : Bool}; {==}))

def br.min(+f: Nat, +st: Cr.Cir.State, +f0: U32, +etag: {D.TgW(f0) == 5 : U32},
  +er: {Cr.Cir.eval(Mc.M.g(Mc.R.tag()), st) == Some{D.TgW(f0)} : Maybe<&2, U32>}) ->
  {Cr.Cir.exec(f, K.B.else(), st) == Cr.Cir.exec(f, Mc.M.ev.min(), st) : Cr.Cir.Out}:
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, K.B.else(), st), Cr.Cir.exec(f, K.B.e1(), st),
    D.eq.if.e(f, Mc.M.eq(Mc.M.g(Mc.R.tag()), Mc.M.c(8)), Mc.M.ev.app(), K.B.e1(), st, Wa.Wasm.op(Wa.Wasm.Op.eq{}, D.TgW(f0), 8),
      D.ev.op(Wa.Wasm.Op.eq{}, Mc.M.g(Mc.R.tag()), Mc.M.c(8), st, D.TgW(f0), 8, er, {==}), K.tag.ne(f0, 5, 8, etag, {==}))) :
    {_ == Cr.Cir.exec(f, Mc.M.ev.min(), st) : Cr.Cir.Out}
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, K.B.e1(), st), Cr.Cir.exec(f, K.B.e2(), st),
    D.eq.if.e(f, Mc.M.eq(Mc.M.g(Mc.R.tag()), Mc.M.c(1)), Mc.M.ev.ref(), K.B.e2(), st, Wa.Wasm.op(Wa.Wasm.Op.eq{}, D.TgW(f0), 1),
      D.ev.op(Wa.Wasm.Op.eq{}, Mc.M.g(Mc.R.tag()), Mc.M.c(1), st, D.TgW(f0), 1, er, {==}), K.tag.ne(f0, 5, 1, etag, {==}))) :
    {_ == Cr.Cir.exec(f, Mc.M.ev.min(), st) : Cr.Cir.Out}
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, K.B.e2(), st), Cr.Cir.exec(f, K.B.e3(), st),
    D.eq.if.e(f, Mc.M.eq(Mc.M.g(Mc.R.tag()), Mc.M.c(2)), Mc.M.ev.ann(), K.B.e3(), st, Wa.Wasm.op(Wa.Wasm.Op.eq{}, D.TgW(f0), 2),
      D.ev.op(Wa.Wasm.Op.eq{}, Mc.M.g(Mc.R.tag()), Mc.M.c(2), st, D.TgW(f0), 2, er, {==}), K.tag.ne(f0, 5, 2, etag, {==}))) :
    {_ == Cr.Cir.exec(f, Mc.M.ev.min(), st) : Cr.Cir.Out}
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, K.B.e3(), st), Cr.Cir.exec(f, K.B.e4(), st),
    D.eq.if.e(f, Mc.M.eq(Mc.M.g(Mc.R.tag()), Mc.M.c(3)), Mc.M.ev.let(), K.B.e4(), st, Wa.Wasm.op(Wa.Wasm.Op.eq{}, D.TgW(f0), 3),
      D.ev.op(Wa.Wasm.Op.eq{}, Mc.M.g(Mc.R.tag()), Mc.M.c(3), st, D.TgW(f0), 3, er, {==}), K.tag.ne(f0, 5, 3, etag, {==}))) :
    {_ == Cr.Cir.exec(f, Mc.M.ev.min(), st) : Cr.Cir.Out}
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, K.B.e4(), st), Cr.Cir.exec(f, K.B.e5(), st),
    D.eq.if.e(f, Mc.M.eq(Mc.M.g(Mc.R.tag()), Mc.M.c(10)), Mc.M.ev.tup(), K.B.e5(), st, Wa.Wasm.op(Wa.Wasm.Op.eq{}, D.TgW(f0), 10),
      D.ev.op(Wa.Wasm.Op.eq{}, Mc.M.g(Mc.R.tag()), Mc.M.c(10), st, D.TgW(f0), 10, er, {==}), K.tag.ne(f0, 5, 10, etag, {==}))) :
    {_ == Cr.Cir.exec(f, Mc.M.ev.min(), st) : Cr.Cir.Out}
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, K.B.e5(), st), Cr.Cir.exec(f, K.B.e6(), st),
    D.eq.if.e(f, Mc.M.eq(Mc.M.g(Mc.R.tag()), Mc.M.c(18)), Mc.M.ev.rwt(), K.B.e6(), st, Wa.Wasm.op(Wa.Wasm.Op.eq{}, D.TgW(f0), 18),
      D.ev.op(Wa.Wasm.Op.eq{}, Mc.M.g(Mc.R.tag()), Mc.M.c(18), st, D.TgW(f0), 18, er, {==}), K.tag.ne(f0, 5, 18, etag, {==}))) :
    {_ == Cr.Cir.exec(f, Mc.M.ev.min(), st) : Cr.Cir.Out}
  D.eq.if.t(f, Mc.M.eq(Mc.M.g(Mc.R.tag()), Mc.M.c(5)), Mc.M.ev.min(), Mc.M.halt(2), st, Wa.Wasm.op(Wa.Wasm.Op.eq{}, D.TgW(f0), 5),
    D.ev.op(Wa.Wasm.Op.eq{}, Mc.M.g(Mc.R.tag()), Mc.M.c(5), st, D.TgW(f0), 5, er, {==}),
    (%Equal.sym(U32, D.TgW(f0), 5, etag) : {U32.is_zero(Wa.Wasm.op(Wa.Wasm.Op.eq{}, _, 5)) == False{} : Bool}; {==}))

# what inc.post gives
def IncQ(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>, +m: Cr.Cir.Cells,
  +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +os: List<&2, D.Rt>, +bs: List<&2, D.Rt>,
  +fs: List<&2, D.AF>, +sp: U32, +pend: U32, +ps: List<&2, U32>, +c: U32, +u: Bk.Term, +xs: List<&2, D.TmpE>, +zs: List<&2, D.Rt>,
  st2: Cr.Cir.State) -> Data:
  D.Ex(Cr.Cir.Cells, m2 => D.P2({st2 == Cr.Cir.State{regs, m2, nx, fi, im, pg, lim, inp, Nil{}, 0} : Cr.Cir.State},
    D.P2({D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m2, fi) == D.Stat(Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), m, fi) : Nat},
    D.P2(D.HSK(True{}, ds, ks, img, m2, nx, fi, im, Con{D.Rt{c, u}, os}, Con{D.Rt{c, u}, bs}, fs, sp, pend, ps),
      D.AccK(True{}, ds, ks, img, m2, nx, fi, im, Con{D.Rt{c, u}, os}, xs, sp, fs, ps, zs)))))

# the push of a frame that holds one part (M.ev.frame): x and y get the parts
# a and b of the focus' cell, each gains a pointer, then tail.mv
def frame2.tl(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>, +m: Cr.Cir.Cells,
  +nx: U32, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +foc: U32, +F: Bk.Term, +xc: U32, +vf: Bk.Term, +yc: U32,
  +va: Bk.Term, +vb: Bk.Term, +kind: D.FK, +q: Bk.Quan, +hv: U32, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +pg: U32, +st0: Cr.Cir.State, +t: Bk.Term, +w: Nat, +hexp: Cr.Cir.Expr, +B: Nat, +pend: U32, +zs: List<&2, D.Rt>, +a: Nat, +b: Nat,
  +hub: {UB(kind, 0, vb) == Nil{} : List<&2, D.Rt>},
  hroom: Or(N.Le(Nat.mul(20n, Nat.add(U32.to_nat(nx), 1n)), B), {U32.is_eq(pend, 0) == False{} : Bool}),
  hnd: {D.Pend.none(ps) == True{} : Bool} -> N.Le(1n+Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), D.Need(ds, st0, t)),
  +hmc: {D.Mem.cells(st0) == Nat.sub(U32.to_nat(nx), U32.to_nat(fi)) : Nat},
  +et2: {D.A.plugs(Con{D.AF{kind, q, False{}, va, vb}, fs}, vf) == t : Bk.Term}, +ew2: N.Le(1n+D.A.w(False{}, vf, Con{D.AF{kind, q, False{}, va, vb}, fs}), w), +afs2: D.AFs.ok(ds, Con{D.AF{kind, q, False{}, va, vb}, fs}),
  +hl: {List.length(&2, U32, regs) == 63n : Nat}, +h1: {List.get(&2, U32, regs, 1n) == Some{0} : Maybe<&2, U32>},
  +h2: {List.get(&2, U32, regs, 2n) == Some{sp} : Maybe<&2, U32>}, +h3: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>},
  +h8: {List.get(&2, U32, regs, 8n) == Some{foc} : Maybe<&2, U32>},
  eh: @regs2: List<&2, U32> -> @m2: Cr.Cir.Cells -> @nx2: U32 -> @pg2: U32 -> {List.get(&2, U32, regs2, 8n) == Some{foc} : Maybe<&2, U32>} ->
    D.IsK(True{}, ds, m2, im, fi, nx2, ks, img, foc, F) ->
    {Cr.Cir.eval(hexp, Cr.Cir.State{regs2, m2, nx2, fi, im, pg2, lim, inp, Nil{}, 0}) == Some{hv} : Maybe<&2, U32>},
  +hok: HdOK(hv, kind, q), +m2: Cr.Cir.Cells, +stB: Cr.Cir.State, qj: IncQ(ds, ks, img, List.set(&2, U32, List.set(&2, U32, regs, 11n, xc), 12n, yc), m2, nx, fi, im, pg, lim, inp, [D.Rt{xc, vf}, D.Rt{foc, F}], Nil{}, fs, sp, pend, ps, yc, va, Nil{}, zs, stB)) ->
  D.PostB(False{}, Cr.Cir.exec(f, X.sel.b(X.sel.b(X.sel.b(X.sel.b(Mc.M.ev.frame(hexp, a, b))))), stB), s => K.MV.next(ds, ks, img, st0, t, w, s), s => st2 => D.HR(ds, t, s, st2), B, lim):
  match qj:
    case Tuple{+m3, Tuple{+est, Tuple{_, Tuple{+hsB, hacB}}}}:
      +hlx = X.L.len(regs, 11n, xc, 63n, hl)
      +hly = X.L.len(List.set(&2, U32, regs, 11n, xc), 12n, yc, 63n, hlx)
      +hsB2 = hsk.drop(True{}, ds, ks, img, m3, nx, fi, im, [D.Rt{yc, va}, D.Rt{xc, vf}, D.Rt{foc, F}], D.Rt{yc, va}, Nil{}, fs, sp, pend, ps, hsB)
      +hsT = {(%Equal.sym(List<&2, D.Rt>, UB(kind, 0, vb), Nil{}, hub) :
          D.HS(ds, ks, img, m3, nx, fi, im, Con{D.Rt{yc, va}, List.append(&2, D.Rt, _, [D.Rt{xc, vf}, D.Rt{foc, F}])}, Nil{}, fs, sp, pend, ps); hsB2) :
        D.HS(ds, ks, img, m3, nx, fi, im, Con{D.Rt{yc, va}, List.append(&2, D.Rt, UB(kind, 0, vb), [D.Rt{xc, vf}, D.Rt{foc, F}])}, Nil{}, fs, sp, pend, ps)}
      +hacT = {(%Equal.sym(List<&2, D.Rt>, UB(kind, 0, vb), Nil{}, hub) :
          D.AccK(True{}, ds, ks, img, m3, nx, fi, im, Con{D.Rt{yc, va}, List.append(&2, D.Rt, _, [D.Rt{xc, vf}, D.Rt{foc, F}])}, Nil{}, sp, fs, ps, zs); hacB) :
        D.AccK(True{}, ds, ks, img, m3, nx, fi, im, Con{D.Rt{yc, va}, List.append(&2, D.Rt, UB(kind, 0, vb), [D.Rt{xc, vf}, D.Rt{foc, F}])}, Nil{}, sp, fs, ps, zs)}
      %Equal.sym(Cr.Cir.State, stB, Cr.Cir.State{List.set(&2, U32, List.set(&2, U32, regs, 11n, xc), 12n, yc), m3, nx, fi, im, pg, lim, inp, Nil{}, 0}, est) : D.PostB(False{}, Cr.Cir.exec(f, X.sel.b(X.sel.b(X.sel.b(X.sel.b(Mc.M.ev.frame(hexp, a, b))))), _), s => K.MV.next(ds, ks, img, st0, t, w, s), s => st2 => D.HR(ds, t, s, st2), B, lim)
      tail.mv(f, ds, ks, img, List.set(&2, U32, List.set(&2, U32, regs, 11n, xc), 12n, yc), m3, nx, fi, im, lim, inp, foc, F, xc, vf, yc, va, 0, vb, kind, q, hv, fs, sp, ps, pg, st0, t, w, hexp, Mc.M.c(0),
        B, pend, zs, hroom, hnd, hmc, et2, ew2, afs2, hsT, hacT, hly,
        X.L.go(List.set(&2, U32, regs, 11n, xc), 12n, 1n, yc, 0, {==}, X.L.go(regs, 11n, 1n, xc, 0, {==}, h1)),
        X.L.go(List.set(&2, U32, regs, 11n, xc), 12n, 2n, yc, sp, {==}, X.L.go(regs, 11n, 2n, xc, sp, {==}, h2)),
        X.L.go(List.set(&2, U32, regs, 11n, xc), 12n, 3n, yc, pend, {==}, X.L.go(regs, 11n, 3n, xc, pend, {==}, h3)),
        X.L.go(List.set(&2, U32, regs, 11n, xc), 12n, 8n, yc, foc, {==}, X.L.go(regs, 11n, 8n, xc, foc, {==}, h8)),
        X.L.go(List.set(&2, U32, regs, 11n, xc), 12n, 11n, yc, xc, {==}, X.L.gs(regs, 11n, xc, X.L.lt(regs, 11n, hl, {==}))),
        X.L.gs(List.set(&2, U32, regs, 11n, xc), 12n, yc, X.L.lt(List.set(&2, U32, regs, 11n, xc), 12n, hlx, {==})),
        eh, regs2 => m2 => nx2 => pg2 => e => {==}, hok)

def frame2.incy(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>, +m: Cr.Cir.Cells,
  +nx: U32, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +foc: U32, +F: Bk.Term, +xc: U32, +vf: Bk.Term, +yc: U32,
  +va: Bk.Term, +vb: Bk.Term, +kind: D.FK, +q: Bk.Quan, +hv: U32, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +pg: U32, +st0: Cr.Cir.State, +t: Bk.Term, +w: Nat, +hexp: Cr.Cir.Expr, +B: Nat, +pend: U32, +zs: List<&2, D.Rt>, +a: Nat, +b: Nat,
  +hub: {UB(kind, 0, vb) == Nil{} : List<&2, D.Rt>},
  hroom: Or(N.Le(Nat.mul(20n, Nat.add(U32.to_nat(nx), 1n)), B), {U32.is_eq(pend, 0) == False{} : Bool}),
  hnd: {D.Pend.none(ps) == True{} : Bool} -> N.Le(1n+Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), D.Need(ds, st0, t)),
  +hmc: {D.Mem.cells(st0) == Nat.sub(U32.to_nat(nx), U32.to_nat(fi)) : Nat},
  +et2: {D.A.plugs(Con{D.AF{kind, q, False{}, va, vb}, fs}, vf) == t : Bk.Term}, +ew2: N.Le(1n+D.A.w(False{}, vf, Con{D.AF{kind, q, False{}, va, vb}, fs}), w), +afs2: D.AFs.ok(ds, Con{D.AF{kind, q, False{}, va, vb}, fs}),
  +hl: {List.length(&2, U32, regs) == 63n : Nat}, +h1: {List.get(&2, U32, regs, 1n) == Some{0} : Maybe<&2, U32>},
  +h2: {List.get(&2, U32, regs, 2n) == Some{sp} : Maybe<&2, U32>}, +h3: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>},
  +h8: {List.get(&2, U32, regs, 8n) == Some{foc} : Maybe<&2, U32>},
  eh: @regs2: List<&2, U32> -> @m2: Cr.Cir.Cells -> @nx2: U32 -> @pg2: U32 -> {List.get(&2, U32, regs2, 8n) == Some{foc} : Maybe<&2, U32>} ->
    D.IsK(True{}, ds, m2, im, fi, nx2, ks, img, foc, F) ->
    {Cr.Cir.eval(hexp, Cr.Cir.State{regs2, m2, nx2, fi, im, pg2, lim, inp, Nil{}, 0}) == Some{hv} : Maybe<&2, U32>},
  +hok: HdOK(hv, kind, q), +stA: Cr.Cir.State, qi: IncQ(ds, ks, img, List.set(&2, U32, List.set(&2, U32, regs, 11n, xc), 12n, yc), m, nx, fi, im, pg, lim, inp, [D.Rt{foc, F}], [D.Rt{yc, va}], fs, sp, pend, ps, xc, vf, Nil{}, zs, stA)) ->
  D.PostB(False{}, Cr.Cir.exec(f, X.sel.b(X.sel.b(X.sel.b(Mc.M.ev.frame(hexp, a, b)))), stA), s => K.MV.next(ds, ks, img, st0, t, w, s), s => st2 => D.HR(ds, t, s, st2), B, lim):
  match qi:
    case Tuple{+m2, Tuple{+est, Tuple{_, Tuple{+hsA, hacA}}}}:
      +hlx = X.L.len(regs, 11n, xc, 63n, hl)
      +hc12 = X.L.gs(List.set(&2, U32, regs, 11n, xc), 12n, yc, X.L.lt(List.set(&2, U32, regs, 11n, xc), 12n, hlx, {==}))
      +hsA2 = hsk.drop(True{}, ds, ks, img, m2, nx, fi, im, [D.Rt{xc, vf}, D.Rt{foc, F}], D.Rt{xc, vf}, [D.Rt{yc, va}], fs, sp, pend, ps, hsA)
      hi = D.inc.post(f, True{}, ds, ks, img, List.set(&2, U32, List.set(&2, U32, regs, 11n, xc), 12n, yc), m2, nx, fi, im, pg, lim, inp, 12n, [D.Rt{xc, vf}, D.Rt{foc, F}], Nil{}, fs, sp, pend, ps,
        yc, va, Nil{}, zs, hsA2, hacA, Unit{}, hc12)
      %Equal.sym(Cr.Cir.State, stA, Cr.Cir.State{List.set(&2, U32, List.set(&2, U32, regs, 11n, xc), 12n, yc), m2, nx, fi, im, pg, lim, inp, Nil{}, 0}, est) : D.PostB(False{}, Cr.Cir.exec(f, X.sel.b(X.sel.b(X.sel.b(Mc.M.ev.frame(hexp, a, b)))), _), s => K.MV.next(ds, ks, img, st0, t, w, s), s => st2 => D.HR(ds, t, s, st2), B, lim)
      D.postb.seq(f, False{}, Mc.M.inc(12n), X.sel.b(X.sel.b(X.sel.b(X.sel.b(Mc.M.ev.frame(hexp, a, b))))), Cr.Cir.State{List.set(&2, U32, List.set(&2, U32, regs, 11n, xc), 12n, yc), m2, nx, fi, im, pg, lim, inp, Nil{}, 0}, st2 => IncQ(ds, ks, img, List.set(&2, U32, List.set(&2, U32, regs, 11n, xc), 12n, yc), m2, nx, fi, im, pg, lim, inp, [D.Rt{xc, vf}, D.Rt{foc, F}], Nil{}, fs, sp, pend, ps, yc, va, Nil{}, zs, st2), s => K.MV.next(ds, ks, img, st0, t, w, s), s => st2 => Empty, s => st2 => D.HR(ds, t, s, st2), B, lim,
        D.postb.wk(False{}, Cr.Cir.exec(f, Mc.M.inc(12n), Cr.Cir.State{List.set(&2, U32, List.set(&2, U32, regs, 11n, xc), 12n, yc), m2, nx, fi, im, pg, lim, inp, Nil{}, 0}), st2 => IncQ(ds, ks, img, List.set(&2, U32, List.set(&2, U32, regs, 11n, xc), 12n, yc), m2, nx, fi, im, pg, lim, inp, [D.Rt{xc, vf}, D.Rt{foc, F}], Nil{}, fs, sp, pend, ps, yc, va, Nil{}, zs, st2), s => st2 => Empty, 0n, B, lim, hi, N.le_zero(B)),
        s => st2 => e => Empty.absurd(D.HR(ds, t, s, st2), e),
        +stB => qj => frame2.tl(f, ds, ks, img, regs, m, nx, fi, im, lim, inp, foc, F, xc, vf, yc, va, vb, kind, q, hv, fs, sp, ps, pg, st0, t, w, hexp, B, pend, zs, a, b, hub, hroom, hnd, hmc, et2, ew2, afs2, hl, h1, h2, h3, h8, eh, hok, m2, stB, qj))

def frame2.mv(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>, +m: Cr.Cir.Cells,
  +nx: U32, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +foc: U32, +F: Bk.Term, +xc: U32, +vf: Bk.Term, +yc: U32,
  +va: Bk.Term, +vb: Bk.Term, +kind: D.FK, +q: Bk.Quan, +hv: U32, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +pg: U32, +st0: Cr.Cir.State, +t: Bk.Term, +w: Nat, +hexp: Cr.Cir.Expr, +B: Nat, +pend: U32, +zs: List<&2, D.Rt>, +a: Nat, +b: Nat,
  +hub: {UB(kind, 0, vb) == Nil{} : List<&2, D.Rt>},
  hroom: Or(N.Le(Nat.mul(20n, Nat.add(U32.to_nat(nx), 1n)), B), {U32.is_eq(pend, 0) == False{} : Bool}),
  hnd: {D.Pend.none(ps) == True{} : Bool} -> N.Le(1n+Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), D.Need(ds, st0, t)),
  +hmc: {D.Mem.cells(st0) == Nat.sub(U32.to_nat(nx), U32.to_nat(fi)) : Nat},
  +et2: {D.A.plugs(Con{D.AF{kind, q, False{}, va, vb}, fs}, vf) == t : Bk.Term}, +ew2: N.Le(1n+D.A.w(False{}, vf, Con{D.AF{kind, q, False{}, va, vb}, fs}), w), +afs2: D.AFs.ok(ds, Con{D.AF{kind, q, False{}, va, vb}, fs}),
  +hl: {List.length(&2, U32, regs) == 63n : Nat}, +h1: {List.get(&2, U32, regs, 1n) == Some{0} : Maybe<&2, U32>},
  +h2: {List.get(&2, U32, regs, 2n) == Some{sp} : Maybe<&2, U32>}, +h3: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>},
  +h8: {List.get(&2, U32, regs, 8n) == Some{foc} : Maybe<&2, U32>},
  eh: @regs2: List<&2, U32> -> @m2: Cr.Cir.Cells -> @nx2: U32 -> @pg2: U32 -> {List.get(&2, U32, regs2, 8n) == Some{foc} : Maybe<&2, U32>} ->
    D.IsK(True{}, ds, m2, im, fi, nx2, ks, img, foc, F) ->
    {Cr.Cir.eval(hexp, Cr.Cir.State{regs2, m2, nx2, fi, im, pg2, lim, inp, Nil{}, 0}) == Some{hv} : Maybe<&2, U32>},
  +hok: HdOK(hv, kind, q), +hxa: {D.Fd(a, m, foc) == xc : U32}, +hyb: {D.Fd(b, m, foc) == yc : U32},
  +hfoc: {Cr.Cir.is_cell(foc, im, fi, nx) == True{} : Bool},
  +hs0: D.HS(ds, ks, img, m, nx, fi, im, [D.Rt{foc, F}], [D.Rt{xc, vf}, D.Rt{yc, va}], fs, sp, pend, ps),
  +hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, [D.Rt{foc, F}], Nil{}, sp, fs, ps, zs)) ->
  D.PostB(False{}, Cr.Cir.exec(f, Mc.M.ev.frame(hexp, a, b), Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, Nil{}, 0}), s => K.MV.next(ds, ks, img, st0, t, w, s), s => st2 => D.HR(ds, t, s, st2), B, lim):
  +S = {Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, Nil{}, 0} : Cr.Cir.State}
  +SX = {Cr.Cir.State{List.set(&2, U32, regs, 11n, xc), m, nx, fi, im, pg, lim, inp, Nil{}, 0} : Cr.Cir.State}
  +SY = {Cr.Cir.State{List.set(&2, U32, List.set(&2, U32, regs, 11n, xc), 12n, yc), m, nx, fi, im, pg, lim, inp, Nil{}, 0} : Cr.Cir.State}
  +hlx = X.L.len(regs, 11n, xc, 63n, hl)
  +evx = Equal.trans(Maybe<&2, U32>, Cr.Cir.eval(Mc.M.f(a, Mc.M.g(8n)), S), Some{D.Fd(a, m, foc)}, Some{xc},
    X.ev.fld(a, Mc.M.g(8n), S, foc, h8, hfoc), Equal.cong(U32, Maybe<&2, U32>, v => Some{v}, D.Fd(a, m, foc), xc, hxa))
  +evy = Equal.trans(Maybe<&2, U32>, Cr.Cir.eval(Mc.M.f(b, Mc.M.g(8n)), SX), Some{D.Fd(b, m, foc)}, Some{yc},
    X.ev.fld(b, Mc.M.g(8n), SX, foc, X.L.go(regs, 11n, 8n, xc, foc, {==}, h8), hfoc), Equal.cong(U32, Maybe<&2, U32>, v => Some{v}, D.Fd(b, m, foc), yc, hyb))
  +ex = X.run.set(f, 11n, Mc.M.f(a, Mc.M.g(8n)), S, xc, evx, hl, {==})
  +ey = X.run.set(f, 12n, Mc.M.f(b, Mc.M.g(8n)), SX, yc, evy, hlx, {==})
  +hc11 = X.L.go(List.set(&2, U32, regs, 11n, xc), 12n, 11n, yc, xc, {==}, X.L.gs(regs, 11n, xc, X.L.lt(regs, 11n, hl, {==})))
  hi = D.inc.post(f, True{}, ds, ks, img, List.set(&2, U32, List.set(&2, U32, regs, 11n, xc), 12n, yc), m, nx, fi, im, pg, lim, inp, 11n, [D.Rt{foc, F}], [D.Rt{yc, va}], fs, sp, pend, ps,
    xc, vf, Nil{}, zs, hs0, hac, Unit{}, hc11)
  %X.rw.seq(f, X.sel.a(Mc.M.ev.frame(hexp, a, b)), X.sel.b(Mc.M.ev.frame(hexp, a, b)), S, SX, ex) : D.PostB(False{}, _, s => K.MV.next(ds, ks, img, st0, t, w, s), s => st2 => D.HR(ds, t, s, st2), B, lim)
  %X.rw.seq(f, X.sel.a(X.sel.b(Mc.M.ev.frame(hexp, a, b))), X.sel.b(X.sel.b(Mc.M.ev.frame(hexp, a, b))), SX, SY, ey) : D.PostB(False{}, _, s => K.MV.next(ds, ks, img, st0, t, w, s), s => st2 => D.HR(ds, t, s, st2), B, lim)
  D.postb.seq(f, False{}, Mc.M.inc(11n), X.sel.b(X.sel.b(X.sel.b(Mc.M.ev.frame(hexp, a, b)))), SY, st2 => IncQ(ds, ks, img, List.set(&2, U32, List.set(&2, U32, regs, 11n, xc), 12n, yc), m, nx, fi, im, pg, lim, inp, [D.Rt{foc, F}], [D.Rt{yc, va}], fs, sp, pend, ps, xc, vf, Nil{}, zs, st2), s => K.MV.next(ds, ks, img, st0, t, w, s), s => st2 => Empty, s => st2 => D.HR(ds, t, s, st2), B, lim,
    D.postb.wk(False{}, Cr.Cir.exec(f, Mc.M.inc(11n), SY), st2 => IncQ(ds, ks, img, List.set(&2, U32, List.set(&2, U32, regs, 11n, xc), 12n, yc), m, nx, fi, im, pg, lim, inp, [D.Rt{foc, F}], [D.Rt{yc, va}], fs, sp, pend, ps, xc, vf, Nil{}, zs, st2), s => st2 => Empty, 0n, B, lim, hi, N.le_zero(B)),
    s => st2 => e => Empty.absurd(D.HR(ds, t, s, st2), e),
    +stA => qi => frame2.incy(f, ds, ks, img, regs, m, nx, fi, im, lim, inp, foc, F, xc, vf, yc, va, vb, kind, q, hv, fs, sp, ps, pg, st0, t, w, hexp, B, pend, zs, a, b, hub, hroom, hnd, hmc, et2, ew2, afs2, hl, h1, h2, h3, h8, eh, hok, stA, qi))


# The bounds of a round
# ---------------------

# three times
def A3(+y: Nat) -> Nat:
  Nat.add(y, Nat.add(y, y))

def a3.succ(+P: Nat) -> {A3(1n+P) == 3n+A3(P) : Nat}:
  +e4 = Equal.trans(Nat, Nat.add(P, Nat.add(P, 1n+P)), Nat.add(P, 1n+Nat.add(P, P)), 1n+A3(P),
    Equal.cong(Nat, Nat, z => Nat.add(P, z), Nat.add(P, 1n+P), 1n+Nat.add(P, P), N.add_succ_r(P, P)), N.add_succ_r(P, Nat.add(P, P)))
  +e6 = Equal.trans(Nat, Nat.add(P, 1n+Nat.add(P, 1n+P)), 1n+Nat.add(P, Nat.add(P, 1n+P)), 2n+A3(P),
    N.add_succ_r(P, Nat.add(P, 1n+P)), Equal.cong(Nat, Nat, z => 1n+z, Nat.add(P, Nat.add(P, 1n+P)), 1n+A3(P), e4))
  Equal.cong(Nat, Nat, z => 1n+z, Nat.add(P, 1n+Nat.add(P, 1n+P)), 2n+A3(P), e6)

def a3.split(+G: Nat, +X: Nat) -> {A3(Nat.add(G, X)) == Nat.add(A3(G), A3(X)) : Nat}:
  Equal.trans(Nat, A3(Nat.add(G, X)), Nat.add(Nat.add(G, X), Nat.add(Nat.add(G, G), Nat.add(X, X))), Nat.add(A3(G), A3(X)),
    Equal.cong(Nat, Nat, z => Nat.add(Nat.add(G, X), z), Nat.add(Nat.add(G, X), Nat.add(G, X)), Nat.add(Nat.add(G, G), Nat.add(X, X)),
      A.add4(G, X, G, X)),
    A.add4(G, X, Nat.add(G, G), Nat.add(X, X)))

# a frame pushed around a part of the focus costs less than the focus: 3 its
# nodes, and its frame at most 2 + 3 the other part's
def w.lt(+G: Nat, +X: Nat, +S: Nat, +W: Nat, +FR: Nat, hS: {S == 1n+Nat.add(G, X) : Nat}, hfr: N.Le(FR, 2n+A3(X))) ->
  N.Le(1n+Nat.add(A3(G), Nat.add(FR, W)), Nat.add(A3(S), W)):
  +AG = A3(G)
  +AX = A3(X)
  +Y = Nat.add(AX, W)
  +RHS = {2n+Nat.add(AG, Y) : Nat}
  +e = Equal.trans(Nat, Nat.add(AG, 2n+Y), 1n+Nat.add(AG, 1n+Y), RHS, N.add_succ_r(AG, 1n+Y),
    Equal.cong(Nat, Nat, z => 1n+z, Nat.add(AG, 1n+Y), 1n+Nat.add(AG, Y), N.add_succ_r(AG, Y)))
  +h = N.le_rw_r(Nat.add(AG, Nat.add(FR, W)), Nat.add(AG, 2n+Y), RHS, e,
    N.add_mono(AG, AG, Nat.add(FR, W), Nat.add(2n+AX, W), N.le_refl(AG), N.add_mono(FR, 2n+AX, W, W, hfr, N.le_refl(W))))
  %Equal.sym(Nat, S, 1n+Nat.add(G, X), hS) : N.Le(1n+Nat.add(AG, Nat.add(FR, W)), Nat.add(A3(_), W))
  %Equal.sym(Nat, A3(1n+Nat.add(G, X)), 3n+A3(Nat.add(G, X)), a3.succ(Nat.add(G, X))) : N.Le(1n+Nat.add(AG, Nat.add(FR, W)), Nat.add(_, W))
  %Equal.sym(Nat, A3(Nat.add(G, X)), Nat.add(AG, AX), a3.split(G, X)) : N.Le(1n+Nat.add(AG, Nat.add(FR, W)), 3n+Nat.add(_, W))
  %Equal.sym(Nat, Nat.add(Nat.add(AG, AX), W), Nat.add(AG, Y), add.assoc(AG, AX, W)) : N.Le(1n+Nat.add(AG, Nat.add(FR, W)), 3n+_)
  h

# Need's round bound from Acc's: 1 + the own cells, with the term's nodes
def need.arith(+S: Nat, +F: Nat, +R: Nat, +L: Nat, +T: Nat, +n: Nat, +X: Nat,
  h1: N.Le(n, Nat.add(S, Nat.add(Nat.add(F, 0n), Nat.add(R, Nat.add(L, 0n))))), h2: {T == Nat.add(F, Nat.add(R, L)) : Nat}, h3: N.Le(T, X)) ->
  N.Le(1n+n, Nat.add(S, Nat.add(16n, X))):
  +e1 = Equal.trans(Nat, Nat.add(S, Nat.add(Nat.add(F, 0n), Nat.add(R, Nat.add(L, 0n)))), Nat.add(S, Nat.add(F, Nat.add(R, Nat.add(L, 0n)))),
    Nat.add(S, Nat.add(F, Nat.add(R, L))),
    Equal.cong(Nat, Nat, z => Nat.add(S, Nat.add(z, Nat.add(R, Nat.add(L, 0n)))), Nat.add(F, 0n), F, N.add_zero(F)),
    Equal.cong(Nat, Nat, z => Nat.add(S, Nat.add(F, Nat.add(R, z))), Nat.add(L, 0n), L, N.add_zero(L)))
  +h1a = N.le_rw_r(n, Nat.add(S, Nat.add(Nat.add(F, 0n), Nat.add(R, Nat.add(L, 0n)))), Nat.add(S, Nat.add(F, Nat.add(R, L))), e1, h1)
  +h1b = N.le_rw_r(n, Nat.add(S, Nat.add(F, Nat.add(R, L))), Nat.add(S, T),
    Equal.cong(Nat, Nat, z => Nat.add(S, z), Nat.add(F, Nat.add(R, L)), T, Equal.sym(Nat, T, Nat.add(F, Nat.add(R, L)), h2)), h1a)
  N.le_trans(1n+n, Nat.add(S, 1n+T), Nat.add(S, Nat.add(16n, X)),
    N.le_rw_r(1n+n, 1n+Nat.add(S, T), Nat.add(S, 1n+T), Equal.sym(Nat, Nat.add(S, 1n+T), 1n+Nat.add(S, T), N.add_succ_r(S, T)), h1b),
    N.add_mono(S, S, 1n+T, Nat.add(16n, X), N.le_refl(S), N.le_trans(T, X, Nat.add(15n, X), h3, N.le_add_l(15n, X))))

# the term's nodes are within Need's twice the larger of the term and its step
def tx.le(+T: Nat, +SS: Nat, +DB: Nat) -> N.Le(T, Nat.add(Nat.mul(2n, Nat.max(T, SS)), Nat.mul(3n, DB))):
  +M = Nat.max(T, SS)
  N.le_trans(T, M, Nat.add(Nat.mul(2n, M), Nat.mul(3n, DB)), le.max(T, SS),
    N.le_trans(M, Nat.mul(2n, M), Nat.add(Nat.mul(2n, M), Nat.mul(3n, DB)), N.le_add_r(M, Nat.mul(1n, M)),
      N.le_add_r(Nat.mul(2n, M), Nat.mul(3n, DB))))

# with no pending cell, a new cell fits in Need: the own cells are at most
# the STATIC ones and the term's nodes (acc.count, plugs.size)
def need.of(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs0: List<&2, U32>, +m: Cr.Cir.Cells,
  +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +foc: U32, +F: Bk.Term, +sp: U32, +fs: List<&2, D.AF>,
  ps: List<&2, U32>, +zs: List<&2, D.Rt>, +t: Bk.Term, +et: {D.A.plugs(fs, F) == t : Bk.Term},
  hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, [D.Rt{foc, F}], Nil{}, sp, fs, ps, zs), e: {D.Pend.none(ps) == True{} : Bool}) ->
  N.Le(1n+Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), D.Need(ds, Cr.Cir.State{regs0, m, nx, fi, im, pg, lim, inp, Nil{}, 0}, t)):
  match ps:
    case Nil{}:
      +n = Nat.sub(U32.to_nat(nx), U32.to_nat(fi))
      +R = D.Rts.size(D.Fr.rts(fs, m, sp))
      +L = List.length(&2, U32, D.Fr.cells(fs, m, sp))
      +FF = Pg.Term.size(F)
      +T = Pg.Term.size(t)
      +h2 = Equal.trans(Nat, T, Pg.Term.size(D.A.plugs(fs, F)), Nat.add(FF, Nat.add(R, L)),
        Equal.cong(Bk.Term, Nat, u => Pg.Term.size(u), t, D.A.plugs(fs, F), Equal.sym(Bk.Term, D.A.plugs(fs, F), t, et)), A.plugs.size(fs, m, sp, F))
      need.arith(D.Stat(n, m, fi), FF, R, L, T, n, Nat.add(Nat.mul(2n, Nat.max(T, D.StepSize(ds, t))), Nat.mul(3n, D.Defs.big(ds))),
        A.acc.count(True{}, ds, ks, img, m, nx, fi, im, [D.Rt{foc, F}], Nil{}, sp, fs, zs, hac), h2, tx.le(T, D.StepSize(ds, t), D.Defs.big(ds)))
    case Con{p, r}:
      D.bool.ft(N.Le(1n+Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), D.Need(ds, Cr.Cir.State{regs0, m, nx, fi, im, pg, lim, inp, Nil{}, 0}, t)), e)

# 20 (nx + 1) bytes: within Budget, when a new cell fits in Need
def budget.of(+nx: U32, +fi: U32, +Nd: Nat, +T: Nat, +Y: Nat, hn: N.Le(1n+Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), Nd),
  hf: N.Le(U32.to_nat(fi), U32.to_nat(nx))) ->
  N.Le(Nat.mul(20n, Nat.add(U32.to_nat(nx), 1n)), Nat.max(Nat.add(Nat.mul(20n, Nat.add(U32.to_nat(fi), Nd)), T), Y)):
  +F = U32.to_nat(fi)
  +X = U32.to_nat(nx)
  +n = Nat.sub(X, F)
  +e1 = Equal.trans(Nat, Nat.add(n, 1n), 1n+Nat.add(n, 0n), 1n+n, N.add_succ_r(n, 0n), Equal.cong(Nat, Nat, z => 1n+z, Nat.add(n, 0n), n, N.add_zero(n)))
  +e2 = Equal.trans(Nat, Nat.add(F, 1n+n), Nat.add(F, Nat.add(n, 1n)), Nat.add(X, 1n),
    Equal.cong(Nat, Nat, z => Nat.add(F, z), 1n+n, Nat.add(n, 1n), Equal.sym(Nat, Nat.add(n, 1n), 1n+n, e1)),
    Equal.trans(Nat, Nat.add(F, Nat.add(n, 1n)), Nat.add(Nat.add(F, n), 1n), Nat.add(X, 1n),
      Equal.sym(Nat, Nat.add(Nat.add(F, n), 1n), Nat.add(F, Nat.add(n, 1n)), add.assoc(F, n, 1n)),
      Equal.cong(Nat, Nat, z => Nat.add(z, 1n), Nat.add(F, n), X, D.add.sub(F, X, hf))))
  +h1 = N.le_rw_l(Nat.add(F, 1n+n), Nat.add(X, 1n), Nat.add(F, Nd), e2, N.add_mono(F, F, 1n+n, Nd, N.le_refl(F), hn))
  N.le_trans(Nat.mul(20n, Nat.add(X, 1n)), Nat.add(Nat.mul(20n, Nat.add(F, Nd)), T), Nat.max(Nat.add(Nat.mul(20n, Nat.add(F, Nd)), T), Y),
    N.le_trans(Nat.mul(20n, Nat.add(X, 1n)), Nat.mul(20n, Nat.add(F, Nd)), Nat.add(Nat.mul(20n, Nat.add(F, Nd)), T),
      N.mul_mono_r(20n, Nat.add(X, 1n), Nat.add(F, Nd), h1), N.le_add_r(Nat.mul(20n, Nat.add(F, Nd)), T)),
    le.max(Nat.add(Nat.mul(20n, Nat.add(F, Nd)), T), Y))

# the heap's first cell is at most next
def heap.finx(-m: Cr.Cir.Cells, -nx: U32, -fi: U32, -im: U32, -rs: List<&2, U32>, -pend: U32, -ps: List<&2, U32>,
  h: D.Heap(m, nx, fi, im, rs, pend, ps)) -> {U32.is_le(fi, nx) == True{} : Bool}:
  match h:
    case Tuple{_, Tuple{_, Tuple{_, Tuple{_, Tuple{_, e}}}}}:
      e

# a pend list's first cell is not 0
def chain.ne(+m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +rs: List<&2, U32>, +pend: U32, +p: U32, +r: List<&2, U32>,
  h: D.Heap(m, nx, fi, im, rs, pend, Con{p, r})) -> {U32.is_eq(pend, 0) == False{} : Bool}:
  match h:
    case Tuple{Tuple{e, Tuple{n0, _}}, _}:
      %Equal.sym(U32, pend, p, e) : {U32.is_eq(_, 0) == False{} : Bool}
      n0

# the round's room for M.alloc: a new cell only with pend 0, when it fits
def room.of(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs0: List<&2, U32>, +m: Cr.Cir.Cells,
  +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +foc: U32, +F: Bk.Term, +sp: U32, +fs: List<&2, D.AF>,
  ps: List<&2, U32>, +pend: U32, +zs: List<&2, D.Rt>, +t: Bk.Term, +et: {D.A.plugs(fs, F) == t : Bk.Term},
  hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, [D.Rt{foc, F}], Nil{}, sp, fs, ps, zs), hp: D.Heap(m, nx, fi, im, [foc], pend, ps)) ->
  Or(N.Le(Nat.mul(20n, Nat.add(U32.to_nat(nx), 1n)), D.Budget(ds, Cr.Cir.State{regs0, m, nx, fi, im, pg, lim, inp, Nil{}, 0}, t)), {U32.is_eq(pend, 0) == False{} : Bool}):
  match ps:
    case Nil{}:
      Inl{budget.of(nx, fi, D.Need(ds, Cr.Cir.State{regs0, m, nx, fi, im, pg, lim, inp, Nil{}, 0}, t), Pg.Term.size(t), Nat.add(Nat.mul(20n, U32.to_nat(nx)), Pg.Term.size(t)),
        need.of(ds, ks, img, regs0, m, nx, fi, im, pg, lim, inp, foc, F, sp, fs, Nil{}, zs, t, et, hac, {==}), D.u.le(fi, nx, heap.finx(m, nx, fi, im, [foc], pend, Nil{}, hp)))}
    case Con{+p, +r}:
      Inr{chain.ne(m, nx, fi, im, [foc], pend, p, r, hp)}


# The push moves' focus: its parts
# --------------------------------
# the parts of the focus' cell, app
def app.x(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +foc: U32, +q: Bk.Quan, +g: Bk.Term, +x: Bk.Term,
  h: D.Is(ds, m, im, fi, nx, ks, img, foc, Bk.Term.App{q, g, x})) -> D.IsK(True{}, ds, m, im, fi, nx, ks, img, D.Fd(2n, m, foc), g):
  match h:
    case Tuple{_, Tuple{_, Tuple{Tuple{_, i}, _}}}:
      i

def app.y(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +foc: U32, +q: Bk.Quan, +g: Bk.Term, +x: Bk.Term,
  h: D.Is(ds, m, im, fi, nx, ks, img, foc, Bk.Term.App{q, g, x})) -> D.IsK(True{}, ds, m, im, fi, nx, ks, img, D.Fd(3n, m, foc), x):
  match h:
    case Tuple{_, Tuple{_, Tuple{_, Tuple{_, i}}}}:
      i

# the parts of the focus' cell are nodes of the focus' term, app
def app.n2(+m: Cr.Cir.Cells, +foc: U32, +q: Bk.Quan, +g: Bk.Term, +x: Bk.Term) ->
  {Bool.or(D.Fl(m, D.Fd(2n, m, foc), 1024), D.Nodes([D.Rt{foc, Bk.Term.App{q, g, x}}], m, D.Fd(2n, m, foc))) == True{} : Bool}:
  +c = D.Fd(2n, m, foc)
  D.or.r(D.Fl(m, c, 1024), D.Nodes([D.Rt{foc, Bk.Term.App{q, g, x}}], m, c),
    D.or.l(D.Node(Bk.Term.App{q, g, x}, m, foc, c), False{}, D.or.r(U32.is_eq(foc, c), Bool.or(D.Node(g, m, c, c), D.Node(x, m, D.Fd(3n, m, foc), c)),
      D.or.l(D.Node(g, m, c, c), D.Node(x, m, D.Fd(3n, m, foc), c), node.self(g, m, c)))))

def app.n3(+m: Cr.Cir.Cells, +foc: U32, +q: Bk.Quan, +g: Bk.Term, +x: Bk.Term) ->
  {Bool.or(D.Fl(m, D.Fd(3n, m, foc), 1024), D.Nodes([D.Rt{foc, Bk.Term.App{q, g, x}}], m, D.Fd(3n, m, foc))) == True{} : Bool}:
  +c = D.Fd(3n, m, foc)
  D.or.r(D.Fl(m, c, 1024), D.Nodes([D.Rt{foc, Bk.Term.App{q, g, x}}], m, c),
    D.or.l(D.Node(Bk.Term.App{q, g, x}, m, foc, c), False{}, D.or.r(U32.is_eq(foc, c), Bool.or(D.Node(g, m, D.Fd(2n, m, foc), c), D.Node(x, m, c, c)),
      D.or.r(D.Node(g, m, D.Fd(2n, m, foc), c), D.Node(x, m, c, c), node.self(x, m, c)))))

# the header of a frame of the focus' quantity, app
def app.eh(+k: U32, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +fi: U32, +im: U32, +lim: U32,
  +inp: List<&2, Word(8n)>, +foc: U32, +q: Bk.Quan, +g: Bk.Term, +x: Bk.Term, +regs2: List<&2, U32>, +m2: Cr.Cir.Cells, +nx2: U32, +pg2: U32,
  h8: {List.get(&2, U32, regs2, 8n) == Some{foc} : Maybe<&2, U32>}, hi: D.IsK(True{}, ds, m2, im, fi, nx2, ks, img, foc, Bk.Term.App{q, g, x})) ->
  {Cr.Cir.eval(Mc.M.header(k, Mc.M.q(Mc.M.g(Mc.R.c())), Mc.M.c(0)), Cr.Cir.State{regs2, m2, nx2, fi, im, pg2, lim, inp, Nil{}, 0}) ==
    Some{Hd(k, Mc.Img.quan(q))} : Maybe<&2, U32>}:
  match hi:
    case Tuple{Tuple{hc, _}, Tuple{hq, _}}:
      eh.q(k, regs2, m2, nx2, fi, im, pg2, lim, inp, foc, D.Fd(0n, m2, foc), q, h8, hc, {==}, hq)

# the parts of the focus' cell, let
def let.x(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +foc: U32, +q: Bk.Quan, +g: Bk.Term, +x: Bk.Term,
  h: D.Is(ds, m, im, fi, nx, ks, img, foc, Bk.Term.Let{q, g, x})) -> D.IsK(True{}, ds, m, im, fi, nx, ks, img, D.Fd(2n, m, foc), g):
  match h:
    case Tuple{_, Tuple{_, Tuple{Tuple{_, i}, _}}}:
      i

def let.y(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +foc: U32, +q: Bk.Quan, +g: Bk.Term, +x: Bk.Term,
  h: D.Is(ds, m, im, fi, nx, ks, img, foc, Bk.Term.Let{q, g, x})) -> D.IsK(True{}, ds, m, im, fi, nx, ks, img, D.Fd(3n, m, foc), x):
  match h:
    case Tuple{_, Tuple{_, Tuple{_, Tuple{_, i}}}}:
      i

# the parts of the focus' cell are nodes of the focus' term, let
def let.n2(+m: Cr.Cir.Cells, +foc: U32, +q: Bk.Quan, +g: Bk.Term, +x: Bk.Term) ->
  {Bool.or(D.Fl(m, D.Fd(2n, m, foc), 1024), D.Nodes([D.Rt{foc, Bk.Term.Let{q, g, x}}], m, D.Fd(2n, m, foc))) == True{} : Bool}:
  +c = D.Fd(2n, m, foc)
  D.or.r(D.Fl(m, c, 1024), D.Nodes([D.Rt{foc, Bk.Term.Let{q, g, x}}], m, c),
    D.or.l(D.Node(Bk.Term.Let{q, g, x}, m, foc, c), False{}, D.or.r(U32.is_eq(foc, c), Bool.or(D.Node(g, m, c, c), D.Node(x, m, D.Fd(3n, m, foc), c)),
      D.or.l(D.Node(g, m, c, c), D.Node(x, m, D.Fd(3n, m, foc), c), node.self(g, m, c)))))

def let.n3(+m: Cr.Cir.Cells, +foc: U32, +q: Bk.Quan, +g: Bk.Term, +x: Bk.Term) ->
  {Bool.or(D.Fl(m, D.Fd(3n, m, foc), 1024), D.Nodes([D.Rt{foc, Bk.Term.Let{q, g, x}}], m, D.Fd(3n, m, foc))) == True{} : Bool}:
  +c = D.Fd(3n, m, foc)
  D.or.r(D.Fl(m, c, 1024), D.Nodes([D.Rt{foc, Bk.Term.Let{q, g, x}}], m, c),
    D.or.l(D.Node(Bk.Term.Let{q, g, x}, m, foc, c), False{}, D.or.r(U32.is_eq(foc, c), Bool.or(D.Node(g, m, D.Fd(2n, m, foc), c), D.Node(x, m, c, c)),
      D.or.r(D.Node(g, m, D.Fd(2n, m, foc), c), D.Node(x, m, c, c), node.self(x, m, c)))))

# the header of a frame of the focus' quantity, let
def let.eh(+k: U32, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +fi: U32, +im: U32, +lim: U32,
  +inp: List<&2, Word(8n)>, +foc: U32, +q: Bk.Quan, +g: Bk.Term, +x: Bk.Term, +regs2: List<&2, U32>, +m2: Cr.Cir.Cells, +nx2: U32, +pg2: U32,
  h8: {List.get(&2, U32, regs2, 8n) == Some{foc} : Maybe<&2, U32>}, hi: D.IsK(True{}, ds, m2, im, fi, nx2, ks, img, foc, Bk.Term.Let{q, g, x})) ->
  {Cr.Cir.eval(Mc.M.header(k, Mc.M.q(Mc.M.g(Mc.R.c())), Mc.M.c(0)), Cr.Cir.State{regs2, m2, nx2, fi, im, pg2, lim, inp, Nil{}, 0}) ==
    Some{Hd(k, Mc.Img.quan(q))} : Maybe<&2, U32>}:
  match hi:
    case Tuple{Tuple{hc, _}, Tuple{hq, _}}:
      eh.q(k, regs2, m2, nx2, fi, im, pg2, lim, inp, foc, D.Fd(0n, m2, foc), q, h8, hc, {==}, hq)

# the parts of the focus' cell, tup
def tup.x(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +foc: U32, +q: Bk.Quan, +g: Bk.Term, +x: Bk.Term,
  h: D.Is(ds, m, im, fi, nx, ks, img, foc, Bk.Term.Tup{q, g, x})) -> D.IsK(True{}, ds, m, im, fi, nx, ks, img, D.Fd(2n, m, foc), g):
  match h:
    case Tuple{_, Tuple{_, Tuple{Tuple{_, i}, _}}}:
      i

def tup.y(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +foc: U32, +q: Bk.Quan, +g: Bk.Term, +x: Bk.Term,
  h: D.Is(ds, m, im, fi, nx, ks, img, foc, Bk.Term.Tup{q, g, x})) -> D.IsK(True{}, ds, m, im, fi, nx, ks, img, D.Fd(3n, m, foc), x):
  match h:
    case Tuple{_, Tuple{_, Tuple{_, Tuple{_, i}}}}:
      i

# the parts of the focus' cell are nodes of the focus' term, tup
def tup.n2(+m: Cr.Cir.Cells, +foc: U32, +q: Bk.Quan, +g: Bk.Term, +x: Bk.Term) ->
  {Bool.or(D.Fl(m, D.Fd(2n, m, foc), 1024), D.Nodes([D.Rt{foc, Bk.Term.Tup{q, g, x}}], m, D.Fd(2n, m, foc))) == True{} : Bool}:
  +c = D.Fd(2n, m, foc)
  D.or.r(D.Fl(m, c, 1024), D.Nodes([D.Rt{foc, Bk.Term.Tup{q, g, x}}], m, c),
    D.or.l(D.Node(Bk.Term.Tup{q, g, x}, m, foc, c), False{}, D.or.r(U32.is_eq(foc, c), Bool.or(D.Node(g, m, c, c), D.Node(x, m, D.Fd(3n, m, foc), c)),
      D.or.l(D.Node(g, m, c, c), D.Node(x, m, D.Fd(3n, m, foc), c), node.self(g, m, c)))))

def tup.n3(+m: Cr.Cir.Cells, +foc: U32, +q: Bk.Quan, +g: Bk.Term, +x: Bk.Term) ->
  {Bool.or(D.Fl(m, D.Fd(3n, m, foc), 1024), D.Nodes([D.Rt{foc, Bk.Term.Tup{q, g, x}}], m, D.Fd(3n, m, foc))) == True{} : Bool}:
  +c = D.Fd(3n, m, foc)
  D.or.r(D.Fl(m, c, 1024), D.Nodes([D.Rt{foc, Bk.Term.Tup{q, g, x}}], m, c),
    D.or.l(D.Node(Bk.Term.Tup{q, g, x}, m, foc, c), False{}, D.or.r(U32.is_eq(foc, c), Bool.or(D.Node(g, m, D.Fd(2n, m, foc), c), D.Node(x, m, c, c)),
      D.or.r(D.Node(g, m, D.Fd(2n, m, foc), c), D.Node(x, m, c, c), node.self(x, m, c)))))

# the header of a frame of the focus' quantity, tup
def tup.eh(+k: U32, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +fi: U32, +im: U32, +lim: U32,
  +inp: List<&2, Word(8n)>, +foc: U32, +q: Bk.Quan, +g: Bk.Term, +x: Bk.Term, +regs2: List<&2, U32>, +m2: Cr.Cir.Cells, +nx2: U32, +pg2: U32,
  h8: {List.get(&2, U32, regs2, 8n) == Some{foc} : Maybe<&2, U32>}, hi: D.IsK(True{}, ds, m2, im, fi, nx2, ks, img, foc, Bk.Term.Tup{q, g, x})) ->
  {Cr.Cir.eval(Mc.M.header(k, Mc.M.q(Mc.M.g(Mc.R.c())), Mc.M.c(0)), Cr.Cir.State{regs2, m2, nx2, fi, im, pg2, lim, inp, Nil{}, 0}) ==
    Some{Hd(k, Mc.Img.quan(q))} : Maybe<&2, U32>}:
  match hi:
    case Tuple{Tuple{hc, _}, Tuple{hq, _}}:
      eh.q(k, regs2, m2, nx2, fi, im, pg2, lim, inp, foc, D.Fd(0n, m2, foc), q, h8, hc, {==}, hq)

# the parts of the focus' cell, min
def min.x(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +foc: U32, +g: Bk.Term, +x: Bk.Term,
  h: D.Is(ds, m, im, fi, nx, ks, img, foc, Bk.Term.Min{g, x})) -> D.IsK(True{}, ds, m, im, fi, nx, ks, img, D.Fd(2n, m, foc), g):
  match h:
    case Tuple{_, Tuple{Tuple{_, i}, _}}:
      i

def min.y(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +foc: U32, +g: Bk.Term, +x: Bk.Term,
  h: D.Is(ds, m, im, fi, nx, ks, img, foc, Bk.Term.Min{g, x})) -> D.IsK(True{}, ds, m, im, fi, nx, ks, img, D.Fd(3n, m, foc), x):
  match h:
    case Tuple{_, Tuple{_, Tuple{_, i}}}:
      i

# the parts of the focus' cell are nodes of the focus' term, min
def min.n2(+m: Cr.Cir.Cells, +foc: U32, +g: Bk.Term, +x: Bk.Term) ->
  {Bool.or(D.Fl(m, D.Fd(2n, m, foc), 1024), D.Nodes([D.Rt{foc, Bk.Term.Min{g, x}}], m, D.Fd(2n, m, foc))) == True{} : Bool}:
  +c = D.Fd(2n, m, foc)
  D.or.r(D.Fl(m, c, 1024), D.Nodes([D.Rt{foc, Bk.Term.Min{g, x}}], m, c),
    D.or.l(D.Node(Bk.Term.Min{g, x}, m, foc, c), False{}, D.or.r(U32.is_eq(foc, c), Bool.or(D.Node(g, m, c, c), D.Node(x, m, D.Fd(3n, m, foc), c)),
      D.or.l(D.Node(g, m, c, c), D.Node(x, m, D.Fd(3n, m, foc), c), node.self(g, m, c)))))

def min.n3(+m: Cr.Cir.Cells, +foc: U32, +g: Bk.Term, +x: Bk.Term) ->
  {Bool.or(D.Fl(m, D.Fd(3n, m, foc), 1024), D.Nodes([D.Rt{foc, Bk.Term.Min{g, x}}], m, D.Fd(3n, m, foc))) == True{} : Bool}:
  +c = D.Fd(3n, m, foc)
  D.or.r(D.Fl(m, c, 1024), D.Nodes([D.Rt{foc, Bk.Term.Min{g, x}}], m, c),
    D.or.l(D.Node(Bk.Term.Min{g, x}, m, foc, c), False{}, D.or.r(U32.is_eq(foc, c), Bool.or(D.Node(g, m, D.Fd(2n, m, foc), c), D.Node(x, m, c, c)),
      D.or.r(D.Node(g, m, D.Fd(2n, m, foc), c), D.Node(x, m, c, c), node.self(x, m, c)))))

# a node's tag and cell
def nd.tag(-ds: List<&2, Bk.Def>, -im: U32, -fi: U32, -nx: U32, -c: U32, -x: Cr.Cir.Cell, -t: Bk.Term, -tag: U32,
  nd: D.Nd(ds, im, fi, nx, c, x, t, tag)) -> {D.TgW(Cr.Cir.Cell.get(0n, x)) == tag : U32}:
  match nd:
    case Tuple{_, Tuple{_, Tuple{e, _}}}:
      e

def nd.cell(-ds: List<&2, Bk.Def>, +im: U32, +fi: U32, +nx: U32, +c: U32, -x: Cr.Cir.Cell, -t: Bk.Term, -tag: U32,
  nd: D.Nd(ds, im, fi, nx, c, x, t, tag)) -> {Cr.Cir.is_cell(c, im, fi, nx) == True{} : Bool}:
  match nd:
    case Tuple{e, _}:
      e


# M.ev.let and M.ev.tup's test of the quantity
def q.nz(q: Bk.Quan, h: {El.Quan.live(q) == True{} : Bool}) -> {U32.is_zero(Wa.Wasm.op(Wa.Wasm.Op.ne{}, Mc.Img.quan(q), 0)) == False{} : Bool}:
  match q:
    case Bk.Quan.Q0{}:
      D.bool.ft({U32.is_zero(Wa.Wasm.op(Wa.Wasm.Op.ne{}, 0, 0)) == False{} : Bool}, h)
    case Bk.Quan.Q1{}:
      {==}
    case Bk.Quan.Q2{}:
      {==}

def q.z(q: Bk.Quan, h: {El.Quan.live(q) == False{} : Bool}) -> {U32.is_zero(Wa.Wasm.op(Wa.Wasm.Op.ne{}, Mc.Img.quan(q), 0)) == True{} : Bool}:
  match q:
    case Bk.Quan.Q0{}:
      {==}
    case Bk.Quan.Q1{}:
      Empty.absurd({U32.is_zero(Wa.Wasm.op(Wa.Wasm.Op.ne{}, 1, 0)) == True{} : Bool}, N.true_ne_false(h))
    case Bk.Quan.Q2{}:
      Empty.absurd({U32.is_zero(Wa.Wasm.op(Wa.Wasm.Op.ne{}, 2, 0)) == True{} : Bool}, N.true_ne_false(h))

# the quantity of the focus' cell, Let and Tup
def let.qs(-ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -m: Cr.Cir.Cells, -nx: U32, -fi: U32, -im: U32,
  -foc: U32, -q: Bk.Quan, -g: Bk.Term, -x: Bk.Term, h: D.Is(ds, m, im, fi, nx, ks, img, foc, Bk.Term.Let{q, g, x})) ->
  D.Qs(Cr.Cir.Cells.get(m, foc), q):
  match h:
    case Tuple{_, Tuple{e, _}}:
      e

def tup.qs(-ds: List<&2, Bk.Def>, -ks: List<&2, List<&2, Word(8n)>>, -img: List<&2, Bk.Term>, -m: Cr.Cir.Cells, -nx: U32, -fi: U32, -im: U32,
  -foc: U32, -q: Bk.Quan, -g: Bk.Term, -x: Bk.Term, h: D.Is(ds, m, im, fi, nx, ks, img, foc, Bk.Term.Tup{q, g, x})) ->
  D.Qs(Cr.Cir.Cells.get(m, foc), q):
  match h:
    case Tuple{_, Tuple{e, _}}:
      e

# mv.ev.app: M.ev's tests reach the frame's push
def app.disp(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32, +r4: U32, +r5: U32, +r6: U32, +r7: U32, +r8: U32, +r9: U32, +r10: U32, +r11: U32, +r12: U32, +r13: U32, +r14: U32, +r15: U32, +r16: U32, +r17: U32, +r18: U32, +r19: U32, +r20: U32, +r21: U32, +r22: U32, +r23: U32, +r24: U32, +r25: U32, +r26: U32, +r27: U32, +r28: U32, +r29: U32, +r30: U32, +r31: U32, +r32: U32, +r33: U32, +r34: U32, +r35: U32, +r36: U32, +r37: U32, +r38: U32, +r39: U32, +r40: U32, +r41: U32, +r42: U32, +r43: U32, +r44: U32, +r45: U32, +r46: U32, +r47: U32, +r48: U32, +r49: U32, +r50: U32, +r51: U32, +r52: U32, +r53: U32, +r54: U32, +r55: U32, +r56: U32, +r57: U32, +r58: U32, +r59: U32, +r60: U32, +r61: U32, +r62: U32,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +q: Bk.Quan, +g: Bk.Term, +x: Bk.Term,
  +nd: D.Nd(ds, im, fi, nx, foc, Cr.Cir.Cells.get(m, foc), Bk.Term.App{q, g, x}, D.A.tag(Bk.Term.App{q, g, x})), +tb: D.Tbl(m, im, fi, nx),
  +hv: {D.Fl(m, foc, 256) == False{} : Bool}) ->
  {Cr.Cir.exec(f, D.B.body(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)) == Cr.Cir.exec(f, Mc.M.ev.app(), K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)) : Cr.Cir.Out}:
  +F = {Bk.Term.App{q, g, x} : Bk.Term}
  Equal.trans(Cr.Cir.Out, Cr.Cir.exec(f, D.B.body(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)), Cr.Cir.exec(f, K.B.else(), K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)), Cr.Cir.exec(f, Mc.M.ev.app(), K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)),
    ev.pre.E(f, ds, ks, img, foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp, F, nd, tb, hv, {==}),
    br.app(f, K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp), D.Fd(0n, m, foc), nd.tag(ds, im, fi, nx, foc, Cr.Cir.Cells.get(m, foc), F, D.A.tag(F), nd), {==}))

def nw.app() -> {NW(Mc.M.ev.app()) == True{} : Bool}:
  {==}

# mv.ev.app's frame costs less than the focus
def app.w(+q: Bk.Quan, +g: Bk.Term, +x: Bk.Term, +fs: List<&2, D.AF>, +w: Nat, ew: {D.A.w(False{}, Bk.Term.App{q, g, x}, fs) == w : Nat}) ->
  N.Le(1n+D.A.w(False{}, g, Con{D.AF{D.FK.arg{}, q, False{}, x, x}, fs}), w):
  match q:
    case Bk.Quan.Q0{}:
      %ew : N.Le(1n+D.A.w(False{}, g, Con{D.AF{D.FK.arg{}, Bk.Quan.Q0{}, False{}, x, x}, fs}), _)
      w.lt(Pg.Term.size(g), Pg.Term.size(x), Pg.Term.size(Bk.Term.App{Bk.Quan.Q0{}, g, x}), D.A.w.frames(fs), 1n, {==}, Unit{})
    case Bk.Quan.Q1{}:
      %ew : N.Le(1n+D.A.w(False{}, g, Con{D.AF{D.FK.arg{}, Bk.Quan.Q1{}, False{}, x, x}, fs}), _)
      w.lt(Pg.Term.size(g), Pg.Term.size(x), Pg.Term.size(Bk.Term.App{Bk.Quan.Q1{}, g, x}), D.A.w.frames(fs), 2n+A3(Pg.Term.size(x)), {==}, N.le_refl(2n+A3(Pg.Term.size(x))))
    case Bk.Quan.Q2{}:
      %ew : N.Le(1n+D.A.w(False{}, g, Con{D.AF{D.FK.arg{}, Bk.Quan.Q2{}, False{}, x, x}, fs}), _)
      w.lt(Pg.Term.size(g), Pg.Term.size(x), Pg.Term.size(Bk.Term.App{Bk.Quan.Q2{}, g, x}), D.A.w.frames(fs), 2n+A3(Pg.Term.size(x)), {==}, N.le_refl(2n+A3(Pg.Term.size(x))))

# mv.ev.app: the frame pushed, an admin move
def app.mv(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32, +r4: U32, +r5: U32, +r6: U32, +r7: U32, +r8: U32, +r9: U32, +r10: U32, +r11: U32, +r12: U32, +r13: U32, +r14: U32, +r15: U32, +r16: U32, +r17: U32, +r18: U32, +r19: U32, +r20: U32, +r21: U32, +r22: U32, +r23: U32, +r24: U32, +r25: U32, +r26: U32, +r27: U32, +r28: U32, +r29: U32, +r30: U32, +r31: U32, +r32: U32, +r33: U32, +r34: U32, +r35: U32, +r36: U32, +r37: U32, +r38: U32, +r39: U32, +r40: U32, +r41: U32, +r42: U32, +r43: U32, +r44: U32, +r45: U32, +r46: U32, +r47: U32, +r48: U32, +r49: U32, +r50: U32, +r51: U32, +r52: U32, +r53: U32, +r54: U32, +r55: U32, +r56: U32, +r57: U32, +r58: U32, +r59: U32, +r60: U32, +r61: U32, +r62: U32,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat, +fs: List<&2, D.AF>,
  +ps: List<&2, U32>, +q: Bk.Quan, +g: Bk.Term, +x: Bk.Term, +et: {D.A.plugs(fs, Bk.Term.App{q, g, x}) == t : Bk.Term}, +ew: {D.A.w(False{}, Bk.Term.App{q, g, x}, fs) == w : Nat}, +afs: D.AFs.ok(ds, fs),
  +isf: D.Is(ds, m, im, fi, nx, ks, img, foc, Bk.Term.App{q, g, x}), +frs: D.Frs(ds, m, im, fi, nx, ks, img, ps, sp, fs),
  +hp: D.Heap(m, nx, fi, im, [foc], pend, ps), +io: D.ImgOK(ds, ks, img, m, im, fi, nx), +zs: List<&2, D.Rt>,
  +hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, [D.Rt{foc, Bk.Term.App{q, g, x}}], Nil{}, sp, fs, ps, zs), +hv: {D.Fl(m, foc, 256) == False{} : Bool}) ->
  D.PostB(False{}, Cr.Cir.exec(f, D.B.body(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)), s => K.MV.next(ds, ks, img, D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), t, w, s), s => st2 => D.HR(ds, t, s, st2), D.Budget(ds, D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp))):
  +F = {Bk.Term.App{q, g, x} : Bk.Term}
  +nd = D.is.nd(ds, m, im, fi, nx, ks, img, foc, F, isf)
  +tb = K.img.tbl(ds, ks, img, m, im, fi, nx, io)
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, D.B.body(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)), Cr.Cir.exec(f, Mc.M.ev.app(), K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)),
    app.disp(f, ds, ks, img, foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp, q, g, x, nd, tb, hv)) :
    D.PostB(False{}, _, s => K.MV.next(ds, ks, img, D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), t, w, s), s => st2 => D.HR(ds, t, s, st2), D.Budget(ds, D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)))
  frame2.mv(f, ds, ks, img, D.St.regs(K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)), m, nx, fi, im, lim, inp, foc, F, D.Fd(2n, m, foc), g, D.Fd(3n, m, foc), x, x, D.FK.arg{}, q, Hd(32, Mc.Img.quan(q)), fs, sp, ps,
    pg, D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), t, w, Mc.M.header(Mc.K.app_arg(), Mc.M.q(Mc.M.g(Mc.R.c())), Mc.M.c(0)), D.Budget(ds, D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), t), pend, zs, 2n, 3n, {==},
    room.of(ds, ks, img, D.RG(foc, 0, sp, pend, D.R59.list(D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62})), m, nx, fi, im, pg, lim, inp, foc, F, sp, fs, ps, pend, zs, t, et, hac, hp),
    e => need.of(ds, ks, img, D.RG(foc, 0, sp, pend, D.R59.list(D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62})), m, nx, fi, im, pg, lim, inp, foc, F, sp, fs, ps, zs, t, et, hac, e), {==}, et,
    app.w(q, g, x, fs, w, ew), ({==}, afs), {==}, {==}, {==}, {==}, {==},
    regs2 => m2 => nx2 => pg2 => h8 => hi => app.eh(32, ds, ks, img, fi, im, lim, inp, foc, q, g, x, regs2, m2, nx2, pg2, h8, hi),
    hd.ok(D.FK.arg{}, q), {==}, {==}, nd.cell(ds, im, fi, nx, foc, Cr.Cir.Cells.get(m, foc), F, D.A.tag(F), nd),
    ((isf, Unit{}), ((app.x(ds, ks, img, m, nx, fi, im, foc, q, g, x, isf), (app.y(ds, ks, img, m, nx, fi, im, foc, q, g, x, isf), Unit{})), ((app.n2(m, foc, q, g, x), (app.n3(m, foc, q, g, x), Unit{})), (frs, (hp, io))))), hac)

# mv.ev.let: M.ev's tests reach the frame's push
def let.disp(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32, +r4: U32, +r5: U32, +r6: U32, +r7: U32, +r8: U32, +r9: U32, +r10: U32, +r11: U32, +r12: U32, +r13: U32, +r14: U32, +r15: U32, +r16: U32, +r17: U32, +r18: U32, +r19: U32, +r20: U32, +r21: U32, +r22: U32, +r23: U32, +r24: U32, +r25: U32, +r26: U32, +r27: U32, +r28: U32, +r29: U32, +r30: U32, +r31: U32, +r32: U32, +r33: U32, +r34: U32, +r35: U32, +r36: U32, +r37: U32, +r38: U32, +r39: U32, +r40: U32, +r41: U32, +r42: U32, +r43: U32, +r44: U32, +r45: U32, +r46: U32, +r47: U32, +r48: U32, +r49: U32, +r50: U32, +r51: U32, +r52: U32, +r53: U32, +r54: U32, +r55: U32, +r56: U32, +r57: U32, +r58: U32, +r59: U32, +r60: U32, +r61: U32, +r62: U32,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +q: Bk.Quan, +g: Bk.Term, +x: Bk.Term,
  +nd: D.Nd(ds, im, fi, nx, foc, Cr.Cir.Cells.get(m, foc), Bk.Term.Let{q, g, x}, D.A.tag(Bk.Term.Let{q, g, x})), +tb: D.Tbl(m, im, fi, nx),
  +hv: {D.Fl(m, foc, 256) == False{} : Bool}, +hq: {El.Quan.live(q) == True{} : Bool}, +hqs: D.Qs(Cr.Cir.Cells.get(m, foc), q)) ->
  {Cr.Cir.exec(f, D.B.body(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)) == Cr.Cir.exec(f, K.stmt.then(Mc.M.ev.let()), K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)) : Cr.Cir.Out}:
  +F = {Bk.Term.Let{q, g, x} : Bk.Term}
  +st2 = {K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp) : Cr.Cir.State}
  +f1 = D.Fd(0n, m, foc)
  +QV = Wa.Wasm.op(Wa.Wasm.Op.and{}, Wa.Wasm.op(Wa.Wasm.Op.shr_u{}, f1, 6), 3)
  +ef = X.ev.fld(0n, Mc.M.g(8n), st2, foc, {==}, nd.cell(ds, im, fi, nx, foc, Cr.Cir.Cells.get(m, foc), F, D.A.tag(F), nd))
  +esh = X.ev.op(Wa.Wasm.Op.shr_u{}, Mc.M.f(0n, Mc.M.g(8n)), Mc.M.c(6), st2, f1, 6, ef, {==})
  +eand = X.ev.op(Wa.Wasm.Op.and{}, Mc.M.shr(Mc.M.f(0n, Mc.M.g(8n)), Mc.M.c(6)), Mc.M.c(3), st2, Wa.Wasm.op(Wa.Wasm.Op.shr_u{}, f1, 6), 3, esh, {==})
  +ene = X.ev.op(Wa.Wasm.Op.ne{}, Mc.M.q(Mc.M.g(8n)), Mc.M.c(0), st2, QV, 0, eand, {==})
  Equal.trans(Cr.Cir.Out, Cr.Cir.exec(f, D.B.body(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)), Cr.Cir.exec(f, Mc.M.ev.let(), K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)), Cr.Cir.exec(f, K.stmt.then(Mc.M.ev.let()), K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)),
    Equal.trans(Cr.Cir.Out, Cr.Cir.exec(f, D.B.body(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)), Cr.Cir.exec(f, K.B.else(), K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)), Cr.Cir.exec(f, Mc.M.ev.let(), K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)),
    ev.pre.E(f, ds, ks, img, foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp, F, nd, tb, hv, {==}),
    br.let(f, K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp), D.Fd(0n, m, foc), nd.tag(ds, im, fi, nx, foc, Cr.Cir.Cells.get(m, foc), F, D.A.tag(F), nd), {==})),
    D.eq.if.t(f, K.stmt.cond(Mc.M.ev.let()), K.stmt.then(Mc.M.ev.let()), K.stmt.else(Mc.M.ev.let()), K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp), Wa.Wasm.op(Wa.Wasm.Op.ne{}, QV, 0), ene,
      (%Equal.sym(U32, D.QnW(D.Fd(0n, m, foc)), Mc.Img.quan(q), hqs) : {U32.is_zero(Wa.Wasm.op(Wa.Wasm.Op.ne{}, _, 0)) == False{} : Bool}; q.nz(q, hq))))

def nw.let() -> {NW(K.stmt.then(Mc.M.ev.let())) == True{} : Bool}:
  {==}

# mv.ev.let's frame costs less than the focus
def let.w(+q: Bk.Quan, +g: Bk.Term, +x: Bk.Term, +fs: List<&2, D.AF>, +w: Nat, ew: {D.A.w(False{}, Bk.Term.Let{q, g, x}, fs) == w : Nat}) ->
  N.Le(1n+D.A.w(False{}, g, Con{D.AF{D.FK.let{}, q, False{}, x, x}, fs}), w):
  %ew : N.Le(1n+D.A.w(False{}, g, Con{D.AF{D.FK.let{}, q, False{}, x, x}, fs}), _)
  w.lt(Pg.Term.size(g), Pg.Term.size(x), Pg.Term.size(Bk.Term.Let{q, g, x}), D.A.w.frames(fs), 0n, {==}, N.le_zero(2n+A3(Pg.Term.size(x))))

# mv.ev.let: the frame pushed, an admin move
def let.mv(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32, +r4: U32, +r5: U32, +r6: U32, +r7: U32, +r8: U32, +r9: U32, +r10: U32, +r11: U32, +r12: U32, +r13: U32, +r14: U32, +r15: U32, +r16: U32, +r17: U32, +r18: U32, +r19: U32, +r20: U32, +r21: U32, +r22: U32, +r23: U32, +r24: U32, +r25: U32, +r26: U32, +r27: U32, +r28: U32, +r29: U32, +r30: U32, +r31: U32, +r32: U32, +r33: U32, +r34: U32, +r35: U32, +r36: U32, +r37: U32, +r38: U32, +r39: U32, +r40: U32, +r41: U32, +r42: U32, +r43: U32, +r44: U32, +r45: U32, +r46: U32, +r47: U32, +r48: U32, +r49: U32, +r50: U32, +r51: U32, +r52: U32, +r53: U32, +r54: U32, +r55: U32, +r56: U32, +r57: U32, +r58: U32, +r59: U32, +r60: U32, +r61: U32, +r62: U32,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat, +fs: List<&2, D.AF>,
  +ps: List<&2, U32>, +q: Bk.Quan, +g: Bk.Term, +x: Bk.Term, +et: {D.A.plugs(fs, Bk.Term.Let{q, g, x}) == t : Bk.Term}, +ew: {D.A.w(False{}, Bk.Term.Let{q, g, x}, fs) == w : Nat}, +afs: D.AFs.ok(ds, fs),
  +isf: D.Is(ds, m, im, fi, nx, ks, img, foc, Bk.Term.Let{q, g, x}), +frs: D.Frs(ds, m, im, fi, nx, ks, img, ps, sp, fs),
  +hp: D.Heap(m, nx, fi, im, [foc], pend, ps), +io: D.ImgOK(ds, ks, img, m, im, fi, nx), +zs: List<&2, D.Rt>,
  +hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, [D.Rt{foc, Bk.Term.Let{q, g, x}}], Nil{}, sp, fs, ps, zs), +hv: {D.Fl(m, foc, 256) == False{} : Bool}, +hq: {El.Quan.live(q) == True{} : Bool}) ->
  D.PostB(False{}, Cr.Cir.exec(f, D.B.body(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)), s => K.MV.next(ds, ks, img, D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), t, w, s), s => st2 => D.HR(ds, t, s, st2), D.Budget(ds, D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp))):
  +F = {Bk.Term.Let{q, g, x} : Bk.Term}
  +nd = D.is.nd(ds, m, im, fi, nx, ks, img, foc, F, isf)
  +tb = K.img.tbl(ds, ks, img, m, im, fi, nx, io)
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, D.B.body(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)), Cr.Cir.exec(f, K.stmt.then(Mc.M.ev.let()), K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)),
    let.disp(f, ds, ks, img, foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp, q, g, x, nd, tb, hv, hq, let.qs(ds, ks, img, m, nx, fi, im, foc, q, g, x, isf))) :
    D.PostB(False{}, _, s => K.MV.next(ds, ks, img, D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), t, w, s), s => st2 => D.HR(ds, t, s, st2), D.Budget(ds, D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)))
  frame2.mv(f, ds, ks, img, D.St.regs(K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)), m, nx, fi, im, lim, inp, foc, F, D.Fd(2n, m, foc), g, D.Fd(3n, m, foc), x, x, D.FK.let{}, q, Hd(35, Mc.Img.quan(q)), fs, sp, ps,
    pg, D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), t, w, Mc.M.header(Mc.K.let_in(), Mc.M.q(Mc.M.g(Mc.R.c())), Mc.M.c(0)), D.Budget(ds, D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), t), pend, zs, 2n, 3n, {==},
    room.of(ds, ks, img, D.RG(foc, 0, sp, pend, D.R59.list(D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62})), m, nx, fi, im, pg, lim, inp, foc, F, sp, fs, ps, pend, zs, t, et, hac, hp),
    e => need.of(ds, ks, img, D.RG(foc, 0, sp, pend, D.R59.list(D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62})), m, nx, fi, im, pg, lim, inp, foc, F, sp, fs, ps, zs, t, et, hac, e), {==}, et,
    let.w(q, g, x, fs, w, ew), (hq, afs), {==}, {==}, {==}, {==}, {==},
    regs2 => m2 => nx2 => pg2 => h8 => hi => let.eh(35, ds, ks, img, fi, im, lim, inp, foc, q, g, x, regs2, m2, nx2, pg2, h8, hi),
    hd.ok(D.FK.let{}, q), {==}, {==}, nd.cell(ds, im, fi, nx, foc, Cr.Cir.Cells.get(m, foc), F, D.A.tag(F), nd),
    ((isf, Unit{}), ((let.x(ds, ks, img, m, nx, fi, im, foc, q, g, x, isf), (let.y(ds, ks, img, m, nx, fi, im, foc, q, g, x, isf), Unit{})), ((let.n2(m, foc, q, g, x), (let.n3(m, foc, q, g, x), Unit{})), (frs, (hp, io))))), hac)

# mv.ev.tup: M.ev's tests reach the frame's push
def tup.disp(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32, +r4: U32, +r5: U32, +r6: U32, +r7: U32, +r8: U32, +r9: U32, +r10: U32, +r11: U32, +r12: U32, +r13: U32, +r14: U32, +r15: U32, +r16: U32, +r17: U32, +r18: U32, +r19: U32, +r20: U32, +r21: U32, +r22: U32, +r23: U32, +r24: U32, +r25: U32, +r26: U32, +r27: U32, +r28: U32, +r29: U32, +r30: U32, +r31: U32, +r32: U32, +r33: U32, +r34: U32, +r35: U32, +r36: U32, +r37: U32, +r38: U32, +r39: U32, +r40: U32, +r41: U32, +r42: U32, +r43: U32, +r44: U32, +r45: U32, +r46: U32, +r47: U32, +r48: U32, +r49: U32, +r50: U32, +r51: U32, +r52: U32, +r53: U32, +r54: U32, +r55: U32, +r56: U32, +r57: U32, +r58: U32, +r59: U32, +r60: U32, +r61: U32, +r62: U32,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +q: Bk.Quan, +g: Bk.Term, +x: Bk.Term,
  +nd: D.Nd(ds, im, fi, nx, foc, Cr.Cir.Cells.get(m, foc), Bk.Term.Tup{q, g, x}, D.A.tag(Bk.Term.Tup{q, g, x})), +tb: D.Tbl(m, im, fi, nx),
  +hv: {D.Fl(m, foc, 256) == False{} : Bool}, +hq: {El.Quan.live(q) == True{} : Bool}, +hqs: D.Qs(Cr.Cir.Cells.get(m, foc), q)) ->
  {Cr.Cir.exec(f, D.B.body(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)) == Cr.Cir.exec(f, K.stmt.then(Mc.M.ev.tup()), K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)) : Cr.Cir.Out}:
  +F = {Bk.Term.Tup{q, g, x} : Bk.Term}
  +st2 = {K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp) : Cr.Cir.State}
  +f1 = D.Fd(0n, m, foc)
  +QV = Wa.Wasm.op(Wa.Wasm.Op.and{}, Wa.Wasm.op(Wa.Wasm.Op.shr_u{}, f1, 6), 3)
  +ef = X.ev.fld(0n, Mc.M.g(8n), st2, foc, {==}, nd.cell(ds, im, fi, nx, foc, Cr.Cir.Cells.get(m, foc), F, D.A.tag(F), nd))
  +esh = X.ev.op(Wa.Wasm.Op.shr_u{}, Mc.M.f(0n, Mc.M.g(8n)), Mc.M.c(6), st2, f1, 6, ef, {==})
  +eand = X.ev.op(Wa.Wasm.Op.and{}, Mc.M.shr(Mc.M.f(0n, Mc.M.g(8n)), Mc.M.c(6)), Mc.M.c(3), st2, Wa.Wasm.op(Wa.Wasm.Op.shr_u{}, f1, 6), 3, esh, {==})
  +ene = X.ev.op(Wa.Wasm.Op.ne{}, Mc.M.q(Mc.M.g(8n)), Mc.M.c(0), st2, QV, 0, eand, {==})
  Equal.trans(Cr.Cir.Out, Cr.Cir.exec(f, D.B.body(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)), Cr.Cir.exec(f, Mc.M.ev.tup(), K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)), Cr.Cir.exec(f, K.stmt.then(Mc.M.ev.tup()), K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)),
    Equal.trans(Cr.Cir.Out, Cr.Cir.exec(f, D.B.body(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)), Cr.Cir.exec(f, K.B.else(), K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)), Cr.Cir.exec(f, Mc.M.ev.tup(), K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)),
    ev.pre.E(f, ds, ks, img, foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp, F, nd, tb, hv, {==}),
    br.tup(f, K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp), D.Fd(0n, m, foc), nd.tag(ds, im, fi, nx, foc, Cr.Cir.Cells.get(m, foc), F, D.A.tag(F), nd), {==})),
    D.eq.if.t(f, K.stmt.cond(Mc.M.ev.tup()), K.stmt.then(Mc.M.ev.tup()), K.stmt.else(Mc.M.ev.tup()), K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp), Wa.Wasm.op(Wa.Wasm.Op.ne{}, QV, 0), ene,
      (%Equal.sym(U32, D.QnW(D.Fd(0n, m, foc)), Mc.Img.quan(q), hqs) : {U32.is_zero(Wa.Wasm.op(Wa.Wasm.Op.ne{}, _, 0)) == False{} : Bool}; q.nz(q, hq))))

def nw.tup() -> {NW(K.stmt.then(Mc.M.ev.tup())) == True{} : Bool}:
  {==}

# mv.ev.tup's frame costs less than the focus
def tup.w(+q: Bk.Quan, +g: Bk.Term, +x: Bk.Term, +fs: List<&2, D.AF>, +w: Nat, ew: {D.A.w(False{}, Bk.Term.Tup{q, g, x}, fs) == w : Nat}) ->
  N.Le(1n+D.A.w(False{}, g, Con{D.AF{D.FK.tupb{}, q, False{}, x, x}, fs}), w):
  %ew : N.Le(1n+D.A.w(False{}, g, Con{D.AF{D.FK.tupb{}, q, False{}, x, x}, fs}), _)
  w.lt(Pg.Term.size(g), Pg.Term.size(x), Pg.Term.size(Bk.Term.Tup{q, g, x}), D.A.w.frames(fs), 2n+A3(Pg.Term.size(x)), {==}, N.le_refl(2n+A3(Pg.Term.size(x))))

# mv.ev.tup: the frame pushed, an admin move
def tup.mv(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32, +r4: U32, +r5: U32, +r6: U32, +r7: U32, +r8: U32, +r9: U32, +r10: U32, +r11: U32, +r12: U32, +r13: U32, +r14: U32, +r15: U32, +r16: U32, +r17: U32, +r18: U32, +r19: U32, +r20: U32, +r21: U32, +r22: U32, +r23: U32, +r24: U32, +r25: U32, +r26: U32, +r27: U32, +r28: U32, +r29: U32, +r30: U32, +r31: U32, +r32: U32, +r33: U32, +r34: U32, +r35: U32, +r36: U32, +r37: U32, +r38: U32, +r39: U32, +r40: U32, +r41: U32, +r42: U32, +r43: U32, +r44: U32, +r45: U32, +r46: U32, +r47: U32, +r48: U32, +r49: U32, +r50: U32, +r51: U32, +r52: U32, +r53: U32, +r54: U32, +r55: U32, +r56: U32, +r57: U32, +r58: U32, +r59: U32, +r60: U32, +r61: U32, +r62: U32,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat, +fs: List<&2, D.AF>,
  +ps: List<&2, U32>, +q: Bk.Quan, +g: Bk.Term, +x: Bk.Term, +et: {D.A.plugs(fs, Bk.Term.Tup{q, g, x}) == t : Bk.Term}, +ew: {D.A.w(False{}, Bk.Term.Tup{q, g, x}, fs) == w : Nat}, +afs: D.AFs.ok(ds, fs),
  +isf: D.Is(ds, m, im, fi, nx, ks, img, foc, Bk.Term.Tup{q, g, x}), +frs: D.Frs(ds, m, im, fi, nx, ks, img, ps, sp, fs),
  +hp: D.Heap(m, nx, fi, im, [foc], pend, ps), +io: D.ImgOK(ds, ks, img, m, im, fi, nx), +zs: List<&2, D.Rt>,
  +hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, [D.Rt{foc, Bk.Term.Tup{q, g, x}}], Nil{}, sp, fs, ps, zs), +hv: {D.Fl(m, foc, 256) == False{} : Bool}, +hq: {El.Quan.live(q) == True{} : Bool}) ->
  D.PostB(False{}, Cr.Cir.exec(f, D.B.body(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)), s => K.MV.next(ds, ks, img, D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), t, w, s), s => st2 => D.HR(ds, t, s, st2), D.Budget(ds, D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp))):
  +F = {Bk.Term.Tup{q, g, x} : Bk.Term}
  +nd = D.is.nd(ds, m, im, fi, nx, ks, img, foc, F, isf)
  +tb = K.img.tbl(ds, ks, img, m, im, fi, nx, io)
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, D.B.body(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)), Cr.Cir.exec(f, K.stmt.then(Mc.M.ev.tup()), K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)),
    tup.disp(f, ds, ks, img, foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp, q, g, x, nd, tb, hv, hq, tup.qs(ds, ks, img, m, nx, fi, im, foc, q, g, x, isf))) :
    D.PostB(False{}, _, s => K.MV.next(ds, ks, img, D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), t, w, s), s => st2 => D.HR(ds, t, s, st2), D.Budget(ds, D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)))
  frame2.mv(f, ds, ks, img, D.St.regs(K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)), m, nx, fi, im, lim, inp, foc, F, D.Fd(2n, m, foc), g, D.Fd(3n, m, foc), x, x, D.FK.tupb{}, q, Hd(36, Mc.Img.quan(q)), fs, sp, ps,
    pg, D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), t, w, Mc.M.header(Mc.K.tup_b(), Mc.M.q(Mc.M.g(Mc.R.c())), Mc.M.c(0)), D.Budget(ds, D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), t), pend, zs, 2n, 3n, {==},
    room.of(ds, ks, img, D.RG(foc, 0, sp, pend, D.R59.list(D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62})), m, nx, fi, im, pg, lim, inp, foc, F, sp, fs, ps, pend, zs, t, et, hac, hp),
    e => need.of(ds, ks, img, D.RG(foc, 0, sp, pend, D.R59.list(D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62})), m, nx, fi, im, pg, lim, inp, foc, F, sp, fs, ps, zs, t, et, hac, e), {==}, et,
    tup.w(q, g, x, fs, w, ew), (hq, afs), {==}, {==}, {==}, {==}, {==},
    regs2 => m2 => nx2 => pg2 => h8 => hi => tup.eh(36, ds, ks, img, fi, im, lim, inp, foc, q, g, x, regs2, m2, nx2, pg2, h8, hi),
    hd.ok(D.FK.tupb{}, q), {==}, {==}, nd.cell(ds, im, fi, nx, foc, Cr.Cir.Cells.get(m, foc), F, D.A.tag(F), nd),
    ((isf, Unit{}), ((tup.x(ds, ks, img, m, nx, fi, im, foc, q, g, x, isf), (tup.y(ds, ks, img, m, nx, fi, im, foc, q, g, x, isf), Unit{})), ((tup.n2(m, foc, q, g, x), (tup.n3(m, foc, q, g, x), Unit{})), (frs, (hp, io))))), hac)

# mv.ev.tup0: M.ev's tests reach the frame's push
def tup0.disp(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32, +r4: U32, +r5: U32, +r6: U32, +r7: U32, +r8: U32, +r9: U32, +r10: U32, +r11: U32, +r12: U32, +r13: U32, +r14: U32, +r15: U32, +r16: U32, +r17: U32, +r18: U32, +r19: U32, +r20: U32, +r21: U32, +r22: U32, +r23: U32, +r24: U32, +r25: U32, +r26: U32, +r27: U32, +r28: U32, +r29: U32, +r30: U32, +r31: U32, +r32: U32, +r33: U32, +r34: U32, +r35: U32, +r36: U32, +r37: U32, +r38: U32, +r39: U32, +r40: U32, +r41: U32, +r42: U32, +r43: U32, +r44: U32, +r45: U32, +r46: U32, +r47: U32, +r48: U32, +r49: U32, +r50: U32, +r51: U32, +r52: U32, +r53: U32, +r54: U32, +r55: U32, +r56: U32, +r57: U32, +r58: U32, +r59: U32, +r60: U32, +r61: U32, +r62: U32,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +q: Bk.Quan, +g: Bk.Term, +x: Bk.Term,
  +nd: D.Nd(ds, im, fi, nx, foc, Cr.Cir.Cells.get(m, foc), Bk.Term.Tup{q, g, x}, D.A.tag(Bk.Term.Tup{q, g, x})), +tb: D.Tbl(m, im, fi, nx),
  +hv: {D.Fl(m, foc, 256) == False{} : Bool}, +hq: {El.Quan.live(q) == False{} : Bool}, +hqs: D.Qs(Cr.Cir.Cells.get(m, foc), q)) ->
  {Cr.Cir.exec(f, D.B.body(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)) == Cr.Cir.exec(f, K.stmt.else(Mc.M.ev.tup()), K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)) : Cr.Cir.Out}:
  +F = {Bk.Term.Tup{q, g, x} : Bk.Term}
  +st2 = {K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp) : Cr.Cir.State}
  +f1 = D.Fd(0n, m, foc)
  +QV = Wa.Wasm.op(Wa.Wasm.Op.and{}, Wa.Wasm.op(Wa.Wasm.Op.shr_u{}, f1, 6), 3)
  +ef = X.ev.fld(0n, Mc.M.g(8n), st2, foc, {==}, nd.cell(ds, im, fi, nx, foc, Cr.Cir.Cells.get(m, foc), F, D.A.tag(F), nd))
  +esh = X.ev.op(Wa.Wasm.Op.shr_u{}, Mc.M.f(0n, Mc.M.g(8n)), Mc.M.c(6), st2, f1, 6, ef, {==})
  +eand = X.ev.op(Wa.Wasm.Op.and{}, Mc.M.shr(Mc.M.f(0n, Mc.M.g(8n)), Mc.M.c(6)), Mc.M.c(3), st2, Wa.Wasm.op(Wa.Wasm.Op.shr_u{}, f1, 6), 3, esh, {==})
  +ene = X.ev.op(Wa.Wasm.Op.ne{}, Mc.M.q(Mc.M.g(8n)), Mc.M.c(0), st2, QV, 0, eand, {==})
  Equal.trans(Cr.Cir.Out, Cr.Cir.exec(f, D.B.body(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)), Cr.Cir.exec(f, Mc.M.ev.tup(), K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)), Cr.Cir.exec(f, K.stmt.else(Mc.M.ev.tup()), K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)),
    Equal.trans(Cr.Cir.Out, Cr.Cir.exec(f, D.B.body(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)), Cr.Cir.exec(f, K.B.else(), K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)), Cr.Cir.exec(f, Mc.M.ev.tup(), K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)),
    ev.pre.E(f, ds, ks, img, foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp, F, nd, tb, hv, {==}),
    br.tup(f, K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp), D.Fd(0n, m, foc), nd.tag(ds, im, fi, nx, foc, Cr.Cir.Cells.get(m, foc), F, D.A.tag(F), nd), {==})),
    D.eq.if.e(f, K.stmt.cond(Mc.M.ev.tup()), K.stmt.then(Mc.M.ev.tup()), K.stmt.else(Mc.M.ev.tup()), K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp), Wa.Wasm.op(Wa.Wasm.Op.ne{}, QV, 0), ene,
      (%Equal.sym(U32, D.QnW(D.Fd(0n, m, foc)), Mc.Img.quan(q), hqs) : {U32.is_zero(Wa.Wasm.op(Wa.Wasm.Op.ne{}, _, 0)) == True{} : Bool}; q.z(q, hq))))

def nw.tup0() -> {NW(K.stmt.else(Mc.M.ev.tup())) == True{} : Bool}:
  {==}

# mv.ev.tup0's frame costs less than the focus
def tup0.w(+q: Bk.Quan, +g: Bk.Term, +x: Bk.Term, +fs: List<&2, D.AF>, +w: Nat, ew: {D.A.w(False{}, Bk.Term.Tup{q, g, x}, fs) == w : Nat}) ->
  N.Le(1n+D.A.w(False{}, x, Con{D.AF{D.FK.tupa{}, q, False{}, g, g}, fs}), w):
  %ew : N.Le(1n+D.A.w(False{}, x, Con{D.AF{D.FK.tupa{}, q, False{}, g, g}, fs}), _)
  w.lt(Pg.Term.size(x), Pg.Term.size(g), Pg.Term.size(Bk.Term.Tup{q, g, x}), D.A.w.frames(fs), 1n, Equal.cong(Nat, Nat, z => 1n+z, Nat.add(Pg.Term.size(g), Pg.Term.size(x)), Nat.add(Pg.Term.size(x), Pg.Term.size(g)), add.comm(Pg.Term.size(g), Pg.Term.size(x))), Unit{})

# mv.ev.tup0: the frame pushed, an admin move
def tup0.mv(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32, +r4: U32, +r5: U32, +r6: U32, +r7: U32, +r8: U32, +r9: U32, +r10: U32, +r11: U32, +r12: U32, +r13: U32, +r14: U32, +r15: U32, +r16: U32, +r17: U32, +r18: U32, +r19: U32, +r20: U32, +r21: U32, +r22: U32, +r23: U32, +r24: U32, +r25: U32, +r26: U32, +r27: U32, +r28: U32, +r29: U32, +r30: U32, +r31: U32, +r32: U32, +r33: U32, +r34: U32, +r35: U32, +r36: U32, +r37: U32, +r38: U32, +r39: U32, +r40: U32, +r41: U32, +r42: U32, +r43: U32, +r44: U32, +r45: U32, +r46: U32, +r47: U32, +r48: U32, +r49: U32, +r50: U32, +r51: U32, +r52: U32, +r53: U32, +r54: U32, +r55: U32, +r56: U32, +r57: U32, +r58: U32, +r59: U32, +r60: U32, +r61: U32, +r62: U32,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat, +fs: List<&2, D.AF>,
  +ps: List<&2, U32>, +q: Bk.Quan, +g: Bk.Term, +x: Bk.Term, +et: {D.A.plugs(fs, Bk.Term.Tup{q, g, x}) == t : Bk.Term}, +ew: {D.A.w(False{}, Bk.Term.Tup{q, g, x}, fs) == w : Nat}, +afs: D.AFs.ok(ds, fs),
  +isf: D.Is(ds, m, im, fi, nx, ks, img, foc, Bk.Term.Tup{q, g, x}), +frs: D.Frs(ds, m, im, fi, nx, ks, img, ps, sp, fs),
  +hp: D.Heap(m, nx, fi, im, [foc], pend, ps), +io: D.ImgOK(ds, ks, img, m, im, fi, nx), +zs: List<&2, D.Rt>,
  +hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, [D.Rt{foc, Bk.Term.Tup{q, g, x}}], Nil{}, sp, fs, ps, zs), +hv: {D.Fl(m, foc, 256) == False{} : Bool}, +hq: {El.Quan.live(q) == False{} : Bool}) ->
  D.PostB(False{}, Cr.Cir.exec(f, D.B.body(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)), s => K.MV.next(ds, ks, img, D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), t, w, s), s => st2 => D.HR(ds, t, s, st2), D.Budget(ds, D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp))):
  +F = {Bk.Term.Tup{q, g, x} : Bk.Term}
  +nd = D.is.nd(ds, m, im, fi, nx, ks, img, foc, F, isf)
  +tb = K.img.tbl(ds, ks, img, m, im, fi, nx, io)
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, D.B.body(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)), Cr.Cir.exec(f, K.stmt.else(Mc.M.ev.tup()), K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)),
    tup0.disp(f, ds, ks, img, foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp, q, g, x, nd, tb, hv, hq, tup.qs(ds, ks, img, m, nx, fi, im, foc, q, g, x, isf))) :
    D.PostB(False{}, _, s => K.MV.next(ds, ks, img, D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), t, w, s), s => st2 => D.HR(ds, t, s, st2), D.Budget(ds, D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)))
  frame2.mv(f, ds, ks, img, D.St.regs(K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)), m, nx, fi, im, lim, inp, foc, F, D.Fd(3n, m, foc), x, D.Fd(2n, m, foc), g, g, D.FK.tupa{}, q, Hd(37, Mc.Img.quan(q)), fs, sp, ps,
    pg, D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), t, w, Mc.M.header(Mc.K.tup_a(), Mc.M.q(Mc.M.g(Mc.R.c())), Mc.M.c(0)), D.Budget(ds, D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), t), pend, zs, 3n, 2n, {==},
    room.of(ds, ks, img, D.RG(foc, 0, sp, pend, D.R59.list(D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62})), m, nx, fi, im, pg, lim, inp, foc, F, sp, fs, ps, pend, zs, t, et, hac, hp),
    e => need.of(ds, ks, img, D.RG(foc, 0, sp, pend, D.R59.list(D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62})), m, nx, fi, im, pg, lim, inp, foc, F, sp, fs, ps, zs, t, et, hac, e), {==}, et,
    tup0.w(q, g, x, fs, w, ew), ((%Equal.sym(Bool, El.Quan.live(q), False{}, hq) : {Bool.or(Bool.not(_), El.Eval.vals(ds, g, False{})) == True{} : Bool}; {==}), afs), {==}, {==}, {==}, {==}, {==},
    regs2 => m2 => nx2 => pg2 => h8 => hi => tup.eh(37, ds, ks, img, fi, im, lim, inp, foc, q, g, x, regs2, m2, nx2, pg2, h8, hi),
    hd.ok(D.FK.tupa{}, q), {==}, {==}, nd.cell(ds, im, fi, nx, foc, Cr.Cir.Cells.get(m, foc), F, D.A.tag(F), nd),
    ((isf, Unit{}), ((tup.y(ds, ks, img, m, nx, fi, im, foc, q, g, x, isf), (tup.x(ds, ks, img, m, nx, fi, im, foc, q, g, x, isf), Unit{})), ((tup.n3(m, foc, q, g, x), (tup.n2(m, foc, q, g, x), Unit{})), (frs, (hp, io))))), hac)

# mv.ev.min: M.ev's tests reach the frame's push
def min.disp(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32, +r4: U32, +r5: U32, +r6: U32, +r7: U32, +r8: U32, +r9: U32, +r10: U32, +r11: U32, +r12: U32, +r13: U32, +r14: U32, +r15: U32, +r16: U32, +r17: U32, +r18: U32, +r19: U32, +r20: U32, +r21: U32, +r22: U32, +r23: U32, +r24: U32, +r25: U32, +r26: U32, +r27: U32, +r28: U32, +r29: U32, +r30: U32, +r31: U32, +r32: U32, +r33: U32, +r34: U32, +r35: U32, +r36: U32, +r37: U32, +r38: U32, +r39: U32, +r40: U32, +r41: U32, +r42: U32, +r43: U32, +r44: U32, +r45: U32, +r46: U32, +r47: U32, +r48: U32, +r49: U32, +r50: U32, +r51: U32, +r52: U32, +r53: U32, +r54: U32, +r55: U32, +r56: U32, +r57: U32, +r58: U32, +r59: U32, +r60: U32, +r61: U32, +r62: U32,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +g: Bk.Term, +x: Bk.Term,
  +nd: D.Nd(ds, im, fi, nx, foc, Cr.Cir.Cells.get(m, foc), Bk.Term.Min{g, x}, D.A.tag(Bk.Term.Min{g, x})), +tb: D.Tbl(m, im, fi, nx),
  +hv: {D.Fl(m, foc, 256) == False{} : Bool}) ->
  {Cr.Cir.exec(f, D.B.body(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)) == Cr.Cir.exec(f, Mc.M.ev.min(), K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)) : Cr.Cir.Out}:
  +F = {Bk.Term.Min{g, x} : Bk.Term}
  Equal.trans(Cr.Cir.Out, Cr.Cir.exec(f, D.B.body(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)), Cr.Cir.exec(f, K.B.else(), K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)), Cr.Cir.exec(f, Mc.M.ev.min(), K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)),
    ev.pre.E(f, ds, ks, img, foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp, F, nd, tb, hv, {==}),
    br.min(f, K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp), D.Fd(0n, m, foc), nd.tag(ds, im, fi, nx, foc, Cr.Cir.Cells.get(m, foc), F, D.A.tag(F), nd), {==}))

def nw.min() -> {NW(Mc.M.ev.min()) == True{} : Bool}:
  {==}

# mv.ev.min's frame costs less than the focus
def min.w(+g: Bk.Term, +x: Bk.Term, +fs: List<&2, D.AF>, +w: Nat, ew: {D.A.w(False{}, Bk.Term.Min{g, x}, fs) == w : Nat}) ->
  N.Le(1n+D.A.w(False{}, g, Con{D.AF{D.FK.minb{}, Bk.Quan.Q0{}, False{}, x, x}, fs}), w):
  %ew : N.Le(1n+D.A.w(False{}, g, Con{D.AF{D.FK.minb{}, Bk.Quan.Q0{}, False{}, x, x}, fs}), _)
  w.lt(Pg.Term.size(g), Pg.Term.size(x), Pg.Term.size(Bk.Term.Min{g, x}), D.A.w.frames(fs), 1n+A3(Pg.Term.size(x)), {==}, N.le_succ(A3(Pg.Term.size(x)), A3(Pg.Term.size(x)), N.le_refl(A3(Pg.Term.size(x)))))

# mv.ev.min: the frame pushed, an admin move
def min.mv(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32, +r4: U32, +r5: U32, +r6: U32, +r7: U32, +r8: U32, +r9: U32, +r10: U32, +r11: U32, +r12: U32, +r13: U32, +r14: U32, +r15: U32, +r16: U32, +r17: U32, +r18: U32, +r19: U32, +r20: U32, +r21: U32, +r22: U32, +r23: U32, +r24: U32, +r25: U32, +r26: U32, +r27: U32, +r28: U32, +r29: U32, +r30: U32, +r31: U32, +r32: U32, +r33: U32, +r34: U32, +r35: U32, +r36: U32, +r37: U32, +r38: U32, +r39: U32, +r40: U32, +r41: U32, +r42: U32, +r43: U32, +r44: U32, +r45: U32, +r46: U32, +r47: U32, +r48: U32, +r49: U32, +r50: U32, +r51: U32, +r52: U32, +r53: U32, +r54: U32, +r55: U32, +r56: U32, +r57: U32, +r58: U32, +r59: U32, +r60: U32, +r61: U32, +r62: U32,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat, +fs: List<&2, D.AF>,
  +ps: List<&2, U32>, +g: Bk.Term, +x: Bk.Term, +et: {D.A.plugs(fs, Bk.Term.Min{g, x}) == t : Bk.Term}, +ew: {D.A.w(False{}, Bk.Term.Min{g, x}, fs) == w : Nat}, +afs: D.AFs.ok(ds, fs),
  +isf: D.Is(ds, m, im, fi, nx, ks, img, foc, Bk.Term.Min{g, x}), +frs: D.Frs(ds, m, im, fi, nx, ks, img, ps, sp, fs),
  +hp: D.Heap(m, nx, fi, im, [foc], pend, ps), +io: D.ImgOK(ds, ks, img, m, im, fi, nx), +zs: List<&2, D.Rt>,
  +hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, [D.Rt{foc, Bk.Term.Min{g, x}}], Nil{}, sp, fs, ps, zs), +hv: {D.Fl(m, foc, 256) == False{} : Bool}) ->
  D.PostB(False{}, Cr.Cir.exec(f, D.B.body(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)), s => K.MV.next(ds, ks, img, D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), t, w, s), s => st2 => D.HR(ds, t, s, st2), D.Budget(ds, D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp))):
  +F = {Bk.Term.Min{g, x} : Bk.Term}
  +nd = D.is.nd(ds, m, im, fi, nx, ks, img, foc, F, isf)
  +tb = K.img.tbl(ds, ks, img, m, im, fi, nx, io)
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, D.B.body(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)), Cr.Cir.exec(f, Mc.M.ev.min(), K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)),
    min.disp(f, ds, ks, img, foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp, g, x, nd, tb, hv)) :
    D.PostB(False{}, _, s => K.MV.next(ds, ks, img, D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), t, w, s), s => st2 => D.HR(ds, t, s, st2), D.Budget(ds, D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)))
  frame2.mv(f, ds, ks, img, D.St.regs(K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)), m, nx, fi, im, lim, inp, foc, F, D.Fd(2n, m, foc), g, D.Fd(3n, m, foc), x, x, D.FK.minb{}, Bk.Quan.Q0{}, 39, fs, sp, ps,
    pg, D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), t, w, Mc.M.c(Mc.K.min_b()), D.Budget(ds, D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), t), pend, zs, 2n, 3n, {==},
    room.of(ds, ks, img, D.RG(foc, 0, sp, pend, D.R59.list(D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62})), m, nx, fi, im, pg, lim, inp, foc, F, sp, fs, ps, pend, zs, t, et, hac, hp),
    e => need.of(ds, ks, img, D.RG(foc, 0, sp, pend, D.R59.list(D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62})), m, nx, fi, im, pg, lim, inp, foc, F, sp, fs, ps, zs, t, et, hac, e), {==}, et,
    min.w(g, x, fs, w, ew), (Unit{}, afs), {==}, {==}, {==}, {==}, {==},
    regs2 => m2 => nx2 => pg2 => h8 => hi => {==},
    hd.min(), {==}, {==}, nd.cell(ds, im, fi, nx, foc, Cr.Cir.Cells.get(m, foc), F, D.A.tag(F), nd),
    ((isf, Unit{}), ((min.x(ds, ks, img, m, nx, fi, im, foc, g, x, isf), (min.y(ds, ks, img, m, nx, fi, im, foc, g, x, isf), Unit{})), ((min.n2(m, foc, g, x), (min.n3(m, foc, g, x), Unit{})), (frs, (hp, io))))), hac)


# mv.ev.rwt: x, y and z get the parts e, p and b of the focus' cell, each gains
# a pointer; y and z trade places among the roots; then tail.mv pushes the
# frame Rwt □ p b
def rwt.tl(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>, +m: Cr.Cir.Cells,
  +nx: U32, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +foc: U32, +e: Bk.Term, +p: Bk.Term, +b: Bk.Term, +xc: U32, +yc: U32,
  +zc: U32, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +pg: U32, +st0: Cr.Cir.State, +t: Bk.Term, +w: Nat, +B: Nat, +pend: U32,
  +zs: List<&2, D.Rt>,
  hroom: Or(N.Le(Nat.mul(20n, Nat.add(U32.to_nat(nx), 1n)), B), {U32.is_eq(pend, 0) == False{} : Bool}),
  hnd: {D.Pend.none(ps) == True{} : Bool} -> N.Le(1n+Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), D.Need(ds, st0, t)),
  +hmc: {D.Mem.cells(st0) == Nat.sub(U32.to_nat(nx), U32.to_nat(fi)) : Nat},
  +et2: {D.A.plugs(Con{D.AF{D.FK.rwt{}, Bk.Quan.Q0{}, False{}, p, b}, fs}, e) == t : Bk.Term}, +ew2: N.Le(1n+D.A.w(False{}, e, Con{D.AF{D.FK.rwt{}, Bk.Quan.Q0{}, False{}, p, b}, fs}), w), +afs2: D.AFs.ok(ds, Con{D.AF{D.FK.rwt{}, Bk.Quan.Q0{}, False{}, p, b}, fs}),
  +hl: {List.length(&2, U32, regs) == 63n : Nat}, +h1: {List.get(&2, U32, regs, 1n) == Some{0} : Maybe<&2, U32>},
  +h2: {List.get(&2, U32, regs, 2n) == Some{sp} : Maybe<&2, U32>}, +h3: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>},
  +h8: {List.get(&2, U32, regs, 8n) == Some{foc} : Maybe<&2, U32>}, +m3: Cr.Cir.Cells, +stC: Cr.Cir.State, qk: IncQ(ds, ks, img, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs, 11n, xc), 12n, yc), 13n, zc), m3, nx, fi, im, pg, lim, inp, [D.Rt{yc, p}, D.Rt{xc, e}, D.Rt{foc, Bk.Term.Rwt{e, p, b}}], Nil{}, fs, sp, pend, ps, zc, b, Nil{}, zs, stC)) ->
  D.PostB(False{}, Cr.Cir.exec(f, X.sel.b(X.sel.b(X.sel.b(X.sel.b(X.sel.b(X.sel.b(Mc.M.ev.rwt())))))), stC), s => K.MV.next(ds, ks, img, st0, t, w, s), s => st2 => D.HR(ds, t, s, st2), B, lim):
  match qk:
    case Tuple{+m4, Tuple{+est, Tuple{_, Tuple{+hsC, hacC}}}}:
      +hlx = X.L.len(regs, 11n, xc, 63n, hl)
      +hly = X.L.len(List.set(&2, U32, regs, 11n, xc), 12n, yc, 63n, hlx)
      +hlz = X.L.len(List.set(&2, U32, List.set(&2, U32, regs, 11n, xc), 12n, yc), 13n, zc, 63n, hly)
      +hsD = hsk.swap(True{}, ds, ks, img, m4, nx, fi, im, D.Rt{zc, b}, D.Rt{yc, p}, [D.Rt{xc, e}, D.Rt{foc, Bk.Term.Rwt{e, p, b}}], fs, sp, pend, ps,
        hsk.drop(True{}, ds, ks, img, m4, nx, fi, im, [D.Rt{zc, b}, D.Rt{yc, p}, D.Rt{xc, e}, D.Rt{foc, Bk.Term.Rwt{e, p, b}}], D.Rt{zc, b}, Nil{}, fs, sp, pend, ps, hsC))
      +hacD = acc.swap(True{}, ds, ks, img, m4, nx, fi, im, D.Rt{zc, b}, D.Rt{yc, p}, [D.Rt{xc, e}, D.Rt{foc, Bk.Term.Rwt{e, p, b}}], sp, fs, ps, zs, hacC)
      +h13 = X.L.gs(List.set(&2, U32, List.set(&2, U32, regs, 11n, xc), 12n, yc), 13n, zc, X.L.lt(List.set(&2, U32, List.set(&2, U32, regs, 11n, xc), 12n, yc), 13n, hly, {==}))
      %Equal.sym(Cr.Cir.State, stC, Cr.Cir.State{List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs, 11n, xc), 12n, yc), 13n, zc), m4, nx, fi, im, pg, lim, inp, Nil{}, 0}, est) : D.PostB(False{}, Cr.Cir.exec(f, X.sel.b(X.sel.b(X.sel.b(X.sel.b(X.sel.b(X.sel.b(Mc.M.ev.rwt())))))), _), s => K.MV.next(ds, ks, img, st0, t, w, s), s => st2 => D.HR(ds, t, s, st2), B, lim)
      tail.mv(f, ds, ks, img, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs, 11n, xc), 12n, yc), 13n, zc), m4, nx, fi, im, lim, inp, foc, Bk.Term.Rwt{e, p, b}, xc, e, yc, p, zc, b, D.FK.rwt{}, Bk.Quan.Q0{}, 38, fs, sp, ps, pg, st0, t, w,
        Mc.M.c(Mc.K.rwt()), Mc.M.g(Mc.R.z()), B, pend, zs, hroom, hnd, hmc, et2, ew2, afs2, hsD, hacD, hlz,
        X.L.go(List.set(&2, U32, List.set(&2, U32, regs, 11n, xc), 12n, yc), 13n, 1n, zc, 0, {==}, X.L.go(List.set(&2, U32, regs, 11n, xc), 12n, 1n, yc, 0, {==}, X.L.go(regs, 11n, 1n, xc, 0, {==}, h1))),
        X.L.go(List.set(&2, U32, List.set(&2, U32, regs, 11n, xc), 12n, yc), 13n, 2n, zc, sp, {==}, X.L.go(List.set(&2, U32, regs, 11n, xc), 12n, 2n, yc, sp, {==}, X.L.go(regs, 11n, 2n, xc, sp, {==}, h2))),
        X.L.go(List.set(&2, U32, List.set(&2, U32, regs, 11n, xc), 12n, yc), 13n, 3n, zc, pend, {==}, X.L.go(List.set(&2, U32, regs, 11n, xc), 12n, 3n, yc, pend, {==}, X.L.go(regs, 11n, 3n, xc, pend, {==}, h3))),
        X.L.go(List.set(&2, U32, List.set(&2, U32, regs, 11n, xc), 12n, yc), 13n, 8n, zc, foc, {==}, X.L.go(List.set(&2, U32, regs, 11n, xc), 12n, 8n, yc, foc, {==}, X.L.go(regs, 11n, 8n, xc, foc, {==}, h8))),
        X.L.go(List.set(&2, U32, List.set(&2, U32, regs, 11n, xc), 12n, yc), 13n, 11n, zc, xc, {==}, X.L.go(List.set(&2, U32, regs, 11n, xc), 12n, 11n, yc, xc, {==}, X.L.gs(regs, 11n, xc, X.L.lt(regs, 11n, hl, {==})))),
        X.L.go(List.set(&2, U32, List.set(&2, U32, regs, 11n, xc), 12n, yc), 13n, 12n, zc, yc, {==}, X.L.gs(List.set(&2, U32, regs, 11n, xc), 12n, yc, X.L.lt(List.set(&2, U32, regs, 11n, xc), 12n, hlx, {==}))),
        regs2 => m2 => nx2 => pg2 => h8b => hi => {==},
        regs2 => m2 => nx2 => pg2 => k13 => Equal.trans(Maybe<&2, U32>, List.get(&2, U32, regs2, 13n), List.get(&2, U32, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs, 11n, xc), 12n, yc), 13n, zc), 13n), Some{zc}, k13, h13),
        hd.rwt())

def rwt.incz(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>, +m: Cr.Cir.Cells,
  +nx: U32, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +foc: U32, +e: Bk.Term, +p: Bk.Term, +b: Bk.Term, +xc: U32, +yc: U32,
  +zc: U32, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +pg: U32, +st0: Cr.Cir.State, +t: Bk.Term, +w: Nat, +B: Nat, +pend: U32,
  +zs: List<&2, D.Rt>,
  hroom: Or(N.Le(Nat.mul(20n, Nat.add(U32.to_nat(nx), 1n)), B), {U32.is_eq(pend, 0) == False{} : Bool}),
  hnd: {D.Pend.none(ps) == True{} : Bool} -> N.Le(1n+Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), D.Need(ds, st0, t)),
  +hmc: {D.Mem.cells(st0) == Nat.sub(U32.to_nat(nx), U32.to_nat(fi)) : Nat},
  +et2: {D.A.plugs(Con{D.AF{D.FK.rwt{}, Bk.Quan.Q0{}, False{}, p, b}, fs}, e) == t : Bk.Term}, +ew2: N.Le(1n+D.A.w(False{}, e, Con{D.AF{D.FK.rwt{}, Bk.Quan.Q0{}, False{}, p, b}, fs}), w), +afs2: D.AFs.ok(ds, Con{D.AF{D.FK.rwt{}, Bk.Quan.Q0{}, False{}, p, b}, fs}),
  +hl: {List.length(&2, U32, regs) == 63n : Nat}, +h1: {List.get(&2, U32, regs, 1n) == Some{0} : Maybe<&2, U32>},
  +h2: {List.get(&2, U32, regs, 2n) == Some{sp} : Maybe<&2, U32>}, +h3: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>},
  +h8: {List.get(&2, U32, regs, 8n) == Some{foc} : Maybe<&2, U32>}, +m2: Cr.Cir.Cells, +stB: Cr.Cir.State, qj: IncQ(ds, ks, img, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs, 11n, xc), 12n, yc), 13n, zc), m2, nx, fi, im, pg, lim, inp, [D.Rt{xc, e}, D.Rt{foc, Bk.Term.Rwt{e, p, b}}], [D.Rt{zc, b}], fs, sp, pend, ps, yc, p, Nil{}, zs, stB)) ->
  D.PostB(False{}, Cr.Cir.exec(f, X.sel.b(X.sel.b(X.sel.b(X.sel.b(X.sel.b(Mc.M.ev.rwt()))))), stB), s => K.MV.next(ds, ks, img, st0, t, w, s), s => st2 => D.HR(ds, t, s, st2), B, lim):
  match qj:
    case Tuple{+m3, Tuple{+est, Tuple{_, Tuple{+hsB, hacB}}}}:
      +hlx = X.L.len(regs, 11n, xc, 63n, hl)
      +hly = X.L.len(List.set(&2, U32, regs, 11n, xc), 12n, yc, 63n, hlx)
      +hc13 = X.L.gs(List.set(&2, U32, List.set(&2, U32, regs, 11n, xc), 12n, yc), 13n, zc, X.L.lt(List.set(&2, U32, List.set(&2, U32, regs, 11n, xc), 12n, yc), 13n, hly, {==}))
      +hsB2 = hsk.drop(True{}, ds, ks, img, m3, nx, fi, im, [D.Rt{yc, p}, D.Rt{xc, e}, D.Rt{foc, Bk.Term.Rwt{e, p, b}}], D.Rt{yc, p}, [D.Rt{zc, b}], fs, sp, pend, ps, hsB)
      hi = D.inc.post(f, True{}, ds, ks, img, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs, 11n, xc), 12n, yc), 13n, zc), m3, nx, fi, im, pg, lim, inp, 13n, [D.Rt{yc, p}, D.Rt{xc, e}, D.Rt{foc, Bk.Term.Rwt{e, p, b}}], Nil{}, fs, sp, pend, ps,
        zc, b, Nil{}, zs, hsB2, hacB, Unit{}, hc13)
      %Equal.sym(Cr.Cir.State, stB, Cr.Cir.State{List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs, 11n, xc), 12n, yc), 13n, zc), m3, nx, fi, im, pg, lim, inp, Nil{}, 0}, est) : D.PostB(False{}, Cr.Cir.exec(f, X.sel.b(X.sel.b(X.sel.b(X.sel.b(X.sel.b(Mc.M.ev.rwt()))))), _), s => K.MV.next(ds, ks, img, st0, t, w, s), s => st2 => D.HR(ds, t, s, st2), B, lim)
      D.postb.seq(f, False{}, Mc.M.inc(13n), X.sel.b(X.sel.b(X.sel.b(X.sel.b(X.sel.b(X.sel.b(Mc.M.ev.rwt())))))), Cr.Cir.State{List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs, 11n, xc), 12n, yc), 13n, zc), m3, nx, fi, im, pg, lim, inp, Nil{}, 0}, st2 => IncQ(ds, ks, img, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs, 11n, xc), 12n, yc), 13n, zc), m3, nx, fi, im, pg, lim, inp, [D.Rt{yc, p}, D.Rt{xc, e}, D.Rt{foc, Bk.Term.Rwt{e, p, b}}], Nil{}, fs, sp, pend, ps, zc, b, Nil{}, zs, st2), s => K.MV.next(ds, ks, img, st0, t, w, s), s => st2 => Empty, s => st2 => D.HR(ds, t, s, st2), B, lim,
        D.postb.wk(False{}, Cr.Cir.exec(f, Mc.M.inc(13n), Cr.Cir.State{List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs, 11n, xc), 12n, yc), 13n, zc), m3, nx, fi, im, pg, lim, inp, Nil{}, 0}), st2 => IncQ(ds, ks, img, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs, 11n, xc), 12n, yc), 13n, zc), m3, nx, fi, im, pg, lim, inp, [D.Rt{yc, p}, D.Rt{xc, e}, D.Rt{foc, Bk.Term.Rwt{e, p, b}}], Nil{}, fs, sp, pend, ps, zc, b, Nil{}, zs, st2), s => st2 => Empty, 0n, B, lim,
          hi, N.le_zero(B)),
        s => st2 => e2 => Empty.absurd(D.HR(ds, t, s, st2), e2),
        +stC => qk => rwt.tl(f, ds, ks, img, regs, m, nx, fi, im, lim, inp, foc, e, p, b, xc, yc, zc, fs, sp, ps, pg, st0, t, w, B, pend, zs, hroom, hnd, hmc, et2, ew2, afs2, hl, h1, h2, h3, h8, m3, stC, qk))

def rwt.incy(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>, +m: Cr.Cir.Cells,
  +nx: U32, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +foc: U32, +e: Bk.Term, +p: Bk.Term, +b: Bk.Term, +xc: U32, +yc: U32,
  +zc: U32, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +pg: U32, +st0: Cr.Cir.State, +t: Bk.Term, +w: Nat, +B: Nat, +pend: U32,
  +zs: List<&2, D.Rt>,
  hroom: Or(N.Le(Nat.mul(20n, Nat.add(U32.to_nat(nx), 1n)), B), {U32.is_eq(pend, 0) == False{} : Bool}),
  hnd: {D.Pend.none(ps) == True{} : Bool} -> N.Le(1n+Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), D.Need(ds, st0, t)),
  +hmc: {D.Mem.cells(st0) == Nat.sub(U32.to_nat(nx), U32.to_nat(fi)) : Nat},
  +et2: {D.A.plugs(Con{D.AF{D.FK.rwt{}, Bk.Quan.Q0{}, False{}, p, b}, fs}, e) == t : Bk.Term}, +ew2: N.Le(1n+D.A.w(False{}, e, Con{D.AF{D.FK.rwt{}, Bk.Quan.Q0{}, False{}, p, b}, fs}), w), +afs2: D.AFs.ok(ds, Con{D.AF{D.FK.rwt{}, Bk.Quan.Q0{}, False{}, p, b}, fs}),
  +hl: {List.length(&2, U32, regs) == 63n : Nat}, +h1: {List.get(&2, U32, regs, 1n) == Some{0} : Maybe<&2, U32>},
  +h2: {List.get(&2, U32, regs, 2n) == Some{sp} : Maybe<&2, U32>}, +h3: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>},
  +h8: {List.get(&2, U32, regs, 8n) == Some{foc} : Maybe<&2, U32>}, +stA: Cr.Cir.State, qi: IncQ(ds, ks, img, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs, 11n, xc), 12n, yc), 13n, zc), m, nx, fi, im, pg, lim, inp, [D.Rt{foc, Bk.Term.Rwt{e, p, b}}], [D.Rt{yc, p}, D.Rt{zc, b}], fs, sp, pend, ps, xc, e, Nil{}, zs, stA)) ->
  D.PostB(False{}, Cr.Cir.exec(f, X.sel.b(X.sel.b(X.sel.b(X.sel.b(Mc.M.ev.rwt())))), stA), s => K.MV.next(ds, ks, img, st0, t, w, s), s => st2 => D.HR(ds, t, s, st2), B, lim):
  match qi:
    case Tuple{+m2, Tuple{+est, Tuple{_, Tuple{+hsA, hacA}}}}:
      +hlx = X.L.len(regs, 11n, xc, 63n, hl)
      +hc12 = X.L.go(List.set(&2, U32, List.set(&2, U32, regs, 11n, xc), 12n, yc), 13n, 12n, zc, yc, {==}, X.L.gs(List.set(&2, U32, regs, 11n, xc), 12n, yc, X.L.lt(List.set(&2, U32, regs, 11n, xc), 12n, hlx, {==})))
      +hsA2 = hsk.drop(True{}, ds, ks, img, m2, nx, fi, im, [D.Rt{xc, e}, D.Rt{foc, Bk.Term.Rwt{e, p, b}}], D.Rt{xc, e}, [D.Rt{yc, p}, D.Rt{zc, b}], fs, sp, pend, ps, hsA)
      hi = D.inc.post(f, True{}, ds, ks, img, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs, 11n, xc), 12n, yc), 13n, zc), m2, nx, fi, im, pg, lim, inp, 12n, [D.Rt{xc, e}, D.Rt{foc, Bk.Term.Rwt{e, p, b}}], [D.Rt{zc, b}], fs, sp, pend, ps,
        yc, p, Nil{}, zs, hsA2, hacA, Unit{}, hc12)
      %Equal.sym(Cr.Cir.State, stA, Cr.Cir.State{List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs, 11n, xc), 12n, yc), 13n, zc), m2, nx, fi, im, pg, lim, inp, Nil{}, 0}, est) : D.PostB(False{}, Cr.Cir.exec(f, X.sel.b(X.sel.b(X.sel.b(X.sel.b(Mc.M.ev.rwt())))), _), s => K.MV.next(ds, ks, img, st0, t, w, s), s => st2 => D.HR(ds, t, s, st2), B, lim)
      D.postb.seq(f, False{}, Mc.M.inc(12n), X.sel.b(X.sel.b(X.sel.b(X.sel.b(X.sel.b(Mc.M.ev.rwt()))))), Cr.Cir.State{List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs, 11n, xc), 12n, yc), 13n, zc), m2, nx, fi, im, pg, lim, inp, Nil{}, 0}, st2 => IncQ(ds, ks, img, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs, 11n, xc), 12n, yc), 13n, zc), m2, nx, fi, im, pg, lim, inp, [D.Rt{xc, e}, D.Rt{foc, Bk.Term.Rwt{e, p, b}}], [D.Rt{zc, b}], fs, sp, pend, ps, yc, p, Nil{}, zs, st2), s => K.MV.next(ds, ks, img, st0, t, w, s), s => st2 => Empty, s => st2 => D.HR(ds, t, s, st2), B, lim,
        D.postb.wk(False{}, Cr.Cir.exec(f, Mc.M.inc(12n), Cr.Cir.State{List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs, 11n, xc), 12n, yc), 13n, zc), m2, nx, fi, im, pg, lim, inp, Nil{}, 0}), st2 => IncQ(ds, ks, img, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs, 11n, xc), 12n, yc), 13n, zc), m2, nx, fi, im, pg, lim, inp, [D.Rt{xc, e}, D.Rt{foc, Bk.Term.Rwt{e, p, b}}], [D.Rt{zc, b}], fs, sp, pend, ps, yc, p, Nil{}, zs, st2), s => st2 => Empty, 0n, B, lim,
          hi, N.le_zero(B)),
        s => st2 => e2 => Empty.absurd(D.HR(ds, t, s, st2), e2),
        +stB => qj => rwt.incz(f, ds, ks, img, regs, m, nx, fi, im, lim, inp, foc, e, p, b, xc, yc, zc, fs, sp, ps, pg, st0, t, w, B, pend, zs, hroom, hnd, hmc, et2, ew2, afs2, hl, h1, h2, h3, h8, m2, stB, qj))

def rwt.run(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +regs: List<&2, U32>, +m: Cr.Cir.Cells,
  +nx: U32, +fi: U32, +im: U32, +lim: U32, +inp: List<&2, Word(8n)>, +foc: U32, +e: Bk.Term, +p: Bk.Term, +b: Bk.Term, +xc: U32, +yc: U32,
  +zc: U32, +fs: List<&2, D.AF>, +sp: U32, +ps: List<&2, U32>, +pg: U32, +st0: Cr.Cir.State, +t: Bk.Term, +w: Nat, +B: Nat, +pend: U32,
  +zs: List<&2, D.Rt>,
  hroom: Or(N.Le(Nat.mul(20n, Nat.add(U32.to_nat(nx), 1n)), B), {U32.is_eq(pend, 0) == False{} : Bool}),
  hnd: {D.Pend.none(ps) == True{} : Bool} -> N.Le(1n+Nat.sub(U32.to_nat(nx), U32.to_nat(fi)), D.Need(ds, st0, t)),
  +hmc: {D.Mem.cells(st0) == Nat.sub(U32.to_nat(nx), U32.to_nat(fi)) : Nat},
  +et2: {D.A.plugs(Con{D.AF{D.FK.rwt{}, Bk.Quan.Q0{}, False{}, p, b}, fs}, e) == t : Bk.Term}, +ew2: N.Le(1n+D.A.w(False{}, e, Con{D.AF{D.FK.rwt{}, Bk.Quan.Q0{}, False{}, p, b}, fs}), w), +afs2: D.AFs.ok(ds, Con{D.AF{D.FK.rwt{}, Bk.Quan.Q0{}, False{}, p, b}, fs}),
  +hl: {List.length(&2, U32, regs) == 63n : Nat}, +h1: {List.get(&2, U32, regs, 1n) == Some{0} : Maybe<&2, U32>},
  +h2: {List.get(&2, U32, regs, 2n) == Some{sp} : Maybe<&2, U32>}, +h3: {List.get(&2, U32, regs, 3n) == Some{pend} : Maybe<&2, U32>},
  +h8: {List.get(&2, U32, regs, 8n) == Some{foc} : Maybe<&2, U32>}, +hxa: {D.Fd(2n, m, foc) == xc : U32}, +hyb: {D.Fd(3n, m, foc) == yc : U32}, +hzc: {D.Fd(4n, m, foc) == zc : U32},
  +hfoc: {Cr.Cir.is_cell(foc, im, fi, nx) == True{} : Bool},
  +hs0: D.HS(ds, ks, img, m, nx, fi, im, [D.Rt{foc, Bk.Term.Rwt{e, p, b}}], [D.Rt{xc, e}, D.Rt{yc, p}, D.Rt{zc, b}], fs, sp, pend, ps),
  +hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, [D.Rt{foc, Bk.Term.Rwt{e, p, b}}], Nil{}, sp, fs, ps, zs)) ->
  D.PostB(False{}, Cr.Cir.exec(f, Mc.M.ev.rwt(), Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, Nil{}, 0}), s => K.MV.next(ds, ks, img, st0, t, w, s), s => st2 => D.HR(ds, t, s, st2), B, lim):
  +S = {Cr.Cir.State{regs, m, nx, fi, im, pg, lim, inp, Nil{}, 0} : Cr.Cir.State}
  +SX = {Cr.Cir.State{List.set(&2, U32, regs, 11n, xc), m, nx, fi, im, pg, lim, inp, Nil{}, 0} : Cr.Cir.State}
  +SY = {Cr.Cir.State{List.set(&2, U32, List.set(&2, U32, regs, 11n, xc), 12n, yc), m, nx, fi, im, pg, lim, inp, Nil{}, 0} : Cr.Cir.State}
  +SZ = {Cr.Cir.State{List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs, 11n, xc), 12n, yc), 13n, zc), m, nx, fi, im, pg, lim, inp, Nil{}, 0} : Cr.Cir.State}
  +hlx = X.L.len(regs, 11n, xc, 63n, hl)
  +hly = X.L.len(List.set(&2, U32, regs, 11n, xc), 12n, yc, 63n, hlx)
  +h8x = X.L.go(regs, 11n, 8n, xc, foc, {==}, h8)
  +h8y = X.L.go(List.set(&2, U32, regs, 11n, xc), 12n, 8n, yc, foc, {==}, h8x)
  +evx = Equal.trans(Maybe<&2, U32>, Cr.Cir.eval(Mc.M.f(2n, Mc.M.g(8n)), S), Some{D.Fd(2n, m, foc)}, Some{xc},
    X.ev.fld(2n, Mc.M.g(8n), S, foc, h8, hfoc), Equal.cong(U32, Maybe<&2, U32>, v => Some{v}, D.Fd(2n, m, foc), xc, hxa))
  +evy = Equal.trans(Maybe<&2, U32>, Cr.Cir.eval(Mc.M.f(3n, Mc.M.g(8n)), SX), Some{D.Fd(3n, m, foc)}, Some{yc},
    X.ev.fld(3n, Mc.M.g(8n), SX, foc, h8x, hfoc), Equal.cong(U32, Maybe<&2, U32>, v => Some{v}, D.Fd(3n, m, foc), yc, hyb))
  +evz = Equal.trans(Maybe<&2, U32>, Cr.Cir.eval(Mc.M.f(4n, Mc.M.g(8n)), SY), Some{D.Fd(4n, m, foc)}, Some{zc},
    X.ev.fld(4n, Mc.M.g(8n), SY, foc, h8y, hfoc), Equal.cong(U32, Maybe<&2, U32>, v => Some{v}, D.Fd(4n, m, foc), zc, hzc))
  +ex = X.run.set(f, 11n, Mc.M.f(2n, Mc.M.g(8n)), S, xc, evx, hl, {==})
  +ey = X.run.set(f, 12n, Mc.M.f(3n, Mc.M.g(8n)), SX, yc, evy, hlx, {==})
  +ez = X.run.set(f, 13n, Mc.M.f(4n, Mc.M.g(8n)), SY, zc, evz, hly, {==})
  +hc11 = X.L.go(List.set(&2, U32, List.set(&2, U32, regs, 11n, xc), 12n, yc), 13n, 11n, zc, xc, {==}, X.L.go(List.set(&2, U32, regs, 11n, xc), 12n, 11n, yc, xc, {==}, X.L.gs(regs, 11n, xc, X.L.lt(regs, 11n, hl, {==}))))
  hi = D.inc.post(f, True{}, ds, ks, img, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs, 11n, xc), 12n, yc), 13n, zc), m, nx, fi, im, pg, lim, inp, 11n, [D.Rt{foc, Bk.Term.Rwt{e, p, b}}], [D.Rt{yc, p}, D.Rt{zc, b}], fs, sp, pend, ps,
    xc, e, Nil{}, zs, hs0, hac, Unit{}, hc11)
  %X.rw.seq(f, X.sel.a(Mc.M.ev.rwt()), X.sel.b(Mc.M.ev.rwt()), S, SX, ex) : D.PostB(False{}, _, s => K.MV.next(ds, ks, img, st0, t, w, s), s => st2 => D.HR(ds, t, s, st2), B, lim)
  %X.rw.seq(f, X.sel.a(X.sel.b(Mc.M.ev.rwt())), X.sel.b(X.sel.b(Mc.M.ev.rwt())), SX, SY, ey) : D.PostB(False{}, _, s => K.MV.next(ds, ks, img, st0, t, w, s), s => st2 => D.HR(ds, t, s, st2), B, lim)
  %X.rw.seq(f, X.sel.a(X.sel.b(X.sel.b(Mc.M.ev.rwt()))), X.sel.b(X.sel.b(X.sel.b(Mc.M.ev.rwt()))), SY, SZ, ez) : D.PostB(False{}, _, s => K.MV.next(ds, ks, img, st0, t, w, s), s => st2 => D.HR(ds, t, s, st2), B, lim)
  D.postb.seq(f, False{}, Mc.M.inc(11n), X.sel.b(X.sel.b(X.sel.b(X.sel.b(Mc.M.ev.rwt())))), SZ, st2 => IncQ(ds, ks, img, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs, 11n, xc), 12n, yc), 13n, zc), m, nx, fi, im, pg, lim, inp, [D.Rt{foc, Bk.Term.Rwt{e, p, b}}], [D.Rt{yc, p}, D.Rt{zc, b}], fs, sp, pend, ps, xc, e, Nil{}, zs, st2), s => K.MV.next(ds, ks, img, st0, t, w, s), s => st2 => Empty, s => st2 => D.HR(ds, t, s, st2), B, lim,
    D.postb.wk(False{}, Cr.Cir.exec(f, Mc.M.inc(11n), SZ), st2 => IncQ(ds, ks, img, List.set(&2, U32, List.set(&2, U32, List.set(&2, U32, regs, 11n, xc), 12n, yc), 13n, zc), m, nx, fi, im, pg, lim, inp, [D.Rt{foc, Bk.Term.Rwt{e, p, b}}], [D.Rt{yc, p}, D.Rt{zc, b}], fs, sp, pend, ps, xc, e, Nil{}, zs, st2), s => st2 => Empty, 0n, B, lim, hi, N.le_zero(B)),
    s => st2 => e2 => Empty.absurd(D.HR(ds, t, s, st2), e2),
    +stA => qi => rwt.incy(f, ds, ks, img, regs, m, nx, fi, im, lim, inp, foc, e, p, b, xc, yc, zc, fs, sp, ps, pg, st0, t, w, B, pend, zs, hroom, hnd, hmc, et2, ew2, afs2, hl, h1, h2, h3, h8, stA, qi))

# the parts of the focus' cell, Rwt
def rwt.x(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +foc: U32, +e: Bk.Term, +p: Bk.Term, +b: Bk.Term, h: D.Is(ds, m, im, fi, nx, ks, img, foc, Bk.Term.Rwt{e, p, b})) -> D.IsK(True{}, ds, m, im, fi, nx, ks, img, D.Fd(2n, m, foc), e):
  match h:
    case Tuple{_, Tuple{Tuple{_, i}, _}}:
      i

def rwt.y(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +foc: U32, +e: Bk.Term, +p: Bk.Term, +b: Bk.Term, h: D.Is(ds, m, im, fi, nx, ks, img, foc, Bk.Term.Rwt{e, p, b})) -> D.IsK(True{}, ds, m, im, fi, nx, ks, img, D.Fd(3n, m, foc), p):
  match h:
    case Tuple{_, Tuple{_, Tuple{Tuple{_, i}, _}}}:
      i

def rwt.z(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +foc: U32, +e: Bk.Term, +p: Bk.Term, +b: Bk.Term, h: D.Is(ds, m, im, fi, nx, ks, img, foc, Bk.Term.Rwt{e, p, b})) -> D.IsK(True{}, ds, m, im, fi, nx, ks, img, D.Fd(4n, m, foc), b):
  match h:
    case Tuple{_, Tuple{_, Tuple{_, Tuple{_, i}}}}:
      i

def rwt.n2(+m: Cr.Cir.Cells, +foc: U32, +e: Bk.Term, +p: Bk.Term, +b: Bk.Term) ->
  {Bool.or(D.Fl(m, D.Fd(2n, m, foc), 1024), D.Nodes([D.Rt{foc, Bk.Term.Rwt{e, p, b}}], m, D.Fd(2n, m, foc))) == True{} : Bool}:
  D.or.r(D.Fl(m, D.Fd(2n, m, foc), 1024), D.Nodes([D.Rt{foc, Bk.Term.Rwt{e, p, b}}], m, D.Fd(2n, m, foc)),
    D.or.l(D.Node(Bk.Term.Rwt{e, p, b}, m, foc, D.Fd(2n, m, foc)), False{}, D.or.r(U32.is_eq(foc, D.Fd(2n, m, foc)), Bool.or(D.Node(e, m, D.Fd(2n, m, foc), D.Fd(2n, m, foc)), Bool.or(D.Node(p, m, D.Fd(3n, m, foc), D.Fd(2n, m, foc)), D.Node(b, m, D.Fd(4n, m, foc), D.Fd(2n, m, foc)))),
      D.or.l(D.Node(e, m, D.Fd(2n, m, foc), D.Fd(2n, m, foc)), Bool.or(D.Node(p, m, D.Fd(3n, m, foc), D.Fd(2n, m, foc)), D.Node(b, m, D.Fd(4n, m, foc), D.Fd(2n, m, foc))), node.self(e, m, D.Fd(2n, m, foc))))))

def rwt.n3(+m: Cr.Cir.Cells, +foc: U32, +e: Bk.Term, +p: Bk.Term, +b: Bk.Term) ->
  {Bool.or(D.Fl(m, D.Fd(3n, m, foc), 1024), D.Nodes([D.Rt{foc, Bk.Term.Rwt{e, p, b}}], m, D.Fd(3n, m, foc))) == True{} : Bool}:
  D.or.r(D.Fl(m, D.Fd(3n, m, foc), 1024), D.Nodes([D.Rt{foc, Bk.Term.Rwt{e, p, b}}], m, D.Fd(3n, m, foc)),
    D.or.l(D.Node(Bk.Term.Rwt{e, p, b}, m, foc, D.Fd(3n, m, foc)), False{}, D.or.r(U32.is_eq(foc, D.Fd(3n, m, foc)), Bool.or(D.Node(e, m, D.Fd(2n, m, foc), D.Fd(3n, m, foc)), Bool.or(D.Node(p, m, D.Fd(3n, m, foc), D.Fd(3n, m, foc)), D.Node(b, m, D.Fd(4n, m, foc), D.Fd(3n, m, foc)))),
      D.or.r(D.Node(e, m, D.Fd(2n, m, foc), D.Fd(3n, m, foc)), Bool.or(D.Node(p, m, D.Fd(3n, m, foc), D.Fd(3n, m, foc)), D.Node(b, m, D.Fd(4n, m, foc), D.Fd(3n, m, foc))), D.or.l(D.Node(p, m, D.Fd(3n, m, foc), D.Fd(3n, m, foc)), D.Node(b, m, D.Fd(4n, m, foc), D.Fd(3n, m, foc)), node.self(p, m, D.Fd(3n, m, foc)))))))

def rwt.n4(+m: Cr.Cir.Cells, +foc: U32, +e: Bk.Term, +p: Bk.Term, +b: Bk.Term) ->
  {Bool.or(D.Fl(m, D.Fd(4n, m, foc), 1024), D.Nodes([D.Rt{foc, Bk.Term.Rwt{e, p, b}}], m, D.Fd(4n, m, foc))) == True{} : Bool}:
  D.or.r(D.Fl(m, D.Fd(4n, m, foc), 1024), D.Nodes([D.Rt{foc, Bk.Term.Rwt{e, p, b}}], m, D.Fd(4n, m, foc)),
    D.or.l(D.Node(Bk.Term.Rwt{e, p, b}, m, foc, D.Fd(4n, m, foc)), False{}, D.or.r(U32.is_eq(foc, D.Fd(4n, m, foc)), Bool.or(D.Node(e, m, D.Fd(2n, m, foc), D.Fd(4n, m, foc)), Bool.or(D.Node(p, m, D.Fd(3n, m, foc), D.Fd(4n, m, foc)), D.Node(b, m, D.Fd(4n, m, foc), D.Fd(4n, m, foc)))),
      D.or.r(D.Node(e, m, D.Fd(2n, m, foc), D.Fd(4n, m, foc)), Bool.or(D.Node(p, m, D.Fd(3n, m, foc), D.Fd(4n, m, foc)), D.Node(b, m, D.Fd(4n, m, foc), D.Fd(4n, m, foc))), D.or.r(D.Node(p, m, D.Fd(3n, m, foc), D.Fd(4n, m, foc)), D.Node(b, m, D.Fd(4n, m, foc), D.Fd(4n, m, foc)), node.self(b, m, D.Fd(4n, m, foc)))))))

# mv.ev.rwt: M.ev's tests reach M.ev.rwt
def rwt.disp(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32, +r4: U32, +r5: U32, +r6: U32, +r7: U32, +r8: U32, +r9: U32, +r10: U32, +r11: U32, +r12: U32, +r13: U32, +r14: U32, +r15: U32, +r16: U32, +r17: U32, +r18: U32, +r19: U32, +r20: U32, +r21: U32, +r22: U32, +r23: U32, +r24: U32, +r25: U32, +r26: U32, +r27: U32, +r28: U32, +r29: U32, +r30: U32, +r31: U32, +r32: U32, +r33: U32, +r34: U32, +r35: U32, +r36: U32, +r37: U32, +r38: U32, +r39: U32, +r40: U32, +r41: U32, +r42: U32, +r43: U32, +r44: U32, +r45: U32, +r46: U32, +r47: U32, +r48: U32, +r49: U32, +r50: U32, +r51: U32, +r52: U32, +r53: U32, +r54: U32, +r55: U32, +r56: U32, +r57: U32, +r58: U32, +r59: U32, +r60: U32, +r61: U32, +r62: U32,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +e: Bk.Term, +p: Bk.Term, +b: Bk.Term,
  +nd: D.Nd(ds, im, fi, nx, foc, Cr.Cir.Cells.get(m, foc), Bk.Term.Rwt{e, p, b}, D.A.tag(Bk.Term.Rwt{e, p, b})), +tb: D.Tbl(m, im, fi, nx),
  +hv: {D.Fl(m, foc, 256) == False{} : Bool}) ->
  {Cr.Cir.exec(f, D.B.body(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)) == Cr.Cir.exec(f, Mc.M.ev.rwt(), K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)) : Cr.Cir.Out}:
  +F = {Bk.Term.Rwt{e, p, b} : Bk.Term}
  Equal.trans(Cr.Cir.Out, Cr.Cir.exec(f, D.B.body(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)), Cr.Cir.exec(f, K.B.else(), K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)), Cr.Cir.exec(f, Mc.M.ev.rwt(), K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)),
    ev.pre.E(f, ds, ks, img, foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp, F, nd, tb, hv, {==}),
    br.rwt(f, K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp), D.Fd(0n, m, foc), nd.tag(ds, im, fi, nx, foc, Cr.Cir.Cells.get(m, foc), F, D.A.tag(F), nd), {==}))

def nw.rwt() -> {NW(Mc.M.ev.rwt()) == True{} : Bool}:
  {==}

# mv.ev.rwt's frame costs less than the focus
def rwt.w(+e: Bk.Term, +p: Bk.Term, +b: Bk.Term, +fs: List<&2, D.AF>, +w: Nat, ew: {D.A.w(False{}, Bk.Term.Rwt{e, p, b}, fs) == w : Nat}) ->
  N.Le(1n+D.A.w(False{}, e, Con{D.AF{D.FK.rwt{}, Bk.Quan.Q0{}, False{}, p, b}, fs}), w):
  %ew : N.Le(1n+D.A.w(False{}, e, Con{D.AF{D.FK.rwt{}, Bk.Quan.Q0{}, False{}, p, b}, fs}), _)
  w.lt(Pg.Term.size(e), Nat.add(Pg.Term.size(p), Pg.Term.size(b)), Pg.Term.size(Bk.Term.Rwt{e, p, b}), D.A.w.frames(fs), 0n, {==},
    N.le_zero(2n+A3(Nat.add(Pg.Term.size(p), Pg.Term.size(b)))))

# mv.ev.rwt: the frame Rwt □ p b pushed, an admin move
def rwt.mv(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32, +pend: U32, +r4: U32, +r5: U32, +r6: U32, +r7: U32, +r8: U32, +r9: U32, +r10: U32, +r11: U32, +r12: U32, +r13: U32, +r14: U32, +r15: U32, +r16: U32, +r17: U32, +r18: U32, +r19: U32, +r20: U32, +r21: U32, +r22: U32, +r23: U32, +r24: U32, +r25: U32, +r26: U32, +r27: U32, +r28: U32, +r29: U32, +r30: U32, +r31: U32, +r32: U32, +r33: U32, +r34: U32, +r35: U32, +r36: U32, +r37: U32, +r38: U32, +r39: U32, +r40: U32, +r41: U32, +r42: U32, +r43: U32, +r44: U32, +r45: U32, +r46: U32, +r47: U32, +r48: U32, +r49: U32, +r50: U32, +r51: U32, +r52: U32, +r53: U32, +r54: U32, +r55: U32, +r56: U32, +r57: U32, +r58: U32, +r59: U32, +r60: U32, +r61: U32, +r62: U32,
  +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat, +fs: List<&2, D.AF>,
  +ps: List<&2, U32>, +e: Bk.Term, +p: Bk.Term, +b: Bk.Term, +et: {D.A.plugs(fs, Bk.Term.Rwt{e, p, b}) == t : Bk.Term}, +ew: {D.A.w(False{}, Bk.Term.Rwt{e, p, b}, fs) == w : Nat},
  +afs: D.AFs.ok(ds, fs), +isf: D.Is(ds, m, im, fi, nx, ks, img, foc, Bk.Term.Rwt{e, p, b}), +frs: D.Frs(ds, m, im, fi, nx, ks, img, ps, sp, fs),
  +hp: D.Heap(m, nx, fi, im, [foc], pend, ps), +io: D.ImgOK(ds, ks, img, m, im, fi, nx), +zs: List<&2, D.Rt>,
  +hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, [D.Rt{foc, Bk.Term.Rwt{e, p, b}}], Nil{}, sp, fs, ps, zs), +hv: {D.Fl(m, foc, 256) == False{} : Bool}) ->
  D.PostB(False{}, Cr.Cir.exec(f, D.B.body(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)), s => K.MV.next(ds, ks, img, D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), t, w, s), s => st2 => D.HR(ds, t, s, st2), D.Budget(ds, D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp))):
  +F = {Bk.Term.Rwt{e, p, b} : Bk.Term}
  +nd = D.is.nd(ds, m, im, fi, nx, ks, img, foc, F, isf)
  +tb = K.img.tbl(ds, ks, img, m, im, fi, nx, io)
  %Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, D.B.body(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)), Cr.Cir.exec(f, Mc.M.ev.rwt(), K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)),
    rwt.disp(f, ds, ks, img, foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp, e, p, b, nd, tb, hv)) :
    D.PostB(False{}, _, s => K.MV.next(ds, ks, img, D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), t, w, s), s => st2 => D.HR(ds, t, s, st2), D.Budget(ds, D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)))
  rwt.run(f, ds, ks, img, D.St.regs(K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)), m, nx, fi, im, lim, inp, foc, e, p, b, D.Fd(2n, m, foc), D.Fd(3n, m, foc), D.Fd(4n, m, foc), fs, sp, ps,
    pg, D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), t, w, D.Budget(ds, D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), t), pend, zs,
    room.of(ds, ks, img, D.RG(foc, 0, sp, pend, D.R59.list(D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62})), m, nx, fi, im, pg, lim, inp, foc, F, sp, fs, ps, pend, zs, t, et, hac, hp),
    e2 => need.of(ds, ks, img, D.RG(foc, 0, sp, pend, D.R59.list(D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62})), m, nx, fi, im, pg, lim, inp, foc, F, sp, fs, ps, zs, t, et, hac, e2), {==}, et,
    rwt.w(e, p, b, fs, w, ew), (Unit{}, afs), {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==},
    nd.cell(ds, im, fi, nx, foc, Cr.Cir.Cells.get(m, foc), F, D.A.tag(F), nd),
    ((isf, Unit{}), ((rwt.x(ds, ks, img, m, nx, fi, im, foc, e, p, b, isf), (rwt.y(ds, ks, img, m, nx, fi, im, foc, e, p, b, isf),
      (rwt.z(ds, ks, img, m, nx, fi, im, foc, e, p, b, isf), Unit{}))), ((rwt.n2(m, foc, e, p, b), (rwt.n3(m, foc, e, p, b), (rwt.n4(m, foc, e, p, b), Unit{}))),
      (frs, (hp, io))))), hac)


# The moves to mode 1
# -------------------

# a round from mode 0 whose focus' cell passes M.ev's test of a value: mode 1,
# with the same cells, an admin move
def val.mv(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +sp: U32,
  +pend: U32, +r4: U32, +r5: U32, +r6: U32, +r7: U32, +r8: U32, +r9: U32, +r10: U32, +r11: U32, +r12: U32, +r13: U32, +r14: U32, +r15: U32, +r16: U32, +r17: U32, +r18: U32, +r19: U32, +r20: U32, +r21: U32, +r22: U32, +r23: U32, +r24: U32, +r25: U32, +r26: U32, +r27: U32, +r28: U32, +r29: U32, +r30: U32, +r31: U32, +r32: U32, +r33: U32, +r34: U32, +r35: U32, +r36: U32, +r37: U32, +r38: U32, +r39: U32, +r40: U32, +r41: U32, +r42: U32, +r43: U32, +r44: U32, +r45: U32, +r46: U32, +r47: U32, +r48: U32, +r49: U32, +r50: U32, +r51: U32, +r52: U32, +r53: U32, +r54: U32, +r55: U32, +r56: U32, +r57: U32, +r58: U32, +r59: U32, +r60: U32, +r61: U32, +r62: U32, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32,
  +inp: List<&2, Word(8n)>, +t: Bk.Term, +w: Nat, +fs: List<&2, D.AF>, +ps: List<&2, U32>, +focus: Bk.Term,
  +et: {D.A.plugs(fs, focus) == t : Bk.Term}, ew: {D.A.w(False{}, focus, fs) == w : Nat}, +afs: D.AFs.ok(ds, fs),
  +isf: D.Is(ds, m, im, fi, nx, ks, img, foc, focus), +frs: D.Frs(ds, m, im, fi, nx, ks, img, ps, sp, fs),
  +hp: D.Heap(m, nx, fi, im, [foc], pend, ps), +io: D.ImgOK(ds, ks, img, m, im, fi, nx), +zs: List<&2, D.Rt>,
  +hac: D.AccK(True{}, ds, ks, img, m, nx, fi, im, [D.Rt{foc, focus}], Nil{}, sp, fs, ps, zs),
  +nz2: {U32.is_zero(U32.or(Bool.to_u32(U32.is_ne(U32.and(D.Fd(0n, m, foc), 256), 0)), Bool.to_u32(U32.is_ne(Cr.Cir.Cell.get(4n, Cr.Cir.Cells.get(m, U32.add(272, U32.and(D.Fd(0n, m, foc), 63)))), 0)))) == False{} : Bool},
  +evv: {Bool.or(Bool.not(True{}), El.Eval.vals(ds, focus, False{})) == True{} : Bool}) ->
  K.MV(ds, ks, img, D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), t, w):
  +nd = D.is.nd(ds, m, im, fi, nx, ks, img, foc, focus, isf)
  +tb = K.img.tbl(ds, ks, img, m, im, fi, nx, io)
  +w2 = D.A.w(True{}, focus, fs)
  +inv3 = {(D.Wit{True{}, focus, fs, foc, sp, pend, ps, D.R59.of(D.St.regs(D.St.set(K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp), 1n, 1)))},
    ((et, ({==}, (evv, (afs, ({==}, (isf, (frs, (hp, (io, ({==}, {==})))))))))), (zs, hac))) : D.Inv(ds, ks, img, D.St.set(K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp), 1n, 1), t, w2)}
  +lt = K.ret.lt(focus, fs, w, ew)
  mv = {(Inl{(w2, (inv3, lt))}, le.peak(ds, D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), t)) : K.MV.next(ds, ks, img, D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), t, w, D.St.set(K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp), 1n, 1))}
  (f => (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, D.B.body(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)), Cr.Cir.Out.next{D.St.set(K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp), 1n, 1)},
      K.ev.val.E(f, ds, ks, img, foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp, focus, nd, tb, nz2)) :
      D.PostB(False{}, _, s => K.MV.next(ds, ks, img, D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), t, w, s), s => st2 => D.HR(ds, t, s, st2), D.Budget(ds, D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)));
      mv),
   (0n, (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec(0n, D.B.body(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)), Cr.Cir.Out.next{D.St.set(K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp), 1n, 1)},
      K.ev.val.E(0n, ds, ks, img, foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp, focus, nd, tb, nz2)) : D.Ends(_);
      Unit{})))

def K.mv.ev.val(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, focus, iv, hv):
  match rest:
    case D.R59{+r4, +r5, +r6, +r7, +r8, +r9, +r10, +r11, +r12, +r13, +r14, +r15, +r16, +r17, +r18, +r19, +r20, +r21, +r22, +r23, +r24, +r25, +r26, +r27, +r28, +r29, +r30, +r31, +r32, +r33, +r34, +r35, +r36, +r37, +r38, +r39, +r40, +r41, +r42, +r43, +r44, +r45, +r46, +r47, +r48, +r49, +r50, +r51, +r52, +r53, +r54, +r55, +r56, +r57, +r58, +r59, +r60, +r61, +r62}:
      match iv:
        case Tuple{Tuple{+et, Tuple{+ew, Tuple{_, Tuple{+afs, Tuple{_, Tuple{+isf, Tuple{+frs, Tuple{+hp, Tuple{+io, Tuple{_, _}}}}}}}}}}, Tuple{+zs, +hac}}:
          +nd = D.is.nd(ds, m, im, fi, nx, ks, img, foc, focus, isf)
          val.mv(ds, ks, img, foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, focus, et, ew, afs, isf, frs, hp, io, zs, hac,
            K.nz.of(D.Fd(0n, m, foc), Cr.Cir.Cell.get(4n, Cr.Cir.Cells.get(m, U32.add(272, U32.and(D.Fd(0n, m, foc), 63)))), hv),
            K.nd.val(ds, im, fi, nx, foc, Cr.Cir.Cells.get(m, foc), focus, D.A.tag(focus), nd, hv))

def K.mv.ev.former(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, focus, iv, hf):
  match rest:
    case D.R59{+r4, +r5, +r6, +r7, +r8, +r9, +r10, +r11, +r12, +r13, +r14, +r15, +r16, +r17, +r18, +r19, +r20, +r21, +r22, +r23, +r24, +r25, +r26, +r27, +r28, +r29, +r30, +r31, +r32, +r33, +r34, +r35, +r36, +r37, +r38, +r39, +r40, +r41, +r42, +r43, +r44, +r45, +r46, +r47, +r48, +r49, +r50, +r51, +r52, +r53, +r54, +r55, +r56, +r57, +r58, +r59, +r60, +r61, +r62}:
      match iv:
        case Tuple{Tuple{+et, Tuple{+ew, Tuple{_, Tuple{+afs, Tuple{_, Tuple{+isf, Tuple{+frs, Tuple{+hp, Tuple{+io, Tuple{_, _}}}}}}}}}}, Tuple{+zs, +hac}}:
          +nd = D.is.nd(ds, m, im, fi, nx, ks, img, foc, focus, isf)
          val.mv(ds, ks, img, foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, focus, et, ew, afs, isf, frs, hp, io, zs, hac,
            K.nzf.go(ds, im, fi, nx, foc, m, focus, nd, K.img.tbl(ds, ks, img, m, im, fi, nx, io), hf), K.tbl.vals(ds, focus, hf))

def K.mv.ev.var(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, i, iv, hv):
  match rest:
    case D.R59{+r4, +r5, +r6, +r7, +r8, +r9, +r10, +r11, +r12, +r13, +r14, +r15, +r16, +r17, +r18, +r19, +r20, +r21, +r22, +r23, +r24, +r25, +r26, +r27, +r28, +r29, +r30, +r31, +r32, +r33, +r34, +r35, +r36, +r37, +r38, +r39, +r40, +r41, +r42, +r43, +r44, +r45, +r46, +r47, +r48, +r49, +r50, +r51, +r52, +r53, +r54, +r55, +r56, +r57, +r58, +r59, +r60, +r61, +r62}:
      match iv:
        case Tuple{Tuple{+et, Tuple{_, Tuple{_, Tuple{+afs, Tuple{_, Tuple{+isf, Tuple{_, Tuple{_, Tuple{+io, Tuple{_, _}}}}}}}}}}, _}:
          +nd = D.is.nd(ds, m, im, fi, nx, ks, img, foc, Bk.Term.Var{i}, isf)
          +tb = K.img.tbl(ds, ks, img, m, im, fi, nx, io)
          hr = K.hr.eq(ds, D.A.plugs(fs, Bk.Term.Var{i}), t, 2, K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp), et,
            K.hr.stuck(ds, D.A.plugs(fs, Bk.Term.Var{i}), K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp), K.ev.stuck(ds, fs, Bk.Term.Var{i}, afs, {==}, {==})))
          (f => (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, D.B.body(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)), Cr.Cir.Out.halt{2, K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)},
              K.ev.var.E(f, ds, ks, img, foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp, i, nd, tb, hv)) :
              D.PostB(False{}, _, s => K.MV.next(ds, ks, img, D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), t, w, s), s => st2 => D.HR(ds, t, s, st2), D.Budget(ds, D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)));
              hr),
           (0n, (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec(0n, D.B.body(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)), Cr.Cir.Out.halt{2, K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)},
              K.ev.var.E(0n, ds, ks, img, foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp, i, nd, tb, hv)) : D.Ends(_);
              Unit{})))

# The moves that push a frame
# ---------------------------

def K.mv.ev.let(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, g, x, iv, hv, hq):
  match rest:
    case D.R59{+r4, +r5, +r6, +r7, +r8, +r9, +r10, +r11, +r12, +r13, +r14, +r15, +r16, +r17, +r18, +r19, +r20, +r21, +r22, +r23, +r24, +r25, +r26, +r27, +r28, +r29, +r30, +r31, +r32, +r33, +r34, +r35, +r36, +r37, +r38, +r39, +r40, +r41, +r42, +r43, +r44, +r45, +r46, +r47, +r48, +r49, +r50, +r51, +r52, +r53, +r54, +r55, +r56, +r57, +r58, +r59, +r60, +r61, +r62}:
      match iv:
        case Tuple{Tuple{+et, Tuple{+ew, Tuple{_, Tuple{+afs, Tuple{_, Tuple{+isf, Tuple{+frs, Tuple{+hp, Tuple{+io, Tuple{_, _}}}}}}}}}}, Tuple{+zs, +hac}}:
          +F = {Bk.Term.Let{q, g, x} : Bk.Term}
          (f => let.mv(f, ds, ks, img, foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, g, x, et, ew, afs, isf, frs, hp, io, zs, hac, hv, hq),
           (0n, (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec(0n, D.B.body(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)), Cr.Cir.exec(0n, K.stmt.then(Mc.M.ev.let()), K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)),
              let.disp(0n, ds, ks, img, foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp, q, g, x, D.is.nd(ds, m, im, fi, nx, ks, img, foc, F, isf),
                K.img.tbl(ds, ks, img, m, im, fi, nx, io), hv, hq, let.qs(ds, ks, img, m, nx, fi, im, foc, q, g, x, isf))) : D.Ends(_);
              ends.nw(0n, K.stmt.then(Mc.M.ev.let()), K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp), nw.let()))))

def K.mv.ev.app(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, g, x, iv, hv):
  match rest:
    case D.R59{+r4, +r5, +r6, +r7, +r8, +r9, +r10, +r11, +r12, +r13, +r14, +r15, +r16, +r17, +r18, +r19, +r20, +r21, +r22, +r23, +r24, +r25, +r26, +r27, +r28, +r29, +r30, +r31, +r32, +r33, +r34, +r35, +r36, +r37, +r38, +r39, +r40, +r41, +r42, +r43, +r44, +r45, +r46, +r47, +r48, +r49, +r50, +r51, +r52, +r53, +r54, +r55, +r56, +r57, +r58, +r59, +r60, +r61, +r62}:
      match iv:
        case Tuple{Tuple{+et, Tuple{+ew, Tuple{_, Tuple{+afs, Tuple{_, Tuple{+isf, Tuple{+frs, Tuple{+hp, Tuple{+io, Tuple{_, _}}}}}}}}}}, Tuple{+zs, +hac}}:
          +F = {Bk.Term.App{q, g, x} : Bk.Term}
          (f => app.mv(f, ds, ks, img, foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, g, x, et, ew, afs, isf, frs, hp, io, zs, hac, hv),
           (0n, (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec(0n, D.B.body(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)), Cr.Cir.exec(0n, Mc.M.ev.app(), K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)),
              app.disp(0n, ds, ks, img, foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp, q, g, x, D.is.nd(ds, m, im, fi, nx, ks, img, foc, F, isf),
                K.img.tbl(ds, ks, img, m, im, fi, nx, io), hv)) : D.Ends(_);
              ends.nw(0n, Mc.M.ev.app(), K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp), nw.app()))))

def K.mv.ev.tup(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, g, x, iv, hv, hq):
  match rest:
    case D.R59{+r4, +r5, +r6, +r7, +r8, +r9, +r10, +r11, +r12, +r13, +r14, +r15, +r16, +r17, +r18, +r19, +r20, +r21, +r22, +r23, +r24, +r25, +r26, +r27, +r28, +r29, +r30, +r31, +r32, +r33, +r34, +r35, +r36, +r37, +r38, +r39, +r40, +r41, +r42, +r43, +r44, +r45, +r46, +r47, +r48, +r49, +r50, +r51, +r52, +r53, +r54, +r55, +r56, +r57, +r58, +r59, +r60, +r61, +r62}:
      match iv:
        case Tuple{Tuple{+et, Tuple{+ew, Tuple{_, Tuple{+afs, Tuple{_, Tuple{+isf, Tuple{+frs, Tuple{+hp, Tuple{+io, Tuple{_, _}}}}}}}}}}, Tuple{+zs, +hac}}:
          +F = {Bk.Term.Tup{q, g, x} : Bk.Term}
          (f => tup.mv(f, ds, ks, img, foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, g, x, et, ew, afs, isf, frs, hp, io, zs, hac, hv, hq),
           (0n, (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec(0n, D.B.body(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)), Cr.Cir.exec(0n, K.stmt.then(Mc.M.ev.tup()), K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)),
              tup.disp(0n, ds, ks, img, foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp, q, g, x, D.is.nd(ds, m, im, fi, nx, ks, img, foc, F, isf),
                K.img.tbl(ds, ks, img, m, im, fi, nx, io), hv, hq, tup.qs(ds, ks, img, m, nx, fi, im, foc, q, g, x, isf))) : D.Ends(_);
              ends.nw(0n, K.stmt.then(Mc.M.ev.tup()), K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp), nw.tup()))))

def K.mv.ev.tup0(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, g, x, iv, hv, hq):
  match rest:
    case D.R59{+r4, +r5, +r6, +r7, +r8, +r9, +r10, +r11, +r12, +r13, +r14, +r15, +r16, +r17, +r18, +r19, +r20, +r21, +r22, +r23, +r24, +r25, +r26, +r27, +r28, +r29, +r30, +r31, +r32, +r33, +r34, +r35, +r36, +r37, +r38, +r39, +r40, +r41, +r42, +r43, +r44, +r45, +r46, +r47, +r48, +r49, +r50, +r51, +r52, +r53, +r54, +r55, +r56, +r57, +r58, +r59, +r60, +r61, +r62}:
      match iv:
        case Tuple{Tuple{+et, Tuple{+ew, Tuple{_, Tuple{+afs, Tuple{_, Tuple{+isf, Tuple{+frs, Tuple{+hp, Tuple{+io, Tuple{_, _}}}}}}}}}}, Tuple{+zs, +hac}}:
          +F = {Bk.Term.Tup{q, g, x} : Bk.Term}
          (f => tup0.mv(f, ds, ks, img, foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, g, x, et, ew, afs, isf, frs, hp, io, zs, hac, hv, hq),
           (0n, (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec(0n, D.B.body(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)), Cr.Cir.exec(0n, K.stmt.else(Mc.M.ev.tup()), K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)),
              tup0.disp(0n, ds, ks, img, foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp, q, g, x, D.is.nd(ds, m, im, fi, nx, ks, img, foc, F, isf),
                K.img.tbl(ds, ks, img, m, im, fi, nx, io), hv, hq, tup.qs(ds, ks, img, m, nx, fi, im, foc, q, g, x, isf))) : D.Ends(_);
              ends.nw(0n, K.stmt.else(Mc.M.ev.tup()), K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp), nw.tup0()))))

def K.mv.ev.rwt(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, e, p, b, iv, hv):
  match rest:
    case D.R59{+r4, +r5, +r6, +r7, +r8, +r9, +r10, +r11, +r12, +r13, +r14, +r15, +r16, +r17, +r18, +r19, +r20, +r21, +r22, +r23, +r24, +r25, +r26, +r27, +r28, +r29, +r30, +r31, +r32, +r33, +r34, +r35, +r36, +r37, +r38, +r39, +r40, +r41, +r42, +r43, +r44, +r45, +r46, +r47, +r48, +r49, +r50, +r51, +r52, +r53, +r54, +r55, +r56, +r57, +r58, +r59, +r60, +r61, +r62}:
      match iv:
        case Tuple{Tuple{+et, Tuple{+ew, Tuple{_, Tuple{+afs, Tuple{_, Tuple{+isf, Tuple{+frs, Tuple{+hp, Tuple{+io, Tuple{_, _}}}}}}}}}}, Tuple{+zs, +hac}}:
          +F = {Bk.Term.Rwt{e, p, b} : Bk.Term}
          (f => rwt.mv(f, ds, ks, img, foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, e, p, b, et, ew, afs, isf, frs, hp, io, zs, hac, hv),
           (0n, (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec(0n, D.B.body(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)), Cr.Cir.exec(0n, Mc.M.ev.rwt(), K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)),
              rwt.disp(0n, ds, ks, img, foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp, e, p, b, D.is.nd(ds, m, im, fi, nx, ks, img, foc, F, isf),
                K.img.tbl(ds, ks, img, m, im, fi, nx, io), hv)) : D.Ends(_);
              ends.nw(0n, Mc.M.ev.rwt(), K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp), nw.rwt()))))

def K.mv.ev.min(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, g, x, iv, hv):
  match rest:
    case D.R59{+r4, +r5, +r6, +r7, +r8, +r9, +r10, +r11, +r12, +r13, +r14, +r15, +r16, +r17, +r18, +r19, +r20, +r21, +r22, +r23, +r24, +r25, +r26, +r27, +r28, +r29, +r30, +r31, +r32, +r33, +r34, +r35, +r36, +r37, +r38, +r39, +r40, +r41, +r42, +r43, +r44, +r45, +r46, +r47, +r48, +r49, +r50, +r51, +r52, +r53, +r54, +r55, +r56, +r57, +r58, +r59, +r60, +r61, +r62}:
      match iv:
        case Tuple{Tuple{+et, Tuple{+ew, Tuple{_, Tuple{+afs, Tuple{_, Tuple{+isf, Tuple{+frs, Tuple{+hp, Tuple{+io, Tuple{_, _}}}}}}}}}}, Tuple{+zs, +hac}}:
          +F = {Bk.Term.Min{g, x} : Bk.Term}
          (f => min.mv(f, ds, ks, img, foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, g, x, et, ew, afs, isf, frs, hp, io, zs, hac, hv),
           (0n, (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec(0n, D.B.body(), D.S(foc, 0, sp, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)), Cr.Cir.exec(0n, Mc.M.ev.min(), K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)),
              min.disp(0n, ds, ks, img, foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp, g, x, D.is.nd(ds, m, im, fi, nx, ks, img, foc, F, isf),
                K.img.tbl(ds, ks, img, m, im, fi, nx, io), hv)) : D.Ends(_);
              ends.nw(0n, Mc.M.ev.min(), K.ev.st2(foc, sp, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp), nw.min()))))
