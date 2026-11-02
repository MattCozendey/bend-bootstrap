# compiler: layer B, the moves that push a frame, and the moves to mode 1 (U10)
# =============================================================================
#
# mv.ev.val, mv.ev.former, mv.ev.var (mode 1, or a halt), and mv.ev.app, mv.ev.let, mv.ev.tup,
# mv.ev.tup0, mv.ev.rwt, mv.ev.min (a frame pushed, an admin move) of move_kit.bend.

import Base
import ../../Book/impl.bend as Bk
import ../../Eval/impl.bend as El
import ../../Wasm/impl.bend as Wa
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

# Fr.rts.b of a frame's cell is UB of its field 3
def ub.rts(kind: D.FK, +m: Cr.Cir.Cells, +z: U32, +vb: Bk.Term) ->
  {D.Fr.rts.b(m, z, kind, vb) == UB(kind, D.Fd(3n, m, z), vb) : List<&2, D.Rt>}:
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

def ne.gt.b(b: Bool, +o: U32, +z: U32, eb: {U32.is_eq(o, z) == b : Bool}, h: N.Le(1n+U32.to_nat(o), U32.to_nat(z))) ->
  {U32.is_eq(o, z) == False{} : Bool}:
  match b:
    case False{}:
      eb
    case True{}:
      +e = D.u32.eq(o, z, eb)
      Empty.absurd({U32.is_eq(o, z) == False{} : Bool}, N.not_succ_le(U32.to_nat(z), (%e : N.Le(1n+U32.to_nat(_), U32.to_nat(z)); h)))

# a cell before z is not z
def ne.gt(+o: U32, +z: U32, h: N.Le(1n+U32.to_nat(o), U32.to_nat(z))) -> {U32.is_eq(o, z) == False{} : Bool}:
  ne.gt.b(U32.is_eq(o, z), o, z, {==}, h)

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

# a cell is not next (the machine's cells are from fi to nx, the image's below fi)
def cell.ne.nx(+c: U32, +im: U32, +fi: U32, +nx: U32, hc: {Cr.Cir.is_cell(c, im, fi, nx) == True{} : Bool},
  him: {U32.is_lt(im, fi) == True{} : Bool}, hfn: {U32.is_le(fi, nx) == True{} : Bool}) -> {U32.is_eq(c, nx) == False{} : Bool}:
  D.or.cases(Bool.and(Bool.not(U32.is_zero(c)), U32.is_le(c, im)), Bool.and(U32.is_le(fi, c), U32.is_lt(c, nx)),
    {U32.is_eq(c, nx) == False{} : Bool}, hc,
    e => ne.gt(c, nx, N.le_trans(1n+U32.to_nat(c), U32.to_nat(fi), U32.to_nat(nx),
      N.le_trans(1n+U32.to_nat(c), 1n+U32.to_nat(im), U32.to_nat(fi),
        D.u.le(c, im, D.and.r(Bool.not(U32.is_zero(c)), U32.is_le(c, im), e)), D.u.lt(im, fi, him)), D.u.le(fi, nx, hfn))),
    e => ne.gt(c, nx, D.u.lt(c, nx, D.and.r(U32.is_le(fi, c), U32.is_lt(c, nx), e))))

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

# Cell.set of field 1 keeps field 0
def cell.f0(c: Cr.Cir.Cell, +v: U32) -> {Cr.Cir.Cell.get(0n, Cr.Cir.Cell.set(1n, c, v)) == Cr.Cir.Cell.get(0n, c) : U32}:
  match c:
    case Cr.Cir.Cell{_, _, _, _, _}:
      {==}

# a cell stays a cell when next grows
def cell.grow(+c: U32, +im: U32, +fi: U32, +nx: U32, +nx2: U32, hc: {Cr.Cir.is_cell(c, im, fi, nx) == True{} : Bool},
  hle: {U32.is_le(nx, nx2) == True{} : Bool}) -> {Cr.Cir.is_cell(c, im, fi, nx2) == True{} : Bool}:
  D.or.cases(Bool.and(Bool.not(U32.is_zero(c)), U32.is_le(c, im)), Bool.and(U32.is_le(fi, c), U32.is_lt(c, nx)),
    {Cr.Cir.is_cell(c, im, fi, nx2) == True{} : Bool}, hc,
    e => D.or.l(Bool.and(Bool.not(U32.is_zero(c)), U32.is_le(c, im)), Bool.and(U32.is_le(fi, c), U32.is_lt(c, nx2)), e),
    +e => D.or.r(Bool.and(Bool.not(U32.is_zero(c)), U32.is_le(c, im)), Bool.and(U32.is_le(fi, c), U32.is_lt(c, nx2)),
      D.and.i(U32.is_le(fi, c), U32.is_lt(c, nx2), D.and.l(U32.is_le(fi, c), U32.is_lt(c, nx), e),
        u.lt_t(c, nx2, N.le_trans(1n+U32.to_nat(c), U32.to_nat(nx), U32.to_nat(nx2),
          D.u.lt(c, nx, D.and.r(U32.is_le(fi, c), U32.is_lt(c, nx), e)), D.u.le(nx, nx2, hle))))))

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

# the field 0 of a cell that M.alloc keeps
def keep.f0(+m: Cr.Cir.Cells, +m1: Cr.Cir.Cells, +ps: List<&2, U32>, +foc: U32,
  h: D.P2({Cr.Cir.Cells.get(m1, foc) == Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, foc), D.Fd(1n, m1, foc)) : Cr.Cir.Cell},
    {Bool.or(Bool.and(U32.is_lt(D.Tg(m, foc), 19), D.Taken(ps, m, foc)), U32.is_eq(D.Fd(1n, m1, foc), D.Fd(1n, m, foc))) == True{} : Bool})) ->
  {D.Fd(0n, m1, foc) == D.Fd(0n, m, foc) : U32}:
  match h:
    case Tuple{e, _}:
      Equal.trans(U32, D.Fd(0n, m1, foc), Cr.Cir.Cell.get(0n, Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, foc), D.Fd(1n, m1, foc))), D.Fd(0n, m, foc),
        Equal.cong(Cr.Cir.Cell, U32, c => Cr.Cir.Cell.get(0n, c), Cr.Cir.Cells.get(m1, foc),
          Cr.Cir.Cell.set(1n, Cr.Cir.Cells.get(m, foc), D.Fd(1n, m1, foc)), e),
        cell.f0(Cr.Cir.Cells.get(m, foc), D.Fd(1n, m1, foc)))

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
    {D.Fd(0n, m2, foc) == D.Fd(0n, m, foc) : U32} -> {Cr.Cir.is_cell(foc, im, fi, nx2) == True{} : Bool} ->
    {Cr.Cir.eval(hexp, Cr.Cir.State{regs2, m2, nx2, fi, im, pg2, lim, inp, Nil{}, 0}) == Some{hv} : Maybe<&2, U32>},
  eb: @regs2: List<&2, U32> -> @m2: Cr.Cir.Cells -> @nx2: U32 -> @pg2: U32 -> {List.get(&2, U32, regs2, 13n) == List.get(&2, U32, regs, 13n) : Maybe<&2, U32>} ->
    {Cr.Cir.eval(bexp, Cr.Cir.State{regs2, m2, nx2, fi, im, pg2, lim, inp, Nil{}, 0}) == Some{bv} : Maybe<&2, U32>},
  +htg: {D.TgW(hv) == D.FK.tag(kind) : U32}, +hrest: D.P2({D.QnW(hv) == Mc.Img.quan(q) : U32},
    D.P2({D.FlW(hv, 1024) == False{} : Bool}, {D.FlW(hv, 2048) == False{} : Bool})),
  +hfoc: {Cr.Cir.is_cell(foc, im, fi, nx) == True{} : Bool}, +hnp: {D.Mem(ps, foc) == False{} : Bool},
  +hfn: {U32.is_eq(foc, nx) == False{} : Bool}, +st1: Cr.Cir.State,
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
  +hle: {U32.is_le(nx, D.St.next(st1)) == True{} : Bool}, +hf0: {D.Fd(0n, D.St.cells(st1), foc) == D.Fd(0n, m, foc) : U32}) ->
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
          +ehv = eh(regs1, m1, nx1, pg1, h8b, hf0, cell.grow(foc, im, fi, nx, nx1, hfoc, hle))
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
    {D.Fd(0n, m2, foc) == D.Fd(0n, m, foc) : U32} -> {Cr.Cir.is_cell(foc, im, fi, nx2) == True{} : Bool} ->
    {Cr.Cir.eval(hexp, Cr.Cir.State{regs2, m2, nx2, fi, im, pg2, lim, inp, Nil{}, 0}) == Some{hv} : Maybe<&2, U32>},
  eb: @regs2: List<&2, U32> -> @m2: Cr.Cir.Cells -> @nx2: U32 -> @pg2: U32 -> {List.get(&2, U32, regs2, 13n) == List.get(&2, U32, regs, 13n) : Maybe<&2, U32>} ->
    {Cr.Cir.eval(bexp, Cr.Cir.State{regs2, m2, nx2, fi, im, pg2, lim, inp, Nil{}, 0}) == Some{bv} : Maybe<&2, U32>},
  +hok: HdOK(hv, kind, q), +hfoc: {Cr.Cir.is_cell(foc, im, fi, nx) == True{} : Bool}, +hnp: {D.Mem(ps, foc) == False{} : Bool},
  +hfn: {U32.is_eq(foc, nx) == False{} : Bool}, +st1: Cr.Cir.State, qa: AlQ(ds, ks, img, regs, m, nx, fi, im, lim, inp, foc, F, xc, vf, yc, va, bv, vb, kind, q, hv, fs, sp, ps, st1)) ->
  D.PostB(False{}, Cr.Cir.exec(f, X.sel.b(Mc.M.push(hexp, Mc.M.g(Mc.R.y()), bexp)), st1), st3 => PushQ(ds, ks, img, regs, m, nx, fi, im, lim, inp, foc, F, xc, vf, yc, va, bv, vb, kind, q, hv, fs, sp, ps, st3), s => st2 => Empty, B, lim):
  match hok:
    case Tuple{+htg, hrest}:
      match qa:
        case Tuple{Tuple{+hsame, Tuple{+z, Tuple{+pend2, Tuple{+ps2, Tuple{+h16, Tuple{+h3b, Tuple{+hzero, Tuple{+hown, Tuple{+hmz, Tuple{_, Tuple{+hnx, Tuple{_, Tuple{_, Tuple{+hptr, Tuple{Tuple{+s1, Tuple{+s2, Tuple{+s3, Tuple{+s4, Tuple{+s5, io}}}}}, Tuple{+zs2, hac2}}}}}}}}}}}}}}}}, Tuple{+hle, hfr}}:
          push.k2(f, ds, ks, img, regs, m, nx, fi, im, lim, inp, foc, F, xc, vf, yc, va, bv, vb, kind, q, hv, fs, sp, ps, hexp, bexp, B, h8, h2, h12, eh, eb, htg, hrest, hfoc, hnp, hfn, st1, same.parts(regs, fi, im, lim, inp, [1n, 2n, 8n, 11n, 12n, 13n], st1, hsame), hsame,
            z, pend2, ps2, h16, h3b, hzero, hown, hmz, hnx, hptr, s1, s2, s3, s4, s5, io, zs2, hac2, hle, keep.f0(m, D.St.cells(st1), ps, foc, hfr(foc, hnp, hfn)))


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

def K.mv.ev.let(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, v, b, iv, hv, hq):
  ?TODO

def K.mv.ev.app(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, g, x, iv, hv):
  ?TODO

def K.mv.ev.tup(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, a, b, iv, hv, hq):
  ?TODO

def K.mv.ev.tup0(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, q, a, b, iv, hv, hq):
  ?TODO

def K.mv.ev.rwt(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, e, p, b, iv, hv):
  ?TODO

def K.mv.ev.min(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, a, b, iv, hv):
  ?TODO
