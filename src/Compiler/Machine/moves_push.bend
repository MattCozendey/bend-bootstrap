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

# Runs that end, runs with no new cell
# ------------------------------------
#
# A statement with no while ends with any fuel (NW, ends.nw); one with no
# alloc, no emit and no while never runs out of memory (NA, noom.na).

def NW(s: Cr.Cir.Stmt) -> Bool:
  match s:
    case Cr.Cir.Stmt.seq{a, b}:
      Bool.and(NW(a), NW(b))
    case Cr.Cir.Stmt.if{_, a, b}:
      Bool.and(NW(a), NW(b))
    case Cr.Cir.Stmt.while{_, _}:
      False{}
    case Cr.Cir.Stmt.emit{_}:
      False{}
    case _:
      True{}

def NA(s: Cr.Cir.Stmt) -> Bool:
  match s:
    case Cr.Cir.Stmt.seq{a, b}:
      Bool.and(NA(a), NA(b))
    case Cr.Cir.Stmt.if{_, a, b}:
      Bool.and(NA(a), NA(b))
    case Cr.Cir.Stmt.while{_, _}:
      False{}
    case Cr.Cir.Stmt.emit{_}:
      False{}
    case Cr.Cir.Stmt.alloc{_}:
      False{}
    case _:
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
