import Base
import ../../Shared/shared.bend as Sd
import ../../Book/impl.bend as Bk
import ../../Eval/impl.bend as El
import ../../Wasm/impl.bend as Wa
import ../../Program/impl.bend as Pg
import ../Cir/impl.bend as Cr

# Machine
# =======
#
# The machine, as a Cir program: Mach.code. A term is a graph of cells;
# a cell never changes after it is made, but for the flags that say what is
# known of it. Field 0 holds its tag (bits 0 to 5: the kernel's order of
# formers, Var 0 to Rwt 18; 32 and above for the machine's own cells), its
# quantity (bits 6 and 7), its flags (VALUE, DATA, STATIC, K, OWNED: bits 8
# to 12) and fv (bits 13 up): 1 + the highest free variable of its term, 0
# when it has none. Field 1 counts the pointers to it, or links it into a
# list. Fields 2 to 4 hold its parts: as the kernel's formers do, in order;
# a Ref holds its def's body (0 for none), a Lab and a Mat their name, by the
# number that the image gives it.
#
# The machine runs as the Lean machine (lean, Interpreter/Machine.lean) does,
# on closed terms: a focus, and a stack of frames, which are cells. A call or
# a λ copies its code, with pointers to its arguments: a part whose free
# variables the copy does not reach is shared, not copied. A cell whose count
# drops to 0 goes to a list of cells to reuse, and its parts lose a pointer
# when the cell is reused. As cells form no cycle, every cell that can no
# longer be reached is freed so (AGENTS.md 3.9.1.4); only the image and the
# cache of the input's bytes are STATIC, never freed.

# building Cir

def M.c(n: U32) -> Cr.Cir.Expr:
  Cr.Cir.Expr.const{n}

def M.g(r: Nat) -> Cr.Cir.Expr:
  Cr.Cir.Expr.get{r}

def M.f(k: Nat, c: Cr.Cir.Expr) -> Cr.Cir.Expr:
  Cr.Cir.Expr.field{k, c}

def M.add(a: Cr.Cir.Expr, b: Cr.Cir.Expr) -> Cr.Cir.Expr:
  Cr.Cir.Expr.op{Wa.Wasm.Op.add{}, a, b}

def M.sub(a: Cr.Cir.Expr, b: Cr.Cir.Expr) -> Cr.Cir.Expr:
  Cr.Cir.Expr.op{Wa.Wasm.Op.sub{}, a, b}

def M.and(a: Cr.Cir.Expr, b: Cr.Cir.Expr) -> Cr.Cir.Expr:
  Cr.Cir.Expr.op{Wa.Wasm.Op.and{}, a, b}

def M.or(a: Cr.Cir.Expr, b: Cr.Cir.Expr) -> Cr.Cir.Expr:
  Cr.Cir.Expr.op{Wa.Wasm.Op.or{}, a, b}

def M.shl(a: Cr.Cir.Expr, b: Cr.Cir.Expr) -> Cr.Cir.Expr:
  Cr.Cir.Expr.op{Wa.Wasm.Op.shl{}, a, b}

def M.shr(a: Cr.Cir.Expr, b: Cr.Cir.Expr) -> Cr.Cir.Expr:
  Cr.Cir.Expr.op{Wa.Wasm.Op.shr_u{}, a, b}

def M.eq(a: Cr.Cir.Expr, b: Cr.Cir.Expr) -> Cr.Cir.Expr:
  Cr.Cir.Expr.op{Wa.Wasm.Op.eq{}, a, b}

def M.ne(a: Cr.Cir.Expr, b: Cr.Cir.Expr) -> Cr.Cir.Expr:
  Cr.Cir.Expr.op{Wa.Wasm.Op.ne{}, a, b}

def M.lt(a: Cr.Cir.Expr, b: Cr.Cir.Expr) -> Cr.Cir.Expr:
  Cr.Cir.Expr.op{Wa.Wasm.Op.lt_u{}, a, b}

def M.le(a: Cr.Cir.Expr, b: Cr.Cir.Expr) -> Cr.Cir.Expr:
  Cr.Cir.Expr.op{Wa.Wasm.Op.le_u{}, a, b}

def M.gt(a: Cr.Cir.Expr, b: Cr.Cir.Expr) -> Cr.Cir.Expr:
  Cr.Cir.Expr.op{Wa.Wasm.Op.gt_u{}, a, b}

def M.ge(a: Cr.Cir.Expr, b: Cr.Cir.Expr) -> Cr.Cir.Expr:
  Cr.Cir.Expr.op{Wa.Wasm.Op.ge_u{}, a, b}

def M.not(a: Cr.Cir.Expr) -> Cr.Cir.Expr:
  Cr.Cir.Expr.eqz{a}

def M.set(r: Nat, e: Cr.Cir.Expr) -> Cr.Cir.Stmt:
  Cr.Cir.Stmt.set{r, e}

def M.st(k: Nat, c: Cr.Cir.Expr, v: Cr.Cir.Expr) -> Cr.Cir.Stmt:
  Cr.Cir.Stmt.store{k, c, v}

def M.do(ss: List<&2, Cr.Cir.Stmt>) -> Cr.Cir.Stmt:
  match ss:
    case Nil{}:
      Cr.Cir.Stmt.nop{}
    case Con{s, rest}:
      Cr.Cir.Stmt.seq{s, M.do(rest)}

def M.if(c: Cr.Cir.Expr, t: Cr.Cir.Stmt, e: Cr.Cir.Stmt) -> Cr.Cir.Stmt:
  Cr.Cir.Stmt.if{c, t, e}

def M.when(c: Cr.Cir.Expr, t: Cr.Cir.Stmt) -> Cr.Cir.Stmt:
  Cr.Cir.Stmt.if{c, t, Cr.Cir.Stmt.nop{}}

def M.while(c: Cr.Cir.Expr, body: Cr.Cir.Stmt) -> Cr.Cir.Stmt:
  Cr.Cir.Stmt.while{c, body}

def M.halt(s: U32) -> Cr.Cir.Stmt:
  Cr.Cir.Stmt.halt{s}

# the registers

def R.focus() -> Nat:
  0n

def R.mode() -> Nat:
  1n

def R.sp() -> Nat:
  2n

def R.pend() -> Nat:
  3n

def R.dx() -> Nat:
  4n

def R.dr() -> Nat:
  5n

def R.aq() -> Nat:
  6n

def R.am() -> Nat:
  7n

def R.c() -> Nat:
  8n

def R.h() -> Nat:
  9n

def R.tag() -> Nat:
  10n

def R.x() -> Nat:
  11n

def R.y() -> Nat:
  12n

def R.z() -> Nat:
  13n

def R.q() -> Nat:
  14n

def R.n() -> Nat:
  15n

def R.fr() -> Nat:
  16n

def R.k() -> Nat:
  17n

def R.p() -> Nat:
  18n

def R.wt() -> Nat:
  19n

def R.wenv() -> Nat:
  20n

def R.wargs() -> Nat:
  21n

def R.wa() -> Nat:
  22n

def R.wx() -> Nat:
  23n

def R.wq() -> Nat:
  24n

def R.wn() -> Nat:
  25n

def R.wres() -> Nat:
  26n

def R.wok() -> Nat:
  27n

def R.wb() -> Nat:
  28n

def R.wh() -> Nat:
  29n

def R.cs() -> Nat:
  30n

def R.csrc() -> Nat:
  31n

def R.cd() -> Nat:
  32n

def R.sdep() -> Nat:
  33n

def R.ck() -> Nat:
  34n

def R.cnew() -> Nat:
  35n

def R.cenv() -> Nat:
  36n

def R.clen() -> Nat:
  37n

def R.cj() -> Nat:
  38n

def R.croot() -> Nat:
  39n

def R.sres() -> Nat:
  40n

def R.cm() -> Nat:
  41n

def R.ds() -> Nat:
  42n

def R.dok() -> Nat:
  43n

def R.dc() -> Nat:
  44n

def R.oc() -> Nat:
  45n

def R.ow() -> Nat:
  46n

def R.ov() -> Nat:
  47n

def R.oi() -> Nat:
  48n

def R.ii() -> Nat:
  49n

def R.ib() -> Nat:
  50n

def R.il() -> Nat:
  51n

def R.iu() -> Nat:
  52n

def R.ij() -> Nat:
  53n

def R.ss() -> Nat:
  54n

def R.ssrc() -> Nat:
  55n

def R.scut() -> Nat:
  56n

def R.sroot() -> Nat:
  57n

def R.sk() -> Nat:
  58n

def R.snew() -> Nat:
  59n

def R.samt() -> Nat:
  60n

def R.t1() -> Nat:
  61n

def R.t2() -> Nat:
  62n

def Mach.regs() -> Nat:
  63n

# the tags of the formers, in the kernel's order

def T.var() -> U32:
  0

def T.ref() -> U32:
  1

def T.ann() -> U32:
  2

def T.let() -> U32:
  3

def T.min() -> U32:
  5

def T.lam() -> U32:
  7

def T.app() -> U32:
  8

def T.tup() -> U32:
  10

def T.prj() -> U32:
  11

def T.lab() -> U32:
  13

def T.mat() -> U32:
  14

def T.efq() -> U32:
  15

def T.rfl() -> U32:
  17

def T.rwt() -> U32:
  18

# the machine's own cells: frames (the kernel's App, Let, Tup, Rwt and Min
# with a hole), the arguments and locals of a walk, and work for a copy and a
# check

def K.app_arg() -> U32:
  32

def K.app_val() -> U32:
  33

def K.app_fun() -> U32:
  34

def K.let_in() -> U32:
  35

def K.tup_b() -> U32:
  36

def K.tup_a() -> U32:
  37

def K.rwt() -> U32:
  38

def K.min_b() -> U32:
  39

def K.min_a() -> U32:
  40

def K.arg() -> U32:
  41

def K.check() -> U32:
  44

def K.root() -> U32:
  45

# the flags

def F.value() -> U32:
  256

def F.data() -> U32:
  512

def F.static() -> U32:
  1024

def F.known() -> U32:
  2048

def F.owned() -> U32:
  4096

# the most that fv holds: a cell whose fv is this is never shared
def F.fv_max() -> U32:
  524287

# the cells that the image holds first (Mach.image): the labels of the names
# 0 to 9, then constant terms, the cache of the input's bytes, and a table
# by tag

def I.lab(id: U32) -> U32:
  U32.inc(id)

def I.nil() -> U32:
  11

def I.true() -> U32:
  12

def I.false() -> U32:
  13

def I.wnil() -> U32:
  14

def I.ref_main() -> U32:
  15

def I.cache() -> U32:
  16

# by tag t, the cell I.table() + t holds the mask of its pointers in field 2
# (1 for field 2, 2 for 3, 4 for 4), the binders above each in field 3 (2
# bits each, the field 2's lowest) and 1 in field 4 when a term of the tag is
# a value by its form
def I.table() -> U32:
  272

# the first cell of the book's defs
def I.book() -> U32:
  291

# the names that the machine knows, by number

def N.unit() -> U32:
  0

def N.nil() -> U32:
  1

def N.con() -> U32:
  2

def N.wnil() -> U32:
  3

def N.wcon() -> U32:
  4

def N.true() -> U32:
  5

def N.false() -> U32:
  6

def N.q0() -> U32:
  7

def N.q1() -> U32:
  8

def N.q2() -> U32:
  9

def N.main() -> U32:
  10

# the parts of a cell

def M.tag(c: Cr.Cir.Expr) -> Cr.Cir.Expr:
  M.and(M.f(0n, c), M.c(63))

def M.q(c: Cr.Cir.Expr) -> Cr.Cir.Expr:
  M.and(M.shr(M.f(0n, c), M.c(6)), M.c(3))

def M.flag(c: Cr.Cir.Expr, flag: U32) -> Cr.Cir.Expr:
  M.ne(M.and(M.f(0n, c), M.c(flag)), M.c(0))

def M.fv(c: Cr.Cir.Expr) -> Cr.Cir.Expr:
  M.shr(M.f(0n, c), M.c(13))

# the entry of the table by tag for the cell c, a term
def M.entry(k: Nat, c: Cr.Cir.Expr) -> Cr.Cir.Expr:
  M.f(k, M.add(M.c(I.table()), M.tag(c)))

# the cell in register r gains a pointer, unless it is none or one of the
# image's
def M.inc(+r: Nat) -> Cr.Cir.Stmt:
  M.when(M.ne(M.g(r), M.c(0)),
    M.when(M.not(M.flag(M.g(r), F.static())),
      M.st(1n, M.g(r), M.add(M.f(1n, M.g(r)), M.c(1)))))

# the cell in register r loses a pointer; at 0 it goes to the list of cells
# to reuse, the pend list
def M.dec(+r: Nat) -> Cr.Cir.Stmt:
  M.when(M.ne(M.g(r), M.c(0)),
    M.when(M.not(M.flag(M.g(r), F.static())), M.do([
      M.set(R.dr(), M.sub(M.f(1n, M.g(r)), M.c(1))),
      M.st(1n, M.g(r), M.g(R.dr())),
      M.when(M.eq(M.g(R.dr()), M.c(0)), M.do([
        M.st(1n, M.g(r), M.g(R.pend())),
        M.set(R.pend(), M.g(r))]))])))

# the part in field k of the cell aq loses a pointer, when the mask am says it
# is one
def M.dec.part(k: Nat, bit: U32) -> Cr.Cir.Stmt:
  M.when(M.ne(M.and(M.g(R.am()), M.c(bit)), M.c(0)), M.do([
    M.set(R.dx(), M.f(k, M.g(R.aq()))),
    M.dec(R.dx())]))

# register r gets a cell, all zeros: the first of the pend list, whose parts
# then lose a pointer, or a new one
def M.alloc(+r: Nat) -> Cr.Cir.Stmt:
  M.if(M.ne(M.g(R.pend()), M.c(0)), M.do([
    M.set(R.aq(), M.g(R.pend())),
    M.set(R.pend(), M.f(1n, M.g(R.aq()))),
    M.if(M.lt(M.tag(M.g(R.aq())), M.c(32)),
      M.set(R.am(), M.entry(2n, M.g(R.aq()))),
      M.set(R.am(), M.c(0))),
    M.dec.part(2n, 1),
    M.dec.part(3n, 2),
    M.dec.part(4n, 4),
    M.st(0n, M.g(R.aq()), M.c(0)),
    M.st(1n, M.g(R.aq()), M.c(0)),
    M.st(2n, M.g(R.aq()), M.c(0)),
    M.st(3n, M.g(R.aq()), M.c(0)),
    M.st(4n, M.g(R.aq()), M.c(0)),
    M.set(r, M.g(R.aq()))]),
    Cr.Cir.Stmt.alloc{r})

# register r gets a new cell: the header h, one pointer to it, and the fields
# a, b and c
def M.make(+r: Nat, h: Cr.Cir.Expr, a: Cr.Cir.Expr, b: Cr.Cir.Expr, c: Cr.Cir.Expr) -> Cr.Cir.Stmt:
  M.do([
    M.alloc(r),
    M.st(0n, M.g(r), h),
    M.st(1n, M.g(r), M.c(1)),
    M.st(2n, M.g(r), a),
    M.st(3n, M.g(r), b),
    M.st(4n, M.g(r), c)])

# the machine's own cell in register r goes to the pend list: its parts lose
# no pointer when it is reused
def M.release(+r: Nat) -> Cr.Cir.Stmt:
  M.do([
    M.st(1n, M.g(r), M.g(R.pend())),
    M.set(R.pend(), M.g(r))])

# a new frame on the stack: the header h, and the fields a and b
def M.push(h: Cr.Cir.Expr, a: Cr.Cir.Expr, b: Cr.Cir.Expr) -> Cr.Cir.Stmt:
  M.do([
    M.alloc(R.fr()),
    M.st(0n, M.g(R.fr()), h),
    M.st(1n, M.g(R.fr()), M.g(R.sp())),
    M.st(2n, M.g(R.fr()), a),
    M.st(3n, M.g(R.fr()), b),
    M.set(R.sp(), M.g(R.fr()))])

# the top frame leaves the stack, and goes to the pend list
def M.pop() -> Cr.Cir.Stmt:
  M.do([
    M.set(R.fr(), M.g(R.sp())),
    M.set(R.sp(), M.f(1n, M.g(R.fr()))),
    M.release(R.fr())])

# a header of the kind k, the quantity q and the flags fl
def M.header(k: U32, q: Cr.Cir.Expr, fl: Cr.Cir.Expr) -> Cr.Cir.Expr:
  M.or(M.or(M.c(k), M.shl(q, M.c(6))), fl)

# Data: register dok gets 1 when the term in register r is Data (Lab, Rfl, or a
# pair of Data whose first field is Data or dead), else 0. Each cell that the
# check reaches is flagged DATA at once, and is not checked again: when the
# check fails, the run ends with no result, so no flag is ever read wrong
def M.data(+r: Nat) -> Cr.Cir.Stmt:
  M.do([
    M.set(R.dok(), M.c(1)),
    M.set(R.ds(), M.c(0)),
    M.make(R.dc(), M.c(K.check()), M.g(r), M.c(0), M.c(0)),
    M.st(1n, M.g(R.dc()), M.g(R.ds())),
    M.set(R.ds(), M.g(R.dc())),
    M.while(M.and(M.ne(M.g(R.ds()), M.c(0)), M.g(R.dok())), M.do([
      M.set(R.dc(), M.g(R.ds())),
      M.set(R.ds(), M.f(1n, M.g(R.dc()))),
      M.set(R.t1(), M.f(2n, M.g(R.dc()))),
      M.release(R.dc()),
      M.when(M.not(M.flag(M.g(R.t1()), F.data())),
        M.if(M.or(M.eq(M.tag(M.g(R.t1())), M.c(T.lab())), M.eq(M.tag(M.g(R.t1())), M.c(T.rfl()))),
          M.st(0n, M.g(R.t1()), M.or(M.f(0n, M.g(R.t1())), M.c(F.data()))),
          M.if(M.eq(M.tag(M.g(R.t1())), M.c(T.tup())), M.do([
            M.st(0n, M.g(R.t1()), M.or(M.f(0n, M.g(R.t1())), M.c(F.data()))),
            M.make(R.dc(), M.c(K.check()), M.f(3n, M.g(R.t1())), M.c(0), M.c(0)),
            M.st(1n, M.g(R.dc()), M.g(R.ds())),
            M.set(R.ds(), M.g(R.dc())),
            M.when(M.ne(M.q(M.g(R.t1())), M.c(0)), M.do([
              M.make(R.dc(), M.c(K.check()), M.f(2n, M.g(R.t1())), M.c(0), M.c(0)),
              M.st(1n, M.g(R.dc()), M.g(R.ds())),
              M.set(R.ds(), M.g(R.dc()))]))]),
            M.set(R.dok(), M.c(0)))))])),
    M.while(M.ne(M.g(R.ds()), M.c(0)), M.do([
      M.set(R.dc(), M.g(R.ds())),
      M.set(R.ds(), M.f(1n, M.g(R.dc()))),
      M.release(R.dc())]))])

# a when c is 1, b when c is 0: by masks, with no branch
def M.pick(+c: Cr.Cir.Expr, a: Cr.Cir.Expr, b: Cr.Cir.Expr) -> Cr.Cir.Expr:
  M.or(M.and(a, M.sub(M.c(0), c)), M.and(b, M.sub(c, M.c(1))))

def M.max(+a: Cr.Cir.Expr, +b: Cr.Cir.Expr) -> Cr.Cir.Expr:
  M.pick(M.gt(a, b), a, b)

# field k (2, 3 or 4, in register rk) of the cell in register rd gets v
def M.put(+rd: Nat, +rk: Nat, +v: Cr.Cir.Expr) -> Cr.Cir.Stmt:
  M.if(M.eq(M.g(rk), M.c(2)), M.st(2n, M.g(rd), v),
    M.if(M.eq(M.g(rk), M.c(3)), M.st(3n, M.g(rd), v), M.st(4n, M.g(rd), v)))

# field k (2, 3 or 4) of the cell c
def M.get(+c: Cr.Cir.Expr, +k: Cr.Cir.Expr) -> Cr.Cir.Expr:
  M.pick(M.eq(k, M.c(2)), M.f(2n, c), M.pick(M.eq(k, M.c(3)), M.f(3n, c), M.f(4n, c)))

# the binders above field k (2, 3 or 4) of the term cell c, by the table
def M.bump(+c: Cr.Cir.Expr, +k: Cr.Cir.Expr) -> Cr.Cir.Expr:
  M.and(M.shr(M.entry(3n, c), M.shl(M.sub(k, M.c(2)), M.c(1))), M.c(3))

# A copy makes its new cells in place: a new cell holds the parts of its
# source until each is copied in turn, and bits 8 to 10 of its field 0 (for
# fields 2 to 4) say which are still to copy. The new cells whose parts are
# not all copied form a stack, linked by field 1, each above the cell that
# holds it; a register holds the depth of the top one, under the binders of
# the copy. A cell leaves the stack once its parts are copied: its fv is then
# known, and field 1 counts its one pointer. A root cell, a Prj, holds the
# result.

# the bit, among those still to copy, of field k
def M.todo.bit(+k: Cr.Cir.Expr) -> Cr.Cir.Expr:
  M.shl(M.c(64), k)

# the bits of the parts that the new cell c still has to copy
def M.todo(+c: Cr.Cir.Expr) -> Cr.Cir.Expr:
  M.and(M.f(0n, c), M.c(1792))

# the first field that the new cell c still has to copy
def M.todo.first(+c: Cr.Cir.Expr) -> Cr.Cir.Expr:
  M.pick(M.ne(M.and(M.f(0n, c), M.c(256)), M.c(0)), M.c(2),
    M.pick(M.ne(M.and(M.f(0n, c), M.c(512)), M.c(0)), M.c(3), M.c(4)))

# the field of the new cell c that its last copied part is in: the highest
# of its pointers that it does not still have to copy
def M.todo.last(+c: Cr.Cir.Expr) -> Cr.Cir.Expr:
  M.pick(M.eq(M.and(M.sub(M.entry(2n, c), M.shr(M.todo(c), M.c(8))), M.c(4)), M.c(4)), M.c(4),
    M.pick(M.eq(M.and(M.sub(M.entry(2n, c), M.shr(M.todo(c), M.c(8))), M.c(2)), M.c(2)), M.c(3), M.c(2)))

# fv of a part: in t1, its contribution to the fv of the cell c, whose field
# k it is, under the binders of the table
def M.fv.part(+c: Nat, k: Nat, bit: U32, shift: U32) -> Cr.Cir.Stmt:
  M.when(M.ne(M.and(M.entry(2n, M.g(c)), M.c(bit)), M.c(0)), M.do([
    M.set(R.t1(), M.fv(M.f(k, M.g(c)))),
    M.set(R.t2(), M.and(M.shr(M.entry(3n, M.g(c)), M.c(shift)), M.c(3))),
    M.if(M.eq(M.g(R.t1()), M.c(F.fv_max())),
      M.set(R.cm(), M.c(F.fv_max())),
      M.when(M.gt(M.g(R.t1()), M.g(R.t2())),
        M.when(M.gt(M.sub(M.g(R.t1()), M.g(R.t2())), M.g(R.cm())),
          M.when(M.ne(M.g(R.cm()), M.c(F.fv_max())),
            M.set(R.cm(), M.sub(M.g(R.t1()), M.g(R.t2())))))))]))

# the new cell c, once its parts are copied, leaves the stack: its fv is the
# most of its parts' fv, less the binders above each, at most fv_max; and one
# pointer points to it
def M.finish(+c: Nat) -> Cr.Cir.Stmt:
  M.do([
    M.st(1n, M.g(c), M.c(1)),
    M.set(R.cm(), M.c(0)),
    M.fv.part(c, 2n, 1, 0),
    M.fv.part(c, 3n, 2, 2),
    M.fv.part(c, 4n, 4, 4),
    M.st(0n, M.g(c), M.or(M.and(M.f(0n, M.g(c)), M.c(255)), M.shl(M.g(R.cm()), M.c(13))))])

# v when small is 1, fv_max when it is 0: by masks, with no branch
def M.if.e(+small: Cr.Cir.Expr, v: Cr.Cir.Expr) -> Cr.Cir.Expr:
  M.or(M.and(v, M.sub(M.c(0), small)), M.and(M.c(F.fv_max()), M.sub(small, M.c(1))))

# a new variable i in register r: its fv is i + 1, at most fv_max
def M.var(+r: Nat, +i: Cr.Cir.Expr) -> Cr.Cir.Stmt:
  M.make(r, M.or(M.c(T.var()), M.shl(
    M.if.e(M.lt(i, M.c(524286)), M.add(i, M.c(1))), M.c(13))), i, M.c(0), M.c(0))

# register r gets a new cell for the part in register src, which the cell in
# register top holds in field k: the source's fields, all to copy; it goes on
# the stack in register s
def M.copy.push(+r: Nat, +src: Nat, +top: Nat, +k: Nat, +s: Nat) -> Cr.Cir.Stmt:
  M.do([
    M.make(r, M.or(M.and(M.f(0n, M.g(src)), M.c(255)), M.shl(M.entry(2n, M.g(src)), M.c(8))),
      M.f(2n, M.g(src)), M.f(3n, M.g(src)), M.f(4n, M.g(src))),
    M.st(1n, M.g(r), M.g(s)),
    M.put(top, k, M.g(r)),
    M.set(s, M.g(r))])

# the root of a copy of the term in register src, in register r: a Prj whose
# part is to copy
def M.copy.root(+r: Nat, +src: Nat) -> Cr.Cir.Stmt:
  M.do([
    M.make(r, M.c(U32.or(T.prj(), 256)), M.g(src), M.c(0), M.c(0)),
    M.st(1n, M.g(r), M.c(0))])

# register r gets the copy's result in the root cell in register root; the
# root goes to the pend list, as a cell whose parts lose no pointer
def M.copy.end(+r: Nat, +root: Nat) -> Cr.Cir.Stmt:
  M.do([
    M.set(r, M.f(2n, M.g(root))),
    M.st(0n, M.g(root), M.c(K.root())),
    M.release(root)])

# register r gets the copy of the term in register src, made by the stack in
# register stack of new cells (above), from a root cell in register root: the
# register depth holds the depth of the top cell, top that cell; part copies
# the part in register at, for its field k, at the depth in register under
def M.copy.walk(+r: Nat, +src: Nat, +root: Nat, +stack: Nat, +depth: Nat, +top: Nat, +k: Nat, +at: Nat,
  +under: Nat, part: Cr.Cir.Stmt) -> Cr.Cir.Stmt:
  M.do([
    M.copy.root(root, src),
    M.set(stack, M.g(root)),
    M.set(depth, M.c(0)),
    M.while(M.ne(M.g(stack), M.c(0)), M.do([
      M.set(top, M.g(stack)),
      M.if(M.eq(M.todo(M.g(top)), M.c(0)), M.do([
        M.set(stack, M.f(1n, M.g(top))),
        M.finish(top),
        M.when(M.ne(M.g(stack), M.c(0)),
          M.set(depth, M.sub(M.g(depth), M.bump(M.g(stack), M.todo.last(M.g(stack))))))]),
      M.do([
        M.set(k, M.todo.first(M.g(top))),
        M.st(0n, M.g(top), M.sub(M.f(0n, M.g(top)), M.todo.bit(M.g(k)))),
        M.set(at, M.get(M.g(top), M.g(k))),
        M.set(under, M.add(M.g(depth), M.bump(M.g(top), M.g(k)))),
        part]))])),
    M.copy.end(r, root)])

# register r gets the term in register v with each free variable from the
# cutoff 0 on moved up by samt, as Term.shift does; a part whose free
# variables are all below its cutoff is shared
def M.shift(+r: Nat, +v: Nat) -> Cr.Cir.Stmt:
  M.copy.walk(r, v, R.sroot(), R.ss(), R.scut(), R.snew(), R.sk(), R.ssrc(), R.sdep(),
    M.if(M.and(M.lt(M.fv(M.g(R.ssrc())), M.c(F.fv_max())), M.le(M.fv(M.g(R.ssrc())), M.g(R.sdep()))),
      M.inc(R.ssrc()),
      M.if(M.eq(M.tag(M.g(R.ssrc())), M.c(T.var())),
        M.if(M.lt(M.f(2n, M.g(R.ssrc())), M.g(R.sdep())),
          M.inc(R.ssrc()),
          M.do([
            M.var(R.t1(), M.add(M.f(2n, M.g(R.ssrc())), M.g(R.samt()))),
            M.put(R.snew(), R.sk(), M.g(R.t1()))])),
        M.do([
          M.copy.push(R.t1(), R.ssrc(), R.snew(), R.sk(), R.ss()),
          M.set(R.scut(), M.g(R.sdep()))]))))

# the part in register csrc, which the new cell cnew holds in field ck, at
# the depth cj: shared, when its free variables are all below cj; for a
# variable cj + j, the local j of the list in cenv, of clen locals, shifted
# by cj; for a variable past them, as the kernel's Env.sub does, j - clen;
# else a new cell on the stack
def M.copy.part() -> Cr.Cir.Stmt:
  M.if(M.and(M.lt(M.fv(M.g(R.csrc())), M.c(F.fv_max())), M.le(M.fv(M.g(R.csrc())), M.g(R.cj()))),
    M.inc(R.csrc()),
    M.if(M.eq(M.tag(M.g(R.csrc())), M.c(T.var())),
      M.if(M.lt(M.f(2n, M.g(R.csrc())), M.g(R.cj())),
        M.inc(R.csrc()),
        M.do([
          M.set(R.t1(), M.sub(M.f(2n, M.g(R.csrc())), M.g(R.cj()))),
          M.if(M.lt(M.g(R.t1()), M.g(R.clen())), M.do([
            M.set(R.t2(), M.g(R.cenv())),
            M.while(M.ne(M.g(R.t1()), M.c(0)), M.do([
              M.set(R.t2(), M.f(1n, M.g(R.t2()))),
              M.set(R.t1(), M.sub(M.g(R.t1()), M.c(1)))])),
            M.set(R.t2(), M.f(2n, M.g(R.t2()))),
            M.if(M.or(M.eq(M.fv(M.g(R.t2())), M.c(0)), M.eq(M.g(R.cj()), M.c(0))),
              M.do([M.inc(R.t2()), M.put(R.cnew(), R.ck(), M.g(R.t2()))]),
              M.do([
                M.set(R.samt(), M.g(R.cj())),
                M.shift(R.sres(), R.t2()),
                M.put(R.cnew(), R.ck(), M.g(R.sres()))]))]),
          M.do([
            M.var(R.t2(), M.sub(M.f(2n, M.g(R.csrc())), M.g(R.clen()))),
            M.put(R.cnew(), R.ck(), M.g(R.t2()))]))])),
      M.do([
        M.copy.push(R.t2(), R.csrc(), R.cnew(), R.ck(), R.cs()),
        M.set(R.cd(), M.g(R.cj()))])))

# register r gets the copy of the term in register src, as Term.subst gives
# it at the depth 0, with the list of locals in cenv, of clen locals
def M.copy(+r: Nat, +src: Nat) -> Cr.Cir.Stmt:
  M.copy.walk(r, src, R.croot(), R.cs(), R.cd(), R.cnew(), R.ck(), R.csrc(), R.cj(), M.copy.part())

# the run goes on when c is not 0; else it ends with no result
def M.need(c: Cr.Cir.Expr, then: Cr.Cir.Stmt) -> Cr.Cir.Stmt:
  M.if(c, then, M.halt(2))

# the term of an argument cell loses a pointer when the cell owned it; the
# cell goes to the pend list
def M.release.arg(+a: Nat) -> Cr.Cir.Stmt:
  M.do([
    M.when(M.flag(M.g(a), F.owned()), M.do([M.set(R.dx(), M.f(2n, M.g(a))), M.dec(R.dx())])),
    M.release(a)])

# all the cells of the list in register l go to the pend list
def M.release.all(+l: Nat) -> Cr.Cir.Stmt:
  M.while(M.ne(M.g(l), M.c(0)), M.do([
    M.set(R.wa(), M.g(l)),
    M.set(l, M.f(1n, M.g(R.wa()))),
    M.release.arg(R.wa())]))

# the quantity of a pair's first field, the pair's in register r used at q
def M.fld(+r: Cr.Cir.Expr, q: Cr.Cir.Expr) -> Cr.Cir.Expr:
  M.pick(M.eq(r, M.c(1)), q, r)

# a λ, a λ-match or Efq: a node of a case tree, which takes an argument, by
# its tag t
def M.takes(+t: Cr.Cir.Expr) -> Cr.Cir.Expr:
  M.or(M.or(M.eq(t, M.c(T.lam())), M.eq(t, M.c(T.prj()))), M.or(M.eq(t, M.c(T.mat())), M.eq(t, M.c(T.efq()))))

# a λ of the case tree binds the first argument: both live or both dead, and
# Data when the λ's quantity is 2
def M.walk.lam() -> Cr.Cir.Stmt:
  M.if(M.eq(M.g(R.wargs()), M.c(0)), M.set(R.wres(), M.c(2)), M.do([
    M.set(R.wa(), M.g(R.wargs())),
    M.set(R.wq(), M.q(M.g(R.wa()))),
    M.set(R.wx(), M.f(2n, M.g(R.wa()))),
    M.set(R.wok(), M.eq(M.ne(M.q(M.g(R.wt())), M.c(0)), M.ne(M.g(R.wq()), M.c(0)))),
    M.when(M.and(M.g(R.wok()), M.eq(M.q(M.g(R.wt())), M.c(2))), M.do([
      M.data(R.wx()),
      M.set(R.wok(), M.g(R.dok()))])),
    M.if(M.g(R.wok()), M.do([
      M.set(R.wargs(), M.f(1n, M.g(R.wa()))),
      M.st(1n, M.g(R.wa()), M.g(R.wenv())),
      M.set(R.wenv(), M.g(R.wa())),
      M.set(R.wn(), M.add(M.g(R.wn()), M.c(1))),
      M.set(R.wt(), M.f(2n, M.g(R.wt())))]),
      M.set(R.wres(), M.c(3)))]))

# a λ-match of pairs splits the first argument, a live pair, into its fields
def M.walk.prj() -> Cr.Cir.Stmt:
  M.if(M.eq(M.g(R.wargs()), M.c(0)), M.set(R.wres(), M.c(2)), M.do([
    M.set(R.wa(), M.g(R.wargs())),
    M.set(R.wq(), M.q(M.g(R.wa()))),
    M.set(R.wx(), M.f(2n, M.g(R.wa()))),
    M.if(M.and(M.ne(M.g(R.wq()), M.c(0)), M.eq(M.tag(M.g(R.wx())), M.c(T.tup()))), M.do([
      M.set(R.wb(), M.q(M.g(R.wx()))),
      M.make(R.wh(),
        M.header(K.arg(), M.fld(M.g(R.wb()), M.g(R.wq())),
          M.and(M.and(M.f(0n, M.g(R.wa())), M.c(F.known())), M.sub(M.c(0), M.ne(M.g(R.wb()), M.c(0))))),
        M.f(2n, M.g(R.wx())), M.c(0), M.c(0)),
      M.st(1n, M.g(R.wh()), M.g(R.wa())),
      M.st(2n, M.g(R.wa()), M.f(3n, M.g(R.wx()))),
      M.set(R.wargs(), M.g(R.wh())),
      M.set(R.wt(), M.f(2n, M.g(R.wt())))]),
      M.set(R.wres(), M.c(3)))]))

# a λ-match of labels takes its first case on the first argument's label, a
# live one; else its other case, on the same argument
def M.walk.mat() -> Cr.Cir.Stmt:
  M.if(M.eq(M.g(R.wargs()), M.c(0)), M.set(R.wres(), M.c(2)), M.do([
    M.set(R.wa(), M.g(R.wargs())),
    M.set(R.wq(), M.q(M.g(R.wa()))),
    M.set(R.wx(), M.f(2n, M.g(R.wa()))),
    M.if(M.and(M.ne(M.g(R.wq()), M.c(0)), M.eq(M.tag(M.g(R.wx())), M.c(T.lab()))),
      M.if(M.eq(M.f(2n, M.g(R.wx())), M.f(2n, M.g(R.wt()))), M.do([
        M.set(R.wargs(), M.f(1n, M.g(R.wa()))),
        M.release.arg(R.wa()),
        M.set(R.wt(), M.f(3n, M.g(R.wt())))]),
      M.do([
        M.st(0n, M.g(R.wa()), M.or(M.f(0n, M.g(R.wa())), M.c(F.known()))),
        M.set(R.wt(), M.f(4n, M.g(R.wt())))])),
      M.set(R.wres(), M.c(3)))]))

# App q f (Var v), where f's head takes an argument: the local v goes first
# among the arguments (a free variable when there is no local v); any other
# App is a leaf
def M.walk.app() -> Cr.Cir.Stmt:
  M.do([
    M.set(R.wx(), M.f(3n, M.g(R.wt()))),
    M.if(M.ne(M.tag(M.g(R.wx())), M.c(T.var())), M.set(R.wres(), M.c(1)), M.do([
      M.set(R.wh(), M.f(2n, M.g(R.wt()))),
      M.while(M.eq(M.tag(M.g(R.wh())), M.c(T.app())), M.set(R.wh(), M.f(2n, M.g(R.wh())))),
      M.set(R.wok(), M.takes(M.tag(M.g(R.wh())))),
      M.if(M.not(M.g(R.wok())), M.set(R.wres(), M.c(1)), M.do([
        M.set(R.wb(), M.f(2n, M.g(R.wx()))),
        M.if(M.lt(M.g(R.wb()), M.g(R.wn())), M.do([
          M.set(R.wh(), M.g(R.wenv())),
          M.while(M.ne(M.g(R.wb()), M.c(0)), M.do([
            M.set(R.wh(), M.f(1n, M.g(R.wh()))),
            M.set(R.wb(), M.sub(M.g(R.wb()), M.c(1)))])),
          M.make(R.wa(), M.header(K.arg(), M.q(M.g(R.wt())), M.and(M.f(0n, M.g(R.wh())), M.c(F.known()))),
            M.f(2n, M.g(R.wh())), M.c(0), M.c(0))]),
        M.do([
          M.var(R.wx(), M.sub(M.g(R.wb()), M.g(R.wn()))),
          M.make(R.wa(), M.header(K.arg(), M.q(M.g(R.wt())), M.c(F.owned())), M.g(R.wx()), M.c(0), M.c(0))])),
        M.st(1n, M.g(R.wa()), M.g(R.wargs())),
        M.set(R.wargs(), M.g(R.wa())),
        M.set(R.wt(), M.f(2n, M.g(R.wt())))]))]))])

# the walk (Eval.walk) of the case tree in register wt on the argument list
# in wargs: wres is 1 at a leaf, 2 when the tree needs more arguments, 3 when
# there is no walk; wenv holds the wn locals that its λs bound
def M.walk() -> Cr.Cir.Stmt:
  M.do([
    M.set(R.wenv(), M.c(0)),
    M.set(R.wn(), M.c(0)),
    M.set(R.wres(), M.c(0)),
    M.while(M.eq(M.g(R.wres()), M.c(0)),
      M.if(M.eq(M.tag(M.g(R.wt())), M.c(T.lam())), M.walk.lam(),
        M.if(M.eq(M.tag(M.g(R.wt())), M.c(T.prj())), M.walk.prj(),
          M.if(M.eq(M.tag(M.g(R.wt())), M.c(T.mat())), M.walk.mat(),
            M.if(M.eq(M.tag(M.g(R.wt())), M.c(T.app())), M.walk.app(),
              M.if(M.eq(M.tag(M.g(R.wt())), M.c(T.efq())),
                M.set(R.wres(), M.pick(M.eq(M.g(R.wargs()), M.c(0)), M.c(2), M.c(3))),
                M.set(R.wres(), M.c(1))))))))])

# a call (Eval.call) of the case tree in wt on the arguments in wargs: at a
# leaf, the copy of the leaf with the walk's locals is the focus, after done,
# and the arguments left are frames; when the tree needs more arguments,
# partial; else no result
def M.call(partial: Cr.Cir.Stmt, done: Cr.Cir.Stmt) -> Cr.Cir.Stmt:
  M.do([
    M.walk(),
    M.if(M.eq(M.g(R.wres()), M.c(1)), M.do([
      M.set(R.cenv(), M.g(R.wenv())),
      M.set(R.clen(), M.g(R.wn())),
      M.copy(R.n(), R.wt()),
      M.set(R.wh(), M.c(0)),
      M.while(M.ne(M.g(R.wargs()), M.c(0)), M.do([
        M.set(R.wa(), M.g(R.wargs())),
        M.set(R.wargs(), M.f(1n, M.g(R.wa()))),
        M.st(1n, M.g(R.wa()), M.g(R.wh())),
        M.set(R.wh(), M.g(R.wa()))])),
      M.while(M.ne(M.g(R.wh()), M.c(0)), M.do([
        M.set(R.wa(), M.g(R.wh())),
        M.set(R.wh(), M.f(1n, M.g(R.wa()))),
        M.set(R.wx(), M.f(2n, M.g(R.wa()))),
        M.inc(R.wx()),
        M.push(M.header(K.app_val(), M.q(M.g(R.wa())), M.and(M.f(0n, M.g(R.wa())), M.c(F.known()))), M.g(R.wx()), M.c(0)),
        M.release.arg(R.wa())])),
      M.release.all(R.wenv()),
      done,
      M.set(R.focus(), M.g(R.n())),
      M.set(R.mode(), M.c(0))]),
    M.if(M.eq(M.g(R.wres()), M.c(2)), M.do([
      M.release.all(R.wargs()),
      M.release.all(R.wenv()),
      partial]),
      M.halt(2)))])

# the locals of a copy: the one term in register r
def M.one(+r: Nat) -> Cr.Cir.Stmt:
  M.do([
    M.make(R.wa(), M.c(K.arg()), M.g(r), M.c(0), M.c(0)),
    M.st(1n, M.g(R.wa()), M.c(0)),
    M.set(R.cenv(), M.g(R.wa())),
    M.set(R.clen(), M.c(1))])

# App q f x (Eval.redex), with the quantity in q, f in x and x in y, both owned
def M.redex() -> Cr.Cir.Stmt:
  M.if(M.eq(M.tag(M.g(R.x())), M.c(T.lam())), M.do([
    M.set(R.wok(), M.eq(M.ne(M.q(M.g(R.x())), M.c(0)), M.ne(M.g(R.q()), M.c(0)))),
    M.when(M.and(M.g(R.wok()), M.eq(M.q(M.g(R.x())), M.c(2))), M.do([
      M.data(R.y()),
      M.set(R.wok(), M.g(R.dok()))])),
    M.need(M.g(R.wok()), M.do([
      M.one(R.y()),
      M.set(R.z(), M.f(2n, M.g(R.x()))),
      M.copy(R.n(), R.z()),
      M.release(R.wa()),
      M.dec(R.y()),
      M.dec(R.x()),
      M.set(R.focus(), M.g(R.n())),
      M.set(R.mode(), M.c(0))]))]),
  M.if(M.eq(M.tag(M.g(R.x())), M.c(T.prj())),
    M.need(M.and(M.ne(M.g(R.q()), M.c(0)), M.eq(M.tag(M.g(R.y())), M.c(T.tup()))), M.do([
      M.set(R.p(), M.q(M.g(R.y()))),
      M.set(R.z(), M.f(2n, M.g(R.y()))),
      M.set(R.k(), M.f(3n, M.g(R.y()))),
      M.inc(R.z()),
      M.inc(R.k()),
      M.push(M.header(K.app_val(), M.g(R.q()), M.c(F.known())), M.g(R.k()), M.c(0)),
      M.push(M.header(K.app_val(), M.fld(M.g(R.p()), M.g(R.q())),
        M.and(M.c(F.known()), M.sub(M.c(0), M.ne(M.g(R.p()), M.c(0))))), M.g(R.z()), M.c(0)),
      M.set(R.n(), M.f(2n, M.g(R.x()))),
      M.inc(R.n()),
      M.dec(R.y()),
      M.dec(R.x()),
      M.set(R.focus(), M.g(R.n())),
      M.set(R.mode(), M.c(0))])),
  M.if(M.eq(M.tag(M.g(R.x())), M.c(T.mat())),
    M.need(M.and(M.ne(M.g(R.q()), M.c(0)), M.eq(M.tag(M.g(R.y())), M.c(T.lab()))),
      M.if(M.eq(M.f(2n, M.g(R.y())), M.f(2n, M.g(R.x()))), M.do([
        M.set(R.n(), M.f(3n, M.g(R.x()))),
        M.inc(R.n()),
        M.dec(R.y()),
        M.dec(R.x()),
        M.set(R.focus(), M.g(R.n())),
        M.set(R.mode(), M.c(0))]),
      M.do([
        M.set(R.n(), M.f(4n, M.g(R.x()))),
        M.inc(R.n()),
        M.push(M.header(K.app_val(), M.g(R.q()), M.c(F.known())), M.g(R.y()), M.c(0)),
        M.dec(R.x()),
        M.set(R.focus(), M.g(R.n())),
        M.set(R.mode(), M.c(0))]))),
  M.do([
    M.make(R.wa(), M.header(K.arg(), M.g(R.q()), M.and(M.c(F.known()), M.sub(M.c(0), M.ne(M.g(R.q()), M.c(0))))),
      M.g(R.y()), M.c(0), M.c(0)),
    M.st(1n, M.g(R.wa()), M.c(0)),
    M.set(R.wargs(), M.g(R.wa())),
    M.set(R.wh(), M.g(R.x())),
    M.while(M.eq(M.tag(M.g(R.wh())), M.c(T.app())), M.do([
      M.make(R.wa(), M.header(K.arg(), M.q(M.g(R.wh())),
        M.and(M.c(F.known()), M.sub(M.c(0), M.ne(M.q(M.g(R.wh())), M.c(0))))), M.f(3n, M.g(R.wh())), M.c(0), M.c(0)),
      M.st(1n, M.g(R.wa()), M.g(R.wargs())),
      M.set(R.wargs(), M.g(R.wa())),
      M.set(R.wh(), M.f(2n, M.g(R.wh())))])),
    M.need(M.eq(M.tag(M.g(R.wh())), M.c(T.ref())), M.do([
      M.set(R.wt(), M.f(2n, M.g(R.wh()))),
      M.need(M.ne(M.g(R.wt()), M.c(0)),
        M.call(
          M.do([
            M.make(R.n(), M.or(M.header(T.app(), M.g(R.q()), M.c(F.value())),
              M.shl(M.max(M.fv(M.g(R.x())), M.fv(M.g(R.y()))), M.c(13))), M.g(R.x()), M.g(R.y()), M.c(0)),
            M.set(R.focus(), M.g(R.n())),
            M.set(R.mode(), M.c(1))]),
          M.do([M.dec(R.y()), M.dec(R.x())])))]))]))))

# the moves of the machine (the Lean machine's move), by the focus: in mode 0
# a term to evaluate, in mode 1 a value; a step of Eval, or a move that only
# finds the next step

# Ann x T: x, a step
def M.ev.ann() -> Cr.Cir.Stmt:
  M.do([
    M.set(R.n(), M.f(2n, M.g(R.c()))),
    M.inc(R.n()),
    M.dec(R.c()),
    M.set(R.focus(), M.g(R.n()))])

# Ref k: the call of k on no arguments: a step to its leaf; or, when its case
# tree takes an argument, a value
def M.ev.ref() -> Cr.Cir.Stmt:
  M.do([
    M.set(R.wt(), M.f(2n, M.g(R.c()))),
    M.need(M.ne(M.g(R.wt()), M.c(0)), M.do([
      M.set(R.wargs(), M.c(0)),
      M.call(M.set(R.mode(), M.c(1)), M.dec(R.c()))]))])

# the part in field a of the focus c, to evaluate, in a frame of header h
# that holds its part in field b
def M.ev.frame(h: Cr.Cir.Expr, a: Nat, b: Nat) -> Cr.Cir.Stmt:
  M.do([
    M.set(R.x(), M.f(a, M.g(R.c()))),
    M.set(R.y(), M.f(b, M.g(R.c()))),
    M.inc(R.x()),
    M.inc(R.y()),
    M.push(h, M.g(R.y()), M.c(0)),
    M.dec(R.c()),
    M.set(R.focus(), M.g(R.x()))])

# App q f x: f, in the frame App q □ x
def M.ev.app() -> Cr.Cir.Stmt:
  M.ev.frame(M.header(K.app_arg(), M.q(M.g(R.c())), M.c(0)), 2n, 3n)

# Let q v f: v in the frame Let q □ f, when q is live; else f with v put in,
# a step
def M.ev.let() -> Cr.Cir.Stmt:
  M.if(M.ne(M.q(M.g(R.c())), M.c(0)),
    M.ev.frame(M.header(K.let_in(), M.q(M.g(R.c())), M.c(0)), 2n, 3n),
    M.do([
      M.set(R.y(), M.f(2n, M.g(R.c()))),
      M.one(R.y()),
      M.set(R.z(), M.f(3n, M.g(R.c()))),
      M.copy(R.n(), R.z()),
      M.release(R.wa()),
      M.dec(R.c()),
      M.set(R.focus(), M.g(R.n()))]))

# Tup q a b, not known to be a value: a in the frame Tup q □ b, when q is
# live; else b in the frame Tup q a □
def M.ev.tup() -> Cr.Cir.Stmt:
  M.if(M.ne(M.q(M.g(R.c())), M.c(0)),
    M.ev.frame(M.header(K.tup_b(), M.q(M.g(R.c())), M.c(0)), 2n, 3n),
    M.ev.frame(M.header(K.tup_a(), M.q(M.g(R.c())), M.c(0)), 3n, 2n))

# Rwt e P f: e, in the frame Rwt □ P f
def M.ev.rwt() -> Cr.Cir.Stmt:
  M.do([
    M.set(R.x(), M.f(2n, M.g(R.c()))),
    M.set(R.y(), M.f(3n, M.g(R.c()))),
    M.set(R.z(), M.f(4n, M.g(R.c()))),
    M.inc(R.x()),
    M.inc(R.y()),
    M.inc(R.z()),
    M.push(M.c(K.rwt()), M.g(R.y()), M.g(R.z())),
    M.dec(R.c()),
    M.set(R.focus(), M.g(R.x()))])

# Min a b: a, in the frame Min □ b
def M.ev.min() -> Cr.Cir.Stmt:
  M.ev.frame(M.c(K.min_b()), 2n, 3n)

# mode 0: a value by its form, or flagged one, is returned; a variable, free
# in the whole term, has no step
def M.ev() -> Cr.Cir.Stmt:
  M.do([
    M.set(R.c(), M.g(R.focus())),
    M.set(R.tag(), M.tag(M.g(R.c()))),
    M.if(M.or(M.flag(M.g(R.c()), F.value()), M.ne(M.entry(4n, M.g(R.c())), M.c(0))),
      M.set(R.mode(), M.c(1)),
    M.if(M.eq(M.g(R.tag()), M.c(T.app())), M.ev.app(),
    M.if(M.eq(M.g(R.tag()), M.c(T.ref())), M.ev.ref(),
    M.if(M.eq(M.g(R.tag()), M.c(T.ann())), M.ev.ann(),
    M.if(M.eq(M.g(R.tag()), M.c(T.let())), M.ev.let(),
    M.if(M.eq(M.g(R.tag()), M.c(T.tup())), M.ev.tup(),
    M.if(M.eq(M.g(R.tag()), M.c(T.rwt())), M.ev.rwt(),
    M.if(M.eq(M.g(R.tag()), M.c(T.min())), M.ev.min(),
      M.halt(2)))))))))])

# the frame in register h, whose term is in field 2, gets the focus there and
# the header hd; its term becomes the focus, to evaluate
def M.swap(hd: Cr.Cir.Expr) -> Cr.Cir.Stmt:
  M.do([
    M.set(R.n(), M.f(2n, M.g(R.h()))),
    M.st(0n, M.g(R.h()), hd),
    M.st(2n, M.g(R.h()), M.g(R.focus())),
    M.set(R.focus(), M.g(R.n())),
    M.set(R.mode(), M.c(0))])

# Let q □ f, with the value v: f with v put in, a step, when q may hold v
def M.ret.let() -> Cr.Cir.Stmt:
  M.do([
    M.set(R.wok(), M.c(1)),
    M.when(M.eq(M.g(R.q()), M.c(2)), M.do([
      M.data(R.focus()),
      M.set(R.wok(), M.g(R.dok()))])),
    M.need(M.g(R.wok()), M.do([
      M.set(R.z(), M.f(2n, M.g(R.h()))),
      M.pop(),
      M.one(R.focus()),
      M.copy(R.n(), R.z()),
      M.release(R.wa()),
      M.dec(R.focus()),
      M.dec(R.z()),
      M.set(R.focus(), M.g(R.n())),
      M.set(R.mode(), M.c(0))]))])

# Tup q a □, with the value v: the value Tup q a v
def M.ret.tup() -> Cr.Cir.Stmt:
  M.do([
    M.set(R.x(), M.f(2n, M.g(R.h()))),
    M.pop(),
    M.make(R.n(), M.or(M.header(T.tup(), M.g(R.q()), M.c(F.value())),
      M.shl(M.max(M.fv(M.g(R.x())), M.fv(M.g(R.focus()))), M.c(13))), M.g(R.x()), M.g(R.focus()), M.c(0)),
    M.set(R.focus(), M.g(R.n()))])

# Rwt □ P f, with the value v: f, a step, when v is Rfl
def M.ret.rwt() -> Cr.Cir.Stmt:
  M.need(M.eq(M.tag(M.g(R.focus())), M.c(T.rfl())), M.do([
    M.set(R.y(), M.f(2n, M.g(R.h()))),
    M.set(R.n(), M.f(3n, M.g(R.h()))),
    M.pop(),
    M.dec(R.y()),
    M.dec(R.focus()),
    M.set(R.focus(), M.g(R.n())),
    M.set(R.mode(), M.c(0))]))

# the name i is Q0, Q1 or Q2
def M.quan(+i: Cr.Cir.Expr) -> Cr.Cir.Expr:
  M.and(M.ge(i, M.c(N.q0())), M.le(i, M.c(N.q2())))

# the least of the quantities that the names i and j name: 2 below none, and
# 0 below all
def M.qmin(+i: Cr.Cir.Expr, +j: Cr.Cir.Expr) -> Cr.Cir.Expr:
  M.pick(M.eq(i, M.c(N.q2())), j,
    M.pick(M.eq(j, M.c(N.q2())), i,
      M.pick(M.or(M.eq(i, M.c(N.q0())), M.eq(j, M.c(N.q0()))), M.c(N.q0()), M.c(N.q1()))))

# Min a □, with the value v: the meet of a and v, a step, when both are labels
# of quantities
def M.ret.min() -> Cr.Cir.Stmt:
  M.do([
    M.set(R.x(), M.f(2n, M.g(R.h()))),
    M.pop(),
    M.need(M.and(M.eq(M.tag(M.g(R.x())), M.c(T.lab())), M.eq(M.tag(M.g(R.focus())), M.c(T.lab()))), M.do([
      M.set(R.p(), M.f(2n, M.g(R.x()))),
      M.set(R.k(), M.f(2n, M.g(R.focus()))),
      M.need(M.and(M.quan(M.g(R.p())), M.quan(M.g(R.k()))), M.do([
        M.set(R.n(), M.add(M.qmin(M.g(R.p()), M.g(R.k())), M.c(1))),
        M.dec(R.x()),
        M.dec(R.focus()),
        M.set(R.focus(), M.g(R.n())),
        M.set(R.mode(), M.c(0))]))]))])

# the cell in register r is a pair at quantity 1
def M.pair(+r: Nat) -> Cr.Cir.Expr:
  M.eq(M.and(M.f(0n, M.g(r)), M.c(255)), M.c(U32.or(T.tup(), 64)))

# the cell c is the label of the name i
def M.is_lab(+c: Cr.Cir.Expr, i: U32) -> Cr.Cir.Expr:
  M.and(M.eq(M.tag(c), M.c(T.lab())), M.eq(M.f(2n, c), M.c(i)))

# the pair in register r ends a constructor's fields: its second is ()
def M.last(+r: Nat) -> Cr.Cir.Expr:
  M.is_lab(M.f(3n, M.g(r)), N.unit())

# a bit of a word, in register t1: True or False, with no fields; ov gains
# 1 << oi when it is True
def M.out.bit() -> Cr.Cir.Stmt:
  M.need(M.pair(R.t1()), M.need(M.last(R.t1()),
    M.need(M.eq(M.tag(M.f(2n, M.g(R.t1()))), M.c(T.lab())), M.do([
      M.set(R.t2(), M.f(2n, M.f(2n, M.g(R.t1())))),
      M.need(M.or(M.eq(M.g(R.t2()), M.c(N.true())), M.eq(M.g(R.t2()), M.c(N.false()))),
        M.when(M.eq(M.g(R.t2()), M.c(N.true())),
          M.set(R.ov(), M.or(M.g(R.ov()), M.shl(M.c(1), M.g(R.oi()))))))]))))

# the byte in register ow, its 8 bits the lowest first, into ov
def M.out.byte() -> Cr.Cir.Stmt:
  M.do([
    M.set(R.ov(), M.c(0)),
    M.set(R.oi(), M.c(0)),
    M.while(M.lt(M.g(R.oi()), M.c(8)),
      M.need(M.pair(R.ow()), M.need(M.is_lab(M.f(2n, M.g(R.ow())), N.wcon()), M.do([
        M.set(R.ow(), M.f(3n, M.g(R.ow()))),
        M.need(M.pair(R.ow()), M.do([
          M.set(R.t1(), M.f(2n, M.g(R.ow()))),
          M.out.bit(),
          M.set(R.ow(), M.f(3n, M.g(R.ow()))),
          M.need(M.pair(R.ow()), M.need(M.last(R.ow()), M.do([
            M.set(R.ow(), M.f(2n, M.g(R.ow()))),
            M.set(R.oi(), M.add(M.g(R.oi()), M.c(1)))])))]))])))),
    M.need(M.pair(R.ow()), M.need(M.is_lab(M.f(2n, M.g(R.ow())), N.wnil()), M.need(M.last(R.ow()),
      Cr.Cir.Stmt.nop{})))])

# the cell of a list in register oc, Con: its byte goes out, and oc gets the
# rest of the list
def M.out.con() -> Cr.Cir.Stmt:
  M.do([
    M.set(R.oc(), M.f(3n, M.g(R.oc()))),
    M.need(M.pair(R.oc()), M.do([
      M.set(R.ow(), M.f(2n, M.g(R.oc()))),
      M.set(R.oc(), M.f(3n, M.g(R.oc()))),
      M.need(M.pair(R.oc()), M.need(M.last(R.oc()), M.do([
        M.set(R.oc(), M.f(2n, M.g(R.oc()))),
        M.out.byte(),
        Cr.Cir.Stmt.emit{M.g(R.ov())}])))]))])

# mode 1 with no frame: the run ends with the bytes of the value, when it is a
# list of bytes (Program.unbytes); else with no result
def M.out() -> Cr.Cir.Stmt:
  M.do([
    M.set(R.oc(), M.g(R.focus())),
    M.while(M.c(1),
      M.need(M.pair(R.oc()), M.need(M.eq(M.tag(M.f(2n, M.g(R.oc()))), M.c(T.lab())), M.do([
        M.set(R.ow(), M.f(2n, M.f(2n, M.g(R.oc())))),
        M.if(M.eq(M.g(R.ow()), M.c(N.nil())), M.need(M.last(R.oc()), M.halt(0)),
          M.need(M.eq(M.g(R.ow()), M.c(N.con())), M.out.con()))]))))])

# mode 1: the value v in the focus goes into the top frame
def M.ret() -> Cr.Cir.Stmt:
  M.if(M.eq(M.g(R.sp()), M.c(0)), M.out(), M.do([
    M.set(R.h(), M.g(R.sp())),
    M.set(R.tag(), M.tag(M.g(R.h()))),
    M.set(R.q(), M.q(M.g(R.h()))),
    M.if(M.or(M.eq(M.g(R.tag()), M.c(K.app_arg())), M.eq(M.g(R.tag()), M.c(K.app_val()))),
      M.if(M.and(M.ne(M.g(R.q()), M.c(0)), M.not(M.flag(M.g(R.h()), F.known()))),
        M.swap(M.header(K.app_fun(), M.g(R.q()), M.c(0))),
        M.do([
          M.set(R.x(), M.g(R.focus())),
          M.set(R.y(), M.f(2n, M.g(R.h()))),
          M.pop(),
          M.redex()])),
    M.if(M.eq(M.g(R.tag()), M.c(K.app_fun())), M.do([
      M.set(R.x(), M.f(2n, M.g(R.h()))),
      M.set(R.y(), M.g(R.focus())),
      M.pop(),
      M.redex()]),
    M.if(M.eq(M.g(R.tag()), M.c(K.let_in())), M.ret.let(),
    M.if(M.eq(M.g(R.tag()), M.c(K.tup_b())), M.swap(M.header(K.tup_a(), M.g(R.q()), M.c(0))),
    M.if(M.eq(M.g(R.tag()), M.c(K.tup_a())), M.ret.tup(),
    M.if(M.eq(M.g(R.tag()), M.c(K.rwt())), M.ret.rwt(),
    M.if(M.eq(M.g(R.tag()), M.c(K.min_b())), M.swap(M.c(K.min_a())),
      M.ret.min())))))))]))

# the header of a pair at quantity 1, a value and Data, that no count frees
def M.h.static() -> U32:
  1866

# the same, freed by its count
def M.h.data() -> U32:
  842

# the start of the run (Program.start): main, applied at quantity 1 to the
# list of the input's bytes, built from its last. A byte is made once, into
# the cache, and never freed: its 8 bits over the image's WNil
def M.input() -> Cr.Cir.Stmt:
  M.do([
    M.set(R.il(), M.c(I.nil())),
    M.set(R.ii(), Cr.Cir.Expr.size{}),
    M.while(M.ne(M.g(R.ii()), M.c(0)), M.do([
      M.set(R.ii(), M.sub(M.g(R.ii()), M.c(1))),
      M.set(R.ib(), Cr.Cir.Expr.byte{M.g(R.ii())}),
      M.set(R.iu(), M.f(2n, M.add(M.c(I.cache()), M.g(R.ib())))),
      M.when(M.eq(M.g(R.iu()), M.c(0)), M.do([
        M.set(R.iu(), M.c(I.wnil())),
        M.set(R.ij(), M.c(8)),
        M.while(M.ne(M.g(R.ij()), M.c(0)), M.do([
          M.set(R.ij(), M.sub(M.g(R.ij()), M.c(1))),
          M.make(R.t1(), M.c(M.h.static()), M.g(R.iu()), M.c(I.lab(N.unit())), M.c(0)),
          M.make(R.t2(), M.c(M.h.static()),
            M.pick(M.and(M.shr(M.g(R.ib()), M.g(R.ij())), M.c(1)), M.c(I.true()), M.c(I.false())),
            M.g(R.t1()), M.c(0)),
          M.make(R.iu(), M.c(M.h.static()), M.c(I.lab(N.wcon())), M.g(R.t2()), M.c(0))])),
        M.st(2n, M.add(M.c(I.cache()), M.g(R.ib())), M.g(R.iu()))])),
      M.make(R.t1(), M.c(M.h.data()), M.g(R.il()), M.c(I.lab(N.unit())), M.c(0)),
      M.make(R.t2(), M.c(M.h.data()), M.g(R.iu()), M.g(R.t1()), M.c(0)),
      M.make(R.il(), M.c(M.h.data()), M.c(I.lab(N.con())), M.g(R.t2()), M.c(0))])),
    M.make(R.focus(), M.c(U32.or(T.app(), 64)), M.c(I.ref_main()), M.g(R.il()), M.c(0))])

# the machine: the start, then a move per round, until a halt
def Mach.code() -> Cr.Cir.Stmt:
  M.do([
    M.input(),
    M.set(R.mode(), M.c(0)),
    M.while(M.c(1), M.if(M.eq(M.g(R.mode()), M.c(0)), M.ev(), M.ret()))])

# Image
# -----
#
# The cells that the module's memory holds from cell 1 (Mach.code's I.*):
# the labels of the names 0 to 9, constant terms, the cache of the input's
# bytes, the table by tag, then the bodies of the book's defs, each a tree of
# cells in pre-order. Each cell of the image is STATIC: no count frees it. A
# Ref holds the body of the first def of its name, as Book.get finds it, or
# 0; a Lab and a Mat hold the number of their name: the place of its first
# copy in a list of names whose first are the machine's (N.*).

# a def's name and the first cell of its body
type Img.Def is Data:
  Img.Def{k: List<&2, Word(8n)>, at: U32}

# the five fields of a cell, then acc
def Img.cell(f0: U32, f2: U32, f3: U32, f4: U32, acc: List<&2, Cr.Cir.Cell>) -> List<&2, Cr.Cir.Cell>:
  Con{Cr.Cir.Cell{f0, 0, f2, f3, f4}, acc}

def Img.quan(q: Bk.Quan) -> U32:
  match q:
    case Bk.Quan.Q0{}:
      0
    case Bk.Quan.Q1{}:
      1
    case Bk.Quan.Q2{}:
      2

# the nodes of a term, as a U32
def Img.size(t: Bk.Term) -> U32:
  match t:
    case Bk.Term.Var{_}:
      1
    case Bk.Term.Ref{_}:
      1
    case Bk.Term.Ann{x, T}:
      U32.inc(U32.add(Img.size(x), Img.size(T)))
    case Bk.Term.Let{_, v, f}:
      U32.inc(U32.add(Img.size(v), Img.size(f)))
    case Bk.Term.Typ{q}:
      U32.inc(Img.size(q))
    case Bk.Term.Min{a, b}:
      U32.inc(U32.add(Img.size(a), Img.size(b)))
    case Bk.Term.All{_, A, B}:
      U32.inc(U32.add(Img.size(A), Img.size(B)))
    case Bk.Term.Lam{_, f}:
      U32.inc(Img.size(f))
    case Bk.Term.App{_, f, x}:
      U32.inc(U32.add(Img.size(f), Img.size(x)))
    case Bk.Term.Sig{_, A, B}:
      U32.inc(U32.add(Img.size(A), Img.size(B)))
    case Bk.Term.Tup{_, a, b}:
      U32.inc(U32.add(Img.size(a), Img.size(b)))
    case Bk.Term.Prj{h}:
      U32.inc(Img.size(h))
    case Bk.Term.Enu{_}:
      1
    case Bk.Term.Lab{_}:
      1
    case Bk.Term.Mat{_, h, m}:
      U32.inc(U32.add(Img.size(h), Img.size(m)))
    case Bk.Term.Efq{}:
      1
    case Bk.Term.Eql{a, b, T}:
      U32.inc(U32.add(Img.size(a), U32.add(Img.size(b), Img.size(T))))
    case Bk.Term.Rfl{}:
      1
    case Bk.Term.Rwt{e, P, f}:
      U32.inc(U32.add(Img.size(e), U32.add(Img.size(P), Img.size(f))))

# fv of a part under k binders, as the cell that holds it counts it: fv_max
# stays fv_max
def Img.down(+fv: U32, +k: U32) -> U32:
  Bool.pick(U32, U32.is_eq(fv, 524287), 524287, Bool.pick(U32, U32.is_gt(fv, k), U32.sub(fv, k), 0))

# fv of a term: 1 + its highest free variable, 0 when it has none, at most
# fv_max (M.var, M.finish)
def Img.fv(t: Bk.Term) -> U32:
  match t:
    case Bk.Term.Var{i}:
      +u = U32.from_nat(i)
      Bool.pick(U32, U32.is_lt(u, 524286), U32.inc(u), 524287)
    case Bk.Term.Ref{_}:
      0
    case Bk.Term.Ann{x, T}:
      U32.max(Img.fv(x), Img.fv(T))
    case Bk.Term.Let{_, v, f}:
      U32.max(Img.fv(v), Img.down(Img.fv(f), 1))
    case Bk.Term.Typ{q}:
      Img.fv(q)
    case Bk.Term.Min{a, b}:
      U32.max(Img.fv(a), Img.fv(b))
    case Bk.Term.All{_, A, B}:
      U32.max(Img.fv(A), Img.down(Img.fv(B), 1))
    case Bk.Term.Lam{_, f}:
      Img.down(Img.fv(f), 1)
    case Bk.Term.App{_, f, x}:
      U32.max(Img.fv(f), Img.fv(x))
    case Bk.Term.Sig{_, A, B}:
      U32.max(Img.fv(A), Img.down(Img.fv(B), 1))
    case Bk.Term.Tup{_, a, b}:
      U32.max(Img.fv(a), Img.fv(b))
    case Bk.Term.Prj{h}:
      Img.fv(h)
    case Bk.Term.Enu{_}:
      0
    case Bk.Term.Lab{_}:
      0
    case Bk.Term.Mat{_, h, m}:
      U32.max(Img.fv(h), Img.fv(m))
    case Bk.Term.Efq{}:
      0
    case Bk.Term.Eql{a, b, T}:
      U32.max(Img.fv(a), U32.max(Img.fv(b), Img.fv(T)))
    case Bk.Term.Rfl{}:
      0
    case Bk.Term.Rwt{e, P, f}:
      U32.max(Img.fv(e), U32.max(Img.down(Img.fv(P), 2), Img.fv(f)))

# a value by its form alone, with no call in it: the image flags such a pair
# VALUE
def Img.is_value(t: Bk.Term) -> Bool:
  match t:
    case Bk.Term.Tup{q, a, b}:
      (Bool.not(El.Quan.live(q)) || Img.is_value(a)) && Img.is_value(b)
    case u:
      El.Term.is_former(u)

# a cell's field 0: the tag t, the quantity q, the flags fl and fv
def Img.header(+t: U32, +q: U32, +fl: U32, +fv: U32) -> U32:
  U32.or(U32.or(U32.or(t, U32.shln(q, 6n)), fl), U32.shln(fv, 13n))

# STATIC, with VALUE and DATA when they hold
def Img.flags(value: Bool, data: Bool) -> U32:
  U32.or(1024, U32.or(Bool.pick(U32, value, 256, 0), Bool.pick(U32, data, 512, 0)))

def Img.ref.if(b: Bool, +at: U32, more: Unit -> U32) -> U32:
  match b:
    case True{}:
      at
    case False{}:
      more(Unit{})

# the body of the first def of the name k, or 0 when there is none
def Img.ref(es: List<&2, Img.Def>, +k: List<&2, Word(8n)>) -> U32:
  match es:
    case Nil{}:
      0
    case Con{Img.Def{+n, +at}, rest}:
      Img.ref.if(Sd.Name.is_eq(n, k), at, u => Img.ref(rest, k))

# the number of the name k: the place of its first copy in ks, from i
def Img.id(ks: List<&2, List<&2, Word(8n)>>, +k: List<&2, Word(8n)>, +i: U32) -> U32:
  match ks:
    case Nil{}:
      i
    case Con{+n, rest}:
      Img.ref.if(Sd.Name.is_eq(n, k), i, u => Img.id(rest, k, U32.inc(i)))

# the cells of the term t from the cell at, then acc
def Img.term(t: Bk.Term, +ks: List<&2, List<&2, Word(8n)>>, +es: List<&2, Img.Def>, +at: U32, acc: List<&2, Cr.Cir.Cell>) ->
  List<&2, Cr.Cir.Cell>:
  match t:
    case Bk.Term.Var{+i}:
      Img.cell(Img.header(T.var(), 0, 1024, Img.fv(Bk.Term.Var{i})), U32.from_nat(i), 0, 0, acc)
    case Bk.Term.Ref{+k}:
      Img.cell(Img.header(T.ref(), 0, 1024, 0), Img.ref(es, k), 0, 0, acc)
    case Bk.Term.Ann{+x, +T}:
      +a = U32.inc(at)
      +b = U32.add(a, Img.size(x))
      Img.cell(Img.header(T.ann(), 0, 1024, Img.fv(Bk.Term.Ann{x, T})), a, b, 0,
        Img.term(x, ks, es, a, Img.term(T, ks, es, b, acc)))
    case Bk.Term.Let{+q, +v, +f}:
      +a = U32.inc(at)
      +b = U32.add(a, Img.size(v))
      Img.cell(Img.header(T.let(), Img.quan(q), 1024, Img.fv(Bk.Term.Let{q, v, f})), a, b, 0,
        Img.term(v, ks, es, a, Img.term(f, ks, es, b, acc)))
    case Bk.Term.Typ{+x}:
      +a = U32.inc(at)
      Img.cell(Img.header(4, 0, 1024, Img.fv(x)), a, 0, 0, Img.term(x, ks, es, a, acc))
    case Bk.Term.Min{+x, +y}:
      +a = U32.inc(at)
      +b = U32.add(a, Img.size(x))
      Img.cell(Img.header(T.min(), 0, 1024, Img.fv(Bk.Term.Min{x, y})), a, b, 0,
        Img.term(x, ks, es, a, Img.term(y, ks, es, b, acc)))
    case Bk.Term.All{+q, +A, +B}:
      +a = U32.inc(at)
      +b = U32.add(a, Img.size(A))
      Img.cell(Img.header(6, Img.quan(q), 1024, Img.fv(Bk.Term.All{q, A, B})), a, b, 0,
        Img.term(A, ks, es, a, Img.term(B, ks, es, b, acc)))
    case Bk.Term.Lam{+q, +f}:
      +a = U32.inc(at)
      Img.cell(Img.header(T.lam(), Img.quan(q), 1024, Img.fv(Bk.Term.Lam{q, f})), a, 0, 0,
        Img.term(f, ks, es, a, acc))
    case Bk.Term.App{+q, +f, +x}:
      +a = U32.inc(at)
      +b = U32.add(a, Img.size(f))
      Img.cell(Img.header(T.app(), Img.quan(q), 1024, Img.fv(Bk.Term.App{q, f, x})), a, b, 0,
        Img.term(f, ks, es, a, Img.term(x, ks, es, b, acc)))
    case Bk.Term.Sig{+q, +A, +B}:
      +a = U32.inc(at)
      +b = U32.add(a, Img.size(A))
      Img.cell(Img.header(9, Img.quan(q), 1024, Img.fv(Bk.Term.Sig{q, A, B})), a, b, 0,
        Img.term(A, ks, es, a, Img.term(B, ks, es, b, acc)))
    case Bk.Term.Tup{+q, +x, +y}:
      +a = U32.inc(at)
      +b = U32.add(a, Img.size(x))
      Img.cell(Img.header(T.tup(), Img.quan(q),
          Img.flags(Img.is_value(Bk.Term.Tup{q, x, y}), El.Term.is_data(Bk.Term.Tup{q, x, y})), Img.fv(Bk.Term.Tup{q, x, y})),
        a, b, 0, Img.term(x, ks, es, a, Img.term(y, ks, es, b, acc)))
    case Bk.Term.Prj{+h}:
      +a = U32.inc(at)
      Img.cell(Img.header(T.prj(), 0, 1024, Img.fv(h)), a, 0, 0, Img.term(h, ks, es, a, acc))
    case Bk.Term.Enu{_}:
      Img.cell(Img.header(12, 0, 1024, 0), 0, 0, 0, acc)
    case Bk.Term.Lab{+k}:
      Img.cell(Img.header(T.lab(), 0, 1536, 0), Img.id(ks, k, 0), 0, 0, acc)
    case Bk.Term.Mat{+k, +h, +m}:
      +a = U32.inc(at)
      +b = U32.add(a, Img.size(h))
      Img.cell(Img.header(T.mat(), 0, 1024, Img.fv(Bk.Term.Mat{k, h, m})), Img.id(ks, k, 0), a, b,
        Img.term(h, ks, es, a, Img.term(m, ks, es, b, acc)))
    case Bk.Term.Efq{}:
      Img.cell(Img.header(T.efq(), 0, 1024, 0), 0, 0, 0, acc)
    case Bk.Term.Eql{+x, +y, +T}:
      +a = U32.inc(at)
      +b = U32.add(a, Img.size(x))
      +c = U32.add(b, Img.size(y))
      Img.cell(Img.header(16, 0, 1024, Img.fv(Bk.Term.Eql{x, y, T})), a, b, c,
        Img.term(x, ks, es, a, Img.term(y, ks, es, b, Img.term(T, ks, es, c, acc))))
    case Bk.Term.Rfl{}:
      Img.cell(Img.header(T.rfl(), 0, 1536, 0), 0, 0, 0, acc)
    case Bk.Term.Rwt{+e, +P, +f}:
      +a = U32.inc(at)
      +b = U32.add(a, Img.size(e))
      +c = U32.add(b, Img.size(P))
      Img.cell(Img.header(T.rwt(), 0, 1024, Img.fv(Bk.Term.Rwt{e, P, f})), a, b, c,
        Img.term(e, ks, es, a, Img.term(P, ks, es, b, Img.term(f, ks, es, c, acc))))

# the names of the labels and λ-matches of t, then acc
def Img.names(t: Bk.Term, acc: List<&2, List<&2, Word(8n)>>) -> List<&2, List<&2, Word(8n)>>:
  match t:
    case Bk.Term.Var{_}:
      acc
    case Bk.Term.Ref{_}:
      acc
    case Bk.Term.Ann{x, T}:
      Img.names(x, Img.names(T, acc))
    case Bk.Term.Let{_, v, f}:
      Img.names(v, Img.names(f, acc))
    case Bk.Term.Typ{q}:
      Img.names(q, acc)
    case Bk.Term.Min{a, b}:
      Img.names(a, Img.names(b, acc))
    case Bk.Term.All{_, A, B}:
      Img.names(A, Img.names(B, acc))
    case Bk.Term.Lam{_, f}:
      Img.names(f, acc)
    case Bk.Term.App{_, f, x}:
      Img.names(f, Img.names(x, acc))
    case Bk.Term.Sig{_, A, B}:
      Img.names(A, Img.names(B, acc))
    case Bk.Term.Tup{_, a, b}:
      Img.names(a, Img.names(b, acc))
    case Bk.Term.Prj{h}:
      Img.names(h, acc)
    case Bk.Term.Enu{_}:
      acc
    case Bk.Term.Lab{k}:
      Con{k, acc}
    case Bk.Term.Mat{k, h, m}:
      Con{k, Img.names(h, Img.names(m, acc))}
    case Bk.Term.Efq{}:
      acc
    case Bk.Term.Eql{a, b, T}:
      Img.names(a, Img.names(b, Img.names(T, acc)))
    case Bk.Term.Rfl{}:
      acc
    case Bk.Term.Rwt{e, P, f}:
      Img.names(e, Img.names(P, Img.names(f, acc)))

# the names of the bodies of ds
def Img.names.defs(ds: List<&2, Bk.Def>) -> List<&2, List<&2, Word(8n)>>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{Bk.Def{_, _, v, _}, rest}:
      Img.names(v, Img.names.defs(rest))

# the names that the machine knows (N.*), in front of the book's
def Img.known(ks: List<&2, List<&2, Word(8n)>>) -> List<&2, List<&2, Word(8n)>>:
  Con{Pg.Program.name.unit(), Con{Pg.Program.name.nil(), Con{Pg.Program.name.con(), Con{Pg.Program.name.wnil(),
    Con{Pg.Program.name.wcon(), Con{Pg.Program.name.true(), Con{Pg.Program.name.false(), Con{El.Quan.name(Bk.Quan.Q0{}),
    Con{El.Quan.name(Bk.Quan.Q1{}), Con{El.Quan.name(Bk.Quan.Q2{}), Con{Pg.Program.name.main(), ks}}}}}}}}}}}

# each def's name and the first cell of its body, from the cell at
def Img.defs(ds: List<&2, Bk.Def>, +at: U32) -> List<&2, Img.Def>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{Bk.Def{k, _, v, _}, rest}:
      Con{Img.Def{k, at}, Img.defs(rest, U32.add(at, Img.size(v)))}

# the cells of the bodies of ds, from the cell at, then acc
def Img.bodies(ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +es: List<&2, Img.Def>, +at: U32) ->
  List<&2, Cr.Cir.Cell>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{Bk.Def{_, _, +v, _}, rest}:
      Img.term(v, ks, es, at, Img.bodies(rest, ks, es, U32.add(at, Img.size(v))))

# the cells of the image: n labels, from the name i
def Img.labels(n: Nat, +i: U32, acc: List<&2, Cr.Cir.Cell>) -> List<&2, Cr.Cir.Cell>:
  match n:
    case 0n:
      acc
    case 1n+m:
      Img.cell(1549, i, 0, 0, Img.labels(m, U32.inc(i), acc))

# a pair at quantity 1, a value and Data
def Img.pair(a: U32, b: U32, acc: List<&2, Cr.Cir.Cell>) -> List<&2, Cr.Cir.Cell>:
  Img.cell(1866, a, b, 0, acc)

# n cells of zeros
def Img.blank(n: Nat, acc: List<&2, Cr.Cir.Cell>) -> List<&2, Cr.Cir.Cell>:
  match n:
    case 0n:
      acc
    case 1n+m:
      Img.cell(0, 0, 0, 0, Img.blank(m, acc))

# the table by tag (I.table): the mask of the pointers, the binders above
# each, and 1 for a former
def Img.table(acc: List<&2, Cr.Cir.Cell>) -> List<&2, Cr.Cir.Cell>:
  Img.cell(0, 0, 0, 0, Img.cell(0, 0, 0, 0, Img.cell(0, 3, 0, 0, Img.cell(0, 3, 4, 0,
  Img.cell(0, 1, 0, 1, Img.cell(0, 3, 0, 0, Img.cell(0, 3, 4, 1, Img.cell(0, 1, 1, 1,
  Img.cell(0, 3, 0, 0, Img.cell(0, 3, 4, 1, Img.cell(0, 3, 0, 0, Img.cell(0, 1, 0, 1,
  Img.cell(0, 0, 0, 1, Img.cell(0, 0, 0, 1, Img.cell(0, 6, 0, 1, Img.cell(0, 0, 0, 1,
  Img.cell(0, 7, 0, 1, Img.cell(0, 0, 0, 1, Img.cell(0, 7, 8, 0, acc)))))))))))))))))))

# cells 1 to 290 (I.*), with main's body at the cell main, then acc
def Img.prefix(main: U32, acc: List<&2, Cr.Cir.Cell>) -> List<&2, Cr.Cir.Cell>:
  Img.labels(10n, 0,
    Img.pair(I.lab(N.nil()), I.lab(N.unit()), Img.pair(I.lab(N.true()), I.lab(N.unit()),
    Img.pair(I.lab(N.false()), I.lab(N.unit()), Img.pair(I.lab(N.wnil()), I.lab(N.unit()),
      Img.cell(1025, main, N.main(), 0,
        Img.blank(256n, Img.table(acc))))))))

# the cells of the image of the book ds
def Img.cells(+ds: List<&2, Bk.Def>) -> List<&2, Cr.Cir.Cell>:
  +ks = Img.known(Img.names.defs(ds))
  +es = Img.defs(ds, I.book())
  Img.prefix(Img.ref(es, Pg.Program.name.main()), Img.bodies(ds, ks, es, I.book()))

def Img.small.if(full: Bool, more: Unit -> Bool) -> Bool:
  match full:
    case True{}:
      False{}
    case False{}:
      more(Unit{})

# the book's bytes are fewer than 2^26 from the n-th: enough for its numbers
# (cells, names, variables) to fit in a U32. Each token of 2 bytes adds 3 nodes
# or more to the book's data form, so a book of more bytes has a size above
# 2^26, and F above 2^32 bytes: more than a module can have
def Img.small(xs: List<&2, Word(8n)>, +n: U32) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{_, rest}:
      Img.small.if(U32.is_eq(n, 67108863), u => Img.small(rest, U32.inc(n)))
