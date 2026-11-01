# compiler: the terms of the machine's cells, for layer B
# =======================================================
#
# The term that a cell of the machine (impl.bend, Machine) stands for, and
# the term of a whole state: its frames around its focus, as the Lean
# machine's plugs puts them (lean, Interpreter/Machine.lean). Layer B relates
# these terms to Eval's steps.
#
# A cell's tag (bits 0 to 5 of field 0), its quantity (bits 6 and 7) and
# its parts (fields 2 to 4, by the table of the image) give its term. A
# label's or a λ-match's name is the name of its number in the image's list
# of names ks. A Ref or an Enu has no free variable, so a copy shares it and
# never makes one: its term is the one at its place in the image, in the
# list img (img's first is cell 1).

import Base
import ../../Book/impl.bend as Bk
import ../../Program/impl.bend as Pg
import ../Cir/impl.bend as Cr
import ./impl.bend as Mc

def tm.quan(+q: U32) -> Bk.Quan:
  Bool.pick(Bk.Quan, U32.is_eq(q, 0), Bk.Quan.Q0{}, Bool.pick(Bk.Quan, U32.is_eq(q, 1), Bk.Quan.Q1{}, Bk.Quan.Q2{}))

# the name of the number i, in the image's list ks
def tm.name(ks: List<&2, List<&2, Word(8n)>>, +i: U32) -> Maybe<&2, List<&2, Word(8n)>>:
  List.get(&2, List<&2, Word(8n)>, ks, U32.to_nat(i))

# the term at the cell c of the image img
def tm.image(img: List<&2, Bk.Term>, +c: U32) -> Maybe<&2, Bk.Term>:
  List.get(&2, Bk.Term, img, U32.to_nat(U32.sub(c, 1)))

def tm.one(k: Bk.Term -> Bk.Term, r: Maybe<&2, Bk.Term>) -> Maybe<&2, Bk.Term>:
  match r:
    case None{}:
      None{}
    case Some{a}:
      Some{k(a)}

def tm.two(k: Bk.Term -> Bk.Term -> Bk.Term, r: Maybe<&2, Bk.Term>, s: Maybe<&2, Bk.Term>) -> Maybe<&2, Bk.Term>:
  match r s:
    case Some{a} Some{b}:
      Some{k(a, b)}
    case _ _:
      None{}

def tm.three(k: Bk.Term -> Bk.Term -> Bk.Term -> Bk.Term, r: Maybe<&2, Bk.Term>, s: Maybe<&2, Bk.Term>,
  t: Maybe<&2, Bk.Term>) -> Maybe<&2, Bk.Term>:
  match r s t:
    case Some{a} Some{b} Some{c}:
      Some{k(a, b, c)}
    case _ _ _:
      None{}

def tm.named(n: Maybe<&2, List<&2, Word(8n)>>, k: List<&2, Word(8n)> -> Bk.Term) -> Maybe<&2, Bk.Term>:
  match n:
    case None{}:
      None{}
    case Some{x}:
      Some{k(x)}

def tm.mat(n: Maybe<&2, List<&2, Word(8n)>>, r: Maybe<&2, Bk.Term>, s: Maybe<&2, Bk.Term>) -> Maybe<&2, Bk.Term>:
  match n r s:
    case Some{k} Some{h} Some{m}:
      Some{Bk.Term.Mat{k, h, m}}
    case _ _ _:
      None{}

# the term of the cell c of the tag tag, the quantity q and field 2 f2; p2,
# p3 and p4 read the terms of its parts, only where the tag has them; none
# for a cell that is no term
def tm.cell(tag: Nat, +q: Bk.Quan, +c: U32, +f2: U32, ks: List<&2, List<&2, Word(8n)>>, img: List<&2, Bk.Term>,
  p2: Unit -> Maybe<&2, Bk.Term>, p3: Unit -> Maybe<&2, Bk.Term>, p4: Unit -> Maybe<&2, Bk.Term>) -> Maybe<&2, Bk.Term>:
  match tag:
    case 0n:
      Some{Bk.Term.Var{U32.to_nat(f2)}}
    case 1n:
      tm.image(img, c)
    case 2n:
      tm.two(a => b => Bk.Term.Ann{a, b}, p2(Unit{}), p3(Unit{}))
    case 3n:
      tm.two(a => b => Bk.Term.Let{q, a, b}, p2(Unit{}), p3(Unit{}))
    case 4n:
      tm.one(a => Bk.Term.Typ{a}, p2(Unit{}))
    case 5n:
      tm.two(a => b => Bk.Term.Min{a, b}, p2(Unit{}), p3(Unit{}))
    case 6n:
      tm.two(a => b => Bk.Term.All{q, a, b}, p2(Unit{}), p3(Unit{}))
    case 7n:
      tm.one(a => Bk.Term.Lam{q, a}, p2(Unit{}))
    case 8n:
      tm.two(a => b => Bk.Term.App{q, a, b}, p2(Unit{}), p3(Unit{}))
    case 9n:
      tm.two(a => b => Bk.Term.Sig{q, a, b}, p2(Unit{}), p3(Unit{}))
    case 10n:
      tm.two(a => b => Bk.Term.Tup{q, a, b}, p2(Unit{}), p3(Unit{}))
    case 11n:
      tm.one(a => Bk.Term.Prj{a}, p2(Unit{}))
    case 12n:
      tm.image(img, c)
    case 13n:
      tm.named(tm.name(ks, f2), k => Bk.Term.Lab{k})
    case 14n:
      tm.mat(tm.name(ks, f2), p3(Unit{}), p4(Unit{}))
    case 15n:
      Some{Bk.Term.Efq{}}
    case 16n:
      tm.three(a => b => t => Bk.Term.Eql{a, b, t}, p2(Unit{}), p3(Unit{}), p4(Unit{}))
    case 17n:
      Some{Bk.Term.Rfl{}}
    case 18n:
      tm.three(a => b => t => Bk.Term.Rwt{a, b, t}, p2(Unit{}), p3(Unit{}), p4(Unit{}))
    case _:
      None{}

# the term of the cell c of the cells m, read at most fuel levels deep; none
# when the fuel ends first, or for a cell that is no term
def tm.of(fuel: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +c: U32) ->
  Maybe<&2, Bk.Term>:
  match fuel:
    case 0n:
      None{}
    case 1n++f:
      +cell = Cr.Cir.Cells.get(m, c)
      +f0 = Cr.Cir.Cell.get(0n, cell)
      tm.cell(U32.to_nat(U32.and(f0, 63)), tm.quan(U32.and(U32.shrn(f0, 6n), 3)), c, Cr.Cir.Cell.get(2n, cell), ks, img,
        u => tm.of(f, m, ks, img, Cr.Cir.Cell.get(2n, cell)), u => tm.of(f, m, ks, img, Cr.Cir.Cell.get(3n, cell)),
        u => tm.of(f, m, ks, img, Cr.Cir.Cell.get(4n, cell)))

def tm.bind(r: Maybe<&2, Bk.Term>, more: Bk.Term -> Maybe<&2, Bk.Term>) -> Maybe<&2, Bk.Term>:
  match r:
    case None{}:
      None{}
    case Some{u}:
      more(u)

# a frame of the kind kind (K.app_arg to K.min_a) and the quantity q, whose
# fields 2 and 3 have the terms a and b, with t in its hole
def tm.plug(kind: Nat, +q: Bk.Quan, a: Maybe<&2, Bk.Term>, b: Maybe<&2, Bk.Term>, t: Bk.Term) -> Maybe<&2, Bk.Term>:
  match kind:
    case 32n:
      tm.one(x => Bk.Term.App{q, t, x}, a)
    case 33n:
      tm.one(x => Bk.Term.App{q, t, x}, a)
    case 34n:
      tm.one(x => Bk.Term.App{q, x, t}, a)
    case 35n:
      tm.one(x => Bk.Term.Let{q, t, x}, a)
    case 36n:
      tm.one(x => Bk.Term.Tup{q, t, x}, a)
    case 37n:
      tm.one(x => Bk.Term.Tup{q, x, t}, a)
    case 38n:
      tm.two(x => y => Bk.Term.Rwt{t, x, y}, a, b)
    case 39n:
      tm.one(x => Bk.Term.Min{t, x}, a)
    case 40n:
      tm.one(x => Bk.Term.Min{x, t}, a)
    case _:
      None{}

def tm.plugs.if(top: Bool, t: Bk.Term, kind: Nat, +q: Bk.Quan, a: Maybe<&2, Bk.Term>, b: Maybe<&2, Bk.Term>,
  more: Bk.Term -> Maybe<&2, Bk.Term>) -> Maybe<&2, Bk.Term>:
  match top:
    case True{}:
      Some{t}
    case False{}:
      tm.bind(tm.plug(kind, q, a, b, t), more)

# the frames from the cell fr on (each links the next by field 1, the
# innermost first; 0 ends them), with t in the innermost's hole
def tm.plugs(fuel: Nat, +m: Cr.Cir.Cells, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +fr: U32,
  t: Bk.Term) -> Maybe<&2, Bk.Term>:
  match fuel:
    case 0n:
      None{}
    case 1n++f:
      +cell = Cr.Cir.Cells.get(m, fr)
      +f0 = Cr.Cir.Cell.get(0n, cell)
      tm.plugs.if(U32.is_zero(fr), t, U32.to_nat(U32.and(f0, 63)), tm.quan(U32.and(U32.shrn(f0, 6n), 3)),
        tm.of(f, m, ks, img, Cr.Cir.Cell.get(2n, cell)), tm.of(f, m, ks, img, Cr.Cir.Cell.get(3n, cell)),
        u => tm.plugs(f, m, ks, img, Cr.Cir.Cell.get(1n, cell), u))

# the register r of regs, 0 when there is none
def tm.reg(regs: List<&2, U32>, +r: Nat) -> U32:
  Maybe.default(&2, U32, List.get(&2, U32, regs, r), 0)

# the term of a state of the machine: its frames (from register sp) around
# its focus (register focus)
def tm.state(+fuel: Nat, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, st: Cr.Cir.State) ->
  Maybe<&2, Bk.Term>:
  match st:
    case Cr.Cir.State{+regs, +cells, _, _, _, _, _, _, _, _}:
      tm.bind(tm.of(fuel, cells, ks, img, tm.reg(regs, Mc.R.focus())),
        t => tm.plugs(fuel, cells, ks, img, tm.reg(regs, Mc.R.sp()), t))

# the nodes of t in pre-order, as Img.term lays out their cells, then acc
def tm.pre(+t: Bk.Term, acc: List<&2, Bk.Term>) -> List<&2, Bk.Term>:
  match t:
    case Bk.Term.Var{_}:
      Con{t, acc}
    case Bk.Term.Ref{_}:
      Con{t, acc}
    case Bk.Term.Ann{+x, +T}:
      Con{t, tm.pre(x, tm.pre(T, acc))}
    case Bk.Term.Let{_, +v, +f}:
      Con{t, tm.pre(v, tm.pre(f, acc))}
    case Bk.Term.Typ{+q}:
      Con{t, tm.pre(q, acc)}
    case Bk.Term.Min{+a, +b}:
      Con{t, tm.pre(a, tm.pre(b, acc))}
    case Bk.Term.All{_, +A, +B}:
      Con{t, tm.pre(A, tm.pre(B, acc))}
    case Bk.Term.Lam{_, +f}:
      Con{t, tm.pre(f, acc)}
    case Bk.Term.App{_, +f, +x}:
      Con{t, tm.pre(f, tm.pre(x, acc))}
    case Bk.Term.Sig{_, +A, +B}:
      Con{t, tm.pre(A, tm.pre(B, acc))}
    case Bk.Term.Tup{_, +a, +b}:
      Con{t, tm.pre(a, tm.pre(b, acc))}
    case Bk.Term.Prj{+h}:
      Con{t, tm.pre(h, acc)}
    case Bk.Term.Enu{_}:
      Con{t, acc}
    case Bk.Term.Lab{_}:
      Con{t, acc}
    case Bk.Term.Mat{_, +h, +m}:
      Con{t, tm.pre(h, tm.pre(m, acc))}
    case Bk.Term.Efq{}:
      Con{t, acc}
    case Bk.Term.Eql{+a, +b, +T}:
      Con{t, tm.pre(a, tm.pre(b, tm.pre(T, acc)))}
    case Bk.Term.Rfl{}:
      Con{t, acc}
    case Bk.Term.Rwt{+e, +P, +f}:
      Con{t, tm.pre(e, tm.pre(P, tm.pre(f, acc)))}

def tm.bodies(ds: List<&2, Bk.Def>) -> List<&2, Bk.Term>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{Bk.Def{_, _, +v, _}, rest}:
      tm.pre(v, tm.bodies(rest))

# the terms of the image's cells, by place: the fixed cells (only the Ref of
# main, cell 15, is a Ref or an Enu; the others never look here), then the
# nodes of the bodies, as Img.cells lays them out
def tm.img(ds: List<&2, Bk.Def>) -> List<&2, Bk.Term>:
  List.append(&2, Bk.Term, List.replicate(Bk.Term, 14n, Bk.Term.Efq{}),
    Con{Bk.Term.Ref{Pg.Program.name.main()},
      List.append(&2, Bk.Term, List.replicate(Bk.Term, 275n, Bk.Term.Efq{}), tm.bodies(ds))})

# the image's names: the machine's own, then the book's (Img.cells)
def tm.names(ds: List<&2, Bk.Def>) -> List<&2, List<&2, Word(8n)>>:
  Mc.Img.known(Mc.Img.names.defs(ds))
