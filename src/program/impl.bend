import Base
import ../shared/shared.bend as Sd
import ../book/impl.bend as Bk
import ../eval/impl.bend as El
import ../wasm/impl.bend as Wa

# Program
# =======
#
# What a program gives on its input (AGENTS.md 3.4.3), and the memory that the
# laws of 3.7.4 (compiler/spec.bend) grant it (3.4.4, 3.8.1.4). The terms mirror
# lean/src/Bootstrap/DataForm/Bytes.lean, and Program.gives mirrors Gives in
# Interpreter/Program.lean, so that the proof of 3.7.6 can join them.

# the names of the constructors of a list of bytes, as `bend -o` writes them
def Program.name.unit() -> List<&2, Word(8n)>:
  [Sd.Byte.from_u32(40), Sd.Byte.from_u32(41)]

def Program.name.nil() -> List<&2, Word(8n)>:
  [Sd.Byte.from_u32(78), Sd.Byte.from_u32(105), Sd.Byte.from_u32(108)]

def Program.name.con() -> List<&2, Word(8n)>:
  [Sd.Byte.from_u32(67), Sd.Byte.from_u32(111), Sd.Byte.from_u32(110)]

def Program.name.wnil() -> List<&2, Word(8n)>:
  [Sd.Byte.from_u32(87), Sd.Byte.from_u32(78), Sd.Byte.from_u32(105), Sd.Byte.from_u32(108)]

def Program.name.wcon() -> List<&2, Word(8n)>:
  [Sd.Byte.from_u32(87), Sd.Byte.from_u32(67), Sd.Byte.from_u32(111), Sd.Byte.from_u32(110)]

def Program.name.true() -> List<&2, Word(8n)>:
  [Sd.Byte.from_u32(84), Sd.Byte.from_u32(114), Sd.Byte.from_u32(117), Sd.Byte.from_u32(101)]

def Program.name.false() -> List<&2, Word(8n)>:
  [Sd.Byte.from_u32(70), Sd.Byte.from_u32(97), Sd.Byte.from_u32(108), Sd.Byte.from_u32(115), Sd.Byte.from_u32(101)]

def Program.name.main() -> List<&2, Word(8n)>:
  [Sd.Byte.from_u32(109), Sd.Byte.from_u32(97), Sd.Byte.from_u32(105), Sd.Byte.from_u32(110)]

# the fields of a constructor: each paired at quantity 1 with the rest, and ()
# at the end
def Program.fields(fs: List<&2, Bk.Term>) -> Bk.Term:
  match fs:
    case Nil{}:
      Bk.Term.Lab{Program.name.unit()}
    case Con{f, rest}:
      Bk.Term.Tup{Bk.Quan.Q1{}, f, Program.fields(rest)}

# the constructor k with the fields fs, as `bend -o` writes a value
def Program.ctor(k: List<&2, Word(8n)>, fs: List<&2, Bk.Term>) -> Bk.Term:
  Bk.Term.Tup{Bk.Quan.Q1{}, Bk.Term.Lab{k}, Program.fields(fs)}

def Program.bit(b: Bool) -> Bk.Term:
  match b:
    case True{}:
      Program.ctor(Program.name.true(), [])
    case False{}:
      Program.ctor(Program.name.false(), [])

# a Word(n), its lowest bit first
def Program.word(n: Nat, w: Word(n)) -> Bk.Term:
  match n:
    case 0n:
      Program.ctor(Program.name.wnil(), [])
    case 1n+p:
      match w:
        case WCon{b, t}:
          Program.ctor(Program.name.wcon(), [Program.bit(b), Program.word(p, t)])

# a list of bytes, as Base's List<&2, Word(8n)>
def Program.bytes(i: List<&2, Word(8n)>) -> Bk.Term:
  match i:
    case Nil{}:
      Program.ctor(Program.name.nil(), [])
    case Con{b, rest}:
      Program.ctor(Program.name.con(), [Program.word(8n, b), Program.bytes(rest)])

# the start term of a run (AGENTS.md 3.2.3): main, applied once at quantity 1 to the
# input's bytes
def Program.start(i: List<&2, Word(8n)>) -> Bk.Term:
  Bk.Term.App{Bk.Quan.Q1{}, Bk.Term.Ref{Program.name.main()}, Program.bytes(i)}

def Program.unbit.if(is_true: Bool, is_false: Bool) -> Maybe<&2, Bool>:
  match is_true is_false:
    case True{} _:
      Some{True{}}
    case False{} True{}:
      Some{False{}}
    case False{} False{}:
      None{}

# the Bool of a constructor's name
def Program.unbit(+k: List<&2, Word(8n)>) -> Maybe<&2, Bool>:
  Program.unbit.if(Sd.Name.is_eq(k, Program.name.true()), Sd.Name.is_eq(k, Program.name.false()))

def Program.unword.nil(ok: Bool) -> Maybe<&2, Word(0n)>:
  match ok:
    case True{}:
      Some{WNil{}}
    case False{}:
      None{}

def Program.unword.con(-p: Nat, ok: Bool, b: Maybe<&2, Bool>, w: Maybe<&2, Word(p)>) ->
  Maybe<&2, Word(1n+p)>:
  match ok b w:
    case True{} Some{x} Some{t}:
      Some{WCon{x, t}}
    case _ _ _:
      None{}

# the Word(n) that Program.word gives the term of; nothing for any other term
def Program.unword(n: Nat, t: Bk.Term) -> Maybe<&2, Word(n)>:
  match n:
    case 0n:
      match t:
        case Bk.Term.Tup{Bk.Quan.Q1{}, Bk.Term.Lab{+k}, Bk.Term.Lab{+u}}:
          Program.unword.nil(Sd.Name.is_eq(k, Program.name.wnil()) && Sd.Name.is_eq(u, Program.name.unit()))
        case _:
          None{}
    case 1n+p:
      match t:
        case Bk.Term.Tup{Bk.Quan.Q1{}, Bk.Term.Lab{+k},
            Bk.Term.Tup{Bk.Quan.Q1{}, Bk.Term.Tup{Bk.Quan.Q1{}, Bk.Term.Lab{+b}, Bk.Term.Lab{+u1}}, Bk.Term.Tup{Bk.Quan.Q1{}, w, Bk.Term.Lab{+u2}}}}:
          Program.unword.con(p,
            Sd.Name.is_eq(k, Program.name.wcon()) && Sd.Name.is_eq(u1, Program.name.unit()) && Sd.Name.is_eq(u2, Program.name.unit()),
            Program.unbit(b), Program.unword(p, w))
        case _:
          None{}

def Program.unbytes.nil(ok: Bool) -> Maybe<&2, List<&2, Word(8n)>>:
  match ok:
    case True{}:
      Some{Nil{}}
    case False{}:
      None{}

def Program.unbytes.con(ok: Bool, w: Maybe<&2, Word(8n)>, bs: Maybe<&2, List<&2, Word(8n)>>) ->
  Maybe<&2, List<&2, Word(8n)>>:
  match ok w bs:
    case True{} Some{x} Some{rest}:
      Some{Con{x, rest}}
    case _ _ _:
      None{}

# the list of bytes that Program.bytes gives the term of; nothing for any
# other term
def Program.unbytes(t: Bk.Term) -> Maybe<&2, List<&2, Word(8n)>>:
  match t:
    case Bk.Term.Tup{Bk.Quan.Q1{}, Bk.Term.Lab{+k}, Bk.Term.Lab{+u}}:
      Program.unbytes.nil(Sd.Name.is_eq(k, Program.name.nil()) && Sd.Name.is_eq(u, Program.name.unit()))
    case Bk.Term.Tup{Bk.Quan.Q1{}, Bk.Term.Lab{+k}, Bk.Term.Tup{Bk.Quan.Q1{}, w, Bk.Term.Tup{Bk.Quan.Q1{}, rest, Bk.Term.Lab{+u}}}}:
      Program.unbytes.con(Sd.Name.is_eq(k, Program.name.con()) && Sd.Name.is_eq(u, Program.name.unit()),
        Program.unword(8n, w), Program.unbytes(rest))
    case _:
      None{}

def Program.result.if(ok: Bool, v: Bk.Term) -> Maybe<&2, List<&2, Word(8n)>>:
  match ok:
    case True{}:
      Program.unbytes(v)
    case False{}:
      None{}

# the bytes at the end r of a run, when it is a value that is a list of bytes
def Program.result(ds: List<&2, Bk.Def>, r: Maybe<Bk.Term>) -> Maybe<&2, List<&2, Word(8n)>>:
  match r:
    case None{}:
      None{}
    case Some{+v}:
      Program.result.if(El.Eval.vals(ds, v, False{}), v)

def Program.gives.of(r: Maybe<List<&2, Bk.Def>>, i: List<&2, Word(8n)>, n: Nat) -> Maybe<&2, List<&2, Word(8n)>>:
  match r:
    case None{}:
      None{}
    case Some{+ds}:
      Program.result(ds, El.Eval.steps(n, ds, Program.start(i)))

# AGENTS.md 3.4.3: what the program of the book bytes p (3.4.5) gives on
# the input i after exactly n steps of Eval: the list of bytes of the value that
# it reaches, or nothing
def Program.gives(p: List<&2, Word(8n)>, i: List<&2, Word(8n)>, n: Nat) -> Maybe<&2, List<&2, Word(8n)>>:
  Program.gives.of(Bk.Book.read(p), i, n)

# the nodes of a term
def Term.size(t: Bk.Term) -> Nat:
  match t:
    case Bk.Term.Var{_}:
      1n
    case Bk.Term.Ref{_}:
      1n
    case Bk.Term.Ann{x, T}:
      1n+Nat.add(Term.size(x), Term.size(T))
    case Bk.Term.Let{_, v, f}:
      1n+Nat.add(Term.size(v), Term.size(f))
    case Bk.Term.Typ{q}:
      1n+Term.size(q)
    case Bk.Term.Min{a, b}:
      1n+Nat.add(Term.size(a), Term.size(b))
    case Bk.Term.All{_, A, B}:
      1n+Nat.add(Term.size(A), Term.size(B))
    case Bk.Term.Lam{_, f}:
      1n+Term.size(f)
    case Bk.Term.App{_, f, x}:
      1n+Nat.add(Term.size(f), Term.size(x))
    case Bk.Term.Sig{_, A, B}:
      1n+Nat.add(Term.size(A), Term.size(B))
    case Bk.Term.Tup{_, a, b}:
      1n+Nat.add(Term.size(a), Term.size(b))
    case Bk.Term.Prj{h}:
      1n+Term.size(h)
    case Bk.Term.Enu{_}:
      1n
    case Bk.Term.Lab{_}:
      1n
    case Bk.Term.Mat{_, h, m}:
      1n+Nat.add(Term.size(h), Term.size(m))
    case Bk.Term.Efq{}:
      1n
    case Bk.Term.Eql{a, b, T}:
      1n+Nat.add(Term.size(a), Nat.add(Term.size(b), Term.size(T)))
    case Bk.Term.Rfl{}:
      1n
    case Bk.Term.Rwt{e, P, f}:
      1n+Nat.add(Term.size(e), Nat.add(Term.size(P), Term.size(f)))

def Program.largest.next(r: Maybe<Bk.Term>, more: Bk.Term -> Nat) -> Nat:
  match r:
    case None{}:
      0n
    case Some{t}:
      more(t)

# the most nodes of a term that the run from t reaches within n steps, t
# included
def Program.largest.go(n: Nat, +ds: List<&2, Bk.Def>, +t: Bk.Term) -> Nat:
  match n:
    case 0n:
      Term.size(t)
    case 1n+m:
      Nat.max(Term.size(t), Program.largest.next(El.Eval.step(ds, t), u => Program.largest.go(m, ds, u)))

def Program.largest.of(r: Maybe<List<&2, Bk.Def>>, i: List<&2, Word(8n)>, n: Nat) -> Nat:
  match r:
    case None{}:
      0n
    case Some{ds}:
      Program.largest.go(n, ds, Program.start(i))

# The largest term of AGENTS.md 3.4.4: the most nodes (3.2.4) of a term that
# the run on the input i reaches within n steps; the input is in the first term
def Program.largest(p: List<&2, Word(8n)>, i: List<&2, Word(8n)>, n: Nat) -> Nat:
  Program.largest.of(Bk.Book.read(p), i, n)

# The nodes of a value's data form (AGENTS.md 3.2.2), as `bend -o` writes it: a
# constructor k{f1, .., fn} is (.k, (f1, (.., (fn, ())))), 3 + n nodes with
# the nodes s of its fields
def Form.size.ctor(n: Nat, s: Nat) -> Nat:
  Nat.add(3n+n, s)

# a Nat: Zero, then a Succ for each unit
def Form.size.nat(n: Nat) -> Nat:
  Nat.add(3n, Nat.mul(4n, n))

# a name: Nil, then a Con of a byte (67 nodes: 8 levels of WCon and a bit,
# then WNil) for each byte
def Form.size.name(k: List<&2, Word(8n)>) -> Nat:
  Nat.add(3n, Nat.mul(72n, List.length(&2, Word(8n), k)))

def Form.size.names(ks: List<&2, List<&2, Word(8n)>>) -> Nat:
  match ks:
    case Nil{}:
      3n
    case Con{k, rest}:
      5n+Nat.add(Form.size.name(k), Form.size.names(rest))

# a term; a quantity has 3 nodes
def Form.size.term(t: Bk.Term) -> Nat:
  match t:
    case Bk.Term.Var{i}:
      Form.size.ctor(1n, Form.size.nat(i))
    case Bk.Term.Ref{k}:
      Form.size.ctor(1n, Form.size.name(k))
    case Bk.Term.Ann{x, T}:
      Form.size.ctor(2n, Nat.add(Form.size.term(x), Form.size.term(T)))
    case Bk.Term.Let{_, v, f}:
      Form.size.ctor(3n, 3n+Nat.add(Form.size.term(v), Form.size.term(f)))
    case Bk.Term.Typ{q}:
      Form.size.ctor(1n, Form.size.term(q))
    case Bk.Term.Min{a, b}:
      Form.size.ctor(2n, Nat.add(Form.size.term(a), Form.size.term(b)))
    case Bk.Term.All{_, A, B}:
      Form.size.ctor(3n, 3n+Nat.add(Form.size.term(A), Form.size.term(B)))
    case Bk.Term.Lam{_, f}:
      Form.size.ctor(2n, 3n+Form.size.term(f))
    case Bk.Term.App{_, f, x}:
      Form.size.ctor(3n, 3n+Nat.add(Form.size.term(f), Form.size.term(x)))
    case Bk.Term.Sig{_, A, B}:
      Form.size.ctor(3n, 3n+Nat.add(Form.size.term(A), Form.size.term(B)))
    case Bk.Term.Tup{_, a, b}:
      Form.size.ctor(3n, 3n+Nat.add(Form.size.term(a), Form.size.term(b)))
    case Bk.Term.Prj{h}:
      Form.size.ctor(1n, Form.size.term(h))
    case Bk.Term.Enu{ks}:
      Form.size.ctor(1n, Form.size.names(ks))
    case Bk.Term.Lab{k}:
      Form.size.ctor(1n, Form.size.name(k))
    case Bk.Term.Mat{k, h, m}:
      Form.size.ctor(3n, Nat.add(Form.size.name(k), Nat.add(Form.size.term(h), Form.size.term(m))))
    case Bk.Term.Efq{}:
      3n
    case Bk.Term.Eql{a, b, T}:
      Form.size.ctor(3n, Nat.add(Form.size.term(a), Nat.add(Form.size.term(b), Form.size.term(T))))
    case Bk.Term.Rfl{}:
      3n
    case Bk.Term.Rwt{e, P, f}:
      Form.size.ctor(3n, Nat.add(Form.size.term(e), Nat.add(Form.size.term(P), Form.size.term(f))))

# a list of defs; a Bool has 3 nodes
def Form.size.defs(ds: List<&2, Bk.Def>) -> Nat:
  match ds:
    case Nil{}:
      3n
    case Con{Bk.Def{k, T, v, _}, rest}:
      5n+Nat.add(Form.size.ctor(4n, 3n+Nat.add(Form.size.name(k), Nat.add(Form.size.term(T), Form.size.term(v)))),
        Form.size.defs(rest))

def Program.size.of(r: Maybe<List<&2, Bk.Def>>) -> Nat:
  match r:
    case None{}:
      0n
    case Some{ds}:
      Form.size.defs(ds)

# the program's size of AGENTS.md 3.2.5: the nodes of the data form of the book
# of the bytes p; 0 when they are no book
def Program.size(p: List<&2, Word(8n)>) -> Nat:
  Program.size.of(Bk.Book.read(p))

# F of AGENTS.md 3.8.1.4: 64 × (the program's size + the largest term) + 2^24
# bytes
def Program.need(+p: List<&2, Word(8n)>, i: List<&2, Word(8n)>, n: Nat) -> Nat:
  Nat.add(Nat.mul(64n, Nat.add(Program.size(p), Program.largest(p, i, n))), 16777216n)

# the bytes of m pages of 2^16 bytes, up to 2^16 pages: as much as a memory of
# 32-bit addresses can have
def Program.memory(m: U32) -> Nat:
  Nat.mul(65536n, U32.to_nat(Wa.Wasm.min(m, 65536)))
