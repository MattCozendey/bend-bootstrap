# compiler: layer B6, the abstract machine
# ========================================
#
# The machine's move (one round of Mach.code's loop) as a Bend function on
# terms: AM.move. Its state is a focus, in mode 0 to evaluate or in mode 1 a
# value, and its frames, innermost first; a frame is a term with a hole, of a
# kind (the cells K.app_arg to K.min_a), a quantity q, the flag KNOWN (k), and
# the terms a (in the frame's field 2) and b (field 3, Rwt's only; a for the
# others). AM.move mirrors M.ev and M.ret branch by branch, after the changes
# D1 to D6 of the redesign: a missing local of a walk is a poison cell, whose
# term is the canonical free variable; a copy gives the canonical form of the
# substitution; a λ-match of labels that misses keeps the argument's KNOWN.
# am.ok says each move is right: an admin move (the same term, a smaller
# measure), the term's canonical step (canon/spec.bend), or a halt as the term
# asks.

import Base
import ../../../Shared/shared.bend as Sd
import ../../../Book/impl.bend as Bk
import ../../../Eval/impl.bend as El
import ../../../Program/impl.bend as Pg
import ../canon/spec.bend as C

# Types
# -----

# the kind of a frame
type FK is Data:
  FK.arg{}
  FK.val{}
  FK.fun{}
  FK.let{}
  FK.tupb{}
  FK.tupa{}
  FK.rwt{}
  FK.minb{}
  FK.mina{}

# a frame: its kind, quantity, KNOWN, and the terms a and b
type AF is Data:
  AF{kind: FK, q: Bk.Quan, k: Bool, a: Bk.Term, b: Bk.Term}

# an argument or a local: its quantity, KNOWN, and its term (heap/spec's
# chains hold them)
type Ag is Data:
  Ag{q: Bk.Quan, k: Bool, t: Bk.Term}

# an abstract state: mode 1 (ret), the focus' term, the frames, innermost
# first
type AS is Data:
  AS{ret: Bool, focus: Bk.Term, fs: List<&2, AF>}

# a move's outcome: the next abstract state, or a halt with its status and,
# for the status 0, its bytes, in order (for the status 2, none)
type AO is Data:
  AO.next{s: AS}
  AO.halt{k: U32, out: List<&2, Word(8n)>}

# what an abstract walk gives: the leaf, its locals and the arguments left;
# or it waits for more arguments; or no walk exists
type AW is Data:
  AW.leaf{u: Bk.Term, e: List<&2, Ag>, xs: List<&2, Ag>}
  AW.waits{}
  AW.none{}

# Frames and states
# -----------------

# the tag of a frame's cell (Mc.K.app_arg to Mc.K.min_a)
def FK.tag(k: FK) -> U32:
  match k:
    case FK.arg{}:
      32
    case FK.val{}:
      33
    case FK.fun{}:
      34
    case FK.let{}:
      35
    case FK.tupb{}:
      36
    case FK.tupa{}:
      37
    case FK.rwt{}:
      38
    case FK.minb{}:
      39
    case FK.mina{}:
      40

def AS.ret(s: AS) -> Bool:
  match s:
    case AS{r, _, _}:
      r

def AS.focus(s: AS) -> Bk.Term:
  match s:
    case AS{_, t, _}:
      t

def AS.fs(s: AS) -> List<&2, AF>:
  match s:
    case AS{_, _, fs}:
      fs

# the frame with t in its hole
def AF.plug(fr: AF, t: Bk.Term) -> Bk.Term:
  match fr:
    case AF{FK.arg{}, q, _, a, _}:
      Bk.Term.App{q, t, a}
    case AF{FK.val{}, q, _, a, _}:
      Bk.Term.App{q, t, a}
    case AF{FK.fun{}, q, _, a, _}:
      Bk.Term.App{q, a, t}
    case AF{FK.let{}, q, _, a, _}:
      Bk.Term.Let{q, t, a}
    case AF{FK.tupb{}, q, _, a, _}:
      Bk.Term.Tup{q, t, a}
    case AF{FK.tupa{}, q, _, a, _}:
      Bk.Term.Tup{q, a, t}
    case AF{FK.rwt{}, _, _, a, b}:
      Bk.Term.Rwt{t, a, b}
    case AF{FK.minb{}, _, _, a, _}:
      Bk.Term.Min{t, a}
    case AF{FK.mina{}, _, _, a, _}:
      Bk.Term.Min{a, t}

# the frames fs around t, the innermost first
def AF.plugs(fs: List<&2, AF>, t: Bk.Term) -> Bk.Term:
  match fs:
    case Nil{}:
      t
    case Con{fr, rest}:
      AF.plugs(rest, AF.plug(fr, t))

# the whole term of a state
def AS.term(s: AS) -> Bk.Term:
  match s:
    case AS{_, t, fs}:
      AF.plugs(fs, t)

# 3 × the nodes of t: the measure of a term to evaluate
def AS.w3(+t: Bk.Term) -> Nat:
  +s = Pg.Term.size(t)
  Nat.add(s, Nat.add(s, s))

# the measure of a frame: what its admin moves still cost, before a step
def AF.w(fr: AF) -> Nat:
  match fr:
    case AF{FK.arg{}, +q, +k, a, _}:
      Bool.pick(Nat, El.Quan.live(q) && Bool.not(k), 2n+AS.w3(a), 1n)
    case AF{FK.val{}, +q, +k, a, _}:
      Bool.pick(Nat, El.Quan.live(q) && Bool.not(k), 2n+AS.w3(a), 1n)
    case AF{FK.fun{}, _, _, _, _}:
      1n
    case AF{FK.let{}, _, _, _, _}:
      0n
    case AF{FK.tupb{}, _, _, a, _}:
      2n+AS.w3(a)
    case AF{FK.tupa{}, _, _, _, _}:
      1n
    case AF{FK.rwt{}, _, _, _, _}:
      0n
    case AF{FK.minb{}, _, _, a, _}:
      1n+AS.w3(a)
    case AF{FK.mina{}, _, _, _, _}:
      0n

def AFs.w(fs: List<&2, AF>) -> Nat:
  match fs:
    case Nil{}:
      0n
    case Con{fr, rest}:
      Nat.add(AF.w(fr), AFs.w(rest))

# the measure of a state: its frames', and its focus' when it is to evaluate
def AS.w(s: AS) -> Nat:
  match s:
    case AS{r, t, fs}:
      Nat.add(Bool.pick(Nat, r, 0n, AS.w3(t)), AFs.w(fs))

# what a frame knows: the function of App q f □ is a value, and q is live; a
# KNOWN argument is a value; Let and Tup □ b are live; the first field of
# Tup q a □ is a value when q is live; Min a □ holds a value
def AF.ok(+ds: List<&2, Bk.Def>, fr: AF) -> Bool:
  match fr:
    case AF{FK.arg{}, _, k, a, _}:
      Bool.not(k) || El.Eval.vals(ds, a, False{})
    case AF{FK.val{}, _, k, a, _}:
      Bool.not(k) || El.Eval.vals(ds, a, False{})
    case AF{FK.fun{}, q, _, a, _}:
      El.Quan.live(q) && El.Eval.vals(ds, a, False{})
    case AF{FK.let{}, q, _, _, _}:
      El.Quan.live(q)
    case AF{FK.tupb{}, q, _, _, _}:
      El.Quan.live(q)
    case AF{FK.tupa{}, q, _, a, _}:
      Bool.not(El.Quan.live(q)) || El.Eval.vals(ds, a, False{})
    case AF{FK.rwt{}, _, _, _, _}:
      True{}
    case AF{FK.minb{}, _, _, _, _}:
      True{}
    case AF{FK.mina{}, _, _, a, _}:
      El.Eval.vals(ds, a, False{})

def AFs.ok(+ds: List<&2, Bk.Def>, fs: List<&2, AF>) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case Con{fr, rest}:
      AF.ok(ds, fr) && AFs.ok(ds, rest)

# what a state knows, but for the focus' flag: each frame's AF.ok; a focus to
# return is a value; the whole term is canonical
def AS.ok0(+ds: List<&2, Bk.Def>, +s: AS) -> Bool:
  AFs.ok(ds, AS.fs(s)) && (Bool.not(AS.ret(s)) || El.Eval.vals(ds, AS.focus(s), False{})) && C.Canon.is(AS.term(s))

# and the focus' VALUE flag vb is only on a value
def AS.ok(+ds: List<&2, Bk.Def>, vb: Bool, +s: AS) -> Bool:
  AS.ok0(ds, s) && (Bool.not(vb) || El.Eval.vals(ds, AS.focus(s), False{}))

# Arguments
# ---------

def Ag.args(xs: List<&2, Ag>) -> List<&2, El.Arg>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{Ag{q, _, t}, rest}:
      Con{El.Arg{q, t}, Ag.args(rest)}

def Ag.terms(es: List<&2, Ag>) -> List<&2, Bk.Term>:
  match es:
    case Nil{}:
      Nil{}
    case Con{Ag{_, _, t}, rest}:
      Con{t, Ag.terms(rest)}

# the arguments of a spine, in front of xs, each KNOWN when it is live (a
# live argument of a value is a value)
def AM.args(t: Bk.Term, xs: List<&2, Ag>) -> List<&2, Ag>:
  match t:
    case Bk.Term.App{+q, f, x}:
      AM.args(f, Con{Ag{q, El.Quan.live(q), x}, xs})
    case _:
      xs

# the frames App q □ x of the arguments xs, the first innermost, around fs
def AM.frames(xs: List<&2, Ag>, fs: List<&2, AF>) -> List<&2, AF>:
  match xs:
    case Nil{}:
      fs
    case Con{Ag{q, k, +t}, rest}:
      Con{AF{FK.val{}, q, k, t, t}, AM.frames(rest, fs)}

# the term of a copy (M.copy) of t with the locals es: the canonical form of
# the substitution
def AM.copy(t: Bk.Term, es: List<&2, Ag>) -> Bk.Term:
  C.Canon.term(El.Term.subst(t, Ag.terms(es), 0n), 0n)

# The walk
# --------

# the local v of e, as an argument of quantity q: its KNOWN and its term; a
# poison cell (the canonical free variable, not KNOWN) when e has none
def AM.local(e: List<&2, Ag>, q: Bk.Quan, v: Nat) -> Ag:
  match e v:
    case Nil{} _:
      Ag{q, False{}, Bk.Term.Var{0n}}
    case Con{Ag{_, k, t}, _} 0n:
      Ag{q, k, t}
    case Con{_, rest} 1n+j:
      AM.local(rest, q, j)

def AM.walk.if(b: Bool, r: AW) -> AW:
  match b:
    case True{}:
      r
    case False{}:
      AW.none{}

def AM.walk.pick(b: Bool, r: AW, s: AW) -> AW:
  match b:
    case True{}:
      r
    case False{}:
      s

def AM.walk.app(node: Bool, r: AW, u: Bk.Term, e: List<&2, Ag>, ys: List<&2, Ag>) -> AW:
  match node:
    case True{}:
      r
    case False{}:
      AW.leaf{u, e, ys}

def AM.walk.leaf(node: Bool, u: Bk.Term, e: List<&2, Ag>, ys: List<&2, Ag>) -> AW:
  match node:
    case True{}:
      match ys:
        case Nil{}:
          AW.waits{}
        case _:
          AW.none{}
    case False{}:
      AW.leaf{u, e, ys}

# the walk of the machine (M.walk) of the case tree t, with the locals e, on
# the arguments xs: Eval.walk, with KNOWN carried as M.walk carries it, and a
# missing local as the canonical free variable
def AM.walk(+ds: List<&2, Bk.Def>, +t: Bk.Term, +e: List<&2, Ag>, +xs: List<&2, Ag>) -> AW:
  match t xs:
    case Bk.Term.Lam{p, f} Con{Ag{q, k, x}, rest}:
      AM.walk.if(El.Quan.binds(p, q, x), AM.walk(ds, f, Con{Ag{q, k, x}, e}, rest))
    case Bk.Term.Prj{h} Con{Ag{q, k, Bk.Term.Tup{r, a, b}}, rest}:
      AM.walk.if(El.Quan.live(q),
        AM.walk(ds, h, e, Con{Ag{El.Quan.fld(r, q), k && El.Quan.live(r), a}, Con{Ag{q, k, b}, rest}}))
    case Bk.Term.Mat{k, h, m} Con{Ag{q, kn, Bk.Term.Lab{j}}, rest}:
      AM.walk.if(El.Quan.live(q), AM.walk.pick(Sd.Name.is_eq(j, k), AM.walk(ds, h, e, rest),
        AM.walk(ds, m, e, Con{Ag{q, kn, Bk.Term.Lab{j}}, rest})))
    case Bk.Term.App{q, f, Bk.Term.Var{v}} ys:
      AM.walk.app(El.Term.takes(El.Term.head(f)), AM.walk(ds, f, e, Con{AM.local(e, q, v), ys}),
        Bk.Term.App{q, f, Bk.Term.Var{v}}, e, ys)
    case u ys:
      AM.walk.leaf(El.Term.takes(u), u, e, ys)

# The move
# --------

# the next state s when b holds; else a halt with 2
def AM.need(b: Bool, s: AS) -> AO:
  match b:
    case True{}:
      AO.next{s}
    case False{}:
      AO.halt{2, []}

# a call (M.call) on the walk w: at a leaf, its copy with the walk's locals is
# the focus, to evaluate, in the frames of the arguments left; when the walk
# waits, the state p; else a halt with 2
def AM.call(w: AW, p: AS, fs: List<&2, AF>) -> AO:
  match w:
    case AW.leaf{u, e, xs}:
      AO.next{AS{False{}, AM.copy(u, e), AM.frames(xs, fs)}}
    case AW.waits{}:
      AO.next{p}
    case AW.none{}:
      AO.halt{2, []}

# the call of the def m on the arguments xs (a Ref's field 2: the body of the
# first def of its name, or none)
def AM.body(+ds: List<&2, Bk.Def>, m: Maybe<Bk.Def>, xs: List<&2, Ag>, p: AS, fs: List<&2, AF>) -> AO:
  match m:
    case None{}:
      AO.halt{2, []}
    case Some{Bk.Def{_, _, v, _}}:
      AM.call(AM.walk(ds, v, [], xs), p, fs)

# the call of the head h of a spine on the arguments xs: a halt with 2 when h
# is no Ref
def AM.head(+ds: List<&2, Bk.Def>, h: Bk.Term, xs: List<&2, Ag>, p: AS, fs: List<&2, AF>) -> AO:
  match h:
    case Bk.Term.Ref{k}:
      AM.body(ds, El.Book.get(ds, k), xs, p, fs)
    case _:
      AO.halt{2, []}

# a λ-match of labels on its label: the first case h when it hits, else the
# other case m on the label
def AM.mat(hit: Bool, q: Bk.Quan, +j: List<&2, Word(8n)>, h: Bk.Term, m: Bk.Term, fs: List<&2, AF>) -> AS:
  match hit:
    case True{}:
      AS{False{}, h, fs}
    case False{}:
      AS{False{}, m, Con{AF{FK.val{}, q, True{}, Bk.Term.Lab{j}, Bk.Term.Lab{j}}, fs}}

# M.redex: App q f y, with f a value, and y a value when q is live
def AM.redex(+ds: List<&2, Bk.Def>, +q: Bk.Quan, +f: Bk.Term, +y: Bk.Term, +fs: List<&2, AF>) -> AO:
  match f y:
    case Bk.Term.Lam{p, b} x:
      AM.need(El.Quan.binds(p, q, x), AS{False{}, AM.copy(b, [Ag{Bk.Quan.Q0{}, False{}, x}]), fs})
    case Bk.Term.Prj{h} Bk.Term.Tup{r, a, b}:
      AM.need(El.Quan.live(q), AS{False{}, h,
        Con{AF{FK.val{}, El.Quan.fld(r, q), El.Quan.live(r), a, a}, Con{AF{FK.val{}, q, True{}, b, b}, fs}}})
    case Bk.Term.Mat{k, h, m} Bk.Term.Lab{j}:
      AM.need(El.Quan.live(q), AM.mat(Sd.Name.is_eq(j, k), q, j, h, m, fs))
    case g x:
      AM.head(ds, El.Term.head(g), AM.args(g, [Ag{q, El.Quan.live(q), x}]), AS{True{}, Bk.Term.App{q, g, x}, fs}, fs)

# App q v □ a, with the value v: a to evaluate, in the frame App q v □, when
# swap (q is live and a is not KNOWN); else the redex
def AM.arg(+ds: List<&2, Bk.Def>, swap: Bool, +q: Bk.Quan, +v: Bk.Term, a: Bk.Term, fs: List<&2, AF>) -> AO:
  match swap:
    case True{}:
      AO.next{AS{False{}, a, Con{AF{FK.fun{}, q, False{}, v, v}, fs}}}
    case False{}:
      AM.redex(ds, q, v, a, fs)

# the meet m of Min a v, a step; a halt with 2 when there is none
def AM.meet(m: Maybe<Bk.Term>, fs: List<&2, AF>) -> AO:
  match m:
    case Some{u}:
      AO.next{AS{False{}, u, fs}}
    case None{}:
      AO.halt{2, []}

def AM.is_rfl(t: Bk.Term) -> Bool:
  match t:
    case Bk.Term.Rfl{}:
      True{}
    case _:
      False{}

# M.ret: the value v into the frame fr, around fs
def AM.ret(+ds: List<&2, Bk.Def>, +v: Bk.Term, fr: AF, fs: List<&2, AF>) -> AO:
  match fr:
    case AF{FK.arg{}, +q, +k, a, _}:
      AM.arg(ds, El.Quan.live(q) && Bool.not(k), q, v, a, fs)
    case AF{FK.val{}, +q, +k, a, _}:
      AM.arg(ds, El.Quan.live(q) && Bool.not(k), q, v, a, fs)
    case AF{FK.fun{}, q, _, a, _}:
      AM.redex(ds, q, a, v, fs)
    case AF{FK.let{}, q, _, a, _}:
      AM.need(El.Quan.fits(q, v), AS{False{}, AM.copy(a, [Ag{Bk.Quan.Q0{}, False{}, v}]), fs})
    case AF{FK.tupb{}, q, _, a, _}:
      AO.next{AS{False{}, a, Con{AF{FK.tupa{}, q, False{}, v, v}, fs}}}
    case AF{FK.tupa{}, q, _, a, _}:
      AO.next{AS{True{}, Bk.Term.Tup{q, a, v}, fs}}
    case AF{FK.rwt{}, _, _, _, b}:
      AM.need(AM.is_rfl(v), AS{False{}, b, fs})
    case AF{FK.minb{}, _, _, a, _}:
      AO.next{AS{False{}, a, Con{AF{FK.mina{}, Bk.Quan.Q0{}, False{}, v, v}, fs}}}
    case AF{FK.mina{}, _, _, a, _}:
      AM.meet(El.Eval.meet(a, v), fs)

# M.out: the halt of a value with no frame: 0 with its bytes, when it is a
# list of bytes; else 2
def AM.out(r: Maybe<&2, List<&2, Word(8n)>>) -> AO:
  match r:
    case Some{bs}:
      AO.halt{0, bs}
    case None{}:
      AO.halt{2, []}

# mode 1: the value v into the top frame; M.out with no frame
def AM.back(+ds: List<&2, Bk.Def>, +v: Bk.Term, fs: List<&2, AF>) -> AO:
  match fs:
    case Nil{}:
      AM.out(Pg.Program.unbytes(v))
    case Con{fr, rest}:
      AM.ret(ds, v, fr, rest)

def AM.let(live: Bool, +q: Bk.Quan, +v: Bk.Term, +f: Bk.Term, fs: List<&2, AF>) -> AO:
  match live:
    case True{}:
      AO.next{AS{False{}, v, Con{AF{FK.let{}, q, False{}, f, f}, fs}}}
    case False{}:
      AO.next{AS{False{}, AM.copy(f, [Ag{Bk.Quan.Q0{}, False{}, v}]), fs}}

def AM.tup(live: Bool, +q: Bk.Quan, +a: Bk.Term, +b: Bk.Term, fs: List<&2, AF>) -> AO:
  match live:
    case True{}:
      AO.next{AS{False{}, a, Con{AF{FK.tupb{}, q, False{}, b, b}, fs}}}
    case False{}:
      AO.next{AS{False{}, b, Con{AF{FK.tupa{}, q, False{}, a, a}, fs}}}

# M.ev past its test of VALUE: a step or a frame, by the focus' former
def AM.ev(+ds: List<&2, Bk.Def>, t: Bk.Term, +fs: List<&2, AF>) -> AO:
  match t:
    case Bk.Term.App{+q, f, +x}:
      AO.next{AS{False{}, f, Con{AF{FK.arg{}, q, False{}, x, x}, fs}}}
    case Bk.Term.Ref{+k}:
      AM.body(ds, El.Book.get(ds, k), [], AS{True{}, Bk.Term.Ref{k}, fs}, fs)
    case Bk.Term.Ann{x, _}:
      AO.next{AS{False{}, x, fs}}
    case Bk.Term.Let{+q, v, f}:
      AM.let(El.Quan.live(q), q, v, f, fs)
    case Bk.Term.Tup{+q, a, b}:
      AM.tup(El.Quan.live(q), q, a, b, fs)
    case Bk.Term.Rwt{e, P, f}:
      AO.next{AS{False{}, e, Con{AF{FK.rwt{}, Bk.Quan.Q0{}, False{}, P, f}, fs}}}
    case Bk.Term.Min{a, +b}:
      AO.next{AS{False{}, a, Con{AF{FK.minb{}, Bk.Quan.Q0{}, False{}, b, b}, fs}}}
    case _:
      AO.halt{2, []}

# a value by its form, as the image's table says (field 4): every former but
# Tup
def AM.former(t: Bk.Term) -> Bool:
  match t:
    case Bk.Term.Tup{_, _, _}:
      False{}
    case u:
      El.Term.is_former(u)

# mode 0: a focus flagged VALUE (val) is returned, as is a value by its form
def AM.eval(+ds: List<&2, Bk.Def>, val: Bool, +t: Bk.Term, fs: List<&2, AF>) -> AO:
  match val:
    case True{}:
      AO.next{AS{True{}, t, fs}}
    case False{}:
      AM.ev(ds, t, fs)

# the move of the machine (one round of Mach.code) on terms; vb is the focus'
# VALUE flag
def AM.move(+ds: List<&2, Bk.Def>, vb: Bool, s: AS) -> AO:
  match s:
    case AS{False{}, +t, fs}:
      AM.eval(ds, vb || AM.former(t), t, fs)
    case AS{True{}, +t, fs}:
      AM.back(ds, t, fs)

# Right moves
# -----------

# an admin move: the same term, a smaller measure
def AO.adm(+s: AS, +s2: AS) -> Bool:
  C.Term.is_eq(AS.term(s2), AS.term(s)) && Nat.is_lt(AS.w(s2), AS.w(s))

# a halt's result r is right: with 0, the bytes out; with 2, none
def AO.res(+k: U32, r: Maybe<&2, List<&2, Word(8n)>>, out: List<&2, Word(8n)>) -> Bool:
  match r:
    case Some{bs}:
      U32.is_eq(k, 0) && Sd.Name.is_eq(bs, out)
    case None{}:
      U32.is_eq(k, 2)

# a move is right: an admin move or the term's canonical step, each to a state
# that knows what AS.ok0 asks; or a halt, when the term has no step, with 0
# and the term's result, or with 2 when it has none
def AO.ok(+ds: List<&2, Bk.Def>, +s: AS, o: AO) -> Bool:
  match o:
    case AO.next{+s2}:
      AS.ok0(ds, s2) && (AO.adm(s, s2) || C.Tm.is(C.CStep(ds, AS.term(s)), AS.term(s2)))
    case AO.halt{k, out}:
      C.Tm.none(C.CStep(ds, AS.term(s))) && AO.res(k, Pg.Program.result(ds, Some{AS.term(s)}), out)

# the term of a walk (Eval.walk's), made canonical: the leaf's copy, in its
# arguments left
def AW.eval(w: AW) -> Maybe<Maybe<Bk.Term>>:
  match w:
    case AW.leaf{u, e, xs}:
      Some{Some{C.Canon.term(El.Term.spine(Ag.args(xs), El.Term.subst(u, Ag.terms(e), 0n)), 0n)}}
    case AW.waits{}:
      Some{None{}}
    case AW.none{}:
      None{}

# Laws
# ----

# LAW: each move of the machine is right
law am.ok:
  for +ds: List<&2, Bk.Def>
  for +vb: Bool
  for +s: AS
  for ok: {AS.ok(ds, vb, s) == True{} : Bool}
  {AO.ok(ds, s, AM.move(ds, vb, s)) == True{} : Bool}

# LAW: the abstract walk is Eval's walk, made canonical
law am.walk_eval:
  for +ds: List<&2, Bk.Def>
  for +t: Bk.Term
  for +e: List<&2, Ag>
  for +xs: List<&2, Ag>
  {AW.eval(AM.walk(ds, t, e, xs)) == C.Canon.walk(El.Eval.walk(t, Ag.terms(e), Ag.args(xs))) : Maybe<Maybe<Bk.Term>>}
