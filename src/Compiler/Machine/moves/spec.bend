# compiler: layer B7, the moves of the machine
# ============================================
#
# One round of the main loop (Mach.round: M.ev in mode 0, M.ret in mode 1)
# moves as the abstract machine says (am/spec.bend's AM.move): from a state
# that Inv finds for the abstract state s (routines/spec.bend), it goes on to
# a state that Inv finds for the move's next state, or it halts as the move
# halts, with the move's bytes as its output; it runs out of memory only below
# its Budget (memory/spec.bend). round.sim says so for every move; it follows
# from one law per move (mv.*), each stated on its abstract state's parts and
# with its outcome as AM.move computes it, and the mode's test (moves/round.bend
# proves it). inv.vb: the focus' VALUE flag is only on a value (what am.ok
# asks of a state, beside AS.ok0).

import Base
import ../../../Shared/shared.bend as Sd
import ../../../Book/impl.bend as Bk
import ../../../Eval/impl.bend as El
import ../../../Program/impl.bend as Pg
import ../../Cir/impl.bend as Cr
import ../impl.bend as Mc
import ../logic/spec.bend as Lg
import ../am/spec.bend as A
import ../heap/spec.bend as Hp
import ../routines/spec.bend as R
import ../memory/spec.bend as Me

# The outcome of a round
# ----------------------

# the focus cell's VALUE flag
def Vb(+st: Cr.Cir.State) -> Bool:
  Hp.Fl(Lg.St.cells(st), Hp.V.reg(st, Mc.R.focus()), Mc.F.value())

def Next.is(+x: Hp.Cx, o: A.AO, +st2: Cr.Cir.State) -> Bool:
  match o:
    case A.AO.next{s}:
      R.Inv(x, st2, s)
    case A.AO.halt{_, _}:
      False{}

# a round goes on to a state that Inv finds for the move's next state
def Next(+x: Hp.Cx, o: A.AO) -> Cr.Cir.State -> Type:
  st2 => {Next.is(x, o, st2) == True{} : Bool}

def Halt.is(o: A.AO, +k: U32, +st2: Cr.Cir.State) -> Bool:
  match o:
    case A.AO.next{_}:
      False{}
    case A.AO.halt{+j, out}:
      U32.is_eq(k, j) && (Bool.not(U32.is_eq(j, 0)) || Sd.Name.is_eq(List.reverse(&2, Word(8n), Lg.St.out(st2)), out))

# a round halts as the move halts: its status, and for the status 0 the
# move's bytes as the output (kept last first)
def Halt(o: A.AO) -> U32 -> Cr.Cir.State -> Type:
  k => st2 => {Halt.is(o, k, st2) == True{} : Bool}

# a frame of an application's argument: App q □ a, known or not
def Mv.isapp(k: A.FK) -> Bool:
  match k:
    case A.FK.arg{}:
      True{}
    case A.FK.val{}:
      True{}
    case _:
      False{}

# a function whose redex is a call (M.redex past its λ, Prj and Mat cases)
def Mv.calls(t: Bk.Term) -> Bool:
  match t:
    case Bk.Term.Lam{_, _}:
      False{}
    case Bk.Term.Prj{_}:
      False{}
    case Bk.Term.Mat{_, _, _}:
      False{}
    case _:
      True{}

# Laws
# ----

# LAW: one round of the main loop moves as AM.move says
law round.sim:
  for +x: Hp.Cx
  for +st: Cr.Cir.State
  for +s: A.AS
  for +iv: {R.Inv(x, st, s) == True{} : Bool}
  Lg.Tot(Mc.Mach.round(), st, Me.Budget(x, st, s), Next(x, A.AM.move(Hp.Cx.ds(x), Vb(st), s)),
    Halt(A.AM.move(Hp.Cx.ds(x), Vb(st), s)))

# LAW: the focus' VALUE flag is only on a value
law inv.vb:
  for +x: Hp.Cx
  for +st: Cr.Cir.State
  for +s: A.AS
  for +iv: {R.Inv(x, st, s) == True{} : Bool}
  {Bool.not(Vb(st)) || El.Eval.vals(Hp.Cx.ds(x), A.AS.focus(s), False{}) == True{} : Bool}

# Laws: mode 0 (M.ev)
# -------------------

# LAW: mode 0, a focus flagged VALUE or a value by its form (the table's
# former bit): it is returned, mode 1
law mv.ev.val:
  for +x: Hp.Cx
  for +st: Cr.Cir.State
  for +t: Bk.Term
  for +fs: List<&2, A.AF>
  for +iv: {R.Inv(x, st, A.AS{False{}, t, fs}) == True{} : Bool}
  for +hv: {Vb(st) || A.AM.former(t) == True{} : Bool}
  Lg.Tot(Mc.M.ev(), st, Me.Budget(x, st, A.AS{False{}, t, fs}), Next(x, A.AO.next{A.AS{True{}, t, fs}}),
    Halt(A.AO.next{A.AS{True{}, t, fs}}))

# LAW: mode 0, the focus Var i, not flagged VALUE: no step, halt 2
law mv.ev.var:
  for +x: Hp.Cx
  for +st: Cr.Cir.State
  for +i: Nat
  for +fs: List<&2, A.AF>
  for +iv: {R.Inv(x, st, A.AS{False{}, Bk.Term.Var{i}, fs}) == True{} : Bool}
  for +hv: {Vb(st) == False{} : Bool}
  Lg.Tot(Mc.M.ev(), st, Me.Budget(x, st, A.AS{False{}, Bk.Term.Var{i}, fs}), Next(x, A.AO.halt{2, []}), Halt(A.AO.halt{2, []}))

# LAW: mode 0, the focus App q f a, not flagged VALUE: f, in the frame
# App q □ a
law mv.ev.app:
  for +x: Hp.Cx
  for +st: Cr.Cir.State
  for +q: Bk.Quan
  for +f: Bk.Term
  for +a: Bk.Term
  for +fs: List<&2, A.AF>
  for +iv: {R.Inv(x, st, A.AS{False{}, Bk.Term.App{q, f, a}, fs}) == True{} : Bool}
  for +hv: {Vb(st) == False{} : Bool}
  Lg.Tot(Mc.M.ev(), st, Me.Budget(x, st, A.AS{False{}, Bk.Term.App{q, f, a}, fs}),
    Next(x, A.AO.next{A.AS{False{}, f, Con{A.AF{A.FK.arg{}, q, False{}, a, a}, fs}}}),
    Halt(A.AO.next{A.AS{False{}, f, Con{A.AF{A.FK.arg{}, q, False{}, a, a}, fs}}}))

# LAW: mode 0, the focus Ref k, not flagged VALUE: the call of k's body on no
# argument (M.call): its leaf's copy, to evaluate; Ref k as a value when the
# body waits for an argument; halt 2 when k has no def or no walk
law mv.ev.ref:
  for +x: Hp.Cx
  for +st: Cr.Cir.State
  for +k: List<&2, Word(8n)>
  for +fs: List<&2, A.AF>
  for +iv: {R.Inv(x, st, A.AS{False{}, Bk.Term.Ref{k}, fs}) == True{} : Bool}
  for +hv: {Vb(st) == False{} : Bool}
  Lg.Tot(Mc.M.ev(), st, Me.Budget(x, st, A.AS{False{}, Bk.Term.Ref{k}, fs}),
    Next(x, A.AM.body(Hp.Cx.ds(x), El.Book.get(Hp.Cx.ds(x), k), [], A.AS{True{}, Bk.Term.Ref{k}, fs}, fs)),
    Halt(A.AM.body(Hp.Cx.ds(x), El.Book.get(Hp.Cx.ds(x), k), [], A.AS{True{}, Bk.Term.Ref{k}, fs}, fs)))

# LAW: mode 0, the focus Ann a b, not flagged VALUE: a, a step
law mv.ev.ann:
  for +x: Hp.Cx
  for +st: Cr.Cir.State
  for +a: Bk.Term
  for +b: Bk.Term
  for +fs: List<&2, A.AF>
  for +iv: {R.Inv(x, st, A.AS{False{}, Bk.Term.Ann{a, b}, fs}) == True{} : Bool}
  for +hv: {Vb(st) == False{} : Bool}
  Lg.Tot(Mc.M.ev(), st, Me.Budget(x, st, A.AS{False{}, Bk.Term.Ann{a, b}, fs}), Next(x, A.AO.next{A.AS{False{}, a, fs}}),
    Halt(A.AO.next{A.AS{False{}, a, fs}}))

# LAW: mode 0, the focus Let q v f with q live, not flagged VALUE: v, in the
# frame Let q □ f
law mv.ev.let:
  for +x: Hp.Cx
  for +st: Cr.Cir.State
  for +q: Bk.Quan
  for +v: Bk.Term
  for +f: Bk.Term
  for +fs: List<&2, A.AF>
  for +iv: {R.Inv(x, st, A.AS{False{}, Bk.Term.Let{q, v, f}, fs}) == True{} : Bool}
  for +hv: {Vb(st) == False{} : Bool}
  for +hq: {El.Quan.live(q) == True{} : Bool}
  Lg.Tot(Mc.M.ev(), st, Me.Budget(x, st, A.AS{False{}, Bk.Term.Let{q, v, f}, fs}),
    Next(x, A.AO.next{A.AS{False{}, v, Con{A.AF{A.FK.let{}, q, False{}, f, f}, fs}}}),
    Halt(A.AO.next{A.AS{False{}, v, Con{A.AF{A.FK.let{}, q, False{}, f, f}, fs}}}))

# LAW: mode 0, the focus Let q v f with q not live, not flagged VALUE: f with
# v put in (its copy), a step
law mv.ev.unlet:
  for +x: Hp.Cx
  for +st: Cr.Cir.State
  for +q: Bk.Quan
  for +v: Bk.Term
  for +f: Bk.Term
  for +fs: List<&2, A.AF>
  for +iv: {R.Inv(x, st, A.AS{False{}, Bk.Term.Let{q, v, f}, fs}) == True{} : Bool}
  for +hv: {Vb(st) == False{} : Bool}
  for +hq: {El.Quan.live(q) == False{} : Bool}
  Lg.Tot(Mc.M.ev(), st, Me.Budget(x, st, A.AS{False{}, Bk.Term.Let{q, v, f}, fs}),
    Next(x, A.AO.next{A.AS{False{}, A.AM.copy(f, [A.Ag{Bk.Quan.Q0{}, False{}, v}]), fs}}),
    Halt(A.AO.next{A.AS{False{}, A.AM.copy(f, [A.Ag{Bk.Quan.Q0{}, False{}, v}]), fs}}))

# LAW: mode 0, the focus Tup q a b with q live, not flagged VALUE: a, in the
# frame Tup q □ b
law mv.ev.tup:
  for +x: Hp.Cx
  for +st: Cr.Cir.State
  for +q: Bk.Quan
  for +a: Bk.Term
  for +b: Bk.Term
  for +fs: List<&2, A.AF>
  for +iv: {R.Inv(x, st, A.AS{False{}, Bk.Term.Tup{q, a, b}, fs}) == True{} : Bool}
  for +hv: {Vb(st) == False{} : Bool}
  for +hq: {El.Quan.live(q) == True{} : Bool}
  Lg.Tot(Mc.M.ev(), st, Me.Budget(x, st, A.AS{False{}, Bk.Term.Tup{q, a, b}, fs}),
    Next(x, A.AO.next{A.AS{False{}, a, Con{A.AF{A.FK.tupb{}, q, False{}, b, b}, fs}}}),
    Halt(A.AO.next{A.AS{False{}, a, Con{A.AF{A.FK.tupb{}, q, False{}, b, b}, fs}}}))

# LAW: mode 0, the focus Tup q a b with q not live, not flagged VALUE: b, in
# the frame Tup q a □
law mv.ev.tup0:
  for +x: Hp.Cx
  for +st: Cr.Cir.State
  for +q: Bk.Quan
  for +a: Bk.Term
  for +b: Bk.Term
  for +fs: List<&2, A.AF>
  for +iv: {R.Inv(x, st, A.AS{False{}, Bk.Term.Tup{q, a, b}, fs}) == True{} : Bool}
  for +hv: {Vb(st) == False{} : Bool}
  for +hq: {El.Quan.live(q) == False{} : Bool}
  Lg.Tot(Mc.M.ev(), st, Me.Budget(x, st, A.AS{False{}, Bk.Term.Tup{q, a, b}, fs}),
    Next(x, A.AO.next{A.AS{False{}, b, Con{A.AF{A.FK.tupa{}, q, False{}, a, a}, fs}}}),
    Halt(A.AO.next{A.AS{False{}, b, Con{A.AF{A.FK.tupa{}, q, False{}, a, a}, fs}}}))

# LAW: mode 0, the focus Rwt e P f, not flagged VALUE: e, in the frame
# Rwt □ P f
law mv.ev.rwt:
  for +x: Hp.Cx
  for +st: Cr.Cir.State
  for +e: Bk.Term
  for +P: Bk.Term
  for +f: Bk.Term
  for +fs: List<&2, A.AF>
  for +iv: {R.Inv(x, st, A.AS{False{}, Bk.Term.Rwt{e, P, f}, fs}) == True{} : Bool}
  for +hv: {Vb(st) == False{} : Bool}
  Lg.Tot(Mc.M.ev(), st, Me.Budget(x, st, A.AS{False{}, Bk.Term.Rwt{e, P, f}, fs}),
    Next(x, A.AO.next{A.AS{False{}, e, Con{A.AF{A.FK.rwt{}, Bk.Quan.Q0{}, False{}, P, f}, fs}}}),
    Halt(A.AO.next{A.AS{False{}, e, Con{A.AF{A.FK.rwt{}, Bk.Quan.Q0{}, False{}, P, f}, fs}}}))

# LAW: mode 0, the focus Min a b, not flagged VALUE: a, in the frame Min □ b
law mv.ev.min:
  for +x: Hp.Cx
  for +st: Cr.Cir.State
  for +a: Bk.Term
  for +b: Bk.Term
  for +fs: List<&2, A.AF>
  for +iv: {R.Inv(x, st, A.AS{False{}, Bk.Term.Min{a, b}, fs}) == True{} : Bool}
  for +hv: {Vb(st) == False{} : Bool}
  Lg.Tot(Mc.M.ev(), st, Me.Budget(x, st, A.AS{False{}, Bk.Term.Min{a, b}, fs}),
    Next(x, A.AO.next{A.AS{False{}, a, Con{A.AF{A.FK.minb{}, Bk.Quan.Q0{}, False{}, b, b}, fs}}}),
    Halt(A.AO.next{A.AS{False{}, a, Con{A.AF{A.FK.minb{}, Bk.Quan.Q0{}, False{}, b, b}, fs}}}))

# Laws: mode 1 (M.ret)
# --------------------

# LAW: mode 1 with no frame, the value v: M.out, halt 0 with v's bytes, or 2
law mv.out:
  for +x: Hp.Cx
  for +st: Cr.Cir.State
  for +v: Bk.Term
  for +iv: {R.Inv(x, st, A.AS{True{}, v, []}) == True{} : Bool}
  Lg.Tot(Mc.M.ret(), st, Me.Budget(x, st, A.AS{True{}, v, []}), Next(x, A.AM.out(Pg.Program.unbytes(v))),
    Halt(A.AM.out(Pg.Program.unbytes(v))))

# LAW: mode 1, the value v into App q □ a (KNOWN k), q live and a not KNOWN:
# a, to evaluate, in the frame App q v □ (M.swap)
law mv.ret.swap:
  for +x: Hp.Cx
  for +st: Cr.Cir.State
  for +v: Bk.Term
  for +kind: A.FK
  for +q: Bk.Quan
  for +k: Bool
  for +a: Bk.Term
  for +b: Bk.Term
  for +fs: List<&2, A.AF>
  for +iv: {R.Inv(x, st, A.AS{True{}, v, Con{A.AF{kind, q, k, a, b}, fs}}) == True{} : Bool}
  for +hk: {Mv.isapp(kind) && El.Quan.live(q) && Bool.not(k) == True{} : Bool}
  Lg.Tot(Mc.M.ret(), st, Me.Budget(x, st, A.AS{True{}, v, Con{A.AF{kind, q, k, a, b}, fs}}),
    Next(x, A.AO.next{A.AS{False{}, a, Con{A.AF{A.FK.fun{}, q, False{}, v, v}, fs}}}),
    Halt(A.AO.next{A.AS{False{}, a, Con{A.AF{A.FK.fun{}, q, False{}, v, v}, fs}}}))

# LAW: mode 1, the value Lam p f into App q □ a, not swapped: f with a put in
# (its copy), a step, when p binds a at q; else halt 2
law mv.ret.app.lam:
  for +x: Hp.Cx
  for +st: Cr.Cir.State
  for +p: Bk.Quan
  for +f: Bk.Term
  for +kind: A.FK
  for +q: Bk.Quan
  for +k: Bool
  for +a: Bk.Term
  for +b: Bk.Term
  for +fs: List<&2, A.AF>
  for +iv: {R.Inv(x, st, A.AS{True{}, Bk.Term.Lam{p, f}, Con{A.AF{kind, q, k, a, b}, fs}}) == True{} : Bool}
  for +hk: {Mv.isapp(kind) && Bool.not(El.Quan.live(q) && Bool.not(k)) == True{} : Bool}
  Lg.Tot(Mc.M.ret(), st, Me.Budget(x, st, A.AS{True{}, Bk.Term.Lam{p, f}, Con{A.AF{kind, q, k, a, b}, fs}}),
    Next(x, A.AM.need(El.Quan.binds(p, q, a), A.AS{False{}, A.AM.copy(f, [A.Ag{Bk.Quan.Q0{}, False{}, a}]), fs})),
    Halt(A.AM.need(El.Quan.binds(p, q, a), A.AS{False{}, A.AM.copy(f, [A.Ag{Bk.Quan.Q0{}, False{}, a}]), fs})))

# LAW: mode 1, the value Prj h into App q □ a, not swapped: the redex
# (AM.redex: on a pair, h in the frames of its fields; else halt 2)
law mv.ret.app.prj:
  for +x: Hp.Cx
  for +st: Cr.Cir.State
  for +h: Bk.Term
  for +kind: A.FK
  for +q: Bk.Quan
  for +k: Bool
  for +a: Bk.Term
  for +b: Bk.Term
  for +fs: List<&2, A.AF>
  for +iv: {R.Inv(x, st, A.AS{True{}, Bk.Term.Prj{h}, Con{A.AF{kind, q, k, a, b}, fs}}) == True{} : Bool}
  for +hk: {Mv.isapp(kind) && Bool.not(El.Quan.live(q) && Bool.not(k)) == True{} : Bool}
  Lg.Tot(Mc.M.ret(), st, Me.Budget(x, st, A.AS{True{}, Bk.Term.Prj{h}, Con{A.AF{kind, q, k, a, b}, fs}}),
    Next(x, A.AM.redex(Hp.Cx.ds(x), q, Bk.Term.Prj{h}, a, fs)), Halt(A.AM.redex(Hp.Cx.ds(x), q, Bk.Term.Prj{h}, a, fs)))

# LAW: mode 1, the value Mat j h m into App q □ a, not swapped: the redex
# (AM.redex: on a label, h when it is j's, else m on it; else halt 2)
law mv.ret.app.mat:
  for +x: Hp.Cx
  for +st: Cr.Cir.State
  for +j: List<&2, Word(8n)>
  for +h: Bk.Term
  for +m: Bk.Term
  for +kind: A.FK
  for +q: Bk.Quan
  for +k: Bool
  for +a: Bk.Term
  for +b: Bk.Term
  for +fs: List<&2, A.AF>
  for +iv: {R.Inv(x, st, A.AS{True{}, Bk.Term.Mat{j, h, m}, Con{A.AF{kind, q, k, a, b}, fs}}) == True{} : Bool}
  for +hk: {Mv.isapp(kind) && Bool.not(El.Quan.live(q) && Bool.not(k)) == True{} : Bool}
  Lg.Tot(Mc.M.ret(), st, Me.Budget(x, st, A.AS{True{}, Bk.Term.Mat{j, h, m}, Con{A.AF{kind, q, k, a, b}, fs}}),
    Next(x, A.AM.redex(Hp.Cx.ds(x), q, Bk.Term.Mat{j, h, m}, a, fs)),
    Halt(A.AM.redex(Hp.Cx.ds(x), q, Bk.Term.Mat{j, h, m}, a, fs)))

# LAW: mode 1, any other value v into App q □ a, not swapped: the call of the
# head of v's spine (AM.redex past its λ, Prj and Mat cases)
law mv.ret.app.call:
  for +x: Hp.Cx
  for +st: Cr.Cir.State
  for +v: Bk.Term
  for +kind: A.FK
  for +q: Bk.Quan
  for +k: Bool
  for +a: Bk.Term
  for +b: Bk.Term
  for +fs: List<&2, A.AF>
  for +iv: {R.Inv(x, st, A.AS{True{}, v, Con{A.AF{kind, q, k, a, b}, fs}}) == True{} : Bool}
  for +hk: {Mv.isapp(kind) && Bool.not(El.Quan.live(q) && Bool.not(k)) && Mv.calls(v) == True{} : Bool}
  Lg.Tot(Mc.M.ret(), st, Me.Budget(x, st, A.AS{True{}, v, Con{A.AF{kind, q, k, a, b}, fs}}),
    Next(x, A.AM.redex(Hp.Cx.ds(x), q, v, a, fs)), Halt(A.AM.redex(Hp.Cx.ds(x), q, v, a, fs)))

# LAW: mode 1, the value v into App q (Lam p f) □: f with v put in (its
# copy), a step, when p binds v at q; else halt 2
law mv.ret.fun.lam:
  for +x: Hp.Cx
  for +st: Cr.Cir.State
  for +v: Bk.Term
  for +q: Bk.Quan
  for +k: Bool
  for +p: Bk.Quan
  for +f: Bk.Term
  for +b: Bk.Term
  for +fs: List<&2, A.AF>
  for +iv: {R.Inv(x, st, A.AS{True{}, v, Con{A.AF{A.FK.fun{}, q, k, Bk.Term.Lam{p, f}, b}, fs}}) == True{} : Bool}
  Lg.Tot(Mc.M.ret(), st, Me.Budget(x, st, A.AS{True{}, v, Con{A.AF{A.FK.fun{}, q, k, Bk.Term.Lam{p, f}, b}, fs}}),
    Next(x, A.AM.need(El.Quan.binds(p, q, v), A.AS{False{}, A.AM.copy(f, [A.Ag{Bk.Quan.Q0{}, False{}, v}]), fs})),
    Halt(A.AM.need(El.Quan.binds(p, q, v), A.AS{False{}, A.AM.copy(f, [A.Ag{Bk.Quan.Q0{}, False{}, v}]), fs})))

# LAW: mode 1, the value v into App q (Prj h) □: the redex
law mv.ret.fun.prj:
  for +x: Hp.Cx
  for +st: Cr.Cir.State
  for +v: Bk.Term
  for +q: Bk.Quan
  for +k: Bool
  for +h: Bk.Term
  for +b: Bk.Term
  for +fs: List<&2, A.AF>
  for +iv: {R.Inv(x, st, A.AS{True{}, v, Con{A.AF{A.FK.fun{}, q, k, Bk.Term.Prj{h}, b}, fs}}) == True{} : Bool}
  Lg.Tot(Mc.M.ret(), st, Me.Budget(x, st, A.AS{True{}, v, Con{A.AF{A.FK.fun{}, q, k, Bk.Term.Prj{h}, b}, fs}}),
    Next(x, A.AM.redex(Hp.Cx.ds(x), q, Bk.Term.Prj{h}, v, fs)), Halt(A.AM.redex(Hp.Cx.ds(x), q, Bk.Term.Prj{h}, v, fs)))

# LAW: mode 1, the value v into App q (Mat j h m) □: the redex
law mv.ret.fun.mat:
  for +x: Hp.Cx
  for +st: Cr.Cir.State
  for +v: Bk.Term
  for +q: Bk.Quan
  for +k: Bool
  for +j: List<&2, Word(8n)>
  for +h: Bk.Term
  for +m: Bk.Term
  for +b: Bk.Term
  for +fs: List<&2, A.AF>
  for +iv: {R.Inv(x, st, A.AS{True{}, v, Con{A.AF{A.FK.fun{}, q, k, Bk.Term.Mat{j, h, m}, b}, fs}}) == True{} : Bool}
  Lg.Tot(Mc.M.ret(), st, Me.Budget(x, st, A.AS{True{}, v, Con{A.AF{A.FK.fun{}, q, k, Bk.Term.Mat{j, h, m}, b}, fs}}),
    Next(x, A.AM.redex(Hp.Cx.ds(x), q, Bk.Term.Mat{j, h, m}, v, fs)),
    Halt(A.AM.redex(Hp.Cx.ds(x), q, Bk.Term.Mat{j, h, m}, v, fs)))

# LAW: mode 1, the value v into App q g □, any other g: the call of the head
# of g's spine
law mv.ret.fun.call:
  for +x: Hp.Cx
  for +st: Cr.Cir.State
  for +v: Bk.Term
  for +q: Bk.Quan
  for +k: Bool
  for +g: Bk.Term
  for +b: Bk.Term
  for +fs: List<&2, A.AF>
  for +iv: {R.Inv(x, st, A.AS{True{}, v, Con{A.AF{A.FK.fun{}, q, k, g, b}, fs}}) == True{} : Bool}
  for +hc: {Mv.calls(g) == True{} : Bool}
  Lg.Tot(Mc.M.ret(), st, Me.Budget(x, st, A.AS{True{}, v, Con{A.AF{A.FK.fun{}, q, k, g, b}, fs}}),
    Next(x, A.AM.redex(Hp.Cx.ds(x), q, g, v, fs)), Halt(A.AM.redex(Hp.Cx.ds(x), q, g, v, fs)))

# LAW: mode 1, the value v into Let q □ f: f with v put in (its copy), a step,
# when q may hold v; else halt 2
law mv.ret.let:
  for +x: Hp.Cx
  for +st: Cr.Cir.State
  for +v: Bk.Term
  for +q: Bk.Quan
  for +k: Bool
  for +f: Bk.Term
  for +b: Bk.Term
  for +fs: List<&2, A.AF>
  for +iv: {R.Inv(x, st, A.AS{True{}, v, Con{A.AF{A.FK.let{}, q, k, f, b}, fs}}) == True{} : Bool}
  Lg.Tot(Mc.M.ret(), st, Me.Budget(x, st, A.AS{True{}, v, Con{A.AF{A.FK.let{}, q, k, f, b}, fs}}),
    Next(x, A.AM.need(El.Quan.fits(q, v), A.AS{False{}, A.AM.copy(f, [A.Ag{Bk.Quan.Q0{}, False{}, v}]), fs})),
    Halt(A.AM.need(El.Quan.fits(q, v), A.AS{False{}, A.AM.copy(f, [A.Ag{Bk.Quan.Q0{}, False{}, v}]), fs})))

# LAW: mode 1, the value v into Tup q □ b: b, to evaluate, in the frame
# Tup q v □ (M.swap)
law mv.ret.tupb:
  for +x: Hp.Cx
  for +st: Cr.Cir.State
  for +v: Bk.Term
  for +q: Bk.Quan
  for +k: Bool
  for +a: Bk.Term
  for +b: Bk.Term
  for +fs: List<&2, A.AF>
  for +iv: {R.Inv(x, st, A.AS{True{}, v, Con{A.AF{A.FK.tupb{}, q, k, a, b}, fs}}) == True{} : Bool}
  Lg.Tot(Mc.M.ret(), st, Me.Budget(x, st, A.AS{True{}, v, Con{A.AF{A.FK.tupb{}, q, k, a, b}, fs}}),
    Next(x, A.AO.next{A.AS{False{}, a, Con{A.AF{A.FK.tupa{}, q, False{}, v, v}, fs}}}),
    Halt(A.AO.next{A.AS{False{}, a, Con{A.AF{A.FK.tupa{}, q, False{}, v, v}, fs}}}))

# LAW: mode 1, the value v into Tup q a □: the value Tup q a v
law mv.ret.tupa:
  for +x: Hp.Cx
  for +st: Cr.Cir.State
  for +v: Bk.Term
  for +q: Bk.Quan
  for +k: Bool
  for +a: Bk.Term
  for +b: Bk.Term
  for +fs: List<&2, A.AF>
  for +iv: {R.Inv(x, st, A.AS{True{}, v, Con{A.AF{A.FK.tupa{}, q, k, a, b}, fs}}) == True{} : Bool}
  Lg.Tot(Mc.M.ret(), st, Me.Budget(x, st, A.AS{True{}, v, Con{A.AF{A.FK.tupa{}, q, k, a, b}, fs}}),
    Next(x, A.AO.next{A.AS{True{}, Bk.Term.Tup{q, a, v}, fs}}), Halt(A.AO.next{A.AS{True{}, Bk.Term.Tup{q, a, v}, fs}}))

# LAW: mode 1, the value v into Rwt □ P f: f, a step, when v is Rfl; else
# halt 2
law mv.ret.rwt:
  for +x: Hp.Cx
  for +st: Cr.Cir.State
  for +v: Bk.Term
  for +q: Bk.Quan
  for +k: Bool
  for +P: Bk.Term
  for +f: Bk.Term
  for +fs: List<&2, A.AF>
  for +iv: {R.Inv(x, st, A.AS{True{}, v, Con{A.AF{A.FK.rwt{}, q, k, P, f}, fs}}) == True{} : Bool}
  Lg.Tot(Mc.M.ret(), st, Me.Budget(x, st, A.AS{True{}, v, Con{A.AF{A.FK.rwt{}, q, k, P, f}, fs}}),
    Next(x, A.AM.need(A.AM.is_rfl(v), A.AS{False{}, f, fs})), Halt(A.AM.need(A.AM.is_rfl(v), A.AS{False{}, f, fs})))

# LAW: mode 1, the value v into Min □ b: b, to evaluate, in the frame Min v □
# (M.swap)
law mv.ret.minb:
  for +x: Hp.Cx
  for +st: Cr.Cir.State
  for +v: Bk.Term
  for +q: Bk.Quan
  for +k: Bool
  for +a: Bk.Term
  for +b: Bk.Term
  for +fs: List<&2, A.AF>
  for +iv: {R.Inv(x, st, A.AS{True{}, v, Con{A.AF{A.FK.minb{}, q, k, a, b}, fs}}) == True{} : Bool}
  Lg.Tot(Mc.M.ret(), st, Me.Budget(x, st, A.AS{True{}, v, Con{A.AF{A.FK.minb{}, q, k, a, b}, fs}}),
    Next(x, A.AO.next{A.AS{False{}, a, Con{A.AF{A.FK.mina{}, Bk.Quan.Q0{}, False{}, v, v}, fs}}}),
    Halt(A.AO.next{A.AS{False{}, a, Con{A.AF{A.FK.mina{}, Bk.Quan.Q0{}, False{}, v, v}, fs}}}))

# LAW: mode 1, the value v into Min a □: their meet, a step; halt 2 when there
# is none
law mv.ret.mina:
  for +x: Hp.Cx
  for +st: Cr.Cir.State
  for +v: Bk.Term
  for +q: Bk.Quan
  for +k: Bool
  for +a: Bk.Term
  for +b: Bk.Term
  for +fs: List<&2, A.AF>
  for +iv: {R.Inv(x, st, A.AS{True{}, v, Con{A.AF{A.FK.mina{}, q, k, a, b}, fs}}) == True{} : Bool}
  Lg.Tot(Mc.M.ret(), st, Me.Budget(x, st, A.AS{True{}, v, Con{A.AF{A.FK.mina{}, q, k, a, b}, fs}}),
    Next(x, A.AM.meet(El.Eval.meet(a, v), fs)), Halt(A.AM.meet(El.Eval.meet(a, v), fs)))
