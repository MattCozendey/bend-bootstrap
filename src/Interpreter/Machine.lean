import Interpreter.Stepwise
import Interpreter.Ops
import Shared.Bytes

-- Machine
-- =======
--
-- Runs of Eval that cost about the same for each step, at any size of the
-- term. stepwise (src/Interpreter/Stepwise.lean) starts each step again from the top
-- of the term, and checks again that each part to the left is a value. The
-- machine keeps its place: a focus, and the frames around it. It evaluates a
-- term under the terms of its variables, its locals, each under locals of its
-- own, and remembers which of them are values. A value keeps its locals too,
-- and so do the arguments of a call that waits for more, so a λ costs the
-- same whatever it holds: the machine puts locals into a term only when the
-- term goes into a pair, or is needed whole. A call that Ops knows
-- (src/Interpreter/Ops.lean) takes all its steps in one move. When it stops,
-- or runs out of gas, stepwise goes on from its term.

open Quan Term

namespace Machine

-- the terms of a term's variables, the innermost first: each under its own
-- locals, with whether it is known to be a value
inductive Locals where
  | nil
  | cons (t : Term) (l : Locals) (k : Bool) (rest : Locals)

-- the term of each local, under its locals
def Locals.terms : Locals → List Term
  | .nil => []
  | .cons t .nil _ rest => t :: rest.terms
  | .cons t l _ rest => sub (Env.sub l.terms) t :: rest.terms

def subst (l : Locals) : Nat → Term := Env.sub l.terms

-- the term t under its locals l
def close (t : Term) : Locals → Term
  | .nil => t
  | l => sub (subst l) t

-- the local v of l, when l has it
def Locals.get? : Locals → Nat → Option (Term × Locals × Bool)
  | .nil, _ => none
  | .cons t l k _, 0 => some (t, l, k)
  | .cons _ _ _ rest, v + 1 => rest.get? v

-- the local v of l, or the variable it is beyond l
def localAt : Locals → Nat → Term × Locals × Bool
  | .nil, v => (Var v, .nil, false)
  | .cons t l k _, 0 => (t, l, k)
  | .cons _ _ _ rest, v + 1 => localAt rest v

-- an argument of a walk: its quantity, its term under its locals, and whether
-- it is known to be a value
abbrev MArg := Quan × Term × Locals × Bool

-- t under l, with a head that is no variable of l
def resolve : Term → Locals → Term × Locals
  | Var 0, .cons t l _ _ => resolve t l
  | Var (v + 1), .cons _ _ _ rest => resolve (Var v) rest
  | t, l => (t, l)

-- unspine (close t l) with the arguments xs: the head of the spine, under its
-- locals, and the arguments, each under its locals; the live ones of a value
-- are values
def unspineL : Term → Locals → List MArg → Term × Locals × List MArg
  | App q f x, l, xs => unspineL f l ((q, x, l, q.live) :: xs)
  | Var 0, .cons t l _ _, xs => unspineL t l xs
  | Var (v + 1), .cons _ _ _ rest, xs => unspineL (Var v) rest xs
  | t, l, xs => (t, l, xs)
termination_by t l => (sizeOf l, sizeOf t)

-- data (close t l), without putting l into t
def dataAt : Term → Locals → Bool
  | Lab _, _ => true
  | Rfl, _ => true
  | Tup q a b, l => (!q.live || dataAt a l) && dataAt b l
  | Var 0, .cons t l _ _ => dataAt t l
  | Var (v + 1), .cons _ _ _ rest => dataAt (Var v) rest
  | _, _ => false
termination_by t l => (sizeOf l, sizeOf t)

-- bindsAt p q (close x l)
def bindsAtL (p q : Quan) (x : Term) (l : Locals) : Bool :=
  p.live == q.live && (p != Q2 || dataAt x l)

-- the term has no variable: no locals change it
def noVars : Term → Bool
  | Var _ => false
  | Ref _ | Enu _ | Lab _ | Efq | Rfl => true
  | Typ a | Prj a | Lam _ a => noVars a
  | Ann a b | Term.Min a b | Let _ a b | All _ a b | App _ a b | Sig _ a b | Tup _ a b | Mat _ a b =>
    noVars a && noVars b
  | Eql a b c | Rwt a b c => noVars a && noVars b && noVars c

-- walk (src/Shared/Interp.lean), with its leaf left open: the leaf, its locals,
-- and the arguments left
def walkOpen (bk : Book) : Term → Locals → List MArg → Option (Option (Term × Locals × List MArg))
  | Lam p f, l, (q, x, xl, k) :: xs =>
    if bindsAtL p q x xl then walkOpen bk f (.cons x xl k l) xs else none
  | Prj h, l, (q, x, xl, k) :: xs =>
    match resolve x xl with
    | (Tup r a b, al) =>
      if q.live then walkOpen bk h l ((Quan.fld r q, a, al, k && r.live) :: (q, b, al, k) :: xs)
      else none
    | _ => none
  | Mat j h m, l, (q, x, xl, _) :: xs =>
    match resolve x xl with
    | (Lab i, _) =>
      if q.live then
        if i = j then walkOpen bk h l xs else walkOpen bk m l ((q, Lab i, .nil, true) :: xs)
      else none
    | _ => none
  | App q f (Var v), l, xs =>
    if takes (unspine f []).1 then walkOpen bk f l ((q, localAt l v) :: xs)
    else some (some (App q f (Var v), l, xs))
  | t, l, xs =>
    if takes t then if xs.isEmpty then some none else none
    else some (some (t, l, xs))

-- a term with a hole, around the focus
inductive Frame where
  -- App q □ x, with x under l
  | appArg (q : Quan) (x : Term) (l : Locals)
  -- App q □ x, with x under l, known to be a value when k
  | appVal (q : Quan) (x : Term) (l : Locals) (k : Bool)
  -- App q f □, with f under l a value
  | appFun (q : Quan) (f : Term) (l : Locals)
  -- Let q □ f, with f under l
  | letIn (q : Quan) (f : Term) (l : Locals)
  -- Tup q □ b, with b under l
  | tupB (q : Quan) (b : Term) (l : Locals)
  -- Tup q a □, with a under l a value when q is live
  | tupA (q : Quan) (a : Term) (l : Locals)
  -- Rwt □ P f, with P and f under l
  | rwt (P f : Term) (l : Locals)
  -- Min □ b, with b under l
  | minB (b : Term) (l : Locals)
  -- Min a □, with a a value
  | minA (a : Term)

-- the frame, with t in its hole
def Frame.plug : Frame → Term → Term
  | .appArg q x l, t => App q t (close x l)
  | .appVal q x l _, t => App q t (close x l)
  | .appFun q f l, t => App q (close f l) t
  | .letIn q f l, t => Let q t (sub (Subst.up (subst l)) f)
  | .tupB q b l, t => Tup q t (close b l)
  | .tupA q a l, t => Tup q (close a l) t
  | .rwt P f l, t => Rwt t (sub (Subst.up (Subst.up (subst l))) P) (close f l)
  | .minB b l, t => Term.Min t (close b l)
  | .minA a, t => Term.Min a t

inductive Focus where
  -- t under l, to evaluate
  | ev (t : Term) (l : Locals)
  -- the value v under l
  | ret (v : Term) (l : Locals)

-- the focus, and its frames, the innermost first
structure State where
  focus : Focus
  stack : List Frame

def Focus.term : Focus → Term
  | .ev t l => close t l
  | .ret v l => close v l

-- the frames st around t, the innermost first
def plugs (st : List Frame) (t : Term) : Term := st.foldl (fun t f => f.plug t) t

-- the whole term of the state
def State.term (s : State) : Term := plugs s.stack s.focus.term

def init (t : Term) : State := ⟨.ev t .nil, []⟩

-- a move: no step of Eval, or one, or n at once (with the state it came from,
-- for a run with less fuel), or none possible (with the state it came from,
-- for stepwise). A move gets its state for itself, so that it can build the
-- next state in the memory of the old one.
inductive Move where
  | admin (s : State)
  | step (s : State)
  | jump (n : Nat) (s from_ : State)
  | stop (from_ : State)

-- the frames of a spine's arguments, the innermost first
def argFrames (ys : List MArg) : List Frame := ys.map fun (q, y, l, k) => .appVal q y l k

-- an argument put together, from its head: the locals that its head does not
-- use are not put into a term
def argOfR : MArg → Arg
  | (q, x, l, _) => (q, close (resolve x l).1 (resolve x l).2)

-- the call of k on xs, when the table tb of Ops has k: its value and its steps
def opsCall (tb : Ops.Table) (k : String) (xs : List MArg) : Option (Term × Nat) :=
  match tb.ops[k]? with
  | some op => op.run (xs.map argOfR)
  | none => none

-- a call of k on xs, in the frames st: its value, when Ops knows it; else the
-- leaf of its case tree; or v under vl, a value, when the case tree needs more
-- arguments. from_ () is the state that it came from.
@[inline] def callMove (bk : Book) (tb : Ops.Table) (k : String) (xs : List MArg) (st : List Frame)
    (v : Term) (vl : Locals) (from_ : Unit → State) : Move :=
  match opsCall tb k xs with
  | some (r, n) => .jump n ⟨.ret r .nil, st⟩ (from_ ())
  | none =>
    match bk.get k with
    | none => .stop (from_ ())
    | some d =>
      match walkOpen bk d.v .nil xs with
      | some (some (t, l, ys)) => .step ⟨.ev t l, argFrames ys ++ st⟩
      | some none => .admin ⟨.ret v vl, st⟩
      | none => .stop (from_ ())

-- the frame that an application of a value came from: App q □ x (appArg),
-- App q □ x with x known or not to be a value (appVal), or App q f □ (appFun)
inductive AppFrom where
  | arg
  | val
  | fun

-- the state that appMove bk tb q f fl x xl st w k comes from
def AppFrom.state (w : AppFrom) (k : Bool) (q : Quan) (f : Term) (fl : Locals) (x : Term)
    (xl : Locals) (st : List Frame) : State :=
  match w with
  | .arg => ⟨.ret f fl, .appArg q x xl :: st⟩
  | .val => ⟨.ret f fl, .appVal q x xl k :: st⟩
  | .fun => ⟨.ret x xl, .appFun q f fl :: st⟩

-- App q f x, in the frames st, with f under fl a value, and x under xl a value
-- when q is live; it came from the frame w
@[inline] def appMove (bk : Book) (tb : Ops.Table) (q : Quan) (f : Term) (fl : Locals) (x : Term)
    (xl : Locals) (st : List Frame) (w : AppFrom) (k : Bool) : Move :=
  match resolve f fl with
  | (Lam p b, bl) =>
    if bindsAtL p q x xl then .step ⟨.ev b (.cons x xl q.live bl), st⟩
    else .stop (w.state k q f fl x xl st)
  | (Prj h, hl) =>
    match resolve x xl with
    | (Tup r a b, al) =>
      if q.live then .step ⟨.ev h hl, .appVal (Quan.fld r q) a al r.live :: .appVal q b al true :: st⟩
      else .stop (w.state k q f fl x xl st)
    | _ => .stop (w.state k q f fl x xl st)
  | (Mat j h m, hl) =>
    match resolve x xl with
    | (Lab i, _) =>
      if q.live then
        if i = j then .step ⟨.ev h hl, st⟩ else .step ⟨.ev m hl, .appVal q (Lab i) .nil true :: st⟩
      else .stop (w.state k q f fl x xl st)
    | _ => .stop (w.state k q f fl x xl st)
  | _ =>
    match unspineL f fl [(q, x, xl, q.live)] with
    | (Ref c, _, ys) =>
      callMove bk tb c ys st (App q (Term.ren Nat.succ f) (Var 0)) (.cons x xl q.live fl)
        (fun _ => w.state k q f fl x xl st)
    | _ => .stop (w.state k q f fl x xl st)

-- c when it is t, else t: t either way
def pick (c t : Term) : Term := if c = t then c else t

theorem pick_eq : pick c t = t := by
  unfold pick; split <;> simp_all

-- t, or its copy in byteTable when t is a byte (src/Shared/Bytes.lean): each
-- pair that the machine builds is shared
def share (t : Term) : Term :=
  match unbits 8 t with
  | some v => if h : v < 256 then pick (byteTable[v]'(by rw [byteTable_size]; exact h)) t else t
  | none => t

theorem share_eq : share t = t := by
  unfold share
  split
  · split
    · exact pick_eq
    · rfl
  · rfl

def move (bk : Book) (tb : Ops.Table) : State → Move
  | ⟨.ev t l, st⟩ =>
    match t with
    | Var i =>
      match l.get? i with
      | some (x, xl, true) => .admin ⟨.ret x xl, st⟩
      | some (x, xl, false) => .admin ⟨.ev x xl, st⟩
      | none => .stop ⟨.ev (Var i) l, st⟩
    | Ref k => callMove bk tb k [] st (Ref k) .nil (fun _ => ⟨.ev (Ref k) l, st⟩)
    | Ann x _ => .step ⟨.ev x l, st⟩
    | App q f x => .admin ⟨.ev f l, .appArg q x l :: st⟩
    | Let q v f =>
      if q.live then .admin ⟨.ev v l, .letIn q f l :: st⟩
      else .step ⟨.ev f (.cons v l false l), st⟩
    | Tup q a b =>
      if noVars (Tup q a b) && value bk (Tup q a b) then .admin ⟨.ret (Tup q a b) .nil, st⟩
      else if q.live then .admin ⟨.ev a l, .tupB q b l :: st⟩
      else .admin ⟨.ev b l, .tupA q a l :: st⟩
    | Rwt e P f => .admin ⟨.ev e l, .rwt P f l :: st⟩
    | Term.Min a b => .admin ⟨.ev a l, .minB b l :: st⟩
    | Lab k => .admin ⟨.ret (Lab k) .nil, st⟩
    | Rfl => .admin ⟨.ret Rfl .nil, st⟩
    | Efq => .admin ⟨.ret Efq .nil, st⟩
    | Enu ks => .admin ⟨.ret (Enu ks) .nil, st⟩
    | t => .admin ⟨.ret t l, st⟩
  | ⟨.ret v vl, []⟩ => .stop ⟨.ret v vl, []⟩
  | ⟨.ret v vl, f :: st⟩ =>
    match f with
    | .appArg q x l =>
      if q.live then .admin ⟨.ev x l, .appFun q v vl :: st⟩ else appMove bk tb q v vl x l st .arg false
    | .appVal q x l k =>
      if q.live && !k then .admin ⟨.ev x l, .appFun q v vl :: st⟩
      else appMove bk tb q v vl x l st .val k
    | .appFun q g gl => appMove bk tb q g gl v vl st .fun false
    | .letIn q f l =>
      if q != Q2 || dataAt v vl then .step ⟨.ev f (.cons v vl true l), st⟩
      else .stop ⟨.ret v vl, .letIn q f l :: st⟩
    | .tupB q b l => .admin ⟨.ev b l, .tupA q v vl :: st⟩
    | .tupA q a al => .admin ⟨.ret (share (Tup q (close a al) (close v vl))) .nil, st⟩
    | .rwt P f l =>
      if (resolve v vl).1 = Rfl then .step ⟨.ev f l, st⟩ else .stop ⟨.ret v vl, .rwt P f l :: st⟩
    | .minB b l =>
      .admin ⟨.ev b l, .minA (match resolve v vl with | (Lab i, _) => Lab i | _ => close v vl) :: st⟩
    | .minA a =>
      match a, (resolve v vl).1 with
      | Lab i, Lab j =>
        if i ∈ QS ∧ j ∈ QS then .step ⟨.ev (Term.qmin (Lab i) (Lab j)) .nil, st⟩
        else .stop ⟨.ret v vl, .minA a :: st⟩
      | _, _ => .stop ⟨.ret v vl, .minA a :: st⟩

-- the moves that a run makes before stepwise takes over: far more than a run
-- can make in practice
def gas : Nat := 2 ^ 60

-- at most fuel more steps of the state s, after n: the term reached, and the
-- steps in all; tb is the book's table of Ops (Ops.prepare)
def run (bk : Book) (tb : Ops.Table) : Nat → Nat → State → Nat → Term × Nat
  | 0, fuel, s, n => stepwise bk fuel s.term n
  | _ + 1, 0, s, n => (s.term, n)
  | gas + 1, fuel + 1, s, n =>
    match move bk tb s with
    | .admin s' => run bk tb gas (fuel + 1) s' n
    | .step s' => run bk tb gas fuel s' (n + 1)
    | .jump k s' s => if k ≤ fuel + 1 then run bk tb gas (fuel + 1 - k) s' (n + k) else (s.term, n)
    | .stop s => stepwise bk (fuel + 1) s.term n

end Machine
