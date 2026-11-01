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
-- own, and remembers what it knows of each: a value, or Data (so that a λ+
-- takes it without a check). A value keeps its locals too, so a λ costs the
-- same whatever it holds: the machine puts locals into a term only when the
-- term goes into a pair, or is needed whole. A spine on a def goes into the
-- def's case tree one argument after the other, each where the walk waits,
-- and a call that Ops knows (src/Interpreter/Ops.lean) takes all its steps in
-- one move. A value that needs no step (a local, a label, a pair of them) is
-- taken in the move that needs it. When the machine stops, or runs out of gas,
-- stepwise goes on from its term.

open Quan Term

namespace Machine

-- small functions of the kernel, inlined in compiled code (each proven equal)
@[inline] def liveC : Quan → Bool
  | Q0 => false
  | _ => true

@[csimp] theorem live_liveC : @Quan.live = @liveC := by
  funext q; cases q <;> rfl

@[inline] def takesC : Term → Bool
  | Lam _ _ | Prj _ | Mat _ _ _ | Efq => true
  | _ => false

@[csimp] theorem takes_takesC : @takes = @takesC := by
  funext t; cases t <;> rfl

@[inline] def getC (bk : Book) (k : String) : Option Def :=
  match bk.lib[k]? with
  | some (_, d) => some d
  | none => none

@[csimp] theorem get_getC : @Book.get = @getC := by
  funext bk k; unfold Book.get getC; split <;> simp_all

-- what is known of a term: nothing, that it is a value, or that it is Data
-- (so a λ+ takes it without a check)
inductive Know where
  | none
  | value
  | data

-- known to be a value
@[inline] def Know.isValue : Know → Bool
  | .none => false
  | _ => true

-- a value when live
@[inline] def Know.ofLive (b : Bool) : Know := if b then .value else .none

-- a value, Data when d
@[inline] def Know.ofData (d : Bool) : Know := if d then .data else .value

-- known to be Data
@[inline] def Know.isData : Know → Bool
  | .data => true
  | _ => false

-- what is known of an argument that a λ of quantity p takes: Data, when p is 2
@[inline] def Know.bind (p : Quan) (k : Know) : Know := if p = Q2 then .data else k

-- what is known of the first part, of quantity r, of a pair known k
@[inline] def Know.fst (r : Quan) (k : Know) : Know := if r.live then k else .none

-- the terms of a term's variables, the innermost first: each under its own
-- locals, with what is known of it
inductive Locals where
  | nil
  | cons (t : Term) (l : Locals) (k : Know) (rest : Locals)

-- the term of each local, under its locals
def Locals.terms : Locals → List Term
  | .nil => []
  | .cons t .nil _ rest => t :: rest.terms
  | .cons t l _ rest => sub (Env.sub l.terms) t :: rest.terms

def subst (l : Locals) : Nat → Term := Env.sub l.terms

-- subst, for compiled code: the term of a variable is put together only when a
-- term has the variable, not with the terms of all the locals
def substL : Locals → Nat → Term
  | .nil, i => Var i
  | .cons t .nil _ _, 0 => t
  | .cons t l _ _, 0 => sub (substL l) t
  | .cons _ _ _ rest, i + 1 => substL rest i

@[csimp] theorem subst_substL : @subst = @substL := by
  funext l
  induction l with
  | nil => funext i; rfl
  | cons t l k r ihl ihr =>
    funext i
    cases i with
    | zero => cases l <;> simp_all [subst, Locals.terms, Env.sub, substL]
    | succ i =>
      have := congrFun ihr i
      cases l <;> simp_all [subst, Locals.terms, Env.sub, substL]

-- the term t under its locals l
def close (t : Term) : Locals → Term
  | .nil => t
  | l => sub (subst l) t

-- l without its first v locals
def Locals.drop : Locals → Nat → Locals
  | .cons _ _ _ rest, v + 1 => rest.drop v
  | l, _ => l

-- the local v of l, when l has it (inlined, so that the pair is not built)
@[inline] def Locals.get? (l : Locals) (v : Nat) : Option (Term × Locals × Know) :=
  match l.drop v with
  | .cons t l k _ => some (t, l, k)
  | .nil => none

-- an argument of a walk: its quantity, its term under its locals, and what is
-- known of it
structure MArg where
  q : Quan
  t : Term
  l : Locals
  k : Know

-- the local v of l as an argument at q, or the variable that is beyond l
def localArg (q : Quan) : Locals → Nat → MArg
  | .nil, v => ⟨q, Var v, .nil, .none⟩
  | .cons t l k _, 0 => ⟨q, t, l, k⟩
  | .cons _ _ _ rest, v + 1 => localArg q rest v

-- t under l, with a head that is no variable of l
def resolve : Term → Locals → Term × Locals
  | Var 0, .cons t l _ _ => resolve t l
  | Var (v + 1), .cons _ _ _ rest => resolve (Var v) rest
  | t, l => (t, l)

-- resolve, for compiled code: a term that is no variable is its own head, and
-- so needs no call (resolveVar is resolve)
def resolveVar : Term → Locals → Term × Locals
  | Var 0, .cons t l _ _ => resolveVar t l
  | Var (v + 1), .cons _ _ _ rest => resolveVar (Var v) rest
  | t, l => (t, l)

@[inline] def resolveC (t : Term) (l : Locals) : Term × Locals :=
  match t with
  | Var _ => resolveVar t l
  | t => (t, l)

@[csimp] theorem resolve_resolveC : @resolve = @resolveC := by
  have e : ∀ t l, resolveVar t l = resolve t l := by
    intro t l
    fun_induction resolve t l
    case case1 ih => rw [resolveVar, ih]
    case case2 ih => rw [resolveVar, ih]
    case case3 t l h1 h2 =>
      unfold resolveVar
      split
      · rename_i t' l' _ _; exact (h1 _ _ _ _ rfl rfl).elim
      · rename_i v' _ _ _ _; exact (h2 _ _ _ _ _ rfl rfl).elim
      · rfl
  funext t l
  unfold resolveC
  split
  · exact (e _ _).symm
  · cases t <;> simp_all [resolve]

-- unspine (close t l) with the arguments xs: the head of the spine, under its
-- locals, and the arguments, each under its locals; the live ones of a value
-- are values
def unspineL : Term → Locals → List MArg → Term × Locals × List MArg
  | App q f x, l, xs => unspineL f l (⟨q, x, l, .ofLive q.live⟩ :: xs)
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

-- bindsAt p q (close x l), with k known of it
def bindsAtL (p q : Quan) (x : Term) (l : Locals) (k : Know) : Bool :=
  p.live == q.live && (p != Q2 || k.isData || dataAt x l)

-- the term has no variable: no locals change it
def noVars : Term → Bool
  | Var _ => false
  | Ref _ | Enu _ | Lab _ | Efq | Rfl => true
  | Typ a | Prj a | Lam _ a => noVars a
  | Ann a b | Term.Min a b | Let _ a b | All _ a b | App _ a b | Sig _ a b | Tup _ a b | Mat _ a b =>
    noVars a && noVars b
  | Eql a b c | Rwt a b c => noVars a && noVars b && noVars c

-- the term is labels and proofs in pairs, whose dead parts have no variable:
-- Data, and its own value under any locals
def closedData : Term → Bool
  | Lab _ | Rfl => true
  | Tup q a b => (if q.live then closedData a else noVars a) && closedData b
  | _ => false

-- where a walk of a case tree ends: at its leaf, under its locals, with the
-- arguments left; at the node that needs more arguments, under its locals;
-- or nowhere
inductive Reach where
  | leaf (t : Term) (l : Locals) (ys : List MArg)
  | need (t : Term) (l : Locals)
  | fail

-- walk (src/Shared/Interp.lean), with its leaf left open; when it needs more
-- arguments, it can go on from where it waits
def walkOpen (bk : Book) : Term → Locals → List MArg → Reach
  | Lam p f, l, ⟨q, x, xl, k⟩ :: xs =>
    if bindsAtL p q x xl k then walkOpen bk f (.cons x xl (k.bind p) l) xs else .fail
  | Prj h, l, ⟨q, x, xl, k⟩ :: xs =>
    match resolve x xl with
    | (Tup r a b, al) =>
      if q.live then
        walkOpen bk h l (⟨Quan.fld r q, a, al, k.fst r⟩ :: ⟨q, b, al, k⟩ :: xs)
      else .fail
    | _ => .fail
  | Mat j h m, l, ⟨q, x, xl, _⟩ :: xs =>
    match resolve x xl with
    | (Lab i, _) =>
      if q.live then
        if i = j then walkOpen bk h l xs else walkOpen bk m l (⟨q, Lab i, .nil, .data⟩ :: xs)
      else .fail
    | _ => .fail
  | App q f (Var v), l, xs =>
    if takes (unspine f []).1 then walkOpen bk f l (localArg q l v :: xs)
    else .leaf (App q f (Var v)) l xs
  | t, l, xs =>
    if takes t then if xs.isEmpty then .need t l else .fail
    else .leaf t l xs

-- an argument of a walk, put together
def argOf : MArg → Arg
  | ⟨q, x, l, _⟩ => (q, close x l)

-- an argument of a spine, under the locals l
def argAt (l : Locals) : Arg → Arg
  | (q, y) => (q, close y l)

-- a term with a hole, around the focus
inductive Frame where
  -- App a.q □ a.t, with the argument a under its locals
  | appArg (a : MArg)
  -- App q f □, with f under l a value
  | appFun (q : Quan) (f : Term) (l : Locals)
  -- Let q □ f, with f under l
  | letIn (q : Quan) (f : Term) (l : Locals)
  -- Tup q □ b, with b under l
  | tupB (q : Quan) (b : Term) (l : Locals)
  -- Tup q a □, with a under l a value when q is live, known to be Data when d
  | tupA (q : Quan) (a : Term) (l : Locals) (d : Bool)
  -- Rwt □ P f, with P and f under l
  | rwt (P f : Term) (l : Locals)
  -- Min □ b, with b under l
  | minB (b : Term) (l : Locals)
  -- App q (spine (Ref k) xs) □, then the arguments ys under l: a call of k,
  -- with xs the last first (rxs), whose walk waits at t under tl
  | call (k : String) (t : Term) (tl : Locals) (rxs : List MArg) (q : Quan) (ys : List Arg)
    (l : Locals)
  -- Min a □, with a a value
  | minA (a : Term)

-- the frame, with t in its hole
def Frame.plug : Frame → Term → Term
  | .appArg a, t => App a.q t (close a.t a.l)
  | .appFun q f l, t => App q (close f l) t
  | .letIn q f l, t => Let q t (sub (Subst.up (subst l)) f)
  | .tupB q b l, t => Tup q t (close b l)
  | .tupA q a l _, t => Tup q (close a l) t
  | .rwt P f l, t => Rwt t (sub (Subst.up (Subst.up (subst l))) P) (close f l)
  | .minB b l, t => Term.Min t (close b l)
  | .call k _ _ rxs q ys l, t => spine (App q (spine (Ref k) (rxs.reverse.map argOf)) t) (ys.map (argAt l))
  | .minA a, t => Term.Min a t

inductive Focus where
  -- t under l, to evaluate
  | ev (t : Term) (l : Locals)
  -- the value v under l, known to be Data when d
  | ret (v : Term) (l : Locals) (d : Bool)

-- the focus, and its frames, the innermost first
structure State where
  focus : Focus
  stack : List Frame

def Focus.term : Focus → Term
  | .ev t l => close t l
  | .ret v l _ => close v l

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
def argFrames (ys : List MArg) : List Frame := ys.map .appArg

-- the call of k on xs, when the table tb of Ops has k: its value and its steps
def opsCall (tb : Ops.Table) (k : String) (xs : List MArg) : Option (Term × Nat) :=
  match tb.ops[k]? with
  | some op => op.run (xs.map argOf)
  | none => none

-- the call of k on xs, in the frames st, whose walk leaves its case tree at u
-- under ul with the arguments zs left: its value, when Ops knows it, else a
-- step to the leaf. from_ () is the state that it came from.
@[inline] def fire (tb : Ops.Table) (k : String) (xs : List MArg) (u : Term) (ul : Locals)
    (zs : List MArg) (st : List Frame) (from_ : Unit → State) : Move :=
  match opsCall tb k xs with
  | some (r, n) => .jump n ⟨.ret r .nil true, st⟩ (from_ ())
  | none => .step ⟨.ev u ul, argFrames zs ++ st⟩

-- a call of k on xs, in the frames st: fire at the leaf of its case tree; or v
-- under vl, a value, when the case tree needs more arguments
@[inline] def callMove (bk : Book) (tb : Ops.Table) (k : String) (xs : List MArg) (st : List Frame)
    (v : Term) (vl : Locals) (from_ : Unit → State) : Move :=
  match bk.get k with
  | none => .stop (from_ ())
  | some d =>
    match walkOpen bk d.v .nil xs with
    | .leaf u ul zs => fire tb k xs u ul zs st from_
    | .need _ _ => .admin ⟨.ret v vl false, st⟩
    | .fail => .stop (from_ ())

-- App a.q f a.t, in the frames st, with f under fl a value, and the argument a
-- a value when it is live; from_ () is the state that it came from
@[inline] def appMove (bk : Book) (tb : Ops.Table) (f : Term) (fl : Locals) (a : MArg)
    (st : List Frame) (from_ : Unit → State) : Move :=
  match resolve f fl with
  | (Lam p b, bl) =>
    if bindsAtL p a.q a.t a.l a.k then .step ⟨.ev b (.cons a.t a.l (a.k.bind p) bl), st⟩
    else .stop (from_ ())
  | (Prj h, hl) =>
    match resolve a.t a.l with
    | (Tup r x y, xl) =>
      if a.q.live then .step ⟨.ev h hl, .appArg ⟨Quan.fld r a.q, x, xl, a.k.fst r⟩ :: .appArg ⟨a.q, y, xl, a.k⟩ :: st⟩
      else .stop (from_ ())
    | _ => .stop (from_ ())
  | (Mat j h m, hl) =>
    match resolve a.t a.l with
    | (Lab i, _) =>
      if a.q.live then
        if i = j then .step ⟨.ev h hl, st⟩ else .step ⟨.ev m hl, .appArg ⟨a.q, Lab i, .nil, .data⟩ :: st⟩
      else .stop (from_ ())
    | _ => .stop (from_ ())
  | _ =>
    match unspineL f fl [⟨a.q, a.t, a.l, .ofLive a.q.live⟩] with
    | (Ref c, _, ys) =>
      callMove bk tb c ys st (App a.q (Term.ren Nat.succ f) (Var 0)) (.cons a.t a.l (.ofLive a.q.live) fl) from_
    | _ => .stop (from_ ())

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

-- the value of t under l, when it is one without a step and without a frame:
-- a value that l knows, a label, Data in pairs with no variable, a node of a
-- case tree or a former; and whether it is known to be Data
@[inline] def imm (t : Term) (l : Locals) : Option (Term × Locals × Bool) :=
  match t with
  | Var i =>
    match l.get? i with
    | some (x, xl, k) => if k.isValue then some (x, xl, k.isData) else none
    | none => none
  | Lab _ | Rfl => some (t, .nil, true)
  | Tup .. => if closedData t then some (t, .nil, true) else none
  | Efq | Enu _ => some (t, .nil, false)
  | Lam .. | Prj _ | Mat .. | Typ _ | All .. | Sig .. | Eql .. => some (t, l, false)
  | _ => none

-- the value v under vl, known to be Data when d, in the frames st: each pair of
-- the frames that it completes without a step is put together
def retTups (v : Term) (vl : Locals) (d : Bool) : List Frame → State
  | .tupA q a al da :: st => retTups (share (Tup q (close a al) (close v vl))) .nil ((!q.live || da) && d) st
  | .tupB q b l :: st =>
    match imm b l with
    | some (b', bl, db) => retTups (share (Tup q (close v vl) (close b' bl))) .nil (d && db) st
    | none => ⟨.ev b l, .tupA q v vl d :: st⟩
  | st => ⟨.ret v vl d, st⟩

-- Tup q a b under l, in the frames st: its value, or the frames of its parts
-- down to the first part that takes a step
def evTup (q : Quan) (a b : Term) (l : Locals) (st : List Frame) : Move :=
  match (if q.live then imm a l else some (a, l, true)) with
  | none => .admin ⟨.ev a l, .tupB q b l :: st⟩
  | some (a', al, da) =>
    match imm b l with
    | some (b', bl, db) => .admin (retTups (share (Tup q (close a' al) (close b' bl))) .nil (da && db) st)
    | none =>
      match b with
      | Tup q' a2 b2 => evTup q' a2 b2 l (.tupA q a' al da :: st)
      | b => .admin ⟨.ev b l, .tupA q a' al da :: st⟩

-- the frames of the arguments ys under l, the first innermost, around st
def appArgs (l : Locals) : List Arg → List Frame → List Frame
  | [], st => st
  | (q, y) :: ys, st => .appArg ⟨q, y, l, .none⟩ :: appArgs l ys st

-- the argument y at q under l, when it can go into a walk without a move: dead,
-- or a value without a step
def ready (q : Quan) (y : Term) (l : Locals) : Option MArg :=
  if q.live then
    match imm y l with
    | some (x, xl, d) => some ⟨q, x, xl, .ofData d⟩
    | none => none
  else some ⟨q, y, l, .none⟩

-- spine (Ref k) xs, with xs the last first (rxs), as a term under its locals
def papOf (k : String) : List MArg → Term × Locals
  | [] => (Ref k, .nil)
  | ⟨q, x, xl, b⟩ :: rxs => (App q (Term.ren Nat.succ (papOf k rxs).1) (Var 0), .cons x xl b (papOf k rxs).2)

-- the argument a goes into the call of k, whose walk waits at t under tl after
-- rxs, with the arguments ys under l after it: fire at the leaf of its case
-- tree, or next u ul when the walk waits at u under ul
@[inline] def feed (bk : Book) (tb : Ops.Table) (k : String) (t : Term) (tl : Locals) (rxs : List MArg)
    (a : MArg) (ys : List Arg) (l : Locals) (st : List Frame) (next : Term → Locals → Move) : Move :=
  let from_ : Unit → State := fun _ => ⟨.ret a.t a.l false, .call k t tl rxs a.q ys l :: st⟩
  match walkOpen bk t tl [a] with
  | .need u ul => next u ul
  | .leaf u ul zs => fire tb k (a :: rxs).reverse u ul zs (appArgs l ys st) from_
  | .fail => .stop (from_ ())

-- the arguments ys under l go, one after the other, into the call of k, whose
-- walk waits at t under tl after rxs; one that must take steps first gets a
-- frame
def go (bk : Book) (tb : Ops.Table) (k : String) (t : Term) (tl : Locals) (rxs : List MArg)
    (l : Locals) (st : List Frame) : List Arg → Move
  | [] => .admin ⟨.ret (papOf k rxs).1 (papOf k rxs).2 false, st⟩
  | (q, y) :: ys =>
    match ready q y l with
    | some a => feed bk tb k t tl rxs a ys l st fun u ul => go bk tb k u ul (a :: rxs) l st ys
    | none => .admin ⟨.ev y l, .call k t tl rxs q ys l :: st⟩

-- the call that the spine t starts: its def, whose case tree takes arguments,
-- and its arguments
@[inline] def spineCall (bk : Book) (t : Term) : Option (String × Def × List Arg) :=
  match unspine t [] with
  | (Ref k, ys) =>
    match bk.get k with
    | some d => if takes d.v then some (k, d, ys) else none
    | none => none
  | _ => none

-- t under l, in the frames st, when t is no value that needs no step (imm)
@[inline] def evMove (bk : Book) (tb : Ops.Table) (t : Term) (l : Locals) (st : List Frame) : Move :=
  match t with
  | Var i =>
    match l.get? i with
    | some (x, xl, _) => .admin ⟨.ev x xl, st⟩
    | none => .stop ⟨.ev (Var i) l, st⟩
  | Ref k => callMove bk tb k [] st (Ref k) .nil (fun _ => ⟨.ev (Ref k) l, st⟩)
  | Ann x _ => .step ⟨.ev x l, st⟩
  | App q f x =>
    match spineCall bk (App q f x) with
    | some (k, d, ys) => go bk tb k d.v .nil [] l st ys
    | none => .admin ⟨.ev f l, .appArg ⟨q, x, l, .none⟩ :: st⟩
  | Let q v f =>
    if q.live then .admin ⟨.ev v l, .letIn q f l :: st⟩
    else .step ⟨.ev f (.cons v l .none l), st⟩
  | Tup q a b => evTup q a b l st
  | Rwt e P f => .admin ⟨.ev e l, .rwt P f l :: st⟩
  | Term.Min a b => .admin ⟨.ev a l, .minB b l :: st⟩
  | t => .stop ⟨.ev t l, st⟩

-- a let of quantity q takes the value v under vl, known to be Data when d: Data,
-- when q is 2
@[inline] def letTakes (q : Quan) (v : Term) (vl : Locals) (d : Bool) : Bool :=
  q != Q2 || d || dataAt v vl

-- Min a v, with v under vl known to be Data when d, in the frames st: the meet
-- of two labels of quantities
@[inline] def meetMove (a v : Term) (vl : Locals) (d : Bool) (st : List Frame) : Move :=
  match a, (resolve v vl).1 with
  | Lab i, Lab j =>
    if i ∈ QS ∧ j ∈ QS then .step ⟨.ev (Term.qmin (Lab i) (Lab j)) .nil, st⟩
    else .stop ⟨.ret v vl d, .minA a :: st⟩
  | _, _ => .stop ⟨.ret v vl d, .minA a :: st⟩

-- the value v under vl, known to be Data when d, into the frame f around st
@[inline] def retMove (bk : Book) (tb : Ops.Table) (v : Term) (vl : Locals) (d : Bool) (f : Frame)
    (st : List Frame) : Move :=
  match f with
  | .appArg a =>
    if a.q.live && !a.k.isValue then .admin ⟨.ev a.t a.l, .appFun a.q v vl :: st⟩
    else appMove bk tb v vl a st fun _ => ⟨.ret v vl d, .appArg a :: st⟩
  | .appFun q g gl => appMove bk tb g gl ⟨q, v, vl, .ofData d⟩ st fun _ => ⟨.ret v vl d, .appFun q g gl :: st⟩
  | .letIn q f l =>
    if letTakes q v vl d then .step ⟨.ev f (.cons v vl ((Know.ofData d).bind q) l), st⟩
    else .stop ⟨.ret v vl d, .letIn q f l :: st⟩
  | .tupB q b l => .admin (retTups v vl d (.tupB q b l :: st))
  | .tupA q a al da => .admin (retTups v vl d (.tupA q a al da :: st))
  | .rwt P f l =>
    if (resolve v vl).1 = Rfl then .step ⟨.ev f l, st⟩ else .stop ⟨.ret v vl d, .rwt P f l :: st⟩
  | .minB b l =>
    .admin ⟨.ev b l, .minA (match resolve v vl with | (Lab i, _) => Lab i | _ => close v vl) :: st⟩
  | .call k t tl rxs q ys l =>
    feed bk tb k t tl rxs ⟨q, v, vl, .ofData d⟩ ys l st fun u ul =>
      go bk tb k u ul (⟨q, v, vl, .ofData d⟩ :: rxs) l st ys
  | .minA a => meetMove a v vl d st

def move (bk : Book) (tb : Ops.Table) : State → Move
  | ⟨.ev t l, st⟩ =>
    match imm t l with
    | some (v, vl, d) => .admin ⟨.ret v vl d, st⟩
    | none => evMove bk tb t l st
  | ⟨.ret v vl d, []⟩ => .stop ⟨.ret v vl d, []⟩
  | ⟨.ret v vl d, f :: st⟩ => retMove bk tb v vl d f st

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
