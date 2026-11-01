import Interpreter.Machine.Loop

-- Machine.Fast
-- ============
--
-- run, as compiled code runs it. run keeps each state while it moves, for the
-- term that a stop, or the end of the fuel, needs; so a move can never build
-- the next state in the memory of the old one. runF hands each state to its
-- move, moveF, which gives the state back when it stops. They give the same
-- (run_runF), so each theorem about run holds of what runs.

open Quan Term

namespace Machine

-- a move, with the state itself when it stops
inductive MoveF where
  | admin (s : State)
  | step (s : State)
  | stop (s : State)

-- the move m of the state s, with s when m stops
def Move.withState : Move → State → MoveF
  | .admin s', _ => .admin s'
  | .step s', _ => .step s'
  | .stop, s => .stop s

-- callMove, its stop with the state stopS () (built only on a stop)
@[inline] def callMoveF (bk : Book) (k : String) (xs : List MArg) (st : List Frame) (v : Term)
    (vl : Locals) (stopS : Unit → State) : MoveF :=
  match bk.get k with
  | none => .stop (stopS ())
  | some d =>
    match walkOpen bk d.v .nil xs with
    | some (some (t, l, ys)) => .step ⟨.ev t l, argFrames ys ++ st⟩
    | some none => .admin ⟨.ret v vl, st⟩
    | none => .stop (stopS ())

theorem callMoveF_eq : callMoveF bk k xs st v vl stopS = (callMove bk k xs st v vl).withState (stopS ()) := by
  unfold callMoveF callMove
  split <;> (try split) <;> simp_all [Move.withState]

-- the frame that an application of a value came from: App q □ x (appArg),
-- App q □ x with x known or not to be a value (appVal), or App q f □ (appFun)
inductive AppFrom where
  | arg
  | val
  | fun

-- the state that appMove bk q f fl x xl st starts from, when it came from the frame w
def AppFrom.state (w : AppFrom) (k : Bool) (q : Quan) (f : Term) (fl : Locals) (x : Term)
    (xl : Locals) (st : List Frame) : State :=
  match w with
  | .arg => ⟨.ret f fl, .appArg q x xl :: st⟩
  | .val => ⟨.ret f fl, .appVal q x xl k :: st⟩
  | .fun => ⟨.ret x xl, .appFun q f fl :: st⟩

-- appMove, its stop with the state that it came from
@[inline] def appMoveF (bk : Book) (q : Quan) (f : Term) (fl : Locals) (x : Term) (xl : Locals)
    (st : List Frame) (w : AppFrom) (k : Bool) : MoveF :=
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
      callMoveF bk c ys st (App q (Term.ren Nat.succ f) (Var 0)) (.cons x xl q.live fl)
        (fun _ => w.state k q f fl x xl st)
    | _ => .stop (w.state k q f fl x xl st)

theorem appMoveF_eq :
    appMoveF bk q f fl x xl st w k = (appMove bk q f fl x xl st).withState (w.state k q f fl x xl st) := by
  unfold appMoveF appMove
  rcases resolve f fl with ⟨t, tl⟩
  cases t
  case Lam p b => simp only; split <;> rfl
  case Prj h =>
    simp only
    rcases resolve x xl with ⟨u, ul⟩
    cases u <;> simp only <;> (try split) <;> rfl
  case Mat j h m =>
    simp only
    rcases resolve x xl with ⟨u, ul⟩
    cases u <;> simp only <;> (try split) <;> (try split) <;> rfl
  all_goals
    simp only
    rcases unspineL _ fl [(q, x, xl, q.live)] with ⟨u, ul, ys⟩
    cases u <;> simp only <;> first | rfl | exact callMoveF_eq

-- move (with its pairs shared, as moveS), each stop with the state it stops in,
-- rebuilt from its parts so that the state itself is free when the move goes on
@[inline] def moveF (bk : Book) (s : State) : MoveF :=
  match s with
  | ⟨.ev t l, st⟩ =>
    match t with
    | Var i =>
      match l.get? i with
      | some (x, xl, true) => .admin ⟨.ret x xl, st⟩
      | some (x, xl, false) => .admin ⟨.ev x xl, st⟩
      | none => .stop ⟨.ev (Var i) l, st⟩
    | Ref k => callMoveF bk k [] st (Ref k) .nil (fun _ => ⟨.ev (Ref k) l, st⟩)
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
      if q.live then .admin ⟨.ev x l, .appFun q v vl :: st⟩ else appMoveF bk q v vl x l st .arg false
    | .appVal q x l k =>
      if q.live && !k then .admin ⟨.ev x l, .appFun q v vl :: st⟩ else appMoveF bk q v vl x l st .val k
    | .appFun q g gl => appMoveF bk q g gl v vl st .fun false
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

theorem moveF_eq : moveF bk s = (move bk s).withState s := by
  obtain ⟨fc, st⟩ := s
  cases fc with
  | ev t l =>
    cases t <;> simp only [moveF, move]
    case Var i => split <;> simp_all [Move.withState]
    case Ref k => exact callMoveF_eq
    all_goals (try split) <;> (try split) <;> rfl
  | ret v vl =>
    cases st with
    | nil => rfl
    | cons f st =>
      cases f
      case minA a =>
        simp only [moveF, move]
        split
        · rename_i heq
          split
          · simp_all [Move.withState]
          · rename_i hc
            simp only [heq, Move.withState, hc, ite_false]
        · split <;> simp_all [Move.withState]
      case appArg q x l =>
        simp only [moveF, move]; split
        · rfl
        · exact appMoveF_eq
      case appVal q x l k =>
        simp only [moveF, move]; split
        · rfl
        · exact appMoveF_eq
      case appFun q g gl => exact appMoveF_eq
      case minB b l => rfl
      all_goals simp only [moveF, move, share_eq]
      all_goals (try split) <;> rfl

-- run, each state handed to its move
def runF (bk : Book) : Nat → Nat → State → Nat → Term × Nat
  | 0, fuel, s, n => stepwise bk fuel s.term n
  | gas + 1, 0, s, n => run bk (gas + 1) 0 s n
  | gas + 1, fuel + 1, s, n =>
    match moveF bk s with
    | .admin s' => runF bk gas (fuel + 1) s' n
    | .step s' => runF bk gas fuel s' (n + 1)
    | .stop s => stepwise bk (fuel + 1) s.term n

@[csimp] theorem run_runF : @run = @runF := by
  funext bk g fuel s n
  induction g generalizing fuel s n with
  | zero => rfl
  | succ g ih =>
    cases fuel with
    | zero => simp only [runF]
    | succ fuel =>
      simp only [run, runF, moveF_eq]
      cases move bk s <;> simp only [Move.withState, ih]

end Machine
