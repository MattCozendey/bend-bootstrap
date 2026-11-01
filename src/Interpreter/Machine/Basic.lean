import Interpreter.Machine

-- Machine.Basic
-- =============
--
-- What a state of the machine knows, and the facts about its terms that the
-- proofs of its moves use.

open Quan Term

namespace Machine

-- what is known of t is true
def Know.Ok (bk : Book) (t : Term) : Know → Prop
  | .none => True
  | .value => Value bk t
  | .data => Data t

-- Data is a value
theorem data_value (h : Data t) : Value bk t := by
  induction h with
  | lab => exact .lab
  | rfl => exact .rfl
  | tup _ _ iha ihb => exact .tup iha ihb

-- a term known to be a value is one
theorem Know.Ok.value (h : Know.Ok bk t k) (hv : k.isValue = true) : Value bk t := by
  cases k
  · cases hv
  · exact h
  · exact data_value h

-- a term known to be Data is
theorem Know.Ok.data (h : Know.Ok bk t k) (hd : k.isData = true) : Data t := by
  cases k <;> simp [Know.isData] at hd
  exact h

theorem Know.ofData_ok (hv : Value bk t) (hd : d = true → Data t) : (Know.ofData d).Ok bk t := by
  cases d
  · exact hv
  · exact hd rfl

theorem Know.ofData_isValue : (Know.ofData d).isValue = true := by
  cases d <;> rfl

theorem Know.ofLive_ok (h : b = true → Value bk t) : (Know.ofLive b).Ok bk t := by
  cases b
  · trivial
  · exact h rfl

theorem Know.ofLive_isValue : (Know.ofLive b).isValue = b := by
  cases b <;> rfl

-- what a λ of quantity p knows of what it takes
theorem Know.bind_ok (hk : Know.Ok bk t k) (hd : p = Q2 → Data t) : (k.bind p).Ok bk t := by
  unfold Know.bind
  split
  · exact hd ‹_›
  · exact hk

-- what each local knows of itself is true, and its own locals know the same
def Locals.Ok (bk : Book) : Locals → Prop
  | .nil => True
  | .cons t l k rest => k.Ok bk (close t l) ∧ l.Ok bk ∧ rest.Ok bk

-- an argument put together, by its parts
theorem argOf_eq : argOf a = (a.q, close a.t a.l) := rfl

-- the locals of an argument know what is true, and so does what is known of it
def argOk (bk : Book) (a : MArg) : Prop :=
  a.l.Ok bk ∧ a.k.Ok bk (close a.t a.l)

-- a call of k whose walk waits at t under tl after the arguments rxs, the last
-- first: each argument is a value when it is live, and the walk of k's case tree
-- on them goes on as the walk from t under tl
def CallOk (bk : Book) (k : String) (t : Term) (tl : Locals) (rxs : List MArg) : Prop :=
  takes t = true ∧ tl.Ok bk ∧ (∀ a ∈ rxs, argOk bk a ∧ a.k.isValue = a.q.live) ∧
    ∃ d, Book.get bk k = some d ∧
      ∀ zs, walk bk d.v [] (rxs.reverse.map argOf ++ zs) = walk bk t tl.terms zs

-- what a frame knows is true
def Frame.Ok (bk : Book) : Frame → Prop
  | .appArg a => argOk bk a
  | .appFun q f l => q.live = true ∧ Value bk (close f l) ∧ l.Ok bk
  | .letIn q _ l => q.live = true ∧ l.Ok bk
  | .tupB q _ l => q.live = true ∧ l.Ok bk
  | .tupA q a l d => (q.live = true → Value bk (close a l)) ∧ l.Ok bk ∧
      (q.live = true → d = true → Data (close a l))
  | .rwt _ _ l => l.Ok bk
  | .minB _ l => l.Ok bk
  | .call k t tl rxs q _ l => q.live = true ∧ CallOk bk k t tl rxs ∧ l.Ok bk
  | .minA a => Value bk a

def Focus.Ok (bk : Book) : Focus → Prop
  | .ev _ l => l.Ok bk
  | .ret v l d => Value bk (close v l) ∧ l.Ok bk ∧ (d = true → Data (close v l))

-- what the state knows is true
def State.Ok (bk : Book) (s : State) : Prop := s.focus.Ok bk ∧ ∀ f ∈ s.stack, f.Ok bk

theorem plugs_append : plugs (fs ++ st) t = plugs st (plugs fs t) := by
  simp [plugs, List.foldl_append]

-- the terms of locals, each under its own locals
theorem terms_cons : (Locals.cons t l k r).terms = close t l :: r.terms := by
  cases l <;> rfl

-- the term of each variable under locals
theorem subst_nil : subst .nil = Var := by
  funext i; rfl

theorem subst_zero : subst (.cons t l k r) 0 = close t l := by
  simp only [subst, terms_cons, Env.sub]

theorem subst_succ : subst (.cons t l k r) (i + 1) = subst r i := by
  simp only [subst, terms_cons, Env.sub]

-- a term under its locals, by its head
theorem close_nil : close t .nil = t := rfl

theorem close_eq : close t l = sub (subst l) t := by
  cases l with
  | nil => rw [subst_nil, sub_var]; rfl
  | cons => rfl

theorem close_var : close (Var i) l = subst l i := by
  rw [close_eq]; rfl

theorem close_lab : close (Lab i) l = Lab i := by
  simp only [close_eq, sub]

theorem close_rfl : close Rfl l = Rfl := by
  simp only [close_eq, sub]

theorem close_ref : close (Ref k) l = Ref k := by
  simp only [close_eq, sub]

theorem close_lam : close (Lam p b) l = Lam p (sub (Subst.up (subst l)) b) := by
  simp only [close_eq, sub]

theorem close_prj : close (Prj h) l = Prj (close h l) := by
  simp only [close_eq, sub]

theorem close_mat : close (Mat j h m) l = Mat j (close h l) (close m l) := by
  simp only [close_eq, sub]

theorem close_app : close (App q f x) l = App q (close f l) (close x l) := by
  simp only [close_eq, sub]

theorem close_tup : close (Tup q a b) l = Tup q (close a l) (close b l) := by
  simp only [close_eq, sub]

-- no locals change a term with no variable
theorem noVars_sub (h : noVars t = true) : sub σ t = t := by
  induction t generalizing σ <;> simp_all [noVars, sub]

theorem noVars_close (h : noVars t = true) : close t l = t := by
  rw [close_eq, noVars_sub h]

-- the local i of l, by the head of l
theorem get?_nil : Locals.nil.get? i = none := by
  cases i <;> rfl

theorem get?_zero : (Locals.cons t l k r).get? 0 = some (t, l, k) := rfl

theorem get?_succ : (Locals.cons t l k r).get? (i + 1) = r.get? i := rfl

-- labels and proofs in pairs: no variable, and Data
theorem closedData_ok (h : closedData t = true) : noVars t = true ∧ Data t := by
  induction t with
  | Lab => exact ⟨rfl, .lab⟩
  | Rfl => exact ⟨rfl, .rfl⟩
  | Tup q a b iha ihb =>
    simp only [closedData, Bool.and_eq_true] at h
    obtain ⟨ha, hb⟩ := h
    have hb' := ihb hb
    split at ha
    next hq =>
      have ha' := iha ha
      exact ⟨by simp [noVars, ha'.1, hb'.1], .tup (fun _ => ha'.2) hb'.2⟩
    next hq => exact ⟨by simp [noVars, ha, hb'.1], .tup (fun h => absurd h hq) hb'.2⟩
  | Var | Ref | Ann | Let | Typ | Min | All | Lam | App | Sig | Prj | Enu | Mat | Efq | Eql | Rwt =>
    simp [closedData] at h

-- the local i, when l has it
theorem get?_close (h : l.get? i = some (x, xl, k)) : subst l i = close x xl := by
  induction l generalizing i with
  | nil => rw [get?_nil] at h; cases h
  | cons t l' k' r _ ih =>
    cases i with
    | zero =>
      simp only [get?_zero, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact subst_zero
    | succ i => rw [subst_succ]; rw [get?_succ] at h; exact ih h

-- the local i knows what is true
theorem get?_ok {l : Locals} (hl : l.Ok bk) (h : l.get? i = some (x, xl, k)) :
    k.Ok bk (close x xl) ∧ xl.Ok bk := by
  induction l generalizing i with
  | nil => rw [get?_nil] at h; cases h
  | cons t l' k' r _ ih =>
    cases i with
    | zero =>
      simp only [get?_zero, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨hl.1, hl.2.1⟩
    | succ i => rw [get?_succ] at h; exact ih hl.2.2 h

-- the local v, or the variable beyond l
theorem localArg_eq : argOf (localArg q l v) = (q, subst l v) := by
  induction l generalizing v with
  | nil => rfl
  | cons t l k r _ ih =>
    cases v with
    | zero => simp only [localArg, argOf, subst_zero]
    | succ v => rw [subst_succ]; exact ih

-- the local v knows what is true
theorem localArg_ok (hl : l.Ok bk) : argOk bk (localArg q l v) := by
  induction l generalizing v with
  | nil => exact ⟨trivial, trivial⟩
  | cons t l k r _ ih =>
    cases v with
    | zero => exact ⟨hl.2.1, hl.1⟩
    | succ v => exact ih hl.2.2

-- a let's body, under its value and l
theorem close_cons : close f (.cons v vl k l) = inst (sub (Subst.up (subst l)) f) (close v vl) := by
  show sub (subst _) f = _
  simp only [inst, sub_sub]
  congr 1; funext i
  cases i with
  | zero => exact subst_zero
  | succ i =>
    rw [subst_succ]
    simp only [Function.comp, Subst.up, sub_ren]
    exact (sub_var _).symm

-- a call that waits for one more argument, under that argument and l
theorem close_shift :
    close (App q (ren Nat.succ f) (Var 0)) (.cons x xl k fl) = App q (close f fl) (close x xl) := by
  rw [close_app, close_var, subst_zero, close_eq, close_eq (l := fl), sub_ren]
  congr 2; funext i; exact subst_succ

-- resolve keeps the term
theorem resolve_close : close (resolve t l).1 (resolve t l).2 = close t l := by
  fun_induction resolve t l
  case case1 ih => rw [ih, close_var, subst_zero]
  case case2 ih => rw [ih, close_var, close_var, subst_succ]
  case case3 => rfl

-- resolve gives locals that know what is true
theorem resolve_ok (hl : l.Ok bk) : (resolve t l).2.Ok bk := by
  fun_induction resolve t l
  case case1 ih => exact ih hl.2.1
  case case2 ih => exact ih hl.2.2
  case case3 => exact hl

theorem resolve_ok' (hl : l.Ok bk) (h : resolve t l = (u, ul)) : ul.Ok bk := by
  have := resolve_ok (t := t) hl; rwa [h] at this

-- a variable that resolve gives is beyond its locals
theorem resolve_var (h : resolve t l = (Var i, ul)) : ul = .nil := by
  fun_induction resolve t l
  case case1 ih => exact ih h
  case case2 ih => exact ih h
  case case3 t l h1 h2 =>
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    cases l with
    | nil => rfl
    | cons =>
      cases i with
      | zero => exact (h1 _ _ _ _ rfl rfl).elim
      | succ i => exact (h2 _ _ _ _ _ rfl rfl).elim

-- the term, from what resolve gives
theorem resolve_eq (h : resolve t l = (u, ul)) : close t l = close u ul := by
  rw [← resolve_close, h]

-- dataAt is data of the term
theorem dataAt_eq : dataAt t l = data (close t l) := by
  fun_induction dataAt t l
  case case1 => simp only [close_eq, sub, data]
  case case2 => simp only [close_eq, sub, data]
  case case3 iha ihb => rw [iha, ihb, close_tup]; rfl
  case case4 ih => rw [ih, close_var, subst_zero]
  case case5 ih => rw [ih, close_var, close_var, subst_succ]
  case case6 t l h1 h2 h3 h4 h5 =>
    cases t
    case Var i =>
      cases l with
      | nil => rfl
      | cons =>
        cases i with
        | zero => exact (h4 _ _ _ _ rfl rfl).elim
        | succ i => exact (h5 _ _ _ _ _ rfl rfl).elim
    all_goals simp_all [close_eq, sub, data]

-- bindsAtL is bindsAt of the term
theorem bindsAtL_eq (hk : Know.Ok bk (close x l) k) : bindsAtL p q x l k = bindsAt p q (close x l) := by
  unfold bindsAtL bindsAt
  rw [dataAt_eq]
  cases k
  · simp [Know.isData]
  · simp [Know.isData]
  · simp only [Know.Ok] at hk; simp [Know.isData, data_iff.2 hk]

-- the term an unspine took apart
theorem spine_unspine (h : unspine t ys = (u, zs)) : spine t ys = spine u zs := by
  induction t generalizing ys with
  | App q f x ihf _ => exact ihf h
  | _ => simp only [unspine, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl

-- unspineL unspines the term under its locals
theorem unspineL_unspine : unspine (close t l) (xs.map argOf) =
    unspine (close (unspineL t l xs).1 (unspineL t l xs).2.1) ((unspineL t l xs).2.2.map argOf) := by
  fun_induction unspineL t l xs
  case case1 ih => rw [← ih, close_app]; rfl
  case case2 ih => rw [← ih, close_var, subst_zero]
  case case3 ih => rw [← ih, close_var, close_var, subst_succ]
  case case4 => rfl

-- the arguments of unspineL have locals that know what is true, and their
-- flags say whether they are live
theorem unspineL_ok (hl : l.Ok bk) (hx : ∀ a ∈ xs, a.l.Ok bk ∧ a.k = .ofLive a.q.live) :
    ∀ a ∈ (unspineL t l xs).2.2, a.l.Ok bk ∧ a.k = .ofLive a.q.live := by
  fun_induction unspineL t l xs
  case case1 ih =>
    refine ih hl fun a m => ?_
    rcases List.mem_cons.1 m with rfl | m
    · exact ⟨hl, rfl⟩
    · exact hx a m
  case case2 ih => exact ih hl.2.1 hx
  case case3 ih => exact ih hl.2.2 hx
  case case4 => exact hx

-- the live arguments of values are values
theorem values_mem (vs : Values bk xs) (m : (q, x) ∈ xs) (l : q.live = true) : Value bk x := by
  induction xs with
  | nil => cases m
  | cons y ys ih =>
    cases vs with
    | cons hx vs =>
      rcases List.mem_cons.1 m with e | m
      · cases e; exact hx l
      · exact ih vs m

-- a list whose live terms are values
theorem values_of (h : ∀ p ∈ xs, p.1.live = true → Value bk p.2) : Values bk xs := by
  induction xs with
  | nil => exact .nil
  | cons p xs ih =>
    exact .cons (h p List.mem_cons_self) (ih fun p' m => h p' (List.mem_cons_of_mem _ m))

-- the arguments that went into a call are values where they are live
theorem values_fed {rxs : List MArg} (h : ∀ a ∈ rxs, argOk bk a ∧ a.k.isValue = a.q.live) :
    Values bk (rxs.reverse.map argOf) := by
  refine values_of fun p m hl => ?_
  simp only [List.mem_map, List.mem_reverse] at m
  obtain ⟨a, m, rfl⟩ := m
  exact (h a m).1.2.value ((h a m).2.trans hl)

-- the call so far is a value: its case tree needs more arguments
theorem CallOk.value (h : CallOk bk k t tl rxs) : Value bk (spine (Ref k) (rxs.reverse.map argOf)) := by
  obtain ⟨ht, -, hrx, d, hd, hw⟩ := h
  have w := hw []
  rw [List.append_nil, walk_need ht] at w
  exact .call hd (values_fed hrx) (walk_iff.1 w)

-- the function of a spine steps
theorem Eval.spine_f (h : Eval bk f f') : Eval bk (spine f ys) (spine f' ys) := by
  induction ys generalizing f f' with
  | nil => exact h
  | cons y ys ih => exact ih (.app_f h)

-- the function of a spine takes its steps
theorem Steps.spine_f (h : Steps bk n f f') : Steps bk n (spine f ys) (spine f' ys) := by
  induction h with
  | refl => exact .refl
  | step e _ ih => exact .step (Eval.spine_f e) ih

-- a step in the hole is a step of the whole term
theorem Eval.plugs (hs : ∀ f ∈ st, f.Ok bk) (h : Eval bk t u) : Eval bk (plugs st t) (plugs st u) :=
  by
  induction st generalizing t u with
  | nil => exact h
  | cons f st ih =>
    have hf := hs f (by simp)
    apply ih (fun g hg => hs g (by simp [hg]))
    cases f <;> simp only [Frame.Ok] at hf <;> simp only [Frame.plug]
    case appArg => exact .app_f h
    case appFun => exact .app_x hf.2.1 hf.1 h
    case letIn => exact .lett hf.1 h
    case tupB => exact .tup_a hf.1 h
    case tupA => exact .tup_b hf.1 h
    case rwt => exact .rwt h
    case minB => exact .min_a h
    case call => exact Eval.spine_f (.app_x hf.2.1.value hf.1 h)
    case minA => exact .min_b hf h

-- steps in the hole are steps of the whole term
theorem Steps.plugs (hs : ∀ f ∈ st, f.Ok bk) (h : Steps bk n t u) :
    Steps bk n (plugs st t) (plugs st u) := by
  induction h with
  | refl => exact .refl
  | step e _ ih => exact .step (Eval.plugs hs e) ih

-- the frames of a spine's arguments
theorem plugs_argFrames : plugs (argFrames ys) t = spine t (ys.map argOf) := by
  induction ys generalizing t with
  | nil => rfl
  | cons y ys ih =>
    obtain ⟨q, x, l, k⟩ := y
    exact ih

-- what a move from a state of term T gives: no step keeps T, a step is one
-- step of Eval, a jump its steps, and the state of a stop or a jump has T
def Move.Ok (bk : Book) (T : Term) : Move → Prop
  | .admin s' => s'.Ok bk ∧ s'.term = T
  | .step s' => s'.Ok bk ∧ Eval bk T s'.term
  | .jump n s' f => s'.Ok bk ∧ Steps bk n T s'.term ∧ f.term = T
  | .stop f => f.term = T

-- a spine under locals
theorem close_spine : close (spine t ys) l = spine (close t l) (ys.map (argAt l)) := by
  induction ys generalizing t with
  | nil => rfl
  | cons y ys ih =>
    obtain ⟨q, y⟩ := y
    simp only [spine, List.map_cons, argAt]
    rw [ih, close_app]

-- the frames of a spine's arguments under l
theorem plugs_appArgs : plugs (appArgs l ys st) t = plugs st (spine t (ys.map (argAt l))) := by
  induction ys generalizing t with
  | nil => rfl
  | cons y ys ih =>
    obtain ⟨q, y⟩ := y
    exact ih

theorem appArgs_ok (hl : l.Ok bk) (hst : ∀ f ∈ st, f.Ok bk) : ∀ f ∈ appArgs l ys st, f.Ok bk := by
  induction ys with
  | nil => exact hst
  | cons y ys ih =>
    obtain ⟨q, y⟩ := y
    intro f m
    rcases List.mem_cons.1 m with rfl | m
    · exact ⟨hl, trivial⟩
    · exact ih f m

-- the call so far, with one more argument
theorem spine_fed : spine (Ref k) ((a :: rxs).reverse.map argOf) =
    App a.q (spine (Ref k) (rxs.reverse.map argOf)) (close a.t a.l) := by
  rw [List.reverse_cons, List.map_append]
  exact spine_snoc

-- the term of papOf
theorem papOf_close : close (papOf k rxs).1 (papOf k rxs).2 = spine (Ref k) (rxs.reverse.map argOf) := by
  induction rxs with
  | nil => rfl
  | cons a rxs ih =>
    obtain ⟨q, x, xl, b⟩ := a
    rw [spine_fed, ← ih]
    exact close_shift

theorem papOf_ok (h : ∀ a ∈ rxs, argOk bk a ∧ a.k.isValue = a.q.live) : (papOf k rxs).2.Ok bk := by
  induction rxs with
  | nil => trivial
  | cons a rxs ih =>
    obtain ⟨q, x, xl, b⟩ := a
    have ha := (h _ List.mem_cons_self).1
    exact ⟨ha.2, ha.1, ih fun a' m => h a' (List.mem_cons_of_mem _ m)⟩

-- a node of a case tree is a value, under any locals
theorem takes_value (h : takes t = true) : Value bk (close t l) := by
  cases t <;> simp [takes] at h <;> simp only [close_eq, sub] <;> constructor

-- a value without a step: the term it stands for is the term
theorem imm_ok (hl : l.Ok bk) (h : imm t l = some (v, vl, d)) :
    close v vl = close t l ∧ Value bk (close v vl) ∧ vl.Ok bk ∧ (d = true → Data (close v vl)) := by
  cases t with
  | Var i =>
    simp only [imm] at h
    split at h
    next x xl k hx =>
      split at h
      next hv =>
        cases h
        have ho := get?_ok hl hx
        refine ⟨by rw [close_var, get?_close hx], ho.1.value hv, ho.2, fun hd => ?_⟩
        cases k <;> simp [Know.isData] at hd
        exact ho.1
      next => cases h
    next => cases h
  | Lam | Prj | Mat => simp only [imm] at h; cases h; exact ⟨rfl, takes_value rfl, hl, nofun⟩
  | Typ | All | Sig | Eql =>
    simp only [imm] at h; cases h
    exact ⟨rfl, by simp only [close_eq, sub]; constructor, hl, nofun⟩
  | Lab | Rfl =>
    simp only [imm] at h; cases h
    refine ⟨by simp only [close_eq, sub], by simp only [close_eq, sub]; constructor, trivial, ?_⟩
    intro; simp only [close_eq, sub]; constructor
  | Efq | Enu =>
    simp only [imm] at h; cases h
    refine ⟨by simp only [close_eq, sub], by simp only [close_eq, sub]; constructor, trivial, nofun⟩
  | Tup q a b =>
    simp only [imm] at h
    split at h
    next hc =>
      cases h
      have hc' := closedData_ok hc
      exact ⟨(noVars_close hc'.1).symm, data_value hc'.2, trivial, fun _ => hc'.2⟩
    next => cases h
  | Ref | Ann | Let | Min | App | Rwt => simp [imm] at h

-- the first part of a pair, when it needs no step: a dead one, or a value
theorem imm_part {q : Quan} {a a' : Term} {l al : Locals} (hl : l.Ok bk)
    (h : (if q.live then imm a l else some (a, l, true)) = some (a', al, da)) :
    close a' al = close a l ∧ (q.live = true → Value bk (close a' al)) ∧ al.Ok bk ∧
      (q.live = true → da = true → Data (close a' al)) := by
  split at h
  next hq => obtain ⟨e, v, o, d⟩ := imm_ok hl h; exact ⟨e, fun _ => v, o, fun _ => d⟩
  next hq => cases h; exact ⟨rfl, fun h => absurd h hq, hl, fun h => absurd h hq⟩

-- an argument that is ready: the term it stands for, and what it knows is true
theorem ready_ok (hl : l.Ok bk) (h : ready q y l = some a) :
    argOf a = (q, close y l) ∧ argOk bk a ∧ a.k.isValue = a.q.live := by
  unfold ready at h
  split at h
  next hq =>
    split at h
    next x xl d hx =>
      cases h
      obtain ⟨e, v, o, hd⟩ := imm_ok hl hx
      refine ⟨by simp [argOf, e], ⟨o, ?_⟩, by cases d <;> simp [Know.ofData, Know.isValue, hq]⟩
      cases d
      · exact v
      · exact hd rfl
    next => cases h
  next hq => cases h; exact ⟨rfl, ⟨hl, trivial⟩, by simp only [Bool.not_eq_true] at hq; simp [hq, Know.isValue]⟩

-- an argument that is not ready is live
theorem ready_live (h : ready q y l = none) : q.live = true := by
  unfold ready at h
  split at h
  next hq => exact hq
  next => cases h

-- what is known of a pair is known of its parts (of the first, when it is live)
theorem Know.Ok.tup (h : Know.Ok bk (Tup r a b) k) :
    Know.Ok bk a (if r.live then k else .none) ∧ Know.Ok bk b k := by
  cases k
  · split <;> exact ⟨trivial, trivial⟩
  · have ⟨va, vb⟩ := value_tup h
    split
    · exact ⟨va ‹_›, vb⟩
    · exact ⟨trivial, vb⟩
  · cases h with
    | tup ha hb =>
      split
      · exact ⟨ha ‹_›, hb⟩
      · exact ⟨trivial, hb⟩

end Machine
