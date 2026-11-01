import Interpreter.Machine.Basic

-- Machine.Walk
-- ============
--
-- walkOpen walks as walk (src/Shared/Interp.lean) does, what it knows is true,
-- and a walk that waits goes on from where it waits.

open Quan Term

namespace Machine

-- the outcome of walk where a walk ends
def Reach.out : Reach → Option (Option Term)
  | .leaf t l ys => some (some (spine (close t l) (ys.map argOf)))
  | .need _ _ => some none
  | .fail => none

-- walkOpen gives walk's outcome, with its leaf left open
theorem walkOpen_walk : (walkOpen bk t l xs).out = _root_.walk bk t l.terms (xs.map argOf) := by
  fun_induction walkOpen bk t l xs
  case case1 hb ih =>
    rw [bindsAtL_eq] at hb
    rw [ih, terms_cons]; simp [Reach.out, argOf, _root_.walk, hb]
  case case2 hb =>
    rw [bindsAtL_eq] at hb
    simp [Reach.out, argOf, _root_.walk, hb]
  case case3 e hq ih =>
    rw [ih]; simp [Reach.out, argOf, resolve_eq e, close_tup, _root_.walk, hq]
  case case4 e hq =>
    simp [Reach.out, argOf, resolve_eq e, close_tup, _root_.walk, hq]
  case case5 h l q x xl k xs hr =>
    rcases e : resolve x xl with ⟨u, ul⟩
    have hc := resolve_eq e
    cases u
    case Tup => exact (hr _ _ _ _ e).elim
    case Var i => obtain rfl := resolve_var e; simp [Reach.out, argOf, hc, close_nil, _root_.walk, takes]
    all_goals simp [Reach.out, argOf, hc, close_eq (l := ul), sub, _root_.walk, takes]
  case case6 e hq ih =>
    rw [ih]; simp [Reach.out, argOf, resolve_eq e, close_lab, _root_.walk, hq]
  case case7 e hq hij ih =>
    rw [ih]; simp [argOf, resolve_eq e, close_lab, _root_.walk, hq, hij]
  case case8 e hq =>
    simp [Reach.out, argOf, resolve_eq e, close_lab, _root_.walk, hq]
  case case10 ht ih =>
    rw [ih]; simp [localArg_eq, _root_.walk, ht, subst]
  case case11 ht =>
    simp [Reach.out, _root_.walk, ht, close_eq, subst]
  case case9 j h m l q x xl k xs hr =>
    rcases e : resolve x xl with ⟨u, ul⟩
    have hc := resolve_eq e
    cases u
    case Lab => exact (hr _ _ e).elim
    case Var i => obtain rfl := resolve_var e; simp [Reach.out, argOf, hc, close_nil, _root_.walk, takes]
    all_goals simp [Reach.out, argOf, hc, close_eq (l := ul), sub, _root_.walk, takes]
  case case12 t l xs h1 h2 h3 h4 ht hx =>
    obtain rfl := List.isEmpty_iff.1 hx
    cases t <;> simp_all [Reach.out, _root_.walk, takes]
  case case13 t l xs h1 h2 h3 h4 ht hx =>
    rcases xs with _ | ⟨⟨q, x, xl, k⟩, xs⟩
    · simp at hx
    cases t
    all_goals first
      | exact (h1 _ _ _ _ _ _ _ rfl rfl).elim
      | exact (h2 _ _ _ _ _ _ rfl rfl).elim
      | exact (h3 _ _ _ _ _ _ _ _ rfl rfl).elim
      | simp_all [Reach.out, _root_.walk, takes]
  case case14 t l xs h1 h2 h3 h4 ht =>
    rcases xs with _ | ⟨⟨q, x, xl, k⟩, xs⟩
    · cases t <;> simp_all [Reach.out, _root_.walk, takes, close_eq, subst]
    cases t
    case App q' f y => cases y <;> simp_all [Reach.out, _root_.walk, takes, close_eq, subst]
    all_goals simp_all [Reach.out, _root_.walk, takes, close_eq, subst]

-- what is true where a walk ends: the leaf's locals and the arguments left
-- know it, and a walk waits at a node that takes an argument
def Reach.Ok (bk : Book) : Reach → Prop
  | .leaf _ l ys => l.Ok bk ∧ ∀ a ∈ ys, argOk bk a
  | .need t l => l.Ok bk ∧ takes t = true
  | .fail => True

theorem walkOpen_ok (hl : l.Ok bk) (hx : ∀ a ∈ xs, argOk bk a) : (walkOpen bk t l xs).Ok bk := by
  fun_induction walkOpen bk t l xs
  case case1 p f l q x xl k xs hb ih =>
    have ha := hx _ List.mem_cons_self
    exact ih ⟨ha.2, ha.1, hl⟩ (fun a m => hx a (.tail _ m))
  case case3 h' l q x xl k xs r a b al e hq ih =>
    have ha := hx _ List.mem_cons_self
    have hal := resolve_ok' ha.1 e
    have hv : k = true → Value bk (Tup r (close a al) (close b al)) := fun hk => by
      rw [← close_tup, ← resolve_eq e]; exact ha.2 hk
    refine ih hl ?_
    intro c m
    rcases List.mem_cons.1 m with rfl | m
    · refine ⟨hal, fun hk => ?_⟩
      simp only [Bool.and_eq_true] at hk
      exact (value_tup (hv hk.1)).1 hk.2
    rcases List.mem_cons.1 m with rfl | m
    · exact ⟨hal, fun hk => (value_tup (hv hk)).2⟩
    · exact hx c (.tail _ m)
  case case6 ih => exact ih hl (fun a m => hx a (.tail _ m))
  case case7 ih =>
    refine ih hl ?_
    intro a m
    rcases List.mem_cons.1 m with rfl | m
    · exact ⟨trivial, fun _ => .lab⟩
    · exact hx a (.tail _ m)
  case case10 ih =>
    refine ih hl ?_
    intro a m
    rcases List.mem_cons.1 m with rfl | m
    · exact localArg_ok hl
    · exact hx a m
  case case12 ht _ => exact ⟨hl, ht⟩
  case case11 => exact ⟨hl, hx⟩
  case case14 => exact ⟨hl, hx⟩
  all_goals trivial

-- a walk that waits goes on from where it waits, with more arguments
theorem walkOpen_append (h : walkOpen bk t l xs = .need u ul) :
    walkOpen bk t l (xs ++ ys) = walkOpen bk u ul ys := by
  fun_induction walkOpen bk t l xs
  case case1 hb ih => simp only [List.cons_append, walkOpen, hb, ite_true]; exact ih h
  case case3 e hq ih => simp only [List.cons_append, walkOpen, e, hq, ite_true]; exact ih h
  case case6 e hq ih => simp only [List.cons_append, walkOpen, e, hq, ite_true]; exact ih h
  case case7 e hq hij ih => simp only [List.cons_append, walkOpen, e, hq, hij, ite_true, ite_false]; exact ih h
  case case10 ht ih => simp only [walkOpen, ht, ite_true]; exact ih h
  case case12 t l xs _ _ _ _ _ hx =>
    obtain rfl := List.isEmpty_iff.1 hx
    cases h; rfl
  all_goals cases h

-- a walk that waits goes on from where it waits, with any more arguments
theorem walk_resume (h : walkOpen bk t l xs = .need u ul) (zs : List Arg) :
    walk bk t l.terms (xs.map argOf ++ zs) = walk bk u ul.terms zs := by
  have e : zs = (zs.map fun (q, x) => (⟨q, x, Locals.nil, false⟩ : MArg)).map argOf := by
    induction zs with
    | nil => rfl
    | cons z zs ih => obtain ⟨q, x⟩ := z; simp only [List.map_cons, argOf, close_nil]; rw [← ih]
  rw [e, ← List.map_append, ← walkOpen_walk, ← walkOpen_walk, walkOpen_append h]

-- the call goes on, with the argument a in its walk
theorem CallOk.feed (hc : CallOk bk k t tl rxs) (ha : argOk bk a ∧ a.k = a.q.live)
    (hw : walkOpen bk t tl [a] = .need u ul) : CallOk bk k u ul (a :: rxs) := by
  obtain ⟨-, htl, hrx, d, hd, hwk⟩ := hc
  have ho := walkOpen_ok (bk := bk) (t := t) (l := tl) (xs := [a]) htl (by simpa using ha.1)
  rw [hw] at ho
  refine ⟨ho.2, ho.1, ?_, d, hd, fun zs => ?_⟩
  · intro a' m
    rcases List.mem_cons.1 m with rfl | m
    · exact ha
    · exact hrx a' m
  · rw [List.reverse_cons, List.map_append, List.append_assoc, hwk]
    exact walk_resume hw zs

end Machine
