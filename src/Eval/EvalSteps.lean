import Eval.Step

-- EvalSteps
-- =========
--
-- AGENTS.md 3.6.3: Eval.steps, the Bend version of Eval
-- (src/Eval/impl.bend), gives what the kernel's Eval gives,
-- after the same number of steps, in both directions. The proof goes through
-- step (src/Shared/Interp.lean), which the version follows case for case
-- (src/Eval/).

open Quan Term

-- a maybe of terms that is some term u was some u
private theorem maybe_term_some {o : Option Term} :
    Form.maybe Form.term o = Form.some (Form.term u) → o = some u := by
  cases o with
  | none => intro h; have := (ctor_inj h).1; simp at this
  | some x =>
    intro h; simp only [Form.maybe, Form.some] at h
    have := (ctor_inj h).2; simp only [List.cons.injEq, and_true] at this
    rw [term_inj this]

-- n steps of step are n steps of Eval
theorem iterate_iff : EvalVersion.iterate bk n t = some u ↔ Steps bk n t u := by
  induction n generalizing t with
  | zero =>
    simp only [EvalVersion.iterate, Option.some.injEq]
    exact ⟨fun h => h ▸ .refl, fun h => by cases h; rfl⟩
  | succ n ih =>
    simp only [EvalVersion.iterate, Option.bind_eq_some_iff]
    constructor
    · rintro ⟨v, hv, hs⟩; exact .step (step_iff.1 hv) (ih.1 hs)
    · intro h; cases h with
      | step e s => exact ⟨_, step_iff.2 e, ih.2 s⟩

-- in a book that holds the Bend version of Eval, the version says that t reaches u after
-- n steps exactly when the kernel's Eval says so
theorem version_steps : Contains B evalVersion →
    (Runs B (App Q1 (App Q1 (App Q1 (Ref "Eval.steps") (Form.nat n)) (Form.defs bk.defs)) (Form.term t))
      (Form.some (Form.term u)) ↔ Steps bk n t u) := by
  intro h
  rw [← iterate_iff]
  constructor
  · rintro ⟨m, s, v⟩
    have ⟨m', s', v'⟩ := EvalVersion.steps_version (n := n) (bk := bk) (t := t) h
    exact maybe_term_some (steps_det s' v' s v).2
  · intro hi
    have := EvalVersion.steps_version (n := n) (bk := bk) (t := t) h
    rwa [hi] at this
