import Shared.Code
import Eval.Generated.Eval

-- EvalSteps.Bool
-- ==============
--
-- The defs of the Bend version of Eval on Bools, quantities and the forms of terms give
-- what their Lean counterparts give.

open Quan Term

namespace EvalVersion

-- a call on values steps to the leaf of its def's case tree, then runs on
private theorem call (hk : Book.get B k = some d) (vs : Values B xs)
    (w : walk B d.v [] xs = some (some u)) (r : Runs B u v) : Runs B (spine (Ref k) xs) v :=
  .step (Eval.walk hk vs w) r

theorem not_version (h : Contains B evalVersion) :
    Runs B (spine (Ref "Bool.not") [(Q1, Form.bool a)]) (Form.bool !a) := by
  have hk : Book.get B "Bool.not" = some «evalVersion.Bool.not» :=
    h «evalVersion.Bool.not» (by simp [evalVersion])
  refine call hk (.cons (fun _ => value_bool) .nil) ?_ (.refl value_bool)
  cases a <;> simp [«evalVersion.Bool.not», walk, Form.bool, ctor, Quan.live, takes, Quan.fld,
    Term.sub, spine]

theorem and_version (h : Contains B evalVersion) :
    Runs B (spine (Ref "Bool.and") [(Q1, Form.bool a), (Q1, Form.bool b)]) (Form.bool (a && b)) :=
  by
  have hk : Book.get B "Bool.and" = some «evalVersion.Bool.and» :=
    h «evalVersion.Bool.and» (by simp [evalVersion])
  refine call hk (.cons (fun _ => value_bool) (.cons (fun _ => value_bool) .nil)) ?_
    (.refl value_bool)
  cases a <;> simp [«evalVersion.Bool.and», walk, Form.bool, ctor, bindsAt, Quan.live, takes,
    Quan.fld, Term.sub, Env.sub, spine, data]

theorem or_version (h : Contains B evalVersion) :
    Runs B (spine (Ref "Bool.or") [(Q1, Form.bool a), (Q1, Form.bool b)]) (Form.bool (a || b)) :=
  by
  have hk : Book.get B "Bool.or" = some «evalVersion.Bool.or» :=
    h «evalVersion.Bool.or» (by simp [evalVersion])
  refine call hk (.cons (fun _ => value_bool) (.cons (fun _ => value_bool) .nil)) ?_
    (.refl value_bool)
  cases a <;> simp [«evalVersion.Bool.or», walk, Form.bool, ctor, bindsAt, Quan.live, takes,
    Quan.fld, Term.sub, Env.sub, spine, data]

theorem live_version (h : Contains B evalVersion) :
    Runs B (spine (Ref "Quan.live") [(Q1, Form.quan q)]) (Form.bool q.live) := by
  have hk : Book.get B "Quan.live" = some «evalVersion.Quan.live» :=
    h «evalVersion.Quan.live» (by simp [evalVersion])
  refine call hk (.cons (fun _ => value_quan) .nil) ?_ (.refl value_bool)
  cases q <;> simp [«evalVersion.Quan.live», walk, Form.bool, Form.quan, ctor, Quan.live, takes,
    Quan.fld, Term.sub, spine]

theorem lives_as_version (h : Contains B evalVersion) :
    Runs B (spine (Ref "Quan.lives_as") [(Q1, Form.quan p), (Q1, Form.quan q)])
      (Form.bool (p.live == q.live)) := by
  have hk : Book.get B "Quan.lives_as" = some «evalVersion.Quan.lives_as» :=
    h «evalVersion.Quan.lives_as» (by simp [evalVersion])
  refine call hk (.cons (fun _ => value_quan) (.cons (fun _ => value_quan) .nil)) ?_
    (.refl value_bool)
  cases p <;> cases q <;> simp [«evalVersion.Quan.lives_as», walk, Form.bool, Form.quan, ctor,
    bindsAt, Quan.live, takes, Quan.fld, Term.sub, spine, data]

theorem fld_version (h : Contains B evalVersion) :
    Runs B (spine (Ref "Quan.fld") [(Q1, Form.quan r), (Q1, Form.quan q)])
      (Form.quan (Quan.fld r q)) := by
  have hk : Book.get B "Quan.fld" = some «evalVersion.Quan.fld» :=
    h «evalVersion.Quan.fld» (by simp [evalVersion])
  refine call hk (.cons (fun _ => value_quan) (.cons (fun _ => value_quan) .nil)) ?_
    (.refl value_quan)
  cases r <;> cases q <;> simp [«evalVersion.Quan.fld», walk, Form.quan, ctor,
    bindsAt, Quan.live, takes, Quan.fld, Term.sub, Env.sub, spine, data]

-- an argument runs first, after a function that is a value
private theorem runs_arg (vf : Value B f) (rx : Runs B x x') (r : Runs B (App Q1 f x') v) :
    Runs B (App Q1 f x) v :=
  have ⟨_, s, _⟩ := rx; .steps (Steps.app_x vf rfl s) r

-- the function of an application runs first
private theorem runs_fun (rf : Runs B f f') (r : Runs B (App q f' x) v) : Runs B (App q f x) v :=
  have ⟨_, s, _⟩ := rf; .steps (Steps.app_f s) r

-- Bool.not runs on an argument that runs to a Bool
private theorem not_runs (h : Contains B evalVersion) (rx : Runs B x (Form.bool a)) :
    Runs B (App Q1 (Ref "Bool.not") x) (Form.bool !a) :=
  runs_arg (.call (xs := []) (h «evalVersion.Bool.not» (by simp [evalVersion])) .nil
    (walk_iff.1 (by simp [walk, «evalVersion.Bool.not», takes]))) rx (not_version h)

-- Quan.live runs on an argument that runs to a quantity
private theorem live_runs (h : Contains B evalVersion) (rx : Runs B x (Form.quan q)) :
    Runs B (App Q1 (Ref "Quan.live") x) (Form.bool q.live) :=
  runs_arg (.call (xs := []) (h «evalVersion.Quan.live» (by simp [evalVersion])) .nil
    (walk_iff.1 (by simp [walk, «evalVersion.Quan.live», takes]))) rx (live_version h)

-- Bool.and runs on arguments that run to Bools
private theorem and_runs (h : Contains B evalVersion) (rx : Runs B x (Form.bool a))
    (ry : Runs B y (Form.bool b)) :
    Runs B (App Q1 (App Q1 (Ref "Bool.and") x) y) (Form.bool (a && b)) := by
  have hk : Book.get B "Bool.and" = some «evalVersion.Bool.and» :=
    h «evalVersion.Bool.and» (by simp [evalVersion])
  have v1 : Value B (App Q1 (Ref "Bool.and") (Form.bool a)) :=
    .call (xs := [(Q1, _)]) hk (.cons (fun _ => value_bool) .nil) (walk_iff.1 (by
      cases a <;> simp [walk, «evalVersion.Bool.and», takes, Form.bool, ctor, Quan.live, Quan.fld]))
  exact runs_fun (runs_arg (.call (xs := []) hk .nil
    (walk_iff.1 (by simp [walk, «evalVersion.Bool.and», takes]))) rx (.refl v1))
    (runs_arg v1 ry (and_version h))

-- Bool.or runs on arguments that run to Bools
private theorem or_runs (h : Contains B evalVersion) (rx : Runs B x (Form.bool a))
    (ry : Runs B y (Form.bool b)) :
    Runs B (App Q1 (App Q1 (Ref "Bool.or") x) y) (Form.bool (a || b)) := by
  have hk : Book.get B "Bool.or" = some «evalVersion.Bool.or» :=
    h «evalVersion.Bool.or» (by simp [evalVersion])
  have v1 : Value B (App Q1 (Ref "Bool.or") (Form.bool a)) :=
    .call (xs := [(Q1, _)]) hk (.cons (fun _ => value_bool) .nil) (walk_iff.1 (by
      cases a <;> simp [walk, «evalVersion.Bool.or», takes, Form.bool, ctor, Quan.live, Quan.fld]))
  exact runs_fun (runs_arg (.call (xs := []) hk .nil
    (walk_iff.1 (by simp [walk, «evalVersion.Bool.or», takes]))) rx (.refl v1))
    (runs_arg v1 ry (or_version h))

theorem is_data_version (h : Contains B evalVersion) :
    Runs B (spine (Ref "Term.is_data") [(Q1, Form.term t)]) (Form.bool (data t)) := by
  have hk : Book.get B "Term.is_data" = some «evalVersion.Term.is_data» :=
    h «evalVersion.Term.is_data» (by simp [evalVersion])
  induction t
  case Tup q a b iha ihb =>
    refine call hk (.cons (fun _ => value_term) .nil) ?_ (and_runs h (or_runs h
      (not_runs h (live_runs h (.refl value_quan))) iha) ihb)
    simp [«evalVersion.Term.is_data», walk, Form.term, ctor, Quan.live, takes, Quan.fld,
      Term.sub, Env.sub, spine, bindsAt, data_iff.2 data_quan, data_iff.2 data_term]
  all_goals
    refine call hk (.cons (fun _ => value_term) .nil) ?_ (.refl value_bool)
    simp [«evalVersion.Term.is_data», walk, Form.term, Form.bool, ctor, Quan.live, takes, Quan.fld,
      Term.sub, spine, bindsAt, data]

theorem fits_version (h : Contains B evalVersion) :
    Runs B (spine (Ref "Quan.fits") [(Q1, Form.quan q), (Q1, Form.term v)])
      (Form.bool (q != Q2 || data v)) := by
  have hk : Book.get B "Quan.fits" = some «evalVersion.Quan.fits» :=
    h «evalVersion.Quan.fits» (by simp [evalVersion])
  have vs : Values B [(Q1, Form.quan q), (Q1, Form.term v)] :=
    .cons (fun _ => value_quan) (.cons (fun _ => value_term) .nil)
  cases q
  case Q2 =>
    refine call hk vs (u := App Q1 (Ref "Term.is_data") (Form.term v)) ?_ ?_
    · simp [«evalVersion.Quan.fits», walk, Form.quan, ctor, Quan.live, takes, Quan.fld,
        Term.sub, Env.sub, spine, bindsAt]
    · simpa [spine] using is_data_version h
  all_goals
    refine call hk vs ?_ (.refl value_bool)
    simp [«evalVersion.Quan.fits», walk, Form.quan, Form.bool, ctor, Quan.live, takes, Quan.fld,
      Term.sub, spine, bindsAt, data]

theorem binds_version (h : Contains B evalVersion) :
    Runs B (spine (Ref "Quan.binds") [(Q2, Form.quan p), (Q1, Form.quan q), (Q1, Form.term x)])
      (Form.bool (bindsAt p q x)) := by
  have hk : Book.get B "Quan.binds" = some «evalVersion.Quan.binds» :=
    h «evalVersion.Quan.binds» (by simp [evalVersion])
  refine call hk (.cons (fun _ => value_quan) (.cons (fun _ => value_quan)
    (.cons (fun _ => value_term) .nil))) ?_ (and_runs h (lives_as_version h) (fits_version h))
  simp [«evalVersion.Quan.binds», walk, Quan.live, takes, Term.sub, Env.sub, spine, bindsAt,
    data_iff.2 data_quan]

theorem is_former_version (h : Contains B evalVersion) :
    Runs B (spine (Ref "Term.is_former") [(Q1, Form.term t)]) (Form.bool (t.former != 0)) := by
  have hk : Book.get B "Term.is_former" = some «evalVersion.Term.is_former» :=
    h «evalVersion.Term.is_former» (by simp [evalVersion])
  refine call hk (.cons (fun _ => value_term) .nil) ?_ (.refl value_bool)
  cases t <;> simp [«evalVersion.Term.is_former», walk, Form.term, Form.bool, ctor, Quan.live,
    takes, Quan.fld, Term.sub, spine, bindsAt, data, former]

theorem takes_version (h : Contains B evalVersion) :
    Runs B (spine (Ref "Term.takes") [(Q1, Form.term t)]) (Form.bool (Term.takes t)) := by
  have hk : Book.get B "Term.takes" = some «evalVersion.Term.takes» :=
    h «evalVersion.Term.takes» (by simp [evalVersion])
  refine call hk (.cons (fun _ => value_term) .nil) ?_ (.refl value_bool)
  cases t <;> simp [«evalVersion.Term.takes», walk, Form.term, Form.bool, ctor, Quan.live,
    takes, Quan.fld, Term.sub, spine, bindsAt, data]

theorem waits_version (h : Contains B evalVersion) :
    Runs B (spine (Ref "Eval.waits") [(Q1, Form.maybe (Form.maybe Form.term) r)])
      (Form.bool (r == some none)) := by
  have hk : Book.get B "Eval.waits" = some «evalVersion.Eval.waits» :=
    h «evalVersion.Eval.waits» (by simp [evalVersion])
  refine call hk (.cons (fun _ => value_maybe (fun _ => value_maybe (fun _ => value_term))) .nil)
    ?_ (.refl value_bool)
  rcases r with _ | _ | t <;> simp [«evalVersion.Eval.waits», walk, Form.maybe, Form.some,
    Form.bool, ctor, Quan.live, takes, Quan.fld, Term.sub, spine, bindsAt, data]

end EvalVersion
