import Interpreter.Machine.Move

-- Machine.Loop
-- ============
--
-- A run of the machine takes steps of Eval, and reaches each value that Eval
-- reaches, after as many steps.

open Quan Term

namespace Machine

theorem init_ok : (init t).Ok bk :=
  ⟨trivial, fun _ h => by simp [init] at h⟩

theorem init_term : (init t).term = t := by
  simp [init, State.term, plugs, Focus.term, close]

-- the steps to a value go through each term on the way, and there are no more
-- of them after it
theorem steps_prefix (h : Steps bk k t u) (h' : Steps bk n t v) (hv : Value bk v) :
    k ≤ n ∧ Steps bk (n - k) u v := by
  induction h generalizing n with
  | refl => simpa using h'
  | step e _ ih =>
    cases h' with
    | refl => exact (eval_value e hv).elim
    | step e' s =>
      cases eval_det e e'
      obtain ⟨hk, hs⟩ := ih s
      exact ⟨by omega, by simpa [Nat.add_sub_add_right] using hs⟩

-- a run takes steps of Eval, no more than its fuel
theorem run_sound (htb : tb = Ops.prepare bk) (hs : s.Ok bk) :
    run bk tb g fuel s m = (u, n) → ∃ k, n = m + k ∧ Steps bk k s.term u ∧ k ≤ fuel := by
  induction g generalizing fuel s m with
  | zero => intro h; exact stepwise_sound h
  | succ g ih =>
    intro h
    cases fuel with
    | zero =>
      simp only [run, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨0, rfl, .refl, Nat.le_refl _⟩
    | succ fuel =>
      have hm := move_ok htb hs
      simp only [run] at h
      split at h <;> rename_i hmv <;> rw [hmv] at hm
      · obtain ⟨hs', he⟩ := hm
        rw [← he]; exact ih hs' h
      · obtain ⟨hs', he⟩ := hm
        obtain ⟨k, rfl, hk, hle⟩ := ih hs' h
        exact ⟨k + 1, by omega, .step he hk, by omega⟩
      · obtain ⟨hs', he, hf⟩ := hm
        split at h
        · obtain ⟨k, rfl, hk, hle⟩ := ih hs' h
          exact ⟨_ + k, by omega, he.trans hk, by omega⟩
        · simp only [Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨0, rfl, hf ▸ .refl, Nat.zero_le _⟩
      · rw [hm] at h
        exact stepwise_sound h

-- a run reaches each value that Eval reaches within its fuel, after as many steps
theorem run_complete (htb : tb = Ops.prepare bk) (hs : s.Ok bk) :
    Steps bk n s.term v → Value bk v → n ≤ fuel → run bk tb g fuel s m = (v, m + n) := by
  intro hst hv hn
  induction g generalizing fuel s m n with
  | zero => exact stepwise_complete hst hv hn
  | succ g ih =>
    cases fuel with
    | zero =>
      obtain rfl : n = 0 := by omega
      cases hst
      simp [run]
    | succ fuel =>
      have hm := move_ok htb hs
      simp only [run]
      split <;> rename_i hmv <;> rw [hmv] at hm
      · obtain ⟨hs', he⟩ := hm
        exact ih hs' (he ▸ hst) hn
      · obtain ⟨hs', he⟩ := hm
        cases hst with
        | refl => exact (eval_value he hv).elim
        | step h1 hr =>
          rename_i n' w
          have hw := eval_det h1 he
          subst hw
          rw [ih hs' hr (by omega)]
          congr 1; omega
      · obtain ⟨hs', he, -⟩ := hm
        obtain ⟨hj, hr⟩ := steps_prefix he hst hv
        rw [if_pos (by omega), ih hs' hr (by omega)]
        congr 1; omega
      · rw [hm]
        exact stepwise_complete hst hv hn

end Machine
