import Joining.OrLaw
import Joining.GivesRun
import Joining.NeedRun

-- Compiler
-- ========
--
-- AGENTS.md 3.6.6: when the interpreter (Interpreter/Program.lean) runs our own
-- compiler, the main of main.bend, on the bytes that the Lean writer
-- writes for a book bk, the bytes w that it gives follow the laws of 3.6.1
-- (Compiler/spec.bend), in each book B that --verdict accepts for main.bend
-- (Book.check B = .ok ()) and that holds main.bend's defs (Trusted B):
-- the Bend version of WASM, run on w on any engine (Wasm.Engine), gives only
-- what bk gives (no wrong result), and when bk gives something, it gives it
-- or runs out of memory (no other failure), and with the memory of 3.9.1.4,
-- on an engine that grants each grow and takes w, it gives it (enough
-- memory).

open Quan Term

set_option linter.unusedSimpArgs false
set_option maxRecDepth 20000

-- Facts
-- -----

-- the list of bytes that a term reads back as is that term
theorem unbits_eq : unbits n w = some v → w = bits n v := by
  fun_induction unbits n w generalizing v
  all_goals intro h
  all_goals simp_all
  · subst h; rfl
  all_goals rename_i n w ih
  all_goals obtain ⟨a, ha, rfl⟩ := h
  all_goals rw [ih ha]
  all_goals simp [bits, ctor]
  all_goals congr 1; omega

theorem unbytes_eq : unbytes v = some bs → v = bytes bs := by
  fun_induction unbytes v generalizing bs
  all_goals intro h
  all_goals simp_all
  · subst h; rfl
  rename_i w t v l hx _
  subst h
  rw [unbits_eq hx]
  simp [bytes, list, byte, ctor, toUInt8_toNat (Gives.unbits_lt hx)]

-- in main.bend's book, renamed back to our code's names (Impl.lean), the versions hold
theorem Trusted.holds (hB : Trusted B) : Holds (Rename.book impl B) := by
  have sub (ds : List Def) (hs : ∀ d ∈ ds, d ∈ evalVersion ++ reader ++ programVersion ++ needVersion ++ trustedVersion) :
      Contains (Rename.book impl B) ds :=
    Rename.contains_book impl_ok fun d hd => by
      obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hd
      exact hB.defs _ (List.mem_map_of_mem (hs d' hd'))
  exact ⟨sub _ (by simp +contextual), sub _ (by simp +contextual), sub _ (by simp +contextual)⟩

-- Program.gives in main.bend's book is Lean's Gives
theorem Trusted.gives (hB : Trusted B) :
    Runs B (givesOf (write bk) i n) (Form.some (bytes o)) ↔ Gives bk i o n := by
  rw [← Gives.gives_iff hB.holds, Rename.runs_iff' impl_ok]
  simp [Rename.term_spine, Rename.arg, Rename.term, givesOf]

-- main, our compiler, steps to Compiler.compile on its input
theorem Trusted.main (hB : Trusted B) : Eval B (start p) (compileOf p) := by
  have hk := hB.get (d := «trustedVersion.main») (by simp [trustedVersion])
  simp only [Rename.defn, «trustedVersion.main», impl_main] at hk
  exact Eval.walk (xs := [(Q1, bytes p)]) hk (.cons (fun _ => value_bytes) .nil)
    (by simp [walk, Rename.term, bindsAt, Quan.live, takes, Term.sub, Env.sub, Term.spine, compileOf,
      unspine, Gives.dbytes])

-- the bytes w that the interpreter gives for our compiler on the bytes p
-- are what Compiler.compile(p) runs to
theorem Trusted.compiles (hB : Trusted B) (hw : interp B fuel p = some (w, k)) :
    Runs B (compileOf p) (bytes w) := by
  obtain ⟨⟨v, hs, hv, hu⟩, -⟩ := interp_iff.1 hw
  cases unbytes_eq hu
  have : ∀ u, Steps B k (start p) u → Value B u → Runs B (compileOf p) u := by
    intro u s hv
    cases s with
    | refl => exact (eval_value hB.main hv).elim
    | step e s => cases eval_det e hB.main; exact ⟨_, s, hv⟩
  exact this _ hs hv

-- the run of WASM on Compiler.compile(p) is its run on the module that
-- Compiler.compile(p) runs to
theorem Trusted.wasm (hB : Trusted B) (rc : Runs B c (bytes w))
    (hr : Runs B (wasmRun f w i m gs L) r) : Runs B (wasmOf f c i m gs L) r := by
  have hk := hB.get (d := «trustedVersion.Wasm.run») (by simp [trustedVersion])
  refine Kit.runs_args hk (.v rfl value_nat (.r rfl rc (.v rfl value_bytes (.v rfl plain_engine.value .nil)))) ?_ hr
  intro j hj; simp at hj
  rcases j with _ | _ | _ | _ | j <;> first | omega |
    simp [Rename.defn, Rename.term, «trustedVersion.Wasm.run», walk, bindsAt, Quan.live, takes, Gives.dbytes]

-- The theorems
-- ------------

-- no wrong result: a result that the Bend version of WASM gives for the module
-- that our compiler writes is one that the book gives
theorem no_wrong_result (hc : Book.check B = .ok ()) (hB : Trusted B)
    (hw : interp B fuel (write bk) = some (w, k))
    (hr : Runs B (wasmRun f w i m gs L) (resultOf o)) :
    ∃ n, Gives bk i o n := by
  obtain ⟨n, r⟩ := law_no_wrong_result hc hB (hB.wasm (hB.compiles hw) hr)
  exact ⟨n, hB.gives.1 r⟩

-- a run goes on through the steps that it takes
theorem Runs.of_steps (s : Steps B n a b) (r : Runs B a v) : Runs B b v := by
  induction s with
  | refl => exact r
  | step e _ ih =>
    obtain ⟨k, s', hv⟩ := r
    cases s' with
    | refl => exact (eval_value e hv).elim
    | step e' s'' => cases eval_det e e'; exact ih ⟨_, s'', hv⟩

-- the run of WASM on Compiler.compile(p) steps to its run on the module that
-- Compiler.compile(p) runs to
theorem Trusted.wasm_steps (hB : Trusted B) (rc : Runs B c (bytes w))
    (hr : Runs B (wasmOf f c i m gs L) r) : Runs B (wasmRun f w i m gs L) r := by
  have hk := hB.get (d := «trustedVersion.Wasm.run») (by simp [trustedVersion])
  obtain ⟨_, s, -⟩ := rc
  have vf : Value B (App Q1 (Ref (impl "Wasm.run")) (Form.nat f)) :=
    Kit.part (xs := [(Q1, _)]) hk (.cons (fun _ => value_nat) .nil)
      (by simp [Rename.defn, Rename.term, «trustedVersion.Wasm.run», walk, bindsAt, Quan.live, takes])
  exact Runs.of_steps (s.app_x vf rfl).app_f.app_f hr

-- no other failure: when the book gives a result, the Bend version of WASM, run
-- on the module that our compiler writes, gives it, or runs out of memory
theorem no_other_failure (hc : Book.check B = .ok ()) (hB : Trusted B)
    (hw : interp B fuel (write bk) = some (w, k)) (hg : Gives bk i o n) :
    ∃ f, Runs B (wasmRun f w i m gs L) (resultOf o) ∨ Runs B (wasmRun f w i m gs L) outOfMemory := by
  obtain ⟨f, r | r⟩ := law_no_other_failure (m := m) (gs := gs) (L := L) hc hB (hB.gives.2 hg)
  · exact ⟨f, .inl (hB.wasm_steps (hB.compiles hw) r)⟩
  · exact ⟨f, .inr (hB.wasm_steps (hB.compiles hw) r)⟩

-- in main.bend's book, renamed back to our code's names (Impl.lean), the versions that
-- Program.need and Program.memory need hold
theorem Trusted.needHolds (hB : Trusted B) : NeedHolds (Rename.book impl B) := by
  have sub (ds : List Def) (hs : ∀ d ∈ ds, d ∈ evalVersion ++ reader ++ programVersion ++ needVersion ++ trustedVersion) :
      Contains (Rename.book impl B) ds :=
    Rename.contains_book impl_ok fun d hd => by
      obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hd
      exact hB.defs _ (List.mem_map_of_mem (hs d' hd'))
  exact ⟨hB.holds, sub _ (by simp +contextual),
    sub [«trustedVersion.Nat.is_le»] (by simp [trustedVersion]) «trustedVersion.Nat.is_le» (by simp)⟩

-- F fits in the memory of m pages exactly when Nat.is_le(Program.need(p, i, n),
-- Program.memory(m)) runs to True in main.bend's book
theorem Trusted.big (hB : Trusted B) (hm : need bk i n ≤ memory m) :
    Runs B (bigOf (write bk) i n m) (Form.bool true) := by
  have r := Gives.big_run (bk := bk) (i := i) (n := n) (m := m) hB.needHolds
  rw [decide_eq_true hm] at r
  have := (Rename.runs_iff' impl_ok).1 r
  simpa [Rename.term_spine, Rename.arg, Rename.term, bigOf, Form.bool, impl_ctor] using this

-- an engine that takes modules of L bytes takes the module w that our compiler
-- writes, when w has at most L bytes: Nat.is_le(List.length(Compiler.compile(p)),
-- L) runs to True in main.bend's book
theorem Trusted.fits (hB : Trusted B) (hw : interp B fuel p = some (w, k)) (hL : w.length ≤ L) :
    Runs B (fitsOf p L) (Form.bool true) := by
  have h := hB.needHolds
  have hk := h.get (d := «needVersion.List.length»)
  have rc : Runs (Rename.book impl B) (App Q2 (Ref "Compiler.compile") (bytes p)) (bytes w) := by
    rw [Rename.runs_iff' impl_ok]
    simpa [Rename.term, compileOf] using hB.compiles hw
  have vl : Value (Rename.book impl B) (App Q0 (App Q0 (Ref "List.length") (Lab "Q2")) word8) :=
    Kit.part (xs := [(Q0, Lab "Q2"), (Q0, word8)]) hk
      (.cons (fun h => by simp [Quan.live] at h) (.cons (fun h => by simp [Quan.live] at h) .nil))
      (by nwalks «needVersion.List.length»)
  have rl := Kit.run_x vl rfl rc (Gives.length_run h (p := w))
  have r := Gives.is_le_run h rl (Gives.nat_run (n := L))
  rw [decide_eq_true hL] at r
  have := (Rename.runs_iff' impl_ok).1 r
  simpa [Rename.term_spine, Rename.arg, Rename.term, fitsOf, compileOf, Form.bool, impl_ctor, word8] using this

-- enough memory: with the memory that F of AGENTS.md 3.9.1.4 asks, on an engine
-- that grants each grow within its pages and takes the module, the Bend version
-- of WASM, run on the module that our compiler writes, gives the result that
-- the book gives
theorem enough_memory (hc : Book.check B = .ok ()) (hB : Trusted B)
    (hw : interp B fuel (write bk) = some (w, k)) (hg : Gives bk i o n)
    (hm : need bk i n ≤ memory m) (hL : w.length ≤ L) :
    ∃ f, Runs B (wasmRun f w i m [] L) (resultOf o) := by
  obtain ⟨f, r⟩ := law_enough_memory hc hB (hB.gives.2 hg) (hB.big hm) (hB.fits hw hL)
  exact ⟨f, hB.wasm_steps (hB.compiles hw) r⟩
