import Joining.Compiler
import Book.Prune

-- SelfHost
-- ========
--
-- AGENTS.md 3.8.7: the binary wc that the interpreter writes when it runs our
-- compiler (the main of main.bend's book B) on the bytes of B's pruned book
-- gives, for each book bk, what our compiler gives for bk: what the
-- interpreter writes when it runs B on bk's bytes. So the theorems of
-- Compiler.lean hold for every module that wc writes.

open Quan Term

variable {B bk : Book} {wc w : List UInt8} {fuel fuel' k f n : Nat} {m : UInt32} {gs : List Bool} {i : List UInt8}

-- a module that wc writes for bk is the one that our compiler writes for bk
theorem self_host (hc : Book.check B = .ok ()) (hB : Trusted B)
    (hs : interp B fuel (write (prune B)) = some (wc, k))
    (hb : Runs B (wasmRun f wc (write bk) m gs) (resultOf w)) :
    ∃ n, interp B n (write bk) = some (w, n) := by
  obtain ⟨n, g⟩ := no_wrong_result hc hB hs hb
  exact ⟨n, interp_iff.2 ⟨prune_gives.1 g, Nat.le_refl n⟩⟩

-- when our compiler writes w for bk, wc writes it or runs out of memory, in one
-- fuel for all of the engine's answers
theorem self_host_complete (hc : Book.check B = .ok ()) (hB : Trusted B)
    (hs : interp B fuel (write (prune B)) = some (wc, k))
    (hw : interp B fuel' (write bk) = some (w, n)) :
    ∃ f, ∀ gs, Runs B (wasmRun f wc (write bk) m gs) (resultOf w) ∨
      Runs B (wasmRun f wc (write bk) m gs) outOfMemory :=
  no_other_failure hc hB hs (prune_gives.2 (interp_iff.1 hw).1)

-- with the memory of AGENTS.md 3.9.1.4, wc writes it
theorem self_host_memory (hc : Book.check B = .ok ()) (hB : Trusted B)
    (hs : interp B fuel (write (prune B)) = some (wc, k))
    (hw : interp B fuel' (write bk) = some (w, n))
    (hm : need (prune B) (write bk) n ≤ memory m) :
    ∃ f, Runs B (wasmRun f wc (write bk) m []) (resultOf w) :=
  enough_memory hc hB hs (prune_gives.2 (interp_iff.1 hw).1) hm

-- wc is never outside the subset
theorem self_host_in_subset (hc : Book.check B = .ok ()) (hB : Trusted B)
    (hs : interp B fuel (write (prune B)) = some (wc, k)) :
    ¬ Runs B (wasmRun f wc i m gs) unsupported :=
  in_subset hc hB hs

-- AGENTS.md 3.8.7, end to end: the binary wc that the interpreter writes when it runs
-- main.bend's book B on B's own pruned book writes, for each book bk's pruned
-- book, a module w whose runs follow the laws for bk itself
theorem trusted_binary (hc : Book.check B = .ok ()) (hB : Trusted B)
    (hs : interp B fuel (write (prune B)) = some (wc, k))
    (hw : Runs B (wasmRun f wc (write (prune bk)) m gs) (resultOf w)) :
    (∀ f' m' gs' o, Runs B (wasmRun f' w i m' gs') (resultOf o) → ∃ n, Gives bk i o n) ∧
    (∀ o n m', Gives bk i o n → ∃ f', ∀ gs',
      Runs B (wasmRun f' w i m' gs') (resultOf o) ∨ Runs B (wasmRun f' w i m' gs') outOfMemory) ∧
    (∀ o n m', Gives bk i o n → need (prune bk) i n ≤ memory m' →
      ∃ f', Runs B (wasmRun f' w i m' []) (resultOf o)) ∧
    (∀ f' m' gs', ¬ Runs B (wasmRun f' w i m' gs') unsupported) := by
  obtain ⟨n, hn⟩ := self_host hc hB hs hw
  refine ⟨fun f' m' gs' o r => ?_, fun o n' m' g => no_other_failure hc hB hn (prune_gives.2 g),
    fun o n' m' g hm => enough_memory hc hB hn (prune_gives.2 g) hm, fun f' m' gs' => in_subset hc hB hn⟩
  obtain ⟨n', g⟩ := no_wrong_result hc hB hn r
  exact ⟨n', prune_gives.1 g⟩
