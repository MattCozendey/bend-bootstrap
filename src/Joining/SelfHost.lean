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

variable {B bk : Book} {wc w : List UInt8} {fuel fuel' k f n : Nat} {m : UInt32} {gs : List Bool}

-- a module that wc writes for bk is the one that our compiler writes for bk
theorem self_host (hc : Book.check B = .ok ()) (hB : Trusted B)
    (hs : interp B fuel (write (prune B)) = some (wc, k))
    (hb : Runs B (wasmRun f wc (write bk) m gs) (resultOf w)) :
    ∃ n, interp B n (write bk) = some (w, n) := by
  obtain ⟨n, g⟩ := no_wrong_result hc hB hs hb
  exact ⟨n, interp_iff.2 ⟨prune_gives.1 g, Nat.le_refl n⟩⟩

-- when our compiler writes w for bk, wc writes it or runs out of memory
theorem self_host_complete (hc : Book.check B = .ok ()) (hB : Trusted B)
    (hs : interp B fuel (write (prune B)) = some (wc, k))
    (hw : interp B fuel' (write bk) = some (w, n)) :
    ∃ f, Runs B (wasmRun f wc (write bk) m gs) (resultOf w) ∨
      Runs B (wasmRun f wc (write bk) m gs) outOfMemory :=
  no_other_failure hc hB hs (prune_gives.2 (interp_iff.1 hw).1)

-- with the memory of AGENTS.md 3.9.1.4, wc writes it
theorem self_host_memory (hc : Book.check B = .ok ()) (hB : Trusted B)
    (hs : interp B fuel (write (prune B)) = some (wc, k))
    (hw : interp B fuel' (write bk) = some (w, n))
    (hm : need (prune B) (write bk) n ≤ memory m) :
    ∃ f, Runs B (wasmRun f wc (write bk) m []) (resultOf w) :=
  enough_memory hc hB hs (prune_gives.2 (interp_iff.1 hw).1) hm
