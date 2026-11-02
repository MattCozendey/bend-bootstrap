import Joining.Values
import Book.Generated.Reader
import Joining.Generated.Exists
import Program.Generated.Program
import Program.Generated.Need

-- Trusted
-- =======
--
-- The book of src/main.bend, whose main is our
-- own compiler, and which holds the laws of Compiler/spec.bend with their proofs: what
-- the theorems of Compiler.lean ask of a book B that the interpreter runs.
-- B holds the Lean versions of our code's defs that the theorems need, under
-- the names that main.bend's book gives them (Impl.lean), its main and
-- Wasm.run, Base's Exists, and a def of the type of each law: a theorem
-- needs a law's proof to exist, not to be a given one.

open Quan Term

set_option linter.unusedSimpArgs false

-- the versions of our code's defs (from its own book), and of main.bend's
-- main and Wasm.run (with our code's names as in Generated/), under
-- the names that main.bend's book gives them
def trustedDefs : List Def := (evalVersion ++ reader ++ programVersion ++ needVersion ++ trustedVersion).map (Rename.defn impl)

-- the laws of Compiler/spec.bend, by name and type (with our code's names as in
-- Generated/)
def laws : List (String × Term) :=
  [«trustedVersion.Compiler_2f_spec.no_wrong_result», «trustedVersion.Compiler_2f_spec.no_other_failure», «trustedVersion.Compiler_2f_spec.enough_memory»]

-- B has a def named l.1, of the type l.2 under the names of main.bend's book
def Declares (B : Book) (l : String × Term) : Prop :=
  ∃ d, Book.get B l.1 = some d ∧ d.T = Rename.term impl l.2

structure Trusted (B : Book) : Prop where
  defs : Contains B trustedDefs
  exists_ : Contains B existsVersion
  declares : ∀ l ∈ laws, Declares B l

-- The terms of the theorems
-- -------------------------

-- Wasm.Engine{m, gs, L}: an engine that gives a memory at most m pages, answers
-- gs to its grows, and takes modules of at most L bytes
def engineOf (m : UInt32) (gs : List Bool) (L : Nat) : Term :=
  ctor (impl "Wasm.Engine") [Form.u32 m, Form.bools gs, Form.nat L]

-- the Bend version of WASM (Wasm/impl.bend's Wasm.run), run with the fuel f on the
-- module w, the input i and the engine Wasm.Engine{m, gs, L}
def wasmRun (f : Nat) (w i : List UInt8) (m : UInt32) (gs : List Bool) (L : Nat) : Term :=
  spine (Ref (impl "Wasm.run")) [(Q1, Form.nat f), (Q2, bytes w), (Q1, bytes i), (Q1, engineOf m gs L)]

-- Wasm.Outcome.result{o}
def resultOf (o : List UInt8) : Term := ctor (impl "Wasm.Outcome.result") [bytes o]

-- Wasm.Outcome.out_of_memory{}
def outOfMemory : Term := ctor (impl "Wasm.Outcome.out_of_memory") []

-- Facts
-- -----

@[simp] theorem ren_bytes : Term.ren r (bytes bs) = bytes bs := plain_bytes.ren
@[simp] theorem sub_bytes : Term.sub s (bytes bs) = bytes bs := plain_bytes.sub
@[simp] theorem ren_nat : Term.ren r (Form.nat n) = Form.nat n := plain_nat.ren
@[simp] theorem sub_nat : Term.sub s (Form.nat n) = Form.nat n := plain_nat.sub
@[simp] theorem ren_u32 : Term.ren r (Form.u32 m) = Form.u32 m := plain_u32.ren
@[simp] theorem sub_u32 : Term.sub s (Form.u32 m) = Form.u32 m := plain_u32.sub

theorem plain_engine : Plain (engineOf m gs L) := plain_ctor (by simp [plain_u32, plain_bools, plain_nat])

@[simp] theorem ren_engine : Term.ren r (engineOf m gs L) = engineOf m gs L := plain_engine.ren
@[simp] theorem sub_engine : Term.sub s (engineOf m gs L) = engineOf m gs L := plain_engine.sub

-- a def of the versions, under its name in main.bend's book
theorem Trusted.get (hB : Trusted B) (hd : d ∈ evalVersion ++ reader ++ programVersion ++ needVersion ++ trustedVersion) :
    Book.get B (impl d.k) = some (Rename.defn impl d) :=
  hB.defs _ (List.mem_map_of_mem hd)

-- impl renames none of Base's types
theorem baseTypes_kept (hd : d ∈ baseTypes) : Rename.defn impl d = d := by
  simp only [baseTypes, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Rename.defn, Rename.term, «evalVersion.Nat», «evalVersion.Nat.arms», «evalVersion.List»,
      «evalVersion.List.arms», «evalVersion.U32», «evalVersion.U32.arms», «evalVersion.Word», «evalVersion.Word.Nil»,
      «evalVersion.Word.Nil.arms», «evalVersion.Word.Con», «evalVersion.Word.Con.arms», «evalVersion.Bool»,
      «evalVersion.Bool.arms», «evalVersion.Maybe», «evalVersion.Maybe.arms»]

theorem Trusted.types (hB : Trusted B) : Contains B baseTypes := by
  intro d hd
  have h1 : d ∈ evalVersion ++ reader ++ programVersion ++ needVersion ++ trustedVersion := by
    simp only [baseTypes, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [evalVersion]
  have h2 := baseTypes_kept hd
  have := hB.get h1
  rwa [h2, show impl d.k = d.k from congrArg Def.k h2] at this

-- a closed, live call on plain arguments
theorem closed_call (h : ∀ a ∈ xs, Plain a.2) : Term.Closed (spine (Ref k) xs) :=
  closed_spine.2 ⟨fun _ => rfl, fun a ha => (h a ha).closed⟩

theorem live_call' (hk : Book.get B k = some d) (h : ∀ a ∈ xs, Plain a.2) :
    Term.Live B (spine (Ref k) xs) := by
  refine live_spine.2 ⟨?_, fun a ha _ => (h a ha).live⟩
  obtain ⟨j, hj⟩ := index_of_get hk
  simp [Term.Live, Term.live, called, unspine, hj, index_lt hj]

-- the type of a law, from its def
theorem Trusted.law {l : String × Term} (hB : Trusted B) (hl : l ∈ _root_.laws) :
    Typed B [] (Ref l.1) (Rename.term impl l.2) := by
  obtain ⟨d, hd, hT⟩ := hB.declares l hl
  have := Typed.ref (Γ := []) (σ := Var) hd
  rwa [sub_var, hT] at this

-- an engine is a value of Wasm.Engine
theorem typed_engine (hB : Trusted B) (cl : Book.Closed B) :
    Typed B [] (engineOf m gs L) (Ref (impl "Wasm.Engine")) := by
  have hT := hB.types
  have hE := hB.get (d := «trustedVersion.Wasm.Engine») (by simp [trustedVersion])
  have hA := hB.get (d := «trustedVersion.Wasm.Engine.arms») (by simp [trustedVersion])
  simp only [Rename.defn, Rename.term, «trustedVersion.Wasm.Engine», «trustedVersion.Wasm.Engine.arms», impl_U32,
    impl_List, impl_Bool, impl_Nat, impl_unit, List.map] at hE hA
  simp only [engineOf, ctor, List.foldr]
  refine typed_pair (A := Enu [impl "Wasm.Engine"]) (Bt := App Q1 (Ref (impl "Wasm.Engine.arms")) (Var 0))
    (.lab (by simp)) ?_ (.step (.delta hE (cl _ _ hE)) .refl)
  simp only [Term.inst, Term.sub, Subst.one]
  refine typed_pair (A := Ref "U32") (Bt := Sig Q1 listBools (Sig Q1 (Ref "Nat") (Enu ["()"]))) (typed_u32' hT cl) ?_ ?_
  · simp only [Term.inst, Term.sub, Subst.one, Subst.up, Term.ren, listBools]
    refine typed_pair (Bt := Sig Q1 (Ref "Nat") (Enu ["()"])) (typed_bools hT cl) ?_ .refl
    simp only [Term.inst, Term.sub, Subst.one, Subst.up, Term.ren]
    refine typed_pair (Bt := Enu ["()"]) (typed_nat hT cl) (typed_label (ks := ["()"]) (by simp) ?_) .refl
    simp only [Term.inst, Term.sub]; exact .refl
  · exact .step (.app (.delta hA (cl _ _ hA)) par_refl) (.step (.hit par_refl) .refl)
