import Joining.Rename
import Joining.Generated.Trusted

-- Impl
-- ====
--
-- The names that `bend -o` gives our code's defs and labels in the book of
-- main.bend, which imports the files of src/: p ++ k for each name k of the
-- file whose prefix is p (its path, as trustedVersion.prefixes lists them:
-- Compiler/impl.bend's is Compiler_2f_impl.), and Base's names as they are.
-- The Lean versions of our code (each feature's Generated/) name them k, as one book
-- would. impl is the renaming of Rename that swaps k and p ++ k for each such
-- k (trustedVersion.names, as the book of main.bend names them), and keeps
-- the names of `kept`: Base's names that the theorems name.

open Quan Term

-- Base's names that the theorems name, which impl keeps
def kept : List String :=
  ["main", "Q0", "Q1", "Q2", "()", "Tuple", "Exists", "Sigma", "Sigma.arms",
   "Zero", "Succ", "Nat", "Nat.arms", "Nil", "Con", "List", "List.arms", "U32", "U32.arms",
   "WNil", "WCon", "Word", "Word.Nil", "Word.Nil.arms", "Word.Con", "Word.Con.arms",
   "False", "True", "Bool", "Bool.arms", "None", "Some", "Maybe", "Maybe.arms",
   "Or", "Either", "Either.arms", "Inl", "Inr", "Empty", "Empty.arms"]

-- s without the prefix p, when it has it
def stripPre (p s : String) : Option String :=
  if p.toList.isPrefixOf s.toList then some (String.ofList (s.toList.drop p.toList.length))
  else none

-- the first prefix of a file that s has, and s without it
def unimpl (s : String) : Option (String × String) :=
  trustedVersion.prefixes.findSome? fun p => (stripPre p s).map (p, ·)

-- the prefix of t's file: the first prefix p such that the book of main.bend names p ++ t
def pre (t : String) : Option String :=
  trustedVersion.prefixes.find? fun p => trustedVersion.names.contains (p ++ t)

-- t is a name of our code's own, which the book of main.bend names p ++ t, with p its
-- file's prefix
def moves (t : String) : Bool :=
  !kept.contains t && !trustedVersion.names.contains t &&
    match pre t with
    | some p => !kept.contains (p ++ t)
    | none => false

def impl (s : String) : String :=
  if moves s then (pre s).getD "" ++ s
  else match unimpl s with
    | some (p, t) => if moves t && pre t == some p then t else s
    | none => s

-- no prefix of a file is a prefix of another one
theorem prefixes_free :
    ∀ p ∈ trustedVersion.prefixes, ∀ q ∈ trustedVersion.prefixes, p.toList.isPrefixOf q.toList = true → p = q := by
  decide

theorem stripPre_append : stripPre p (p ++ t) = some t := by
  have : p.toList.isPrefixOf (p ++ t).toList = true := by
    rw [String.toList_append, List.isPrefixOf_iff_prefix]; exact List.prefix_append _ _
  unfold stripPre; split
  · rw [String.toList_append, List.drop_left, String.ofList_toList]
  · contradiction

theorem stripPre_some (h : stripPre p s = some t) : s = p ++ t := by
  unfold stripPre at h
  split at h
  · rename_i hp
    cases h
    rw [List.isPrefixOf_iff_prefix, List.prefix_iff_eq_append] at hp
    apply String.ext
    rw [String.toList_append]
    simp only [String.toList_ofList]
    exact hp.symm
  · cases h

theorem stripPre_prefix (h : (stripPre q s).isSome) : q.toList <+: s.toList := by
  unfold stripPre at h
  split at h
  · rename_i hp; exact List.isPrefixOf_iff_prefix.1 hp
  · cases h

theorem unimpl_some (h : unimpl s = some (p, t)) : s = p ++ t := by
  obtain ⟨q, -, hq⟩ := List.exists_of_findSome?_eq_some h
  cases hs : stripPre q s with
  | none => simp [hs] at hq
  | some u =>
    simp only [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hq
    obtain ⟨rfl, rfl⟩ := hq
    exact stripPre_some hs

-- the first of the prefixes L that x has is p, when no other one of L is a prefix of x
theorem findSome_only {L : List String} (hp : p ∈ L) (hs : stripPre p x = some t)
    (only : ∀ q ∈ L, (stripPre q x).isSome → q = p) :
    L.findSome? (fun q => (stripPre q x).map (q, ·)) = some (p, t) := by
  induction L with
  | nil => cases hp
  | cons q qs ih =>
    by_cases e : q = p
    · subst e; simp [hs]
    · have hn : stripPre q x = none := by
        cases h : stripPre q x with
        | none => rfl
        | some _ => exact absurd (only q List.mem_cons_self (by simp [h])) e
      rw [List.findSome?_cons_of_isNone (by simp [hn])]
      exact ih ((List.mem_cons.1 hp).resolve_left fun h => e h.symm)
        (fun q' hq' => only q' (List.mem_cons_of_mem _ hq'))

-- the first prefix that p ++ t has is p, when p is a file's
theorem unimpl_append (hp : p ∈ trustedVersion.prefixes) : unimpl (p ++ t) = some (p, t) := by
  apply findSome_only hp stripPre_append
  intro q hq hs
  have h1 := stripPre_prefix hs
  have h2 : p.toList <+: (p ++ t).toList := by
    rw [String.toList_append]; exact List.prefix_append _ _
  rcases Nat.le_total q.toList.length p.toList.length with l | l
  · exact prefixes_free q hq p hp (List.isPrefixOf_iff_prefix.2 (List.prefix_of_prefix_length_le h1 h2 l))
  · exact (prefixes_free p hp q hq (List.isPrefixOf_iff_prefix.2 (List.prefix_of_prefix_length_le h2 h1 l))).symm

theorem pre_mem (h : pre t = some p) : p ∈ trustedVersion.prefixes ∧ trustedVersion.names.contains (p ++ t) = true := by
  unfold pre at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem moves_pre (h : moves t = true) : ∃ p, pre t = some p ∧ trustedVersion.names.contains (p ++ t) = true ∧
    kept.contains (p ++ t) = false := by
  unfold moves at h
  cases hp : pre t with
  | none => simp [hp] at h
  | some p => simp only [hp, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
              exact ⟨p, rfl, (pre_mem hp).2, h.2⟩

theorem impl_impl (s : String) : impl (impl s) = s := by
  by_cases hs : moves s = true
  · obtain ⟨p, hp, hn, -⟩ := moves_pre hs
    have h1 : impl s = p ++ s := by simp [impl, hs, hp]
    have h2 : moves (p ++ s) = false := by
      simp only [moves, hn, Bool.not_true, Bool.and_false, Bool.false_and]
    rw [h1]
    simp only [impl, h2, Bool.false_eq_true, ite_false, unimpl_append (pre_mem hp).1, hs, hp,
      beq_self_eq_true, Bool.and_self, ite_true]
  · cases hu : unimpl s with
    | none => simp [impl, hs, hu]
    | some pt =>
      obtain ⟨p, t⟩ := pt
      by_cases ht : moves t = true ∧ pre t = some p
      · have e := unimpl_some hu
        have h1 : impl s = t := by simp [impl, hs, hu, ht.1, ht.2]
        rw [h1]
        simp [impl, ht.1, ht.2, e]
      · have h1 : impl s = s := by
          simp only [impl, hs, hu, Bool.false_eq_true, ite_false]
          split
          · rename_i hc; simp only [Bool.and_eq_true, beq_iff_eq] at hc; exact absurd hc ht
          · rfl
        rw [h1, h1]

-- impl keeps the names of kept
theorem impl_kept (h : s ∈ kept) : impl s = s := by
  have hk : kept.contains s = true := by simpa using h
  have hs : moves s = false := by simp only [moves, hk, Bool.not_true, Bool.false_and]
  cases hu : unimpl s with
  | none => simp [impl, hs, hu]
  | some pt =>
    obtain ⟨p, t⟩ := pt
    have e := unimpl_some hu
    simp only [impl, hs, hu, Bool.false_eq_true, ite_false]
    split
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨p', hp', -, hk'⟩ := moves_pre hc.1
      rw [hc.2] at hp'; cases hp'
      rw [e] at hk; rw [hk] at hk'; cases hk'
    · rfl

theorem impl_ok : Rename.Ok impl where
  inv := impl_impl
  qs := fun s h => impl_kept (by simp only [QS, List.mem_cons, List.not_mem_nil, or_false] at h
                                 rcases h with rfl | rfl | rfl <;> decide)
