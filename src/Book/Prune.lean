import Interpreter.Program

-- Prune
-- =====
--
-- AGENTS.md 3.6.8: the defs that a run of a program can call. Eval reads the
-- book in one place only, the body of a called def (Eval.call, Value.call), and
-- it never makes a name (3.3.7). So a run from `main` calls only the defs that
-- main's body reaches through the bodies of defs, and the book of those defs
-- gives what the whole book gives (prune_gives). A def's type never runs.
--
-- prune finds that set fast (reach, a worklist over a HashSet) and then checks
-- it (closed, one pass over the book): only the check is proven, so when it
-- fails, prune keeps the whole book, which is always right.

open Quan Term

-- Names
-- -----

-- each name of a Ref in t satisfies p
def Term.refsIn (p : String → Bool) : Term → Bool
  | Var _ => true
  | Ref k => p k
  | Ann x T => x.refsIn p && T.refsIn p
  | Let _ v f => v.refsIn p && f.refsIn p
  | Typ q => q.refsIn p
  | Min a b => a.refsIn p && b.refsIn p
  | All _ A B => A.refsIn p && B.refsIn p
  | Lam _ f => f.refsIn p
  | App _ f x => f.refsIn p && x.refsIn p
  | Sig _ A B => A.refsIn p && B.refsIn p
  | Tup _ a b => a.refsIn p && b.refsIn p
  | Prj h => h.refsIn p
  | Enu _ => true
  | Lab _ => true
  | Mat _ h m => h.refsIn p && m.refsIn p
  | Efq => true
  | Eql a b T => a.refsIn p && b.refsIn p && T.refsIn p
  | Rfl => true
  | Rwt e P f => e.refsIn p && P.refsIn p && f.refsIn p

-- the names of the Refs in t, before acc
def Term.refs : Term → List String → List String
  | Var _, acc => acc
  | Ref k, acc => k :: acc
  | Ann x T, acc => x.refs (T.refs acc)
  | Let _ v f, acc => v.refs (f.refs acc)
  | Typ q, acc => q.refs acc
  | Min a b, acc => a.refs (b.refs acc)
  | All _ A B, acc => A.refs (B.refs acc)
  | Lam _ f, acc => f.refs acc
  | App _ f x, acc => f.refs (x.refs acc)
  | Sig _ A B, acc => A.refs (B.refs acc)
  | Tup _ a b, acc => a.refs (b.refs acc)
  | Prj h, acc => h.refs acc
  | Enu _, acc => acc
  | Lab _, acc => acc
  | Mat _ h m, acc => h.refs (m.refs acc)
  | Efq, acc => acc
  | Eql a b T, acc => a.refs (b.refs (T.refs acc))
  | Rfl, acc => acc
  | Rwt e P f, acc => e.refs (P.refs (f.refs acc))

-- The book of the defs that p keeps
-- ---------------------------------

-- the defs whose names p keeps, in their order
def Book.keep (p : String → Bool) (bk : Book) : Book :=
  Book.of (bk.defs.filter (p ·.k))

-- the body of each def whose name p keeps names only what p keeps
def Book.closed (p : String → Bool) (bk : Book) : Bool :=
  bk.defs.all fun d => !p d.k || d.v.refsIn p

-- the names that main reaches through the bodies of defs: one pop of the
-- worklist for each name in it, so fuel for each Ref of every body, and main
def Book.reach (bk : Book) : Nat → List String → Std.HashSet String → Std.HashSet String
  | 0, _, seen => seen
  | _, [], seen => seen
  | n + 1, k :: ks, seen =>
    if seen.contains k then Book.reach bk n ks seen
    else Book.reach bk n (((bk.get k).map (·.v.refs ks)).getD ks) (seen.insert k)

def Book.fuel (bk : Book) : Nat :=
  bk.defs.foldl (fun n d => n + (d.v.refs []).length) 1

-- the book of the defs that a run from main can call, when the check passes,
-- else the whole book
def prune (bk : Book) : Book :=
  let seen := Book.reach bk bk.fuel ["main"] {}
  let p := (seen.contains ·)
  if p "main" && bk.closed p then bk.keep p else bk

-- Facts
-- -----

theorem refsIn_ren (r : Ren) (t : Term) : (Term.ren r t).refsIn p = t.refsIn p := by
  induction t generalizing r <;> simp_all [Term.ren, Term.refsIn]

theorem refsIn_up (hs : ∀ i, (s i).refsIn p) : ∀ i, (Subst.up s i).refsIn p
  | 0 => rfl
  | i + 1 => by simp [Subst.up, refsIn_ren, hs i]

theorem refsIn_sub (hs : ∀ i, (s i).refsIn p) (ht : t.refsIn p) : (Term.sub s t).refsIn p := by
  induction t generalizing s with
  | Var i => exact hs i
  | Rwt e P f ihe ihP ihf =>
    simp only [Term.sub, Term.refsIn, Bool.and_eq_true] at ht ⊢
    exact ⟨⟨ihe hs ht.1.1, ihP (refsIn_up (refsIn_up hs)) ht.1.2⟩, ihf hs ht.2⟩
  | _ => simp_all [Term.sub, Term.refsIn, refsIn_up]

theorem refsIn_inst (hf : f.refsIn p) (hv : v.refsIn p) : (Term.inst f v).refsIn p :=
  refsIn_sub (fun | 0 => hv | _ + 1 => rfl) hf

theorem refsIn_spine : (Term.spine t xs).refsIn p = (t.refsIn p && xs.all (·.2.refsIn p)) := by
  induction xs generalizing t with
  | nil => simp [Term.spine]
  | cons a xs ih => obtain ⟨q, x⟩ := a; simp [Term.spine, ih, Term.refsIn, Bool.and_assoc]

theorem refsIn_envSub (he : ∀ x ∈ e, x.refsIn p) : ∀ i, (Env.sub e i).refsIn p := by
  induction e with
  | nil => intro i; rfl
  | cons x e ih =>
    intro i; cases i with
    | zero => exact he x (.head _)
    | succ i => exact ih (fun y hy => he y (.tail _ hy)) i

theorem refsIn_qmin (ha : a.refsIn p) (hb : b.refsIn p) : (Term.qmin a b).refsIn p := by
  unfold Term.qmin; split <;> simp_all [Term.refsIn]

-- a walk's leaf names only what its tree, its environment and its spine name
theorem refsIn_walk (w : Walk bk f e xs o) (hf : f.refsIn p) (he : ∀ x ∈ e, x.refsIn p)
    (hx : ∀ a ∈ xs, a.2.refsIn p) : ∀ t, o = some t → t.refsIn p := by
  induction w with
  | lam _ _ _ ih =>
    exact ih hf (fun y hy => by
      cases hy with
      | head => exact hx _ (.head _)
      | tail _ hy => exact he y hy) (fun a ha => hx a (.tail _ ha))
  | prj _ _ ih =>
    have ht := hx _ (.head _)
    simp only [Term.refsIn, Bool.and_eq_true] at ht
    exact ih hf he (by
      intro a ha
      simp only [List.mem_cons] at ha
      rcases ha with rfl | rfl | ha
      · exact ht.1
      · exact ht.2
      · exact hx a (.tail _ ha))
  | hit _ _ ih =>
    simp only [Term.refsIn, Bool.and_eq_true] at hf; exact ih hf.1 he (fun a ha => hx a (.tail _ ha))
  | miss _ _ _ ih => simp only [Term.refsIn, Bool.and_eq_true] at hf; exact ih hf.2 he hx
  | app _ _ ih =>
    simp only [Term.refsIn, Bool.and_eq_true] at hf
    exact ih hf.1 he (fun a ha => by
      cases ha with
      | head => exact refsIn_envSub he _
      | tail _ ha => exact hx a ha)
  | need => intro _ h; cases h
  | done =>
    intro t h; cases h
    rw [refsIn_spine, Bool.and_eq_true]
    exact ⟨refsIn_sub (refsIn_envSub he) hf, List.all_eq_true.2 hx⟩

-- with the bodies of p's defs naming only what p keeps, a step names only
-- what p keeps
theorem refsIn_eval (hb : ∀ k d, Book.get bk k = some d → p k → d.v.refsIn p)
    (e : Eval bk t u) (ht : t.refsIn p) : u.refsIn p := by
  induction e with
  | call hk _ w =>
    rw [refsIn_spine, Bool.and_eq_true] at ht
    exact refsIn_walk w (hb _ _ hk ht.1) (by simp) (fun a ha => List.all_eq_true.1 ht.2 a ha) _ rfl
  | beta =>
    simp only [Term.refsIn, Bool.and_eq_true] at ht
    exact refsIn_inst ht.1 ht.2
  | unlet =>
    simp only [Term.refsIn, Bool.and_eq_true] at ht
    exact refsIn_inst ht.2 ht.1
  | meet => exact refsIn_qmin rfl rfl
  | _ => simp_all [Term.refsIn]

-- Walks, values and steps in two books
-- ------------------------------------

-- a walk never reads its book
theorem Walk.book (w : Walk bk t e xs o) : Walk bk' t e xs o := by
  induction w with
  | lam a b _ ih => exact .lam a b ih
  | prj a _ ih => exact .prj a ih
  | hit a _ ih => exact .hit a ih
  | miss a b _ ih => exact .miss a b ih
  | app a _ ih => exact .app a ih
  | need a => exact .need a
  | done a => exact .done a

section
variable {B C : Book}

-- a value in a book is one in each book that holds its defs
mutual
theorem Value.sub (hs : ∀ k d, Book.get C k = some d → Book.get B k = some d) :
    Value C t → Value B t
  | .lam => .lam
  | .prj => .prj
  | .mat => .mat
  | .efq => .efq
  | .lab => .lab
  | .rfl => .rfl
  | .typ => .typ
  | .all => .all
  | .sig => .sig
  | .enu => .enu
  | .eql => .eql
  | .tup ha hb => .tup (fun h => Value.sub hs (ha h)) (Value.sub hs hb)
  | .call hk hx w => .call (hs _ _ hk) (Values.sub hs hx) w.book

theorem Values.sub (hs : ∀ k d, Book.get C k = some d → Book.get B k = some d) :
    Values C xs → Values B xs
  | .nil => .nil
  | .cons ha hx => .cons (fun h => Value.sub hs (ha h)) (Values.sub hs hx)
end

-- a value that names only what p keeps is one in each book that agrees on p's names
mutual
theorem Value.keep (hg : ∀ k, p k → Book.get C k = Book.get B k) :
    Value B t → t.refsIn p → Value C t
  | .lam, _ => .lam
  | .prj, _ => .prj
  | .mat, _ => .mat
  | .efq, _ => .efq
  | .lab, _ => .lab
  | .rfl, _ => .rfl
  | .typ, _ => .typ
  | .all, _ => .all
  | .sig, _ => .sig
  | .enu, _ => .enu
  | .eql, _ => .eql
  | .tup ha hb, ht => by
    simp only [Term.refsIn, Bool.and_eq_true] at ht
    exact .tup (fun h => Value.keep hg (ha h) ht.1) (Value.keep hg hb ht.2)
  | .call hk hx w, ht => by
    rw [refsIn_spine, Bool.and_eq_true] at ht
    exact .call ((hg _ ht.1).trans hk) (Values.keep hg hx ht.2) w.book

theorem Values.keep (hg : ∀ k, p k → Book.get C k = Book.get B k) :
    Values B xs → xs.all (·.2.refsIn p) → Values C xs
  | .nil, _ => .nil
  | .cons ha hx, ht => by
    simp only [List.all_cons, Bool.and_eq_true] at ht
    exact .cons (fun h => Value.keep hg (ha h) ht.1) (Values.keep hg hx ht.2)
end

theorem Eval.sub (hs : ∀ k d, Book.get C k = some d → Book.get B k = some d)
    (e : Eval C t u) : Eval B t u := by
  induction e with
  | ann => exact .ann
  | app_f _ ih => exact .app_f ih
  | app_x hf hq _ ih => exact .app_x (Value.sub hs hf) hq ih
  | beta a hx c => exact .beta a (fun h => Value.sub hs (hx h)) c
  | split hq hv => exact .split hq (Value.sub hs hv)
  | hit hq => exact .hit hq
  | miss hq hj => exact .miss hq hj
  | call hk hx w => exact .call (hs _ _ hk) (Values.sub hs hx) w.book
  | lett hq _ ih => exact .lett hq ih
  | unlet hv hd => exact .unlet (fun h => Value.sub hs (hv h)) hd
  | tup_a hq _ ih => exact .tup_a hq ih
  | tup_b ha _ ih => exact .tup_b (fun h => Value.sub hs (ha h)) ih
  | rwt _ ih => exact .rwt ih
  | cast => exact .cast
  | min_a _ ih => exact .min_a ih
  | min_b ha _ ih => exact .min_b (Value.sub hs ha) ih
  | meet hi hj => exact .meet hi hj

theorem Eval.keep (hg : ∀ k, p k → Book.get C k = Book.get B k)
    (e : Eval B t u) (ht : t.refsIn p) : Eval C t u := by
  induction e with
  | ann => exact .ann
  | app_f _ ih => simp only [Term.refsIn, Bool.and_eq_true] at ht; exact .app_f (ih ht.1)
  | app_x hf hq _ ih =>
    simp only [Term.refsIn, Bool.and_eq_true] at ht
    exact .app_x (Value.keep hg hf ht.1) hq (ih ht.2)
  | beta a hx c =>
    simp only [Term.refsIn, Bool.and_eq_true] at ht
    exact .beta a (fun h => Value.keep hg (hx h) ht.2) c
  | split hq hv =>
    simp only [Term.refsIn, Bool.and_eq_true] at ht
    exact .split hq (Value.keep hg hv (by simp only [Term.refsIn, Bool.and_eq_true]; exact ht.2))
  | hit hq => exact .hit hq
  | miss hq hj => exact .miss hq hj
  | call hk hx w =>
    rw [refsIn_spine, Bool.and_eq_true] at ht
    exact .call ((hg _ ht.1).trans hk) (Values.keep hg hx ht.2) w.book
  | lett hq _ ih => simp only [Term.refsIn, Bool.and_eq_true] at ht; exact .lett hq (ih ht.1)
  | unlet hv hd =>
    simp only [Term.refsIn, Bool.and_eq_true] at ht
    exact .unlet (fun h => Value.keep hg (hv h) ht.1) hd
  | tup_a hq _ ih => simp only [Term.refsIn, Bool.and_eq_true] at ht; exact .tup_a hq (ih ht.1)
  | tup_b ha _ ih =>
    simp only [Term.refsIn, Bool.and_eq_true] at ht
    exact .tup_b (fun h => Value.keep hg (ha h) ht.1) (ih ht.2)
  | rwt _ ih => simp only [Term.refsIn, Bool.and_eq_true] at ht; exact .rwt (ih ht.1.1)
  | cast => exact .cast
  | min_a _ ih => simp only [Term.refsIn, Bool.and_eq_true] at ht; exact .min_a (ih ht.1)
  | min_b ha _ ih =>
    simp only [Term.refsIn, Bool.and_eq_true] at ht
    exact .min_b (Value.keep hg ha ht.1) (ih ht.2)
  | meet hi hj => exact .meet hi hj

theorem Steps.sub (hs : ∀ k d, Book.get C k = some d → Book.get B k = some d)
    (s : Steps C n t u) : Steps B n t u := by
  induction s with
  | refl => exact .refl
  | step e _ ih => exact .step (e.sub hs) ih

theorem Steps.keep (hg : ∀ k, p k → Book.get C k = Book.get B k)
    (hb : ∀ k d, Book.get B k = some d → p k → d.v.refsIn p)
    (s : Steps B n t u) (ht : t.refsIn p) : Steps C n t u ∧ u.refsIn p := by
  induction s with
  | refl => exact ⟨.refl, ht⟩
  | step e _ ih =>
    obtain ⟨s', hu⟩ := ih (refsIn_eval hb e ht)
    exact ⟨.step (e.keep hg ht) s', hu⟩

end

-- The kept book
-- -------------

variable {p : String → Bool} {k : String} {ds : List Def} {bk : Book} {d : Def}

theorem find_filter_keep (h : p k = true) :
    (ds.filter (p ·.k)).find? (·.k == k) = ds.find? (·.k == k) := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    by_cases hd : d.k = k
    · subst hd; simp [h]
    · by_cases hp : p d.k <;> simp [hp, hd, ih]

theorem find_filter_drop (h : p k = false) : (ds.filter (p ·.k)).find? (·.k == k) = none := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    by_cases hd : d.k = k
    · subst hd; simp [h, ih]
    · by_cases hp : p d.k <;> simp [hp, hd, ih]

theorem keep_get (h : p k = true) : Book.get (bk.keep p) k = Book.get bk k := by
  rw [get_find, get_find]; exact find_filter_keep h

theorem keep_sub : Book.get (bk.keep p) k = some d → Book.get bk k = some d := by
  cases h : p k
  · rw [get_find]; simp [Book.keep, Book.of, find_filter_drop h]
  · rw [keep_get h]; exact id

theorem closed_bodies (hc : bk.closed p = true) :
    ∀ k d, Book.get bk k = some d → p k → d.v.refsIn p := by
  intro k d hk hp
  rw [get_find] at hk
  have hm := List.mem_of_find?_eq_some hk
  have hd : d.k = k := by simpa using List.find?_some hk
  have := List.all_eq_true.1 hc d hm
  simp_all

theorem refsIn_bits : (bits n v).refsIn p := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => simp [bits, ctor, Term.refsIn, ih]

theorem refsIn_bytes : (bytes i).refsIn p := by
  induction i with
  | nil => rfl
  | cons b bs ih => simpa [bytes, list, byte, ctor, Term.refsIn, refsIn_bits] using ih

-- a book that keeps main and the bodies that it reaches gives what the whole
-- book gives
theorem keep_gives (hm : p "main" = true) (hc : bk.closed p = true) :
    Gives (bk.keep p) i r n ↔ Gives bk i r n := by
  have hs : ∀ k d, Book.get (bk.keep p) k = some d → Book.get bk k = some d := fun _ _ => keep_sub
  have hg : ∀ k, p k → Book.get (bk.keep p) k = Book.get bk k := fun _ h => keep_get h
  have ht : (start i).refsIn p := by simp [start, Term.refsIn, hm, refsIn_bytes]
  constructor
  · rintro ⟨v, s, hv, hu⟩
    exact ⟨v, s.sub hs, Value.sub hs hv, hu⟩
  · rintro ⟨v, s, hv, hu⟩
    obtain ⟨s', hr⟩ := s.keep hg (closed_bodies hc) ht
    exact ⟨v, s', Value.keep hg hv hr, hu⟩

-- AGENTS.md 3.6.8: the pruned book gives what the book gives, after the same
-- number of steps
theorem prune_gives : Gives (prune bk) i r n ↔ Gives bk i r n := by
  unfold prune
  dsimp only
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    exact keep_gives h.1 h.2
  · exact Iff.rfl
