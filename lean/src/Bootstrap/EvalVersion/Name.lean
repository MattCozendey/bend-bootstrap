import Bootstrap.EvalSteps.Bool

-- EvalSteps.Name
-- ==============
--
-- The defs of the Bend version of Eval on names: equality, the lookup of a def, and the
-- meet of two quantity labels.

open Quan Term

namespace EvalVersion

-- a call whose arguments are values steps to the leaf of its walk
private theorem run_call (hk : Book.get B k = some d) (vs : Values B xs)
    (w : walk B d.v [] xs = some (some u)) (r : Runs B u v) : Runs B (spine (Ref k) xs) v :=
  .step (Eval.walk hk vs w) r

-- a call that needs more arguments is a value
private theorem value_part (hk : Book.get B k = some d) (vs : Values B xs)
    (w : walk B d.v [] xs = some none) : Value B (spine (Ref k) xs) :=
  .call hk vs (walk_iff.1 w)

-- the argument of a value runs first
private theorem run_x (vf : Value B f) (l : q.live = true) (rx : Runs B x x')
    (r : Runs B (App q f x') v) : Runs B (App q f x) v := by
  obtain ⟨_, s, -⟩ := rx
  exact .steps (Steps.app_x vf l s) r

-- the function of an application runs first
private theorem run_f (rf : Runs B f f') (r : Runs B (App q f' x) v) : Runs B (App q f x) v := by
  obtain ⟨_, s, -⟩ := rf
  exact .steps (Steps.app_f s) r

-- a call on one argument, which runs first
private theorem run1 (hk : Book.get B k = some d) (l1 : q1.live = true) (r1 : Runs B x1 v1)
    (w0 : walk B d.v [] [] = some none)
    (w : walk B d.v [] [(q1, v1)] = some (some u)) (r : Runs B u v) :
    Runs B (App q1 (Ref k) x1) v := by
  obtain ⟨_, _, h1⟩ := id r1
  exact run_x (value_part (xs := []) hk .nil w0) l1 r1
    (run_call (xs := [(q1, v1)]) hk (.cons (fun _ => h1) .nil) w r)

-- a call on two arguments, which run first
private theorem run2 (hk : Book.get B k = some d) (l1 : q1.live = true) (l2 : q2.live = true)
    (r1 : Runs B x1 v1) (r2 : Runs B x2 v2)
    (w0 : walk B d.v [] [] = some none) (w1 : walk B d.v [] [(q1, v1)] = some none)
    (w : walk B d.v [] [(q1, v1), (q2, v2)] = some (some u)) (r : Runs B u v) :
    Runs B (App q2 (App q1 (Ref k) x1) x2) v := by
  obtain ⟨_, _, h1⟩ := id r1
  obtain ⟨_, _, h2⟩ := id r2
  have p1 : Value B (App q1 (Ref k) v1) :=
    value_part (xs := [(q1, v1)]) hk (.cons (fun _ => h1) .nil) w1
  exact run_f (run_x (value_part (xs := []) hk .nil w0) l1 r1 (.refl p1))
    (run_x p1 l2 r2 (run_call (xs := [(q1, v1), (q2, v2)]) hk
      (.cons (fun _ => h1) (.cons (fun _ => h2) .nil)) w r))

-- a call on three arguments, which run first
private theorem run3 (hk : Book.get B k = some d) (l1 : q1.live = true) (l2 : q2.live = true)
    (l3 : q3.live = true) (r1 : Runs B x1 v1) (r2 : Runs B x2 v2) (r3 : Runs B x3 v3)
    (w0 : walk B d.v [] [] = some none) (w1 : walk B d.v [] [(q1, v1)] = some none)
    (w2 : walk B d.v [] [(q1, v1), (q2, v2)] = some none)
    (w : walk B d.v [] [(q1, v1), (q2, v2), (q3, v3)] = some (some u)) (r : Runs B u v) :
    Runs B (App q3 (App q2 (App q1 (Ref k) x1) x2) x3) v := by
  obtain ⟨_, _, h1⟩ := id r1
  obtain ⟨_, _, h2⟩ := id r2
  obtain ⟨_, _, h3⟩ := id r3
  have p1 : Value B (App q1 (Ref k) v1) :=
    value_part (xs := [(q1, v1)]) hk (.cons (fun _ => h1) .nil) w1
  have p2 : Value B (App q2 (App q1 (Ref k) v1) v2) :=
    value_part (xs := [(q1, v1), (q2, v2)]) hk (.cons (fun _ => h1) (.cons (fun _ => h2) .nil)) w2
  exact run_f (run_f (run_x (value_part (xs := []) hk .nil w0) l1 r1 (.refl p1))
    (run_x p1 l2 r2 (.refl p2)))
    (run_x p2 l3 r3 (run_call (xs := [(q1, v1), (q2, v2), (q3, v3)]) hk
      (.cons (fun _ => h1) (.cons (fun _ => h2) (.cons (fun _ => h3) .nil))) w r))

-- a pair at quantity 1 runs field by field
private theorem run_tup (ra : Runs B a a') (rb : Runs B b b') : Runs B (Tup Q1 a b) (Tup Q1 a' b') := by
  obtain ⟨n, s, va⟩ := ra
  obtain ⟨m, t, vb⟩ := rb
  have s' : Steps B n (Tup Q1 a b) (Tup Q1 a' b) := by
    clear t; induction s with
    | refl => exact .refl
    | step e _ ih => exact .step (.tup_a rfl e) (ih va)
  have t' : Steps B m (Tup Q1 a' b) (Tup Q1 a' b') := by
    clear s s'; induction t with
    | refl => exact .refl
    | step e _ ih => exact .step (.tup_b (fun _ => va) e) (ih vb)
  exact ⟨_, s'.trans t', .tup (fun _ => va) vb⟩

-- the comparison of two words, as Word.cmp makes it from the top bit down
def wc : Nat → Nat → Nat → Ordering
  | 0, _, _ => .eq
  | n + 1, v, w =>
    match wc n (v / 2) (w / 2) with
    | .lt => .lt
    | .eq => compare (v % 2) (w % 2)
    | .gt => .gt

-- the form of a Cmp
def cmpForm : Ordering → Term
  | .lt => ctor "LT" []
  | .eq => ctor "EQ" []
  | .gt => ctor "GT" []

-- a Cmp form is a value
theorem value_cmp : Value B (cmpForm o) := by cases o <;> exact value_ctor nofun

-- two words compare equal when they are equal modulo 2 ^ n
private theorem wc_eq : wc n v w = .eq ↔ v % 2 ^ n = w % 2 ^ n := by
  induction n generalizing v w with
  | zero => simp [wc, Nat.mod_one]
  | succ n ih =>
    have ev : v % 2 ^ (n + 1) = v % 2 + 2 * (v / 2 % 2 ^ n) := by rw [Nat.pow_succ', Nat.mod_mul]
    have ew : w % 2 ^ (n + 1) = w % 2 + 2 * (w / 2 % 2 ^ n) := by rw [Nat.pow_succ', Nat.mod_mul]
    have hc : compare (v % 2) (w % 2) = .eq ↔ v % 2 = w % 2 := Nat.compare_eq_eq
    rw [ev, ew]
    simp only [wc]
    split <;> rename_i h
    · have := mt (ih (v := v / 2) (w := w / 2)).2 (by simp [h])
      simp only [reduceCtorEq, false_iff]; omega
    · rw [hc]; have := (ih (v := v / 2) (w := w / 2)).1 h; omega
    · have := mt (ih (v := v / 2) (w := w / 2)).2 (by simp [h])
      simp only [reduceCtorEq, false_iff]; omega

-- the form of a word's lowest bit
abbrev bitForm (v : Nat) : Term := ctor (if v % 2 = 1 then "True" else "False") []

-- Bool.cmp compares two bits
theorem bool_cmp (h : Contains B evalVersion) :
    Runs B (App Q1 (App Q1 (Ref "Bool.cmp") (bitForm v)) (bitForm w))
      (cmpForm (compare (v % 2) (w % 2))) := by
  have hk : Book.get B "Bool.cmp" = some «evalVersion.Bool.cmp» := h «evalVersion.Bool.cmp» (by simp [evalVersion])
  rcases Nat.mod_two_eq_zero_or_one v with hv | hv <;>
  rcases Nat.mod_two_eq_zero_or_one w with hw | hw <;>
  exact run_call (xs := [(Q1, _), (Q1, _)]) hk
    (.cons (fun _ => value_ctor nofun) (.cons (fun _ => value_ctor nofun) .nil))
    (by simp [walk, «evalVersion.Bool.cmp», hv, hw, ctor, cmpForm, takes, Quan.live, Quan.fld, sub, spine, compare, compareOfLessAndEq])
    (.refl value_cmp)

-- Word.cmp compares two words of n bits
theorem word_cmp (h : Contains B evalVersion) :
    Runs B (App Q1 (App Q1 (App Q1 (Ref "Word.cmp") (Form.nat n)) (bits n v)) (bits n w))
      (cmpForm (wc n v w)) := by
  have hk : Book.get B "Word.cmp" = some «evalVersion.Word.cmp» := h «evalVersion.Word.cmp» (by simp [evalVersion])
  have hf : Book.get B "Word.cmp.fin" = some «evalVersion.Word.cmp.fin» := h «evalVersion.Word.cmp.fin» (by simp [evalVersion])
  induction n generalizing v w with
  | zero =>
    exact run_call (xs := [(Q1, _), (Q1, _), (Q1, _)]) hk
      (.cons (fun _ => value_nat) (.cons (fun _ => value_bits) (.cons (fun _ => value_bits) .nil)))
      (by simp [walk, «evalVersion.Word.cmp», Form.nat, bits, ctor, cmpForm, wc, takes, Quan.live, Quan.fld, sub, spine, bindsAt])
      (.refl value_cmp)
  | succ n ih =>
    refine run_call (xs := [(Q1, _), (Q1, _), (Q1, _)]) hk
      (u := App Q1 (App Q1 (App Q1 (Ref "Word.cmp.fin") (bitForm v)) (bitForm w))
        (App Q1 (App Q1 (App Q1 (Ref "Word.cmp") (Form.nat n)) (bits n (v / 2))) (bits n (w / 2))))
      (.cons (fun _ => value_nat) (.cons (fun _ => value_bits) (.cons (fun _ => value_bits) .nil)))
      ?_ ?_
    · simp [walk, «evalVersion.Word.cmp», Form.nat, bits, ctor, takes, Quan.live, Quan.fld, sub, spine, bindsAt, Env.sub, data_iff.2 data_nat, data_iff.2 data_bits]
    · have vs : Values B [(Q1, bitForm v), (Q1, bitForm w)] :=
        .cons (fun _ => value_ctor nofun) (.cons (fun _ => value_ctor nofun) .nil)
      refine run_x (value_part (xs := [(Q1, _), (Q1, _)]) hf vs
        (by simp [walk, «evalVersion.Word.cmp.fin», ctor, takes, bindsAt])) rfl ih ?_
      have vs3 : Values B [(Q1, bitForm v), (Q1, bitForm w), (Q1, cmpForm (wc n (v / 2) (w / 2)))] :=
        .cons (fun _ => value_ctor nofun) (.cons (fun _ => value_ctor nofun)
          (.cons (fun _ => value_cmp) .nil))
      revert vs3
      cases ho : wc n (v / 2) (w / 2) <;> intro vs3
      · exact run_call (xs := [(Q1, _), (Q1, _), (Q1, _)]) hf vs3 (u := cmpForm .lt)
          (by simp [walk, «evalVersion.Word.cmp.fin», ctor, cmpForm, takes, bindsAt, data, Quan.live, Quan.fld, sub, spine])
          (by simp only [wc, ho]; exact .refl value_cmp)
      · exact run_call (xs := [(Q1, _), (Q1, _), (Q1, _)]) hf vs3
          (u := App Q1 (App Q1 (Ref "Bool.cmp") (bitForm v)) (bitForm w))
          (by simp [walk, «evalVersion.Word.cmp.fin», ctor, cmpForm, takes, bindsAt, data, Quan.live, Quan.fld, sub, spine, Env.sub])
          (by simp only [wc, ho]; exact bool_cmp h)
      · exact run_call (xs := [(Q1, _), (Q1, _), (Q1, _)]) hf vs3 (u := cmpForm .gt)
          (by simp [walk, «evalVersion.Word.cmp.fin», ctor, cmpForm, takes, bindsAt, data, Quan.live, Quan.fld, sub, spine])
          (by simp only [wc, ho]; exact .refl value_cmp)

-- Byte.is_eq says whether two bytes are equal
private theorem byte_is_eq (h : Contains B evalVersion) :
    Runs B (App Q1 (App Q1 (Ref "Byte.is_eq") (byte x)) (byte y)) (Form.bool (x == y)) := by
  have hk : Book.get B "Byte.is_eq" = some «evalVersion.Byte.is_eq» := h «evalVersion.Byte.is_eq» (by simp [evalVersion])
  have he : Book.get B "Cmp.is_eq" = some «evalVersion.Cmp.is_eq» := h «evalVersion.Cmp.is_eq» (by simp [evalVersion])
  have vs : Values B [(Q1, byte x), (Q1, byte y)] :=
    .cons (fun _ => value_byte) (.cons (fun _ => value_byte) .nil)
  refine run_call (xs := [(Q1, _), (Q1, _)]) hk vs
    (u := App Q1 (Ref "Cmp.is_eq") (App Q1 (App Q1 (App Q1 (Ref "Word.cmp") (Form.nat 8)) (byte x)) (byte y)))
    (by simp [walk, «evalVersion.Byte.is_eq», takes, bindsAt, data_iff.2 data_byte, Quan.live, sub, spine, Env.sub,
      Form.nat, ctor]) ?_
  have rc : Runs B (App Q1 (App Q1 (App Q1 (Ref "Word.cmp") (Form.nat 8)) (byte x)) (byte y))
      (cmpForm (wc 8 x.toNat y.toNat)) := word_cmp h
  have hxy : (x == y) = (wc 8 x.toNat y.toNat == .eq) := by
    have := wc_eq (n := 8) (v := x.toNat) (w := y.toNat)
    rw [Nat.mod_eq_of_lt x.toNat_lt, Nat.mod_eq_of_lt y.toNat_lt] at this
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, this, UInt8.toNat_inj]
  rw [hxy]
  refine run_x (value_part (xs := []) he .nil (by simp [walk, «evalVersion.Cmp.is_eq», takes])) rfl rc ?_
  cases wc 8 x.toNat y.toNat <;>
  exact run_call (xs := [(Q1, _)]) he (.cons (fun _ => value_cmp) .nil)
    (by simp [walk, «evalVersion.Cmp.is_eq», cmpForm, ctor, takes, bindsAt, Quan.live, Quan.fld, sub, spine, Form.bool])
    (.refl value_bool)

-- Bool.and on its first Bool waits for the second
private theorem value_and (h : Contains B evalVersion) :
    Value B (App Q1 (Ref "Bool.and") (Form.bool b)) := by
  have hk : Book.get B "Bool.and" = some «evalVersion.Bool.and» := h «evalVersion.Bool.and» (by simp [evalVersion])
  cases b <;> exact value_part (xs := [(Q1, _)]) hk (.cons (fun _ => value_bool) .nil)
    (by simp [walk, «evalVersion.Bool.and», Form.bool, ctor, takes, Quan.live, Quan.fld])

-- Name.is_eq says whether two lists of bytes are equal
private theorem name_is_eq_bytes (h : Contains B evalVersion) :
    Runs B (App Q1 (App Q1 (Ref "Name.is_eq") (bytes xs)) (bytes ys)) (Form.bool (xs == ys)) := by
  have hk : Book.get B "Name.is_eq" = some «evalVersion.Name.is_eq» := h «evalVersion.Name.is_eq» (by simp [evalVersion])
  have ha : Book.get B "Bool.and" = some «evalVersion.Bool.and» := h «evalVersion.Bool.and» (by simp [evalVersion])
  have vs : Values B [(Q1, bytes xs), (Q1, bytes ys)] :=
    .cons (fun _ => value_bytes) (.cons (fun _ => value_bytes) .nil)
  induction xs generalizing ys with
  | nil =>
    cases ys <;>
    exact run_call (xs := [(Q1, _), (Q1, _)]) hk vs
      (by simp [walk, «evalVersion.Name.is_eq», bytes, list, ctor, takes, bindsAt, Quan.live, Quan.fld, sub, spine, Form.bool])
      (.refl value_bool)
  | cons x xs ih =>
    cases ys with
    | nil =>
      exact run_call (xs := [(Q1, _), (Q1, _)]) hk vs
        (by simp [walk, «evalVersion.Name.is_eq», bytes, list, ctor, takes, bindsAt, Quan.live, Quan.fld, sub, spine, Form.bool])
        (.refl value_bool)
    | cons y ys =>
      refine run_call (xs := [(Q1, _), (Q1, _)]) hk vs
        (u := App Q1 (App Q1 (Ref "Bool.and") (App Q1 (App Q1 (Ref "Byte.is_eq") (byte x)) (byte y)))
          (App Q1 (App Q1 (Ref "Name.is_eq") (bytes xs)) (bytes ys)))
        (by simp [walk, «evalVersion.Name.is_eq», bytes, list, ctor, takes, bindsAt, Quan.live, Quan.fld, sub, spine, Env.sub]) ?_
      rw [List.cons_beq_cons]
      refine run_f (run_x (value_part (xs := []) ha .nil (by simp [walk, «evalVersion.Bool.and», takes]))
        rfl (byte_is_eq h) (.refl (value_and h))) ?_
      exact run_x (value_and h) rfl
        (ih (.cons (fun _ => value_bytes) (.cons (fun _ => value_bytes) .nil))) (and_version h)

theorem name_is_eq_version (h : Contains B evalVersion) :
    Runs B (spine (Ref "Name.is_eq") [(Q1, Form.name a), (Q1, Form.name b)]) (Form.bool (a == b)) := by
  have e : (a == b) = (a.toUTF8.toList == b.toUTF8.toList) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
    exact ⟨fun e => e ▸ rfl, fun e => name_inj (by simp only [Form.name, e])⟩
  rw [e]
  exact name_is_eq_bytes h

-- the form of a def is a value
private theorem value_defn : Value B (Form.defn d) :=
  value_ctor (by simpa [Form.name] using ⟨value_bytes, value_term, value_term, value_bool⟩)

theorem get_version (h : Contains B evalVersion) :
    Runs B (spine (Ref "Book.get") [(Q1, Form.defs ds), (Q2, Form.name k)])
      (Form.maybe Form.defn (ds.find? (·.k == k))) := by
  have hk : Book.get B "Book.get" = some «evalVersion.Book.get» := h «evalVersion.Book.get» (by simp [evalVersion])
  have hi : Book.get B "Book.get.if" = some «evalVersion.Book.get.if» := h «evalVersion.Book.get.if» (by simp [evalVersion])
  have dn : ∀ k, data (Form.name k) = true := fun _ => data_iff.2 data_bytes
  have vs : Values B [(Q1, Form.defs ds), (Q2, Form.name k)] :=
    .cons (fun _ => value_defs) (.cons (fun _ => value_bytes) .nil)
  induction ds with
  | nil =>
    exact run_call (xs := [(Q1, _), (Q2, _)]) hk vs
      (by simp [walk, «evalVersion.Book.get», Form.defs, list, ctor, takes, bindsAt, dn, Quan.live, Quan.fld, sub, spine, Form.maybe])
      (.refl (value_maybe (fun _ => value_defn)))
  | cons d ds ih =>
    refine run_call (xs := [(Q1, _), (Q2, _)]) hk vs
      (u := App Q1 (App Q1 (App Q1 (Ref "Book.get.if")
          (App Q1 (App Q1 (Ref "Name.is_eq") (Form.name d.k)) (Form.name k))) (Form.defn d))
        (App Q2 (App Q1 (Ref "Book.get") (Form.defs ds)) (Form.name k)))
      (by simp [walk, «evalVersion.Book.get», Form.defs, Form.defn, list, ctor, takes, bindsAt, dn, Quan.live, Quan.fld, sub, spine, Env.sub]) ?_
    have r1 := name_is_eq_version (a := d.k) (b := k) h
    have r3 := ih (.cons (fun _ => value_defs) (.cons (fun _ => value_bytes) .nil))
    revert r1
    cases hb : (d.k == k) <;> intro r1
    · refine run3 hi rfl rfl rfl r1 (.refl value_defn) r3
        (by simp [walk, «evalVersion.Book.get.if», takes])
        (by simp [walk, «evalVersion.Book.get.if», Form.bool, ctor, takes, Quan.live, Quan.fld])
        (by simp [walk, «evalVersion.Book.get.if», Form.bool, ctor, takes, bindsAt, Quan.live, Quan.fld])
        (by simp [walk, «evalVersion.Book.get.if», Form.bool, ctor, takes, bindsAt, Quan.live, Quan.fld, sub, spine, Env.sub]; rfl) ?_
      simp only [List.find?_cons, hb]
      exact .refl (value_maybe (fun _ => value_defn))
    · refine run3 hi rfl rfl rfl r1 (.refl value_defn) r3
        (by simp [walk, «evalVersion.Book.get.if», takes])
        (by simp [walk, «evalVersion.Book.get.if», Form.bool, ctor, takes, Quan.live, Quan.fld])
        (by simp [walk, «evalVersion.Book.get.if», Form.bool, ctor, takes, bindsAt, Quan.live, Quan.fld])
        (u := Form.some (Form.defn d))
        (by simp [walk, «evalVersion.Book.get.if», Form.bool, Form.some, ctor, takes, bindsAt, Quan.live, Quan.fld, sub, spine, Env.sub]) ?_
      simp only [List.find?_cons, hb, Form.maybe]
      exact .refl (value_ctor (by simp [value_defn]))

-- the quantity a label names, as Quan.read reads it
private def readQ (k : String) : Option Quan :=
  if k == "Q0" then some Q0 else if k == "Q1" then some Q1 else if k == "Q2" then some Q2 else none

-- the least of two quantities, as Quan.min
private def qmn : Quan → Quan → Quan
  | Q2, r => r
  | r, Q2 => r
  | Q0, _ => Q0
  | _, Q0 => Q0
  | _, _ => Q1

-- the label of a quantity, as Quan.name
private def qname : Quan → String
  | Q0 => "Q0"
  | Q1 => "Q1"
  | Q2 => "Q2"

-- the meet of two read labels, as Eval.meet.of
private def mo : Option Quan → Option Quan → Option Term
  | some p, some q => some (Lab (qname (qmn p q)))
  | _, _ => none

-- the model gives Interp's meet
private theorem mo_meet : mo (readQ i) (readQ j) = meet (Lab i) (Lab j) := by
  by_cases hi : i ∈ QS
  · by_cases hj : j ∈ QS
    · simp only [QS, List.mem_cons, List.not_mem_nil, or_false] at hi hj
      rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;> rfl
    · have : readQ j = none := by
        simp only [QS, List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
        simp [readQ, hj]
      simp [this, mo, meet, hj]
  · have : readQ i = none := by
      simp only [QS, List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
      simp [readQ, hi]
    simp [this, mo, meet, hi]

-- the bytes of the labels Q0, Q1 and Q2
private theorem name_q : Form.name "Q0" = bytes [81, 48] ∧ Form.name "Q1" = bytes [81, 49] ∧
    Form.name "Q2" = bytes [81, 50] := by
  refine ⟨?_, ?_, ?_⟩ <;> unfold Form.name <;> congr 1
  · rw [show "Q0" = String.ofList ['Q', '0'] from rfl]
    simp only [String.toUTF8, String.toByteArray_ofList, ByteArray.toList, toList_loop,
      List.utf8Encode, List.toList_data_toByteArray]
    decide
  · rw [show "Q1" = String.ofList ['Q', '1'] from rfl]
    simp only [String.toUTF8, String.toByteArray_ofList, ByteArray.toList, toList_loop,
      List.utf8Encode, List.toList_data_toByteArray]
    decide
  · rw [show "Q2" = String.ofList ['Q', '2'] from rfl]
    simp only [String.toUTF8, String.toByteArray_ofList, ByteArray.toList, toList_loop,
      List.utf8Encode, List.toList_data_toByteArray]
    decide

-- Word.low gives the low n bits of a word of n + m bits
private theorem word_low (h : Contains B evalVersion) :
    Runs B (App Q1 (App Q1 (App Q1 (Ref "Word.low") (Form.nat n)) (Form.nat m)) (bits (n + m) v))
      (bits n v) := by
  have hk : Book.get B "Word.low" = some «evalVersion.Word.low» := h «evalVersion.Word.low» (by simp [evalVersion])
  have vs : Values B [(Q1, Form.nat n), (Q1, Form.nat m), (Q1, bits (n + m) v)] :=
    .cons (fun _ => value_nat) (.cons (fun _ => value_nat) (.cons (fun _ => value_bits) .nil))
  induction n generalizing v with
  | zero =>
    exact run_call (xs := [(Q1, _), (Q1, _), (Q1, _)]) hk vs
      (by simp [walk, «evalVersion.Word.low», Form.nat, bits, ctor, takes, Quan.live, Quan.fld, sub, spine, bindsAt])
      (.refl value_bits)
  | succ n ih =>
    rw [show n + 1 + m = n + m + 1 by omega] at vs ⊢
    refine run_call (xs := [(Q1, _), (Q1, _), (Q1, _)]) hk vs
      (u := ctor "WCon" [bitForm v,
        App Q1 (App Q1 (App Q1 (Ref "Word.low") (Form.nat n)) (Form.nat m)) (bits (n + m) (v / 2))])
      (by simp [walk, «evalVersion.Word.low», Form.nat, bits, ctor, takes, Quan.live, Quan.fld, sub, spine, bindsAt,
        Env.sub, data_iff.2 data_nat, data_iff.2 data_bits]) ?_
    simp only [bits, ctor, List.foldr]
    exact run_tup (.refl .lab) (run_tup (.refl (.tup (fun _ => .lab) .lab))
      (run_tup (ih (.cons (fun _ => value_nat) (.cons (fun _ => value_nat) (.cons (fun _ => value_bits) .nil))))
        (.refl .lab)))

-- Byte.from_u32 gives the low byte of a U32
theorem from_u32_run (h : Contains B evalVersion) (r : Runs B x (ctor "U32" [bits 32 v])) :
    Runs B (App Q1 (Ref "Byte.from_u32") x) (bits 8 v) := by
  have hk : Book.get B "Byte.from_u32" = some «evalVersion.Byte.from_u32» :=
    h «evalVersion.Byte.from_u32» (by simp [evalVersion])
  have vu : Value B (ctor "U32" [bits 32 v]) := value_ctor (by simpa using value_bits)
  refine run_x (value_part (xs := []) hk .nil (by simp [walk, «evalVersion.Byte.from_u32», takes])) rfl r ?_
  exact run_call (xs := [(Q1, _)]) hk (.cons (fun _ => vu) .nil)
    (u := App Q1 (App Q1 (App Q1 (Ref "Word.low") (Form.nat 8)) (Form.nat 24)) (bits (8 + 24) v))
    (by simp [walk, «evalVersion.Byte.from_u32», Form.nat, ctor, takes, Quan.live, Quan.fld, sub, spine, bindsAt,
      Env.sub, data_iff.2 data_bits])
    (word_low h)

-- Byte.from_u32 on the def k
abbrev fromLit (k : String) : Term := App Q1 (Ref "Byte.from_u32") (Ref k)

-- the byte of a def of the version whose term is the U32 c
private theorem lit_byte (h : Contains B evalVersion) (hd : d ∈ evalVersion)
    (w : walk B d.v [] [] = some (some (ctor "U32" [bits 32 c]))) :
    Runs B (fromLit d.k) (bits 8 c) :=
  from_u32_run h (run_call (xs := []) (h d hd) .nil w (.refl (value_ctor (by simpa using value_bits))))

-- a list literal of two bytes runs to its bytes
private theorem lit_run (r1 : Runs B x1 (byte c1)) (r2 : Runs B x2 (byte c2)) :
    Runs B (Tup Q1 (Lab "Con") (Tup Q1 x1 (Tup Q1 (Tup Q1 (Lab "Con") (Tup Q1 x2
      (Tup Q1 (Tup Q1 (Lab "Nil") (Lab "()")) (Lab "()")))) (Lab "()")))) (bytes [c1, c2]) := by
  simp only [bytes, List.map, list, ctor, List.foldr]
  exact run_tup (.refl .lab) (run_tup r1 (run_tup (run_tup (.refl .lab) (run_tup r2
    (run_tup (.refl (.tup (fun _ => .lab) .lab)) (.refl .lab)))) (.refl .lab)))

-- the list literals of Q0, Q1 and Q2 run to their names
private theorem lits (h : Contains B evalVersion) :
    Runs B (Tup Q1 (Lab "Con") (Tup Q1 (fromLit "U32.lit81") (Tup Q1 (Tup Q1 (Lab "Con") (Tup Q1 (fromLit "U32.lit48")
      (Tup Q1 (Tup Q1 (Lab "Nil") (Lab "()")) (Lab "()")))) (Lab "()")))) (Form.name "Q0") ∧
    Runs B (Tup Q1 (Lab "Con") (Tup Q1 (fromLit "U32.lit81") (Tup Q1 (Tup Q1 (Lab "Con") (Tup Q1 (fromLit "U32.lit49")
      (Tup Q1 (Tup Q1 (Lab "Nil") (Lab "()")) (Lab "()")))) (Lab "()")))) (Form.name "Q1") ∧
    Runs B (Tup Q1 (Lab "Con") (Tup Q1 (fromLit "U32.lit81") (Tup Q1 (Tup Q1 (Lab "Con") (Tup Q1 (fromLit "U32.lit50")
      (Tup Q1 (Tup Q1 (Lab "Nil") (Lab "()")) (Lab "()")))) (Lab "()")))) (Form.name "Q2") := by
  have l81 : Runs B (fromLit "U32.lit81") (byte 81) := lit_byte (d := «evalVersion.U32.lit81») h
    (by simp [evalVersion]) (by simp [walk, «evalVersion.U32.lit81», takes, sub, spine, bits, ctor])
  have l48 : Runs B (fromLit "U32.lit48") (byte 48) := lit_byte (d := «evalVersion.U32.lit48») h
    (by simp [evalVersion]) (by simp [walk, «evalVersion.U32.lit48», takes, sub, spine, bits, ctor])
  have l49 : Runs B (fromLit "U32.lit49") (byte 49) := lit_byte (d := «evalVersion.U32.lit49») h
    (by simp [evalVersion]) (by simp [walk, «evalVersion.U32.lit49», takes, sub, spine, bits, ctor])
  have l50 : Runs B (fromLit "U32.lit50") (byte 50) := lit_byte (d := «evalVersion.U32.lit50») h
    (by simp [evalVersion]) (by simp [walk, «evalVersion.U32.lit50», takes, sub, spine, bits, ctor])
  rw [name_q.1, name_q.2.1, name_q.2.2]
  exact ⟨lit_run l81 l48, lit_run l81 l49, lit_run l81 l50⟩

-- Name.is_eq on a name waits for the second
private theorem value_is_eq (h : Contains B evalVersion) :
    Value B (App Q1 (Ref "Name.is_eq") (Form.name a)) := by
  have hk : Book.get B "Name.is_eq" = some «evalVersion.Name.is_eq» := h «evalVersion.Name.is_eq» (by simp [evalVersion])
  unfold Form.name
  cases a.toUTF8.toList <;>
  exact value_part (xs := [(Q1, _)]) hk (.cons (fun _ => value_bytes) .nil)
    (by simp [walk, «evalVersion.Name.is_eq», bytes, list, ctor, takes, bindsAt, Quan.live, Quan.fld])

-- Quan.read.if picks its quantity when its Bool is True
private theorem read_if (h : Contains B evalVersion) (r1 : Runs B x (Form.bool b))
    (r3 : Runs B y (Form.maybe Form.quan o)) :
    Runs B (App Q1 (App Q1 (App Q1 (Ref "Quan.read.if") x) (Form.quan q)) y)
      (Form.maybe Form.quan (if b then some q else o)) := by
  have hk : Book.get B "Quan.read.if" = some «evalVersion.Quan.read.if» := h «evalVersion.Quan.read.if» (by simp [evalVersion])
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact run3 hk rfl rfl rfl r1 (.refl value_quan) r3
      (by simp [walk, «evalVersion.Quan.read.if», takes])
      (by simp [walk, «evalVersion.Quan.read.if», Form.bool, ctor, takes, Quan.live, Quan.fld])
      (by simp [walk, «evalVersion.Quan.read.if», Form.bool, ctor, takes, bindsAt, Quan.live, Quan.fld])
      (by simp [walk, «evalVersion.Quan.read.if», Form.bool, ctor, takes, bindsAt, Quan.live, Quan.fld, sub, spine, Env.sub])
      (.refl (value_maybe (fun _ => value_quan)))
  · exact run3 hk rfl rfl rfl r1 (.refl value_quan) r3
      (by simp [walk, «evalVersion.Quan.read.if», takes])
      (by simp [walk, «evalVersion.Quan.read.if», Form.bool, ctor, takes, Quan.live, Quan.fld])
      (by simp [walk, «evalVersion.Quan.read.if», Form.bool, ctor, takes, bindsAt, Quan.live, Quan.fld])
      (u := Form.some (Form.quan q))
      (by simp [walk, «evalVersion.Quan.read.if», Form.bool, Form.some, ctor, takes, bindsAt, Quan.live, Quan.fld, sub, spine, Env.sub])
      (.refl (value_maybe (f := Form.quan) (o := some q) (fun _ => value_quan)))

-- Quan.name gives the label of a quantity
private theorem qname_run (h : Contains B evalVersion) (r : Runs B x (Form.quan q)) :
    Runs B (App Q1 (Ref "Quan.name") x) (Form.name (qname q)) := by
  have hk : Book.get B "Quan.name" = some «evalVersion.Quan.name» := h «evalVersion.Quan.name» (by simp [evalVersion])
  obtain ⟨l0, l1, l2⟩ := lits h
  cases q
  · exact run1 hk rfl r (by simp [walk, «evalVersion.Quan.name», takes])
      (by simp [walk, «evalVersion.Quan.name», Form.quan, ctor, takes, Quan.live, Quan.fld, sub, spine]) l0
  · exact run1 hk rfl r (by simp [walk, «evalVersion.Quan.name», takes])
      (by simp [walk, «evalVersion.Quan.name», Form.quan, ctor, takes, Quan.live, Quan.fld, sub, spine]) l1
  · exact run1 hk rfl r (by simp [walk, «evalVersion.Quan.name», takes])
      (by simp [walk, «evalVersion.Quan.name», Form.quan, ctor, takes, Quan.live, Quan.fld, sub, spine]) l2

-- Quan.read reads a label
private theorem read_run (h : Contains B evalVersion) :
    Runs B (App Q2 (Ref "Quan.read") (Form.name k)) (Form.maybe Form.quan (readQ k)) := by
  have hk : Book.get B "Quan.read" = some «evalVersion.Quan.read» := h «evalVersion.Quan.read» (by simp [evalVersion])
  have dn : data (Form.name k) = true := data_iff.2 data_bytes
  have l0 := qname_run (q := Q0) h (.refl value_quan)
  have l1 := qname_run (q := Q1) h (.refl value_quan)
  have l2 := qname_run (q := Q2) h (.refl value_quan)
  refine run_call (xs := [(Q2, _)]) hk (.cons (fun _ => value_bytes) .nil)
    (by simp [walk, «evalVersion.Quan.read», takes, bindsAt, dn, Quan.live, sub, spine, Env.sub]; rfl) ?_
  unfold readQ
  exact read_if (q := Q0) h (run_x (value_is_eq h) rfl l0 (name_is_eq_version (a := k) (b := "Q0") h))
    (read_if (q := Q1) h (run_x (value_is_eq h) rfl l1 (name_is_eq_version (a := k) (b := "Q1") h))
      (read_if (q := Q2) h (run_x (value_is_eq h) rfl l2 (name_is_eq_version (a := k) (b := "Q2") h))
        (.refl (value_maybe (f := Form.quan) (o := none) (fun _ => value_quan)))))

-- Quan.min gives the least of two quantities
private theorem min_run (h : Contains B evalVersion) :
    Runs B (App Q1 (App Q1 (Ref "Quan.min") (Form.quan p)) (Form.quan q)) (Form.quan (qmn p q)) := by
  have hk : Book.get B "Quan.min" = some «evalVersion.Quan.min» := h «evalVersion.Quan.min» (by simp [evalVersion])
  cases p <;> cases q <;>
  exact run_call (xs := [(Q1, _), (Q1, _)]) hk
    (.cons (fun _ => value_quan) (.cons (fun _ => value_quan) .nil))
    (by simp [walk, «evalVersion.Quan.min», Form.quan, qmn, ctor, takes, bindsAt, Quan.live, Quan.fld, sub, spine, Env.sub])
    (.refl value_quan)

-- Eval.meet.of gives the meet of two read labels
private theorem meet_of_run (h : Contains B evalVersion) (r1 : Runs B x (Form.maybe Form.quan o1))
    (r2 : Runs B y (Form.maybe Form.quan o2)) :
    Runs B (App Q1 (App Q1 (Ref "Eval.meet.of") x) y) (Form.maybe Form.term (mo o1 o2)) := by
  have hk : Book.get B "Eval.meet.of" = some «evalVersion.Eval.meet.of» := h «evalVersion.Eval.meet.of» (by simp [evalVersion])
  have hm : Book.get B "Quan.min" = some «evalVersion.Quan.min» := h «evalVersion.Quan.min» (by simp [evalVersion])
  have hn : Book.get B "Quan.name" = some «evalVersion.Quan.name» := h «evalVersion.Quan.name» (by simp [evalVersion])
  cases o1 <;> cases o2
  case some.some p q =>
    refine run2 hk rfl rfl r1 r2 (by simp [walk, «evalVersion.Eval.meet.of», takes])
      (by simp [walk, «evalVersion.Eval.meet.of», Form.maybe, Form.some, ctor, takes, bindsAt, Quan.live, Quan.fld])
      (u := Tup Q1 (Lab "Some") (Tup Q1 (Tup Q1 (Lab "Term.Lab") (Tup Q1
        (App Q1 (Ref "Quan.name") (App Q1 (App Q1 (Ref "Quan.min") (Form.quan p)) (Form.quan q)))
        (Lab "()"))) (Lab "()")))
      (by simp [walk, «evalVersion.Eval.meet.of», Form.maybe, Form.some, ctor, takes, bindsAt, Quan.live, Quan.fld, sub, spine, Env.sub, data_iff.2 data_quan]) ?_
    show Runs B _ (Tup Q1 (Lab "Some") (Tup Q1 (Tup Q1 (Lab "Term.Lab")
      (Tup Q1 (Form.name (qname (qmn p q))) (Lab "()"))) (Lab "()")))
    exact run_tup (.refl .lab) (run_tup (run_tup (.refl .lab)
      (run_tup (qname_run h (min_run h)) (.refl .lab))) (.refl .lab))
  all_goals
    exact run2 hk rfl rfl r1 r2 (by simp [walk, «evalVersion.Eval.meet.of», takes])
      (by simp [walk, «evalVersion.Eval.meet.of», Form.maybe, Form.some, ctor, takes, bindsAt, Quan.live, Quan.fld])
      (u := ctor "None" [])
      (by simp [walk, «evalVersion.Eval.meet.of», Form.maybe, Form.some, ctor, takes, bindsAt, Quan.live, Quan.fld, sub, spine])
      (.refl (value_ctor nofun))

-- Eval.meet on two terms that are not both labels gives None
private theorem meet_none (h : Contains B evalVersion) (hm : meet a b = none)
    (w : walk B «evalVersion.Eval.meet».v [] [(Q1, Form.term a), (Q1, Form.term b)] =
      some (some (ctor "None" []))) :
    Runs B (spine (Ref "Eval.meet") [(Q1, Form.term a), (Q1, Form.term b)])
      (Form.maybe Form.term (meet a b)) := by
  rw [hm]
  exact run_call (h «evalVersion.Eval.meet» (by simp [evalVersion]))
    (.cons (fun _ => value_term) (.cons (fun _ => value_term) .nil)) w (.refl (value_ctor nofun))

theorem meet_version (h : Contains B evalVersion) :
    Runs B (spine (Ref "Eval.meet") [(Q1, Form.term a), (Q1, Form.term b)])
      (Form.maybe Form.term (meet a b)) := by
  have hk : Book.get B "Eval.meet" = some «evalVersion.Eval.meet» := h «evalVersion.Eval.meet» (by simp [evalVersion])
  have ho : Book.get B "Eval.meet.of" = some «evalVersion.Eval.meet.of» := h «evalVersion.Eval.meet.of» (by simp [evalVersion])
  cases a
  case Lab i =>
    cases b
    case Lab j =>
      refine run_call (xs := [(Q1, _), (Q1, _)]) hk
        (.cons (fun _ => value_term) (.cons (fun _ => value_term) .nil))
        (u := App Q1 (App Q1 (Ref "Eval.meet.of") (App Q2 (Ref "Quan.read") (Form.name i)))
          (App Q2 (Ref "Quan.read") (Form.name j)))
        (by simp [walk, «evalVersion.Eval.meet», Form.term, ctor, takes, bindsAt, Quan.live, Quan.fld, sub, spine, Env.sub]) ?_
      rw [← mo_meet]
      exact meet_of_run h (read_run h) (read_run h)
    all_goals exact meet_none h (by rfl) (by simp [walk, «evalVersion.Eval.meet», Form.term, ctor, takes, bindsAt, Quan.live, Quan.fld, sub, spine])
  all_goals exact meet_none h (by rfl) (by simp [walk, «evalVersion.Eval.meet», Form.term, ctor, takes, bindsAt, Quan.live, Quan.fld, sub, spine])

end EvalVersion
