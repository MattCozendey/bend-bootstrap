import Bootstrap.Bytes

-- Book
-- ====
--
-- The Bend data form of the kernel's book (bootstrap/bend/src/compiler),
-- as `bend -o` writes its values, and the Lean writer of INVARIANTS #5, whose
-- tokens Book.read reads back. That Bend file states the tokens. The writer
-- puts each list last to first, as the reader puts each item in front.

open Quan Term

namespace Form

def name (k : String) : Term := bytes k.toUTF8.toList

def nat : Nat → Term
  | 0 => ctor "Zero" []
  | n + 1 => ctor "Succ" [nat n]

def quan : Quan → Term
  | Q0 => ctor "Quan.Q0" []
  | Q1 => ctor "Quan.Q1" []
  | Q2 => ctor "Quan.Q2" []

def bool (b : Bool) : Term := ctor (if b then "True" else "False") []

def term : Term → Term
  | Var i => ctor "Term.Var" [nat i]
  | Ref k => ctor "Term.Ref" [name k]
  | Ann x T => ctor "Term.Ann" [term x, term T]
  | Let q v f => ctor "Term.Let" [quan q, term v, term f]
  | Typ q => ctor "Term.Typ" [term q]
  | Term.Min a b => ctor "Term.Min" [term a, term b]
  | All q A B => ctor "Term.All" [quan q, term A, term B]
  | Lam q f => ctor "Term.Lam" [quan q, term f]
  | App q f x => ctor "Term.App" [quan q, term f, term x]
  | Sig q A B => ctor "Term.Sig" [quan q, term A, term B]
  | Tup q a b => ctor "Term.Tup" [quan q, term a, term b]
  | Prj h => ctor "Term.Prj" [term h]
  | Enu ks => ctor "Term.Enu" [list (ks.map name)]
  | Lab k => ctor "Term.Lab" [name k]
  | Mat k h m => ctor "Term.Mat" [name k, term h, term m]
  | Efq => ctor "Term.Efq" []
  | Eql a b T => ctor "Term.Eql" [term a, term b, term T]
  | Rfl => ctor "Term.Rfl" []
  | Rwt e P f => ctor "Term.Rwt" [term e, term P, term f]

def defn (d : Def) : Term := ctor "Def" [name d.k, term d.T, term d.v, bool d.o]

def defs (ds : List Def) : Term := list (ds.map defn)

def some (x : Term) : Term := ctor "Some" [x]

-- an Option, as Base's Maybe, with f the form of its value
def maybe (f : α → Term) : Option α → Term
  | .some x => some (f x)
  | .none => ctor "None" []

def env (e : Env) : Term := list (e.map term)

def arg : Arg → Term
  | (q, x) => ctor "Arg" [quan q, term x]

def args (xs : List Arg) : Term := list (xs.map arg)

end Form

-- One to one
-- ----------
-- DEFINITION #4: no two terms, defs or books share a data form.

-- a chain of fields that ends in () gives back its fields
private theorem fields_inj {fs fs' : List Term} :
    fs.foldr (Tup Q1) (Lab "()") = fs'.foldr (Tup Q1) (Lab "()") → fs = fs' := by
  induction fs generalizing fs' with
  | nil => cases fs' <;> simp
  | cons f fs ih =>
    cases fs' with
    | nil => simp
    | cons f' fs' => simp only [List.foldr_cons, Tup.injEq]; exact fun h => by rw [h.2.1, ih h.2.2]

-- constructors with equal forms have equal labels and fields
theorem ctor_inj : ctor k fs = ctor k' fs' → k = k' ∧ fs = fs' := by
  intro h
  simp only [ctor, Term.Tup.injEq, Term.Lab.injEq] at h
  exact ⟨h.2.1, fields_inj h.2.2⟩

-- ByteArray.toList.loop puts the bytes from i after the reversed r
theorem toList_loop (bs : ByteArray) (i : Nat) (r : List UInt8) :
    ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
  fun_induction ByteArray.toList.loop bs i r with
  | case1 i r hi ih =>
    rw [ih]
    have hi' : i < bs.data.toList.length := by rw [Array.length_toList]; exact hi
    rw [List.drop_eq_getElem_cons hi']
    simp [ByteArray.get!, hi]
  | case2 i r hi =>
    have hi' : bs.data.toList.length ≤ i := by rw [Array.length_toList]; exact Nat.le_of_not_lt hi
    simp [List.drop_eq_nil_of_le hi']

-- the form of a name, its UTF-8 bytes, says which name it is
theorem name_inj : Form.name a = Form.name b → a = b := by
  intro h
  have h1 := congrArg unbytes h
  simp only [Form.name, unbytes_bytes, Option.some.injEq, ByteArray.toList, toList_loop,
    String.toUTF8, List.reverse_nil, List.nil_append, List.drop_zero] at h1
  exact String.toByteArray_inj.1 (ByteArray.ext (Array.ext' h1))

-- the form of a nat says which nat it is
private theorem nat_inj {a b : Nat} : Form.nat a = Form.nat b → a = b := by
  induction a generalizing b with
  | zero =>
    cases b with
    | zero => intro; rfl
    | succ m => intro h; simp only [Form.nat] at h; have := (ctor_inj h).1; simp at this
  | succ n ih =>
    cases b with
    | zero => intro h; simp only [Form.nat] at h; have := (ctor_inj h).1; simp at this
    | succ m => intro h; have := (ctor_inj h).2; simp at this; exact congrArg (· + 1) (ih this)

-- the form of a quantity says which quantity it is
private theorem quan_inj {a b : Quan} : Form.quan a = Form.quan b → a = b := by
  cases a <;> cases b <;> intro h <;> have := (ctor_inj h).1 <;> simp_all [Form.quan]

-- the form of a bool says which bool it is
private theorem bool_inj {a b : Bool} : Form.bool a = Form.bool b → a = b := by
  cases a <;> cases b <;> intro h <;> have := (ctor_inj h).1 <;> simp_all [Form.bool]

-- the form of a list says which list it is
private theorem list_inj {xs ys : List Term} : list xs = list ys → xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> intro h <;> have := (ctor_inj h).1 <;> simp_all [list]
  | cons x xs ih =>
    cases ys with
    | nil => intro h; have := (ctor_inj h).1; simp_all [list]
    | cons y ys => intro h; have := (ctor_inj h).2; simp at this; rw [this.1, ih this.2]

-- the form of a list of names says which names they are
private theorem names_inj {ks ks' : List String} :
    list (ks.map Form.name) = list (ks'.map Form.name) → ks = ks' :=
  fun h => (List.map_inj_right fun _ _ => name_inj).1 (list_inj h)

-- the form of a term says which term it is
theorem term_inj {a b : Term} : Form.term a = Form.term b → a = b := by
  induction a generalizing b <;> cases b <;> intro h <;> (try rfl) <;> simp only [Form.term] at h <;>
    have ⟨hk, hf⟩ := ctor_inj h <;> (try simp at hk) <;>
    revert hf <;> simp only [List.cons.injEq, and_true, and_imp] <;> intros <;>
    simp only [Term.Var.injEq, Term.Ref.injEq, Term.Ann.injEq, Term.Let.injEq, Term.Typ.injEq,
      Term.Min.injEq, Term.All.injEq, Term.Lam.injEq, Term.App.injEq, Term.Sig.injEq,
      Term.Tup.injEq, Term.Prj.injEq, Term.Enu.injEq, Term.Lab.injEq, Term.Mat.injEq,
      Term.Eql.injEq, Term.Rwt.injEq] <;>
    (try refine ⟨?_, ?_, ?_⟩) <;> (try refine ⟨?_, ?_⟩) <;>
    first
      | rfl
      | exact nat_inj ‹_›
      | exact quan_inj ‹_›
      | exact names_inj ‹_›
      | exact name_inj ‹_›
      | (apply_assumption; assumption)

-- the form of a def says which def it is
theorem defn_inj {d d' : Def} : Form.defn d = Form.defn d' → d = d' := by
  cases d; cases d'
  intro h
  simp only [Form.defn] at h
  have := (ctor_inj h).2
  simp only [List.cons.injEq, and_true] at this
  obtain ⟨hk, hT, hv, ho⟩ := this
  rw [name_inj hk, term_inj hT, term_inj hv, bool_inj ho]

-- the form of a book, the list of its defs, says which book it is
theorem book_inj {a b : Book} : Form.defs a.defs = Form.defs b.defs → a = b := by
  obtain ⟨ds, l, o⟩ := a
  obtain ⟨ds', l', o'⟩ := b
  intro h
  have e : ds = ds' := (List.map_inj_right fun _ _ => defn_inj).1 (list_inj h)
  subst e o o'
  rfl

namespace Write

def tok (tag : Nat) (arg : UInt8 := 0) : List UInt8 := [tag.toUInt8, arg]

def name (k : String) : List UInt8 := tok 5 ++ k.toUTF8.toList.reverse.flatMap (tok 6 ·)

def nat : Nat → List UInt8
  | 0 => tok 3
  | n + 1 => nat n ++ tok 4

def quan : Quan → List UInt8
  | Q0 => tok 0
  | Q1 => tok 1
  | Q2 => tok 2

def bool (b : Bool) : List UInt8 := tok (if b then 10 else 9)

def names (ks : List String) : List UInt8 := tok 7 ++ ks.reverse.flatMap (name · ++ tok 8)

def term : Term → List UInt8
  | Var i => nat i ++ tok 14
  | Ref k => name k ++ tok 15
  | Ann x T => term x ++ term T ++ tok 16
  | Let q v f => quan q ++ term v ++ term f ++ tok 17
  | Typ q => term q ++ tok 18
  | Term.Min a b => term a ++ term b ++ tok 19
  | All q A B => quan q ++ term A ++ term B ++ tok 20
  | Lam q f => quan q ++ term f ++ tok 21
  | App q f x => quan q ++ term f ++ term x ++ tok 22
  | Sig q A B => quan q ++ term A ++ term B ++ tok 23
  | Tup q a b => quan q ++ term a ++ term b ++ tok 24
  | Prj h => term h ++ tok 25
  | Enu ks => names ks ++ tok 26
  | Lab k => name k ++ tok 27
  | Mat k h m => name k ++ term h ++ term m ++ tok 28
  | Efq => tok 29
  | Eql a b T => term a ++ term b ++ term T ++ tok 30
  | Rfl => tok 31
  | Rwt e P f => term e ++ term P ++ term f ++ tok 32

def defn (d : Def) : List UInt8 := name d.k ++ term d.T ++ term d.v ++ bool d.o ++ tok 13

end Write

def write (bk : Book) : List UInt8 :=
  Write.tok 11 ++ bk.defs.reverse.flatMap (Write.defn · ++ Write.tok 12)
