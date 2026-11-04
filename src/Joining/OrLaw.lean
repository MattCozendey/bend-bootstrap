import Joining.Laws

-- OrLaw
-- =====
--
-- exists_conv (Join.lean) for a "there is" part whose property is, for all
-- values of a Data type, an Or of two equations, as no_other_failure states
-- it: the witness, and for each value, the equation of the two that its
-- proof proves. And in_subset, whose property is no equation (Empty).

open Quan Term

set_option linter.unusedSimpArgs false

-- Base's Or and Either, under their names in main.bend's book
def orVersion : List Def := [«trustedVersion.Or», «trustedVersion.Either», «trustedVersion.Either.arms»]

-- a closed typed term whose evaluation is accessible runs to a value it
-- reduces to (as Join.lean's)
private theorem runs_acc' (wt : Book.WellTyped B) (lv : Book.Live B) :
    Acc (fun u t => Eval B t u) t → Typed B [] t A → ∃ v, Runs B t v ∧ Pars B t v := by
  intro hacc
  induction hacc with
  | intro t _ ih =>
    intro ht
    rcases progress B t A wt lv ht with hv | ⟨u, e⟩
    · exact ⟨t, Runs.refl hv, .refl⟩
    · have pu := eval_pars lv.1 e
      obtain ⟨v, r, p⟩ := ih u e (pars_sr wt ht pu)
      exact ⟨v, Runs.step e r, pars_trans pu p⟩

private theorem one_ren : sub (Subst.one v) (ren Nat.succ t) = t := by
  rw [sub_ren]; exact sub_var t

-- Base's Exists A P unfolds to a Σ over the one label "Tuple" (as Join.lean's)
private theorem exists_pars (cl : Book.Closed B)
    (hE : Book.get B "Exists" = some «existsVersion.Exists»)
    (hS : Book.get B "Sigma" = some «existsVersion.Sigma») :
    Pars B (App Q0 (App Q0 (Ref "Exists") A) P)
      (Sig Q1 (Enu ["Tuple"])
        (App Q1
          (App Q0
            (App Q0 (App Q0 (App Q0 (Ref "Sigma.arms") (ren Nat.succ (Lab "Q1"))) (ren Nat.succ (Lab "Q1")))
              (ren Nat.succ A))
            (ren Nat.succ (Lam Q0 (App Q0 (ren Nat.succ P) (Var 0)))))
          (Var 0))) := by
  refine .step (.app (.app (.delta hE (cl _ _ hE)) par_refl) par_refl) ?_
  dsimp only [«existsVersion.Exists»]
  refine .step (.app (.beta par_refl par_refl) par_refl) ?_
  simp only [Term.inst, Term.sub, Subst.one, Subst.up]
  refine .step (.beta par_refl par_refl) ?_
  simp only [Term.inst, Term.sub, Subst.one, Subst.up, sub_succ, one_ren]
  refine .step (.app (.app (.app (.app (.delta hS (cl _ _ hS)) par_refl) par_refl) par_refl) par_refl) ?_
  dsimp only [«existsVersion.Sigma»]
  refine .step (.app (.app (.app (.beta par_refl par_refl) par_refl) par_refl) par_refl) ?_
  simp only [Term.inst, Term.sub, Subst.one, Subst.up]
  refine .step (.app (.app (.beta par_refl par_refl) par_refl) par_refl) ?_
  simp only [Term.inst, Term.sub, Subst.one, Subst.up, sub_succ, one_ren]
  refine .step (.app (.beta par_refl par_refl) par_refl) ?_
  simp only [Term.inst, Term.sub, Subst.one, Subst.up, sub_succ, one_ren]
  refine .step (.beta par_refl par_refl) ?_
  simp only [Term.inst, Term.sub, Subst.one, Subst.up, sub_succ, one_ren]
  exact .refl

-- Sigma.arms at "Tuple" unfolds to the Σ of the two fields (as Join.lean's)
private theorem arms_pars (cl : Book.Closed B)
    (hA : Book.get B "Sigma.arms" = some «existsVersion.Sigma.arms») :
    Pars B (App Q1 (App Q0 (App Q0 (App Q0 (App Q0 (Ref "Sigma.arms") q0) q1) A) P) (Lab "Tuple"))
      (Sig Q1 A (Sig Q1 (App Q0 (ren Nat.succ P) (Var 0)) (Enu ["()"]))) := by
  refine .step (.app (.app (.app (.app (.app (.delta hA (cl _ _ hA)) par_refl) par_refl) par_refl) par_refl) par_refl) ?_
  dsimp only [«existsVersion.Sigma.arms»]
  refine .step (.app (.app (.app (.app (.beta par_refl par_refl) par_refl) par_refl) par_refl) par_refl) ?_
  simp only [Term.inst, Term.sub, Subst.up]
  refine .step (.app (.app (.app (.beta par_refl par_refl) par_refl) par_refl) par_refl) ?_
  simp only [Term.inst, Term.sub, Subst.up, sub_succ]
  refine .step (.app (.app (.beta par_refl par_refl) par_refl) par_refl) ?_
  simp only [Term.inst, Term.sub, Subst.one, Subst.up, sub_succ]
  refine .step (.app (.beta par_refl par_refl) par_refl) ?_
  simp only [Term.inst, Term.sub, Subst.one, Subst.up, sub_succ, one_ren]
  refine .step (.hit par_refl) ?_
  exact .refl

-- Base's Or X Y unfolds to a Σ over Inl and Inr
private theorem or_pars (cl : Book.Closed B) (ho : Contains B orVersion) :
    Pars B (App Q0 (App Q0 (Ref "Or") X) Y)
      (Sig Q1 (Enu ["Inl", "Inr"]) (App Q1 (App Q0 (App Q0 (App Q0 (App Q0 (Ref "Either.arms")
        (Lab "Q1")) (Lab "Q1")) (ren Nat.succ X)) (ren Nat.succ Y)) (Var 0))) := by
  have hO := ho «trustedVersion.Or» (by simp [orVersion])
  have hE := ho «trustedVersion.Either» (by simp [orVersion])
  refine .step (.app (.app (.delta hO (cl _ _ hO)) par_refl) par_refl) ?_
  dsimp only [«trustedVersion.Or»]
  refine .step (.app (.beta par_refl par_refl) par_refl) ?_
  simp only [Term.inst, Term.sub, Subst.one, Subst.up]
  refine .step (.beta par_refl par_refl) ?_
  simp only [Term.inst, Term.sub, Subst.one, Subst.up, sub_succ, one_ren]
  refine .step (.app (.app (.app (.app (.delta hE (cl _ _ hE)) par_refl) par_refl) par_refl) par_refl) ?_
  dsimp only [«trustedVersion.Either»]
  refine .step (.app (.app (.app (.beta par_refl par_refl) par_refl) par_refl) par_refl) ?_
  simp only [Term.inst, Term.sub, Subst.one, Subst.up]
  refine .step (.app (.app (.beta par_refl par_refl) par_refl) par_refl) ?_
  simp only [Term.inst, Term.sub, Subst.one, Subst.up, sub_succ, one_ren]
  refine .step (.app (.beta par_refl par_refl) par_refl) ?_
  simp only [Term.inst, Term.sub, Subst.one, Subst.up, sub_succ, one_ren]
  refine .step (.beta par_refl par_refl) ?_
  simp only [Term.inst, Term.sub, Subst.one, Subst.up, sub_succ, one_ren, Term.ren]
  exact .refl

-- Either.arms at Inl, and at Inr, unfolds to the Σ of its field
private theorem either_pars (cl : Book.Closed B) (ho : Contains B orVersion) :
    Pars B (App Q1 (App Q0 (App Q0 (App Q0 (App Q0 (Ref "Either.arms") q0) q1) X) Y) (Lab "Inl"))
      (Sig Q1 X (Enu ["()"])) ∧
    Pars B (App Q1 (App Q0 (App Q0 (App Q0 (App Q0 (Ref "Either.arms") q0) q1) X) Y) (Lab "Inr"))
      (Sig Q1 Y (Enu ["()"])) := by
  have hA := ho «trustedVersion.Either.arms» (by simp [orVersion])
  constructor <;>
  · refine .step (.app (.app (.app (.app (.app (.delta hA (cl _ _ hA)) par_refl) par_refl) par_refl) par_refl) par_refl) ?_
    dsimp only [«trustedVersion.Either.arms»]
    refine .step (.app (.app (.app (.app (.beta par_refl par_refl) par_refl) par_refl) par_refl) par_refl) ?_
    simp only [Term.inst, Term.sub, Subst.up]
    refine .step (.app (.app (.app (.beta par_refl par_refl) par_refl) par_refl) par_refl) ?_
    simp only [Term.inst, Term.sub, Subst.up, sub_succ]
    refine .step (.app (.app (.beta par_refl par_refl) par_refl) par_refl) ?_
    simp only [Term.inst, Term.sub, Subst.one, Subst.up, sub_succ]
    refine .step (.app (.beta par_refl par_refl) par_refl) ?_
    simp only [Term.inst, Term.sub, Subst.one, Subst.up, sub_succ, one_ren]
    first
      | exact .step (.hit par_refl) .refl
      | exact .step (.miss (by decide) par_refl) (.step (.hit par_refl) .refl)

-- a run keeps a closed, live term closed and live (the kernel's ev)
private theorem steps_live (lv : Book.Live B) (s : Steps B n t u) :
    Term.Closed t → Term.Live B t → Term.Closed u ∧ Term.Live B u := by
  induction s with
  | refl => exact fun hc hl => ⟨hc, hl⟩
  | step e _ ih => exact fun hc hl => ih (pars_closed (eval_pars lv.1 e) hc) (ev lv e (closed_ren hc) hl).1

-- the fields of a closed, live pair at a live quantity are closed and live
private theorem tup_closed_live (hc : Term.Closed (Tup Q1 a b)) (hl : Term.Live B (Tup Q1 a b)) :
    (Term.Closed a ∧ Term.Live B a) ∧ (Term.Closed b ∧ Term.Live B b) := by
  simp only [Term.Live, Term.live, Quan.live, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hl
  have h σ := hc σ
  simp only [Term.sub, Tup.injEq] at h
  exact ⟨⟨fun σ => (h σ).2.1, hl.1⟩, ⟨fun σ => (h σ).2.2, hl.2⟩⟩

-- in a book that --verdict accepts and that holds Base's Exists and Or, a
-- closed, live proof e that there is a y : A such that, for each g : G, x == z
-- or x' == z', for a Data type A, has a witness w: a Data value of type A such
-- that, for each plain g of type G at w, x and z, or x' and z', convert at w
-- and g
theorem exists_all_or_conv (hc : Book.check B = .ok ()) (hk : Contains B existsVersion) (ho : Contains B orVersion)
    (hcl : Term.Closed e) (hl : Term.Live B e)
    (ht : Typed B [] e (App Q0 (App Q0 (Ref "Exists") A)
      (Lam Q0 (All Q2 G (App Q0 (App Q0 (Ref "Or") (Eql x z T)) (Eql x' z' T'))))))
    (hA : Typed B [] A T2) :
    ∃ w, Data w ∧ Typed B [] w A ∧ ∀ g, Plain g → Typed B [] g (Term.inst G w) →
      Conv B (Term.inst (Term.sub (Subst.up (Subst.one w)) x) g) (Term.inst (Term.sub (Subst.up (Subst.one w)) z) g) ∨
      Conv B (Term.inst (Term.sub (Subst.up (Subst.one w)) x') g) (Term.inst (Term.sub (Subst.up (Subst.one w)) z') g) := by
  obtain ⟨wt, lv⟩ := book_check B hc
  have hE := hk «existsVersion.Exists» (by simp [existsVersion])
  have hS := hk «existsVersion.Sigma» (by simp [existsVersion])
  have hR := hk «existsVersion.Sigma.arms» (by simp [existsVersion])
  obtain ⟨v, ⟨_, sv, vv⟩, pv⟩ := runs_acc' wt lv (halts B e lv hcl hl) ht
  have cv := steps_live lv sv hcl hl
  have hv := pars_sr wt ht pv
  -- the pair of the label and the rest
  obtain ⟨a, b, rfl, ha, hb⟩ := canon_sig wt vv hv ⟨_, exists_pars lv.1 hE hS, .refl⟩
  have ⟨va, vb⟩ := value_tup vv
  obtain ⟨k, hk', rfl⟩ := canon_enu wt (va rfl) ha crefl
  simp only [List.mem_singleton] at hk'; subst hk'
  simp only [Term.inst, Term.sub, Subst.one, one_ren] at hb
  -- the pair of the witness and the rest
  obtain ⟨w, b', rfl, hw, hb'⟩ := canon_sig wt vb hb ⟨_, arms_pars lv.1 hR, .refl⟩
  have ⟨vw, vb'⟩ := value_tup vb
  simp only [Term.inst, Term.sub, Subst.one, one_ren] at hb'
  -- the pair of the proof and the unit; the proof is closed and live
  obtain ⟨p, u, rfl, hp, -⟩ := canon_sig wt vb' hb' crefl
  have cp := (tup_closed_live (tup_closed_live (tup_closed_live cv.1 cv.2).2.1 (tup_closed_live cv.1 cv.2).2.2).2.1
    (tup_closed_live (tup_closed_live cv.1 cv.2).2.1 (tup_closed_live cv.1 cv.2).2.2).2.2).1
  -- the proof is a function of each g : G
  have hall : Pars B (App Q0 (Lam Q0 (App Q0 (ren Nat.succ (Lam Q0 (All Q2 G (App Q0 (App Q0 (Ref "Or") (Eql x z T))
      (Eql x' z' T'))))) (Var 0))) w)
      (All Q2 (Term.inst G w) (Term.sub (Subst.up (Subst.one w))
        (App Q0 (App Q0 (Ref "Or") (Eql x z T)) (Eql x' z' T')))) := by
    refine .step (.beta par_refl par_refl) ?_
    simp only [Term.inst, Term.sub, Subst.one, one_ren]
    refine .step (.beta par_refl par_refl) ?_
    exact .refl
  have hp' := Typed.conv hp (.conv ⟨_, hall, .refl⟩)
  refine ⟨w, canon_data wt (vw rfl) hw hA, hw, fun g hg hgt => ?_⟩
  -- its application to g runs to a proof of the Or
  have ht2 := Typed.app hp' hgt
  have cl2 : Term.Closed (App Q2 p g) := fun σ => by simp only [Term.sub, cp.1 σ, hg.sub]
  have ll2 : Term.Live B (App Q2 p g) := live_app.2 ⟨cp.2, fun _ => hg.live⟩
  obtain ⟨v2, ⟨_, _, vv2⟩, pv2⟩ := runs_acc' wt lv (halts B _ lv cl2 ll2) ht2
  have hv2 := pars_sr wt ht2 pv2
  simp only [Term.inst, Term.sub] at hv2
  obtain ⟨l, r, rfl, hl', hr⟩ := canon_sig wt vv2 hv2 ⟨_, or_pars lv.1 ho, .refl⟩
  obtain ⟨vl, vr⟩ := value_tup vv2
  obtain ⟨j, hj, rfl⟩ := canon_enu wt (vl rfl) hl' crefl
  simp only [Term.inst, Term.sub, Subst.one, one_ren] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl
  · obtain ⟨q, u', e, hq, -⟩ := canon_sig wt vr hr ⟨_, (either_pars lv.1 ho).1, .refl⟩
    rw [e] at vr
    obtain ⟨-, c⟩ := canon_eql wt ((value_tup vr).1 rfl) hq crefl
    exact .inl c
  · obtain ⟨q, u', e, hq, -⟩ := canon_sig wt vr hr ⟨_, (either_pars lv.1 ho).2, .refl⟩
    rw [e] at vr
    obtain ⟨-, c⟩ := canon_eql wt ((value_tup vr).1 rfl) hq crefl
    exact .inr c

theorem Trusted.ors (hB : Trusted B) : Contains B orVersion := by
  intro d hd
  simp only [orVersion, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl
  · have := hB.get (d := «trustedVersion.Or») (by simp [trustedVersion])
    simpa [Rename.defn, Rename.term, «trustedVersion.Or»] using this
  · have := hB.get (d := «trustedVersion.Either») (by simp [trustedVersion])
    simpa [Rename.defn, Rename.term, «trustedVersion.Either»] using this
  · have := hB.get (d := «trustedVersion.Either.arms») (by simp [trustedVersion])
    simpa [Rename.defn, Rename.term, «trustedVersion.Either.arms»] using this

-- a closed, live call on closed, live arguments
theorem live_args (hk : Book.get B k = some d) (h : ∀ a ∈ xs, Term.Live B a.2) :
    Term.Live B (spine (Ref k) xs) := by
  refine live_spine.2 ⟨?_, fun a ha _ => h a ha⟩
  obtain ⟨j, hj⟩ := index_of_get hk
  simp [Term.Live, Term.live, called, unspine, hj, index_lt hj]

theorem typed_wasm (hB : Trusted B) (cl : Book.Closed B) :
    Typed B [] (wasmOf f (compileOf p) i m gs) (Ref (impl "Wasm.Outcome")) := by
  have hT := hB.types
  have h1 := Typed.ref (Γ := []) (σ := Var) (hB.get (d := «trustedVersion.Wasm.run») (by simp [trustedVersion]))
  have h2 := Typed.ref (Γ := []) (σ := Var) (hB.get (d := «trustedVersion.Compiler.compile») (by simp [trustedVersion]))
  rw [sub_var] at h1 h2
  simp [Rename.defn, Rename.term, «trustedVersion.Wasm.run», «trustedVersion.Compiler.compile»] at h1 h2
  have hc := Typed.app h2 (typed_bytes hT cl (bs := p))
  simp [Term.inst, Term.sub, Subst.one] at hc
  have := Typed.app (Typed.app (Typed.app (Typed.app h1 (typed_nat hT cl (n := f))) hc)
    (typed_bytes hT cl (bs := i))) (typed_engine hB cl (m := m) (gs := gs))
  simpa [Term.inst, Term.sub, Subst.one, Subst.up, Term.ren, wasmOf, compileOf, spine] using this

theorem typed_outcome (hB : Trusted B) : Typed B [] (Ref (impl "Wasm.Outcome")) T2 := by
  have := Typed.ref (Γ := []) (σ := Var) (hB.get (d := «trustedVersion.Wasm.Outcome») (by simp [trustedVersion]))
  simpa [sub_var, Rename.defn, Rename.term, «trustedVersion.Wasm.Outcome»] using this

-- the law no_other_failure: in one fuel f for all of the engine's answers gs
theorem law_no_other_failure (hc : Book.check B = .ok ()) (hB : Trusted B)
    (hg : Runs B (givesOf p i n) (Form.some (bytes o))) :
    ∃ f, ∀ gs, Runs B (wasmOf f (compileOf p) i m gs) (resultOf o) ∨ Runs B (wasmOf f (compileOf p) i m gs) outOfMemory := by
  have hT := hB.types
  have ⟨wt, lv⟩ := book_check B hc
  have cl := lv.1
  have h0 := hB.law (l := «trustedVersion.Compiler_2f_spec.no_other_failure») (by simp [laws])
  simp [Rename.term, «trustedVersion.Compiler_2f_spec.no_other_failure»] at h0
  have h1 := Typed.app (Typed.app (Typed.app (Typed.app (Typed.app h0 (typed_bytes hT cl (bs := p)))
    (typed_bytes hT cl (bs := i))) (typed_nat hT cl (n := n))) (typed_bytes hT cl (bs := o)))
    (typed_u32' hT cl (m := m))
  simp [Term.inst, Term.sub, Subst.one, Subst.up, Term.ren] at h1
  have hg' : Runs B (App Q1 (App Q1 (App Q1 (Ref (impl "Program.gives")) (bytes p)) (bytes i)) (Form.nat n))
      (Tup Q1 (Lab "Some") (Tup Q1 (bytes o) (Lab "()"))) := hg
  have h2 := Typed.app h1 (runs_rfl hc hg' (T := maybeList))
  simp only [Term.inst, Term.sub, Subst.one, Subst.up, Term.ren, sub_bytes, ren_bytes, sub_nat, ren_nat,
    sub_u32, ren_u32] at h2
  obtain ⟨d, hd, -⟩ := hB.declares «trustedVersion.Compiler_2f_spec.no_other_failure» (by simp [laws])
  have hN : Typed B [] (Ref "Nat") T2 := by
    have := Typed.ref (Γ := []) (σ := Var) (hT «evalVersion.Nat» (by simp [baseTypes]))
    simpa [sub_var, «evalVersion.Nat»] using this
  have pa : ∀ a ∈ [(Q2, bytes p), (Q2, bytes i), (Q2, Form.nat n), (Q2, bytes o), (Q2, Form.u32 m),
      (Q1, Rfl)], Plain a.2 := by
    simp [plain_nat, plain_bytes, plain_u32, Plain.rfl]
  obtain ⟨w, dw, tw, cw⟩ := exists_all_or_conv hc hB.exists_ hB.ors (closed_call pa) (live_call' hd pa) h2 hN
  obtain ⟨f, rfl⟩ := canon_nat wt hT cl (data_value dw) tw
  have hk : Book.get B (impl "Wasm.run") = _ := hB.get (d := «trustedVersion.Wasm.run») (by simp [trustedVersion])
  have hcmp : Book.get B (impl "Compiler.compile") = _ :=
    hB.get (d := «trustedVersion.Compiler.compile») (by simp [trustedVersion])
  have pc : Term.Closed (compileOf p) := closed_call (xs := [(Q2, bytes p)]) (by simp [plain_bytes])
  have lc : Term.Live B (compileOf p) := live_call' (xs := [(Q2, bytes p)]) hcmp (by simp [plain_bytes])
  refine ⟨f, fun gs => ?_⟩
  have cw' : Term.Closed (wasmOf f (compileOf p) i m gs) :=
    closed_spine.2 ⟨fun _ => rfl, by simp [plain_nat.closed, pc, plain_bytes.closed, plain_engine.closed]⟩
  have lw : Term.Live B (wasmOf f (compileOf p) i m gs) :=
    live_args hk (fun a ha => by
      simp only [wasmOf, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl <;>
        first | exact lc | exact plain_nat.live | exact plain_bytes.live | exact plain_engine.live)
  have hgs : Typed B [] (Form.bools gs) _ := typed_bools hT cl (gs := gs)
  have c := cw (Form.bools gs) plain_bools (by simpa [Term.inst, Term.sub, Subst.one, listBools] using hgs)
  simp only [Term.inst, Term.sub, Subst.one, Subst.up, Term.ren, sub_bytes, sub_nat, sub_u32, plain_bools.sub] at c
  rcases c with c | c
  · exact .inl (conv_runs hc cw' lw (typed_wasm hB cl) (typed_outcome hB)
      (plain_ctor (by simp [plain_bytes])) (by simpa [wasmOf, engineOf, compileOf, spine, ctor, resultOf, outOfMemory] using c))
  · exact .inr (conv_runs hc cw' lw (typed_wasm hB cl) (typed_outcome hB) (plain_ctor nofun)
      (by simpa [wasmOf, engineOf, compileOf, spine, ctor, resultOf, outOfMemory] using c))

-- a closed, live term has no type Base's Empty, a Σ over no label
theorem not_empty (hc : Book.check B = .ok ()) (hB : Trusted B) (hcl : Term.Closed t) (hl : Term.Live B t)
    (ht : Typed B [] t (Ref "Empty")) : False := by
  have ⟨wt, lv⟩ := book_check B hc
  have hE : Book.get B "Empty" = some «trustedVersion.Empty» := by
    simpa [Rename.defn, Rename.term, «trustedVersion.Empty»] using
      hB.get (d := «trustedVersion.Empty») (by simp [trustedVersion])
  obtain ⟨v, ⟨_, _, vv⟩, pv⟩ := runs_acc' wt lv (halts B t lv hcl hl) ht
  have hv := pars_sr wt ht pv
  obtain ⟨a, b, rfl, ha, -⟩ := canon_sig wt vv hv ⟨_, .step (.delta hE (lv.1 _ _ hE)) .refl, .refl⟩
  obtain ⟨k, hk, -⟩ := canon_enu wt ((value_tup vv).1 rfl) ha crefl
  simp at hk

-- the law in_subset: no run of the compiled program is unsupported
theorem law_in_subset (hc : Book.check B = .ok ()) (hB : Trusted B)
    (hr : Runs B (wasmOf f (compileOf p) i m gs) unsupported) : False := by
  have hT := hB.types
  have ⟨wt, lv⟩ := book_check B hc
  have cl := lv.1
  have h0 := hB.law (l := «trustedVersion.Compiler_2f_spec.in_subset») (by simp [laws])
  simp [Rename.term, «trustedVersion.Compiler_2f_spec.in_subset»] at h0
  have h1 := Typed.app (Typed.app (Typed.app (Typed.app h0 (typed_nat hT cl (n := f)))
    (typed_bytes hT cl (bs := p))) (typed_bytes hT cl (bs := i))) (typed_engine hB cl (m := m) (gs := gs))
  simp [Term.inst, Term.sub, Subst.one, Subst.up, Term.ren] at h1
  have hr' : Runs B (App Q1 (App Q1 (App Q1 (App Q1 (Ref (impl "Wasm.run")) (Form.nat f))
      (App Q2 (Ref (impl "Compiler.compile")) (bytes p))) (bytes i)) (engineOf m gs))
      (Tup Q1 (Lab (impl "Wasm.Outcome.unsupported")) (Lab "()")) := hr
  have h2 := Typed.app h1 (runs_rfl hc hr' (T := Ref (impl "Wasm.Outcome")))
  simp only [Term.inst, Term.sub, Subst.one, Subst.up, Term.ren, sub_bytes, ren_bytes, sub_nat, ren_nat,
    sub_engine, ren_engine] at h2
  obtain ⟨d, hd, -⟩ := hB.declares «trustedVersion.Compiler_2f_spec.in_subset» (by simp [laws])
  have pa : ∀ a ∈ [(Q2, Form.nat f), (Q2, bytes p), (Q2, bytes i), (Q2, engineOf m gs), (Q1, Rfl)], Plain a.2 := by
    simp [plain_nat, plain_bytes, plain_engine, Plain.rfl]
  exact not_empty hc hB (closed_call pa) (live_call' hd pa) h2

-- Nat.is_le(Program.need(p, i, n), Program.memory(m))
def bigOf (p i : List UInt8) (n : Nat) (m : UInt32) : Term :=
  App Q1 (App Q1 (Ref (impl "Nat.is_le")) (spine (Ref (impl "Program.need")) [(Q2, bytes p), (Q1, bytes i),
    (Q1, Form.nat n)])) (App Q1 (Ref (impl "Program.memory")) (Form.u32 m))

theorem law_enough_memory (hc : Book.check B = .ok ()) (hB : Trusted B)
    (hg : Runs B (givesOf p i n) (Form.some (bytes o))) (hb : Runs B (bigOf p i n m) (Form.bool true)) :
    ∃ f, Runs B (wasmOf f (compileOf p) i m []) (resultOf o) := by
  have hT := hB.types
  have ⟨wt, lv⟩ := book_check B hc
  have cl := lv.1
  have h0 := hB.law (l := «trustedVersion.Compiler_2f_spec.enough_memory») (by simp [laws])
  simp [Rename.term, «trustedVersion.Compiler_2f_spec.enough_memory»] at h0
  have h1 := Typed.app (Typed.app (Typed.app (Typed.app (Typed.app h0 (typed_bytes hT cl (bs := p)))
    (typed_bytes hT cl (bs := i))) (typed_nat hT cl (n := n))) (typed_bytes hT cl (bs := o)))
    (typed_u32' hT cl (m := m))
  simp [Term.inst, Term.sub, Subst.one, Subst.up, Term.ren] at h1
  have hg' : Runs B (App Q1 (App Q1 (App Q1 (Ref (impl "Program.gives")) (bytes p)) (bytes i)) (Form.nat n))
      (Tup Q1 (Lab "Some") (Tup Q1 (bytes o) (Lab "()"))) := hg
  have h2 := Typed.app h1 (runs_rfl hc hg' (T := maybeList))
  simp only [Term.inst, Term.sub, Subst.one, Subst.up, Term.ren, sub_bytes, ren_bytes, sub_nat, ren_nat,
    sub_u32, ren_u32] at h2
  have hb' : Runs B (App Q1 (App Q1 (Ref (impl "Nat.is_le")) (App Q1 (App Q1 (App Q2 (Ref (impl "Program.need"))
      (bytes p)) (bytes i)) (Form.nat n))) (App Q1 (Ref (impl "Program.memory")) (Form.u32 m)))
      (Tup Q1 (Lab "True") (Lab "()")) := hb
  have h3 := Typed.app h2 (runs_rfl hc hb' (T := Ref "Bool"))
  simp only [Term.inst, Term.sub, Subst.one, Subst.up, Term.ren, sub_bytes, ren_bytes, sub_nat, ren_nat,
    sub_u32, ren_u32] at h3
  obtain ⟨d, hd, -⟩ := hB.declares «trustedVersion.Compiler_2f_spec.enough_memory» (by simp [laws])
  have hN : Typed B [] (Ref "Nat") T2 := by
    have := Typed.ref (Γ := []) (σ := Var) (hT «evalVersion.Nat» (by simp [baseTypes]))
    simpa [sub_var, «evalVersion.Nat»] using this
  have pa : ∀ a ∈ [(Q2, bytes p), (Q2, bytes i), (Q2, Form.nat n), (Q2, bytes o), (Q2, Form.u32 m),
      (Q1, Rfl), (Q1, Rfl)], Plain a.2 := by
    simp [plain_nat, plain_bytes, plain_u32, Plain.rfl]
  obtain ⟨w, dw, tw, cw⟩ := exists_conv hc hB.exists_ (closed_call pa) (live_call' hd pa) h3 hN
  obtain ⟨f, rfl⟩ := canon_nat wt hT cl (data_value dw) tw
  have hk : Book.get B (impl "Wasm.run") = _ := hB.get (d := «trustedVersion.Wasm.run») (by simp [trustedVersion])
  have hcmp : Book.get B (impl "Compiler.compile") = _ :=
    hB.get (d := «trustedVersion.Compiler.compile») (by simp [trustedVersion])
  have pc : Term.Closed (compileOf p) := closed_call (xs := [(Q2, bytes p)]) (by simp [plain_bytes])
  have lc : Term.Live B (compileOf p) := live_call' (xs := [(Q2, bytes p)]) hcmp (by simp [plain_bytes])
  have cw' : Term.Closed (wasmOf f (compileOf p) i m []) :=
    closed_spine.2 ⟨fun _ => rfl, by simp [plain_nat.closed, pc, plain_bytes.closed, plain_engine.closed]⟩
  have lw : Term.Live B (wasmOf f (compileOf p) i m []) :=
    live_args hk (fun a ha => by
      simp only [wasmOf, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl <;>
        first | exact lc | exact plain_nat.live | exact plain_bytes.live | exact plain_engine.live)
  simp only [Term.inst, Term.sub, Subst.one, sub_bytes, sub_u32, sub_nat] at cw
  exact ⟨f, conv_runs hc cw' lw (typed_wasm hB cl) (typed_outcome hB) (plain_ctor (by simp [plain_bytes])) cw⟩
