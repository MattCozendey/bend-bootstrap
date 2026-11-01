import Interpreter.Machine.App

-- Machine.Move
-- ============
--
-- Each move keeps what the state knows true, and gives what Move.Ok says.

open Quan Term

namespace Machine

-- a value goes into the pairs around it: the term stays, and what the state
-- knows stays true
theorem retTups_ok (hv : Value bk (close v vl)) (hvl : vl.Ok bk) (hd : d = true → Data (close v vl))
    (hst : ∀ f ∈ st, f.Ok bk) :
    (retTups v vl d st).Ok bk ∧ (retTups v vl d st).term = plugs st (close v vl) := by
  induction st generalizing v vl d with
  | nil => exact ⟨⟨⟨hv, hvl, hd⟩, hst⟩, rfl⟩
  | cons f st ih =>
    have hf := hst f List.mem_cons_self
    have hs := fun g m => hst g (List.mem_cons_of_mem f m)
    cases f <;> simp only [retTups] <;> simp only [Frame.Ok] at hf
    case tupA q a al da =>
      have := ih (v := share (Tup q (close a al) (close v vl))) (vl := .nil) (d := (!q.live || da) && d)
        (by rw [share_eq, close_nil]; exact .tup hf.1 hv) trivial
        (by
          rw [share_eq, close_nil]
          intro h
          simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
          exact .tup (fun hq => hf.2.2 hq (h.1.resolve_left (by simp [hq]))) (hd h.2))
        hs
      refine ⟨this.1, this.2.trans ?_⟩
      simp only [share_eq, close_nil, plugs, List.foldl, Frame.plug]
    case tupB q b l =>
      split
      next b' bl db hb =>
        have hb' := imm_ok hf.2 hb
        have := ih (v := share (Tup q (close v vl) (close b' bl))) (vl := .nil) (d := d && db)
          (by rw [share_eq, close_nil]; exact .tup (fun _ => hv) hb'.2.1) trivial
          (by
            rw [share_eq, close_nil]
            intro h
            simp only [Bool.and_eq_true] at h
            exact .tup (fun _ => hd h.1) (hb'.2.2.2 h.2))
          hs
        refine ⟨this.1, this.2.trans ?_⟩
        simp only [share_eq, close_nil, plugs, List.foldl, Frame.plug, hb'.1]
      next => exact ⟨⟨hf.2, List.forall_mem_cons.2 ⟨⟨fun _ => hv, hvl, fun _ => hd⟩, hs⟩⟩, rfl⟩
    all_goals exact ⟨⟨⟨hv, hvl, hd⟩, hst⟩, rfl⟩

-- a pair goes down to the first part that takes a step
theorem evTup_ok (hl : l.Ok bk) (hst : ∀ f ∈ st, f.Ok bk) :
    (evTup q a b l st).Ok bk (plugs st (close (Tup q a b) l)) := by
  induction b generalizing q a st with
  | Tup q' a2 b2 _ ih =>
    unfold evTup
    split
    next hra =>
      have hq : q.live = true := by
        split at hra
        · assumption
        · cases hra
      exact ⟨⟨hl, List.forall_mem_cons.2 ⟨⟨hq, hl⟩, hst⟩⟩, by
        simp only [State.term, Focus.term, close_tup, plugs, List.foldl, Frame.plug]⟩
    next a' al da hra =>
      have ha' := imm_part hl hra
      split
      next b' bl db hb =>
        simp only [imm] at hb
        split at hb
        next hc =>
          cases hb
          have hc' := closedData_ok hc
          have := retTups_ok (st := st) (v := share (Tup q (close a' al) (close (Tup q' a2 b2) .nil)))
            (vl := .nil) (d := da && true)
            (by rw [share_eq, close_nil, close_nil]; exact .tup ha'.2.1 (data_value hc'.2)) trivial
            (by
              rw [share_eq, close_nil, close_nil]
              intro h
              simp only [Bool.and_true] at h
              exact .tup (fun hq => ha'.2.2.2 hq h) hc'.2)
            hst
          refine ⟨this.1, this.2.trans ?_⟩
          simp only [share_eq, close_nil, close_tup (q := q), ha'.1, noVars_close hc'.1]
        next => cases hb
      next hb =>
        have := ih (q := q') (a := a2) (st := .tupA q a' al da :: st)
          (List.forall_mem_cons.2 ⟨⟨ha'.2.1, ha'.2.2.1, ha'.2.2.2⟩, hst⟩)
        simp only [plugs, List.foldl, Frame.plug] at this
        simp only [close_tup (q := q), ← ha'.1]
        exact this
  | _ =>
    unfold evTup
    split
    next hra =>
      have hq : q.live = true := by
        split at hra
        · assumption
        · cases hra
      exact ⟨⟨hl, List.forall_mem_cons.2 ⟨⟨hq, hl⟩, hst⟩⟩, by
        simp only [State.term, Focus.term, close_tup, plugs, List.foldl, Frame.plug]⟩
    next a' al da hra =>
      have ha' := imm_part hl hra
      split
      next b' bl db hb =>
        have hb' := imm_ok hl hb
        have := retTups_ok (st := st) (v := share (Tup q (close a' al) (close b' bl))) (vl := .nil)
          (d := da && db)
          (by rw [share_eq, close_nil]; exact .tup ha'.2.1 hb'.2.1) trivial
          (by
            rw [share_eq, close_nil]
            intro h
            simp only [Bool.and_eq_true] at h
            exact .tup (fun hq => ha'.2.2.2 hq h.1) (hb'.2.2.2 h.2))
          hst
        refine ⟨this.1, this.2.trans ?_⟩
        simp only [share_eq, close_nil, close_tup, ha'.1, hb'.1]
      next =>
        exact ⟨⟨hl, List.forall_mem_cons.2 ⟨⟨ha'.2.1, ha'.2.2.1, ha'.2.2.2⟩, hst⟩⟩, by
          simp only [State.term, Focus.term, close_tup, plugs, List.foldl, Frame.plug, ha'.1]⟩

-- the call that a spine starts
theorem spineCall_some (h : spineCall bk t = some (k, d, ys)) :
    unspine t [] = (Ref k, ys) ∧ Book.get bk k = some d ∧ takes d.v = true := by
  unfold spineCall at h
  split at h
  next k' ys' e =>
    split at h
    next d' hd =>
      split at h
      next ht => cases h; exact ⟨e, hd, ht⟩
      next => cases h
    next => cases h
  next => cases h

theorem move_ok (htb : tb = Ops.prepare bk) (hs : s.Ok bk) : (move bk tb s).Ok bk s.term := by
  obtain ⟨fc, st⟩ := s
  obtain ⟨hf, hst⟩ := hs
  simp only at hst
  cases fc with
  | ev t l =>
    simp only [Focus.Ok] at hf
    simp only [move]
    split
    next v vl d hi =>
      obtain ⟨e, hv, hvl, hd⟩ := imm_ok hf hi
      exact ⟨⟨⟨hv, hvl, hd⟩, hst⟩, by simp only [State.term, Focus.term, e]⟩
    next hi =>
    cases t
    case Var i =>
      simp only [evMove]
      split
      · rename_i x xl k hx
        refine ⟨⟨(get?_ok hf hx).2, hst⟩, ?_⟩
        simp only [State.term, Focus.term, close_var, get?_close hx]
      · rfl
    case Ref k =>
      have e : State.term ⟨.ev (Ref k) l, st⟩ = plugs st (spine (Ref k) (([] : List MArg).map argOf)) := by
        simp only [State.term, Focus.term, close_ref, List.map_nil, spine]
      simp only [evMove]
      rw [e]
      exact callMove_ok htb .nil nofun rfl trivial hst e
    case Ann x T =>
      simp only [evMove]
      refine ⟨⟨hf, hst⟩, Eval.plugs hst ?_⟩
      simp only [Focus.term, close_eq, Term.sub]
      exact .ann
    case App q f x =>
      have hpush : (Move.admin ⟨.ev f l, .appArg ⟨q, x, l, .none⟩ :: st⟩).Ok bk
          (State.term ⟨.ev (App q f x) l, st⟩) :=
        ⟨⟨hf, List.forall_mem_cons.2 ⟨⟨hf, trivial⟩, hst⟩⟩, by
          simp only [State.term, Focus.term, close_app, plugs, List.foldl, Frame.plug]⟩
      simp only [evMove]
      split
      next k d ys hc =>
        obtain ⟨e, hd, ht⟩ := spineCall_some hc
        have hT : State.term ⟨.ev (App q f x) l, st⟩ =
            plugs st (spine (spine (Ref k) (([] : List MArg).reverse.map argOf)) (ys.map (argAt l))) := by
          have h1 : App q f x = spine (Ref k) ys := spine_unspine e
          simp only [State.term, Focus.term, h1, close_spine, close_ref, List.reverse_nil,
            List.map_nil, spine]
        rw [hT]
        exact go_ok htb ⟨ht, trivial, nofun, d, hd, fun zs => rfl⟩ hf hst
      next => exact hpush
    case Let q v f =>
      simp only [evMove]
      split
      · rename_i hq
        exact ⟨⟨hf, List.forall_mem_cons.2 ⟨⟨hq, hf⟩, hst⟩⟩, by
          simp only [State.term, Focus.term, close_eq, Term.sub, plugs, List.foldl, Frame.plug]⟩
      · rename_i hq
        refine ⟨⟨⟨trivial, hf, hf⟩, hst⟩, Eval.plugs hst ?_⟩
        simp only [Focus.term, close_cons]
        simp only [close_eq, Term.sub]
        exact .unlet (fun h => absurd h hq) (fun e => by subst e; exact absurd rfl hq)
    case Tup q a b => simp only [evMove]; exact evTup_ok hf hst
    case Rwt e P f =>
      simp only [evMove]
      exact ⟨⟨hf, List.forall_mem_cons.2 ⟨hf, hst⟩⟩, by
        simp only [State.term, Focus.term, close_eq, Term.sub, plugs, List.foldl, Frame.plug]⟩
    case Min a b =>
      simp only [evMove]
      exact ⟨⟨hf, List.forall_mem_cons.2 ⟨hf, hst⟩⟩, by
        simp only [State.term, Focus.term, close_eq, Term.sub, plugs, List.foldl, Frame.plug]⟩
    all_goals simp only [evMove]; rfl
  | ret v vl d =>
    simp only [Focus.Ok] at hf
    cases st with
    | nil => rfl
    | cons g st =>
      have hg := hst g List.mem_cons_self
      have hs := fun g' h => hst g' (List.mem_cons_of_mem g h)
      clear hst
      cases g <;> simp only [Frame.Ok] at hg <;> simp only [move, retMove, meetMove]
      case appArg a =>
        split
        · rename_i hq
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at hq
          exact ⟨⟨hg.1, List.forall_mem_cons.2 ⟨⟨hq.1, hf.1, hf.2.1⟩, hs⟩⟩, rfl⟩
        · rename_i hq
          simp only [Bool.and_eq_true, Bool.not_eq_true', not_and, Bool.not_eq_false] at hq
          exact appMove_ok htb hf.1 hf.2.1 hg (fun h => hg.2.value (hq h)) hs rfl
      case appFun q f fl =>
        exact appMove_ok (a := ⟨q, v, vl, .ofData d⟩) htb hg.2.1 hg.2.2
          ⟨hf.2.1, Know.ofData_ok hf.1 hf.2.2⟩ (fun _ => hf.1) hs rfl
      case letIn q f l =>
        split
        · rename_i hq
          simp only [letTakes] at hq
          have hd : q = Q2 → Data (close v vl) := fun e => by
            subst e
            simp only [bne_self_eq_false, Bool.false_or, Bool.or_eq_true] at hq
            rcases hq with hq | hq
            · exact hf.2.2 hq
            · exact data_iff.1 (by simpa [dataAt_eq] using hq)
          refine ⟨⟨⟨Know.bind_ok (Know.ofData_ok hf.1 hf.2.2) hd, hf.2.1, hg.2⟩, hs⟩, Eval.plugs hs ?_⟩
          simp only [Focus.term, close_cons]
          exact .unlet (fun _ => hf.1) hd
        · rfl
      case tupB q b l =>
        have := retTups_ok hf.1 hf.2.1 hf.2.2 (st := .tupB q b l :: st) (List.forall_mem_cons.2 ⟨hg, hs⟩)
        exact ⟨this.1, this.2⟩
      case tupA q a al da =>
        have := retTups_ok hf.1 hf.2.1 hf.2.2 (st := .tupA q a al da :: st) (List.forall_mem_cons.2 ⟨hg, hs⟩)
        exact ⟨this.1, this.2⟩
      case rwt P f l =>
        split
        · rename_i hv
          have e := resolve_close (t := v) (l := vl)
          rw [hv, close_rfl] at e
          refine ⟨⟨hg, hs⟩, ?_⟩
          simp only [State.term, Focus.term, plugs, List.foldl, Frame.plug]
          rw [← e]
          exact Eval.plugs hs .cast
        · rfl
      case minB b l =>
        refine ⟨⟨hg, List.forall_mem_cons.2 ⟨?_, hs⟩⟩, ?_⟩
        · simp only [Frame.Ok]
          split
          · exact .lab
          · exact hf.1
        · simp only [State.term, Focus.term, plugs, List.foldl, Frame.plug]
          split
          · rename_i e; rw [resolve_eq e, close_lab]
          · rfl
      case call k t tl rxs q ys l =>
        have ha : argOk bk ⟨q, v, vl, .ofData d⟩ ∧ (Know.ofData d).isValue = q.live :=
          ⟨⟨hf.2.1, Know.ofData_ok hf.1 hf.2.2⟩, Know.ofData_isValue.trans hg.1.symm⟩
        have hT : State.term ⟨.ret v vl d, .call k t tl rxs q ys l :: st⟩ =
            plugs st (spine (spine (Ref k) ((⟨q, v, vl, .ofData d⟩ :: rxs).reverse.map argOf)) (ys.map (argAt l))) := by
          simp only [State.term, Focus.term, plugs, List.foldl, Frame.plug, spine_fed]
        rw [hT]
        exact feed_ok htb hg.2.1 ha hg.2.2 hs fun u ul hw => go_ok htb (hg.2.1.feed ha hw) hg.2.2 hs
      case minA a =>
        split
        · split
          · rename_i i j e hq
            have ev := resolve_close (t := v) (l := vl)
            rw [e, close_lab] at ev
            refine ⟨⟨trivial, hs⟩, ?_⟩
            simp only [State.term, Focus.term, plugs, List.foldl, Frame.plug]
            rw [← ev]
            exact Eval.plugs hs (.meet hq.1 hq.2)
          · rfl
        · rfl

end Machine
