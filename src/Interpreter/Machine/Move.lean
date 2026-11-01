import Interpreter.Machine.App

-- Machine.Move
-- ============
--
-- Each move keeps what the state knows true, and gives what Move.Ok says.

open Quan Term

namespace Machine

theorem move_ok (htb : tb = Ops.prepare bk) (hs : s.Ok bk) : (move bk tb s).Ok bk s.term := by
  obtain ⟨fc, st⟩ := s
  obtain ⟨hf, hst⟩ := hs
  simp only at hst
  cases fc with
  | ev t l =>
    simp only [Focus.Ok] at hf
    cases t
    case Var i =>
      simp only [move]
      split
      · rename_i x xl hx
        have := get?_ok hf hx
        refine ⟨⟨⟨this.1 rfl, this.2⟩, hst⟩, ?_⟩
        simp only [State.term, Focus.term, close_var, get?_close hx]
      · rename_i x xl hx
        refine ⟨⟨(get?_ok hf hx).2, hst⟩, ?_⟩
        simp only [State.term, Focus.term, close_var, get?_close hx]
      · rfl
    case Ref k =>
      have e : State.term ⟨.ev (Ref k) l, st⟩ = plugs st (spine (Ref k) (([] : List MArg).map argOf)) := by
        simp only [State.term, Focus.term, close_ref, List.map_nil, spine]
      simp only [move]
      rw [e]
      exact callMove_ok htb .nil nofun rfl trivial hst e
    case Ann x T =>
      simp only [move]
      refine ⟨⟨hf, hst⟩, Eval.plugs hst ?_⟩
      simp only [Focus.term, close_eq, Term.sub]
      exact .ann
    case App q f x =>
      have hpush : (Move.admin ⟨.ev f l, .appArg q x l :: st⟩).Ok bk (State.term ⟨.ev (App q f x) l, st⟩) :=
        ⟨⟨hf, List.forall_mem_cons.2 ⟨hf, hst⟩⟩, by
          simp only [State.term, Focus.term, close_app, plugs, List.foldl, Frame.plug]⟩
      simp only [move]
      split
      next k ys e =>
        split
        next d hd =>
          split
          next ht =>
            have hT : State.term ⟨.ev (App q f x) l, st⟩ =
                plugs st (spine (spine (Ref k) (([] : List MArg).reverse.map argOf)) (ys.map (argAt l))) := by
              have h1 : App q f x = spine (Ref k) ys := spine_unspine e
              simp only [State.term, Focus.term, h1, close_spine, close_ref, List.reverse_nil,
                List.map_nil, spine]
            rw [hT]
            exact go_ok htb ⟨ht, trivial, nofun, d, hd, fun zs => rfl⟩ hf hst
          next => exact hpush
        next => exact hpush
      next => exact hpush
    case Let q v f =>
      simp only [move]
      split
      · rename_i hq
        exact ⟨⟨hf, List.forall_mem_cons.2 ⟨⟨hq, hf⟩, hst⟩⟩, by
          simp only [State.term, Focus.term, close_eq, Term.sub, plugs, List.foldl, Frame.plug]⟩
      · rename_i hq
        refine ⟨⟨⟨nofun, hf, hf⟩, hst⟩, Eval.plugs hst ?_⟩
        simp only [Focus.term, close_cons]
        simp only [close_eq, Term.sub]
        exact .unlet (fun h => absurd h hq) (fun e => by subst e; exact absurd rfl hq)
    case Tup q a b =>
      simp only [move]
      split
      · rename_i hv
        simp only [Bool.and_eq_true] at hv
        refine ⟨⟨⟨value_iff.1 hv.2, trivial⟩, hst⟩, ?_⟩
        simp only [State.term, Focus.term, noVars_close hv.1]
      split
      · rename_i hq
        exact ⟨⟨hf, List.forall_mem_cons.2 ⟨⟨hq, hf⟩, hst⟩⟩, by
          simp only [State.term, Focus.term, close_tup, plugs, List.foldl, Frame.plug]⟩
      · rename_i hq
        exact ⟨⟨hf, List.forall_mem_cons.2 ⟨⟨fun h => absurd h hq, hf⟩, hst⟩⟩, by
          simp only [State.term, Focus.term, close_tup, plugs, List.foldl, Frame.plug]⟩
    all_goals simp only [move]
    all_goals first
      | exact ⟨⟨hf, List.forall_mem_cons.2 ⟨hf, hst⟩⟩, by
          simp only [State.term, Focus.term, close_eq, Term.sub, plugs, List.foldl, Frame.plug]⟩
      | exact ⟨⟨hf, List.forall_mem_cons.2 ⟨⟨hf, hf⟩, hst⟩⟩, by
          simp only [State.term, Focus.term, close_eq, Term.sub, plugs, List.foldl, Frame.plug]⟩
      | exact ⟨⟨⟨by simp only [close_eq, Term.sub]; constructor, trivial⟩, hst⟩, by
          simp only [State.term, Focus.term, close_eq, Term.sub]⟩
      | exact ⟨⟨⟨by simp only [close_eq, Term.sub]; constructor, hf⟩, hst⟩, rfl⟩
  | ret v vl =>
    simp only [Focus.Ok] at hf
    cases st with
    | nil => rfl
    | cons g st =>
      have hg := hst g List.mem_cons_self
      have hs := fun g' h => hst g' (List.mem_cons_of_mem g h)
      clear hst
      cases g <;> simp only [Frame.Ok] at hg <;> simp only [move]
      case appArg q x l =>
        split
        · rename_i hq
          exact ⟨⟨hg, List.forall_mem_cons.2 ⟨⟨hq, hf⟩, hs⟩⟩, rfl⟩
        · rename_i hq
          exact appMove_ok htb hf.1 hf.2 (fun h => absurd h hq) hg hs rfl
      case appVal q x l k =>
        split
        · rename_i hq
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at hq
          exact ⟨⟨hg.2, List.forall_mem_cons.2 ⟨⟨hq.1, hf⟩, hs⟩⟩, rfl⟩
        · rename_i hq
          simp only [Bool.and_eq_true, Bool.not_eq_true', not_and, Bool.not_eq_false] at hq
          exact appMove_ok htb hf.1 hf.2 (fun h => hg.1 (hq h)) hg.2 hs rfl
      case appFun q f fl => exact appMove_ok htb hg.2.1 hg.2.2 (fun _ => hf.1) hf.2 hs rfl
      case letIn q f l =>
        split
        · rename_i hq
          refine ⟨⟨⟨fun _ => hf.1, hf.2, hg.2⟩, hs⟩, Eval.plugs hs ?_⟩
          simp only [Focus.term, close_cons]
          refine .unlet (fun _ => hf.1) (fun e => data_iff.1 ?_)
          subst e
          simpa [dataAt_eq] using hq
        · rfl
      case tupB q b l => exact ⟨⟨hg.2, List.forall_mem_cons.2 ⟨⟨fun _ => hf.1, hf.2⟩, hs⟩⟩, rfl⟩
      case tupA q a al => simp only [share_eq]; exact ⟨⟨⟨Value.tup hg.1 hf.1, trivial⟩, hs⟩, rfl⟩
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
        have ha : argOk bk (q, v, vl, true) ∧ true = q.live := ⟨⟨hf.2, fun _ => hf.1⟩, hg.1.symm⟩
        have hT : State.term ⟨.ret v vl, .call k t tl rxs q ys l :: st⟩ =
            plugs st (spine (spine (Ref k) (((q, v, vl, true) :: rxs).reverse.map argOf)) (ys.map (argAt l))) := by
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
