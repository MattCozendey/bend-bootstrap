import Interpreter.Machine.Walk

-- Machine.App
-- ===========
--
-- The moves of a call, and of an application of a value.

open Quan Term

namespace Machine

-- the frames of arguments known to be values where their flag says so
private theorem argFrames_ok (h : ∀ a ∈ ys, argOk bk a) : ∀ f ∈ argFrames ys, f.Ok bk := by
  intro f m
  simp only [argFrames, List.mem_map] at m
  obtain ⟨⟨q, y, l, k⟩, m, rfl⟩ := m
  exact ⟨(h _ m).2.value, (h _ m).1⟩

-- the call that Ops knows reaches its value after its steps
theorem opsCall_sound (htb : tb = Ops.prepare bk) (h : opsCall tb k xs = some (r, n)) :
    Steps bk n (spine (Ref k) (xs.map argOf)) r ∧ Value bk r ∧ Data r := by
  have hm : xs.map argOfR = xs.map argOf :=
    List.map_congr_left fun ⟨q, x, l, _⟩ _ => congrArg (q, ·) resolve_close
  have e : opsCall tb k xs = Ops.call tb k (xs.map argOf) := by
    unfold opsCall Ops.call
    rw [hm]
    split <;> simp_all
  subst htb
  exact ⟨(Ops.call_sound (e ▸ h)).1, (Ops.call_sound (e ▸ h)).2, Ops.call_data (e ▸ h)⟩

-- a call of k on xs: its value when Ops knows it, else a step to the leaf of
-- its walk, or v under vl, the call itself, when its case tree needs more
theorem callMove_ok (htb : tb = Ops.prepare bk) (vs : Values bk (xs.map argOf))
    (hx : ∀ a ∈ xs, argOk bk a) (hv : close v vl = spine (Ref k) (xs.map argOf)) (hvl : vl.Ok bk)
    (hst : ∀ f ∈ st, f.Ok bk) (hf : (from_ ()).term = plugs st (spine (Ref k) (xs.map argOf))) :
    (callMove bk tb k xs st v vl from_).Ok bk (plugs st (spine (Ref k) (xs.map argOf))) := by
  unfold callMove
  split
  next r m e =>
    obtain ⟨s, hr, hd⟩ := opsCall_sound htb e
    exact ⟨⟨⟨hr, trivial, fun _ => hd⟩, hst⟩, Steps.plugs hst s, hf⟩
  next =>
    split
    · exact hf
    next d hk =>
      have w := walkOpen_walk (bk := bk) (t := d.v) (l := .nil) (xs := xs) trivial hx
      have ho := walkOpen_ok (bk := bk) (t := d.v) (l := .nil) (xs := xs) trivial hx
      split
      next t l ys hw =>
        rw [hw] at w ho
        have w' := walk_iff.1 w.symm
        refine ⟨⟨ho.1, fun f m => ?_⟩, ?_⟩
        · rcases List.mem_append.1 m with m | m
          · exact argFrames_ok ho.2 f m
          · exact hst f m
        · simp only [State.term, Focus.term, plugs_append, plugs_argFrames]
          exact Eval.plugs hst (.call hk vs w')
      next hw =>
        rw [hw] at w
        have w' := walk_iff.1 w.symm
        refine ⟨⟨⟨?_, hvl, nofun⟩, hst⟩, ?_⟩
        · rw [hv]; exact .call hk vs w'
        · simp only [State.term, Focus.term, hv]
      next => exact hf

-- an App of a value whose spine is on a def is a spine of values on a def
private theorem app_call (hf : Value bk f) (hx : q.live = true → Value bk x)
    (e : unspine f [(q, x)] = (Ref k, xs)) :
    App q f x = spine (Ref k) xs ∧ Values bk xs := by
  have e' := e
  rw [unspine_app] at e'
  simp only [Prod.mk.injEq] at e'
  obtain ⟨e1, rfl⟩ := e'
  have ef : f = spine (Ref k) (unspine f []).2 :=
    spine_unspine (t := f) (ys := []) (by rw [← e1])
  have ⟨k', d, ys, e2, _, vs, _⟩ := value_inv hf (by rw [ef]; exact (spine_ft ⟨rfl, rfl⟩).1)
  have h3 := spine_head e2
  rw [h3] at ef ⊢
  exact ⟨by rw [spine_snoc, ← ef], values_snoc.2 ⟨vs, hx⟩⟩

-- the call of appMove: a spine of values on a def, whose arguments know what
-- is true
private theorem appMove_call (hf : Value bk (close f fl)) (hfl : fl.Ok bk)
    (hx : q.live = true → Value bk (close x xl)) (hxl : xl.Ok bk)
    (e : unspineL f fl [⟨q, x, xl, .ofLive q.live⟩] = (Ref k, kl, ys)) :
    App q (close f fl) (close x xl) = spine (Ref k) (ys.map argOf) ∧
      Values bk (ys.map argOf) ∧ ∀ a ∈ ys, argOk bk a := by
  have u := unspineL_unspine (t := f) (l := fl) (xs := [⟨q, x, xl, .ofLive q.live⟩])
  rw [e] at u
  simp only [close_ref, List.map_cons, List.map_nil, argOf, unspine] at u
  have ⟨hv, vs⟩ := app_call hf hx u
  have ho := unspineL_ok (t := f) (xs := [⟨q, x, xl, .ofLive q.live⟩]) hfl (by simp [hxl])
  rw [e] at ho
  refine ⟨hv, vs, fun a m => ⟨(ho a m).1, ?_⟩⟩
  rw [(ho a m).2]
  have m' : (a.q, close a.t a.l) ∈ ys.map argOf := List.mem_map_of_mem m
  exact Know.ofLive_ok (values_mem vs m')

-- App q f x, with f under fl a value, and x under xl a value when q is live
theorem appMove_ok (htb : tb = Ops.prepare bk) (hf : Value bk (close f fl)) (hfl : fl.Ok bk)
    (hx : q.live = true → Value bk (close x xl)) (hxl : xl.Ok bk) (hst : ∀ g ∈ st, g.Ok bk)
    (hw : (w.state k q f fl x xl st).term = plugs st (App q (close f fl) (close x xl))) :
    (appMove bk tb q f fl x xl st w k).Ok bk (plugs st (App q (close f fl) (close x xl))) := by
  unfold appMove
  split
  next p b bl e =>
    split
    next hb =>
      rw [bindsAtL_eq (Know.ofLive_ok hx)] at hb
      refine ⟨⟨⟨Know.bind_ok (Know.ofLive_ok hx) (bindsAt_iff.1 hb).2, hxl, resolve_ok' hfl e⟩, hst⟩, ?_⟩
      simp only [State.term, Focus.term, close_cons]
      rw [resolve_eq e, close_lam]
      exact Eval.plugs hst (.beta (bindsAt_iff.1 hb).1 hx (bindsAt_iff.1 hb).2)
    · exact hw
  next h' hl e =>
    split
    next r a b al e2 =>
      split
      next hq =>
        have hal := resolve_ok' hxl e2
        have ex : close x xl = Tup r (close a al) (close b al) := by rw [resolve_eq e2, close_tup]
        have ⟨va, vb⟩ := value_tup (ex ▸ hx hq)
        refine ⟨⟨resolve_ok' hfl e, ?_⟩, ?_⟩
        · intro g m
          simp only [List.mem_cons] at m
          rcases m with rfl | rfl | m
          · exact ⟨va, hal⟩
          · exact ⟨fun _ => vb, hal⟩
          · exact hst g m
        · rw [resolve_eq e, close_prj, ex]
          exact Eval.plugs hst (.split hq (ex ▸ hx hq))
      · exact hw
    · exact hw
  next j h' m hl e =>
    split
    next i il e2 =>
      have ex : close x xl = Lab i := by rw [resolve_eq e2, close_lab]
      split
      next hq =>
        split
        next hij =>
          subst hij
          refine ⟨⟨resolve_ok' hfl e, hst⟩, ?_⟩
          rw [resolve_eq e, close_mat, ex]
          exact Eval.plugs hst (.hit hq)
        next hij =>
          refine ⟨⟨resolve_ok' hfl e, ?_⟩, ?_⟩
          · intro g m
            simp only [List.mem_cons] at m
            rcases m with rfl | m
            · exact ⟨fun _ => .lab, trivial⟩
            · exact hst g m
          · rw [resolve_eq e, close_mat, ex]
            exact Eval.plugs hst (.miss hq hij)
      · exact hw
    · exact hw
  · split
    next c kl ys e =>
      obtain ⟨hv, vs, hys⟩ := appMove_call hf hfl hx hxl e
      rw [hv]
      exact callMove_ok htb vs hys (by rw [close_shift]; exact hv) ⟨Know.ofLive_ok hx, hxl, hfl⟩ hst
        (by rw [← hv]; exact hw)
    · exact hw

-- the argument a goes into a call: its value when Ops knows it, else a step to
-- the leaf of its walk, or what next gives when the walk waits
theorem feed_ok (htb : tb = Ops.prepare bk) (hc : CallOk bk k t tl rxs)
    (ha : argOk bk a ∧ a.k.isValue = a.q.live) (hl : l.Ok bk) (hst : ∀ f ∈ st, f.Ok bk)
    (hnext : ∀ u ul, walkOpen bk t tl [a] = .need u ul →
      (next u ul).Ok bk (plugs st (spine (spine (Ref k) ((a :: rxs).reverse.map argOf)) (ys.map (argAt l))))) :
    (feed bk tb k t tl rxs a ys l st next).Ok bk
      (plugs st (spine (spine (Ref k) ((a :: rxs).reverse.map argOf)) (ys.map (argAt l)))) := by
  have hfrom : State.term ⟨.ret a.t a.l false, .call k t tl rxs a.q ys l :: st⟩ =
      plugs st (spine (spine (Ref k) ((a :: rxs).reverse.map argOf)) (ys.map (argAt l))) := by
    simp only [State.term, Focus.term, plugs, List.foldl, Frame.plug, spine_fed]
  unfold feed
  have w := walkOpen_walk (bk := bk) (t := t) (l := tl) (xs := [a]) hc.2.1 (by simpa using ha.1)
  have ho := walkOpen_ok (bk := bk) (t := t) (l := tl) (xs := [a]) hc.2.1 (by simpa using ha.1)
  split
  next u ul hw => exact hnext u ul hw
  next u ul zs hw =>
    rw [hw] at w ho
    obtain ⟨-, -, hrx, d, hd, hwk⟩ := hc
    have wk : walk bk d.v [] ((a :: rxs).reverse.map argOf) =
        some (some (spine (close u ul) (zs.map argOf))) := by
      rw [List.reverse_cons, List.map_append, hwk]; exact w.symm
    have vs : Values bk ((a :: rxs).reverse.map argOf) := values_fed fun a' m => by
      rcases List.mem_cons.1 m with rfl | m
      · exact ha
      · exact hrx a' m
    have e := Eval.call hd vs (walk_iff.1 wk)
    split
    next r n eo =>
      obtain ⟨s, hr, hd⟩ := opsCall_sound htb eo
      refine ⟨⟨⟨hr, trivial, fun _ => hd⟩, appArgs_ok hl hst⟩, ?_, hfrom⟩
      simp only [State.term, Focus.term, close_nil, plugs_appArgs]
      exact Steps.plugs hst (Steps.spine_f s)
    next =>
      refine ⟨⟨ho.1, fun f m => ?_⟩, ?_⟩
      · rcases List.mem_append.1 m with m | m
        · exact argFrames_ok ho.2 f m
        · exact appArgs_ok hl hst f m
      · simp only [State.term, Focus.term, plugs_append, plugs_argFrames, plugs_appArgs]
        exact Eval.plugs hst (Eval.spine_f e)
  next => exact hfrom

-- the arguments ys go into a call one after the other
theorem go_ok (htb : tb = Ops.prepare bk) (hc : CallOk bk k t tl rxs) (hl : l.Ok bk)
    (hst : ∀ f ∈ st, f.Ok bk) :
    (go bk tb k t tl rxs l st ys).Ok bk
      (plugs st (spine (spine (Ref k) (rxs.reverse.map argOf)) (ys.map (argAt l)))) := by
  induction ys generalizing t tl rxs with
  | nil =>
    refine ⟨⟨⟨?_, papOf_ok hc.2.2.1, nofun⟩, hst⟩, ?_⟩
    · rw [papOf_close]; exact hc.value
    · simp only [State.term, Focus.term, papOf_close, List.map_nil, spine]
  | cons y ys ih =>
    obtain ⟨q, y⟩ := y
    simp only [go]
    split
    next a ha =>
      obtain ⟨hy, hok, hlive⟩ := ready_ok hl ha
      have e : spine (spine (Ref k) (rxs.reverse.map argOf)) (((q, y) :: ys).map (argAt l)) =
          spine (spine (Ref k) ((a :: rxs).reverse.map argOf)) (ys.map (argAt l)) := by
        rw [spine_fed]
        obtain ⟨q', x, xl, b⟩ := a
        simp only [argOf, Prod.mk.injEq] at hy
        obtain ⟨rfl, hy⟩ := hy
        simp only [List.map_cons, argAt, spine, hy]
      rw [e]
      exact feed_ok htb hc ⟨hok, hlive⟩ hl hst fun u ul hw => ih (hc.feed ⟨hok, hlive⟩ hw)
    next ha =>
      refine ⟨⟨hl, fun f m => ?_⟩, rfl⟩
      rcases List.mem_cons.1 m with rfl | m
      · exact ⟨ready_live ha, hc, hl⟩
      · exact hst f m

end Machine
