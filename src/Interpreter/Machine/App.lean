import Interpreter.Machine.Walk

-- Machine.App
-- ===========
--
-- The moves of a call, and of an application of a value.

open Quan Term

namespace Machine

-- the frames of arguments that know what is true
private theorem argFrames_ok (h : ∀ a ∈ ys, argOk bk a) : ∀ f ∈ argFrames ys, f.Ok bk := by
  intro f m
  simp only [argFrames, List.mem_map] at m
  obtain ⟨a, m, rfl⟩ := m
  exact h a m

-- the call that Ops knows reaches its value after its steps
theorem opsCall_sound (htb : tb = Ops.prepare bk) (h : opsCall tb k xs = some (r, n)) :
    Steps bk n (spine (Ref k) (xs.map argOf)) r ∧ Value bk r ∧ Data r := by
  have e : opsCall tb k xs = Ops.call tb k (xs.map argOf) := by
    unfold opsCall Ops.call
    split <;> simp_all
  subst htb
  exact ⟨(Ops.call_sound (e ▸ h)).1, (Ops.call_sound (e ▸ h)).2, Ops.call_data (e ▸ h)⟩

-- a call at the leaf of its walk: its value when Ops knows it, else a step to
-- the leaf
theorem fire_ok (htb : tb = Ops.prepare bk) (hk : Book.get bk k = some d)
    (vs : Values bk (xs.map argOf))
    (hw : walk bk d.v [] (xs.map argOf) = some (some (spine (close u ul) (zs.map argOf))))
    (hul : ul.Ok bk) (hzs : ∀ a ∈ zs, argOk bk a) (hst : ∀ f ∈ st, f.Ok bk)
    (hf : (from_ ()).term = plugs st (spine (Ref k) (xs.map argOf))) :
    (fire tb k xs u ul zs st from_).Ok bk (plugs st (spine (Ref k) (xs.map argOf))) := by
  unfold fire
  split
  next r m e =>
    obtain ⟨s, hr, hd⟩ := opsCall_sound htb e
    exact ⟨⟨⟨hr, trivial, fun _ => hd⟩, hst⟩, Steps.plugs hst s, hf⟩
  next =>
    refine ⟨⟨hul, fun f m => ?_⟩, ?_⟩
    · rcases List.mem_append.1 m with m | m
      · exact argFrames_ok hzs f m
      · exact hst f m
    · simp only [State.term, Focus.term, plugs_append, plugs_argFrames]
      exact Eval.plugs hst (.call hk vs (walk_iff.1 hw))

-- a call of k on xs: fire at the leaf of its walk, or v under vl, the call
-- itself, when its case tree needs more
theorem callMove_ok (htb : tb = Ops.prepare bk) (vs : Values bk (xs.map argOf))
    (hx : ∀ a ∈ xs, argOk bk a) (hv : close v vl = spine (Ref k) (xs.map argOf)) (hvl : vl.Ok bk)
    (hst : ∀ f ∈ st, f.Ok bk) (hf : (from_ ()).term = plugs st (spine (Ref k) (xs.map argOf))) :
    (callMove bk tb k xs st v vl from_).Ok bk (plugs st (spine (Ref k) (xs.map argOf))) := by
  unfold callMove
  split
  · exact hf
  next d hk =>
    have w := walkOpen_walk (bk := bk) (t := d.v) (l := .nil) (xs := xs) trivial hx
    have ho := walkOpen_ok (bk := bk) (t := d.v) (l := .nil) (xs := xs) trivial hx
    split
    next u ul zs hw =>
      rw [hw] at w ho
      exact fire_ok htb hk vs w.symm ho.1 ho.2 hst hf
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

-- App a.q f a.t, with f under fl a value, and the argument a a value when it
-- is live
theorem appMove_ok (htb : tb = Ops.prepare bk) (hf : Value bk (close f fl)) (hfl : fl.Ok bk)
    (ha : argOk bk a) (hx : a.q.live = true → Value bk (close a.t a.l)) (hst : ∀ g ∈ st, g.Ok bk)
    (hw : (from_ ()).term = plugs st (App a.q (close f fl) (close a.t a.l))) :
    (appMove bk tb f fl a st from_).Ok bk (plugs st (App a.q (close f fl) (close a.t a.l))) := by
  obtain ⟨q, x, xl, k⟩ := a
  obtain ⟨hxl, hk⟩ := ha
  dsimp only at hx hw hk hxl ⊢
  unfold appMove
  split
  next p b bl e =>
    split
    next hb =>
      rw [bindsAtL_eq hk] at hb
      refine ⟨⟨⟨Know.bind_ok hk (bindsAt_iff.1 hb).2, hxl, resolve_ok' hfl e⟩, hst⟩, ?_⟩
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
        have hkt : Know.Ok bk (Tup r (close a al) (close b al)) k := ex ▸ hk
        refine ⟨⟨resolve_ok' hfl e, ?_⟩, ?_⟩
        · intro g m
          simp only [List.mem_cons] at m
          rcases m with rfl | rfl | m
          · exact ⟨hal, hkt.tup.1⟩
          · exact ⟨hal, hkt.tup.2⟩
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
            · exact ⟨trivial, .lab⟩
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
    have := fire_ok (st := appArgs l ys st)
      (from_ := fun _ => ⟨.ret a.t a.l false, .call k t tl rxs a.q ys l :: st⟩) htb hd vs wk ho.1 ho.2
      (appArgs_ok hl hst) (by rw [plugs_appArgs]; exact hfrom)
    rw [plugs_appArgs] at this
    exact this
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
