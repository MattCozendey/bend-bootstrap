# S3 notes: statement decisions vs the plan (canon, am)

Lane S3 of P2. Branch `w/s3` (worktree `bb-wt/s3`). Files: `src/Compiler/Machine/canon/{spec,impl}.bend`,
`src/Compiler/Machine/am/{spec,impl}.bend`, `src/Compiler/Machine/s3_smoke.bend`.

## Checked against the kernel's Eval (why the statements are true)

- Eval.step never goes under a binder (it recurses into App f/x, Let v, Tup a/b, Rwt e, Min a/b,
  Ann x). It reads a running term's variable only through Term.subst/shift/Env.sub (moves it) and
  through shape tests (vals: no former; is_data: no; walk: Lam binds via is_data, Prj needs Tup, Mat
  needs Lab). Eval.walk's `App q f (Var v)` case reads the variable of the *book's* case tree, never
  of the running term. So `canon.step` holds for every t (also for open def bodies): both sides
  differ only in which free index each free variable has, and Canon erases that.
- `canon.subst` holds without asking `es` canonical (checked by hand: bound, local and free
  variables case by case).
- `canon.steps` follows from `canon.step` (proven). With `canon.result`, a machine run of j CSteps
  that halts gives exactly Eval's result after j steps; a halt 2 (no CStep, no result) means Eval's
  term after j steps has no step and no result.

## Changes vs the plan's text (§4.5, §4.6)

1. **`Maybe<Bk.Term>` without `&2`** in `Tm.is`, `Canon.opt`, `CStep`, `CSteps`: Eval's step is
   `Maybe<Bk.Term>`; `Maybe<&2, Bk.Term>` would not typecheck against it.
2. **`Canon.is_at(t, d)`** added (`Canon.is(t) = Canon.is_at(t, 0)`), and the helper `Canon.var`
   for the Var case. Needed by `canon.subst_below`.
3. **Copy lemmas made exact.** The plan only named `canon.subst_below` and `canon.lift`. Stated:
   - `canon.subst_below`: t canonical at d, |es| ≤ n ⟹ `Canon(subst(shift(t, n, d), es, d), d) = t`.
     This is the shared-part case of a λ/let body copy (source depth 1, one local): the part's view at
     depth 1+k is `shift(view at k, 1, k)` (view.deeper), and its poison must stay free. **It is false
     when n < |es|**: a poison variable would then be replaced by a local. So the copy's sharing of a
     part *with poison* is right only when the source depth is ≥ the number of locals.
   - `canon.subst_closed` (new, with `Term.closed`): a part closed at d is its own substitution and
     canonical form. This is the shared-part case of a call-leaf copy (source depth 0, wn locals):
     there n = 0 < |es| in general, so `subst_below` does not apply; the leaf is a STATIC image cell
     with no poison, and a part with fv ≤ k is closed at k. **For S2:** `copy.spec` with wt (d = 0)
     needs the source part to be poison-free (STATIC suffices); the heap layer needs "a STATIC cell
     with fv ≤ k reads closed at k" and "a cell with fv ≤ d reads canonical at d".
   - `canon.lift`: `Canon(lift(es, k, k+j), k) = shift(Env.sub(es, j), k, 0)` for a canonical local.
     Holds also for j ≥ |es| (then Env.sub gives Var 0).
4. **`am.walk_eval` generalized and premise dropped.** The plan had `e = []` and the premise
   `Ag.canon(xs)`. The statement holds for every e and xs with no premise (AW.eval and Canon.walk
   both canonicalize the leaf, and a walk tests arguments only by shape). Stronger, and directly
   inductive. `Ag.canon` is not defined (no use).
5. **Accessor and helper names.** Old `A.plug/A.plugs/A.w3/A.w.frame/A.w.frames/A.w` became
   `AF.plug`, `AF.plugs`, `AS.w3`, `AF.w`, `AFs.w`, `AS.w` (the alias `A` would have made them
   `A.A.plug`). `AS.ret/AS.focus/AS.fs` are written out (Bend makes no accessors). `AF.ok`,
   `AFs.ok` are Bool now.
6. **`AO.halt`'s bytes**: for status 0 the result's bytes; for status 2 always `[]`. The machine may
   emit some bytes before M.out halts with 2, so S4's `Halt(o)` must compare the output only when the
   status is 0.
7. **`AM.copy(t, es)`** = `Canon.term(Term.subst(t, Ag.terms(es), 0), 0)`: the plan's `Copy.term`
   (routines/spec, S2). S2 can define `Copy.term` as `A.AM.copy` or use it directly.
8. **`AM.walk` keeps the unused `ds`** (plan signature; S2's `walk.spec` calls it so).
9. **Frames' `b`**: `a` for every kind but Rwt (as in the plan's mv.ev.app example); `q` is Q0 and
   KNOWN False for Rwt, Min□b and Min a□ frames (their cells' headers have q 0).
10. `am.ok`'s `AO.ok` halt clause asks also "no CStep" for status 0 (a value has no step; it saves
   B8 a lemma).

## AM.move vs the machine (§3's new code)

Mirrors M.ev/M.ret/M.redex/M.call/M.walk at 4ebef88 with: D1 (Data by the DATA flag = Term.is_data),
D2 (no effect on terms), D4 (λ-match of labels that misses keeps the argument's KNOWN), D6 (no
local: poison, `Ag{q, False, Var 0}`; copies give canonical forms). KNOWN: initial call arguments
`live(q)`; walk Prj: first field `k && live(r)`, second `k`; walk local: the local's KNOWN; Prj
redex frames: `live(r)` and True; Mat miss frame: True. Mode 0 test: `vb || AM.former(t)` with
AM.former = Term.is_former but Tup (the image's table, field 4). **Not checked against the new
Mc code** (P1 is in flight); the plan's smoke "AM.move = Mach.round on the same state" belongs to
S2/S4 once P1 lands.

## Smoke (s3_smoke.bend, bend2 --check-only and kernel kdiag3: all pass)

Canon.term on open terms; CStep and canon.step on open terms (incl. an open def body and a walk
through a missing local); canon.subst, subst_below, lift instances; am.walk_eval instance; AM.move
single moves (poison, canonical λ-step inside frames); whole runs of AM with every move checked by
AO.ok: identity on [] and [5], list tail by λ-matches (walk Prj/Mat) on [] and [5], the same by
redexes of Prj/Mat in the running term, a walk through poison, a stuck free variable (halt 2), a mix
of Let/Min/Rwt/Ann/unlet, a failed meet (halt 2); and the same runs with VALUE set on every value
(the most AS.ok allows). Negative controls (a wrong expected byte) fail as they should.
