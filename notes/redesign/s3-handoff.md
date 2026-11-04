# S3 handoff: canon (B5) and am (B6)

Branch `w/s3` off `feature/redesign` (worktree `C:\Users\mathe\source\repos\bb-wt\s3`). Commits:
`ffb99c1` (skeleton, smoke), `b9041dc` (canon.subst_closed). Not pushed; not merged.
Statement decisions and why: `s3-notes.md`.

## Files

| File | What | Holes |
|---|---|---|
| `src/Compiler/Machine/canon/spec.bend` | Term.is_eq, Tm.is, Tm.none, Term.closed, Canon.term/opt/walk/is_at/is, CStep, CSteps; 14 laws | (laws) |
| `src/Compiler/Machine/canon/impl.bend` | one def per law; kit (canon.ff, canon.and.l/r) | 9 `?TODO` |
| `src/Compiler/Machine/am/spec.bend` | FK, AF, Ag, AS, AO, AW; AF.plug(s), AS.term, AS.w, AF.ok, AS.ok0, AS.ok; Ag.args/terms; AM.walk, AM.move (+ AM.* helpers), AM.copy; AO.ok, AW.eval; 2 laws | (laws) |
| `src/Compiler/Machine/am/impl.bend` | one def per law | 2 `?TODO` |
| `src/Compiler/Machine/s3_smoke.bend` | computed checks (outside main's closure; delete in P5) | 0 |

Imports: Base, Shared/shared.bend, Book, Eval, Program, and am → canon/spec. No machine layer,
no S1 file (shared.bend of Machine/ is not needed).

## Laws (exact headers; bodies in spec.bend)

canon/spec.bend:
- `term.is_eq_ok` (+a, +b, e: Term.is_eq(a,b)=True) ⊢ a = b — open
- `term.is_eq_refl` (+a) ⊢ Term.is_eq(a,a) = True — open
- `canon.step` (+ds, +t) ⊢ CStep(ds, Canon.term(t,0)) = CStep(ds, t) — open (the key lemma)
- `canon.steps` (+n, +ds, +t) ⊢ CSteps(n, ds, Some{Canon.term(t,0)}) = Canon.opt(Eval.steps(n, ds, t)) — **proven** (from canon.step)
- `canon.result` (+ds, r) ⊢ Program.result(ds, Canon.opt(r)) = Program.result(ds, r) — open
- `canon.size` (+t, +d) ⊢ Term.size(Canon.term(t,d)) = Term.size(t) — **proven**
- `canon.vals` (+ds, +t, +d, a) ⊢ Eval.vals(ds, Canon.term(t,d), a) = Eval.vals(ds, t, a) — open
- `canon.data` (+t, +d) ⊢ Term.is_data(Canon.term(t,d)) = Term.is_data(t) — **proven**
- `canon.idem` (+t, +d) ⊢ Canon.term(Canon.term(t,d),d) = Canon.term(t,d) — **proven**
- `canon.start` (+i) ⊢ Canon.is(Program.start(i)) = True — open
- `canon.subst` (+t, +es, +d) ⊢ Canon(subst(Canon(t, d+|es|), es, d), d) = Canon(subst(t, es, d), d) — open
- `canon.subst_below` (+t, +es, +n, +d, hc: Canon.is_at(t,d), hn: |es| ≤ n) ⊢ Canon(subst(shift(t,n,d), es, d), d) = t — open
- `canon.subst_closed` (+t, +es, +d, hc: Term.closed(t,d)) ⊢ Canon(subst(t, es, d), d) = t — **proven**
- `canon.lift` (+es, +k, +j, hc: Canon.is(Env.sub(es,j))) ⊢ Canon(lift(es, k, k+j), k) = shift(Env.sub(es,j), k, 0) — open

am/spec.bend:
- `am.ok` (+ds, +vb, +s, ok: AS.ok(ds, vb, s)) ⊢ AO.ok(ds, s, AM.move(ds, vb, s)) = True — open
- `am.walk_eval` (+ds, +t, +e, +xs) ⊢ AW.eval(AM.walk(ds, t, e, xs)) = Canon.walk(Eval.walk(t, Ag.terms(e), Ag.args(xs))) — open

## For the other lanes

- S2: use `A.AM.copy(t, es)` for the copy's term (= the plan's Copy.term); `A.AM.walk(ds, t, e, xs)`
  (general e). Copy proof: λ/let body (one local, source depth 1) → `canon.subst_below` with n = 1;
  call leaf (source depth 0, STATIC) → `canon.subst_closed`; local → `canon.lift`; past the locals →
  poison (Var k by computation). Needs heap facts: fv ≤ d ⟹ the view at d is canonical at d;
  STATIC and fv ≤ k ⟹ closed at k. `copy.spec` with wt (d = 0) is false for a source part with
  poison and |es| > 0: keep the source STATIC (it is: the walk only follows image cells).
- S4: `AO.halt{2, out}` has `out = []`; compare the output only for status 0. Halt-2 reasoning:
  `AO.ok` gives `Tm.none(CStep(term))` and no result; with `canon.steps`, `canon.step` and
  `canon.result` that is Eval's term after j steps having no step and no result. A lemma
  "CSteps(1+n) = CStep after CSteps(n)" is not stated; prove it beside its use.
- P1/S2 check (not done here, P1 was in flight): AM.move must equal what `Mach.round()` does on the
  same state (plan §5.4 smoke). The mapping, branch by branch, is in s3-notes.md ("AM.move vs the
  machine").

## For P3 (F4 canon, F5 am)

- F4: the plan's route (a relation Rel kept by shift/subst/Env.sub/walk/vals/callWalk/redex/step).
  Useful first: Canon(shift(e, k, c), k+c) = shift(Canon(e, c), k, c); shift by 0 is identity;
  Term.is_eq_ok/refl (need Nat.is_eq, Name.is_eq and Quan.is_eq lemmas; Base has none for Nat.is_eq).
  The proven defs show the per-former pattern (generated: 19 cases, one rewrite per child, `_`
  marks the right side's child).
- F5: port eval_facts.bend (ev.stops: a value has no step; ev.stuck: a stuck focus makes its frames'
  term stuck; walk.more) from 4ebef88 (`git show 4ebef88:src/Compiler/Machine/eval_facts.bend`),
  with AF.ok/AFs.ok now Bool. am.ok splits by AM.move's cases (≈30 helpers). Invariant to carry in
  the walk: each KNOWN argument's term is a value.

## Gates run

- G1: `~/lead/gate.sh` on all five files: bend2 prints only the TODO count; kdiag3 0 FAIL (spec
  files: 14 and 48 defs; smoke: 60 defs). gate.sh does not map law-filling defs (`C.x`, `A.x` →
  `spec.x` in the lowered book), so the impl proofs were kernel-checked by name directly:
  14 defs of canon/impl (`spec.canon.steps`, `spec.canon.size`, `spec.canon.data`,
  `spec.canon.idem`, `spec.canon.subst_closed` and their helpers), 0 FAIL.
- G5: no def/law/type name of the new files clashes with any file that stays after P1 (all of src/
  but Compiler/Machine/* other than impl.bend and runs_as_eval.bend), nor within them. Not checked
  against S1/S2's new files (not visible). Smoke helpers are `smk.*`/`Smk.*`/`SR`.
- G2/G3: not run (files outside main's closure until S4 imports them).

WSL mirror for checks: `~/wt/s3` (src rsynced from the worktree, `bend` → `~/bb/bend`).
