# S4 notes: statement decisions vs the plan (moves B7, memory B8, assembly)

Lane S4 of P2. Branch `w/s4` (worktree `bb-wt/s4`), on feature/redesign (967db15, then merged up to
bec2fe8: S1 follow-up, S2 follow-up `Lg.St.reg`, S2 review fixes F1–F3/G1/G2/G4). Files:
`src/Compiler/Machine/moves/{spec,ev,ret,call,round}.bend`, `memory/{spec,impl}.bend`, `moves.bend`,
`runs_as_eval.bend` (bodies only), `s4_smoke.bend`. Each deviation is decided on merit.

## The shape

- **moves/spec.bend**: `Vb` (the focus' VALUE flag), `Next(x, o)` = `st2 => {Next.is(x, o, st2) == True}`
  (Inv of the move's next state; False for a halt), `Halt(o)` = `k => st2 => {Halt.is(o, k, st2) == True}`
  (the status, and for 0 the bytes as the output reversed), `round.sim` (plan §4.8, with `Me.Budget`), `inv.vb`,
  27 move laws `mv.*`, and `call.frames` (review G3).
- **moves/round.bend**: round.sim PROVEN from the move laws: the mode's test (`tot.if` on Inv's mode
  register), then AM.move's case split (VALUE flag, focus term; top frame, swap test, function at a
  redex). Only `inv.vb` is open there.
- **moves.bend**: the assembly, PROVEN, no `?TODO`: `asm.post` (any fuel, by induction on the fuel),
  `asm.done` (some fuel, by induction on canonical steps and the measure), `asm.mem` (no out of memory
  within F), Cir.result's start (`asm.res.*`, `asm.rex.*`, `asm.rok.*`), the run of Mach.code (input,
  mode, loop), how a run ends, `mach.*.proof`. runs_as_eval's four bodies call them (statements byte
  for byte; the import `./moves.bend as Gen2Moves` is back, as at 4ebef88).
- **memory/spec.bend**: `Mem.cells`, `Stat`, `Defs.big`, `StepSize`, `Need`, `Budget`, `Peak`, `Fits.halt`,
  `Start.ok`; laws eval.stops, round.mem, input.mem, need.peak, budget.need, input.need, need.lim,
  start.ok, code.fits. memory/impl.bend: all `?TODO` (routes in its header).

## Deviations from the plan's text (§4.8, §4.9), and why

1. **Budget lives in memory/spec.bend**, which moves/spec imports (the plan put it in moves/spec): the
   memory laws need it and must not import the move laws.
2. **Need has 3 × max(|t|, |step|), not 2 ×.** During a call, the old term, the spine's argument cells
   (up to |t| / 2) and the new copy are live together, so 2 × max can be too small (round.mem would
   be false). F still covers it: Room = 20 (fi + Peak) + S <= 20·307 + 20 C + 80 W + 61.3 S < F, with
   |i| <= S / 72 (start.size) where memory_bound.bend used |i| <= S.
3. **The memory bound needs run invariants that Inv does not hold**, so the plan's `budget.need` (Inv
   and the run's position only) is false as stated: next - first counts the free list, which only the
   run's history bounds, and the cache's STATIC cells are not in Inv. So: `round.mem` (a round keeps
   next - first within max(before, Need) and makes no STATIC cell; exec-level, no Tot), `input.mem`
   (after M.input: cache <= 6144, next - first <= Peak), and `budget.need`/`need.peak` take `Stat <= C`,
   `C <= 6144`, `Mem.cells <= Peak` as premises. The assembly carries them (Asm.Ms).
4. **The output's room at halt 0 (`code.fits`) is a law here** (memory/spec), not in Halt: out.spec does
   not give it, and it is a fact of Cir alone (cir_fits.bend at 4ebef88 ported). Halt compares status
   and bytes only.
5. **`start.ok`**: mach.memory must also exclude Cir.result's out of memory *before* the program
   (memory check, input length, alloc of the input), which old moves.bend never handled (its
   mach.memory was a bare hole). Law: with need <= memory(m), Cir.result's checks pass.
6. **`eval.stops`** (a value has no step; ev.stops of eval_facts at 4ebef88) is stated in memory/spec:
   the loop needs it (a term with a result takes no step) and no other lane states it.
7. **Move laws**: 27, not 30: `mv.ev.val` covers VALUE and former (one test in M.ev); `mv.ret.swap`
   covers App q □ a of both arg kinds (premise `Kind.is_app`), and so do `mv.ret.app.*`. Each states its
   outcome as AM.move computes it in its case (some as `AM.redex(..)`, `AM.need(..)`, `AM.body(..)`,
   `AM.out(..)`, `AM.meet(..)` terms, so the dispatcher needs no split on the argument). Branch facts
   are separate Bool premises (`hk`, `hs`, `hc`, `hq`, `hv`).
8. **`call.frames`** (review G3): M.call's second loop (argument cells to frames) cannot be stepped by
   push.spec (between push and release two cells point to one term of count 1). Law for the whole
   loop, with its text as `Call.frames()` (a copy of the code inside M.call; the smoke checks the
   copy is definitional? see Smoke) and the frames `Call.fs(ys, fs)` (the chain at wh is the
   arguments left reversed, so `Call.fs(rev(xs), fs) = AM.frames(xs, fs)`; a call leaf proves that).
9. **The loop's invariant is `Asm.J = Inv && AS.ok0`**; `inv.vb` gives the rest of AS.ok (VALUE only on
   a value, from H's V.chk). AS.ok0 at the start is `canon.start`.

## Checked against the code and the laws (why the statements are true)

- round.sim's Next/Halt are exactly what the dispatcher needs; each mv law's outcome is the reduct of
  AM.move in its case (round.bend checks it by conversion).
- Halt.is for status 2 does not look at the output (AO.halt{2, []}; S3's note).
- round.mem: a new cell is taken only when the free list is empty (M.alloc), when next - first = |L|;
  every live cell is STATIC or held (Cov), held cells <= the term's nodes, so live <= Stat + |t| plus
  what the round adds (<= |t'| + |t|/2 + 3 big + 16). No round makes a STATIC cell (only M.input).
- budget.need: Budget = max(20 (fi + Need) + |t|, 20 next + |t|) and next <= fi + Peak.
- code.fits: held at 4ebef88 for any St0 (cir_fits); the new M.alloc still takes a new cell first.

## Findings for other lanes (route by the coordinator)

- G5: `Inv` (routines/spec.bend) and `alloc.reg` (routines/spec.bend) share raw names with layer A
  (`Cir/simulation_relation.bend`, `Cir/simulation_stmt.bend`). Paths keep them apart in the book; the
  G5 rule as written counts them. S4's own names clash with nothing.
- Bend2 lessons (for P3): `&&` is left-associative; a match must come before any local statement; a
  computed value cannot be matched or destructured (give it a helper def, or use projections);
  `+x` lets need Data (Base's `A & B` is a Type: use `Sigma<&2, &2, A, _ => B>` for reusable facts);
  lambda binders need `+` to be reused; `(%e : P; t)` has type P[b] for t : P[a] (e : {a == b}).

## gen2 tally

(see s4-handoff.md: filled at the end)
