# Statement review of lane S4 (moves B7, memory B8, the assembly)

Reviewer: independent statement reviewer (Opus), 2026-11-04. I read branch `w/s4` at d78fbea. S4
has since been merged into feature/redesign (fdce9fa). I compared the merged files with d78fbea.
`moves.bend`, `moves/round.bend`, `moves/ev.bend`, `moves/spec.bend` and `memory/spec.bend` are the
same, except that S2 renamed `Inv` to `MInv` (md5 equal after the rename). In the S2 files that
these rest on, the merge changed four things:
- `Fix` gains "free's head is 0 or a cell";
- `Chs.go` reads its arguments by projections;
- `swap.spec`'s premise is split in two;
- `alloc.reg` / `make.reg` become `alloc.regs` / `make.regs`, and there is a new `alloc.cell`.
All are true and equivalent (or stronger). None of them closes G1 or G2. Line numbers are those of
feature/redesign. The w/s4 worktree also held an uncommitted edit of `s4_smoke.bend`; I did not
review it (see G3).
I read every S4 statement, the code it speaks about (`Machine/impl.bend`), the laws it uses (S1 to
S3), and the path up to `src/Compiler/spec.bend`. I edited no file of the repo. Proof bodies are
out of scope (AGENTS 2.3.2), except that the assembly must really be proven: I checked that again
with the kernel.

## Verdict

**No false statement found. The assembly is really proven, and `enough_memory` really follows.
But two gaps of strength (G1, G2) make leaves that the stated laws cannot reach: fix them before
P3 lane F15 starts, and before the move lanes F14 prove their budgets.**

- **The assembly is proven.** I re-ran the kernel on the S4 mirror at d78fbea (`~/lead/gate.sh`; the
  merge changes only the name MInv):
  `moves.bend` 124 defs, **0 fail**. `moves/round.bend` 12 defs, 1 fail, which is the hole
  `inv.vb`. `moves.bend` holds no `?TODO`, no `@unsafe`, and no `Empty.absurd` that does not come
  from a real contradiction. It uses only stated laws: `Mv.round.sim`, `Mv.inv.vb`, the nine `Me.*`
  laws, `R.input.spec`, `A.am.ok`, `C.canon.steps`, `C.canon.result`, `C.canon.start`,
  `C.term.is_eq_ok`, `C.term.is_eq_refl`, and the logic laws `Lg.tot.any`, `Lg.tot.wk`,
  `Lg.frame.fixed`, `Lg.exec.more`, `Lg.exec.set`, `Lg.reg.lt`, `Lg.nregs.set`, `Lg.lim.set`. All
  its other names are proven defs.
- **No hole sits above the leaves.** In the whole tree, every `?TODO` fills a stated law, except
  layer A's known `mach_wasm.uniform` (runs_as_cir.bend).
- **`runs_as_eval.bend` keeps its 4 statements byte for byte.** Its diff from main is one line: the
  body of `mach.memory`. `proof.bend`, `spec.bend` and layer A are the same as on feature/redesign.
  So the chain `mach.*` → `proof.bend` → the four laws of `spec.bend` is the one that G2/G3 already
  check.
- **Budget ≤ F holds, with a wide margin** (arithmetic below). F is measured on the bytes `p` that
  the compiler reads, which are the pruned Book's bytes (3.5 step 3). So it is the program size of
  3.3.8 for the program that is compiled.

## Findings, by severity

### G1 (high, gap): `round.mem` and `input.mem` cannot be reached from the stated routine laws

- Where: memory/spec.bend:143 `round.mem`, :156 `input.mem`. They rest on the routine laws of
  routines/spec.bend: `push.spec` :461, `one.spec` :524, `copy.spec` :591, `walk.spec` :620, `dec.spec`,
  `pop.spec`, `release_arg.spec`, `release_all.spec`, `inc.spec`, `input.spec` :654. Also
  `call.frames` (moves/spec.bend:554).
- Statement: `round.mem`: `exec(f, Mach.round(), st) = next{st2}` gives
  `Stat(st2) ≤ Stat(st) ∧ Mem.cells(st2) ≤ max(Mem.cells(st), Need(ds, st, s))`.
- Both laws are TRUE. I checked them against the code. A fresh cell is taken only when the free
  list is empty, and then next − first is |L|. No round makes a STATIC cell: only `M.input` uses
  `M.h.static()`, `M.copy` masks the header with 255, and the other headers have no bit 10.
  `round.mem` also holds on every round of `s4_smoke` and of my runs.
- Problem: no stated law says anything about `next`, or about the length of the free list, after a
  routine.
  - Every routine post says `H(x, st2, L2, ..)` plus a bound on |L2|.
  - H's `Part` says `next − fi = |L2| + |free list|`. That allows any `next`, if the free list is
    long enough.
  - `Kept` (routines/spec.bend:45) is `Agree ∧ Same`, and `Same` (:38) does not hold `next`. So
    even `dec.spec`, which "takes no cell", does not say that `next` stays. The plan's §4.7 Keep
    said "next is the same". The implementation dropped that clause, because the allocating
    routines share `Kept`.
  - So the route in s4-handoff.md (from `Alloc.st` and the |L2| bounds) does not exist. Proving
    `round.mem` means stepping all 27 moves a second time at the exec level, outside the Tot/WP kit,
    and stepping the inside of `copy`, `walk` and `dec` too. That is a second proof of S2's hardest
    routines.
  - `input.mem` has the same problem, on one loop: its `Stat ≤ 6144` needs the cache's count.
- Argument (no counterexample is needed: the stated laws are too weak). `copy.spec`'s post holds
  for a state `st2` whose `next` is `next(st) + 10^6`, with a free list of 10^6 cells. Such a state
  satisfies H, Kept and |L2| ≤ |L| + |copy|. And from it `round.mem` fails.
- Fix (recommended, local; it also deletes one leaf):
  1. In routines/spec.bend, add the high-water fact
     `def Hw(+st: Cr.Cir.State, +st2: Cr.Cir.State, +fi: U32, n: Nat) -> Bool:
     Nat.is_le(U32.to_nat(Lg.St.next(st2)), Nat.max(U32.to_nat(Lg.St.next(st)), Nat.add(U32.to_nat(fi), n)))`.
     It says that `next` grows only up to the routine's own budget.
  2. Add `Hw(st, st2, Hp.Cx.fi(x), N)` to the post of each routine that may take a cell, with N the
     same count as in its budget:
     - `push.spec`, `one.spec` :524, `call.frames`: N = 1 + |L|;
     - `copy.spec`: N = |L| + 1 + |AM.copy(t, es)|;
     - `walk.spec`: N = |L| + 2|tt|.
     `alloc.spec` and `make.spec` already give it, since they give the exact state.
  3. Add `U32.is_eq(Lg.St.next(st2), Lg.St.next(st))` to the routines that take no cell: `dec`,
     `pop`, `inc`, `swap`, `release_arg`, `release_all` (release and nth give their exact state).
  4. In moves/spec.bend, give the move's post the memory facts, so that each move law proves them
     while it steps. For example, `Next(x, st, s, o)` with
     `Next.is(..) && Nat.is_le(Me.Stat(st2), Me.Stat(st)) && Nat.is_le(Me.Mem.cells(st2), Nat.max(Me.Mem.cells(st), Me.Need(ds, st, s)))`
     for a next. This means one more parameter in the 27 move laws and in `round.sim`. Then delete
     `round.mem`. `asm.mem.next` takes the facts from round.sim's post. This is a small edit: in
     `asm.rnd`, the round's Q gains the conjunct.
  5. Add to `input.spec`'s post `Lg.Reg(st, free) == Some{0}` and the cache bound (at most 24 STATIC
     cells a byte that M.input meets, so ≤ 6144). Then delete `input.mem`. Its own-cell half follows
     from G2's law, since an empty free list gives `Mem.cells = |V.Live|`.
- Another route, if lanes S1 and S2 should not change: one generic law that runs the round again
  with the limit cut to Budget (exec does not look at the limit except to refuse a grow). It needs
  page facts (pages ≤ limit, 20·next ≤ 65536·pages) and gives the bound only up to a page (+3277
  cells; F still covers it). It is more work than the fix above.

### G2 (medium-high, gap): no stated law bounds the live cells by the term

- Where: memory/spec.bend (Need, :85) against the routine budgets (`I.Cells.bytes(fi, k + |L|)`,
  routines/spec.bend:279, :284, :367, and push/one/call.frames).
- Problem: every move law's Tot uses `Me.Budget(x, st, s)`, a function of `Stat(st)` and of the
  term's size. Every routine law that it calls allows out of memory below `fi + |L| + k`, where L
  is the list of live cells. To prove any move law that takes a cell (ev.app/let/unlet/tup/tup0/rwt/
  min/ref; ret.swap is free; ret.app.*, ret.fun.*, ret.let, ret.tupa, minb...), the prover needs
  `|V.Live(st)| ≤ Stat(st) + Term.size(AS.term(s))`. No law states it, and it is not a routine
  fact: it comes from `Part`, `Cov` and the view's footprint (one cell or fewer for each node of the
  term, since the read shares cells; one frame cell for each frame node of `AF.plugs`). G1's fix
  needs it too. Without it, 27 lanes would each have to find and prove the same heap lemma.
- It is TRUE. Under `MInv` (no chain, the focus the only root), `Cov` puts each non-STATIC live cell
  in the footprint of the focus or of a frame's terms, or makes it a frame cell. Every STATIC own
  cell is counted by `Stat`. A view visits at most one cell for each node of the term that it
  reads. A frame cell matches the node that `AF.plug` adds (App, Let, Tup, Rwt and its two terms
  P, f, Min). Computed: it holds at every round of the runs below.
- Fix: state it once, in memory/spec.bend:

  ```
  # LAW: the live cells of a state that MInv finds are at most its STATIC own
  # cells and one cell a node of its whole term
  law live.le:
    for +x: Hp.Cx
    for +st: Cr.Cir.State
    for +s: A.AS
    for +iv: {R.MInv(x, st, s) == True{} : Bool}
    {Nat.is_le(List.length(&2, U32, Hp.V.Live(st)), Nat.add(Stat(st), Pg.Term.size(A.AS.term(s)))) == True{} : Bool}
  ```

  With it, the budgets close. I tallied the worst move, a call (mv.ret.app.call), from the routine
  budgets:

  `|L0| (≤ Stat + |t|) + spine args (≤ |t|/2) + walk 2|tt| (≤ 2 big) + 1 + |AM.copy| (≤ |t'|) + 1 ≤ Stat + 16 + 3·max(|t|, |t'|) + 3·big = Need`.

  The lam, let and unlet copies need `|L0| + 1 + |copy|`, which is also below Need. So the move
  laws, as stated, can be proven from the routine laws plus `live.le`.

### G3 (low): the memory-edge smoke cannot tell where it ran out of memory

- Where: s4_smoke.bend at d78fbea, `smk4.run.edge` (the expected value is
  `SR4Out{True{}, None{}, True{}}`, and `smk4.res` drops the round count).
- Problem: an out of memory in `M.input` (`smk4.started`) gives the same `SR4Out` as one in a
  round. So the test does not show that a round reached the edge. The S4 agent is now rewriting
  this case (the uncommitted diff makes f return a λ "a value by its form: one round"), which
  suggests that the committed version did not exercise what its comment says.
- Fix: also compare the round count (`SR4.n > 0`), or return SR4 and not SR4Out for that case.
  Also: s4-handoff.md ends with "Memory edge: see the end of this file", but that section is
  missing. Add it, or drop the reference.

### N1 (note, no change): why Need has 3×, as I see it

The handoff explains 3·max by the true peak. The true peak of a call is about
`|t| + |t|/2 + 2·big` (the copy makes at most |leaf| ≤ big new cells), so 2× would cover it. The
3× is needed only because the routine laws bound coarsely: `copy.spec` bounds by |AM.copy(t, es)|
(locals counted again for each use, ≤ |t'|), and `walk.spec` by 2|tt|. That is a sound reason to
keep 3×, and F still covers it (see below). Only the reason in s4-notes item 2 should say so.

### N2 (note): `budget.need` has premises that it does not use

`iv: MInv(..)` is not needed (the arithmetic uses `hm`, `hst`, `hC`, `ht`, `he` and Start's
`first`). It is harmless, since the assembly has MInv at hand. Keep it, or drop it to save P3 a
binder.

## enough_memory: does Budget ≤ F hold? (3.9.1.4, 3.3.8)

Yes. Here k is the image's cell count and first is the first own cell.

- `Img.cells`: 290 prefix cells (10 labels, 4 pairs, main's cell, 256 cache cells, 19 table cells),
  then one cell for each node of each def body. So k = 290 + Σ|v|.
- `Cir.first`: 20·first ≤ 20(k + 1) + len + 19.
- `|start(i)| = 5 + 72·|i|` (67 nodes a byte, plus 5 for each Con), so len ≤ S/72.
- `Form.size.term` gives at least 3 nodes for each term node (Efq and Rfl have 3, everything else
  more). So size ≥ 3·Σ|v| ≥ 3·big.

Then, with C ≤ 6144 and Mem.cells ≤ Peak:

`Budget ≤ 20·(first + C + 16 + 3S + 3·big) + S ≤ 20·Σ|v| + 60·big + 61.02·S + 129,100`

and

`F = 64·size + 64·S + 16,777,216 ≥ 192·Σ|v| + 64·S + 16,777,216`.

The margin is at least `112·Σ|v| + 2.98·S + 16.6 M`, so it is never tight.

- `input.need`: `20·(first + 1 + 27·|i|) ≤ 20·Σ|v| + 541·|i| + 5,900`, and 541·|i| ≤ 7.6·S. True.
- `start.ok`: 20(k + 1) + len ≤ F − 2^24 + 5,820 < 4294967280, and pages(end) ≤ lim, since F ≤
  65536·min(m, 65536). True. Without `Img.small`, a book whose image wraps U32 has F > 2^32, so the
  premise `big` is false and the law holds vacuously.
- The U32 cell limit of `Cir.exec.alloc` (next < 214748364) is reached only when
  20·(fi + Need) > 2^32 ≥ Lim, which is out of memory below Budget. That agrees with round.sim.

## Computed checks (review-scratch/rv4_smoke.bend)

(Running when this section was written; the results follow below once it ends.)

## Statements checked and fine

memory/spec.bend:
- `eval.stops` (:135): true (Eval.step of a value is None; proven).
- `round.mem` (:143): true (see G1 for its provability).
- `input.mem` (:156): true. After M.input: the cache has ≤ 24 STATIC cells a distinct byte; the
  list has 3 cells a byte; then the focus. So Mem.cells ≤ Stat + 3|i| + 1 ≤ Peak for every n,
  since largest ≥ |start|.
- `need.peak` (:180): true. `Eval.run` gives Some only after exactly n steps, so CSteps(j) for
  j ≤ n is one of the run's terms (canon.size keeps the size). At j = n the term is a value, so
  StepSize is 0 (eval.stops, canon.vals). For j < n the step is CSteps(j+1).
- `budget.need` (:200): true, with a wide margin (above).
- `input.need` (:228): true. `need.lim` (:245): true (proven). `start.ok` (:262): true. It mirrors
  Cir.result's three checks exactly (pages ≤ m, length32, alloc.pages with min(m, 65536)).
- `code.fits` (:274), for any St0: true.
  - M.input always takes a fresh cell first (all registers are 0 in St0), so 20·next ≤ 65536·pages
    from then on.
  - Each emit checks next < 214748365 and that b = at(next) + outn does not wrap, then the room for
    byte b.
  - So at a halt 0, at(next) + outn ≤ 65536·pages, and `Wasm.fits` holds. That includes the
    wrap-to-0 case at exactly 2^32, which needs 65536 pages, and the room check gives them.
  - The machine halts only with 0 or 2 (no halt 1).
- Definitions: Mem.cells, Stat (bit 10 = STATIC; FREE cells have header 46, no STATIC), Need,
  Budget, Peak, Start.ok, Fits.halt (field order of Cir.State checked). Each matches its comment.

moves/spec.bend:
- `Vb`, `Next`/`Next.is` (False on a halt), `Halt`/`Halt.is`: exact. A halt 0 compares the reversed
  output byte for byte, as Cir.ended does. A halt 2 ignores the output, as Cir.ended does.
- `round.sim` (:107): true as far as I can check by hand. It is proven from the move laws, and the
  kernel confirms the dispatch over every term former and frame kind.
  - Its Budget covers every routine budget once G2's law is given.
  - It covers the output: `Out.budget = 20·next + |v|` is Budget's second component, and the bytes
    are fewer than the nodes.
  - It covers the U32 cell limit.
- `inv.vb` (:116): true. `V.tm` checks `¬VALUE ∨ Eval.vals(ds, t, False)` at each node
  (heap/spec.bend:321), and MInv reads the focus at depth 0 as s.focus.
- The 27 move laws: each outcome is AM.move's reduct in its case (the kernel accepts round.bend's
  conversions). I compared each against the code. KNOWN of the call's arguments (`live(q)`) agrees
  with `AM.args`. The Prj redex pushes b then a. A Mat miss pushes a KNOWN Lab frame. Swap headers
  have q and no flags (min_a: Q0). Let checks DATA only at Q2. Rwt checks the Rfl tag. Min checks
  both labels and their quantities. Out needs pairs at Q1, exactly as `Program.unbytes` does.
  - `mv.ev.val`'s `Vb ∨ former` is M.ev's single test.
  - `mv.ev.unlet` needs no fits test, since the let is dead.
  - The Q0 / Q1 / Q2 splits of Let and Tup match `M.q ≠ 0`.
- `call.frames` (:554): true. Its text is M.call's loop (`smk4.call.eq`). Each round of the loop:
  - push takes the head of the free list, or a fresh cell when the list is empty, then release
    frees an argument cell. So 1 + |L| bounds every alloc, and |L2| ≤ |L|.
  - The pointer moves from the argument cell's field 2 to the frame's field 2. Released cells are
    FREE, which have no counted pointers.
  - KNOWN comes from the argument's header.
  - Call.fs pushes the chain's head first, the deepest, so `Call.fs(rev(xs), fs) = AM.frames(xs, fs)`.
  - `Same` lists exactly the registers that it writes (wa, wh, free, fr, sp).

Assembly and top: `Asm.J = MInv ∧ AS.ok0`; inv.vb completes AS.ok for am.ok. `Asm.Ms`/`Asm.Mf` carry
exactly what need.peak, budget.need and round.mem need. Cir.result's out-of-memory checks before
the program are excluded by start.ok. M.input's are excluded by input.need ≤ need.lim. mach.safe
uses code.fits for a halt 0 and `Lg.tot.any` for "never a trap". The four `mach.*` statements are
unchanged, so `proof.bend` gives no_wrong_result, no_other_failure (uniform, through layer A's
`mach_wasm.uniform` hole, which is not S4's), enough_memory and in_subset from them.
