# P3 lane plan (127 holes, from holes.md at S4's merge)

Rules: one agent per file at a time (the merge queue registers files per lane). Every prover: gen2
first (`ask --file <file> <def>`; `--ind` is default; `--wp` for Tot/WP goals), only proof bodies and
new helper defs in its own files, submit through the merge queue after each closed law (small batches
merge early), then `git merge feature/redesign` and continue. A statement that looks false goes to the
coordinator with the evidence, never "fixed" by the prover.

## Wave 1: start now (gen2 already helps here)

| Lane | File(s) | Holes | Agent | Notes |
|---|---|---|---|---|
| L-canon | canon/impl.bend | 9 | Opus for `canon.step` (D6 key lemma), Sonnet for the rest | pure term meta-theory |
| L-am | am/impl.bend | 2 | Sonnet | `am.ok`, `am.walk_eval` (hand-checked true by the reviewer) |
| L-image | image/impl.bend | 6 | Sonnet | salvage from old image_* files (`git show 4ebef88:...`), td-imgstart helpers |
| L-count | heap/count.bend | 6 | Sonnet | |
| L-memory | memory/impl.bend | 7 | Sonnet | port old memory_bound arithmetic |
| L-logic | logic/impl.bend | 8 of 11 | Sonnet | `--ind` closes cell(s).get_set; frame.regs/fixed wait for the injectivity tactic |
| L-header | header/impl.bend | 13 of 18 | Sonnet | `--ind` closed 8 mask laws on copies: paste; hd.*_of after and_shl/and_low |
| L-view | heap/view.bend | 18 | Sonnet x1 (split later if slow) | frame/deeper/canon/rc laws: induction on the view |

## Wave 2: after gen2 `--wp` reads cells (in progress)

| Lane | File(s) | Holes | Agent |
|---|---|---|---|
| L-prims | routines/prims.bend | 12 | Sonnet |
| L-ev | moves/ev.bend | 10 | Sonnet |
| L-ret | moves/ret.bend | 8 | Sonnet |
| L-call | moves/call.bend | 10 | Sonnet |
| L-round | moves/round.bend | 1 (`inv.vb`) | Sonnet |

## Hard leaves: one strong agent (Opus) each, in parallel with the waves

| Leaf | Where | Why strong |
|---|---|---|
| loops: nth, dec cascade, copy, walk, out, input, release_all | routines/*.bend, prims | a loop invariant must be invented (gen2 prints the tot.while obligations + skeleton) |
| fuel laws: tot.any, tot.frame, tot.frame_out | logic/impl.bend | existential fuel, not induction |
| 5 mask laws: and_shl, shr_shl, and_low, shr_low, sub_bit | header/impl.bend | borrow / commutation word lemmas |
| mach_wasm.uniform | Cir/runs_as_cir.bend | layer A: a fuel bound inside simulation_host |

## Scaling

Start wave 1 (8 lanes) + 2 strong agents (loops; fuel+mask). Measure for the first hour: holes closed
per hour per lane, gen2 asks and hits, merge-queue pass rate. Then add wave 2 when `--wp` lands, split
slow big files (heap/view, header, prims) into 2 proof files each, and scale to ~15–20 agents if the
spend limit allows.
