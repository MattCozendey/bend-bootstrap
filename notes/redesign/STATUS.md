# Redesign status (handoff file)

Updated: 2026-11-04 09:40 (America/Sao_Paulo). Keep this file current: whoever coordinates updates it after every merge, phase change or agent start/stop, and commits it (this folder is a git repo: `git -C <this folder> commit -am "status: ..."`).

## Goal

A self-hosted Bend compiler that can be trusted, PROVEN (AGENTS.md section 3), the objectively best one. The lead gave full freedom below the milestones of AGENTS.md 3.11, AGENTS.md included. Hard constraint: milestones 1–4 must still hold after every merge (`src/milestones.ts`, all 5 steps). Never run `--verdict` from agents (only the lead's final check, AGENTS 3.2.5). main is not touched; all work lands on branch `feature/redesign`.

## Documents (this folder: C:\Users\mathe\source\repos\bb-wt\reports\redesign\)

| File | What |
|---|---|
| STATUS.md | this file: where everything is, who does what, what is next |
| redesign-plan.md | THE plan (architect, 2026-11-04): target architecture, machine changes, exact statements, phases P0–P7, gates G1–G5, lanes |
| design-assessment.md | why: the design is sound, the difficulty is accidental (D1–D9 design, P1–P9 proof pitfalls) |
| law-audit.md | audit of spec.bend + Lean theorems against AGENTS.md (F1–F8); all approved fixes are done (w/laws) |
| holes.md | hole ledger (P0 writes it; every gate compares the TODO count with it) |
| p0-measure.md, p1-notes.md, p1-handoff.md | P0/P1 outputs (being written) |
| s3-notes.md, s3-handoff.md | skeleton lane S3 outputs (being written) |
| laws-scratch/ | logs of the law-fix agent |

## Branches and worktrees (repo C:\Users\mathe\source\repos\bend-bootstrap; worktrees in C:\Users\mathe\source\repos\bb-wt\)

| Branch | Worktree | State |
|---|---|---|
| feature/redesign | bb-wt/redesign | integration branch, PUSHED to origin (github MattCozendey/bend-bootstrap), tracking origin/feature/redesign; push after every merge (`git push origin feature/redesign`), and refresh the docs snapshot in the branch at `notes/redesign/` (copy *.md and tools/ from this folder, commit) before pushing. Has: gen2 upgrade (d57bb26), law fixes (6693442), P0 census.ts (d94bad2), P1 machine code (4908672) + old proof tree deleted (ec0f1a0), S3 merged (9daf8f5), AGENTS 3.10.3 fix (ef4c444), gen2 shared servers merged (1e0c483), S2 review fixes merged (bec2fe8), gen2 round 2 merged (9aaf458), gen2 --wp merged (015dba0, flag-only), S2 follow-up merged (5c86a0d: Wasm imports), S2 merged (967db15: heap/image/routines/Inv, 40 laws open; Mach.code vs AM.move whole-run smoke passes), S1 merged (7122c61: kit + 39/50 logic laws proven; 11 logic + 18 header laws open). All gates G1–G5 pass on P1; main closure: 35 files, 5 holes (4 runs_as_eval + mach_wasm.uniform) |
| w/gen2-up | bb-wt/gen2-up | DONE, merged. gen2: bounded errors, 1 GB stack, match-fix helper, --find, --lemmas, --hole, fast reload |
| w/laws | bb-wt/laws | DONE, merged. in_subset law (F1), uniform no_other_failure (F2, one new layer-A hole `mach_wasm.uniform`), trusted_binary + 3.8.7 script (F3), AGENTS.md 3.3.8/3.6.1.4/3.7.1/3.9.1.3.4 |
| w/s3 | bb-wt/s3 | DONE, MERGED (9daf8f5). canon: 14 laws (5 proven), am: 2 laws; smoke all pass; G1 pass. See s3-handoff.md |
| w/td-prjtup, w/td-imgstart | bb-wt/td-* | gen2 test drives on OLD files (deleted by P1). Keep for salvage (img_ok helpers → lane F7) |
| feature/deepseek-provers | WSL ~/ds/repo | ON HOLD. DeepSeek output judged unreliable; do not merge without full re-gating |

## Who works on what (now)

| Agent | Task | Where |
|---|---|---|
| Skeleton S4 (Opus) | moves.bend assembly COMPLETE (mach.safe/sound/complete/memory proven from the laws; runs_as_eval bodies filled; G3 call.frames); in final gates (G3 milestones running 09:32); then holes.md | bb-wt/s4 on w/s4 |
| gen2-wp (Opus) | round 3: wp.alloc/emit, early stop, tot.while obligations + invariant skeleton, S2 facts; next merge | w/gen2-wp |
| gen2-ind (Opus) | smarter induction behind `--ind` (functional induction, generalize before inducting, helper-lemma proposals, word induction on width, early give-up); module gen2_ind.ts | bb-wt/gen2-ind on w/gen2-ind |
| Coordinator (Claude Code session) | reviews reports, merges, starts phases, keeps this file | — |

## Next steps (in order)

0. NOW (09:40): S4 final gates -> merge w/s4 -> publish holes.md per file -> plan P3 lanes from it -> start the swarm small (measure holes/hour with gen2 --wp --ind), then scale. Merge w/gen2-wp and w/gen2-ind when their rounds finish (flag-only; bench + crash replay must hold).

1. DONE: P0, P1, S3 merged.
2. (S3 notes for S2/S4 below.) Notes for S2/S4 from S3: plan's canon.subst_below was false for n < |es| (fixed with premise |es| <= n; call-leaf copies use canon.subst_closed), so copy.spec with wt is right only for a poison-free (STATIC) source; a halt 2 carries out = [] so S4's Halt(o) compares output only for status 0; AM.move vs Mach.round() smoke check still to do (needs P1 code) — S2 or S4 runs it.
3. S1 DONE+MERGED (see s1-handoff.md; NOTE: proof books must import logic/impl.bend and header/impl.bend, not only specs — bend2 rejects use of an unfilled law; gate.sh reuses one temp file per basename and misses law-filling defs: kernel-check those by name). S2 DONE+MERGED (967db15). RUNNING: S4 and the S1–S3 statement review. (heap, image, routines, Inv) — need P1's handoff (register numbers, header layout, routine names).
4. Skeleton lane S4 (moves, memory, assembly moves.bend proven from the laws; runs_as_eval bodies) after S1–S3.
4b. RUNNING (branch w/gen2-wp, from w/g2pool; module src/Shared/scripts/gen2_wp.ts behind flag `--wp`, default once measured): the original gen2 agent builds a WP-stepping tactic on S1's Tot/WP/Cir.writes rules (plan: ~60% of holes are Cir-stepping goals), plus `{==}`-closure of computable frame Bools. Before P3.
5. Statement review by a second strong agent + smoke checks (biggest risk: a false statement).
6. P3: ~15 prover lanes (F1–F15 in the plan §5.5), Haiku/Sonnet + gen2, Opus reviewer per ~4 lanes. Add a lane for layer-A hole `mach_wasm.uniform`.
7. P6 (word cells) NOT needed: P0 census: self-compile peak 0.72 GiB on the old machine, 10,797 pages (0.66 GiB) after P1; pruned book 761,548 bytes (1.1% of 2^26).
8. P4 close (0 holes, `bend -o src/main.bend` works) → lead runs `--verdict`. P5 sweeps. P6 word cells only if P0 census needs it. P7 self-host run.

## Infrastructure (from g2pool, DONE; details in g2pool-notes.md)

- WSL KEEP-ALIVE IS MANDATORY: WSL shuts down when no wsl.exe is attached, killing servers and jobs. Start once from Windows PowerShell: `Start-Process -WindowStyle Hidden wsl.exe -ArgumentList '-d','Ubuntu-24.04','-e','/home/math/lead/g2serve.sh','hold'` (running since 08:17).
- gen2 servers: `wsl.exe -d Ubuntu-24.04 -e ~/lead/g2serve.sh start <clean checkout> <file> [--replicas K]` (systemd units, 3G each, 10G total, no heavy.sh slot); agents: `bun src/Shared/scripts/gen2.ts ask --file <their copy> <def> [--partial|--lemmas|--check <def>]`. 4–8 agents per server; 30–60 agents fit.
- Merge queue: `bun C:/Users/mathe/source/repos/bb-wt/reports/redesign/tools/mergeq.ts lane|add|run|status|result|land|check ...`; state under mergeq/ (resumable from `status`). Enforces prover rules, G1 incremental (law fills kernel-checked by name), G5, G2 per batch, G3 only when needed.
- ~/lead/gate.sh now symlinks tools/gate.sh (unique temp names; checks law-filling defs; MISSING on unknown names). Original: ~/lead/gate.sh.orig-g2pool.
- Merge order: w/g2pool (merged) before w/gen2-wp.

## Rules for every agent

- GEN2 FIRST (lead's rule): every agent that proves anything tries gen2 first (`ask --file <file> <def>`, `--wp` for Tot/WP goals, `--lemmas`, `--partial`, `--find`), and only then proves by hand; keep a tally (asked/closed/advanced/misleading) in its notes for gen2's development. P3 prover briefs must include this.

- Commit work in progress on your own branch often (at least after each coherent piece), so nothing is lost if you stop (an org spend limit stopped all agents once).
- Keep your handoff/notes file in this folder current.
- Gates: plan §5.0 (G1 gate.sh per file, G2 main.bend loads with the ledger's TODO count, G3 milestones, G4 run.ts + computed layer-A checks for machine changes, G5 hygiene). Gate scripts: WSL ~/lead/ (gate.sh, heavy.sh with 3 shared slots, milestones.sh).
- In worktrees use `git status --ignore-submodules=all`; never change the `bend` submodule; never set git config in a worktree (it writes the shared config).
- gen2 (src/Shared/scripts/gen2.ts): `serve` once via heavy.sh, then `ask --check`, `ask <def> --lemmas`, `--hole N`, `ask x --find RE`. The gate is the only judge.

## Decisions log

- 2026-11-04: statement review S1–S3 (review-s123.md): 3 false statements (F1 critical fv saturation, F2 memory edge, F3 count wrap) + 4 gaps (G1–G4); all local fixes; routed to S2 (F1–F3, G1, G2, G4) and S4 (G3). Canon, am.ok, am.walk_eval verified true; 9 extra machine-vs-AM runs pass.

- 2026-11-04: --wp measured: 0/18 S2 routine holes closed; stops at register reads with no fact (needs kit reg.some), unnamed Wasm ops (import), calls to routines with own laws (next gen2 step), loops (reviewer writes invariants). Merged flag-only.

- 2026-11-04: gen2 trial by S1: base gen2 0/17 holes (misleading partial, noisy hints); WIP --wp stepper useful (stepped 2 sets in 0.1 s) but stops at field reads -> fed back to gen2-wp.

- 2026-11-04: merge-queue gating: G3 (milestones, ~12 min) only when a batch touches files outside the proof-only set (Machine/* proof files except impl.bend, with the prover-rule check passed), plus a safety-net run every ~10 batches and at phase boundaries. Target ~2 min per proof-only batch.

- 2026-11-04: P0: 3.4.1.4 already holds (0.7 GiB); P6 dropped; AGENTS 3.10.3 updated (ef4c444).

- 2026-11-04: P3 policy: prover agents iterate with gen2 ONLY and never run the gate; the orchestrator gates in batches via the merge queue (w/g2pool). WSL has 15 GB: raising it needs `wsl --shutdown` (kills running jobs), so not done mid-phase.

- 2026-11-04: DeepSeek provers set aside (unreliable judgment; bogus copy.post refutation). copy.post law stands.
- 2026-11-04: internal phase specs (definitions/move_kit/copy_substitution) are not frozen; only spec.bend laws + Lean theorems are.
- 2026-11-04: redesign adopted per redesign-plan.md: D1–D7 all yes, D8 frame theorem instead of Cir procedures, word cells only if P0 census needs them (> ~3.5 GiB).
- 2026-11-04: law fixes F1–F6 approved and merged; engine exactness done as "one fuel for all answer lists" (covers infinite answer sequences).
