# Redesign handoff

Start here: `STATUS.md` (goal, rules, branches, who does what, next steps, decisions log).

- This folder is a snapshot, refreshed at each push of `feature/redesign`. The live copy is
  `C:\Users\mathe\source\repos\bb-wt\reports\redesign\` (a local git repo) on the lead's machine.
- The plan: `redesign-plan.md`. Why: `design-assessment.md`, `law-audit.md`. Review of the
  skeleton statements: `review-s123.md`.
- Per lane, what exists and what the next writer must know: `p1-handoff.md`, `s1-handoff.md` and
  `s1-names.md`, `s2-handoff.md`, `s3-handoff.md`, `s4-handoff.md`; decisions in the `*-notes.md`.
- gen2 (the proof assistant for the prover swarm): `src/Shared/scripts/gen2.ts` header, plus
  `gen2-wp-notes.md`, `gen2-ind-notes.md`, `g2pool-notes.md` (shared servers, merge queue).
- Merge queue and gate tools: `tools/` (`mergeq.ts`, `gate.sh`, `g1.sh`, `g3.sh`, `g2serve.sh`,
  `kmap.awk`). On the lead's machine they are installed in WSL `~/lead/`.
- Open holes: `holes.md`.
- Unmerged agent branches are pushed to origin as `w/*` (work in progress; they merge into
  `feature/redesign` through the gates in `STATUS.md`).
