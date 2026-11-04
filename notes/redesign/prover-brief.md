# Prover brief (P3): read this fully before you start

You fill `?TODO` holes in Bend2 proof files of the redesigned machine proofs of a trusted Bend compiler.
Goal of the project: a self-hosted Bend compiler that is PROVEN. Your lane (branch, files, gen2 ports)
is in your task message. Project state: `STATUS.md` in this folder
(`C:\Users\mathe\source\repos\bb-wt\reports\redesign\`). Lane plan: `lanes.md`. Open holes: `holes.md`.
Language: read the skill `bend2` (or `.agents/skills/bend2/SKILL.md` in the repo). The handoffs
(`s1-handoff.md`, `s1-names.md`, `s2-handoff.md`, `s3-handoff.md`, `s4-handoff.md`) say what each layer's
names mean.

## Setup (Windows; repo C:\Users\mathe\source\repos\bend-bootstrap)
- From the repo root: `git worktree add ../bb-wt/<lane> -b <branch> feature/redesign` (your task message
  gives `<lane>` and `<branch>`). Work only there. Use PowerShell git, or Git Bash git with
  `-c submodule.recurse=false`; for status use `git status --ignore-submodules=all`. Never touch `bend`.
- Commit with `git -c user.email=mpereira@blueboltsolutions.com commit ...` (never `git config`); end each
  message with `Co-Authored-By: Claude <noreply@anthropic.com>`.

## Rules (the merge queue enforces them mechanically; breaking one gets your work dropped)
- Change ONLY your lane's files. In them: replace `?TODO` bodies with proofs, and add new helper defs
  (place each helper ABOVE the def that uses it: bend2 only lets a def call defs above it).
- Never change a statement (a def's header/type), a def without `?TODO`, an import line (adding an import
  is fine), a `law`, or add `@unsafe`. Never delete a file.
- If a statement looks FALSE or unprovable as stated: stop on it, write the evidence (a counterexample, or
  the exact stuck subgoal) in your notes file, and move to the next hole. Never weaken anything.
- A proof may use any law, proven or not (every law is a separate hole).

## gen2 FIRST (the lead's rule), then by hand
The gen2 servers for your files are already running (ports in your task message). From your worktree:

    bun src/Shared/scripts/gen2.ts ask --file src/<your file> <def>            # try to prove (induction is on)
    bun src/Shared/scripts/gen2.ts ask --file src/<your file> <def> --wp       # code-stepping goals (Tot/WP)
    bun src/Shared/scripts/gen2.ts ask --file src/<your file> <def> --partial  # best partial, open leaves
    bun src/Shared/scripts/gen2.ts ask --file src/<your file> <def> --lemmas   # candidate lemmas per hole
    bun src/Shared/scripts/gen2.ts ask --file src/<your file> --hole N <def> --lemmas
    bun src/Shared/scripts/gen2.ts ask --file src/<your file> x --find <regex> # find defs by name
    bun src/Shared/scripts/gen2.ts ask --file src/<your file> --check <def>     # bend2's check of one def

- Paste what gen2 proves (helpers too, in the printed order). Add `--budget 4000` for big goals.
- gen2 is never the judge; the gate is. But a def that passes `--check <def>` almost always passes.
- Check one def at a time (`--check <def>`), not the whole file (it holds the server for everyone).
- Do NOT run gate.sh, milestones, smoke files or bend2 on main.bend: the coordinator gates.
- Keep a tally in your notes file: holes asked, closed by gen2, advanced by gen2, misleading answers.

## Submitting (after EACH proven law: small batches merge early)
1. `--check <def>` passes for the def and its helpers. Commit.
2. `bun C:\Users\mathe\source\repos\bb-wt\reports\redesign\tools\mergeq.ts check <branch>` (the rule check).
3. `bun C:\Users\mathe\source\repos\bb-wt\reports\redesign\tools\mergeq.ts add <branch>`.
4. The coordinator's loop gates and lands queued lanes every ~10 min. See your result with
   `bun ...\mergeq.ts result <branch>`. If it failed, fix and re-add.
5. Every so often, `git merge feature/redesign` into your branch (others' proofs land there).

## Notes and the end
- Notes file: `C:\Users\mathe\source\repos\bb-wt\reports\redesign\p3-<lane>-notes.md`: per hole, its status
  (proven / stuck: why / suspected false: evidence), plus the gen2 tally. Commit that folder after
  updating: `git -C C:/Users/mathe/source/repos/bb-wt/reports/redesign add p3-<lane>-notes.md` then
  `git -C ... commit -qm "p3 <lane>: ..."` (add only your own notes file).
- Stop when every hole of your lane is proven, or the rest are stuck; then report: proven (list), stuck
  (why), suspected false (evidence), gen2 tally.
