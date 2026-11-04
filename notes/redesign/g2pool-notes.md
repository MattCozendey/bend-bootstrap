# g2pool: swarm infrastructure for P3 (notes)

Branch `w/g2pool` (worktree bb-wt/g2pool, from feature/redesign 9daf8f5): gen2.ts only. The
orchestrator's tools live in this folder (`tools/`, versioned here, outside the repo and the trust).

## What exists

| Piece | Where | What |
|---|---|---|
| gen2 shared servers | src/Shared/scripts/gen2.ts (w/g2pool: 2ee7768, 4fd2bd4) | `ask --file F` sends the agent's own text; the server re-parses only the entry's defs on top of its loaded imports; asks are queued one at a time; new imports load; differing import files are named in a NOTE; `--write` lands through the client; one `[ask]` log line per ask; `ask` loads no bend.ts (starts in ~0.3 s, works without a `bend` link). Header section SHARED SERVERS. |
| server launcher | tools/g2serve.sh = WSL `~/lead/g2serve.sh` (symlink) | each server a systemd user unit `g2pool-<port>` in `g2pool.slice`: own MemoryMax (default 3G, no swap), Nice 10, Restart=on-failure; the slice caps all servers at 10G; NO heavy.sh slot. Registry `C:\Users\mathe\.g2pool\<port>.json` (= WSL `~/.g2pool`), read by `ask --file`. `--replicas K` with per-worktree affinity. |
| merge queue | tools/mergeq.ts (Windows bun), tools/g1.sh, tools/g3.sh, tools/kmap.awk (WSL) | state in `mergeq/` (queue.txt, lanes.txt, state.json, results/, batches/, log.txt); scratch worktree bb-wt/mergeq; the test run's state is archived in mergeq/test-2026-11-04/ |
| gate.sh fix | tools/gate.sh = WSL `~/lead/gate.sh` (symlink; original: `~/lead/gate.sh.orig-g2pool`) | same output and verdict; (1) the lowered temp file is named by worktree + HOST's whole path (logic/impl.bend and header/impl.bend gated at once no longer overwrite each other); (2) law-filling defs (`def Lg.x`, lowered `spec.x`) are kernel-checked, through kmap.awk; an unmapped name prints `MISSING`. On logic/impl.bend at 7122c61: the old script checked 44 of 94 defs (the 50 fills silently skipped, 0 fail), the new one 94 (11 FAIL = exactly the 11 open law holes). |

## Commands

Orchestrator, once per session (from Windows PowerShell; WSL stops when no wsl.exe is attached and
takes every server with it; WSL's interop is off, so WSL cannot start this itself):

    Start-Process -WindowStyle Hidden wsl.exe -ArgumentList '-d','Ubuntu-24.04','-e','/home/math/lead/g2serve.sh','hold'

Servers (WSL; run from Windows as `wsl.exe -d Ubuntu-24.04 -e ~/lead/g2serve.sh ...`). Start them from
a clean worktree of feature/redesign (e.g. `git worktree add --detach ../bb-wt/pool feature/redesign`
plus a `bend` link), one per lane file:

    ~/lead/g2serve.sh start /mnt/c/Users/mathe/source/repos/bb-wt/pool Compiler/Machine/heap/view.bend [--replicas 2] [--mem 3G]
    ~/lead/g2serve.sh list | log PORT | restart PORT|FILE | stop PORT|FILE|all

After a merge into feature/redesign: `git -C bb-wt/pool checkout --detach feature/redesign`, then
`g2serve.sh restart <file>` for each server whose imports changed (asks name differing imports).

Prover agent (its own worktree from feature/redesign; Windows or WSL; never the gate):

    cd <worktree>
    bun src/Shared/scripts/gen2.ts ask --file src/Compiler/Machine/heap/view.bend --check view.deeper
    bun src/Shared/scripts/gen2.ts ask --file src/Compiler/Machine/heap/view.bend view.deeper --partial
    bun src/Shared/scripts/gen2.ts ask --file src/Compiler/Machine/heap/view.bend view.deeper --lemmas
    bun C:\Users\mathe\source\repos\bb-wt\reports\redesign\tools\mergeq.ts check <its branch>   # prover rules only

Prefer `--check <def>` to a whole-file `--check` (1.5 s on a 2,400-entry file, and it holds the queue).

Orchestrator, merge queue (Windows, from anywhere):

    bun C:\Users\mathe\source\repos\bb-wt\reports\redesign\tools\mergeq.ts lane w/F3 Compiler/Machine/header/impl.bend
    bun ...\mergeq.ts add w/F3             # also: add <branch> --owner [--g4-done] for a statement owner
    bun ...\mergeq.ts run                  # gate + land one batch (all queued lanes)
    bun ...\mergeq.ts run --g3 force       # phase boundary
    bun ...\mergeq.ts status | result w/F3 | land [--ff-checked-out] | drop w/F3

`run` commits `mergeq/` in this repo at the end of each batch. A lost context resumes from
`mergeq.ts status` (queue, running lock, last batch, results, passed-but-not-landed batch).

## The batch, and when G3 runs (coordinator's policy, 2026-11-04)

1. Prover rules per lane, on the lane's own changes (from its merge base with the target): only its
   registered files (lanes.txt; an unregistered lane: only proof files, see below, not registered to
   another lane); no deleted file; every base item (def, law, type) keeps its header; an item with no
   `?TODO` keeps its whole text; no import removed; no new `law`; no new `@unsafe`. New defs/types may
   be added; an open def's body may change.
2. Merge each passing lane `--no-ff` into the scratch worktree bb-wt/mergeq (detached at the target).
3. G1, incremental, in parallel over heavy.sh's 3 slots (g1.sh per changed .bend file): bend2
   `--check-only` (only the TODO count), lower, kdiag3 on the changed or added defs only, by name
   (law fills `C.x` mapped to `<ns of C>.x`, e.g. `spec.canon.step`); every name must be found
   (kdiag3 skips unknown names silently, so the checked count is compared); a FAIL is accepted only
   on a def that still has a `?TODO`. Cached by the text of the file, its import closure and the
   names: a re-merge gates only what changed.
4. G5: no def/law/type name in two files of the closure of main.bend and of every .bend under
   src/Compiler/Machine/ (only clashes that touch a changed file count; law fills are not names); no
   import of a missing file.
5. A lane that fails 1-4 is dropped and the batch is merged again without it.
6. G2 once per batch: `bend2 --check-only src/main.bend` loads and its TODO count equals the `?TODO`
   count of main.bend's import closure; the result prints the old and new count (update holes.md).
7. G3 (milestones, ~12 min, g3.sh in ~/bb under a lock, ~/bb's checkout restored) only if:
   - a lane of the batch is not proof-only, or
   - `--g3 force` (always before a phase boundary), or
   - safety net: 10 batches or 24 h since the last passing G3 (the first batch runs it).
   **Proof-only** = a prover lane (not `--owner`) that passed the rules and changed only `.bend`
   files under `src/Compiler/Machine/`, other than `Machine/impl.bend` and any `*/spec.bend`.
   **Triggers G3:** any other changed path: Machine/impl.bend, any spec.bend, Cir/*, Compiler/
   spec.bend, impl.bend, proof.bend, img_small.bend, need_big.bend, Eval, Book, Program, Wasm,
   main.bend, every .lean file, tests, any .ts, AGENTS.md; and every `--owner` lane. Why a proof-only
   change cannot affect G3: milestones 1-3 read the Lean files and the trusted defs of main.bend's
   book (Eval/Book/Program/Wasm/Compiler impl), 4-5 read Wasm and the host; G5 covers name clashes.
8. Land: the target moves to the batch's last merge by compare-and-swap on the tip the batch started
   from. If a worktree has the target checked out (today bb-wt/redesign has feature/redesign): not
   landed, `mergeq.ts land` later; or `--ff-checked-out`, which fast-forwards that worktree only if it
   has no uncommitted change. A failed G2/G3 holds every merged lane in the queue (they cannot be
   told apart); a failed lane leaves the queue with its result file (`mergeq.ts result <branch>`).
   An `--owner` lane that changes Machine/impl.bend is refused until G4 was run by hand (`--g4-done`).
   Not automated: `bun check` when an owner lane changes TypeScript.

## Measurements (2026-11-04)

Servers, memory (systemd MemoryPeak of the unit, after asks):

| Entry | Book entries | Load | Peak |
|---|---|---|---|
| Machine/canon/impl.bend | 942 | 0.2 s | 54-93 MB |
| Machine/runs_as_eval.bend | 1,275 | 0.6 s | 51 MB |
| main.bend (whole closure) | 2,765 | 3.1 s | 176 MB |
| old shift_gives_shift.bend (4ebef88 layout, heaviest test) | 2,446 | 2.2-2.5 s | 395-470 MB under load |

Per-ask cost on shift_gives_shift (2,446 entries): a switch between worktrees re-parses the entry in
80-480 ms; `--check` (whole file) 1.4-2.1 s; `--lemmas` 0.3 s; a prove miss 2.3-3.1 s; `--find` 0.5-1 s;
a client round trip from Windows adds ~0.3 s (bun start).

Concurrent askers (scratch/g2pool/load.ts: N simulated agents, each its own worktree copy with its own
def above every hole, so no answer cache is shared; 6 asks each: --check, --lemmas, a prove miss,
--find, a prove miss, --check; think time between asks):

| Setup | Think | Wall p50 | Wall p90 | Max |
|---|---|---|---|---|
| 1 agent, 1 server | 0.5-2 s | 1.6 s | 2.7 s | 2.7 s |
| 8 agents, 1 server | 3-10 s | 7.0 s | 10.9 s | 12.9 s |
| 8 agents, 2 replicas | 3-10 s | 2.8 s | 5.5 s | 7.3 s |
| 16 agents, 2 replicas | 3-10 s | 2.8 s | 6.7 s | 7.5 s |
| 8 agents, 1 server, shared prefix (cache hits) | 3-10 s | 1.6 s | 5.5 s | 6.4 s |

Reading: one server keeps up with ~4 agents (a real LLM agent thinks 10-60 s between asks, so likely
6-8); `--replicas 2` for a file with more agents. Every answer was correct for its own text (the
isolation test: a def that exists in one worktree only is never found from another; --check errors
stay with the worktree that has them).

Capacity in WSL's 15 GB: agents run on Windows; WSL holds the servers and the gates. Gates: heavy.sh's
3 slots (each capped at 5 GB, typically 1-2 GB). Servers: ~0.05-0.5 GB each (new-layout books are small:
main.bend's whole closure peaks at 176 MB), capped together at 10 GB by the slice. So ~25 lane files
with one server each (~3-8 GB) plus replicas for hot files fit, i.e. ~15 lanes x 2-4 agents = 30-60
concurrent agents, bounded by ask latency (~4-8 agents per server process), not by memory.

Merge queue test (throwaway target `mq/test-target`, branches mq/*; feature/redesign untouched):

| Batch | Lanes | Outcome | Time |
|---|---|---|---|
| 1 | good, badrule (header change), badg1 (wrong proof), dup (name clash) | good and badrule refused (canon/impl.bend registered to another lane: the registration check); badg1 FAIL G1 (bend2 error); dup FAIL G5 (canon.ff in runs_as_eval.bend and canon/impl.bend) | 5 s |
| 2 | good | rules, G1 (kernel 1 def), G5, G2 (5 TODOs) pass; NOT LANDED (target checked out in g2t2); `land` refused; `land --ff-checked-out` refused while g2t2 was dirty, then fast-forwarded it when clean | 15 s |
| 3 | good2, dup2 | dup2 FAIL G5, dropped; batch merged again; G1 from cache; G2 pass; LANDED by compare-and-swap | 17 s |
| 4 | good3, `--g3 force --dry-run` | G1, G5, G2 pass; G3 PASS (milestones steps 1-5, EXIT 0; ~/bb restored to its previous commit after); NOT LANDED (dry run) | 14.5 min |

Same-basename files: g1.sh names its temp file by a hash of worktree + path. A fill of a law in
another directory (`import ../canon/spec.bend as C`, `def C.term.is_eq_refl`) maps to
`_2e_._2f_canon_2f_spec.term.is_eq_refl` and is kernel-checked (tested with a temporary file).
Separately, `mergeq.ts check` caught: header change, a frozen (hole-free) body change, an import
removal, a file outside the lane's registered files.

## Known limits / next

- WSL's interop is off (binfmt), so nothing in WSL can start a Windows process: the holder must be
  started from Windows. WSL restarted twice this morning (07:24, 07:32) when no wsl.exe was attached;
  any long job (P1's census too) needs a wsl.exe that stays open.
- Worktrees with a `bend` junction: plain `git status`/`git diff` fail inside the junction; use
  `--ignore-submodules=all` (mergeq does).
- G2/G3 failures are not bisected (the batch's lanes are held; run them in smaller batches).
- gen2: keeping a few parsed texts (one per recent worktree) would remove the 0.1-0.5 s re-parse per
  switch; a statement-check cache across switches.
