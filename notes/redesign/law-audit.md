# Law audit: bend-bootstrap @ 4ebef88 (main)

Read-only audit. I changed no file in the repo. I did not run `bend`, `--verdict` or a long kernel run.

## Verdict

1. **The statements are almost right.** The three laws (spec.bend) and the Lean theorems 3.6.2 to 3.6.8 say what AGENTS.md section 3 says. They compose to "the 3.8.7 binary gives what our compiler's Book gives by Eval, and its output follows the laws". There are four gaps. One is serious: **F1**. A compiled module that is outside the WASM subset escapes the trusted model, so on a real engine it can give a wrong result.
2. **The proofs are far from done.**
   - **Lean side: complete.** Each theorem of 3.6.2 to 3.6.8 is proven. `#print axioms` shows only `propext`, `Classical.choice` and `Quot.sound`. There is no `sorry`, `axiom`, `native_decide`, `implemented_by` or `extern`.
   - **Bend side: open.** The import closure of `src/main.bend` (71 files) has **35 open holes (`?TODO`) in 11 files**. The core of `enough_memory` (`mach.memory`) is a bare `?TODO`.
   - Because of the holes, `bend -o` refuses main.bend and `--verdict` cannot accept it. So the premise `Book.check B = .ok ()` of every Lean joining theorem cannot be met yet.
   - 3.8.7 (the self-host run) was never done, and no script for it exists.
   - 3.4.1.4 (self-hosting fits) does not hold now: 4.6 GB is needed and the limit is 4 GiB (AGENTS 3.10.3).

## What the top-level statements are

Only these files say what you are promised. A redesign of the machine (Compiler/Machine, Compiler/Cir, proof.bend) cannot weaken them. Guard these by review:

- **Lean (the real top level):**
  - Interpreter/Program.lean: `start`, `Gives`, `interp`
  - Shared/Bytes.lean: `ctor`, `bits`, `list`, `bytes`, `unbytes`
  - Shared/OneResult.lean: `Steps`
  - Shared/DataForm.lean: `Form.*`, `write`
  - Book/Prune.lean: `prune`
  - Joining/NeedRun.lean:23-44: `Term.nodes`, `largest`, `need`, `memory`
  - Joining/Trusted.lean: `Trusted`, `engineOf`, `wasmRun`, `resultOf`, `outOfMemory`
  - The statements, not the proofs, of Joining/Compiler.lean:99/129/159 and Joining/SelfHost.lean:18/26/34
- **Bend:**
  - src/Compiler/spec.bend (the three laws).
  - src/Wasm/impl.bend, as a whole. It is the trusted meaning of WASM, and no proof pins it (see F5).
- **Pinned by Lean proofs. No hand guard needed:**
  - Program/impl.bend (GivesRun.lean `gives_iff`, NeedRun.lean `big_run`)
  - Eval/impl.bend (`version_steps`)
  - Book/impl.bend (`read_write`)

## Findings, by severity

### F1 (HIGH): no law keeps the compiled module inside the WASM subset

- **Where:** src/Compiler/spec.bend:16-53, and AGENTS 3.6.1 together with 3.9.1.3.2.
- **Clause:** each law speaks of `Wa.Wasm.run(f, C.Compiler.compile(p), i, eng)`.
- **Problem:**
  - 3.9.1.3.2 trusts the Bend model only on modules of the subset.
  - For a module outside the subset, the model gives `unsupported`. So `no_wrong_result` holds with nothing to prove, but a real engine runs the module. It can give a result.
  - When Eval gives a result on some input, `no_other_failure` forces the model to instantiate the module, so the module is in the subset. When Eval gives a result on **no** input, no law constrains the module. Examples: no `main`, a stuck program, a value that is not bytes.
  - So a redesigned compiler can emit, for such a program, an out-of-subset module that gives a result on a real engine. That is a wrong result (3.6.1.1) that the laws do not exclude.
  - The current compiler always emits the machine module or `Compiler.halt`. These are in the subset, so the gap is only in the statement.
- **Proposed fix:** add a fourth law. Its premises are the same as the others, so it holds for every program.

```
# LAW (AGENTS.md 3.6.1.4), in the subset: the compiled module is one that the
# Bend version of WASM covers (3.9.1.2), for every program, input and engine
law in_subset:
  for +f: Nat
  for +p: List<&2, Word(8n)>
  for +i: List<&2, Word(8n)>
  for +eng: Wa.Wasm.Engine
  {Wa.Wasm.run(f, C.Compiler.compile(p), i, eng) != Wa.Wasm.Outcome.unsupported{} : Wa.Wasm.Outcome}
```

- **AGENTS text (proposal):**
  > 3.6.1.4 `in_subset`: the compiled program, run by its target's Bend version, never leaves the subset that the version covers (for WASM: it is never `unsupported`). Why: the target's trust (3.9.1.3) covers only the subset; a module outside it could give a result that no law sees.
- **Lean joining:** add the matching theorem to Joining/Compiler.lean:

```lean
theorem in_subset (hc : Book.check B = .ok ()) (hB : Trusted B)
    (hw : interp B fuel (write bk) = some (w, k)) :
    ¬ Runs B (wasmRun f w i m gs) (ctor (impl "Wasm.Outcome.unsupported") [])
```

- **Check:** `unsupported` comes only from decode, validation or the host exports (Wasm/impl.bend:1749-1758, 2006-2032). Those come before any engine choice or input use, so `!= unsupported` means "inside the subset".

### F2 (MEDIUM): the engine model cannot refuse grows forever, so `no_other_failure` is weaker than 3.9.1.2

- **Where:** src/Wasm/impl.bend:1481-1487 (`Wasm.grants`: past the list, it grants each) and 2031-2036 (`Wasm.Engine{pages, grows}`). The law is at src/Compiler/spec.bend:30-39.
- **Clause:** "its answers to grows within that limit, in order (False refuses one; past the list, it grants each)".
- **Problem:**
  - 3.9.1.2 says "which memory grows it refuses" is an engine choice, and "the laws hold for every choice". A real engine can refuse every grow from some point on. The model cannot express that: each engine grants all grows after a finite list.
  - A compiler that retries a refused grow in a loop meets `no_other_failure` for every list engine, because a grant comes at last. On an engine that always refuses, it runs forever, with no result and no OOM. That is a failure other than OOM (3.6.1.2), and the law does not exclude it.
  - `no_wrong_result` is not affected: a run that ends uses a finite number of answers.
  - The current compiler reports OOM on the first refusal (Cir/runs_as_cir.bend:129-131), so the gap is only in the statement.
- **Proposed fix (exact):** give the answers as a function: `Wasm.Engine{pages: U32, grows: Nat -> Bool}` (the answer to the k-th grow within the limit). If a Data type cannot hold a function, give `Wasm.run` the answers as a separate parameter.
  - `no_other_failure` then quantifies over every answer function.
  - `enough_memory` uses `k => True{}`.
- **Proposed fix (smaller, covers "refuses from some point on"):** `Wasm.Engine{pages: U32, grows: List<&2, Bool>, then: Bool}`, where `then` answers every grow after the list.
  - `enough_memory` uses `Wasm.Engine{m, [], True{}}`.
  - Change the Wasm.grants comment to: "past its answers, it gives `then`".
  - This does not cover answer sequences that never become constant.

### F3 (MEDIUM): no end-to-end statement, and the premises come from separate runs

- **Where:** src/Joining/SelfHost.lean:18-39; src/Joining/scripts/Trusted.lean:14-17; bend/bend2/safe.ts:1701-1731; src/Shared/lower.ts:1-12.
- **Problem:**
  - (a) There is no single theorem that says what you want about a **user** program bk. You must compose `self_host` + Compiler.lean + `prune_gives` by hand. The step is easy, but it is the one statement that protects you, so it should exist.
  - (b) The premises `hc : Book.check B = .ok ()`, `hB : Trusted B` and `hs : interp B fuel (write (prune B)) = some (wc, k)` must all be about **one** B. Today they come from different runs:
    - `--verdict` does not check your .bendtt file. It writes its own text to a temp file and runs the kernel binary on that (safe.ts:1701-1731).
    - The Trusted check, Write.lean and Run.lean each parse a file again.
    - Today that file comes from `lower.ts`, which is our own untrusted code, not `bend -o` (3.7.3).
  - Nothing in 3.5 or 3.7 says that all these runs use the same text.
- **Proposed fix (Lean theorem, in SelfHost.lean):**

```lean
-- AGENTS.md 3.8.7, end to end: the binary wc that the interpreter writes for
-- main.bend's pruned book compiles each book bk to a module w whose runs follow
-- the laws for bk itself
theorem trusted_binary (hc : Book.check B = .ok ()) (hB : Trusted B)
    (hs : interp B fuel (write (prune B)) = some (wc, k))
    (hw : Runs B (wasmRun f wc (write (prune bk)) m gs) (resultOf w)) :
    (∀ f' m' gs' o, Runs B (wasmRun f' w i m' gs') (resultOf o) → ∃ n, Gives bk i o n) ∧
    (∀ o n m' gs', Gives bk i o n →
      ∃ f', Runs B (wasmRun f' w i m' gs') (resultOf o) ∨ Runs B (wasmRun f' w i m' gs') outOfMemory) ∧
    (∀ o n m', Gives bk i o n → need (prune bk) i n ≤ memory m' →
      ∃ f', Runs B (wasmRun f' w i m' []) (resultOf o))
```

  Add the F1 clause too, once that law exists. The proof is `self_host`, then Compiler.lean with `prune bk`, then `prune_gives`.
- **Proposed fix (runtime):** write one Lean script for 3.8.7. It parses main.bendtt once into B, then:
  1. runs `Book.check B` and requires `.ok ()`. This is the kernel's own checker (3.7.2), so it replaces `--verdict` for this B;
  2. runs the Trusted check;
  3. computes `write (prune B)`;
  4. runs `interp B fuel` on those bytes (FRESH, 3.10.2);
  5. writes wc and prints the SHA-256 of main.bendtt.

  The .bendtt must come from `bend -o`, not lower.ts.

### F4 (LOW): 3.7 does not name all of what 3.8.7 trusts

- **Where:** AGENTS 3.7.1 ("Lean."); lakefile.lean (`precompileModules := true`).
- **Problem:**
  - The premises of 3.8.7 (`hc`, `hB`, `hs`) are not proofs. They are answers of compiled Lean code: the kernel's `Book.parse` (a `partial def`), `Book.check`, `interp`, `write`, `prune` (which calls `partial def Book.reach`, src/Shared/Refs.lean:24) and the Trusted check. All of these run natively through Lean's compiler and the clang that Lean ships.
  - This is like trusting `native_decide`, which the guard forbids inside proofs.
  - "Lean" may cover it, but the text does not say so.
- **Proposed AGENTS text:**
  > 3.7.1 Lean: its kernel, which checks our theorems, and its compiler and runtime (with the C compiler that its toolchain ships), which run the kernel's parser and checker (3.2.5) and the steps of 3.8.7 (the writer, the pruning, the Trusted check and the interpreter), whose answers are the premises of 3.6.6 and 3.8.7.

### F5 (LOW): the WASM model is part of the statement, and nothing pins it

- **Where:** src/Wasm/impl.bend (all of it); src/Joining/Generated/Trusted.lean (`trustedVersion` copies `Wasm.run`).
- **Problem:**
  - The meaning of every law depends on `Wasm.run`, including the engine and host sections and the `Outcome` cases.
  - No Lean proof constrains it. The Trusted check only says that B holds the generated copy, and the copy is regenerated by a script.
  - An edit to Wasm/impl.bend (for example during the machine redesign, if the subset grows) changes what the laws mean. Only the tests (milestones.ts steps 3 to 5) and review catch it.
- **Proposed fix:** add a rule.
  > 3.9.1.3.4 Wasm/impl.bend changes only with my approval, and each change reruns milestones.ts steps 3 to 5 on the same commit.

  Also add a check to milestones.ts: the `Wasm.*` defs in the WasmTests book are equal, up to the name prefix, to those in main.bend's book. Today WasmTests builds its own book from `bend src/Wasm/impl.bend -o`, while the laws use main.bend's lowering.

### F6 (INFO): F is measured on the pruned book

- **Where:** src/Program/impl.bend:337-343; Joining/NeedRun.lean:40; SelfHost.lean:34.
- **Problem:** none.
  - The law's "program" is the book whose bytes p the compiler gets, and that is `prune bk`.
  - `Form.defs (prune bk)` has no more nodes than `bk`, and `largest` is the same (`prune_gives`, same steps).
  - So F(prune bk) ≤ F(bk). The promise is the same or stronger than 3.3.8 read on the full Book.
- **Proposed fix (optional):** in 3.3.8, add "(the Book as the compiler gets it, pruned: 3.6.8)".

### F7 (INFO): checks that passed

- **Run (3.3.3):**
  - src/Program/impl.bend:80-81 is `App Q1 (Ref "main") (bytes i)`. Interpreter/Program.lean:14 says the same. The two are joined by `start_run` (Gives.lean:232).
- **Result (3.3.4):**
  - `Program.result` is `Eval.vals` and then `unbytes`. Lean's `Gives` (Interpreter/Program.lean:18) is `Value` ∧ `unbytes`. The two are joined by `gives_iff`.
  - `unbytes` takes exactly the 3.3.1 shapes: Q1 tuples, `Lab "()"`, Base names. Anything else is "no result".
  - `Eval.steps` counts exactly n steps (Eval/impl.bend:605-616), so "the result" is reached at exactly one n (`steps_det`).
  - A Book without `main` gets stuck at `Ref "main"`, so its module gives no result in the model.
- **Eval (3.6.3):** the laws use `El.Eval.steps`. `version_steps` (EvalSteps.lean:39) ties it to the kernel's `Steps`, step for step, in both directions.
- **F (3.9.1.4):** `need = 64 × (Form.defs nodes + largest within n steps) + 2^24`, with n the exact step count of the run. `memory m = 65536 × min(m, 2^16)`.
  - Node counts: `Term.nodes` is one node per kernel constructor, with names inside the node (3.3.7). The data form counts each name byte as 72 nodes and each Nat unit as 4 nodes (3.3.8).
  - The Bend version and the Lean version are proven equal (`big_run`, `program_size_run`).
- **For every program:**
  - p ranges over all bytes. Bytes that are not a book give no Eval result and the module `halt(2)`.
  - Books of 2^26 bytes or more compile to `halt(1)` (OOM). `need.big` (need_big.bend, no hole) proves that their F is above 4 GiB.
  - `bk` in the Lean theorems is any Book, checked or not, and the compiler's own Book is included.
- **Vacuity:**
  - `enough_memory` is not empty: for a small program, F is about 2^24 + 64 × (size), far below 4 GiB.
  - The premise `big` is the exact F test.
  - `Engine{m, []}` grants each grow within m pages.
  - A compiler that always reports OOM fails `enough_memory`.
  - A compiler that never gives a result fails `enough_memory`.
  - The only empty cases are the ones AGENTS allows: F above 4 GiB, an engine with refusals, and no Eval result. F1 and F2 are the remaining holes.
- **Engines:**
  - `no_wrong_result` and `no_other_failure` quantify over `eng`.
  - OOM is the program's own status (alloc gives -1, or run gives 1). This is allowed by 3.6.1.2, and `enough_memory` bounds it.
  - The subset has no `call` instruction, so the engine's call-stack limit (3.9.1.4) cannot matter.

### F8 (INFO): small text drift

- Joining/Trusted.lean:44-45 (`engineOf`): the comment omits "past gs, it grants each". This is the fact that F2 is about. Fix it together with F2.

## Status of the proofs that the laws rest on (Part 1)

- **proof.bend:** the proofs of the three laws are complete. They rest on four groups of lemmas:

| Lemmas | File | State |
|---|---|---|
| Layer A: `halt.no_result`, `halt.oom`, `mach_wasm.sound/result/result.all/oom` | Cir/runs_as_cir.bend | No `?TODO` in the Cir closure. Not checked by the kernel. |
| `img.small` | img_small.bend | No hole. Not checked by the kernel. |
| `need.big` | need_big.bend | No hole. Not checked by the kernel. |
| Layer B: `mach.safe`, `mach.sound`, `mach.complete`, `mach.memory` | Machine/runs_as_eval.bend | Open (see below). |

- **Layer B details:**
  - `mach.safe`, `mach.sound` and `mach.complete` call moves.bend. moves.bend imports the files that have holes, and rests on 47 internal `law`s (move_kit.bend, definitions.bend, copy_substitution.bend).
  - `mach.memory` is a bare `?TODO` (moves.bend:1225 and runs_as_eval.bend:57). So `enough_memory` has no proof at all for its core.
- **Holes per law:**
  - `no_wrong_result` needs A + `mach.safe` + `mach.sound`.
  - `no_other_failure` needs A + `mach.complete`.
  - `enough_memory` needs A + `need.big` + `mach.memory`.
- **Open holes in the closure of main.bend (code holes, not comments): 35.**

| File | Holes |
|---|---|
| shift_gives_shift.bend | 13 |
| walk.bend | 6 |
| moves_copy.bend | 4 |
| moves_call.bend | 3 |
| copy_gives_subst.bend | 2 |
| data_check.bend | 2 |
| copy_bridge.bend | 1 |
| heap_ops.bend | 1 |
| input_bridge.bend | 1 |
| moves.bend | 1 |
| runs_as_eval.bend | 1 |

- **Not traced:** which of the three B lemmas reaches which hole. That needs a def-level call graph or the checker's report.
- **Clean:** no `@unsafe` or foreign code in the closure.

## Lean theorems (Part 2)

Checked with `lean` on a scratch file against the repo's build (.lake oleans of 2026-11-03 11:59; no .lean file is newer). `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for each theorem below. `src/Bootstrap.lean` ends with `#guard_axioms`, which fails the build on any other axiom. `partial def` appears in Refs.lean (`Book.reach`, not used by any proof) and in the scripts only. `@[csimp]` appears twice (`byte_byteS`, `stepwise_stepwiseF`), and both are proven.

| AGENTS | Lean statement | Matches the wording | Status |
|---|---|---|---|
| 3.6.2 data form 1-1 | `term_inj`, `defn_inj`, `book_inj` (DataForm.lean:145-180) | yes | proven |
| 3.6.3 Bend Eval = Eval | `version_steps` (EvalSteps.lean:39): `Runs B (Eval.steps n defs t) (some u) ↔ Steps bk n t u`, if B holds evalVersion | yes: same n, both directions | proven |
| 3.6.4 reader | `read_write` (Read.lean:17): `Runs B (Book.read (bytes (write bk))) (some (Form.defs bk.defs))` | yes | proven |
| 3.6.5 interpreter | `interp_iff` (Interpreter/Program.lean:36): `interp bk fuel i = some (r,n) ↔ Gives bk i r n ∧ n ≤ fuel` | yes | proven |
| 3.6.6 joining | `no_wrong_result`, `no_other_failure`, `enough_memory` (Joining/Compiler.lean:99/129/159), if `Book.check B = .ok ()` and `Trusted B` | yes (plus F1) | proven; premises not met yet (no `--verdict`) |
| 3.6.7 one result | `eval_det`, `steps_det` (OneResult.lean:74/94), `gives_det` | yes | proven |
| 3.6.8 pruning | `prune_gives` (Prune.lean:333): `Gives (prune bk) i r n ↔ Gives bk i r n` | yes: same n | proven |
| 3.8.7 | `self_host`, `self_host_complete`, `self_host_memory` (SelfHost.lean) | yes; no end-to-end form (F3) | proven, if hc, hB, hs |

## Chain, steps and milestones

| Item | State | What is open |
|---|---|---|
| 3.5.1 `bend -o` | trusted | `bend -o` refuses main.bend while holes exist. lower.ts (untrusted) stands in today. |
| 3.5.2 parse + `--verdict` | not possible yet | The 35 holes. `--verdict` checks its own temp text, not your file (F3). |
| 3.5.3 writer / reader / prune | proven | none |
| 3.5.4 compiler laws | stated; proof open | Layer B holes. Layer A not checked by the kernel. F1, F2. |
| 3.5.5 interpreter | proven | none |
| 3.5.6 self-host run | not done | No script. Feasibility (steps, time) unknown. |
| 3.5.7 engine and host | trusted, tested | Test runs not checked in this audit (milestones.ts steps 3-5). |
| 3.8.1 Bend Eval + 3.6.3 | done | none |
| 3.8.2 writer, reader, prune + theorems | done | none |
| 3.8.3 WASM Bend version | written (2042 lines) | trusted by review and tests (3.9.1.3.2); F5 |
| 3.8.4 compiler + laws by `--verdict` | open | 35 holes; `mach.memory` empty; no `--verdict` yet |
| 3.8.5 Lean interpreter + 3.6.5 | done | none |
| 3.8.6 joining 3.6.6 | done in Lean | conditional on 3.8.4 |
| 3.8.7 self-hosting | theorems done; run not done | run, single-B script (F3) |
| 3.8.8 WASM extra steps (SpecTec Lean) | not started | all |
| 3.4.1.4 self-host fits | not met | 4.6 GB needed, 4 GiB limit (3.10.3: word cells) |
| 3.9.1.3.2 official tests + FORMS | harness exists (WasmTests.lean, differential.ts, milestones.ts) | pass state not run here |
| 3.9.1.3.3 host | harness exists (agree.ts, Host.lean) | pass state not run here |
| M1 Lean interpreter, proven | done | none |
| M2 Bend Eval, proven | done | Today the "B holds it" check runs on lower.ts output. |
| M3 Bend reader, proven | done | same note as M2 |
| M4 WASM subset interpreter, reviewed and tested | harness done | test pass state not checked here |

## Checks that need the kernel or long runs (not done)

- `--verdict` on main.bend (impossible until the holes close).
- `--verdict` on the hole-free part (Layer A, img_small, need_big), to confirm that they check.
- milestones.ts steps 2 to 5.
- The size of `write (prune B)` for main.bend. It must be below 2^26 bytes, else the compiler compiles itself to `halt(1)`.
- The step count of 3.8.7.

## Open questions

1. F1: do you approve the new law `in_subset` (and AGENTS 3.6.1.4)?
2. F2: should engine answers be a function (exact), or a list plus `then` (simpler, covers "refuses from some point on")?
3. F3: should I add `trusted_binary` to SelfHost.lean, and one Lean script for 3.8.7 that parses once and checks, prunes, writes and interprets the same B?
4. F4: do you approve the 3.7.1 wording?
5. F5: do you freeze src/Wasm/impl.bend with the laws (3.9.1.3.4), and add the "same Wasm defs" check to milestones.ts?
6. F6: do you want the 3.3.8 note on the pruned book?
