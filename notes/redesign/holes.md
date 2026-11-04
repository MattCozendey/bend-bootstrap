# Hole ledger (redesign)

One line per open `?TODO` in the import closure of `src/main.bend` on `feature/redesign`. G2 compares
`bend2 --check-only src/main.bend` ("N TODOs found") with the count here. Counted by
`tmp-p1/closure.py` (imports followed from main.bend; `?TODO` outside comments).

## Now: feature/redesign @ ec0f1a0 (after P1) — 5 holes, 35 files

| # | File | Line | Def | Layer | Lane | Owner |
|---|---|---|---|---|---|---|
| 1 | Compiler/Machine/runs_as_eval.bend | 26 | mach.safe | B interface | P2 S4 (assembly), proven from the laws in P2 | P2 S4 owner |
| 2 | Compiler/Machine/runs_as_eval.bend | 35 | mach.sound | B interface | P2 S4 | P2 S4 owner |
| 3 | Compiler/Machine/runs_as_eval.bend | 46 | mach.complete | B interface | P2 S4 | P2 S4 owner |
| 4 | Compiler/Machine/runs_as_eval.bend | 56 | mach.memory | B interface | P2 S4 | P2 S4 owner |
| 5 | Compiler/Cir/runs_as_cir.bend | 240 | mach_wasm.uniform | A (from w/laws, F2) | layer A (outside the plan's lanes) | unassigned (coordinator) |

G2 on ec0f1a0: "5 TODOs found" (11 s). Matches.

When P2 lands, every law of §4 adds one hole (its proof def), and holes 1–4 close (S4 proves them from
the laws). Each P2/P3 merge updates this table.

## History

| State | Holes | Files | Note |
|---|---|---|---|
| main 4ebef88 | 35 | 71 | as law-audit.md lists them; G2 "35 TODOs found" (58 s) |
| + w/laws (6693442) | 36 | 71 | + mach_wasm.uniform (Cir/runs_as_cir.bend) |
| + P1 (ec0f1a0) | 5 | 35 | the old layer-B tree is deleted (34 of its holes go); runs_as_eval's 3 proven-by-moves bodies become holes |

The 35 holes of 4ebef88, all deleted by P1 (salvage: `git show 4ebef88:<path>`):
runs_as_eval mach.memory; moves mach.memory.proof; heap_ops al.reuse.term; copy_gives_subst Cp.body.ok,
Cp.start; shift_gives_shift Sh.part.share, Sh.part.keep, Sh.part.var, Sh.part.push, Sh.part.b, Sh.part.a,
Sh.part.ok, Sh.todo.ok (4), Sh.done.fin, Sh.start; copy_bridge K.copy.post; data_check K.data.post,
K.data.done; walk mat.hit, mat.miss.ws, prj.tup, lam.live, app.push, K.walk.done; input_bridge
K.input.post; moves_copy K.mv.ev.unlet, K.mv.ret.app.lam, K.mv.ret.fun.lam, K.mv.ret.let; moves_call
K.mv.ev.ref, K.mv.ret.app.call, K.mv.ret.fun.call.

## Gate file list (what G1 covers)

G1 runs `~/lead/gate.sh WT <file> [HOST]` on each changed `.bend` file of a merge. The files that a
redesign merge may change, and their host:

| File(s) | Host | Note |
|---|---|---|
| src/Compiler/Machine/impl.bend | itself | P1 only (and P6); then also G4 |
| src/Compiler/Machine/runs_as_eval.bend | itself (or main.bend) | 4 statements frozen |
| src/Compiler/Machine/shared.bend, */spec.bend, */impl.bend, heap/*.bend, routines/*.bend, moves/*.bend, moves.bend | itself; a file that does not lower alone: src/Compiler/Machine/moves.bend (once it exists) or main.bend | P2/P3 lanes (§4.0) |
| src/Compiler/Cir/module_valid.bend, simulation_code_size.bend, simulation_host.bend | itself | not changed; rerun (G4) whenever Machine/impl.bend changes |
| src/main.bend | itself | G2 |

Never changed by the redesign (§5.0): spec.bend, Compiler/impl.bend, proof.bend, Cir/*, img_small.bend,
need_big.bend, Eval, Book, Program, Wasm, main.bend, every .lean file, the bend submodule.
