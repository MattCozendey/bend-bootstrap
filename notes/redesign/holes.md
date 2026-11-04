# Hole ledger (redesign)

One line per open `?TODO` in the import closure of `src/main.bend` on `feature/redesign`. G2 compares
`bend2 --check-only src/main.bend` ("N TODOs found") with the count here. Counted by
`tmp-p1/closure.py` (imports followed from main.bend; `?TODO` outside comments).

## Now: w/s2 on feature/redesign 1c470be (P2 complete: S1–S4) — 128 holes, 65 files

G2 on w/s4 (7a36905, feature/redesign bec2fe8 merged): `bend2 --check-only src/main.bend` prints the TODO
count below (see s4-handoff.md, Gates); S4's closure script (imports followed from main.bend; `?TODO`
outside comments) counts 127. runs_as_eval's 4 holes are closed (moves.bend's assembly, proven from the
laws); every other hole is a law's proof (one `?TODO` def each), independent of the others: a proof may
use any law, proven or not.

| File | Holes | Lane |
|---|---|---|
| Compiler/Cir/runs_as_cir.bend | 1 | layer A (w/laws F2) |
| Compiler/Machine/am/impl.bend | 2 | F5 am |
| Compiler/Machine/canon/impl.bend | 9 | F4 canon |
| Compiler/Machine/header/impl.bend | 18 | F3 header |
| Compiler/Machine/heap/count.bend | 6 | F6 heap |
| Compiler/Machine/heap/view.bend | 18 | F6 heap |
| Compiler/Machine/image/impl.bend | 6 | F7 image |
| Compiler/Machine/logic/impl.bend | 11 | F2 logic |
| Compiler/Machine/memory/impl.bend | 7 | F15 memory |
| Compiler/Machine/moves/call.bend | 10 | F14 moves |
| Compiler/Machine/moves/ev.bend | 10 | F14 moves |
| Compiler/Machine/moves/ret.bend | 8 | F14 moves |
| Compiler/Machine/moves/round.bend | 1 | F14 moves |
| Compiler/Machine/routines/copy.bend | 1 | F10 copy |
| Compiler/Machine/routines/dec.bend | 3 | F9 dec |
| Compiler/Machine/routines/input.bend | 1 | F13 input |
| Compiler/Machine/routines/nth.bend | 1 | F8 prims |
| Compiler/Machine/routines/out.bend | 1 | F12 out |
| Compiler/Machine/routines/prims.bend | 13 | F8 prims |
| Compiler/Machine/routines/walk.bend | 1 | F11 walk |

| # | File | Line | Def | Lane | Statement owner |
|---|---|---|---|---|---|
| 1 | Compiler/Cir/runs_as_cir.bend | 240 | mach_wasm.uniform | layer A (w/laws F2) | coordinator |
| 2 | Compiler/Machine/logic/impl.bend | 378 | Lg.cells.get_set | F2 logic | S1 |
| 3 | Compiler/Machine/logic/impl.bend | 381 | Lg.cell.get_set | F2 logic | S1 |
| 4 | Compiler/Machine/logic/impl.bend | 464 | Lg.frame.regs | F2 logic | S1 |
| 5 | Compiler/Machine/logic/impl.bend | 467 | Lg.frame.fixed | F2 logic | S1 |
| 6 | Compiler/Machine/logic/impl.bend | 631 | Lg.exec.alloc | F2 logic | S1 |
| 7 | Compiler/Machine/logic/impl.bend | 644 | Lg.wp.alloc | F2 logic | S1 |
| 8 | Compiler/Machine/logic/impl.bend | 647 | Lg.wp.emit | F2 logic | S1 |
| 9 | Compiler/Machine/logic/impl.bend | 650 | Lg.tot.any | F2 logic | S1 |
| 10 | Compiler/Machine/logic/impl.bend | 653 | Lg.tot.while | F2 logic | S1 |
| 11 | Compiler/Machine/logic/impl.bend | 922 | Lg.tot.frame | F2 logic | S1 |
| 12 | Compiler/Machine/logic/impl.bend | 925 | Lg.tot.frame_out | F2 logic | S1 |
| 13 | Compiler/Machine/header/impl.bend | 15 | Hd.hd.tag_of | F3 header | S1 |
| 14 | Compiler/Machine/header/impl.bend | 18 | Hd.hd.q_of | F3 header | S1 |
| 15 | Compiler/Machine/header/impl.bend | 21 | Hd.hd.fv_of | F3 header | S1 |
| 16 | Compiler/Machine/header/impl.bend | 24 | Hd.hd.has_of | F3 header | S1 |
| 17 | Compiler/Machine/header/impl.bend | 27 | Hd.hd.todo_of | F3 header | S1 |
| 18 | Compiler/Machine/header/impl.bend | 30 | Hd.mask.and_or | F3 header | S1 |
| 19 | Compiler/Machine/header/impl.bend | 33 | Hd.mask.and_and | F3 header | S1 |
| 20 | Compiler/Machine/header/impl.bend | 36 | Hd.mask.and_shl | F3 header | S1 |
| 21 | Compiler/Machine/header/impl.bend | 39 | Hd.mask.shr_or | F3 header | S1 |
| 22 | Compiler/Machine/header/impl.bend | 42 | Hd.mask.shr_and | F3 header | S1 |
| 23 | Compiler/Machine/header/impl.bend | 45 | Hd.mask.shr_shl | F3 header | S1 |
| 24 | Compiler/Machine/header/impl.bend | 48 | Hd.mask.or_zero | F3 header | S1 |
| 25 | Compiler/Machine/header/impl.bend | 51 | Hd.mask.zero_or | F3 header | S1 |
| 26 | Compiler/Machine/header/impl.bend | 54 | Hd.mask.and_zero | F3 header | S1 |
| 27 | Compiler/Machine/header/impl.bend | 57 | Hd.mask.zero_and | F3 header | S1 |
| 28 | Compiler/Machine/header/impl.bend | 60 | Hd.mask.and_low | F3 header | S1 |
| 29 | Compiler/Machine/header/impl.bend | 63 | Hd.mask.shr_low | F3 header | S1 |
| 30 | Compiler/Machine/header/impl.bend | 66 | Hd.mask.sub_bit | F3 header | S1 |
| 31 | Compiler/Machine/canon/impl.bend | 44 | C.term.is_eq_ok | F4 canon | S3 |
| 32 | Compiler/Machine/canon/impl.bend | 47 | C.term.is_eq_refl | F4 canon | S3 |
| 33 | Compiler/Machine/canon/impl.bend | 50 | C.canon.step | F4 canon | S3 |
| 34 | Compiler/Machine/canon/impl.bend | 69 | C.canon.result | F4 canon | S3 |
| 35 | Compiler/Machine/canon/impl.bend | 138 | C.canon.vals | F4 canon | S3 |
| 36 | Compiler/Machine/canon/impl.bend | 268 | C.canon.start | F4 canon | S3 |
| 37 | Compiler/Machine/canon/impl.bend | 271 | C.canon.subst | F4 canon | S3 |
| 38 | Compiler/Machine/canon/impl.bend | 274 | C.canon.subst_below | F4 canon | S3 |
| 39 | Compiler/Machine/canon/impl.bend | 363 | C.canon.lift | F4 canon | S3 |
| 40 | Compiler/Machine/am/impl.bend | 18 | A.am.ok | F5 am | S3 |
| 41 | Compiler/Machine/am/impl.bend | 21 | A.am.walk_eval | F5 am | S3 |
| 42 | Compiler/Machine/heap/view.bend | 26 | Hp.view.frame | F6 heap | S2 |
| 43 | Compiler/Machine/heap/view.bend | 29 | Hp.view.more | F6 heap | S2 |
| 44 | Compiler/Machine/heap/view.bend | 32 | Hp.view.deeper | F6 heap | S2 |
| 45 | Compiler/Machine/heap/view.bend | 35 | Hp.view.static | F6 heap | S2 |
| 46 | Compiler/Machine/heap/view.bend | 38 | Hp.view.canon | F6 heap | S2 |
| 47 | Compiler/Machine/heap/view.bend | 41 | Hp.view.closed | F6 heap | S2 |
| 48 | Compiler/Machine/heap/view.bend | 44 | Hp.view.chk | F6 heap | S2 |
| 49 | Compiler/Machine/heap/view.bend | 47 | Hp.view.tag | F6 heap | S2 |
| 50 | Compiler/Machine/heap/view.bend | 50 | Hp.view.kid | F6 heap | S2 |
| 51 | Compiler/Machine/heap/view.bend | 53 | Hp.agree.store | F6 heap | S2 |
| 52 | Compiler/Machine/heap/view.bend | 56 | Hp.agree.store1 | F6 heap | S2 |
| 53 | Compiler/Machine/heap/view.bend | 59 | Hp.agree.put | F6 heap | S2 |
| 54 | Compiler/Machine/heap/view.bend | 62 | Hp.agree.refl | F6 heap | S2 |
| 55 | Compiler/Machine/heap/view.bend | 65 | Hp.agree.trans | F6 heap | S2 |
| 56 | Compiler/Machine/heap/view.bend | 68 | Hp.view.rc_fv | F6 heap | S2 |
| 57 | Compiler/Machine/heap/view.bend | 71 | Hp.view.rc_frame | F6 heap | S2 |
| 58 | Compiler/Machine/heap/view.bend | 74 | Hp.view.rc_more | F6 heap | S2 |
| 59 | Compiler/Machine/heap/view.bend | 77 | Hp.view.rc_up | F6 heap | S2 |
| 60 | Compiler/Machine/heap/count.bend | 27 | Hp.h.set | F6 heap | S2 |
| 61 | Compiler/Machine/heap/count.bend | 30 | Hp.h.live | F6 heap | S2 |
| 62 | Compiler/Machine/heap/count.bend | 33 | Hp.h.rts_swap | F6 heap | S2 |
| 63 | Compiler/Machine/heap/count.bend | 36 | Hp.h.chs_swap | F6 heap | S2 |
| 64 | Compiler/Machine/heap/count.bend | 39 | Hp.h.static_root | F6 heap | S2 |
| 65 | Compiler/Machine/heap/count.bend | 42 | Hp.h.count | F6 heap | S2 |
| 66 | Compiler/Machine/image/impl.bend | 29 | I.img.start | F7 image | S2 |
| 67 | Compiler/Machine/image/impl.bend | 32 | I.img.frame | F7 image | S2 |
| 68 | Compiler/Machine/image/impl.bend | 35 | I.img.store | F7 image | S2 |
| 69 | Compiler/Machine/image/impl.bend | 38 | I.img.put | F7 image | S2 |
| 70 | Compiler/Machine/image/impl.bend | 41 | I.img.table | F7 image | S2 |
| 71 | Compiler/Machine/image/impl.bend | 44 | I.img.ref | F7 image | S2 |
| 72 | Compiler/Machine/routines/prims.bend | 32 | R.alloc.spec | F8 prims | S2 |
| 73 | Compiler/Machine/routines/prims.bend | 35 | R.make.spec | F8 prims | S2 |
| 74 | Compiler/Machine/routines/prims.bend | 38 | R.release.spec | F8 prims | S2 |
| 75 | Compiler/Machine/routines/prims.bend | 41 | R.inc.spec | F8 prims | S2 |
| 76 | Compiler/Machine/routines/prims.bend | 44 | R.push.spec | F8 prims | S2 |
| 77 | Compiler/Machine/routines/prims.bend | 47 | R.pop.spec | F8 prims | S2 |
| 78 | Compiler/Machine/routines/prims.bend | 50 | R.swap.spec | F8 prims | S2 |
| 79 | Compiler/Machine/routines/prims.bend | 53 | R.one.spec | F8 prims | S2 |
| 80 | Compiler/Machine/routines/prims.bend | 56 | R.h.node | F8 prims | S2 |
| 81 | Compiler/Machine/routines/prims.bend | 59 | R.h.arg | F8 prims | S2 |
| 82 | Compiler/Machine/routines/prims.bend | 61 | R.alloc.regs | F8 prims | S2 |
| 83 | Compiler/Machine/routines/prims.bend | 64 | R.make.regs | F8 prims | S2 |
| 84 | Compiler/Machine/routines/nth.bend | 31 | R.nth.spec | F8 prims | S2 |
| 85 | Compiler/Machine/routines/dec.bend | 32 | R.dec.spec | F9 dec | S2 |
| 86 | Compiler/Machine/routines/dec.bend | 35 | R.release_arg.spec | F9 dec | S2 |
| 87 | Compiler/Machine/routines/dec.bend | 38 | R.release_all.spec | F9 dec | S2 |
| 88 | Compiler/Machine/routines/copy.bend | 35 | R.copy.spec | F10 copy | S2 |
| 89 | Compiler/Machine/routines/walk.bend | 31 | R.walk.spec | F11 walk | S2 |
| 90 | Compiler/Machine/routines/out.bend | 31 | R.out.spec | F12 out | S2 |
| 91 | Compiler/Machine/routines/input.bend | 32 | R.input.spec | F13 input | S2 |
| 92 | Compiler/Machine/memory/impl.bend | 848 | Me.round.mem | F15 memory | S4 |
| 93 | Compiler/Machine/memory/impl.bend | 851 | Me.input.mem | F15 memory | S4 |
| 94 | Compiler/Machine/memory/impl.bend | 854 | Me.need.peak | F15 memory | S4 |
| 95 | Compiler/Machine/memory/impl.bend | 857 | Me.budget.need | F15 memory | S4 |
| 96 | Compiler/Machine/memory/impl.bend | 860 | Me.input.need | F15 memory | S4 |
| 97 | Compiler/Machine/memory/impl.bend | 869 | Me.start.ok | F15 memory | S4 |
| 98 | Compiler/Machine/memory/impl.bend | 872 | Me.code.fits | F15 memory | S4 |
| 99 | Compiler/Machine/moves/ev.bend | 44 | Mv.mv.ev.val | F14 moves | S4 |
| 100 | Compiler/Machine/moves/ev.bend | 47 | Mv.mv.ev.var | F14 moves | S4 |
| 101 | Compiler/Machine/moves/ev.bend | 50 | Mv.mv.ev.app | F14 moves | S4 |
| 102 | Compiler/Machine/moves/ev.bend | 53 | Mv.mv.ev.ann | F14 moves | S4 |
| 103 | Compiler/Machine/moves/ev.bend | 56 | Mv.mv.ev.let | F14 moves | S4 |
| 104 | Compiler/Machine/moves/ev.bend | 59 | Mv.mv.ev.unlet | F14 moves | S4 |
| 105 | Compiler/Machine/moves/ev.bend | 62 | Mv.mv.ev.tup | F14 moves | S4 |
| 106 | Compiler/Machine/moves/ev.bend | 65 | Mv.mv.ev.tup0 | F14 moves | S4 |
| 107 | Compiler/Machine/moves/ev.bend | 68 | Mv.mv.ev.rwt | F14 moves | S4 |
| 108 | Compiler/Machine/moves/ev.bend | 71 | Mv.mv.ev.min | F14 moves | S4 |
| 109 | Compiler/Machine/moves/ret.bend | 43 | Mv.mv.out | F14 moves | S4 |
| 110 | Compiler/Machine/moves/ret.bend | 46 | Mv.mv.ret.swap | F14 moves | S4 |
| 111 | Compiler/Machine/moves/ret.bend | 49 | Mv.mv.ret.let | F14 moves | S4 |
| 112 | Compiler/Machine/moves/ret.bend | 52 | Mv.mv.ret.tupb | F14 moves | S4 |
| 113 | Compiler/Machine/moves/ret.bend | 55 | Mv.mv.ret.tupa | F14 moves | S4 |
| 114 | Compiler/Machine/moves/ret.bend | 58 | Mv.mv.ret.rwt | F14 moves | S4 |
| 115 | Compiler/Machine/moves/ret.bend | 61 | Mv.mv.ret.minb | F14 moves | S4 |
| 116 | Compiler/Machine/moves/ret.bend | 64 | Mv.mv.ret.mina | F14 moves | S4 |
| 117 | Compiler/Machine/moves/call.bend | 45 | Mv.call.frames | F14 moves | S4 |
| 118 | Compiler/Machine/moves/call.bend | 48 | Mv.mv.ev.ref | F14 moves | S4 |
| 119 | Compiler/Machine/moves/call.bend | 51 | Mv.mv.ret.app.lam | F14 moves | S4 |
| 120 | Compiler/Machine/moves/call.bend | 54 | Mv.mv.ret.app.prj | F14 moves | S4 |
| 121 | Compiler/Machine/moves/call.bend | 57 | Mv.mv.ret.app.mat | F14 moves | S4 |
| 122 | Compiler/Machine/moves/call.bend | 60 | Mv.mv.ret.app.call | F14 moves | S4 |
| 123 | Compiler/Machine/moves/call.bend | 63 | Mv.mv.ret.fun.lam | F14 moves | S4 |
| 124 | Compiler/Machine/moves/call.bend | 66 | Mv.mv.ret.fun.prj | F14 moves | S4 |
| 125 | Compiler/Machine/moves/call.bend | 69 | Mv.mv.ret.fun.mat | F14 moves | S4 |
| 126 | Compiler/Machine/moves/call.bend | 72 | Mv.mv.ret.fun.call | F14 moves | S4 |
| 127 | Compiler/Machine/moves/round.bend | 292 | Mv.inv.vb | F14 moves | S4 |
| 128 | Compiler/Machine/routines/prims.bend | 67 | R.alloc.cell | F8 prims | S2 |

## History

| State | Holes | Files | Note |
|---|---|---|---|
| main 4ebef88 | 35 | 71 | as law-audit.md lists them; G2 "35 TODOs found" (58 s) |
| + w/laws (6693442) | 36 | 71 | + mach_wasm.uniform (Cir/runs_as_cir.bend) |
| + P1 (ec0f1a0) | 5 | 35 | the old layer-B tree is deleted (34 of its holes go); runs_as_eval's 3 proven-by-moves bodies become holes |
| + P2 S1–S4 (w/s4 8060b19) | 129 | 65 | the new tree joins main's closure (moves.bend imports every proof file); runs_as_eval's 4 holes closed by the assembly; 128 law holes + mach_wasm.uniform |
| w/s4 7a36905 | 127 | 65 | S4 proved need.lim and eval.stops (memory/impl) |
| w/s2 on 1c470be | 128 | 65 | + S2's alloc.cell (gen2 --wp); G5 renames Inv → MInv, alloc.reg → alloc.regs, make.reg → make.regs; G2 "128 TODOs found" |

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
