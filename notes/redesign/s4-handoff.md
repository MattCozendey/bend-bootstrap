# S4 handoff: moves (B7), memory (B8), the assembly (moves.bend), runs_as_eval's bodies

Branch `w/s4` off `feature/redesign` (967db15; feature/redesign merged again up to bec2fe8: S1/S2
follow-ups and S2's review fixes). Worktree `C:\Users\mathe\source\repos\bb-wt\s4`. Not pushed, not merged.
Statement decisions and why: `s4-notes.md`. WSL mirror: `~/wt/s4` (`~/wt/s4gate.sh [-c] Compiler/Machine/NAME`
rsyncs, then gates or bend2-checks; note it takes the path without `.bend`).

## Files (src/Compiler/Machine/)

| File | What | Holes |
|---|---|---|
| `memory/spec.bend` | Mem.cells, Stat, Defs.big, StepSize, Need, Budget, Peak, Start.ok, Fits.halt; 9 laws | (laws) |
| `memory/impl.bend` | one def per law; need.lim PROVEN (memory_bound's memory.le, ported); the rest `?TODO` | 8 |
| `moves/spec.bend` | Vb, Next/Next.is, Halt/Halt.is, Kind.is_app, Head.calls, Call.frames(+scr, fs); round.sim, inv.vb, 27 mv.*, call.frames | (laws) |
| `moves/round.bend` | round.sim PROVEN from the mv laws (mode test, AM.move's case split) | 1 (inv.vb) |
| `moves/ev.bend` | mv.ev.* but ref | 10 |
| `moves/ret.bend` | mv.out, mv.ret.swap/let/tupb/tupa/rwt/minb/mina | 8 |
| `moves/call.bend` | call.frames, mv.ev.ref, mv.ret.app.*, mv.ret.fun.* | 10 |
| `moves.bend` | the assembly: PROVEN, no `?TODO` (bend2 and kernel: 124 defs, 0 fail) | 0 |
| `runs_as_eval.bend` | 4 statements byte for byte; bodies call `Gen2Moves.mach.*.proof` | 0 |
| `s4_smoke.bend` | computed checks (outside main's closure; P5 deletes it) | 0 |

## Law headers

memory/spec.bend (alias `Me`):
- `eval.stops` (vals(ds, t, False) = True) ⊢ Eval.step(ds, t) = None
- `round.mem` (Inv(x,st,s), exec(f, Mach.round(), st) = next{st2}) ⊢ Stat(st2) ≤ Stat(st) ∧ Mem.cells(st2) ≤ max(Mem.cells(st), Need(ds,st,s))
- `input.mem` (Book.read, Img.small, Start, exec(f, M.input(), St0) = next{st}) ⊢ Stat(Mode0 st) ≤ 6144 ∧ Mem.cells(Mode0 st) ≤ Peak(ds, Stat(Mode0 st), largest(p,i,n))
- `need.peak` (Book.read, result at n = o, j ≤ n, CSteps(j) is AS.term(s), Stat(st) ≤ C) ⊢ Need(ds,st,s) ≤ Peak(ds, C, largest(p,i,n))
- `budget.need` (+ Start, Inv(Cx.of(ds,k,first), st, s), C ≤ 6144, Mem.cells(st) ≤ Peak) ⊢ Budget(Cx.of(..), st, s) ≤ Program.need(p,i,n)
- `input.need` (Book.read, Start) ⊢ Input.budget(first, i) ≤ need(p,i,n)
- `need.lim` (Start, need ≤ memory(m)) ⊢ need ≤ Lim(St0) — PROVEN
- `start.ok` (Book.read, need ≤ memory(m)) ⊢ Start.ok(Img.cells(ds), i, m) (Cir.result's checks before the program pass)
- `code.fits` ⊢ Fits.halt(exec(n, Mach.code(), St0(..))) (a halt 0's output lies in the memory)

moves/spec.bend (alias `Mv`):
- `round.sim` (Inv(x,st,s)) ⊢ Tot(Mach.round(), st, Budget(x,st,s), Next(x, AM.move(ds, Vb(st), s)), Halt(AM.move(..))) — PROVEN
- `inv.vb` (Inv) ⊢ ¬Vb(st) ∨ Eval.vals(ds, focus(s), False)
- mode 0, each `(x, st, <focus parts>, fs, iv: Inv(x, st, AS{False, t, fs}), hv: Vb(st) = False [, hq: live(q) = b])
  ⊢ Tot(M.ev(), st, Budget, Next(x, o), Halt(o))`: `mv.ev.val` (hv: Vb ∨ AM.former(t); o = next AS{True,t,fs}), `mv.ev.var` (halt 2),
  `mv.ev.app`, `mv.ev.ref` (o = AM.body(ds, Book.get(ds,k), [], AS{True, Ref k, fs}, fs)), `mv.ev.ann`, `mv.ev.let`/`unlet`,
  `mv.ev.tup`/`tup0`, `mv.ev.rwt`, `mv.ev.min`
- mode 1, each `⊢ Tot(M.ret(), ..)`: `mv.out` (o = AM.out(unbytes v)), `mv.ret.swap` (hk: Kind.is_app(kind), hs: live(q) ∧ ¬k),
  `mv.ret.app.lam/prj/mat/call` (hk, hs: … = False; call: hc: Head.calls(v)), `mv.ret.fun.lam/prj/mat/call`, `mv.ret.let`,
  `mv.ret.tupb`, `mv.ret.tupa`, `mv.ret.rwt`, `mv.ret.minb`, `mv.ret.mina` — outcomes as AM.move computes them
- `call.frames` (H with the chain at wh = c of ys, Reg(wh) = c) ⊢ Tot(Call.frames(), st, Cells.bytes(fi, 1+|L|),
  ∃L2. H(.., L2, rs, Call.fs(ys, fs), chs) ∧ wh = 0 ∧ Same(st, st2, Call.frames.scr()) ∧ |L2| ≤ |L|, No) (review G3)

## For P3 (F14 moves, F15 memory)

- A move law: `Lg.tot.of_wp`, then step M.ev/M.ret with the rewrite kit and the routine laws (S2), and
  `h.*` for H; Budget(x, st, s) ≥ every routine budget used (Need's 3 × max covers the copy, the walk,
  the spine's argument cells); the post `Next.is(x, o, st2)` is `R.Inv(x, st2, s2)` for a next.
- Call moves: the first loop of M.call (wargs reversed onto wh: only field-1 stores) keeps H; the second
  is `call.frames`; then `Call.fs(rev(xs), fs) = AM.frames(xs, fs)` (a small list lemma), release_all(wenv).
- round.mem / input.mem: by the free list's discipline (M.alloc takes a new cell only when free = 0,
  then next - first = |L| by Part); they need routine-level facts about next (helpers in memory/impl:
  e.g. from Alloc.st, and the |L2| bounds of the routine laws).
- need.peak/budget.need/input.need/start.ok: port memory_bound.bend (4ebef88) and its kit
  (first_cell_past_table's hw.*, img_small's Bl, eval_facts' ev.stops for largest.step); 3 S for 2 S.
- code.fits: port cir_fits.bend (4ebef88); its NewCells is `free = 0` now.
- eval.stops: port ev.stops (eval_facts.bend 4ebef88, `stops`).

## Smoke (s4_smoke.bend; bend2 --check-only: only the imports' TODO count)

Round by round, on whole runs from St0: Inv, AS.ok (inv.vb), am.ok's AO.ok, Next.is / Halt.is against
AM.move's outcome (round.sim), round.mem, Fits.halt at a halt, out of memory only below Budget (and
M.input's below Input.budget). New cases, all pass: a Rwt whose proof is no Rfl (halt 2), a Mat miss by a
redex inside a Let's frame (halt 0, []), a Q2 bind of no Data by a redex and by a Let (halt 2), Prj on no
pair (halt 2); negative controls fail (a wrong book's moves; a wrong expected halt). Memory edge: see the
end of this file.

## Gates

(filled at the end)
