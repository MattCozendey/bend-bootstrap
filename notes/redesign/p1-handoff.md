# P1 handoff: the machine as implemented (for the P2 skeleton writers)

Branch feature/redesign. Code: src/Compiler/Machine/impl.bend (commit 4908672). Old proof tree deleted
(ec0f1a0). Deviations from the plan: p1-notes.md. Gate results: end of this file.

## Registers (`Mach.regs() = 53`)

| # | name | # | name | # | name | # | name |
|---|---|---|---|---|---|---|---|
| 0 | focus | 14 | y | 28 | wres | 42 | oc |
| 1 | mode | 15 | z | 29 | wok | 43 | ow |
| 2 | sp | 16 | q | 30 | wb | 44 | ov |
| 3 | free | 17 | n | 31 | wh | 45 | oi |
| 4 | dx | 18 | fr | 32 | cs | 46 | ii |
| 5 | dr | 19 | k | 33 | csrc | 47 | ib |
| 6 | aq | 20 | p | 34 | cd | 48 | il |
| 7 | am | 21 | wt | 35 | ck | 49 | iu |
| 8 | fl | 22 | wenv | 36 | cnew | 50 | ij |
| 9 | dk | 23 | wargs | 37 | cenv | 51 | t1 |
| 10 | c | 24 | wa | 38 | clen | 52 | t2 |
| 11 | h | 25 | wx | 39 | cj | | |
| 12 | tag | 26 | wq | 40 | croot | | |
| 13 | x | 27 | wn | 41 | cm | | |

`wb` is now used only by `M.walk.prj` (the pair's quantity).

## Header (field 0)

| Bits | Meaning |
|---|---|
| 0–5 | tag: formers 0–18 (Var 0, Ref 1, Ann 2, Let 3, Typ 4, Min 5, All 6, Lam 7, App 8, Sig 9, Tup 10, Prj 11, Enu 12, Lab 13, Mat 14, Efq 15, Eql 16, Rfl 17, Rwt 18); frames 32–40 (`K.app_arg` 32, `app_val` 33, `app_fun` 34, `let_in` 35, `tup_b` 36, `tup_a` 37, `rwt` 38, `min_b` 39, `min_a` 40); `K.arg` 41; `K.free` 46. (44 and 45 are gone.) |
| 6–7 | q |
| 8 | VALUE (`F.value` 256) |
| 9 | DATA (`F.data` 512): set when the cell is made (image, input, `M.finish` for a copied Tup, `M.ret.tup`) |
| 10 | STATIC (`F.static` 1024) |
| 11 | KNOWN (`F.known` 2048): frames and argument cells only |
| 12 | BUILD (`F.build` 4096): a new cell of a copy, parts not all copied |
| 13–31 | fv (`M.fv` = shr 13); while BUILD, bits 13/14/15 (8192/16384/32768) are the todo bits of fields 2/3/4 |

- Poison: a Var cell (tag 0) whose fv is 0; made by `M.poison(r)` = `M.make(r, 0, 0, 0, 0)` (header 0,
  count 1, fields 0). A real Var has fv ≥ 1.
- FREE: tag 46, field 1 links the free list (head: register `free`); fields 2–4 stale.
- Field 1: count of a live term cell; list link of a frame (stack, from `sp`), an argument (chain), a
  BUILD cell (the copy's stack, from `cs`), a cell on `fl` (the cascade's list) or a FREE cell.
- Copy root: header `Prj | BUILD | 8192` = 12299, field 1 = 0, field 2 = the source; released (FREE)
  at the end of `M.copy`.
- Input cells: `M.h.static()` 1866 (Tup q1 VALUE DATA STATIC), `M.h.data()` 842 (Tup q1 VALUE DATA).

## Routines (impl.bend), and their scratch lists

A routine's `scr()` lists the registers that it may write, besides the target register a caller names.
Each list is checked by computation: the set/alloc targets of the routine's code are inside it.

| Routine | Effect | `scr()` (besides the target) |
|---|---|---|
| `M.inc(r)` | count of r's cell + 1 unless r = 0 or STATIC | none (writes no register) |
| `M.release(r)` | r's cell: tag FREE, onto the free list | `[free]` |
| `M.free.part(k, bit)` | (inside the cascade) field k of aq loses a pointer when am has bit; at 0 onto fl | — |
| `M.dec(r)` | r's term cell loses a pointer unless r = 0 or STATIC; at 0 it and, in cascade, each part left with none, are freed | `[free, dr, aq, am, fl, dk]` |
| `M.alloc(r)` | r gets a cell, all zeros: the free list's head, or a new cell (`Cir.Stmt.alloc`) | `[free]` |
| `M.make(r, h, a, b, c)` | alloc, then fields h, 1, a, b, c | `[free]` |
| `M.push(h, a, b)` | new frame (h, sp, a, b) on top | `[free, fr, sp]` |
| `M.pop()` | top frame off and freed (its parts are the caller's) | `[free, fr, sp]` |
| `M.poison(r)` | r gets a new poison cell | `[free]` |
| `M.nth()` | t2 := the cell t1 steps down (field 1) from t2 | `[t1, t2]` |
| `M.copy(r, src)` | r gets the copy of src's term (subst at depth 0 with locals cenv/clen; a variable past them → poison; no shift) | `[free, cs, csrc, cd, ck, cnew, cj, croot, cm, t1, t2]` |
| `M.release.arg(a)` | dx := field 2 of a; `M.dec(dx)`; `M.release(a)` | `[free, dx, dr, aq, am, fl, dk]` |
| `M.release.all(l)` | each argument cell of the list l: `M.release.arg` | `[free, wa, dx, dr, aq, am, fl, dk]` (target: l) |
| `M.walk()` | the walk of wt on wargs: wres 1 leaf / 2 waits / 3 none; wenv, wn the locals | `[free, dx, dr, aq, am, fl, dk, wt, wenv, wargs, wa, wx, wq, wn, wres, wok, wb, wh, t1, t2]` |
| `M.one(r)` | the one local of a copy: a new argument cell that takes r's pointer (no inc); cenv, clen := it, 1 | `[free, wa, cenv, clen]` |
| `M.swap(hd)` | the top frame h gets the focus and the header hd; its term becomes the focus, mode 0 | `[n, focus, mode]` |
| `M.out()` | mode 1, no frame: halt 0 with the bytes of the focus' value, or halt 2 | `[oc, ow, ov, oi, t1, t2]` |
| `M.input()` | the start term into focus | `[free, focus, ii, ib, il, iu, ij, t1, t2]` |

Helpers without scr (expressions or composites): `M.data.of(a, b, q)` (DATA of a pair from its parts'
headers), `M.finish(c)` (writes t1, t2, cm; field 1 := 1; header := tag/q | DATA of a Tup | fv),
`M.fv.part`, `M.copy.push()` (t2 := new BUILD cell for csrc, onto cs, put into cnew's field ck),
`M.copy.part()`, `M.todo*`, `M.bump`, `M.get`, `M.put`, `M.pick`, `M.max`, `M.fld`, `M.takes`,
`M.walk.lam/prj/mat/app`, `M.call(partial, done)`, `M.redex()`, `M.ev.*`, `M.ret.*`, `M.need(c, s)`
(= if c then s else halt 2).

## Top level

- `Mach.round() = M.if(M.eq(M.g(R.mode()), M.c(0)), M.ev(), M.ret())`.
- `Mach.code() = M.do([M.input(), M.set(R.mode(), M.c(0)), M.while(M.c(1), Mach.round())])`.

## Ownership rules (what the heap invariant must say)

- A live term cell's count = pointers from live term cells' counted fields (table mask; a BUILD cell's
  todo fields are not counted) + from frames' term fields (field 2; Rwt's frame fields 2 and 3) +
  from argument cells' field 2 + owned registers.
- Each argument cell owns its term (D2): made with an inc'd term (walk.prj both fields, walk.app's
  local, redex's y and spine arguments, ev.let's y) or with a moved pointer (`M.one` from redex's y
  and ret.let's focus), or a new poison (walk.app with no local).
- Moves of a pointer, no count change: `M.one`; `M.call`'s arguments left → frames; a frame popped →
  the register that read it; `M.walk.lam`'s argument → wenv.
- `M.alloc` changes no cell but the one it takes; only `M.dec` frees term cells; `M.release` frees
  frames, arguments and the copy root.
- The copy (`M.copy`) frees nothing; its only allocations are `M.copy.push` (BUILD cells), poison
  cells, and its root.
- `M.walk.mat` on a miss changes no cell (D4). On a hit, the label's argument is released (its label
  loses a pointer).

## Measurements of the new code

- `NS(Mach.code())` = 21,892 (bound 2^16 = 65,536; old 39,318). `T.dep(Mach.code())` = 2,686 (bound
  50,000; old 5,184). `ok.stmt(Mach.code(), 53)` = True.

## For S2 and S4: the smoke check AM.move vs Mach.round()

S3 wrote `AM.move` (am/spec.bend) before this code existed, so the plan's smoke check (§5.4: `AM.move`
on small terms equals what `Mach.round()` does on the same state, both computed with `{==}`) is
still open: S2 or S4 must run it (see s3-handoff.md, s3-notes.md "AM.move vs the machine"). A read of
s3-notes' mapping against this code finds it consistent: initial call arguments KNOWN iff live(q);
walk Prj: the first field KNOWN iff the argument's KNOWN and live(r), the second keeps the argument's
KNOWN; walk local: the local's KNOWN; no local: a poison argument, not KNOWN; Prj redex frames KNOWN
(second) and live(r) (first); Mat miss frame KNOWN; a label miss in the walk changes nothing (D4);
mode 0 returns when VALUE is set or the table's former bit is 1 (not for Tup). P1's deviations 2 and 3
(moves of pointers in `M.one` and `M.call`) change counts only, never a term or a flag.

## Gates (P1 state: ec0f1a0)

- **G1** gate.sh: Machine/impl.bend: bend2 ALL PROOFS CHECK; kernel 249 defs, 0 fail.
  Machine/runs_as_eval.bend: bend2 "4 TODOs"; kernel 4 defs, 4 fail = exactly the 4 holes.
- **G2** bend2 main.bend: "5 TODOs found" (11 s) = holes.md (4 runs_as_eval + mach_wasm.uniform).
- **G3** milestones.ts steps 1–5 on ec0f1a0 (WSL clone ~/bb-rd): all 5 ok (725 s).
- **G4** run.ts: 23/23 cases ok; with TRUSTED=1 FRESH=1: 23/23 and "the Lean interpreter compiles echo
  to the same bytes", 0 failed. Computed layer-A checks with the kernel: Cir/module_valid.bend (67
  defs, 0 fail: mach.ok), Cir/simulation_code_size.bend (23 defs, 0 fail: mach.nodes),
  Cir/simulation_host.bend (99 defs, 0 fail: mach.hR, mach.hd).
- **G5** `bun check`: no error in our files (224 errors, all inside the bend submodule's bend.ts and
  safe.ts, which lower.ts imports; the same as before P1). No def/law name of Machine/ is defined in
  two files of the closure (22 duplicates remain, all in layer A, img_small and need_big, untouched
  and older). No import of a deleted file (G2 loads).
- **Census** (P0's, again): self-compile peak 10,797 pages = 0.659 GiB (4ebef88: 11,800 = 0.720 GiB,
  −8.5 %), 216 s (was 798 s); the prog books −35 to −41 % pages, 5–6× faster (p0-measure.md §6).
- After the merge of w/s3 (9daf8f5): G1 on its 5 files: bend2 prints only TODO counts (unfilled
  laws), kernel 0 fail; G5: no name clash with the closure; main's closure unchanged (35 files, 5
  holes), so G2/G3 stand.
