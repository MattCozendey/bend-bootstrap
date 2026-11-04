# P1 notes: deviations from the plan, and why

P1 = redesign-plan.md §3 and §5.3, on feature/redesign. Commits: 4908672 (Machine/impl.bend), ec0f1a0
(deletions, runs_as_eval.bend bodies). Each deviation keeps the laws' meaning (the laws, spec.bend,
proof.bend and layer A are untouched) and is decided on merit.

1. **`M.dec.scr` includes `free`.** §3.2 says the cascade writes only `fl aq am dr dk`. Its
   `M.release` also writes `free` (the free list's head). So `M.dec.scr() = [free, dr, aq, am, fl, dk]`.
   No caller passes any of them to `M.dec` (checked by computation, below).
2. **`M.one(r)` moves r's pointer into the local; it does not inc.** §3.3 says `M.one` incs and the
   callers release the local with `M.release.arg`. With the move, the two callers that own r
   (`M.redex`'s λ case with y, `M.ret.let` with focus) drop their own `M.dec(r)`, and
   `M.release.arg(wa)` drops that pointer; the one caller that borrows (`M.ev.let`'s dead case, y from
   the focus) incs y first. Same counts, one inc and one dec less per β-step, and the local still owns
   its term (D2).
3. **`M.call` moves each argument left into its frame.** It pushes the frame with the argument's term
   and frees the argument cell by `M.release` (not inc, then `M.release.arg`). Same reason: the frame
   takes the argument's pointer; no count changes.
4. **No `M.st(1, r, 0)` in `M.dec`** (the plan's sketch had it): field 1 is already 0 when the count
   drops to 0, so the cell heads the list `fl` as it is.
5. **`M.data.of(a, b, q)`, not `M.data.tup(c)`.** One expression over the two parts and the quantity:
   `M.finish` passes the fields of c and `M.q(c)` (only for a Tup, since another tag's fields need not
   be cells), `M.ret.tup` passes the registers x, focus and q. It is 512 when b is DATA and (a is DATA
   or q = 0), as `El.Term.is_data` asks.
6. **`M.copy.root` and `M.copy.end` are inlined into `M.copy`** (one caller each, two statements);
   `M.copy.push()` and `M.copy.part()` stay named, on fixed registers (`t2 csrc cnew ck cs`).
7. **`M.walk.app` keeps the variable's index in t1** (not wb), so that it calls `M.nth` (whose
   interface is t1 = steps, t2 = start cell, result in t2), as the copy does.
8. **The cascade reads the table without a tag guard.** Only term cells reach `fl` (M.dec is only
   called on terms, and a term's parts are terms), so `M.entry(2, aq)` reads the table for tags 0–18.
   The old guard (`tag < 32`) existed because the old pend list mixed frames and terms; the free list
   now holds only FREE cells, which the cascade never reads.
9. **Scratch lists** are defs beside each routine that writes registers: `M.<r>.scr()` for release,
   dec, alloc, make, push, pop, poison, nth, copy, release.arg, release.all, walk, one, swap, out,
   input (`M.inc` writes no register). A routine with a target register (alloc, make, poison, copy,
   release.all's list) does not list its target. Checked by computation (redesign-scratch/measure.bend):
   the set/alloc targets of each routine are inside its list, with its target added.
10. **No D5 fallback.** `NS(Mach.code())` = 21,892 nodes (old 39,318; bound 65,536): removing the three
    inlined `M.dec`s from every `M.alloc` saves more than the cascade inlined at each `M.dec` costs.
11. **The two merge commits** (d57bb26 gen2-up, 6693442 w/laws) carry the repo's default author email;
    every P0/P1 commit carries mpereira@blueboltsolutions.com.
12. **compile.ts's command** (`getCompile`, with its big stack) moved from run.ts into Shared/shared.ts,
    since census.ts is its second caller (AGENTS 2.5.4). census.ts mutates typed arrays: speed is a
    priority there (2.5.1; the lead was not reachable, so decided on merit: a census over up to 2^28
    cells cannot be done without mutation in reasonable time).

No other change: the image (Img.*), the table, the frame kinds, `M.out`, `M.input`, and the Cir
constructs used are as before.
