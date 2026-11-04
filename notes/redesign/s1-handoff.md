# S1 handoff: shared kit (B0), logic (B1), header (B2)

Branch `w/s1` off `feature/redesign` (worktree `C:\Users\mathe\source\repos\bb-wt\s1`). Not pushed,
not merged. Names and exact headers: `s1-names.md`. Decisions and gen2 tally: `s1-notes.md`.

Commits: 949139d (headers, stubs), 5b43485 (smoke), 47345d7 (kit proven, Lim as N.D, + hypotheses),
019841b (exec.more, tot.wk, tot.if, exec.set), 6189fe1 (tot.seq, exec.store, wp.set, wp.store),
a5ff23e (tot.of_wp; erased predicates), be0649f (wp.of_tot), 4f3ddcc (wp.wk); merged feature/redesign
(fast-forward to 015dba0), 8b21a13 (bool.case, St.reg, reg.some, reg.lt); merged feature/redesign (fast-forward to 9dd2ced),
f28882f (wp.alloc/wp.emit `@+p`, kit u32.is_zero_t).

## Files

| File | What | Holes |
|---|---|---|
| `Machine/shared.bend` | Has, Mem, Disj, Sub; bool.*, nat.*, has.ne, disj.has, sub.has, sub.con, list.length_set, list.get_set | 0 (all proven) |
| `Machine/logic/spec.bend` | St.* accessors/updaters, Reg, Lim, Ok, Tot, No, WP (+WP.ok/if/pick), Loop, Cir.writes, Cir.emits, Regs.kept, St.kept; 50 laws | (laws) |
| `Machine/logic/impl.bend` | one def per law; kit lg.* (ported `mono` from 4ebef88) | 11 |
| `Machine/header/spec.bend` | Hd.tag/q/has/fv/todo/flag_bit/fits, Tbl.cell/mask/bind/former; 18 laws | (laws) |
| `Machine/header/impl.bend` | one def per law | 18 |
| `Machine/s1_smoke.bend` | computed checks (outside main's closure; delete in P5) | 0 |

## Proven (41 of 52 logic laws; kernel-checked by name: 41 `spec.*` defs, 0 fail)

exec.more, tot.seq, tot.if, tot.wk, **tot.of_wp, wp.of_tot**, wp.wk, exec.set, exec.store, wp.set,
wp.store, reg.* (4), nregs.* (4), cells.set/store/alloc/emit, next.* (4), outn.* (4), fixed.* (4),
lim.* (4), reg.some, reg.lt. The kit: all (incl. bool.case).

## Open (for P3)

- logic (F2): `tot.any` (determinism + exec.more), `tot.while` (strong induction on the measure;
  fuel = rounds' fuels joined by exec.more), `exec.alloc`, `wp.alloc`, `wp.emit` (Cir.room and
  next arithmetic, see s1-notes "Checked against Cir"), `cells.get_set` (trie induction over the 32
  bits), `cell.get_set` (5x5 split), `frame.regs`, `frame.fixed` (induction on fuel and statement,
  as mono), `tot.frame`, `tot.frame_out` (from the frame laws, per register).
- header (F3): the 13 mask laws (Word-level lemmas by induction on the width first, then U32), then
  `hd.tag_of/q_of/fv_of/has_of/todo_of` from them.

## For S2 and S4 (must read)

- **Import `logic/impl.bend` (and `header/impl.bend`) in your proof books**, not only the specs:
  bend2 refuses a proof that uses a law with no fill in the book ("an unfilled law is a dead claim").
  S2's branch (5e954c7) imports only the specs and has the pre-a5ff23e logic/spec (relevant Q/H):
  merge w/s1 again.
- Proving a routine law: `Lg.tot.of_wp` turns `Tot(code, ..)` into `WP(code, b, h => x => Q(x), H, st)`;
  closed code then unfolds by evaluation; step primitives with `wp.set/store/alloc/emit`; at a call
  of another routine use `Lg.wp.of_tot` + its law + `Lg.tot.wk`; open a while with `Lg.tot.while`.
  The WIP `--wp` stepper (w/gen2-wp) already steps register sets this way.
- `Cir.exec(f, ..)` needs f split before it reduces; `match st` before any `%` rewrite.
- Frames: `{K.Sub(Lg.Cir.writes(<code>), <list>) == True{} : Bool}` closes by `{==}` (smoke: M.dec,
  M.alloc + target, M.copy + target, M.walk).

## Register count in the routine laws (for S2's owner)

`reg.some` needs `q < St.nregs(st)`. It is reachable from every routine law's premises: `Hp.H` →
`Room` → `Fix` → `Nat.is_eq(Lg.St.nregs(st), Mc.Mach.regs())` (by `K.bool.and_l/and_r`, then
`K.nat.is_eq_ok`); `out.spec` has it through `Inv` → `Hp.H`; `release.spec` states
`Nat.is_lt(Mc.R.free(), Lg.St.nregs(st))`; `input.spec`'s start state `I.St0(Mc.Mach.regs(), ..)` has
it by computation; `nth.spec` has Reg facts for t1 and t2, which give their bounds by `Lg.reg.lt`.
No premise is missing. Two suggestions to S2 (its files, not changed here): `Hp.V.reg` is
`V.or0(Lg.Reg(st, r))`, the same value as `Lg.St.reg`; defining `V.reg` as `Lg.St.reg` (or one lemma
`V.reg(st, r) == Lg.St.reg(st, r)`) lets the stepper use `reg.some` on S2's invariants with no
bridge. And the count as an equation `{Lg.St.nregs(st) == Mc.Mach.regs()}` is what the stepper
reads; `Fix` gives it as a Bool `Nat.is_eq`, so one `K.nat.is_eq_ok` turns it into one.

## Gates run

- G1 at 8b21a13 (changed files): shared.bend ALL PROOFS CHECK, kernel 29 defs 0 fail; logic/spec 52
  TODOs (laws), kernel 36 defs 0 fail; logic/impl 11 TODOs, gate kernel 96 defs, 11 fail = exactly
  the 11 holes (a hole is lowered as a self-call), and the 41 law fills by name 0 fail. Files of
  other lanes that import them still load (routines/spec, heap/spec: only TODO counts).
- G1 earlier (`~/lead/gate.sh`, mirror `~/wt/s1`): shared.bend ALL PROOFS CHECK, kernel 25 defs 0 fail;
  logic/spec 50 TODOs (laws), kernel 35 defs 0 fail; logic/impl 11 TODOs, kernel 44 helper defs 0
  fail + 39 law fills by name (`spec.*`, lowered alone to /tmp/s1-logic.bendtt) 0 fail;
  header/spec and header/impl 18 TODOs, kernel 11 defs 0 fail; s1_smoke 29 defs 0 fail.
  Note: gate.sh writes /tmp/gate-<wt>-<basename>.bendtt, so two `impl.bend` of one worktree
  overwrite each other's lowering; lower and check law fills right after their own file.
- G5: no def/law/type name of the six files is defined in any other .bend under src/ (feature/redesign
  + w/s1), nor in S2's own files (heap/, image/, routines/, s2_smoke at 5e954c7).
- G2/G3: not run (the files are outside main's closure until S4 imports them).
