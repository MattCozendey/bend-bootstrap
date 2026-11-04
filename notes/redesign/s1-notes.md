# S1 notes: statement decisions vs the plan (shared kit, logic, header)

Lane S1 of P2. Branch `w/s1` (worktree `bb-wt/s1`). Files: `src/Compiler/Machine/shared.bend`,
`logic/{spec,impl}.bend`, `header/{spec,impl}.bend`, `s1_smoke.bend`. Names: `s1-names.md`.

## Changes vs the plan's text (§4.1, §4.2), and why

1. **WP is a computed def, and its post takes the halt post first.** `Lg.WP(s, b, K, H, st)`,
   `K: (U32 -> State -> Type) -> State -> Type`. Bend is affine: a WP that passes H both to a
   sequence's first part and into the continuation of the second uses H twice and is rejected. With
   K given H at each leaf (`K(H, st2)`), each path uses H once. A while is `Tot` inside WP; a
   primitive is `WP.ok(Cir.exec(0n, prim, st), ..)`, which is exactly Cir.exec's clause.
   `tot.of_wp`/`wp.of_tot` replace the plan's `tot.wp` (both directions; both proven).
2. **Predicate parameters are erased** (`Tot(.., -Q, -H)`, laws `for -Q`, `-H`, `-K`, `-I`).
   Uses inside a Pi or Sigma are erased, so Tot's body may name them freely; a relevant parameter
   would make every caller that names H twice (as `x => K(H, x)` and `H`) fail affinity.
3. **Every Data parameter and equation hypothesis of a law is reusable (`+`)**: proofs are affine
   too, and an equation proof is Data.
4. **No `K.P2`**: `P2` is already defined in two layer-A files (G5). Facts join with `A & B`.
5. **`Lg.Lim(st)` = `N.D(16n, U32.to_nat(Wa.Wasm.min(St.limit(st), 65536)))`**: the number of
   `Program.memory`, but the plan's `Nat.mul(65536n, ..)` overflows bend2's stack on a symbolic
   limit (it unfolds 65536 levels of Nat.add). With `min`, Lim ≤ 2^32, so the alloc and emit
   budgets hold also past cell 214748364 and for any limit: no premise on the limit is needed.
6. **Register count**: `Nat.is_lt(r, St.nregs(st))` premises, not `Mc.Mach.regs()`: logic does not
   import the machine (it is generic Cir logic).
7. **Primitive laws**: apply rules `wp.set/store/alloc/emit` (what a Cir stepper needs) besides the
   plan's rewrites `exec.set/store`; `exec.alloc` is one law with both outcomes (a new cell, or out
   of memory below 20 (next + 1) bytes). No `exec.halt` (it computes). The emit budget is
   20 next + outn + 1 bytes (checked at the edge in the smoke).
8. **Frame**: besides `frame.regs`/`frame.fixed` (exec level), `tot.frame` (registers outside
   `Cir.writes`, the same count, next not smaller, and `St.fixed`, in a Tot's post) and
   `tot.frame_out` (no emit: out and outn kept), because a Tot hides the exec equation that
   `frame.regs` needs.
9. **Accessors and their rewrites**: Bend makes no accessors, so `St.*` and the
   `<accessor>.<updater>` family (all proven, by matching the state).
10. **`Loop`** uses WP for the body (not Tot) and `&`; `tot.while` as the plan otherwise.
11. **Header**: defs keep the `Hd.`/`Tbl.` prefix (unique for G5); callers write `Hs.Hd.tag`.
    `Tbl.cell(t)` is the image's own table cell (`Img.table`), so `Tbl.mask/bind/former` agree with
    the table by definition for terms; machine tags: frames 32–40 and K.arg 41 have mask 1
    (field 2), Rwt's frame 38 has 3, FREE and the rest 0. Mask laws: the algebra of and/or/shifts
    (13 laws) plus `hd.*_of` and `hd.todo_of`; `mask.sub_bit` covers the copy's todo clear.
12. **`No(s, st)`** without erased parameters (its type must be `U32 -> State -> Type`).

## Checked against Cir (why the statements are true)

Each law was re-derived from Cir/impl.bend: exec's fuel only counts while rounds (a sequence
passes the same fuel to both parts, so `tot.seq` joins fuels by `exec.more` and `Nat.add`
commuted); `Cir.exec.alloc` traps once output began (so `wp.alloc` asks `outn == 0`), fails on
next ≥ 214748364 or when `Cir.room` finds no pages (both below 20 (next + 1) ≤ Lim's bound since
Lim ≤ 2^32 and need > lim means 65536·lim ≤ 20 next + 19); emit fails on next ≥ 214748365, on a
wrapped address (then 20 next + outn ≥ 2^32), or no room; `Cells.set` treats a non-node at a
level > 0 as empty, as `Cells.get` does, so `cells.get_set` holds for every `m`; `Cell.get`'s
default case makes `cell.get_set` need k, j ≤ 4.

## Gotchas found (for every lane)

- **An unfilled law is a dead claim**: a book that imports only `logic/spec.bend` cannot *use*
  `Lg.tot.of_wp` etc. in a proof. Import `logic/impl.bend` (and `header/impl.bend`) somewhere in
  the book; a law filled with a `?TODO` body is usable. In an impl file, a law's fill must sit
  above every def that uses it.
- `Cir.exec(f, ..)` does not reduce on a symbolic fuel f (its match splits the fuel first):
  split f (0n / 1n+p) before rewriting.
- A rewrite (`%e : P`) is a statement: `match st` must come before it. `%e : P` turns the `b` of
  `e: {a == b}` (marked `_` in P) into `a`; `(%e : P; t)` has type P[b] for `t : P[a]`.
- Nat literals ≥ 2^16 in a def that a check normalizes on symbolic data overflow the stack: use
  `N.D(k, x)`.

## Smoke (s1_smoke.bend; bend2 and kernel: 29 defs, 0 fail)

WP unfolds closed code to its run (sets, an if, M.make's alloc + stores with budget 60, a halt
through `M.need`), a while inside WP is Tot (M.nth, fuel 3); the alloc and emit budgets at their
edges (fits at next 3275 / outn 15; out of memory one cell / one byte later, with Lim below the
budget); `Cir.writes` of M.dec, M.alloc, M.copy, M.walk inside their scratch lists (plus the
target); only M.out emits; `St.kept`; `Tbl.mask/bind/former` on every kind of tag; the input
headers 1866/842 as `Img.header`; header parts read back. A negative control (a wrong register
value) fails.

## gen2 tally (lead's request)

g2pool's gen2 (w/g2pool, served in one WSL session; loads in 0.15–0.2 s):
- logic holes asked (budget 8 s, `--partial`): `cell.get_set`, `cells.get_set`, `frame.fixed`,
  `frame.regs`, `wp.wk`, `tot.any`, `tot.frame_out`, `exec.alloc`: **0/8 proven**; 0.9–11 s per
  ask (wp.wk and exec.alloc hit the budget, 8–15 M lookups). Useful: none. One partial
  (`tot.frame_out`: applied `tot.wk` and left `Q(x) -> Q(x) & frame facts`, which is not provable
  that way: misleading). The "why" lists propose `N.rel_eq`, `K.nat.is_eq_ok` and `Equal.cong` with
  an unfixable `A` for equations of non-Nat types: noise. `wp.wk` I then proved in one line from
  `tot.of_wp`, `tot.wk`, `wp.of_tot` (gen2 did not find that composition).
- header holes (mask algebra, `hd.tag_of`): **0/9**; 10–930 ms each. They need Word-level
  induction lemmas that do not exist yet; gen2 only proposes the match on n.
- earlier (gen2 on feature/redesign, `prove`): kit lemmas `disj.has`, `sub.has`, `sub.con`: 0/3
  (its candidate `%Equal.sym(.., disj.has(x <> rest, ..))` is a non-structural self-call).
- WIP `--wp` stepper (w/gen2-wp) on two closed-code Tot goals in a scratch file: on two sets it
  **stepped both** (tot.of_wp, wp.set with register facts chained by reg.set, nregs.set) and left
  only the post leaf, in 0.1 s: useful. On a set that reads a field it stopped at once ("reads
  fields only when the proof can match the start state"). It first failed with "an unfilled law is
  a dead claim" because the scratch file imported only logic/spec (see Gotchas).

## Follow-up (8b21a13): kit for the --wp stepper

`K.bool.case` (as gen2-wp-notes.md proposed) and `Lg.reg.some` in S1's form: the value is the
accessor `Lg.St.reg(st, q)` (logic cannot name S2's `Hp.V.reg`, which is the same value), plus its
converse `Lg.reg.lt` (a Reg fact gives the count fact, e.g. for nth.spec's t1/t2). The register count
is reachable from every routine law (see s1-handoff.md, "Register count"); nothing is missing.

## gen2 tally, round 2 (lead's rule: gen2 first; gen2 + --wp of feature/redesign 015dba0)

Asked in one WSL session (serve, ask, stop), `--partial` (`--wp` on the logic file), budget 8 s
(logic) / 4 s (header).
- **Retro-test** (the bodies blanked in a scratch copy): `list.get_lt` **proven** (37 ms),
  `Lg.reg.some` **proven** (15 ms), `Lg.reg.lt` **proven** (7 ms, given `list.lt_get`);
  `list.lt_get`: partial, only the Nil case (None = Some refutation) open (0.2 s): useful;
  `bool.case`: nothing (goal `G`, 14 ms). So 3 of 5 would have needed no hand work.
- **Open logic holes (11)**: 0 proven. `wp.alloc`, `wp.emit`, `tot.while` (--wp, 0.04–1 s): a leaf
  whose hint is "apply Lg.wp.alloc / Lg.wp.emit / Lg.tot.while", i.e. the law being proven
  (circular: misleading; the stepper should not offer a def's own law there either).
  `tot.frame`, `tot.frame_out`: "dead end, not shown" (correct now). `cell.get_set`,
  `cells.get_set`, `frame.fixed`, `frame.regs`, `tot.any`, `exec.alloc`: plain partial `?TODO`,
  0.9–10 s (exec.alloc spends the whole budget).
- **Header holes (18)**: 0 proven; mask laws 15 ms–1 s, `hd.*_of` and `mask.sub_bit` time out at
  4 s. They need Word-level lemmas (induction on the width) that the book does not have.
- Verdict: gen2 now closes "apply a kit lemma under `match st`" and plain list inductions on the
  first try; it does not yet find a structural induction that needs a new helper (frame laws, trie
  lemma) or 32-bit reasoning.

## Follow-up (f28882f)

`wp.alloc`/`wp.emit` take `@+p` (reusable page binder). `K.u32.is_zero_t`: gen2 first (partial
`?TODO` in 0.3 s, `--lemmas` offers only Equal.sym/trans): no help; by hand through a Word lemma
(`word.cmp_zero`, induction on the width), first try.
