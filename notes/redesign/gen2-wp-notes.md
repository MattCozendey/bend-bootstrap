# gen2 --wp: notes (agent gen2-wp, branch w/gen2-wp from w/g2pool)

## What it is

`gen2 prove|ask <file> <def> --wp` (off by default): on a goal `Lg.Tot(code, st, b, Q, H)` or `Lg.WP(code, b, K, H, st)`
with closed code (S1's logic, s1-names.md), gen2 writes the proof that steps the code, and leaves only the real leaves as
numbered `?TODO`s, each with a one-line hint and its goal.

- Module `src/Shared/scripts/gen2_wp.ts` (the stepper); hook in gen2.ts: `wpGoal` (verify by bend2's def check with the
  text in place, try each leaf with the leaf tactics, report), `wpWhole` (a body that is `?TODO`), and `proveHoles` (a
  `?TODO` alone on its line). With the flag off nothing runs.
- A Tot goal becomes WP by `tot.of_wp` (K = `h => Q`). WP is computed by the code, so a sequence and an if need no law:
  the stepper proves the first statement's WP with the post "then the rest's WP" (continuations printed eta-reduced:
  `h => t => Lg.WP(rest, b, K, h, t)`). A sequence is flattened; its suffixes are lets built from the end (linear size).
- set: `wp.set`; store: `wp.store` (its cell fact `{Lg.St.is_cell(st, c) == True{}}` from the context). Register reads in
  an expression: rewritten one by one by facts `{Lg.Reg(st, r) == Some{c}}` (hypotheses for the start state; `reg.set`,
  `reg.store` after a step, chained by `Equal.trans`), the register count by `{Lg.St.nregs(st) == N}` carried by
  `nregs.set`/`nregs.store`. Values are computed (nf) and printed.
- if: its condition rewritten by its value (`WP.if`); the branch is taken when `U32.is_zero(v)` computes, or once Bool
  facts of the context rewrite parts of it (one rewrite per fact), or by a split on the smallest Bool part that decides
  it both ways, with the kit lemma `bool.case` (below) when the book has it: each branch gets the fact
  `{part == True/False}`, which later ifs use too (at most 4 nested splits).
- Field reads (and cell facts after stores): when the goal's state is a parameter (a whole body), the proof starts with
  `match st:` (a let `ws0` names the constructor); then the accessors compute, a field read needs only the start's
  is_cell fact (rewritten inside `Cir.eval.field`), and that fact holds after sets and stores by computation. gen2 tries
  this second when the plain run leaves a field read or a cell fact, and keeps the run that steps further.
- Leaves: the post at the end (closed by a hypothesis when one fits), an undecided if, a loop (tot.while's
  obligations), a halt (H; with `Lg.No` a fact must rule the path out), alloc/emit (wp.alloc/wp.emit's premises), a
  routine with a law `<name>.spec` (close by `wp.of_tot` + the law + `wp.wk`), a byte/size read, the step limit (400) or
  the time budget (half the ask's budget; the rest for the leaves).
- Every text is checked by bend2's def check before it is printed (the fragment check gen2 used at first accepted an
  erased H passed live; the def check does not). A text that does not check is not shown; the normal search runs.

## Requests

- S1 (done in a5ff23e): predicate parameters of the laws erased (-Q, -H, -K): without it no multi-step proof checks.
- Kit lemma for the if split (shared.bend), proven by `match b`:
  ```
  def bool.case(+b: Bool, -G: Type, t: @+h: {b == True{} : Bool} -> G, f: @+h: {b == False{} : Bool} -> G) -> G:
    match b:
      case True{}:
        t({==})
      case False{}:
        f({==})
  ```
- For S2's routine statements (premises are Bool invariants, registers read through `Hp.V.reg`): a kit law
  `reg.some: {Nat.is_lt(q, St.nregs(st)) == True{}} -> {Lg.Reg(st, q) == Some{Hp.V.reg(st, q)}}` (or its S1 form with an
  accessor), and the register count `{Lg.St.nregs(st) == Mc.Mach.regs()}` reachable from `Hp.H` by `bool.and_l/and_r`.
  Then --wp reads every register; today it needs a Reg fact per register read.
- S1 (open): the page binder of `wp.alloc` and `wp.emit` relevant, `for q: @+p: U32 -> K(H, St.alloc(st, r, p))` (and
  `St.emit(st, v, p)`). With `@p` the stepped proof is refused ("wp0 consumed more than once": p is used in the state
  and in its facts). The testbed has the patch; every alloc/emit proof that --wp prints fails the def check until it
  lands, so --wp shows none.
- S1 (open): `u32.is_zero_t(x, h: {U32.is_zero(x) == True{} : Bool}) : {x == 0 : U32}` (Fix states the output count
  so; wp.alloc asks the equation).
- S2 (open): see the round-3 table (swap's hh, Chs.go's nested pattern, the free head's is_cell, alloc.cell).

## Measurements

| version | regression (flag off) | --wp on the test goals (bb-wt/scratch/gen2/wp, S1 4f3ddcc) |
|---|---|---|
| fa30ae4 | need_big 80/119 @1000 ms, median 4 ms; 51 crash states: 0 crashes | sets, decided ifs, Bool-split arms: proven (14-70 ms) |
| 50d4396 | same | + M.release, M.pop (stores, a field read) step to the post (170-530 ms) |
| a4cdaed | need_big 80/119, median 3 ms; 51 crash states: 0 crashes | + undecided if split by bool.case: both branches stepped |
| next | (see commit) | + symbolic registers, facts inside Bool invariants; S2's holes: see below |
| f034d97 | need_big 80/119, 21.7 s; 51 crash states: 0 crashes | + alloc/emit stepped, loop obligations; w.t3-w.t10 as before |
| 6b3cfdd | 79-80/119 (chain2 at the edge); 0 crashes | + st0 laws, size/byte reads, r < N, nat.is_eq_refl |
| 6c89675 | need_big 80/119 (2 of 2 runs), 24.7-25.9 s, median 3 ms; 0 crashes | stall window 0.6 of the budget |

Baseline before the hook: need_big 80/119, median 3 ms (gen2-up 7727b7d).

## Hit rate on S2's routine holes (w/s2 d23476f, testbed copy, `--wp --budget 4000`)

18 holes (prims 10, nth, dec 3, copy, walk, out, input). Closed: 0. Every one stops at its first or second statement, each
with a clear one-line reason (0.9-5 s per ask, load included; h.arg/h.node are not Tot goals):

| stops at | holes | what unblocks it |
|---|---|---|
| a register read with no fact (sp, free, reg 0) or no register count | pop, release (after 2 stores), out, walk, input | a kit law `reg.some` (below) and the count `St.nregs(st) == Mc.Mach.regs()` reachable from the invariant |
| an op in a condition, and the proof file does not import Wasm/impl.bend (the op cannot be named) | alloc, inc, dec | `import ../../../Wasm/impl.bend as Wa` in the routine proof files |
| a field read, the run with `match st` stopped by the same missing register fact | swap, release_arg | as the first row |
| a routine call with a law (M.alloc in make/push, M.make in one/copy) | make, one, push, copy | done by hand today (wp.of_tot + the law + tot.wk); next for gen2: instantiate the law from the call and the context |
| a loop | nth, release_all | tot.while with an invariant (the lane's reviewer) |

What works today on S2's code: symbolic registers (a parameter r with `{Lg.Reg(st, r) == Some{c}}`; two registers told apart
by computation or by a fact `{Nat.is_eq(r, q) == False{}}`), facts inside a Bool invariant (`&&` split by bool.and_l/and_r,
`Bool.not` by bool.not_t, `Cir.is_cell(c, St.image(st), ..)` as a cell fact, `Nat.is_lt(r, St.nregs(st))` as a count fact),
stores with their cell fact. release.spec steps its two stores and stops at the read of free.

## Round 2 (after S1's reg.some/reg.lt/bool.case and S2's Wasm imports, feature/redesign 85af8f7)

- A routine call with a law: `wp.of_tot` + `tot.wk` + the law, instantiated by gen2's matcher: the law's parameters from
  the call's code, its state and the goal's budget, then from its premises matched against the context's facts (and the
  conjuncts of the Bool invariants); a premise that computes closes by `{==}`; the halts by identity, or `Empty.absurd`
  for `Lg.No`; the post: identity when it is the goal's own, else a leaf "after <law>: the rest from x, with q".
- Registers with no fact: `reg.some` (value `Lg.St.reg(st, q)`) with `q < St.nregs(st)` from the count; the count from
  `Fix`'s Bool `Nat.is_eq(St.nregs(st), Mach.regs())` (by `K.nat.is_eq_ok`), found by unfolding the invariant defs
  (Hp.H, Room, Fix: a Bool def whose body is an && is opened, up to 24 levels); a symbolic register's bound by `reg.lt`.
- Never circular: the stepper refuses to use the law it is proving (or the law that def fills), and a leaf never
  suggests it (S1's report on wp.alloc, wp.emit, tot.while).
- Every "proven"/"filled" claim passes bend2's def check: the whole-body proofs, each hole's fill (with the body as it
  is), the cached answers, the --wp texts (by the def check with the text in place); and now once more on the whole
  filled body before it is printed (a helper-free body). The fragment check (tryText) is only a pre-filter in the search.

### Re-measure on the 18 routine holes (round 2)

Closed: **release.spec** (proven by --wp, 0.5 s; its body: 4 steps, the post by `{==}`). The others, by where they stop:

| stops at | holes |
|---|---|
| a field read whose cell has no is_cell fact (the frame's cell, St.reg(st, sp)) | pop (after 2 steps), swap, release_arg |
| the post after a routine law (wq : {x == R.Alloc.st(st, r)}: stepping on from Alloc.st needs its register/cell facts) | make, push |
| make.spec not instantiable (its value parameters hv.. are fixed by Ev facts the caller does not have) | one, copy |
| an alloc statement (wp.alloc not stepped yet) | alloc (after 3 steps) |
| the post at the end, with an if split (both branches stepped) | inc, dec (3 steps, 2 leaves) |
| a loop | nth, release_all, walk (after 4 steps), out (after 2 steps) |
| a start state I.St0(..) with no count fact | input |
| not Tot goals | h.arg, h.node |

## Round 3 (feature/redesign bec2fe8: S2's facts merged)

New in --wp:

- alloc and emit statements step: `wp.alloc` / `wp.emit` under their page binder (`wpN`); `St.outn == 0` carried from
  a fact on the start by `outn.set/store/alloc`; the budget premise from a context fact (else a leaf); the registers
  after it by `reg.alloc/emit`, the count by `nregs.alloc/emit`. Test goal w.t10: 3 statements, 1 leaf (the post).
- A loop with no routine law: the leaf prints tot.while's exact obligations, ready to fill: the replacement text
  `Lg.wp.of_tot(.., Lg.tot.while(c, body, b, I, Q, H, r, n0, st, i))`, the types of I, r and i, an invariant skeleton
  over the registers that the loop writes, and the values of the registers that it reads (nth, release_all, walk, out,
  input).
- Equation laws about a state that a function builds: `<f>.nregs`, `<f>.reg` (`I.St0`: S2's st0.nregs, st0.reg).
- size and byte reads, computed from the state's input.
- A symbolic register's bound `r < St.nregs(st)` from a Bool fact `r < N` once the count N is known (alloc.spec's
  hr); the same symbolic register written, then read: the pick's condition by `nat.is_eq_refl` (before, that text
  failed the def check, so it was not shown).
- At a tie, the run that matches the start state is kept: its leaf names the missing fact.
- Early stop: a win counts as progress only at level 0, or when its proof is not a closer: exec.alloc 5.4 s -> 2.4 s at
  budget 4000.

### Re-measure on the 18 routine holes (round 3, `--budget 4000`, testbed with S1's spec patched as asked below)

Closed: release.spec (still; 0.54 s of stepping, 2-4 s per ask with the load of the larger files). The others:

| hole | before -> now | stops at | what unblocks it |
|---|---|---|---|
| input | 1 -> 3 statements | its loop (tot.while obligations printed) | the loop's invariant (the lane) |
| alloc | 3 -> 4 statements, 4 leaves | (1) `{St.outn(st) == 0}`: Fix has `U32.is_zero(St.outn(st))` only; (2) the budget `20 (next+1) <= Cells.bytes(..)` (Part's count: the lane's proof); (3) the post; (4) the free head's field read: its is_cell is inside `V.free`'s Maybe match | (1) S1: a kit law `u32.is_zero_t(x, h: {U32.is_zero(x) == True{}}) : {x == 0 : U32}` (or wp.alloc's premise as that Bool); (4) S2: is_cell of the free head written out in Fix/Room, as for Rts/Frs |
| swap | same step, new reason | the field read of register h's cell: h's value is only `I.Mb.is(Lg.Reg(st, h), St.reg(st, sp))` | S2: hh as `{Lg.Reg(st, Mc.R.h()) == Some{Lg.St.reg(st, Mc.R.sp())}}`, or a kit law `mb.is_t` to that equation |
| release_arg | same step, new reason | no is_cell for the chain's cell c: `Chs.go` matches `Con{A.Ag{q, k, t}, rest}`, so it does not unfold for an abstract ag | S2: `Chs.go` matching `Con{ag, rest}` (fields by accessors); then its conjuncts unfold |
| make, push | 1 statement | after alloc.spec: the rest from `Alloc.st(st, r)` | gen2 next: step on from the state of the law's post (`wq`'s first part), with alloc.reg/make.reg for the registers; then each store needs `is_cell(Alloc.cell(st))` in `Alloc.st(st, r)`: S2, a law alloc.cell |
| one, copy | 1 statement | make.spec not instantiable (its hv.. are fixed by Ev facts that the caller does not have) | the lane: Ev facts for the call's expressions |
| pop | 3 statements | release.spec's premises at a stepped state (ws2): gen2 matches premises only against the context's facts | gen2 next: offer the stepped states' register and cell facts to the matcher |
| inc, dec | 3 statements, 2 leaves | the post at the end of each branch | the lane (the post's invariant) |
| nth, release_all, walk, out | 1-4 statements | a loop | tot.while: the printed obligations |
| h.arg, h.node, alloc.reg, make.reg | | not Tot goals | |

### For the induction lane (w/gen2-ind, `--ind`)

S2 reports that gen2 stopped short on the inductions of `st0.nregs` and `st0.reg` (image/spec.bend; proven by hand in
4bf709a). Add them to the --ind test set: a count and a register of `St0(n, ..)`, whose regs are
`List.replicate(U32, n, 0)` (induction on n, the register q below n).

## Speed

- The main search stops when no subgoal closed for 0.6 of the budget (at least 300 ms; half the budget lost chain2 in 3
  of 8 bench runs), or when a whole cost level meets no
  new goal; then the partial pass and the decomposition are skipped. need_big at 1000 ms: 80/119 (unchanged), the bench's
  total 47.7 s -> 29.6 s (misses ~2.0 s -> ~0.7 s each), median hit 3 ms. (A window of a third of the budget lost chain2.)
- The miss hints read each def's source with one existsSync per def: now one per file (0.45 s of a 5.4 s miss).
- exec.alloc / wp.alloc / wp.emit used their whole budget (their search kept closing small rewrite subgoals); since
  round 3 only a level-0 win or a non-closer win is progress: exec.alloc stops at 2.4 s (was 5.4 s at 4000).

## Testbed

`bb-wt/scratch/gen2/wp/`: a copy of src with S1's logic/header/shared (w/s1 4f3ddcc; shared.bend plus the bool.case
lemma above, testbed only) and `Machine/wp_test.bend` (hand-written Tot/WP goals over Machine/impl's builders:
w.t3-w.t9, w.fo).

## Other gen2 fixes in this branch (from S1's tally)

- A partial whose hole asks `P -> P & (new facts)` (tot.wk's post left open) is not shown: "a dead end, not shown".
- The `why` lists: a lemma whose equation is over another type than the goal's, or with a type parameter nothing fixes
  (Equal.cong's A), is left out; the rest ranked by their number of open issues. Near misses only for a head that names a
  def or a constructor (not a function goal).
