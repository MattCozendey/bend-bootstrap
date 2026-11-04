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

## Measurements

| version | regression (flag off) | --wp on the test goals (bb-wt/scratch/gen2/wp, S1 4f3ddcc) |
|---|---|---|
| fa30ae4 | need_big 80/119 @1000 ms, median 4 ms; 51 crash states: 0 crashes | sets, decided ifs, Bool-split arms: proven (14-70 ms) |
| 50d4396 | same | + M.release, M.pop (stores, a field read) step to the post (170-530 ms) |
| next | (running) | + undecided if split by bool.case: both branches stepped |

Baseline before the hook: need_big 80/119, median 3 ms (gen2-up 7727b7d).

## Testbed

`bb-wt/scratch/gen2/wp/`: a copy of src with S1's logic/header/shared (w/s1 4f3ddcc; shared.bend plus the bool.case
lemma above, testbed only) and `Machine/wp_test.bend` (hand-written Tot/WP goals over Machine/impl's builders:
w.t3-w.t9, w.fo).

## Other gen2 fixes in this branch (from S1's tally)

- A partial whose hole asks `P -> P & (new facts)` (tot.wk's post left open) is not shown: "a dead end, not shown".
- The `why` lists: a lemma whose equation is over another type than the goal's, or with a type parameter nothing fixes
  (Equal.cong's A), is left out; the rest ranked by their number of open issues. Near misses only for a head that names a
  def or a constructor (not a function goal).
