# gen2 --ind: notes (agent gen2-ind, branch w/gen2-ind from feature/redesign)

## What it is

`gen2 prove|ask <file> <def> --ind` (off by default). Module `src/Shared/scripts/gen2_ind.ts`; hooks in gen2.ts,
all behind `IND`: an API object (`indApi`), temp defs (`addTemp`/`dropTemps`: helper lemmas while gen2 proves
them; a temp enters the lemma index only with its proof; an unproven temp is open), `indWhole` in `proveOne`
(after the normal search misses a whole body), one line in `leafGo`, one line in `splitCands`, the misses of
`bench` (time added), IND in serve's answer-cache key, and the option line in the header.

* Schemes (a skeleton TEXT with ?TODO arms, checked by bend2's def check; each arm's goal read from bend2's
  error at a marked hole; arms closed by gen2's leaf tactics with the induction hypothesis, else helpers):
  - enum: a Nat bounded by a hypothesis `{Nat.is_le(x, c) == True{}}` (or is_lt), c <= 8: every value and
    `(c+1)n+p` (not `_`: bend2 types `_`'s binder as `Nat - Zero`, which no tactic reads), jointly with the
    other parameters that the goal's calls read (a record such as Cir.Cell: its constructor);
  - u32+width: the U32 parameters that U32 ops take are destructured (`U32{w}`); a goal over words of width
    32n is the instance at 32n of a helper over any width n (the classic generalization before induction;
    the literal 0 becomes `Word.zero(n)`); a U32 equation closes by `Equal.cong(Word(32n), U32, w => U32{w}, ..)`;
  - word: n, then the words with their head bits as nested patterns `WCon{False{}, t}` (a pattern binder
    cannot be matched after a later parameter), `WNil{}` at width 0; a second skeleton also splits the
    other parameters the calls read;
  - fun: functional induction: the parameters a recursive call reads, also through a recursive call in a
    read position (`List.get(List.replicate(U32, n, 0), q)` gives `match n q`);
  - nat: a Nat that blocks the goal.
  Multi-scrutinee matches list the parameters in parameter order (bend2 rejects another order).
* Helpers for an arm the leaf tactics leave (only on a skeleton that closed some arm; at most 16 per def,
  nested 3 deep; deduplicated by statement; helpers before the arms of the best two skeletons, ranked
  enum > u32+width > word+split > fun > word > nat > u32):
  1. the arm rewritten by an instance of the induction hypothesis (found in the arm's normal form, also
     against the conclusion's normal form: St.nregs(St0(n, ..)) is List.length(List.replicate(..)));
     the instance must descend as bend2 checks (live parameters equal left to right until one is a
     strict constructor subterm); parameters the side does not name stay the arm's own; premises are
     context facts of the same normal form. A rewritten arm that computes closes as
     `(%e : P; {==})`; else the stuck calls common to both sides become variables (U32.shrn(a, p) -> g);
  2. a stuck call of an enumeration type (Cmp, Bool) becomes a variable WITH its equation
     (`+g: Cmp, +hg: {g == Word.cmp(p, x, y) : Cmp}`, call with `{==}`): the helper holds iff the arm does;
  3. the arm's own goal over its context (its normal form when shorter), when no instance of the
     hypothesis occurs in it (shr.pad needs its own induction).
  Each helper keeps the context's facts over its parameters as premises, is proven by gen2's search, then
  by the schemes; a failed helper is dropped and never printed.
* leaf: a constructor clash in a hypothesis whose type has type parameters (`{None == Some{c}}` at
  `Maybe<&2, A>`) closes any goal: `Empty.absurd(GOAL, (%e : maybe.T(A, _); Unit{}))` (predicates
  found by their telescope; gen2's own absurd needs a one-parameter predicate and an Empty goal).
* splits: a pending parameter of an enumeration type (Bool) is a split candidate even when no call
  blocks on it (bool.case: only its hypotheses name b).
* Checks: each arm fill is checked in the whole body by bend2's def check (a hole goal does not check the
  descent of the induction hypothesis, so a leaf proof may call it with equal arguments); each helper by
  the def check; the final body again. What prints is what checked.
* Output: `# HELPERS (new, from gen2 --ind; each proven, and checked with the body below): paste them above
  def X(`, the helpers in dependency order, then `# the body of X:` and the body; `--write` writes both.
  A partial (with --partial) only when it closes more than the normal partial: the checked skeleton, its
  proven helpers, and each open arm's goal.
* Time: the schemes get max(budget, 2.5 s) after the normal search misses; a skeleton that closes no arm
  gets no helpers (no progress: frame.regs, exec.alloc answer in 0.3-0.4 s more).

## Results (testbed bb-wt/scratch/gen2/ind: copies of feature/redesign 9aaf458+; blanked = its body
## (and, for st0, its hand helper) removed)

Times: total of the ask (normal search + --ind) / the --ind part. Budget 1000 (serve's default) and 4000.

| case | without --ind | with --ind | --ind time | gate (bend2 + kernel) |
|---|---|---|---|---|
| shared bool.case (blanked) | miss | proven (split on b) | 6 ms | pass |
| shared list.lt_get (blanked) | Nil case open | proven (clash through maybe.T) | 28 ms | pass |
| shared list.get_lt (blanked) | proven | proven | - | pass |
| logic cell.get_set | miss (time) | proven (enum, 36 arms) | 0.1-0.15 s | pass |
| logic cells.get_set | miss | proven (u32+width, word+split, 9 helpers) | 1.3 s (1000) / 1.9 s (4000) | pass |
| image st0.nregs (blanked, img.rep_len deleted) | miss | proven (nat + IH rewrite) | 57 ms | pass |
| image st0.reg (blanked, img.rep_get deleted) | miss | proven (fun:List.get) | 0.1 s | pass |
| header mask.and_or, and_and | miss | proven (u32+width, word) | 0.3-0.5 s | pass |
| header mask.shr_or, shr_and | miss | proven (nat; IH rewrite; U32 helper; width; shr.pad helper) | 0.35-0.7 s | pass |
| header mask.or_zero, zero_or, and_zero, zero_and | miss | proven (Word.zero) | 6-31 ms | pass |
| header mask.and_shl, shr_shl | miss | miss | - | - |
| header mask.and_low, shr_low, sub_bit | miss | miss | - | - |
| header hd.tag_of, q_of, fv_of, has_of, todo_of | miss | miss | - | - |
| logic frame.regs, frame.fixed, tot.frame, tot.frame_out, tot.any, exec.alloc | miss | miss | +0.3-0.6 s | - |

Not closed, and why:
* mask.and_shl, mask.shr_shl: the shift count n is an induction where the hypothesis needs another
  argument (and(shln(a, p), m') with m' = shr(m)) and a commutation lemma (shrn(shr(m), p) =
  shr(shrn(m, p))): two lemmas gen2 does not conjecture.
* mask.and_low, mask.shr_low, mask.sub_bit: arithmetic (subtraction with borrow, comparison against
  2^k): a carry-generalized Word.adc lemma; the hypotheses mention U32 values, so the width lift cannot
  generalize them.
* hd.*_of: no induction: a rewrite chain through the mask laws (and_or, and_shl, and_low) and Hd.fits'
  facts; possible once those laws are proven (then they are lemmas gen2 rewrites with).
* frame.regs, frame.fixed: an induction on the statement with the run's equation e: exec(f, s, st) ==
  next{st2} as a hypothesis: the arms need the inversion of Cir.exec.then and of next{..} (injectivity),
  which gen2's leaf tactics lack. tot.frame, tot.frame_out: Tot is an existential over fuel (the frame
  laws inside). tot.any: fuel monotonicity with a Nat comparison, not an induction. exec.alloc: a case
  analysis of Cir.exec.alloc's ifs (the early stop of round 2 answers in about 1.7 s).

Gate (bb-wt/scratch/gen2/ind/gateall.sh: every --ind output spliced into copies, ~/lead/gate.sh): shared.bend
ALL PROOFS CHECK, kernel 29/29; logic, image, header: bend2 and the kernel fail only on the holes still open
(logic 9, image 6 of its 60, header 10); every --ind proof and helper passes both.

Testbed scripts (bb-wt/scratch/gen2/ind): t.sh (prove on a copy), all.sh (every case, with/without --ind),
gateall.sh (splice + gate), regress.sh (need_big bench + the 51 crash states), srv.sh (a shared server).

## Regression (need_big bench, budget 1000; 51 replayed crash states)

| version | flag off | flag on | crash states (off) |
|---|---|---|---|
| base (feature/redesign 9aaf458 = gen2-wp wp13) | 79/119, hit median 4 ms | - | 0 crashes |
| 4a6c5c8 | 79/119, median 4 ms, same hits | - | 0 crashes, 51 verdicts |
| 5e0153c | 79/119 | 80/119 (+Word.rel by the Bool split), no loss, hit median 4 ms, miss median 576 vs 569 ms; total 39 s vs 30 s (misses try the schemes) | - |
| 002693d (merged feature/redesign 9dd2ced: stall window 0.6) | 80/119, hit median 3 ms, total 26.4 s | 81/119 (+Word.rel), hit median 4 ms, total 30.7 s | 0 crashes, 51 verdicts |

The crash states run `--check` (no search), so the flag does not reach them.

## Notes for others

* gen2.ts's answer cache key has no WP (an ask with --wp may get a cached answer of an ask without it,
  and back): the same fix as IND here (add WP to optsKey) — left to the gen2-wp owner.
* A --ind answer is not served from the answer cache (its body calls helpers that are not in the book
  when the cache rechecks it); it is computed again (1-2 s).

## Round 2 (coordinator's decision: --ind is the DEFAULT)

* `--ind` is on by default; `--no-ind` turns it off (`--ind` is still accepted).
* serve's answer-cache key holds IND and WP, so asks with different flags never share a cached answer.
* `--ind` answers are cacheable: the cache keeps the helpers' head and body; a repeat ask adds them to the
  book as temps, def-checks each helper and then the body, and drops them (cells.get_set: 1.7 s first
  ask, 10 ms served on the repeat).
* Shared server (one ask at a time): when other asks are already queued as this one starts, the schemes
  get the budget only (no 2.5 s floor). An ask runs synchronously, so asks that arrive during it are seen
  only by the next one. Measured (budget 1000): a miss (exec.alloc) served in 1.2 s with two quick asks
  behind it; they waited at most 0.95 s and were served in 6-12 ms.

## Round 3: constructor injectivity and inversion (default on, bounded)

In the arms of a skeleton (before the helpers), each step leaves the arm's continuation as a new ?TODO:
* chain: an equation goal closed by at most two equations (context facts; instances of the induction
  hypothesis whose premises context facts give, never k's own parameters), joined by Equal.trans;
* clash C1{..} == C2{..}: `Empty.absurd(G, (%sym : is_C1(_); Unit{}))` (a predicate helper);
* injectivity C{as} == C{bs}: the goal's variable rewritten by the other part (a projection helper with a
  default, `Equal.cong`); a goal variable equal to a constructor value is substituted;
* inversion of F(.., r, ..) == C{y} (C with fields; r stuck; F any def that matches r: Cir.exec.then,
  Cir.exec.if, Cir.exec.set, Cir.exec.set.of, ..): a helper in continuation style
  `inv(.., r, h, G, x.. => h1 => h2 => ..)` (bend2 destructures only a variable, never a computed value)
  for the one constructor of r that can give C; else a case split, one continuation per constructor
  (exec.if.of on a Bool), the impossible ones closed by the clash step; a record variable (st) inverts to
  its fields. Each hypothesis is inverted once per arm.
* funScheme also reads the hypotheses' types (frame.fixed: e : exec(f, s, st) == next{st2} gives
  `match f s`, with the fuel f as a read Nat).
* Arms are checked at their goals (fast); a fill that calls the def itself, and the whole body at the end,
  by the def check.
* Found by the gate, fixed: gen2's def check sees every body, so a helper printed below a def that uses it
  passed gen2 but failed bend2's file check (a def calls only defs above it). Helpers now print in
  dependency order (gate pass after the fix).

Hit counts (before = 089e691, after = 40570cd):

| target | before | after |
|---|---|---|
| frame.fixed | 1/18 arms closed (no proof) | proven at budget 4000 (3.0 s for --ind, 27 helpers; gate pass); budget 1000: 6 arms open |
| frame.regs | 1/18 arms closed | 12 open at budget 20000 (nop, halt, store, emit, while closed in both fuels), 15 at 4000; left: set/alloc (List.get after List.set with the written register apart: list.get_set and the Bool fact), seq/if (Has over List.append for the hypothesis' premises) |
| need_big bench (default) | 81/119 | 81/119, no loss, hit median 5 ms (4 before; noise level) |
| test set (budget 1000) | as before | same: every earlier proof still found |
| crash states | 0 | 0 |
