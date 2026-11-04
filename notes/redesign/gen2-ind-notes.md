# gen2 --ind: notes (agent gen2-ind, branch w/gen2-ind from feature/redesign)

## What it is

`gen2 prove|ask <file> <def> --ind` (off by default). Module `src/Shared/scripts/gen2_ind.ts`; hooks in gen2.ts
(all behind `IND`): an API object (`indApi`), temp defs (`addTemp`/`dropTemps`: helper lemmas while gen2 proves
them; a temp enters the lemma index only with its proof), `indWhole` in `proveOne` (after the normal search
misses), one line in `leafGo` (clash through a predicate with type parameters), one line in `splitCands`
(Bool parameters that only hypotheses name), and the misses of `bench` (time added).

* Schemes: a skeleton TEXT with ?TODO arms, checked by bend2's def check; each arm's goal is read from bend2's
  error at a marked hole; each arm is closed by gen2's leaf tactics, else by a helper. Kinds:
  enum (a Nat bounded by a hypothesis `Nat.is_le(x, c)`: every value and `(c+1)n+p`, jointly with the
  other parameters the goal's calls read), u32+width (U32 parameters destructured; a goal over words of
  width 32n is the instance of a helper over width n: the generalization before induction; the literal 0
  is `Word.zero(n)`), word (n, the words with their head bits as nested patterns `WCon{False{}, t}`,
  WNil at width 0; also with the other read parameters), fun (functional induction: the parameters a
  recursive call reads, also through nested recursive calls: `List.get(List.replicate(U32, n, 0), q)`
  gives `match n q`), nat.
* Helpers for an arm the leaf tactics leave (only on a skeleton that closed some arm; at most 16 per
  def, nested 3 deep; deduplicated by statement): (1) the arm rewritten by the induction hypothesis
  (an instance found in the arm's normal form, also against the conclusion's normal form; it must
  descend as bend2 checks: live parameters equal left to right until one is a strict subterm; its
  premises are context facts of the same normal form), then the stuck calls common to both sides
  generalized (U32.shrn(a, p) -> g); (2) a stuck call of an enumeration type (Cmp, Bool) generalized
  WITH its equation `+g: Cmp, +hg: {g == Word.cmp(p, x, y)}` (equivalent: never false); (3) the arm's
  own goal over its context (true iff the arm), when no IH instance occurs in it. Each helper is
  proven by gen2's search, then by the schemes; a failed one is dropped (never printed).
* Every printed text passed bend2's def check in gen2's book (each arm fill is checked in the whole
  body: the leaf tactics in a hole goal do not check the descent of the induction hypothesis).
* Output: `# HELPERS (new, from gen2 --ind; each proven ...): paste them above def X(` then the
  helpers (in dependency order), then the body. `--write` writes both.

## Results (testbed bb-wt/scratch/gen2/ind; copies; budget 4000 ms unless said)

| case | before | --ind | time (--ind part) | gate (bend2 + kernel) |
|---|---|---|---|---|
| shared list.lt_get (blanked) | Nil case open | proven | 28 ms | - |
| shared bool.case (blanked) | nothing | proven | 7 ms | - |
| shared list.get_lt (blanked) | proven | proven | 46 ms | - |
| logic cell.get_set | miss | proven (enum, 36 arms) | 148 ms | pass |
| logic cells.get_set | miss | proven (u32+width, 9 helpers) | 1.9 s | pass |
| image st0.nregs (blanked, its helper deleted) | miss | proven (nat + IH rewrite) | 61 ms | - |
| image st0.reg (blanked, its helper deleted) | miss | proven (fun:List.get) | 148 ms | - |
| header mask.and_or, and_and | miss | proven (u32+width, word) | 0.5 s | pass |
| header mask.shr_or, shr_and | miss | proven (nat, IH rewrite, U32 helper, width, shr.pad helper) | 0.7 s | pass |
| header mask.or_zero, zero_or, and_zero, zero_and | miss | proven (Word.zero) | 10-24 ms | pass |
| header mask.and_shl, shr_shl, and_low, shr_low, sub_bit | miss | miss | - | - |
| header hd.*_of (5) | miss (4 s) | miss | - | - |
| logic frame.regs, frame.fixed, tot.frame, tot.frame_out, tot.any, exec.alloc | miss | miss | - | - |

(table filled as measured; see the sections below)
