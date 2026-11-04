# Statement review of the redesign skeleton, lanes S1, S2, S3

Reviewer: independent statement reviewer (Opus), 2026-11-04. Branch feature/redesign. I read the
files at 967db15 (the head I was asked to review). The branch has since moved to 05406a6. That
change only renames heap's `V.reg` to logic's `Lg.St.reg`, and it adds `reg.some` and `reg.lt`.
Both new laws are true. Every finding below holds at both heads. Line numbers are those of 05406a6.
Proof bodies are out of scope (AGENTS 2.3.2). I edited no file of the repo.

## Verdict

**Not ready for P3 as it is. There are three FALSE statements (F1, F2, F3) and three gaps of
strength (G1, G2, G3) that block the assembly.** Each fix is local: a premise, a post conjunct, a
clause of H, or a new heap lemma. No layer needs a redesign. All the other statements that I
checked are true. They are strong enough for their consumers and none is vacuous (list at the end).
The core is sound:

- `am.ok`, `am.walk_eval` and the canon family hold in every case. I checked them by hand, branch
  by branch, against `Eval.step`, `Eval.walk` and `Program.result`.
- The new computed runs confirm the machine against AM.move on every branch that the S2 notes
  listed as not run (section "Smoke").

The worst finding is F1. Once fv saturates, the heap invariant forbids a state that the machine
really reaches, on a book that is inside the promise.

## Findings, by severity

### F1 (critical, false): fv saturation breaks `fv <= d` at roots. copy.spec is false, and Inv cannot be kept

- Where: heap/spec.bend:692 `V.held.at` (used by `Rts` :697, `V.frame`, `Chs.go`). Also
  routines/spec.bend:582 `copy.spec` (its post), :414 `inc.spec` (premise `fv <= d`), :345 `Inv`.
- Statement: `V.held.at(x, st, c, d, t) := V.is(V.at(x, st, c, d), t) && Nat.is_le(U32.to_nat(Fv(cells, c)), d)`.
  copy.spec's post asks `Hp.H(x, st2, L2, Con{Hp.Rt{n, 0n, A.AM.copy(t, es)}, rs}, ..)`, so
  `fv(n) <= 0`.
- Problem: fv has 19 bits. A Var of index >= 524286 has fv = fv_max = 524287 (Img.go,
  impl.bend:1580; `V.fv.var`). fv_max then climbs through every ancestor: `Img.down` keeps it, and so
  do M.fv.part and M.finish (impl.bend:652). When a copy shares a bound Var of such an index, the
  new root has fv = fv_max. M.copy.part (impl.bend:694) takes its branch "Var with index < cj: inc,
  share", because index < cj. So `fv(n) <= 0` fails, even though the copy itself is correct.
- Counterexample, built from the statement. It is not computed: it needs about 524288 nested
  binders, too deep for bend2's evaluator.
  - The book: `main = λx. Ann{λ^524287. Var{524286}, Efq}`. Var{524286} is bound by the outermost of
    the 524287 λs.
  - It needs about 3 MiB of book bytes. That is below `Img.small`'s 2^26.
  - Its F (3.9.1.4) is about 2^27 bytes, so `enough_memory` promises a result (status 2: the value
    is no list of bytes).
  - The run: round 1 calls main. Its walk binds x, and its leaf (the Ann) is copied with
    es = [input].
  - The copy reaches the Var at cj = 524287 > 524286 and shares the STATIC image cell, whose fv is
    fv_max. Every new λ cell and the Ann root then get fv_max.
  - copy.spec's premises hold, and the copy runs to `next`. But its post H is false (`Rts`:
    fv(n) = 524287 > 0). From then on no state satisfies `Inv`, so S4's `round.sim` becomes false for
    this program.
- Fix: make "no real variable free at d" a heap predicate that does not depend on fv.
  - In heap/spec, add the recursive Bool predicate `V.rc(g, m, c, d)`: "the real variables of the
    read are bound at d". A Var cell gives `U32.is_zero(Fv(m,c)) || Nat.is_lt(U32.to_nat(Fd(2n,m,c)), d)`.
    Any other cell gives the conjunction, over the fields k of `Hs.Tbl.mask(Tg(m,c))`, of
    `V.rc(g-1, m, Fd(k,m,c), d + Hs.Tbl.bind(Tg(m,c), k))`. g = 0 gives False.
  - `V.held.at := V.is(V.at(..)) && V.rc(next, cells, c, d)`.
  - `inc.spec`'s `fv <= d` becomes `V.rc`.
  - Add `view.rc_fv`: fv < 524287, fv <= d and a read that succeeds give `V.rc` (this is the copy's
    sharing test).
  - Add `view.rc_frame`: Agree on `V.cells` keeps `V.rc`.
  - Add `view.rc_more` (more levels) and `view.rc_up` (d <= d2 gives rc at d2).
  - Re-state `view.deeper`, `view.canon` and `view.closed` with the premise `V.rc(g, m, c, d)` (resp.
    k) in place of the two fv premises.
  - The copy proof then gets locals by rc at 0 (no fv needed). The shared parts get rc from the fv
    test, and the result root gets rc at 0. Neither the machine nor the laws change.

### F2 (high, false): h.node and h.arg are false at the edge of memory, and make/alloc posts lack the bound

- Where: routines/spec.bend:663 `h.node`, :684 `h.arg`. Also :355 `alloc.spec` and :368
  `make.spec` (their posts).
- Statement: `h.node` concludes `Hp.H(x, Make.st(st, r, v), Con{Alloc.cell(st), L}, ..)` from
  `Hp.H(x, st, L, ps ++ rs, ..)`.
- Problem: H contains `Fix`, which asks `U32.is_le(St.next(st), 214748364)` (heap/spec.bend:622).
  With an empty free list, `Make.st` takes cell `next` and makes next `U32.inc(next)`. Take
  next = 214748364 (which H allows) and register free = 0. Then `next(Make.st(..))` = 214748365, so
  the conclusion's Fix is false, while every premise can hold.
- Counterexample, by argument (not computable: Part needs about 214M own cells). Make all the live
  cells STATIC own cells of a tag with mask 0. Cov, Cnt and Clo hold trivially.
- The machine never gets there: Cir refuses that alloc with out of memory. But h.node is a pure
  lemma, and make.spec's post (`st2 == Make.st(..)`) does not say that the alloc succeeded. So S4
  cannot even supply a premise.
- Fix:
  - Add to the posts of alloc.spec and make.spec the conjunct
    `{U32.is_le(Lg.St.next(st2), 214748364) == True{} : Bool}`.
  - Add the premise `{U32.is_le(Lg.St.next(Make.st(st, r, v)), 214748364) == True{} : Bool}` to
    h.node and to h.arg. Equivalently: `free != 0 || next < 214748364`.

### F3 (high, false): a count can wrap. inc.spec, copy.spec and walk.spec are false for a long root list

- Where: routines/spec.bend:414 `inc.spec`, :582 `copy.spec`, :610 `walk.spec`. Each runs `M.inc`
  on a cell that may already be a root of `rs`.
- Statement: `Cnt` (heap/spec.bend:659) asks `to_nat(Fd(1, c)) == V.refs(L, m, c) + Rt.count(rs, c)`.
  `rs` has no bound in H.
- Problem: let `rs` hold 2^32 - 1 - refs copies of `Rt{c, d, t}`. Then H holds with
  Fd(1, c) = 0xFFFFFFFF. `M.inc` stores `U32.add(0xFFFFFFFF, 1) = 0`, and Cnt then needs 0 = 2^32.
  So the post is false: the run reaches `next`, but Q fails.
- copy.spec (the shared parts and the locals' terms are inc'd) and walk.spec (the Tup's parts in
  walk.prj, and the locals in walk.app) fail the same way.
- refs alone cannot overflow: refs <= 3 |L| <= 3 × 214748364 < 2^30, by Part and Fix. Only `rs` is
  unbounded.
- Counterexample, by argument (a list of about 4·10^9 roots).
- Fix:
  - Add the premise `+hb: {Nat.is_le(List.length(&2, Hp.Rt, rs), 64n) == True{} : Bool}` to
    inc.spec, copy.spec and walk.spec. S4's root lists are short concrete lists, so `{==}` closes
    it.
  - Add the heap law `h.count`: from H, |rs| <= 64 and a live counted c, conclude
    `U32.to_nat(Fd(1n, m, c)) < 2^31`. Prove it once: V.refs <= 3 |L|, and |L| <= next - fi <= 214748364.

### G1 (medium-high, too weak): H does not bound the live STATIC own cells, so budget.need is blocked

- Where: heap/spec.bend:810 `Cov`, :814 `H`, and routines/spec.bend:345 `Inv`. The consumer is the
  plan §4.9 `budget.need` (`Need = Stat + 16 + 2·max(..) + ..`).
- Problem: Cov says that each live cell is STATIC or held. But nothing bounds how many live STATIC
  own cells there are (the input's byte cache). So `|V.Live(st)|`, which every routine budget
  counts, cannot be bounded by a term size from Inv. The old design carried `Stat` <= `Cache.max`
  in the invariant, and "Stat does not grow" in each routine post (4ebef88 definitions.bend:1193,
  :3283). The new routine posts carry neither.
- Fix: add to H (best in Fix or Cov) the clause `Nat.is_le(V.stat(L, m), 6144n)`, where V.stat
  counts the cells of L flagged STATIC.
  - Every routine post already states H, so the clause is kept for free.
  - No routine but M.input makes a STATIC cell: copy.push drops the flag, and h.node and h.arg ask
    for counted cells or arg headers.
  - input.spec gives at most 256 × 24.

### G2 (medium, too weak): the heap has no law that reorders roots or chains

- Where: heap/spec.bend, laws section. The consumers are the S4 moves.
- Problem: the routine laws take their root first (`dec.spec` `Con{Rt{c,d,t}, rs}`, `one.spec`,
  `swap.spec`), `push.spec` takes `Push.rts(fr, .., rs)`, and `h.node` takes `ps ++ rs`. The
  routines also put the new roots first (inc, copy, pop) and take their chain first (copy,
  release_arg, release_all, walk).
- The moves interleave these, and no law reorders. Examples:
  - In M.ev.frame, after `inc x; inc y; push`, the roots are `[x, c]`, and `dec(c)` needs c first.
  - M.ret.rwt pops to `[P-root, f-root, focus]`, then `dec(y)` and `dec(focus)`.
  - M.call needs the args chain (second) consumed before `release.all(wenv)`.
- H is invariant under a permutation of rs and of chs (Cnt counts, and Rts, Chs and Cov are
  conjunctions or membership), but that is unstated.
- Fix: add `h.rts_swap` (H with `a :: b :: rs` gives H with `b :: a :: rs`), and `h.chs_swap` (the
  same for chains). Alternatively one `h.perm` with a Bool `Perm`. Each is a short proof.

### G3 (medium, too weak): M.call's frame loop has no usable law

- Where: routines/spec.bend:453 `push.spec`, and the loop in M.call (impl.bend:885). The body is
  `push(header of wa, field 2 of wa, 0); release(wa)`.
- Problem: push.spec needs H with the frame's term as an owned root. In M.call the term is owned by
  the argument cell wa, and the frame takes that pointer only when `release(wa)` runs (no dec).
  Between the push and the release, two live cells point to the term while its count is 1. So no H
  holds there, and push.spec cannot be applied. S2 left the loop to S4 (s2-notes 15), but S4 then
  has to re-derive alloc, store and release heap reasoning outside H.
- Fix: state one Tot law for the body or for the two loops. Example (`frames.spec`):
  - From: `Hp.H(x, st, L, rs, fs, Con{Hp.Ch{c, ys}, chs})` with wargs = c.
  - The two while loops of M.call reach `Hp.H(x, st2, L2, rs, A.AM.frames(ys, fs), chs)`, with
    wargs = wh = 0, `Same` outside the loop's registers, and |L2| <= |L|.
  - Budget 20 (fi + |L| + 1).
  - The loop's Cir statement goes into routines/spec.bend as a def, built with the same M.* calls.

### G4 (low, too weak): no law adds a STATIC image cell as a root without a code step

- Where: heap/spec.bend. The consumer is M.ret.min (impl.bend:1151): `focus := I.lab(qmin)`, with
  no M.inc.
- Fix: add `h.static_root`. From H, `V.img(x, m, c)` and `V.held.at(x, st, c, d, t)`, conclude H
  with `Rt{c, d, t} :: rs`. Cnt skips STATIC cells, and Cov accepts them.

## Smoke: the uncovered cases, computed

The file is `review-scratch/rv_smoke.bend`. I ran it on a copy of feature/redesign@967db15 (WSL
`~/wt/rv`, heavy.sh, `bend2 --check-only`, 2 minutes). At every round it checks three things on
the real state and the abstract state, and it also compares the halts:

- `R.Inv(x, st, s)`;
- `A.AS.ok(ds, VALUE flag, s)`;
- am.ok's conclusion `A.AO.ok(ds, s, A.AM.move(..))`.

**All 9 runs pass.** The negative control (a wrong halt) fails, as it should:

| Run | Case | Halt |
|---|---|---|
| rwt | Rwt whose proof is a value, not Rfl | 2 |
| matmiss | λ-match of labels misses in a redex, under a fun frame | 0, the input |
| q2bad / q2ok | Q2 bind of a λ (no Data) / of the input (Data) | 2 / 0 |
| prjbad / prjwalk / prjdead | Prj on a label by redex / in a def's walk / at Q0 | 2 |
| matdead | Mat redex at Q0 | 2 |
| partial | partial call (waits, VALUE App), then the full call, in a Tup frame | 2 |

The alloc at the edge of memory, checked by hand against Cir.exec.alloc and Cir.room:

- `exec.alloc` and `alloc.spec` hold at the edge (Lim <= 20 next + 19 < 20 (next+1)).
- `input.spec` is tight but true: a book of 3275 image cells and an empty input with lim = 1 page
  needs Lim = 65536 < 65540 = 20 (first+1).
- The only edge failure is the pure lemma F2.

## Answers to the targeted questions

- **A Rwt not on Rfl, a Mat miss with frames, a Q2 non-Data bind, a Prj on no pair:** AM, the
  machine, Inv and AO.ok agree. I checked it by hand and by computation (table above).
- **canon.subst_below needs |es| <= n:** it is right and needed. copy.spec's premise
  `|es| <= Copy.depth(wt) || STATIC c` covers every copy that the machine makes:
  - λ/let bodies have one local at depth 1;
  - call leaves are STATIC image cells, where canon.subst_closed applies through view.closed;
  - wt with es = [] is fine with n = 0.
- **Rt{c, d, t}:** the depth is right and needed (Let 1, Rwt motive 2, a popped Let body read at
  depth 1). Only its `fv <= d` side is wrong (F1).
- **Saturated fv 524287:** view.deeper, view.canon and view.closed rightly ask fv < max. But Rts,
  Frs, Chs and inc.spec use `fv <= d` with no escape for fv_max: F1.
- **Poison, STATIC, BUILD and FREE cells:**
  - A poison cell reads Var{d}, and V.st.ok bars poison from STATIC cells.
  - H bars BUILD from live cells (Cov), so BUILD matters only inside copy.spec.
  - FREE cells never read, and Part pins them to the free list.
  - Cache and table cells (header 0) read as poison, but Clo, Rts and V.Held keep every pointer off
    them.
- **U32 wrap:** next cannot wrap, because Cir refuses an alloc at 214748364. outn cannot wrap, and
  `exec.emit`'s budget covers its wrap test. clen and wn are bounded by distinct chain cells. Only
  counts can wrap: F3.
- **Empty lists:** nth needs j < |as|. release_all with as = [] means c = 0 and the loop does not
  run. A waiting walk means wargs = 0 and ys2 = []. Frs/Chs on [] ask 0. All fine.
- **Fuel:** Tot carries some fuel, `tot.any` gives the form at any fuel, and every routine's loop
  ends (dec's cascade frees one cell per round, copy pops one, walk descends). Fine.
- **Shape for weak provers:** fine overall. The premises are Bool, every equation premise is
  reusable, and the laws have few parameters. The only splits are the 19-way former splits of the
  canon family, which cannot be avoided. H is a 7-clause conjunction: provers need its projections
  (S2 note 15), so state `h.room`, `h.cnt` and the others once, as `and_l`/`and_r` lemmas, to save
  every lane the same 3-step chain.

## Statements checked and found fine (true, strong enough, not vacuous)

- **shared.bend:** everything (proven).
- **logic/spec:**
  - the judgment and the WP laws: exec.more, tot.any, tot.seq, tot.if, tot.while, tot.wk, tot.of_wp,
    wp.of_tot, wp.wk;
  - the primitive laws: exec.set, exec.store, exec.alloc, wp.set, wp.store, wp.alloc, wp.emit. I
    checked the out-of-memory bounds against Cir.room and the 214748364/214748365 tests;
  - the updater laws: all reg.*, nregs.*, cells.*, next.*, outn.*, fixed.*, lim.*, plus reg.some and
    reg.lt (new). cells.get_set also holds on malformed tries (get gives zero there);
  - the frame laws: frame.regs, frame.fixed, tot.frame (next cannot wrap), tot.frame_out.
- **header/spec:**
  - hd.tag_of, hd.q_of, hd.fv_of, hd.has_of, hd.todo_of (Hd.fits gives exactly the needed ranges);
  - all mask.* laws, which hold for every n, since a shift by 32 or more gives 0 on both sides;
  - Tbl.* agree with Img.table.
- **heap/spec:**
  - view.frame, view.more, view.static, view.chk, view.tag, view.kid;
  - view.deeper, view.canon, view.closed: true as stated, but see F1 for their premise;
  - agree.store, agree.store1, agree.put, agree.refl, agree.trans;
  - h.set and h.live.
- **image/spec:** img.start, img.frame, img.store, img.put, img.table, img.ref, and Cx.terms's layout
  (Ref of main at cell 15, the bodies from 291).
- **routines/spec:**
  - true as stated: release.spec (also when r = free), nth.spec (chain cells are distinct, so
    from_nat is injective), dec.spec (an exact cascade; no cell is freed twice, since counts are
    exact), push.spec, pop.spec, swap.spec, one.spec, release_arg.spec, release_all.spec, out.spec,
    input.spec;
  - alloc.spec and make.spec are true as stated, but see F2 for their posts;
  - Walk.post / walk.spec: checked branch by branch against M.walk.lam/prj/mat/app and Efq. The
    KNOWN, quantity and chain order match AM.walk, and the budget is 2 cells a node. True but for
    F3;
  - copy.spec: the semantics are right (locals via canon.lift, sharing via subst_below or
    subst_closed, poison past the locals). It is false only by F1 and F3;
  - Inv: right in content, but it inherits F1.
- **canon/spec:** term.is_eq_ok, term.is_eq_refl, canon.step, canon.steps, canon.result,
  canon.size, canon.vals, canon.data, canon.idem, canon.start, canon.subst, canon.subst_below,
  canon.subst_closed, canon.lift. All true (Eval never reads a free index; walk tests arguments by
  shape only). canon.lift holds also for k = 0 and j >= |es|.
- **am/spec:**
  - am.ok, checked over all the branches of AM.move:
    - every admin move strictly lowers AS.w;
    - every step equals CStep, including through all 9 frame kinds, since every hole is at depth 0;
    - every halt has no CStep and the right result (a halt 2 term holds a non-Tup/Lab node, or is
      not a value);
    - the KNOWN ⟹ value invariant carries through AM.args, Prj, Mat-miss and AM.local.
  - am.walk_eval holds for every e and xs: poison Var{0} and Eval's Var{v - |e|} have the same
    canonical form.
