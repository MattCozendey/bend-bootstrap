# Design assessment: the Bend-to-WASM machine and its proofs

Read-only sweep (thermo-nuclear + erasure + cyclomatic complexity), with a system-design focus. Base: `main` @ 4ebef88. No file in the repo was changed.

Grades: **(a)** an obvious win that I am confident about. **(b)** plausible, but it needs a spike first. **(c)** it looks bad, but it is essential.

---

## 1. Verdict

1. **The machine model is not "stupid from the start".** Its core is close to forced by the laws and by 3.9.1.4. A substitution machine is needed because F counts term size. Immutable acyclic cells with refcounts are needed because every unreachable cell must be freed, and sharing is needed in practice for time. Frames are cells, so the stack is in WASM memory. A fixed interpreter plus a data image is a fine way to make "the compiler". I would keep all of this. (c)
2. **Most of the difficulty is accidental.** It comes from two sources:
   - **Design.** About six micro-optimizations each add a whole invariant dimension: the DATA memo flag set ahead of the check, borrowed pointers with the OWNED flag, lazy decrement with zombies, list-dependent pointer meaning, the copy's todo bits aliased onto the flag bits, and shift for open terms. Each one saves a few instructions and costs thousands of proof lines.
   - **Proof architecture. This is the larger source.** No layer sits between "bits in cells and 63 registers" and "Eval terms". There are three views of "a cell stands for a term" and two heap invariants, and a 10k-line bridge connects them. About eight separate program-logic kits do the same job. About 415 lemma names are defined more than once (≈8k lines of extra copies). 189 lemmas split on all 19 formers (≈17.6k lines).
3. **The status is worse than "36 holes" suggests.** The open holes are the *core* simulation lemmas, not leaves: `copy.post`, `walk.post`/`walk.done`, `data.post`/`data.done`, all 3 call moves, all 4 copy-using moves (`unlet`, `ret.app.lam`, `ret.fun.lam`, `ret.let`), `al.reuse.term` (on the path of every `M.alloc`), 13 holes in shift, `input.post` and `mach.memory`. What is proven is mainly the easy moves, which already cost ≈700 proof lines per trivial move (`swap_moves.bend`: 5,382 lines for 7 moves of about 60 Cir lines).
4. **Recommendation.** Do not throw the machine away. Do four cheap design deletions first (§3, D1–D4); they *remove* open holes. Then fix the proof architecture before the remaining core proofs: one term view, one heap invariant, one WP logic, generic frame theorems, and a shared kit (§4, §5). Otherwise the copy and walk will each cost another 10–30k lines with the current technique (this is an extrapolation, not a measurement).

---

## 2. Measurements

| Item | Number |
|---|---|
| Machine implementation (`Machine/impl.bend`) | 1,824 lines; the Cir machine itself ≈1,330 lines, 17 `while` loops, 63 registers |
| Machine proofs (`src/Compiler/Machine/*.bend` less impl) | ≈115k lines, 6,814 `def`s |
| Proof : code ratio | ≈90 : 1 |
| Copy-related proof files | ≈29k lines (copy_bridge 10,305; copy_walk 4,185; copy_header_bits 3,702; copy_kit 2,687; copy_end 1,611; …), and `copy.post` is still open |
| M.data proofs (`data_check` + `data_walk`) | 7,127 lines; `data.post`/`data.done` open |
| M.out proof (`out_bytes.bend`) | 6,182 lines for ≈45 lines of Cir |
| Lemmas that re-prove a heap clause (Cnt/Pc/Ptr/Pts/PendOK/Heap/Clo/Cov/Stat/Frs/Kept/Held/Rts) | 503 defs, ≈8.6k lines |
| Defs with a full 19-former case split | 189 defs, ≈17.6k lines |
| Names defined in 2+ files | 415 names, ≈8.2k lines in the extra copies |
| `Equal.sym/trans/cong/subst` uses | ≈7.4k (accounting 836, copy_bridge 558, heap_ops 514, swap_moves 425) |
| 32-bit bit-blasting lemmas (`WCon` × 32) | ≈125 in Machine (copy_header_bits 32, swap_moves 43, moves_push 35) |
| `dk` mentions (the DATA-flag duality) | 3,472 in 12 files |
| zombie / `zs` / `Pend.terms` / `PendOK` mentions | ≈3,300 |

---

## 3. Design findings, ranked by impact

### D1 (a). Compute DATA when the cell is made; delete `M.data`

- **Now.** `M.data` (impl.bend:583–620) is a loop with a stack of `K.check` cells. It sets the DATA flag on shared cells *before* the check is known to pass. Because of this, every term-view predicate exists twice: `IsCK/NdK/FrsK/RtsK/DefsK/ImgOKK/HSK/DataK` with a `dk: Bool` (definitions.bend:80–250, 599–612). Proofs: data_check (4,285) and data_walk (2,842). Holes: `K.data.post`, `K.data.done`.
- **Why it can go.** `El.Term.is_data` (Eval/impl.bend:48) is structural and compositional: Lab, Rfl, or `Tup q a b` with `(dead q || data a) && data b`. Just like `fv`, it can be a header bit that is computed when the cell is made. `Img.go` already computes it (`Img.Out.data`).
- **Change.** Compute the bit in `M.finish` (Tup rule from the parts' bits), in `M.ret.tup`, and in the input headers (already DATA). `M.data(r)` becomes "read the bit". NdK's DATA clause becomes an equality, kept at creation exactly as the fv clause is kept.
- **Removes.** The `M.data` loop, `K.check`, registers ds/dok/dc, `Data.need`, the `dk` duality everywhere, 7.1k lines, and 2 open holes.
- **Cost.** About 10–15 Cir lines, plus the creation-time lemma for the bit. Note that the copy's todo bits sit on bit 9 (DATA), so `M.finish` must set the bit after it clears the todo bits.

### D2 (a). Each argument cell owns its term; borrow only STATIC cells

- **Now.** A `K.arg` cell owns its term only when OWNED (4096) is set. `Ag` (definitions.bend:1398–1418) has 12 clauses and a 5-way disjunction: "STATIC, a node of an owned root, one of `vs`, or the Var of an OWNED arg later in the chain". It also needs `Ag.vars`, the `vs` threading, and `Held(os, bs)` in HS. That makes 375 mentions of Held / Ag.vars / 4096.
- **Change.** `M.inc` the term when you make an arg cell, and `M.dec` it in `M.release.arg`. Inc the copy source too. Borrowed pointers then exist only for STATIC cells (the image), which need no count.
- **Removes.** OWNED, `vs`, `Ag.vars`, the disjunction, most of `Held`/`bs`, and the "released after the borrower" ordering facts.
- **Cost.** About 6 `M.inc`/`M.dec` calls. Time cost: one store per argument.

### D3 (a). Re-tag released machine cells, so the pointers of a cell depend on that cell only

- **Now.** `Fs(m, ps, o)` (definitions.bend:833–841) counts the pointers of a frame or arg only when `not Mem(ps, o)`. So every change to the pend list changes `Fs` of other cells, and through `Pc` and `Ptr` it changes the global `Cnt`. This is a main source of the `*.pop`, `*.sw`, `*.st` lemma families (§4 P1).
- **Change.** `M.release` also stores a "free" tag (one store). Then `Fs(m, o)` reads only o's own fields, and pend membership leaves the counts of `Cnt`.
- **Cost.** 1 Cir store. Proof: `Fs`/`Cnt`/`PendOK` change their statements (frozen file: ask the lead).

### D4 (a). Remove the KNOWN store in the walk's label miss (impl.bend:877)

- On a miss, `M.walk.mat` sets KNOWN on the arg cell. The arg is a live Lab, and a Lab is a value by its form (table entry 4). KNOWN only saves the two admin moves of a later swap. It is also the heap write that makes `mat.miss.ws` need a chain fact that `WS` does not have (walk.bend:1995).
- Without the store, the miss changes only registers, and `mat.miss.ws` should follow from `WS` with no heap reasoning. KNOWN only implies a value, so leaving it unset is always sound.

### D5 (b). Free cells eagerly, with no zombies between moves

- **Now.** `M.dec` at 0 pushes the cell on the pend list. Its parts lose their pointer only when `M.alloc` reuses it (impl.bend:504–540). So between rounds, `AccK` carries zombies `zs` that still stand for terms (`Pend.terms`, `Rt.cells(zs) == Pend.terms(ps, m)`, `PendOK`). `copy_substitution` has its own "garbage P / pend Q / zombie size" model. `al.reuse.term` (heap_ops.bend ≈6375) is open because of this: the reuse cascades into other cells' counts.
- **Alternative.** When a count reaches 0, run a worklist loop in `M.dec`: pop a cell, dec its parts, push the parts that reach 0, then put the cell on a free list that holds no counted pointers. The memory bound stays the same.
- **Effect.** The zombie concept moves into one loop inside `dec` (one proof), and Inv/HS/AccK lose `zs`. `M.alloc` becomes "pop the free list", with no effect on other cells.
- **Spike.** Write the dec-loop invariant and confirm that the amortized time is acceptable for the self-compile.

### D6 (b). Make free variables "poison"; delete `M.shift`

- **Now.** `M.shift` is a second instance of `M.copy.walk` with its own 7 registers (impl.bend:749–766). It is used only when a local's term has `fv > 0` under binders. Proofs: shift_gives_shift (922 lines, 13 holes, the Sh.start measure issue) and the local branch of `copy.part`.
- **Why.** The machine runs closed terms. Free variables come only from malformed books (an open def body, or the "no local v" case of `walk.app`). In Eval, a free variable can never become bound (subst shifts it past binders) and can never be inspected (mat, prj and data on a Var get stuck or say no). A result is a byte list, which holds no Var. So a free variable's *index* never affects whether there is a result, or what it is.
- **Change.** Treat every free variable as one closed "poison" atom (fv 0). Then all locals are closed, the copy never shifts, and `M.shift` goes away.
- **Spike.** Write and prove a Bend lemma that Eval respects "equal up to free-variable indices", as a relation kept by subst and by steps. It must be stated over the 19 formers (≈1–2k lines, by my estimate). The relation must also hold between the machine's term and Eval's term in `Inv` (A.plugs equality becomes `≈`). This changes the frozen `Inv`: ask the lead.

### D7 (b). Do not alias the copy's todo bits onto the flag bits

- During a copy, bits 8–10 of a new cell mean "fields still to copy". After `M.finish` they mean VALUE/DATA/STATIC (impl.bend:643–696), and field 1 means a stack link. So `Fl(m, c, 1024)` (STATIC) is ambiguous for cells under construction, which matters because `Cnt` skips STATIC cells. Result: copy_header_bits (3,702 lines, ≈32 bit-blast lemmas) and copy_frame_tags (1,203).
- **Option 1, cheap.** Put the todo bits in the fv bits (13–15). fv is computed at finish anyway, so the flag bits are never ambiguous.
- **Option 2.** Use an explicit copy work stack of frame cells. Memory: `Need` is ≈2 cells (40 bytes) per term node out of the 64 that F gives (definitions.bend:3361), so about 1 extra cell per node fits, but measure it first.

### D8 (b). Give Cir a cheap register frame (syntax first, procedures only if needed)

- 63 global registers, and every routine is an inlined macro. So each phase post states `Kept(regs, regs2, keep)` with `Disj(keep, scr)`, and proofs build `R59` and the 63-deep `rg.of` match (3 copies, ≈260 lines each). The register/kept/disj family is about 176 defs, ≈3.2k lines.
- **Cheap fix (proof only, (a)).** Add a syntactic `Cir.writes(s): List<Nat>` and prove once: "`exec(f, s, st) = next(st2)` keeps every register not in `writes(s)`". `Disj` then *computes* on the concrete `Mach.code` subterms. Prove a similar `Cir.stores_to` frame for cells.
- **Procedures with locals in Cir, (b).** This means a layer-A change (Cir→WASM simulation, ≈13k proven lines), so do it only if the syntactic frame is not enough. Non-recursive calls have bounded call depth, so they do not break the "stack in WASM memory" rule.

### D9 (c). Essential, keep

- Refcounts on immutable acyclic cells. Exact freeing (3.9.1.4) with the simplest proof. A tracing GC needs reachability invariants and 2× memory or a mark stack.
- Substitution, not environments. Closures can keep dead locals alive, which breaks F's term-size bound.
- Sharing by fv. Without it, a λ body that holds big closed data is copied on each call, so time becomes quadratic. The fv_max saturation is needed for 13 header bits; it could shrink after D6.
- Frames as cells, STATIC image, names stored once, 32-bit bounds (`next <= 214748364`, `ptr.bound`). All forced by 3.9.1.4 and 32-bit WASM.
- One fuel-indexed `post` (any fuel) plus one `done` (some fuel ends) per phase. Inherent to `Cir.exec`'s fuel. The *number* of times it is redone is not (P5).
- Fixed interpreter plus data image, and the Cir layer A. Both reasonable and proven. Keep them.

---

## 4. Proof-body pitfalls (the lead's addition)

Each pitfall below says where it comes from: **[design]** or **[technique]**, and what removes it.

### P1. Each heap invariant clause is re-proven by hand after each kind of mutation
- **Shape.** For each mutation (a store, a pop, a swap of roots, an alloc, a release) there is a family `Pc.X, ptr.X, cnt.X(.at), pts.X(.at), pendok.X, heap.X, clo.X(.at), cov.X(.at), static.X, frs.X`. Example: `swap_moves.bend` has `Ptr.sw, cnt.sw.at, Cnt.sw, PendOK.sw, Pts.sw, Heap.sw`, then `Pc.pop, ptr.pop, pendok.pop, cnt.pop.at, …, heap.pop`, then `pendok.st, cnt.st.at, cnt.st, heap.st`, then `ptr.sw2 … acc.sw2`.
- **Size.** 503 defs, ≈8.6k lines repo-wide, spread over 10–12 files.
- **Source.** [technique], made worse by [design] D3. `Cnt` is a global sum (`Pc` over all cells), and `Fs` depends on the pend list.
- **Fix.** Prove one "delta" lemma per primitive, once: "a store of field k at o from a to b keeps `Heap` with counts a−1, b+1", and "a pend push/pop with re-tag keeps `Heap`". Every move then composes primitives. With D3 the delta is local. Better still, state the counts as a multiset equation (counts = ⊎ Fs(o) ⊎ roots).

### P2. Three views of "a cell stands for a term", and two heap invariants, joined by bridges
- **Views.**
  - `Is/IsCK`: relational, with flags (definitions.bend:126–195).
  - `T.tm.of`: a functional reader with fuel (cell_terms.bend).
  - `Tm`: a checked reader with fuel, plus `Al` and `FvOK` (copy_substitution.bend:310).
- **Heap invariants.** `Heap` + `AccK` (exact `Cnt`, `Cov`, `Clo`, zombies) in definitions, against copy_substitution's garbage `P/Q` + zombie size + cover `Cv`.
- **Bridges.** cell_stands_for (538), out_bytes_from_is (312), checked_terms_stay (760), and **copy_bridge (10,305 lines, and its goal `K.copy.post` is still `?TODO`)**.
- **Source.** [technique and process]. Two "frozen" intermediate specs (definitions, copy_substitution) were written in different words, by different units (U0–U15).
- **Fix.** One view only. I suggest the checked functional reader (`Tm`-like) plus a computable footprint `cells(m, c)`. Then the frame lemma is "a write outside the footprint keeps the term", proven once (`checked_terms_stay` already has this shape). Restate `CopyPost`/`HS` in that view, and delete the bridges. This needs the lead to unfreeze one of the two specs.

### P3. About eight program-logic kits for the same Cir semantics
- **Kits.** `Post/PostB/post.seq/postb.seq/mono.seq/rw.seq` (definitions), `DW.Sim/Sim.seq/Sim.wh/WP` (data_walk), `Wp` (copy_walk), `Ok.seq/Ok.loop/X.seq` (copy_kit), `Wp` with `CasesK` (out_bytes), `fits.seq` (cir_fits), `Cp.loop` (copy_gives_subst), `Sh.*` (shift).
- **Fuel monotonicity.** Proven again and again: names with mono/more/ends/done/fin/nd come to ≈376 defs, ≈6.9k lines (an overlapping estimate).
- **Source.** [technique and process]: parallel units.
- **Fix.** One verified `WP(s, Q)` computed by recursion on `Cir.Stmt`, with one soundness theorem against `Cir.exec`, one `while` rule (invariant plus measure), and one fuel-monotonicity lemma. Each phase then gives only an invariant, a measure and the per-branch obligations. The 17 loops of impl.bend each now have their own induction.

### P4. Case splits that only follow the implementation's branches, or all 19 formers
- **Size.** 189 defs with a full split on `Bk.Term` (≈17.6k lines). Examples: `Node.fz` (271 lines, in 2 files), `node.set` (231), `node.fs` (195), and the 33 splits in copy_bridge. Most cases do the same thing: "parts in fields 2/3/4 by the tag mask".
- **Source.** [technique]. The machine is already generic: tag mask and binders come from `Img.table`. The proofs are not.
- **Fix.** Define once `Term.kids(t): List<(Term, binders)>` and `Term.node(t)` (tag, q, name), and prove `kids` agrees with the table mask. State `Is`, `Node`, footprint and `Term.below` over `kids`, and prove the node lemmas by list recursion: one case, not 19.

### P5. "God" signatures and transport noise
- **Signatures.** Statements carry the whole world: `al.reuse.term` has ≈38 parameters, and `mat.miss.ws`/`mat.hit` have ≈40. The latter take states written as `List.set(List.set(List.set(regs2, 22n, …), 24n, …), 23n, …)` inline, three times per statement.
- **Transport.** About 7.4k `Equal.sym/trans/cong` uses, plus `(x, r1) = h` unpacking chains of `P2` tuples (heap_ops has 142 of these chains).
- **Source.** [technique].
- **Fix.** Use record contexts (`Ctx{ds, ks, img, fi, im, lim, inp}`, `HeapV{m, nx, pend, ps}`) and named invariant records with projections, not nested `P2` tuples. The WP of P3 computes the state, so statements do not spell out `List.set` towers.

### P6. Lemma copies across files
- 415 names are defined in 2 or more files (≈8.2k lines in the extra copies).
- Exact or near copies: `rg.of` ×3 (≈260 lines each), `Node.fz`, `is.fz`, `node.ne`, `tbl.mask`, `Mask` (definitions and heap_facts), `atag.lt` ×5, `fs.zero` ×5, `ends.nw` ×3, `heap.pop` / `cnt.pop.at` / `frs.pop.c` (moves_match and swap_moves), `mat.miss` / `mat.go` / `prj.go` (walk and moves_match). Every file also has its own Bool/Nat/U32 kit (`or.assoc`, `lt.le`, `max.le`, `add.comm`, …).
- Some copies are variants: with or without `dk`, or the same body under a different statement.
- **Source.** [process and technique].
- **Fix.** One `Machine/kit.bend` (Bool/Nat/U32/List) and one `heap_kit.bend`. D1 removes the `dk` reason for the variants.

### P7. Bit-blasting the header
- About 125 lemmas destructure a U32 into 32 `WCon`s (each ≈190 lines in copy_header_bits: `Hp.tag.f`, `Hp.q.f`, `Hf.q.f`, `Hp.todo.f`, `Hp.low.f`, …).
- **Source.** [design] (packed header, D7 aliasing) and [technique].
- **Fix.** A small library of mask laws, proven once by bit-blasting: `and(or(a, shl(b, s)), m) = and(a, m)` when the masks are disjoint, and so on. Then every header fact is a rewrite, not a 32-way split. D7 removes the aliasing cases. A 6-field cell (unpacked header) is (b): it costs 4 bytes per cell against F.

### P8. Proofs that work around design choices
| Workaround | Where | Removed by |
|---|---|---|
| `dk` duality, `HSK(False)` inside M.data | definitions, data_*, heap_ops | D1 |
| zombies `zs`, `Pend.terms`, zombie size | AccK, copy_substitution AL | D5 |
| OWNED / `vs` / `Ag.vars` / `Held` | Ag, HS, walk WH (two Ag clauses) | D2 |
| `Mem(ps, o)` inside `Fs`/`Cnt` | `*.pop`, `*.sw`, `pendok.*` | D3 |
| KNOWN store on a shared arg | `mat.miss.ws` hole | D4 |
| todo bits = flag bits; field 1 = count or link | copy_header_bits, copy_frame_tags | D7 |
| shift registers and measure (Sh.start) | shift_gives_shift | D6 |
| 63-element register list | `rg.of`×3, R59, Kept/Disj | D8 (syntactic frame) |
| U32 wrap bounds (`Room`, `ptr.bound`) | spread across files | (c), but centralize in one `bounds` lemma per primitive |

### P9. Each loop's invariant restates the whole heap
- `WH` (walk.bend:876–895) re-asserts `HS`, two `Ag`s, `Kept.cells`, `Stat`, `AccK`, `PsSub`, two budgets and a size bound in every round. `CopyQ` (definitions.bend:1595) is the same.
- **Source.** [technique].
- **Fix.** Split each loop invariant into (i) the frame: "heap outside my footprint unchanged", given by the P2/P3 frame theorems, and (ii) a small local invariant about the loop's own cells and registers. Budgets then become one "allocated ≤ k per round" lemma.

---

## 5. Alternative architecture (same laws, same machine)

Keep L0 (Eval), the abstract state (`Wit`: ret, focus, frames, `A.plugs`, `A.w`, the round/loop proof of moves.bend, which is proven), layer A (Cir→WASM) and the machine's shape. Change only the middle:

```
Eval  ⇐  abstract machine on terms (exists: Wit, AF, moves.bend loop)
      ⇐  [NEW] abstract heap HM: Map<Ptr, Node{tag,q,kids,fv,value,data}>,
           counts as a multiset equation, one footprint, one frame rule;
           machine routines restated as HM operations (alloc/inc/dec/make/copy/walk)
      ⇐  Cir code: proven against HM routine by routine with
           one WP + syntactic register/cell frame + mask-law library
```

- **Term reasoning** (subst, walk, data, out) happens only in the HM layer, over clean nodes.
- **Bits and registers** appear only in the Cir⇐HM step, which is mostly mechanical decoding.
- **Estimated effect.** P1, P2, P4, P5 and P9 shrink sharply. My rough guess is that the remaining work drops to well under half of what the current technique would need. Confidence: medium. No spike has been done.
- **Cost.** It rewrites `definitions.bend`, `move_kit.bend` and `copy_substitution.bend`, which are frozen, so the lead must allow it. The proven easy moves (swap, push, out, match) and the copy proofs would have to be redone. Layer A, Img, the Lean side and the laws do not change.

**Incremental order (cheapest first, each step deletes something):**
1. D1, D2, D3, D4 (code: about 30 Cir lines). This deletes `data_check`/`data_walk`, the `dk` duality and 3+ open holes, and makes `mat.miss.ws` local.
2. One shared kit plus one WP plus the syntactic frame theorems (P3, P6, D8). These are new files; the old ones migrate as they are touched.
3. Pick the single term view and heap invariant (P2), and restate `CopyPost` in it *before* more work on `copy_bridge`.
4. Spikes: D5 (eager free), D6 (poison free variables), D7 (todo bits).

---

## 6. Risks and open questions

1. **Q1.** Do you allow changes to the frozen specs (`definitions.bend`, `move_kit.bend`, `copy_substitution.bend`)? D1–D3, D6 and all of P2 depend on it. The laws (`spec.bend`) do not change.
2. **Q2.** Is time per step a requirement? 3.4.1.4 measures only memory, but the self-compile must finish. D2 adds an inc/dec per argument, and D5 moves free work into `dec`; both are small.
3. **Q3.** D6 asks Eval-level meta-theory (free-variable irrelevance) to be stated as a lemma. Per AGENTS.md 2.3.1, I would propose the exact statement to you before anyone writes it.
4. **Risk.** The duplicate counts are by name; some copies are variants. The pitfall line counts overlap between families, so they are indicators, not exact sums.
5. **Risk.** The rewrite estimates in §5 are extrapolations from the measured cost of the proven moves. No spike has been done.
6. **Risk.** D7 option 2 and D5 must be checked against the per-node budget (≈40 of 64 bytes used now).
7. **Note.** AGENTS.md 2.1.4: many proof files are over 1000 lines. I propose no split here; P2, P3 and P6 would shrink them as a side effect.
