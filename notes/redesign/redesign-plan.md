# Redesign plan: layer B (the machine) and its proofs

Base: `main` @ 4ebef88. All work lands on `feature/redesign`. This plan is executable: each phase says what to write, where, and what gates it. It does not implement anything.

Sources: AGENTS.md, design-assessment.md (D1–D9, P1–P9), law-audit.md (F1–F8), the skills `bend2` and `experimental-bend-spec`, and the code (Machine/impl.bend, Cir/*, Compiler/impl.bend, proof.bend, the internal spec files, the proof files).

Lead update (applies to all of this plan): no questions go to the lead. Every choice is made here, on merit, D6 included. Section 7 gives the AGENTS.md text that the redesign needs. The milestones of AGENTS 3.11 must hold after each phase.

---

## 1. Verdict

1. **Keep the machine's model, replace the proof architecture.** The substitution machine with refcounted immutable cells, frames as cells, a STATIC image and a fixed Cir interpreter is right (assessment D9). Most of the cost is accidental: about six micro-optimizations, three term views, two heap invariants, eight program-logic kits and 19-way splits. The open holes are the core (copy, walk, data, call moves, alloc reuse, shift, input, memory). So the remaining proof work must be redone anyway. Redo it on a clean base, not on top of the 115k lines.
2. **Keep unchanged:** the laws (spec.bend), proof.bend, Compiler/impl.bend, layer A (Compiler/Cir/*, ≈13k proven lines), the image builder (Img.*), img_small.bend, need_big.bend, Eval/Book/Program/Wasm impl, and all Lean. Layer A is generic in the Cir program. It ties to `Mach.code` only by four computed checks (module_valid `mach.ok`, code_size `mach.nodes`, host `mach.hR`, `mach.hd`). These recheck by computation on the new code.
3. **Replace:** everything under `src/Compiler/Machine/` except `impl.bend` (which changes) and `runs_as_eval.bend` (its four statements stay exactly; its bodies are refilled).
4. **Decisions (all on merit, with reasons in §2.3):**

| Item | Decision |
|---|---|
| D1 DATA bit at creation, delete M.data | Yes |
| D2 each argument cell owns its term | Yes |
| D3 re-tag released cells FREE | Yes |
| D4 no KNOWN store on a label miss | Yes |
| D5 free eagerly (cascade in M.dec), no zombies | Yes |
| D6 free variables as poison, delete M.shift | **Yes**, with one Eval lemma family (canon.bend) |
| D7 todo bits off the flag bits | Yes: todo bits move to bits 13–15, and a BUILD flag (bit 12, freed by D2) marks a cell under construction |
| D8 Cir procedures / register frames | No Cir change (layer A stays). A syntactic `writes(s)` frame theorem and register compaction (63 → 53) instead |
| Word/constructor packing (3.10.3) | Not on the critical path. Designed in (generic node kinds); built in the last phase (P9), sized by a Phase 0 measurement |
| Single fuel judgment | Yes: one total-correctness judgment `Tot` per routine and per move. The any-fuel (partial) form follows once from fuel monotonicity. This halves the phase obligations (one law per routine, not `post` plus `done`) |

5. **Effect (estimate, medium confidence).** New layer B ≈ 32–38k lines in total, against ≈115k now with the core still open. Weak agents can fill most holes, because each statement is small and most premises are Bool-valued.

---
## 2. Target architecture

### 2.1 Layers

Each layer has one view or one invariant. A layer speaks of the layer below only through that layer's statements.

```
spec.bend laws ── proof.bend (unchanged) ── layer A (Cir → WASM, unchanged)
                                         └─ layer B interface: runs_as_eval.bend (4 statements, unchanged)
layer B:
  B8 assembly   moves.bend: the loop, mach.safe/sound/complete/memory
  B7 moves      one simulation law per move:  Inv(st, s)  ⟹  Tot(round, st, Inv(AM.move(s)))
  B6 abstract   am.bend: AM.move, a Bend FUNCTION on abstract states (terms, frames);
     machine     am.ok: each move is an admin move, a CStep, or a justified halt
  B5 canon      canon.bend: Eval does not see the index of a free variable (D6)
  B4 routines   one spec per Cir routine (alloc, inc, dec, make, release, push, pop, swap,
                 nth, copy, walk, out, input), in heap terms
  B3 heap       heap.bend: the decode of a cell, the one term view V.tm, its footprint and
                 frame law, the one heap invariant H, the primitive-store lemmas
  B2 header     header.bend: the header codec and the mask laws (the only bit-blasting)
  B1 logic      logic.bend: Tot and its rules (seq, if, while, conseq), a WP for
                 while-free code, the register frame, fuel monotonicity
  B0 kit        kit.bend: one Bool/Nat/U32/List kit
```

### 2.2 The one judgment, the one view, the one invariant

- **Judgment (B1).** `Tot(s, st, B, Q, H)`: some fuel runs `s` from `st` to `next{st2}` with `Q(st2)`, or to `halt{k, st2}` with `H(k, st2)`, or to out of memory only when the memory limit of `st` has fewer than `B` bytes. Never a trap, never out of fuel. Fuel monotonicity (proven once) gives the any-fuel form that `mach.safe` and `mach.sound` need: at any fuel, the run is out of fuel or gives that same outcome.
- **View (B3).** `V.tm(g, x, m, c, d)`: the term of cell `c`, read at most `g` levels deep, at binder depth `d`. It is *checked*: it gives `None` unless each node's header is right (a term tag, fv as its parts give it, DATA = `Term.is_data`, VALUE ⟹ `Eval.vals`, no BUILD bit). A poison cell (a Var whose fv is 0) reads as `Var{d}`. It replaces `Is/IsCK`, `T.tm.of` and `Tm`, and their bridges.
- **Footprint (B3).** `V.cells(g, m, c)`: the cells that the read visits. One frame law: a heap that agrees on fields 0, 2, 3 and 4 of the footprint gives the same view. Every "a write elsewhere keeps the term" fact is this one law.
- **Heap invariant (B3).** `H(x, st, L, rs, fs, chs)`: the own cells split into the live cells `L` and the free list; each live term cell counts its pointers exactly (from live cells and from the owned roots `rs`); every pointer of a live cell goes to a live or a STATIC cell; every live cell is a node of a root's term, a frame, an argument or local cell, or a cell under construction. With D3 and D5, the pointers of a cell depend on that cell only, and there are no zombies.
- **State invariant (B7).** `Inv(x, st, s)`: the registers hold the abstract state `s`; `H` holds with the focus as the one owned root; the focus' view is `s.focus`; the frames from `sp` hold `s.fs`; the image is intact (`ImgOK`); no output. One record of named clauses, not nested `P2` tuples.

### 2.3 How the layers give the laws

- `no_wrong_result`, `no_other_failure`: proof.bend → layer A → `mach.safe`, `mach.sound`, `mach.complete` (B8). B8 runs the loop: `Inv` at the start (input routine); per round, `round.sim` (B7) gives `Inv` of `AM.move(s)` or a halt. `am.ok` (B6) says that each move is an admin move (same term, smaller measure `A.w`), a `CStep` (a canonical step), or a halt that HR justifies. `canon.steps` (B5) turns CSteps into Eval's steps on the real book: the same step count, the same result.
- `enough_memory`: `mach.memory` (B8). Each routine's `Tot` allows out of memory only below its budget; each move's budget is at most `Budget(x, st, s)`; `memory_bound` (its arithmetic, ported) gives `Budget ≤ Program.need`. So with `need ≤ memory(m)`, no round runs out of memory.
- `in_subset` (the new law on branch w/laws) rests on layer A only: module_valid's computed `mach.ok`, the decode round trip, and the halt module. The new `Mach.code` must keep `mach.ok` true; Phase 1's gate checks it. The exact engine model of w/laws changes layer A's host files, not layer B: layer B's interface is `Cir.result(n, Mach.code(), Mach.regs(), Img.cells(ds), i, m)`, which has no engine.

### 2.4 Reasons for the decisions

- **D1–D4.** Each deletes an invariant dimension (the dk duality; OWNED, `vs`, `Held`; the list-dependent `Fs`; the `mat.miss.ws` heap write). D1 needs no loop: only a Tup can be made at run time with DATA set (a Lab or an Rfl has fv 0, so a copy always shares it). So the bit is one branch-free expression in `M.finish` and `M.ret.tup`.
- **D5, eager free.** With no zombies, `M.alloc` pops a FREE cell and changes no other cell. So a borrowed pointer stays valid across every alloc, and only `M.dec` frees. The cascade is one loop with one proof. The total work is the same as today (each freed cell's parts lose one pointer, once); only its time moves. The peak memory is the same or lower. Fallback, only if the computed code-size check fails: `M.dec` pushes to the worklist, and one `M.drain` at the end of each round frees it (zombies then live only inside a move).
- **D6, poison.** The machine runs closed terms. A free variable comes only from a malformed book (an open def body, or the "no local v" case of `Eval.walk.app`). Eval can neither bind such a variable later (subst keeps a free variable free) nor inspect it (walk, prj, mat and data on a Var get stuck or say no), and a result is a byte list, which holds no Var. So the machine makes each such variable a *poison* cell (a Var with fv 0), which a copy always shares and never shifts. The view reads poison at depth `d` as `Var{d}`. That is exactly the canonical form `Canon` (each free variable at depth `d` is `Var{d}`), and Eval's subst maps canonical terms to canonical terms. Deleted: `M.shift` (a second copy loop, 9 registers), `M.var`, the 2^31 free-variable bound (free_variables, read_bound, read_var_*, `Terms.below` premises) and 13 open holes. Added: one Eval lemma family (canon.bend, §4.5). It is pure term meta-theory that weak agents can prove in parallel from day one.
- **D7.** Bits 13–15 hold the todo bits while BUILD (bit 12) is set; `M.finish` clears both and writes fv there. So VALUE, DATA and STATIC are never ambiguous, and `Ptrs` (the counted pointers of a cell) reads "BUILD ⟹ only the fields that are not todo". Bit 12 is free because D2 deletes OWNED.
- **D8.** Procedures in Cir would reopen layer A (≈13k proven lines) for a proof convenience. The syntactic frame `Cir.writes(s)` with `Disj` by computation gives the same benefit. Registers are compacted, and each routine's scratch set is a constant list, so `Disj` closes by `{==}`.
- **Packing (word or constructor cells, AGENTS 3.10.3).** It changes only memory, which 3.4.1.4 measures and does not prove. It adds node kinds whose inner structure is not in cells and must be unpacked (with allocation) when a walk or a redex looks inside. On the critical path it delays the first complete proof, and its right form (word cells, or 2-field constructor cells, which pack every list and word 3×) depends on a census that does not exist yet. The design keeps it local: node kinds are generic (`Tbl.mask`, `Tbl.bind`, `Tbl.former` are Bend functions of the tag; the view, `Ptrs`, the copy and the heap laws are stated over kids, not over formers). A later packing touches only the view's new kind cases, `M.ret.tup`/`M.finish` (pack), `walk.prj`/`redex.prj` (unpack) and `M.out`. Phase 0 measures; P9 builds it when the measure needs it.
- **One judgment.** Every routine and every move ends, so a total statement plus fuel monotonicity gives the partial one. Today each phase has `X.post` (any fuel) and `X.done` (some fuel): two proofs of one run.
- **Assembly.** moves.bend's proven loop (round, loop.post, loop.done, run.*) is the template; it is ported to `Inv`, `Tot` and `CStep`.

---

## 3. Machine code changes (Machine/impl.bend, Phase 1)

All changes land in one commit of Phase 1, because they all break the old proofs anyway. The image (Img.*), `Mach.code`'s top shape (`M.input`, then the loop of `M.ev`/`M.ret`), the frame kinds and the table do not change. Only Cir constructs that the machine already emits are used, so the WASM forms that milestone 4 checks do not grow.

### 3.1 Header and tags

| Bits | Now | New |
|---|---|---|
| 0–5 | tag | tag (same; `K.free() = 46` added; `K.check` 44 and `K.root` 45 deleted) |
| 6–7 | q | q |
| 8 | VALUE (or todo of field 2 under copy) | VALUE only |
| 9 | DATA (or todo of field 3) | DATA only, set when the cell is made |
| 10 | STATIC (or todo of field 4) | STATIC only |
| 11 | KNOWN | KNOWN (frames and argument cells only) |
| 12 | OWNED | **BUILD**: the cell is under construction by a copy |
| 13–31 | fv | fv; while BUILD, bits 13–15 are the todo bits of fields 2–4 |

A *poison* cell is a Var cell (tag 0) whose fv is 0. A real Var always has fv ≥ 1, so the two never mix. A FREE cell has tag 46; field 1 links the free list.

### 3.2 Registers (63 → 53)

Deleted: `ds dok dc` (D1), `ss ssrc scut sroot sk snew samt sdep sres` (D6). Added: `fl` (the cells to free) and `dk` (the cascade's part). `pend` is renamed `free`. New numbering, in this order: `focus mode sp free dx dr aq am fl dk c h tag x y z q n fr k p wt wenv wargs wa wx wq wn wres wok wb wh cs csrc cd ck cnew cenv clen cj croot cm oc ow ov oi ii ib il iu ij t1 t2` (0 to 52). `Mach.regs() = 53`.

Rule: the cascade of `M.dec` writes only `fl aq am dr dk`. No caller passes one of them to `M.dec` (the syntactic frame checks it, §4.1).

### 3.3 Routines, concretely

- **`M.dec(r)` (D5).** As now, the count drops by one. At 0, the cell goes to `fl`, and a loop frees the cells of `fl`: each part (by `Tbl` mask, from the image's table as now) that is not STATIC loses a pointer and joins `fl` at 0; then the cell is released.
  ```
  M.when(M.ne(M.g(r), M.c(0)), M.when(M.not(M.flag(M.g(r), F.static())), M.do([
    M.set(R.dr(), M.sub(M.f(1n, M.g(r)), M.c(1))),
    M.st(1n, M.g(r), M.g(R.dr())),
    M.when(M.eq(M.g(R.dr()), M.c(0)), M.do([
      M.st(1n, M.g(r), M.c(0)),
      M.set(R.fl(), M.g(r)),
      M.while(M.ne(M.g(R.fl()), M.c(0)), M.do([
        M.set(R.aq(), M.g(R.fl())),
        M.set(R.fl(), M.f(1n, M.g(R.aq()))),
        M.set(R.am(), M.entry(2n, M.g(R.aq()))),
        M.free.part(2n, 1), M.free.part(3n, 2), M.free.part(4n, 4),
        M.release(R.aq())]))]))])))
  # M.free.part(k, bit): when am has bit, dk := field k of aq; unless STATIC, its count drops,
  # and at 0 it joins fl (field 1 := fl; fl := dk)
  ```
  ≈ +18 lines. `M.dec.part` is deleted.
- **`M.alloc(r)` (D5).** Pops the free list, or takes a new cell; it frees nothing.
  ```
  M.if(M.ne(M.g(R.free()), M.c(0)), M.do([
    M.set(r, M.g(R.free())), M.set(R.free(), M.f(1n, M.g(r))),
    M.st(0n, M.g(r), M.c(0)), M.st(1n, M.g(r), M.c(0)), M.st(2n, M.g(r), M.c(0)),
    M.st(3n, M.g(r), M.c(0)), M.st(4n, M.g(r), M.c(0))]),
    Cr.Cir.Stmt.alloc{r})
  ```
  ≈ −8 lines (no part decrements).
- **`M.release(r)` (D3).** `M.st(0, r, K.free()); M.st(1, r, free); free := r`. +1 line.
- **`M.release.arg(a)` (D2).** Always: `dx := field 2 of a; M.dec(dx); M.release(a)`. The OWNED test goes.
- **`M.data` (D1).** Deleted (≈35 lines). Its three callers (`M.walk.lam`, the λ case of `M.redex`, `M.ret.let`) read `M.flag(·, F.data())`.
- **DATA at creation (D1).** One expression for a pair `c` (its parts are finished cells):
  ```
  # 512 when the pair's second part is Data and its first is Data or dead
  def M.data.tup(+c: Cr.Cir.Expr) -> Cr.Cir.Expr:
    M.and(M.and(M.f(0n, M.f(3n, c)), M.or(M.f(0n, M.f(2n, c)), M.sub(M.c(0), M.eq(M.q(c), M.c(0))))), M.c(512))
  ```
  `M.finish(c)`: `t1 := 0; when tag(c) = Tup: t1 := M.data.tup(c)`; the last store becomes `or(or(and(f0, 255), t1), shl(cm, 13))` (this also clears BUILD and the todo bits). `M.ret.tup`: the header ors in the same expression over the registers `x` and `focus`. The input's headers already set DATA. ≈ +6 lines.
- **Copy (D6, D7).** `M.copy.walk` has one caller after D6, so it is inlined into `M.copy`.
  - `M.todo.bit(k) = shl(2048, k)` (8192, 16384, 32768); `M.todo(c) = and(f0, 57344)`; `M.todo.first` tests 8192 and 16384; `M.todo.last` shifts the todo bits right by 13.
  - `M.copy.push`: header `or(or(and(f0(src), 255), F.build()), shl(entry2(src), 13))`.
  - `M.copy.root`: header `T.prj | F.build() | 8192`. `M.copy.end`: `r := field 2 of root; M.release(root)` (no K.root store).
  - `M.copy.part`: the shared case and the bound-Var case stay (inc). A local `j < clen`: `t2 :=` the `j`-th local (by `M.nth`), `M.inc(t2)`, put it in field `ck` (no shift, ever). A variable past the locals: `M.poison(t2)`, put it in field `ck`. Any other part: `M.copy.push` as now.
  - `M.poison(r) = M.make(r, M.c(T.var()), M.c(0), M.c(0), M.c(0))`.
  - `M.nth`: the walk down a chain of `j` argument cells by field 1 (today inlined twice: copy.part and walk.app). One loop, one spec.
  - Deleted: `M.shift` (≈18 lines), `M.var`, `M.if.e`, the 9 shift registers.
- **Walk (D2, D4, D6).**
  - `M.walk.prj`: `t1 := field 2 of wx; inc t1; t2 := field 3 of wx; inc t2`; the new argument `wh` holds `t1`; `wa` holds `t2`; then `M.dec(wx)`. (+4 lines.)
  - `M.walk.mat`: the miss branch only sets `wt` (the KNOWN store goes).
  - `M.walk.app`: a local: the new argument holds the local's term, inc'd. No local: `M.poison(wx)`, and the argument owns it.
  - `M.redex`: the first argument `y`: `M.inc(y)` when the argument cell is made; each spine argument: `t1 := field 3 of wh; M.inc(t1)`. (+3 lines.)
  - `M.one(r)`: `M.inc(r)`; its callers release the local with `M.release.arg` (not `M.release`).
- **Net.** ≈ 1,330 → ≈ 1,270 Cir lines. Code nodes grow by the inlined cascade (≈ 40 nodes at each of ≈ 35 `M.dec` sites); the computed check `mach.nodes` (≤ 2^16) must still pass. If it fails, use D5's fallback (`M.drain` once per round).

### 3.4 What the code change must keep (Phase 1 gate)

1. `bend2 --check-only` on `src/main.bend` (holes allowed; only the TODO count is printed).
2. The computed layer-A checks on the new code: `Cir/module_valid.bend` (`mach.ok`), `Cir/simulation_code_size.bend` (`mach.nodes`), `Cir/simulation_host.bend` (`mach.hR`, `mach.hd`), with the kernel (`~/lead/gate.sh`, host `src/main.bend` or the file itself).
3. `src/Compiler/tests/run.ts`: every program of `progs/` compiles, and its module gives what the Lean interpreter gives, on each input. Then `TRUSTED=1 FRESH=1` once (echo.bend through the interpreter).
4. `src/milestones.ts` steps 1–5 (§5.0).
5. The Phase 0 census, run again: the self-compile's peak memory and cells must not grow by more than 5%.

---

## 4. The new internal statements (exact Bend text)

These are the holes that prover agents fill. Each `law` is in a statement file (`<layer>/spec.bend`); its proof is a `def` of the same name in that layer's proof files. Agents never change a statement; a statement change goes through the phase owner (§5.0). The Phase 2 owner checks every text below with `bend2 --check-only` and may fix syntax only.

### 4.0 Folder layout

```
src/Compiler/Machine/
  impl.bend               the machine's code (Phase 1)
  runs_as_eval.bend       layer B's interface: its 4 statements stay exactly; bodies call moves.bend
  shared.bend             B0 kit: Base-only (P2, Ex, Has, Disj, Mem, the Bool/Nat/U32/List lemmas)
  logic/spec.bend         B1          logic/impl.bend
  header/spec.bend        B2          header/impl.bend
  heap/spec.bend          B3          heap/view.bend, heap/count.bend, heap/frame.bend
  image/spec.bend         B3 (image)  image/impl.bend (ported image facts)
  canon/spec.bend         B5          canon/impl.bend (may split: shift.bend, subst.bend, step.bend)
  am/spec.bend            B6          am/impl.bend (ported eval_facts, eval_spine)
  routines/spec.bend      B4          routines/prims.bend, nth.bend, dec.bend, copy.bend, walk.bend,
                                      out.bend, input.bend
  moves/spec.bend         B7          moves/ev.bend, moves/ret.bend, moves/call.bend, moves/round.bend
  memory/spec.bend        B8 (memory) memory/impl.bend (ported memory_bound)
  moves.bend              B8 assembly: the loop, mach.safe/sound/complete/memory.proof
```

This follows `experimental-bend-spec` in spirit (a spec file per unit, proofs beside it, one `shared.bend`). One deviation: a layer's `spec.bend` imports the code that it speaks of (Cir, Machine/impl, Eval), because these are internal proof layers about existing code, not public modules.

Common aliases in the texts below: `Cr` = Cir/impl, `Mc` = Machine/impl, `Bk` = Book/impl, `El` = Eval/impl, `Pg` = Program/impl, `K` = shared.bend, `Lg` = logic/spec, `Hd` = header/spec, `V` = heap/spec, `C` = canon/spec, `A` = am/spec, `R` = routines/spec, `I` = image/spec.

### 4.1 B1 logic/spec.bend

```
# register r of the state st; nothing when there is no register r
def Reg(st: Cr.Cir.State, +r: Nat) -> Maybe<&2, U32>:
  Cr.Cir.eval.get(r, st)

# the memory limit of st, in bytes
def Lim(st: Cr.Cir.State) -> Nat:
  match st:
    case Cr.Cir.State{_, _, _, _, _, _, lim, _, _, _}:
      Nat.mul(65536n, U32.to_nat(lim))

# the run ended: anything but out of fuel
def Out.done(o: Cr.Cir.Out) -> Bool:
  match o:
    case Cr.Cir.Out.not_done{}:
      False{}
    case _:
      True{}

# the outcome o is good: next with Q, a halt with H, out of memory only when the limit lim
# has fewer than b bytes; never a trap, never out of fuel
def Ok(o: Cr.Cir.Out, +lim: Nat, +b: Nat, Q: Cr.Cir.State -> Type, H: U32 -> Cr.Cir.State -> Type) -> Type:
  match o:
    case Cr.Cir.Out.next{st}:
      Q(st)
    case Cr.Cir.Out.halt{s, st}:
      H(s, st)
    case Cr.Cir.Out.out_of_memory{}:
      {Nat.is_lt(lim, b) == True{} : Bool}
    case Cr.Cir.Out.trap{}:
      Empty
    case Cr.Cir.Out.not_done{}:
      Empty

# Tot: with some fuel, s runs from st to a good outcome
def Tot(s: Cr.Cir.Stmt, +st: Cr.Cir.State, +b: Nat, Q: Cr.Cir.State -> Type, H: U32 -> Cr.Cir.State -> Type) -> Type:
  &f:Nat -> Ok(Cr.Cir.exec(f, s, st), Lim(st), b, Q, H)

# no halt
def No(-s: U32, -st: Cr.Cir.State) -> Type:
  Empty

# the registers that s may write: the targets of its sets and allocs
def Cir.writes(s: Cr.Cir.Stmt) -> List<&2, Nat>

# st with the register r set to v; with the field k of the cell c set to v
def St.set(st: Cr.Cir.State, +r: Nat, v: U32) -> Cr.Cir.State
def St.store(st: Cr.Cir.State, +k: Nat, +c: U32, v: U32) -> Cr.Cir.State
def St.cells(st: Cr.Cir.State) -> Cr.Cir.Cells
def St.next(st: Cr.Cir.State) -> U32

# LAW: a run that ends with the fuel f ends the same with more fuel
law exec.more:
  for +f: Nat
  for +g: Nat
  for s: Cr.Cir.Stmt
  for +st: Cr.Cir.State
  for d: {Out.done(Cr.Cir.exec(f, s, st)) == True{} : Bool}
  {Cr.Cir.exec(Nat.add(f, g), s, st) == Cr.Cir.exec(f, s, st) : Cr.Cir.Out}

# LAW: at any fuel, a Tot run is out of fuel or good (what mach.safe and mach.sound use)
law tot.any:
  for s: Cr.Cir.Stmt
  for +st: Cr.Cir.State
  for +b: Nat
  for Q: Cr.Cir.State -> Type
  for H: U32 -> Cr.Cir.State -> Type
  for t: Tot(s, st, b, Q, H)
  for +g: Nat
  Or({Cr.Cir.exec(g, s, st) == Cr.Cir.Out.not_done{} : Cr.Cir.Out}, Ok(Cr.Cir.exec(g, s, st), Lim(st), b, Q, H))

# LAW: a sequence: the first statement runs to a state from which the second does
law tot.seq:
  for a: Cr.Cir.Stmt
  for c: Cr.Cir.Stmt
  for +st: Cr.Cir.State
  for +b: Nat
  for Q: Cr.Cir.State -> Type
  for H: U32 -> Cr.Cir.State -> Type
  for t: Tot(a, st, b, st2 => Tot(c, st2, b, Q, H), H)
  Tot(Cr.Cir.Stmt.seq{a, c}, st, b, Q, H)

# LAW: an if, by the value v of its condition
law tot.if:
  for c: Cr.Cir.Expr
  for y: Cr.Cir.Stmt
  for n: Cr.Cir.Stmt
  for +st: Cr.Cir.State
  for +b: Nat
  for Q: Cr.Cir.State -> Type
  for H: U32 -> Cr.Cir.State -> Type
  for +v: U32
  for e: {Cr.Cir.eval(c, st) == Some{v} : Maybe<&2, U32>}
  for t: Tot(Bool.pick(Cr.Cir.Stmt, U32.is_zero(v), n, y), st, b, Q, H)
  Tot(Cr.Cir.Stmt.if{c, y, n}, st, b, Q, H)

# one round of a while from st, with the invariant I at the measure n: its condition has a
# value; at 0, Q; else the body runs to I at a smaller measure
def Loop(c: Cr.Cir.Expr, body: Cr.Cir.Stmt, +st: Cr.Cir.State, +b: Nat, +n: Nat, I: Nat -> Cr.Cir.State -> Type,
  Q: Cr.Cir.State -> Type, H: U32 -> Cr.Cir.State -> Type) -> Type:
  &v:U32 -> K.P2({Cr.Cir.eval(c, st) == Some{v} : Maybe<&2, U32>},
    Loop.of(U32.is_zero(v), body, st, b, n, I, Q, H))

def Loop.of(zero: Bool, body: Cr.Cir.Stmt, +st: Cr.Cir.State, +b: Nat, +n: Nat, I: Nat -> Cr.Cir.State -> Type,
  Q: Cr.Cir.State -> Type, H: U32 -> Cr.Cir.State -> Type) -> Type:
  match zero:
    case True{}:
      Q(st)
    case False{}:
      Tot(body, st, b, st2 => &k:Nat -> K.P2({Nat.is_lt(k, n) == True{} : Bool}, I(k, st2)), H)

# LAW: the while rule: an invariant I, indexed by a measure that each round lowers
law tot.while:
  for c: Cr.Cir.Expr
  for body: Cr.Cir.Stmt
  for +b: Nat
  for I: Nat -> Cr.Cir.State -> Type
  for Q: Cr.Cir.State -> Type
  for H: U32 -> Cr.Cir.State -> Type
  for r: @n: Nat -> @st: Cr.Cir.State -> I(n, st) -> Loop(c, body, st, b, n, I, Q, H)
  for +n: Nat
  for +st: Cr.Cir.State
  for i: I(n, st)
  Tot(Cr.Cir.Stmt.while{c, body}, st, b, Q, H)

# LAW: a weaker conclusion: a larger budget, weaker posts
law tot.wk:
  for s: Cr.Cir.Stmt
  for +st: Cr.Cir.State
  for +b: Nat
  for +b2: Nat
  for Q: Cr.Cir.State -> Type
  for Q2: Cr.Cir.State -> Type
  for H: U32 -> Cr.Cir.State -> Type
  for H2: U32 -> Cr.Cir.State -> Type
  for hb: {Nat.is_le(b, b2) == True{} : Bool}
  for hq: @st2: Cr.Cir.State -> Q(st2) -> Q2(st2)
  for hh: @k: U32 -> @st2: Cr.Cir.State -> H(k, st2) -> H2(k, st2)
  for t: Tot(s, st, b, Q, H)
  Tot(s, st, b2, Q2, H2)

# LAW: a statement with no while runs with the fuel 0 (its WP is its run at fuel 0)
law tot.wp:
  for s: Cr.Cir.Stmt
  for +st: Cr.Cir.State
  for +b: Nat
  for Q: Cr.Cir.State -> Type
  for H: U32 -> Cr.Cir.State -> Type
  for o: Ok(Cr.Cir.exec(0n, s, st), Lim(st), b, Q, H)
  Tot(s, st, b, Q, H)

# LAW: a set, as an equation of the run (the rewrite kit: exec.store, exec.alloc.new,
# exec.halt, reg.set, reg.store, fd.store, lim.set, lim.store have the same shape)
law exec.set:
  for +f: Nat
  for +r: Nat
  for e: Cr.Cir.Expr
  for +st: Cr.Cir.State
  for +v: U32
  for he: {Cr.Cir.eval(e, st) == Some{v} : Maybe<&2, U32>}
  for hr: {Nat.is_lt(r, Mc.Mach.regs()) == True{} : Bool}
  for hl: {List.length(&2, U32, St.regs(st)) == Mc.Mach.regs() : Nat}
  {Cr.Cir.exec(f, Cr.Cir.Stmt.set{r, e}, st) == Cr.Cir.Out.next{St.set(st, r, v)} : Cr.Cir.Out}

# LAW: a register after a set
law reg.set:
  for +st: Cr.Cir.State
  for +r: Nat
  for +v: U32
  for +q: Nat
  for hr: {Nat.is_lt(r, List.length(&2, U32, St.regs(st))) == True{} : Bool}
  {Reg(St.set(st, r, v), q) == Bool.pick(Maybe<&2, U32>, Nat.is_eq(r, q), Some{v}, Reg(st, q)) : Maybe<&2, U32>}

# LAW: the register frame: a register that s does not write keeps its value
law frame.regs:
  for +f: Nat
  for s: Cr.Cir.Stmt
  for +st: Cr.Cir.State
  for +st2: Cr.Cir.State
  for +r: Nat
  for e: {Cr.Cir.exec(f, s, st) == Cr.Cir.Out.next{st2} : Cr.Cir.Out}
  for w: {K.Has(Cir.writes(s), r) == False{} : Bool}
  {Reg(st2, r) == Reg(st, r) : Maybe<&2, U32>}

# LAW: a run keeps the limit, the input, first and image (frame.fixed: one law, by a
# projection St.fixed(st) of those four)
law frame.fixed:
  for +f: Nat
  for s: Cr.Cir.Stmt
  for +st: Cr.Cir.State
  for +st2: Cr.Cir.State
  for e: {Cr.Cir.exec(f, s, st) == Cr.Cir.Out.next{st2} : Cr.Cir.Out}
  {St.fixed(st2) == St.fixed(st) : St.Fixed}
```

### 4.2 B2 header/spec.bend

The only file with 32-bit bit-blasting. Every other header fact is a rewrite by these laws. The encoder is the image's own `Mc.Img.header(t, q, fl, fv)`.

```
def Hd.tag(h: U32) -> U32:
  U32.and(h, 63)

def Hd.q(h: U32) -> U32:
  U32.and(U32.shrn(h, 6n), 3)

def Hd.has(h: U32, +bit: U32) -> Bool:
  U32.is_ne(U32.and(h, bit), 0)

def Hd.fv(h: U32) -> U32:
  U32.shrn(h, 13n)

# the header's parts fit: a tag below 64, a quantity below 4, flags only in bits 8 to 12, fv
# below 2^19
def Hd.fits(+t: U32, +q: U32, +fl: U32, +fv: U32) -> Bool:
  U32.is_lt(t, 64) && U32.is_lt(q, 4) && U32.is_eq(U32.and(fl, 4294959359), 0) && U32.is_lt(fv, 524288)

# LAW: the tag of a header (hd.q_of, hd.fv_of: the same shape)
law hd.tag_of:
  for +t: U32
  for +q: U32
  for +fl: U32
  for +fv: U32
  for h: {Hd.fits(t, q, fl, fv) == True{} : Bool}
  {Hd.tag(Mc.Img.header(t, q, fl, fv)) == t : U32}

# LAW: a flag of a header is the flag of fl, for a bit of 8 to 12
law hd.has_of:
  for +t: U32
  for +q: U32
  for +fl: U32
  for +fv: U32
  for +bit: U32
  for h: {Hd.fits(t, q, fl, fv) == True{} : Bool}
  for hb: {Hd.flag_bit(bit) == True{} : Bool}
  {Hd.has(Mc.Img.header(t, q, fl, fv), bit) == Hd.has(fl, bit) : Bool}

# LAW: a mask that misses b keeps a's bits (mask.or.hit, mask.and.assoc, mask.shl.low,
# mask.shr.or: the same family, each proven once by its 32 bits)
law mask.or.miss:
  for +a: U32
  for +b: U32
  for +m: U32
  for e: {U32.and(b, m) == 0 : U32}
  {U32.and(U32.or(a, b), m) == U32.and(a, m) : U32}
```

The table, as Bend functions of the tag (the image's table cells must equal them: `img.table`, §4.4):

```
# the fields that hold counted pointers, by tag: 1 field 2, 2 field 3, 4 field 4. Terms as the
# image's table; frames and argument cells: field 2 (Rwt's frame: fields 2 and 3); FREE: none
def Tbl.mask(+t: U32) -> U32

# the binders above field k of a term of tag t
def Tbl.bind(+t: U32, +k: Nat) -> Nat

# a term of tag t is a value by its form
def Tbl.former(+t: U32) -> Bool
```

### 4.3 B3 heap/spec.bend

```
# what a run never changes: the book, the image's names and terms (from cell 1), the image's
# last cell, the first own cell
type Cx is Data:
  Cx{ds: List<&2, Bk.Def>, ks: List<&2, List<&2, Word(8n)>>, img: List<&2, Bk.Term>, im: U32, fi: U32}

# an owned root: a cell and its term at depth 0
type Rt is Data:
  Rt{c: U32, t: Bk.Term}

# a chain of argument cells (linked by field 1) from the cell c, with their arguments (A.Ag)
type Ch is Data:
  Ch{c: U32, as: List<&2, A.Ag>}

def Fd(+k: Nat, m: Cr.Cir.Cells, +c: U32) -> U32:
  Cr.Cir.Cell.get(k, Cr.Cir.Cells.get(m, c))

def Tg(m: Cr.Cir.Cells, +c: U32) -> U32:
  Hd.tag(Fd(0n, m, c))

def Fl(m: Cr.Cir.Cells, +c: U32, +bit: U32) -> Bool:
  Hd.has(Fd(0n, m, c), bit)

def Fv(m: Cr.Cir.Cells, +c: U32) -> U32:
  Hd.fv(Fd(0n, m, c))

# the counted pointers of the cell c: the fields of Tbl.mask of its tag, less the todo
# fields while it is BUILD
def Ptrs(m: Cr.Cir.Cells, +c: U32) -> List<&2, U32>

# the term of the cell c at the depth d, read at most g levels deep, checked: a term's tag and
# no BUILD; fv as the parts give it (saturated at 524287); DATA iff Term.is_data; VALUE only
# when Eval.vals; a Ref or an Enu is the image's term at its cell; a Lab or a Mat names the
# name of its number (ks); a Var with fv 0 (poison) is Var{d}
def V.tm(g: Nat, x: Cx, m: Cr.Cir.Cells, +c: U32, +d: Nat) -> Maybe<&2, Bk.Term>

# V.tm with the fuel of the state: next levels are enough, as the cells form no cycle
def V.at(x: Cx, st: Cr.Cir.State, +c: U32, +d: Nat) -> Maybe<&2, Bk.Term>:
  V.tm(U32.to_nat(Lg.St.next(st)), x, Lg.St.cells(st), c, d)

# the cells that V.tm reads
def V.cells(g: Nat, m: Cr.Cir.Cells, +c: U32) -> List<&2, U32>

# m and m2 agree on the fields 0, 2, 3 and 4 of each cell of cs
def Agree(cs: List<&2, U32>, m: Cr.Cir.Cells, m2: Cr.Cir.Cells) -> Bool

# LAW: the frame law: a heap that agrees on what the read reads gives the same term
law view.frame:
  for +g: Nat
  for +x: Cx
  for +m: Cr.Cir.Cells
  for +m2: Cr.Cir.Cells
  for +c: U32
  for +d: Nat
  for a: {Agree(V.cells(g, m, c), m, m2) == True{} : Bool}
  {V.tm(g, x, m2, c, d) == V.tm(g, x, m, c, d) : Maybe<&2, Bk.Term>}

# LAW: more fuel reads the same term
law view.more:
  for +g: Nat
  for +h: Nat
  for +x: Cx
  for +m: Cr.Cir.Cells
  for +c: U32
  for +d: Nat
  for +t: Bk.Term
  for e: {V.tm(g, x, m, c, d) == Some{t} : Maybe<&2, Bk.Term>}
  {V.tm(Nat.add(g, h), x, m, c, d) == Some{t} : Maybe<&2, Bk.Term>}

# LAW: deeper, a cell whose real variables are below d reads as its term shifted from d: only
# its poison moves (the copy's sharing rests on this)
law view.deeper:
  for +g: Nat
  for +x: Cx
  for +m: Cr.Cir.Cells
  for +c: U32
  for +d: Nat
  for +k: Nat
  for +t: Bk.Term
  for hf: {Nat.is_le(U32.to_nat(Fv(m, c)), d) == True{} : Bool}
  for e: {V.tm(g, x, m, c, d) == Some{t} : Maybe<&2, Bk.Term>}
  {V.tm(g, x, m, c, Nat.add(d, k)) == Some{El.Term.shift(t, k, d)} : Maybe<&2, Bk.Term>}

# LAW: a store to a cell outside cs, or to field 1 of any cell, keeps Agree (agree.store1:
# the field-1 case)
law agree.store:
  for cs: List<&2, U32>
  for +m: Cr.Cir.Cells
  for +o: U32
  for +k: Nat
  for +v: U32
  for n: {K.Mem(cs, o) == False{} : Bool}
  {Agree(cs, m, Cr.Cir.Cells.set(m, o, Cr.Cir.Cell.set(k, Cr.Cir.Cells.get(m, o), v))) == True{} : Bool}
```

The heap invariant is one Bool, so a proof splits it with `Bool.and` lemmas and closes concrete parts by `{==}`. Each clause has a projection law (`h.part`, `h.cnt`, …: `H(...) == True → Clause(...) == True`).

```
# the own cells (from fi to next) are the live ones L and the free list's, each once; the free
# list is the chain from the register free, by field 1, each cell FREE
def Part(x: Cx, st: Cr.Cir.State, L: List<&2, U32>) -> Bool

# each live cell that is not STATIC and not BUILD counts its pointers: from the live cells
# (Ptrs) and from the owned roots rs, exactly
def Cnt(m: Cr.Cir.Cells, L: List<&2, U32>, rs: List<&2, Rt>) -> Bool

# each pointer of a live cell goes to a live cell or a STATIC one
def Clo(m: Cr.Cir.Cells, L: List<&2, U32>) -> Bool

# each root reads as its term at depth 0, and is live or STATIC
def Rts(x: Cx, st: Cr.Cir.State, L: List<&2, U32>, rs: List<&2, Rt>) -> Bool

# the frames from the register sp hold fs: kind (tag), q, KNOWN (k), the terms a (field 2)
# and b (field 3, Rwt's only)
def Frs(x: Cx, st: Cr.Cir.State, fs: List<&2, AF>) -> Bool

# each chain's cells hold its arguments (tag K.arg, q, KNOWN, the term in field 2)
def Chs(x: Cx, st: Cr.Cir.State, chs: List<&2, Ch>) -> Bool

# each live cell is a node of a root's, a frame's or an argument's term (in V.cells), or a
# frame or argument cell; no live cell is BUILD
def Cov(x: Cx, st: Cr.Cir.State, L: List<&2, U32>, rs: List<&2, Rt>, fs: List<&2, AF>, chs: List<&2, Ch>) -> Bool

# the image is intact (§4.4), next is at most 214748364, and there are Mach.regs() registers
def Base(x: Cx, st: Cr.Cir.State) -> Bool

# the heap invariant
def H(x: Cx, st: Cr.Cir.State, L: List<&2, U32>, rs: List<&2, Rt>, fs: List<&2, AF>, chs: List<&2, Ch>) -> Bool:
  Part(x, st, L) && Cnt(Lg.St.cells(st), L, rs) && Clo(Lg.St.cells(st), L) && Rts(x, st, L, rs) &&
    Frs(x, st, fs) && Chs(x, st, chs) && Cov(x, st, L, rs, fs, chs) && Base(x, st)
```

Pure heap lemmas (no Cir; one per primitive effect). Each says how `H` changes when the cells change in one way. Example, the others have the same shape (`h.dec1` for a count above 1, `h.release`, `h.pop_free`, `h.new_node` for a finished term node over owned roots, `h.frame`, `h.arg`, `h.unarg`):

```
# LAW: a root gains a pointer: its count + 1, and it is a root once more
law h.inc:
  for +x: Cx
  for +st: Cr.Cir.State
  for +L: List<&2, U32>
  for +rs: List<&2, Rt>
  for +fs: List<&2, AF>
  for +chs: List<&2, Ch>
  for +c: U32
  for +t: Bk.Term
  for h: {H(x, st, L, rs, fs, chs) == True{} : Bool}
  for hn: {Held(x, st, L, rs, fs, chs, c, t) == True{} : Bool}
  {H(x, Inc(st, c), L, Con{Rt{c, t}, rs}, fs, chs) == True{} : Bool}
```

Here `Held(..., c, t)`: `c` is STATIC, or live, and a node of a held term, and it reads as `t` at depth 0. `Inc(st, c)` is `st` with field 1 of `c` plus 1 when `c` is not STATIC (what `M.inc` does).

### 4.4 B3 image/spec.bend

The image does not change, so its facts are ported (salvage: img_ok, image_layout, image_flags, image_header_bits, image_names, image_nm, image_occ, image_tries, image_positions, image_term_facts, first_cell_past_table, read_var_bound; ≈4.6k lines today). Only their conclusions change: from `IsK`/`ImgOKK` with `dk` to `V.tm` and one Bool.

```
# the context of a book's run: its names (Img.known of its bodies' names), the terms of the
# image's k cells, and the first own cell
def Cx.of(+ds: List<&2, Bk.Def>, +k: U32, +first: U32) -> V.Cx

# the image is intact: cells 1 to 15 as Img.prefix makes them; the table's cells 272 to 290
# give Tbl.mask, Tbl.bind and Tbl.former; each def's body cell reads as its body (V.tm at
# depth 0); each cell from 1 to im is STATIC; each cache cell (16 to 271) holds 0 or a STATIC
# cell of its byte
def ImgOK(x: V.Cx, m: Cr.Cir.Cells) -> Bool

# LAW: the image at the start of a run of a book that Book.read reads
law img.start:
  for +p: List<&2, Word(8n)>
  for +ds: List<&2, Bk.Def>
  for +i: List<&2, Word(8n)>
  for +m: U32
  for +k: U32
  for +len: U32
  for +pg: U32
  for +lim: U32
  for +first: U32
  for rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>}
  for small: {Mc.Img.small(p, 0) == True{} : Bool}
  for s: Start(Mc.Img.cells(ds), i, m, k, len, pg, lim, first)
  {ImgOK(Cx.of(ds, k, first), Cr.Cir.load(Mc.Img.cells(ds), 1, Cr.Cir.Cells.none{})) == True{} : Bool}

# LAW: the image stays when the cells 1 to im agree (img.frame); the cache stays when its
# cells' fields 2 do not change (img.cache)
law img.frame:
  for +x: V.Cx
  for +m: Cr.Cir.Cells
  for +m2: Cr.Cir.Cells
  for h: {ImgOK(x, m) == True{} : Bool}
  for a: {V.Agree(Img.range(V.Cx.im(x)), m, m2) == True{} : Bool}
  {ImgOK(x, m2) == True{} : Bool}
```

`St0`, `Start` and `Cells.bytes` move from definitions.bend to image/spec.bend unchanged.

### 4.5 B5 canon/spec.bend (D6)

Pure Eval meta-theory. It imports Base, Book, Eval, Program and shared.bend only. It is independent of the machine, so it can start on day one.

```
# a Bool equality of terms (term.is_eq_ok: True gives the equation; term.is_eq_refl)
def Term.is_eq(a: Bk.Term, b: Bk.Term) -> Bool

# r is Some of t
def Tm.is(r: Maybe<&2, Bk.Term>, t: Bk.Term) -> Bool

# t at the depth d: each variable free there (at the inner depth e, an index of d + e or more)
# becomes the one canonical free variable Var{d + e}; the others stay
def Canon.term(t: Bk.Term, +d: Nat) -> Bk.Term

def Canon.opt(r: Maybe<Bk.Term>) -> Maybe<Bk.Term>

# t is canonical at depth 0
def Canon.is(t: Bk.Term) -> Bool:
  Term.is_eq(Canon.term(t, 0n), t)

# a step of Eval, made canonical
def CStep(+ds: List<&2, Bk.Def>, +t: Bk.Term) -> Maybe<Bk.Term>:
  Canon.opt(El.Eval.step(ds, t))

# n canonical steps from r
def CSteps(n: Nat, +ds: List<&2, Bk.Def>, r: Maybe<Bk.Term>) -> Maybe<Bk.Term>

# LAW: Eval does not see the index of a free variable: a canonical step from the canonical
# form of t is the canonical form of t's step
law canon.step:
  for +ds: List<&2, Bk.Def>
  for +t: Bk.Term
  {CStep(ds, Canon.term(t, 0n)) == CStep(ds, t) : Maybe<Bk.Term>}

# LAW: n canonical steps from the canonical form of t are the canonical form of n of Eval's
# steps (by canon.step, on n)
law canon.steps:
  for +n: Nat
  for +ds: List<&2, Bk.Def>
  for +t: Bk.Term
  {CSteps(n, ds, Some{Canon.term(t, 0n)}) == Canon.opt(El.Eval.steps(n, ds, t)) : Maybe<Bk.Term>}

# LAW: the result does not see free variables
law canon.result:
  for +ds: List<&2, Bk.Def>
  for r: Maybe<Bk.Term>
  {Pg.Program.result(ds, Canon.opt(r)) == Pg.Program.result(ds, r) : Maybe<&2, List<&2, Word(8n)>>}

# LAW: nor the size (canon.vals, canon.data, canon.idem, canon.start: the same shape:
# Eval.vals, Term.is_data, Canon.term twice, Program.start(i) is canonical)
law canon.size:
  for +t: Bk.Term
  for +d: Nat
  {Pg.Term.size(Canon.term(t, d)) == Pg.Term.size(t) : Nat}

# LAW: the copy's substitution: the canonical form of a substitution of a canonical term t
# (at depth d + |es|) by canonical terms es is the canonical form of the substitution of t
# itself; and a part whose real variables are below d is unchanged by it but for its poison
# (canon.subst_below), and Term.lift of a canonical local is its shift (canon.lift)
law canon.subst:
  for +t: Bk.Term
  for +es: List<&2, Bk.Term>
  for +d: Nat
  {Canon.term(El.Term.subst(Canon.term(t, Nat.add(d, List.length(&2, Bk.Term, es))), es, d), d) ==
    Canon.term(El.Term.subst(t, es, d), d) : Bk.Term}
```

The proof route (for the canon owner): a relation `Rel(d, n, t, u)` (the same shape; a variable bound inside or below `d + n` is the same in both; above, both are free), proven kept by `Term.shift`, `Term.subst`, `Env.sub`, `Eval.walk`, `Eval.vals`, `Eval.callWalk`, `Eval.redex`, `Eval.step`; and `Canon.term(t, d) = Canon.term(u, d)` iff `Rel(d, 0, t, u)`. Eval inspects an index only in subst, shift, `Env.sub` and `Eval.walk.app` (whose variable comes from the book's case tree, never from the running term). Expected size: 2–3k lines, mostly per-former congruences; by its structure it suits weak agents best.

### 4.6 B6 am/spec.bend

am/spec.bend imports no machine layer, and heap/spec.bend imports it (for `AF` and `Ag`). `FK`, `AF`, `A.plug`, `A.plugs`, `A.w*` and `AF.ok` move here from definitions.bend unchanged (AF.ok becomes Bool). eval_facts.bend and eval_spine.bend are ported here.

```
# an argument or a local: its quantity, KNOWN, and its term (heap/spec's chains hold them)
type Ag is Data:
  Ag{q: Bk.Quan, k: Bool, t: Bk.Term}

# an abstract state: mode 1 (ret), the focus' term, the frames, innermost first
type AS is Data:
  AS{ret: Bool, focus: Bk.Term, fs: List<&2, AF>}

# a move's outcome: the next abstract state, or a halt with its status and its bytes, in order
type AO is Data:
  AO.next{s: AS}
  AO.halt{k: U32, out: List<&2, Word(8n)>}

# what an abstract walk gives: the leaf, its locals and the arguments left; or it waits for
# more arguments; or no walk exists
type AW is Data:
  AW.leaf{u: Bk.Term, e: List<&2, Ag>, xs: List<&2, Ag>}
  AW.waits{}
  AW.none{}

def AS.term(s: AS) -> Bk.Term
def AS.w(s: AS) -> Nat

# what a state knows, but for the focus' flag: each frame's AF.ok; a focus to return is a
# value; the whole term is canonical
def AS.ok0(+ds: List<&2, Bk.Def>, s: AS) -> Bool

# and the focus' VALUE flag vb is only on a value
def AS.ok(+ds: List<&2, Bk.Def>, vb: Bool, s: AS) -> Bool:
  AS.ok0(ds, s) && (Bool.not(vb) || El.Eval.vals(ds, AS.focus(s), False{}))

# the walk of the machine (M.walk) on terms: Eval.walk, with KNOWN carried as M.walk carries
# it, and a missing local as the canonical free variable
def AM.walk(+ds: List<&2, Bk.Def>, t: Bk.Term, e: List<&2, Ag>, xs: List<&2, Ag>) -> AW

# the move of the machine (one round of Mach.code) on terms; vb is the focus' VALUE flag
def AM.move(+ds: List<&2, Bk.Def>, vb: Bool, s: AS) -> AO

# a move is right: an admin move (the same term, a smaller measure) or the term's canonical
# step, each to a state that knows what AS.ok0 asks; or a halt 0 with the term's result, or a
# halt 2 when the term has no step and no result
def AO.ok(+ds: List<&2, Bk.Def>, s: AS, o: AO) -> Bool

# LAW: each move of the machine is right
law am.ok:
  for +ds: List<&2, Bk.Def>
  for +vb: Bool
  for +s: AS
  for ok: {AS.ok(ds, vb, s) == True{} : Bool}
  {AO.ok(ds, s, AM.move(ds, vb, s)) == True{} : Bool}

# LAW: the abstract walk's terms are Eval's walk, made canonical (AW.eval: the leaf's
# Canon(Term.spine(xs, Term.subst(u, e, 0))))
law am.walk_eval:
  for +ds: List<&2, Bk.Def>
  for +t: Bk.Term
  for +xs: List<&2, Ag>
  for hc: {Ag.canon(xs) == True{} : Bool}
  {AW.eval(AM.walk(ds, t, [], xs)) == C.Canon.walk(El.Eval.walk(t, [], Ag.args(xs))) : Maybe<Maybe<Bk.Term>>}
```

`AM.move` is a function, so `am.ok` splits by `AM.move`'s cases, one helper law per move (≈30), each a short term argument. The owner writes `AM.move` to mirror `M.ev` and `M.ret` branch by branch.

### 4.7 B4 routines/spec.bend

A routine's law says what the Cir code does to the heap, in `H` terms, with `Tot`. Each routine has one law (no `.post`/`.done` pair). Each routine's scratch registers are a constant list `Mc.M.<r>.scr()` (in impl.bend, beside the routine), and `Lg.Cir.writes(code) ⊆ scr` is checked by `{==}`.

```
# the state after the routine: the registers outside ws, the input, the limit, first and the
# image are as before
def Same(st: Cr.Cir.State, st2: Cr.Cir.State, ws: List<&2, Nat>) -> Bool

# the cells of L2 are among L's and keep their fields 0, 2, 3, 4 from st to st2; next is the
# same; and Same(st, st2, ws)
def Kept(st: Cr.Cir.State, st2: Cr.Cir.State, L: List<&2, U32>, L2: List<&2, U32>, ws: List<&2, Nat>) -> Bool

# LAW: M.inc(r): the cell of r gains a pointer, and is one more root; no cell is taken
law inc.spec:
  for +x: V.Cx
  for +st: Cr.Cir.State
  for +L: List<&2, U32>
  for +rs: List<&2, V.Rt>
  for +fs: List<&2, A.AF>
  for +chs: List<&2, V.Ch>
  for +r: Nat
  for +c: U32
  for +t: Bk.Term
  for h: {V.H(x, st, L, rs, fs, chs) == True{} : Bool}
  for hr: {Lg.Reg(st, r) == Some{c} : Maybe<&2, U32>}
  for hn: {V.Held(x, st, L, rs, fs, chs, c, t) == True{} : Bool}
  Lg.Tot(Mc.M.inc(r), st, 0n,
    st2 => K.P2({V.H(x, st2, L, Con{V.Rt{c, t}, rs}, fs, chs) == True{} : Bool}, {Kept(st, st2, L, L, []) == True{} : Bool}),
    Lg.No)

# LAW: M.dec(r): the root of r loses its pointer; the cells that then have none are freed, at
# once and in cascade; no cell is taken
law dec.spec:
  for +x: V.Cx
  for +st: Cr.Cir.State
  for +L: List<&2, U32>
  for +rs: List<&2, V.Rt>
  for +fs: List<&2, A.AF>
  for +chs: List<&2, V.Ch>
  for +r: Nat
  for +c: U32
  for +t: Bk.Term
  for h: {V.H(x, st, L, Con{V.Rt{c, t}, rs}, fs, chs) == True{} : Bool}
  for hr: {Lg.Reg(st, r) == Some{c} : Maybe<&2, U32>}
  for hw: {K.Has(Mc.M.dec.scr(), r) == False{} : Bool}
  Lg.Tot(Mc.M.dec(r), st, 0n,
    st2 => &L2:List<&2, U32> -> K.P2({V.H(x, st2, L2, rs, fs, chs) == True{} : Bool},
      {Kept(st, st2, L, L2, Mc.M.dec.scr()) == True{} : Bool}),
    Lg.No)

# LAW: M.make(r, h, a, b, c), with the values hv, av, bv, cv of its expressions (which do not
# read r): r gets a cell n that was FREE or new, with the fields hv, 1, av, bv, cv; every other
# cell keeps its fields; out of memory only below the cells up to fi + |L| + 1
law make.spec:
  for +x: V.Cx
  for +st: Cr.Cir.State
  for +L: List<&2, U32>
  for +rs: List<&2, V.Rt>
  for +fs: List<&2, A.AF>
  for +chs: List<&2, V.Ch>
  for +r: Nat
  for h: Cr.Cir.Expr
  for a: Cr.Cir.Expr
  for b: Cr.Cir.Expr
  for c: Cr.Cir.Expr
  for +v: Cr.Cir.Cell
  for hs: {V.H(x, st, L, rs, fs, chs) == True{} : Bool}
  for he: {Evals(st, r, h, a, b, c) == Some{v} : Maybe<&2, Cr.Cir.Cell>}
  Lg.Tot(Mc.M.make(r, h, a, b, c), st, V.Cells.bytes(V.Cx.fi(x), Nat.add(List.length(&2, U32, L), 1n)),
    st2 => &n:U32 -> {Took(x, st, st2, L, r, n, v) == True{} : Bool},
    Lg.No)
```

`Took(x, st, st2, L, r, n, v)`: `n` is FREE (the head of the free list, which moves on) or `n` is the old next (and next moves on); `r` holds `n`; cell `n` is `v` with field 1 = 1; every other cell and register (but `r`, `free` and M.alloc's scratch) is unchanged. The pure lemma `h.new_node` (B3) then gives `H` with `n` live and owned. The same pattern covers `push.spec`, `pop.spec`, `swap.spec`, `release.spec`, `release_arg.spec` (= dec then release), `one.spec`, and `nth.spec`:

```
# LAW: M.nth: t2 gets the j-th cell of the chain from cenv (j in t1, below the chain's length)
law nth.spec:
  for +x: V.Cx
  for +st: Cr.Cir.State
  for +ce: U32
  for +as: List<&2, A.Ag>
  for +j: Nat
  for hc: {V.Chs(x, st, [V.Ch{ce, as}]) == True{} : Bool}
  for he: {Lg.Reg(st, Mc.R.t2()) == Some{ce} : Maybe<&2, U32>}
  for hj: {Lg.Reg(st, Mc.R.t1()) == Some{U32.from_nat(j)} : Maybe<&2, U32>}
  for hl: {Nat.is_lt(j, List.length(&2, A.Ag, as)) == True{} : Bool}
  Lg.Tot(Mc.M.nth(), st, 0n,
    st2 => &c:U32 -> K.P2({Lg.Reg(st2, Mc.R.t2()) == Some{c} : Maybe<&2, U32>},
      K.P2({V.Chs.at(x, st, ce, j, c) == True{} : Bool}, {Kept(st, st2, [], [], [Mc.R.t1(), Mc.R.t2()]) == True{} : Bool})),
    Lg.No)
```

The large routines:

```
# LAW: M.copy(n, src), src wt (a call's leaf, d = 0) or z (a λ's or a let's body, d = 1): the
# cell c of src reads as t at the depth d, and is live or STATIC; the chain from cenv holds the
# locals es, and clen is their number. n gets a new owned root of the canonical form of
# t with es put in; the cells of L keep their fields 0, 2, 3, 4; out of memory only below the
# cells up to fi + |L| + the result's nodes + 1
law copy.spec:
  for +x: V.Cx
  for +st: Cr.Cir.State
  for +L: List<&2, U32>
  for +rs: List<&2, V.Rt>
  for +fs: List<&2, A.AF>
  for +chs: List<&2, V.Ch>
  for +wt: Bool
  for +d: Nat
  for +c: U32
  for +t: Bk.Term
  for +ce: U32
  for +es: List<&2, A.Ag>
  for h: {V.H(x, st, L, rs, fs, Con{V.Ch{ce, es}, chs}) == True{} : Bool}
  for hs: {Lg.Reg(st, Copy.src(wt)) == Some{c} : Maybe<&2, U32>}
  for ht: {V.Held.at(x, st, L, rs, fs, chs, c, d, t) == True{} : Bool}
  for he: {Lg.Reg(st, Mc.R.cenv()) == Some{ce} : Maybe<&2, U32>}
  for hl: {Lg.Reg(st, Mc.R.clen()) == Some{U32.from_nat(List.length(&2, A.Ag, es))} : Maybe<&2, U32>}
  Lg.Tot(Mc.M.copy(Mc.R.n(), Copy.src(wt)), st, Copy.budget(x, L, t, es),
    st2 => &n:U32 -> &L2:List<&2, U32> -> K.P2({Lg.Reg(st2, Mc.R.n()) == Some{n} : Maybe<&2, U32>},
      K.P2({V.H(x, st2, L2, Con{V.Rt{n, Copy.term(t, es)}, rs}, fs, Con{V.Ch{ce, es}, chs}) == True{} : Bool},
        {Kept(st, st2, L, L2, Mc.M.copy.scr()) == True{} : Bool})),
    Lg.No)

# the copy's term: C.Canon.term(El.Term.subst(t, A.Ag.terms(es), 0n), 0n)
def Copy.term(t: Bk.Term, es: List<&2, A.Ag>) -> Bk.Term
```

The copy's proof: one `tot.while` with the invariant "the root's *partial* view is constant": a field still to copy reads as `Canon(subst(view of its source part at its depth, es, depth))`, a copied field as its view. Initially the partial view is `Copy.term(t, es)`; each round keeps it (share: `view.deeper` and `canon.subst`; local: `canon.lift`; past the locals: poison; push: the same view; finish: todo empty, so partial = real). The measure is the number of source nodes still to copy.

```
# LAW: M.walk: the case tree at wt (a STATIC cell of the term tt), on the argument chain at
# wargs (xs): wres 1 at a leaf (wt its cell, wenv and wn its locals, wargs the arguments left),
# 2 when it waits, 3 when no walk exists, as AM.walk says; the arguments' cells move to wenv
# or are released; it takes one cell per Prj node walked and per missing local (poison), and no other
law walk.spec:
  for +x: V.Cx
  for +st: Cr.Cir.State
  for +L: List<&2, U32>
  for +rs: List<&2, V.Rt>
  for +fs: List<&2, A.AF>
  for +chs: List<&2, V.Ch>
  for +tc: U32
  for +tt: Bk.Term
  for +ca: U32
  for +xs: List<&2, A.Ag>
  for h: {V.H(x, st, L, rs, fs, Con{V.Ch{ca, xs}, chs}) == True{} : Bool}
  for hw: {Lg.Reg(st, Mc.R.wt()) == Some{tc} : Maybe<&2, U32>}
  for ha: {Lg.Reg(st, Mc.R.wargs()) == Some{ca} : Maybe<&2, U32>}
  for ht: {V.Static.is(x, st, tc, tt) == True{} : Bool}
  Lg.Tot(Mc.M.walk(), st, Walk.budget(x, L, tt),
    st2 => &L2:List<&2, U32> -> {Walk.post(x, st, st2, L, L2, rs, fs, chs, A.AM.walk(V.Cx.ds(x), tt, [], xs)) == True{} : Bool},
    Lg.No)

# LAW: M.out, in mode 1 with no frame, from the focus' cell of the value v: halt 0 with the
# bytes of v (Program.unbytes) as its output, or halt 2 when v is no list of bytes; it takes
# no cell; out of memory only when the output does not fit after next
law out.spec:
  for +x: V.Cx
  for +st: Cr.Cir.State
  for +v: Bk.Term
  for iv: {Inv(x, st, A.AS{True{}, v, []}) == True{} : Bool}
  Lg.Tot(Mc.M.out(), st, Nat.add(Nat.mul(20n, U32.to_nat(Lg.St.next(st))), Pg.Term.size(v)), Lg.No,
    k => st2 => {Out.end(v, k, st2) == True{} : Bool})

# LAW: M.input, from Cir.result's start: the focus holds the start term, as Inv asks; out of
# memory only below the cells up to first + 1 + 27 |i|
law input.spec:
  for +p: List<&2, Word(8n)>
  for +ds: List<&2, Bk.Def>
  for +i: List<&2, Word(8n)>
  for +m: U32
  for +k: U32
  for +len: U32
  for +pg: U32
  for +lim: U32
  for +first: U32
  for rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>}
  for small: {Mc.Img.small(p, 0) == True{} : Bool}
  for s: I.Start(Mc.Img.cells(ds), i, m, k, len, pg, lim, first)
  Lg.Tot(Mc.M.input(), I.St0(Mc.Mach.regs(), Mc.Img.cells(ds), first, k, pg, lim, i), Input.budget(first, i),
    st => {Inv(I.Cx.of(ds, k, first), Mode0(st), A.AS{False{}, Pg.Program.start(i), []}) == True{} : Bool},
    Lg.No)
```

`Inv` (B7) is defined in routines/spec.bend, because `out.spec` and `input.spec` use it:

```
# the state st holds the abstract state s: the registers focus, mode, sp; H with the focus as
# the one owned root and no chain; the frames from sp hold s.fs; the focus' VALUE flag only on
# a value; no output
def Inv(x: V.Cx, st: Cr.Cir.State, s: A.AS) -> Bool
```

It is Bool, with its live set computed: `L` is the list of the own cells that are not on the free list (`V.Live(st)`), so `Inv` needs no witness.

### 4.8 B7 moves/spec.bend

```
# the focus cell's VALUE flag
def Vb(st: Cr.Cir.State) -> Bool

# a round goes on to a state that Inv finds for the move's next state; or it halts as the
# move halts, with the move's bytes as the output (last first)
def Next(x: V.Cx, o: A.AO) -> Cr.Cir.State -> Type
def Halt(o: A.AO) -> U32 -> Cr.Cir.State -> Type

# the bytes that a round may need (ported Budget, Need: §4.9)
def Budget(x: V.Cx, st: Cr.Cir.State, s: A.AS) -> Nat

# LAW: one round of the main loop moves as AM.move says
law round.sim:
  for +x: V.Cx
  for +st: Cr.Cir.State
  for +s: A.AS
  for iv: {R.Inv(x, st, s) == True{} : Bool}
  Lg.Tot(Mc.Mach.round(), st, Budget(x, st, s), Next(x, A.AM.move(V.Cx.ds(x), Vb(st), s)), Halt(A.AM.move(V.Cx.ds(x), Vb(st), s)))
```

`Mach.round()` is the body of the main loop, made a named def in impl.bend (`Mach.code` then uses it; its value does not change). `round.sim` splits by the code's branches into one law per move. Each states its abstract state in parts and its outcome concretely, so `AM.move` computes to it by `{==}`. Example (the others: `mv.ev.val`, `mv.ev.former`, `mv.ev.var`, `mv.ev.ref`, `mv.ev.ann`, `mv.ev.let`, `mv.ev.unlet`, `mv.ev.tup`, `mv.ev.tup0`, `mv.ev.rwt`, `mv.ev.min`, `mv.out`, `mv.ret.swap`, `mv.ret.app.lam`, `mv.ret.fun.lam`, `mv.ret.app.prj`, `mv.ret.fun.prj`, `mv.ret.app.mat`, `mv.ret.fun.mat`, `mv.ret.app.call`, `mv.ret.fun.call`, `mv.ret.let`, `mv.ret.tupb`, `mv.ret.tupa`, `mv.ret.rwt`, `mv.ret.minb`, `mv.ret.mina`; the same 30 as move_kit.bend):

```
# LAW: mode 0, the focus App q f a, not flagged VALUE: f, in the frame App q □ a
law mv.ev.app:
  for +x: V.Cx
  for +st: Cr.Cir.State
  for +q: Bk.Quan
  for +f: Bk.Term
  for +a: Bk.Term
  for +fs: List<&2, A.AF>
  for iv: {R.Inv(x, st, A.AS{False{}, Bk.Term.App{q, f, a}, fs}) == True{} : Bool}
  for hv: {Vb(st) == False{} : Bool}
  Lg.Tot(Mc.M.ev(), st, Budget(x, st, A.AS{False{}, Bk.Term.App{q, f, a}, fs}),
    Next(x, A.AO.next{A.AS{False{}, f, Con{A.AF{A.FK.arg{}, q, False{}, a, a}, fs}}}), Lg.No)
```

Eight parameters. Today's `mv.ev.app` has about 20, plus the premise `IV`.

### 4.9 B8 memory/spec.bend and the assembly

- `Need`, `Need.bytes`, `Budget`, `Defs.big`, `StepSize` are ported from definitions.bend with the zombie terms removed: `Need(x, st, s) = Stat + 16 + 2·max(|term|, |CStep term|) + 3·Defs.big(ds)` own cells.
- Laws (ported from memory_bound.bend, ≈1.7k lines, its arithmetic kept):

```
# LAW: a round's budget is at most F, for a state of a run of n steps (the term is one of the
# run's terms: CSteps(j, ds, start) with j ≤ n)
law budget.need:
  for +p: List<&2, Word(8n)>
  for +ds: List<&2, Bk.Def>
  for +i: List<&2, Word(8n)>
  for +n: Nat
  for +j: Nat
  for +x: V.Cx
  for +st: Cr.Cir.State
  for +s: A.AS
  for rd: {Bk.Book.read(p) == Some{ds} : Maybe<List<&2, Bk.Def>>}
  for hj: {Nat.is_le(j, n) == True{} : Bool}
  for ht: {C.Tm.is(C.CSteps(j, ds, Some{Pg.Program.start(i)}), A.AS.term(s)) == True{} : Bool}
  for iv: {R.Inv(x, st, s) == True{} : Bool}
  {Nat.is_le(Budget(x, st, s), Pg.Program.need(p, i, n)) == True{} : Bool}
```

- moves.bend: the proven loop (round.post, loop.post, loop.done, run.*, mach.*.proof) is ported to `Inv`, `Tot` (with `tot.any` for the any-fuel lemmas), `CSteps` and `canon.steps`. `mach.memory.proof` (today a bare `?TODO`) follows the same loop with `budget.need`. runs_as_eval.bend's four bodies call it.

---

## 5. Phases

### 5.0 Rules for every phase

- **Branch.** Each phase works in its own worktree off `feature/redesign` and merges into it. A lane (a set of disjoint files) of a phase may merge alone once its gate passes. `main` is not touched.
- **Statements are owned.** Only the phase owner (a strong agent) writes or changes a `spec.bend` or a def that a statement uses. A prover agent changes only proof bodies and adds helper lemmas in its own proof file. A statement that seems false goes back to the owner, with the counterexample or the failing subgoal.
- **One hole ledger** (`reports/redesign/holes.md`, outside the repo): each open `?TODO` in the closure of `src/main.bend`, its file, its lane, its owner. The gate compares the TODO count with it.
- **Gate (never `--verdict`).** A merge needs all of:
  - **G1** `~/lead/gate.sh WT <file> [src/main.bend]` on each changed `.bend` file: `bend2 --check-only` prints only a TODO count, and the kernel check (kdiag3) prints no FAIL.
  - **G2** `bend2 --check-only src/main.bend` from `src/`: it loads; its TODO count equals the ledger's.
  - **G3** the milestones (AGENTS 3.11) still hold: `~/lead/milestones.sh WORK LOG` on the merge commit, that is `src/milestones.ts` steps 1–5: (1) `lake build`, no axiom but Lean's (milestones 1–3); (2) main.bend's book holds the trusted Bend versions exactly (milestones 2, 3; this also guards that main, `Compiler.compile` and the laws did not change); (3) the WASM tests pass and each form that the compiler emits is run by a passing test (milestone 4; it catches a machine change that emits a new form); (4) the host agrees; (5) the differential run agrees (milestone 4). Steps 4–5 do not depend on layer B; run all five at each merge anyway (they are cheap and the rule is "after every phase").
  - **G4** (phases that change `Machine/impl.bend` only) `bun src/Compiler/tests/run.ts WORK` passes (every program of `progs/` gives what the Lean interpreter gives), once with `TRUSTED=1 FRESH=1`; and the computed layer-A checks pass in the kernel: `Cir/module_valid.bend` (`mach.ok`), `Cir/simulation_code_size.bend` (`mach.nodes`), `Cir/simulation_host.bend` (`mach.hR`, `mach.hd`).
  - **G5** hygiene: no def name is defined in two files of the closure (a one-line script over `^def `/`^law `); no import of a deleted file; `bun run typecheck` and the lint if TypeScript changed.
- **Never touched by the redesign:** src/Compiler/spec.bend, src/Compiler/impl.bend, src/Compiler/proof.bend, src/Compiler/Cir/*, src/Compiler/img_small.bend, src/Compiler/need_big.bend, src/Eval, src/Book, src/Program, src/Wasm, src/main.bend, every `.lean` file, the `bend` submodule. (Branch w/laws owns the law and engine changes; a merge from it into `feature/redesign` reruns G2 and G3.)

### 5.1 Phase list

| Phase | What | Agents | Est. lines |
|---|---|---|---|
| P0 | Measure; set up the branch, the ledger, the gate list | 1 strong | ~300 (TS) |
| P1 | Machine code (§3); delete the old layer-B proof tree | 1 strong | −110k, +~60 Cir |
| P2 | The skeleton: every spec file and def of §4, every law as a `?TODO`, the assembly proven from the laws | 3 strong, then 1 | ~6–8k |
| P3 | Fill every hole, in lanes, in parallel | many weak + gen2, 2 strong reviewers | ~25–30k |
| P4 | Close the closure: 0 holes; `bend -o src/main.bend` works | 1 strong | small |
| P5 | Sweeps (AGENTS 2.1.3) | 1 strong | net deletion |
| P6 | Packing, only if P0's or P4's census needs it | 1 strong + weak | ~3–5k |
| P7 | The self-host run of 3.8.7, with branch w/laws' single-B script | 1 strong | small |

### 5.2 P0: measure and set up

1. Create the worktree of `feature/redesign`; write the hole ledger (35 holes today, as the law audit lists them) and the list of files that the gate covers.
2. Measure on 4ebef88 (a Measurement test, bend2 kinds: no pass or fail; script `src/Compiler/tests/census.ts`):
   - the size of `write(prune B)` for main.bend's book (law audit: it must be below 2^26 bytes, else the compiler compiles itself to `halt(1)`);
   - the self-compile on the real engine: the compiled compiler (compile.ts on the pruned book) run by host.ts on its own pruned book's bytes: the peak pages, the peak live cells, and a census of the live cells at the peak by tag and by shape (bits of words, list cells, other Tups, frames, arguments);
   - the node count of `Mach.code()` against the 2^16 bound of `mach.nodes` (headroom for D5's inlined cascade);
   - the gate's time per file (to size the lanes).
3. Decide P6 by the census: if the peak after P1 is at most 3.5 GiB, P6 is not needed; else P6 builds the packing that the census favors (word cells when words dominate; 2-field constructor cells when lists and other constructors dominate). If the pruned book is near 2^26 bytes, record it as a P7 blocker (the cutoff is in Compiler/impl.bend, which this redesign does not touch).

Gate: G5 (TypeScript), G3.

### 5.3 P1: the machine code

Files:
- Changed: `src/Compiler/Machine/impl.bend` (§3; also `Mach.round()` as a named def, and each routine's `scr()` list).
- Changed: `src/Compiler/Machine/runs_as_eval.bend`: the four statements stay byte for byte; the bodies become `?TODO`; the import of moves.bend goes. The closure then has 4 holes.
- Deleted (salvage later by `git show 4ebef88:<path>`): every other file of `src/Compiler/Machine/` (the ~60 proof files, scratch_*.bend, copy_counterexamples.bend) and `src/Compiler/Machine/scripts/gen.ts` (its symbolic runs are replaced by `tot.wp` and the rewrite kit).
- Kept unchanged: all of §5.0's list.

Gate: G1 on the two changed files; G2 (4 holes); G3; G4; P0's census again (the peak must not grow by more than 5%; D2 adds one count per argument, D5 frees earlier).

Not parallel: one agent, one commit for the code, one for the deletions.

### 5.4 P2: the skeleton

Goal: the whole proof DAG exists, every law is stated, every def that a law uses is written, and the top (moves.bend, runs_as_eval.bend) is *proven* from the laws. Then every hole is independent of every other, and P3 can run them all at once.

Lanes (disjoint files; one strong agent each):
- **S1** shared.bend, logic/spec.bend, header/spec.bend (+ `Cir.writes`, `St.*`, `Tbl.*`).
- **S2** heap/spec.bend, image/spec.bend, routines/spec.bend (`V.tm`, `V.cells`, `Ptrs`, `H` and its clauses, `ImgOK`, `Cx.of`, the routine laws, `Inv`). Needs S1's and S3's names, not their proofs: S1 and S3 publish their def headers on day 1.
- **S3** canon/spec.bend, am/spec.bend (`Canon.term`, `CStep`, `CSteps`, `Term.is_eq`, `AM.walk`, `AM.move`, `AO.ok`, the ported `FK/AF/A.*`).
- **S4** (after S1–S3 merge) moves/spec.bend, memory/spec.bend, moves.bend (the assembly, ported and proven from the laws), runs_as_eval.bend's bodies.

Each lane also writes its proof files with one `def <law>(...): ?TODO` per law, so the book loads.

Checks that the statements are right, before P3 spends on them (the biggest risk is a false statement):
- a second strong agent reads each law against the code and §2 (review of statements only, AGENTS 2.3.2);
- computed checks on tiny states (a `*_smoke.bend` file per lane, outside main's closure, deleted in P5): `V.tm` on the start image of a two-def book gives the bodies; `AM.move` on small terms matches what `Mach.round()` does on the same state (both computed with `{==}`); `Canon.term` and `CStep` on terms with free variables.

Gate: G1 per file, G2 (TODO count = the ledger: every law hole of §4, and no hole in moves.bend), G3, G5.

### 5.5 P3: fill the holes

All holes are independent. Lanes are by file, so two agents never edit one file. Each lane has a weak agent (Haiku or Sonnet) driving gen2, and a strong reviewer per four lanes who answers statement questions and writes the hard skeletons (loop invariants).

| Lane | Files | Holes (approx.) | Depends on (statements only) | Agent | Est. lines |
|---|---|---|---|---|---|
| F1 kit | shared.bend | ~60 small | none | weak | 1.2k (salvage) |
| F2 logic | logic/impl.bend | ~15 | F1 names | weak, strong for `tot.while` | 1.2k |
| F3 header | header/impl.bend | ~12 bit-blast | none | weak (gen2 + case split on 32 bits) | 1k |
| F4 canon | canon/impl.bend (+ shift.bend, subst.bend, step.bend) | ~40 | none | 2–3 weak | 2.5k |
| F5 am | am/impl.bend | ~35 (one per move + walk) | canon names | 2 weak | 2k (salvage eval_facts, eval_spine) |
| F6 heap | heap/view.bend, heap/count.bend, heap/frame.bend | ~40 | header, logic names | 2 weak, strong for `view.deeper` | 3.5k |
| F7 image | image/impl.bend | ~20 (port) | heap names | weak | 3k (salvage image_*) |
| F8 prims | routines/prims.bend, routines/nth.bend | ~15 | heap, logic | weak | 1.5k |
| F9 dec | routines/dec.bend | 1 loop + ~10 | heap, logic | strong skeleton, weak fill | 1k |
| F10 copy | routines/copy.bend | 1 loop + ~25 | heap, canon | strong skeleton, 2 weak | 3k |
| F11 walk | routines/walk.bend | 1 loop + ~20 | heap, am | strong skeleton, weak | 2k |
| F12 out | routines/out.bend | 2 loops + ~10 | heap | weak | 1k |
| F13 input | routines/input.bend | 2 loops + ~15 | heap, image | weak (salvage start_input's arithmetic) | 2k |
| F14 moves | moves/ev.bend, moves/ret.bend, moves/call.bend | 30 | routines, am | 3 weak | 4.5k |
| F15 memory | memory/impl.bend | ~10 | moves, canon | weak (port memory_bound) | 1.5k |

Total ≈ 31k lines, against ≈115k today. Order of priority, when agents are few: F1, F2, F3 first (they make gen2 stronger on everything else: the rewrite kit, the mask laws); then F4, F6, F8 (the most used lemmas); then the rest. A hole's proof may use any law, proven or not, so no lane waits for another lane's proofs.

Gate per merge: G1 on the lane's files, G2 (the ledger's count falls), G3, G5.

### 5.6 P4: close

- 0 holes in the closure of `src/main.bend` (G2 prints no TODO).
- `bend -o src/main.bend` gives the `.bendtt` (it refuses while holes exist); Shared/lower.ts's output and it agree on `Trusted.lean`'s check (G3 step 2 on both).
- Then the lead's check: `--verdict` must print "ALL PROOFS CHECK" (AGENTS 3.2.5). This plan does not run it.

### 5.7 P5: sweeps

AGENTS 2.1.3, as written: sweep 1 on the branch diff from 4ebef88 (thermo-nuclear, erasure, cyclomatic-complexity), then later sweeps on the scope that the lead picks. Delete the smoke files, any helper with no caller, and any duplicate lemma. Proof bodies are exempt from review sweeps (AGENTS 2.3.2), so the sweep reads statements, defs and code.

### 5.8 P6: packing (only if P0's census needs it)

Built on the proven machine, so the gate catches every regression. Touches: `Tbl.*` (new tags), `V.tm` (the new kind's term), `M.ret.tup`/`M.finish` (pack), `M.walk.prj` and the Prj redex (unpack, which takes cells), `M.out` (read a packed byte), `out.spec`, `copy.spec` (no change: kids are generic), the memory laws (a packed cell has fewer cells than nodes, so `Need` holds as is). AGENTS 3.10.3 changes then (§7).

### 5.9 P7: the self-host run

With branch w/laws' single-B script (law audit F3): parse main.bendtt once, `Book.check`, the Trusted check, `write (prune B)`, `interp` FRESH, write the binary, print the SHA-256. Then measure 3.4.1.4: the binary compiles itself on the real engine within 4 GiB.

---

## 6. gen2

### 6.1 Conventions that every statement follows

1. **Small.** At most 8–10 explicit parameters. The static context is one record (`V.Cx`); the abstract state is one record (`A.AS`). A move law takes `x`, `st`, the parts of its focus, `fs`, `Inv`, and one or two branch facts.
2. **Bool premises.** A premise is `{P(...) == True{} : Bool}` with `P` computable (`H`, `Inv`, `Held`, `Chs`, `ImgOK`, `AS.ok`, `AO.ok`, `Disj`, `Has`, `Mem`), or a register or field equation `{Lg.Reg(st, r) == Some{c} : Maybe<&2, U32>}`. A Bool invariant is split by `Bool.and` laws and its concrete parts close by `{==}`.
3. **Rewrite-shaped conclusions.** An equation's left side is the term to rewrite, and its head is the function that gen2 indexes it by (`Cr.Cir.exec`, `Lg.Reg`, `V.tm`, `C.CStep`, `Hd.tag`, `U32.and`, …).
4. **No towers.** States are built by named updaters (`St.set`, `St.store`, `V.Inc`), never by inline `List.set(List.set(...))`. No statement destructures a `P2` chain: each invariant clause has a projection law.
5. **Generic over kids.** A heap or view fact is proven by recursion on `Kids`/`Ptrs` lists, not by a split on the 19 formers. The 19-way splits live only in the defs `V.tm`, `Canon.term`, `AM.*` and in canon's congruence lemmas.
6. **One judgment.** Every Cir fact is a `Tot`. A loop is proven only by `tot.while`, with its invariant and measure written by the lane's strong reviewer; the holes are then the branch obligations. A while-free piece is proven by `tot.wp` and the rewrite kit (`exec.*`, `reg.*`, `fd.*`).
7. **Frames by computation.** The scratch registers of a routine are a constant list; `{K.Disj(...) == True{} : Bool}` and `{K.Has(Lg.Cir.writes(<code>), r) == False{} : Bool}` close by `{==}`.
8. **Unique names, by layer prefix:** `exec.*`, `tot.*`, `reg.*`, `frame.*`, `hd.*`, `mask.*`, `tbl.*`, `view.*`, `agree.*`, `h.*`, `img.*`, `canon.*`, `term.*`, `am.*`, `<routine>.spec`, `mv.*`, `budget.*`. gen2's helpers are `<def>.h<i>` in the same file. G5 rejects a name defined twice.
9. **One file, one owner.** At most ~1,500 lines per file (AGENTS 2.1.4: a larger file is split only with the lead's assent, so split by lane in P2 instead).

### 6.2 gen2 features that pay off most (for branch w/gen2-up), in order

1. **A Cir runner tactic.** On a goal `Lg.Tot(s, st, ...)` or `Lg.Ok(Cr.Cir.exec(0n, s, st), ...)` with `s` concrete: unfold `seq`/`if`/`set`/`store` by the `exec.*` laws, discharge each `Cr.Cir.eval` side condition by rewriting `Lg.Reg` and `V.Fd` with the hypotheses, and stop at a routine call (`Mc.M.copy(...)`, …) to apply its `*.spec` law and chain the frame (`Kept`, `Same`). It replaces Machine/scripts/gen.ts. About 60% of the holes (routines and moves) are of this kind.
2. **Bool splitting and hypothesis harvest.** From `{a && b == True}` in context, add `a` and `b`; on a goal `{a && b == True}`, split it; case-split on a Bool subterm that blocks evaluation.
3. **Bounded U32/Nat arithmetic.** Decide linear facts over `U32.is_lt/is_le/add/sub/inc` and `U32.to_nat` under no-wrap hypotheses (next ≤ 214748364, counts ≤ next).
4. **List normal forms.** `List.get` after `List.set` with literal indices; `Has`, `Mem`, `Disj` on literal lists; `List.length` of literal lists.
5. **Induction templates.** Structural induction on `Bk.Term` where each case closes by the hypotheses and congruence (canon's ≈40 holes are of this kind), and on lists (`Kids`, `Ptrs`, chains).
6. **A statement lint mode.** Flag a statement with more than 10 parameters, a non-Bool premise that could be Bool, a `List.set` tower, or a duplicate name.

---

## 7. AGENTS.md changes

The redesign keeps every law, theorem and milestone. It needs one text change, and only when P6 decides the packing. Replace 3.10.3 with:

> - **3.10.3** TODO: the compiled compiler compiling itself needs more memory than WASM's 4 GiB (4.6 GB when measured), so 3.4.1.4 does not hold yet. The census of the self-compile (`src/Compiler/tests/census.ts`) picks a packed cell kind (a word cell, or a cell for a constructor of two fields); the machine's node kinds are generic, so the change is local to the view, to the making and the opening of a pair, and to the output. The proofs of the machine must cover it.

No other AGENTS.md text changes for this redesign. Remarks:
- D6 needs no AGENTS text: canon.bend's laws are proven by `--verdict` with the rest of the book, and they are internal to layer B (AGENTS 2.2.1: their place is canon/spec.bend's header).
- 3.9.1.4's rules stay true: every unreachable cell is freed (now as soon as its last pointer goes), names are stored once, the stack is in WASM memory, and the cache stays at most 6144 cells.
- The texts of law audit F1–F6 (3.6.1.4 `in_subset`, the engine model, 3.7.1, 3.9.1.3.4, 3.3.8) belong to branch w/laws.

---

## 8. What is kept, adapted, redone

| Work | Lines | Fate | Why |
|---|---|---|---|
| Layer A (Compiler/Cir/*) | ≈20.5k | **Kept unchanged** | Generic in the Cir program; ties to the machine only by 4 computed checks |
| img_small, need_big, proof.bend, spec.bend, Compiler/impl.bend | ≈4.2k | **Kept unchanged** | The image and the compile function do not change |
| Eval, Book, Program, Wasm, all Lean | — | **Kept unchanged** | Out of scope; pinned by Lean or by review |
| image_*, img_ok, first_cell_past_table, read_var_bound | ≈4.6k | **Adapted** → image/impl | The image is the same; only the conclusion's view changes |
| memory_bound | ≈1.7k | **Adapted** → memory/impl | Its arithmetic stays; `Need` loses the zombie terms |
| eval_facts, eval_spine | ≈1.4k | **Adapted** → am/impl | Term facts; the statements move to `AS`/`CStep` |
| moves.bend's loop and run | ≈1.2k | **Adapted** → moves.bend | Proven structure; ported to `Inv`, `Tot`, `CSteps` |
| cir_fits (output fits at halt 0) | ≈1.2k | **Adapted** → memory/impl | Cir-level facts; re-proven on the new code with `Tot` |
| start_input (its arithmetic), copy_header_bits (its bit-blast core), checked_terms_stay (its shape), definitions' "More fuel" and kits | parts | **Salvaged** into input.bend, header/impl, view.frame, logic/impl, shared.bend | The proofs' shapes fit the new statements |
| definitions, move_kit, copy_substitution, accounting, heap_facts, heap_ops, cell_terms, cell_stands_for, copy_* (9 files), data_check, data_walk, walk, swap_moves, moves_push, moves_match, moves_copy, moves_call, moves_out, out_bytes, out_bytes_from_is, statement_runs, shift_gives_shift, free_variables, read_bound, read_var_g, input_bridge, scratch_*, scripts/gen.ts | ≈95k | **Redone or deleted** | They are stated over the old views and invariants (HS, AccK, Ag, dk, zombies), or over code that goes (M.data, M.shift). The proven easy moves (swap_moves: 5.4k lines for 7 moves) cost ≈100–150 lines each in the new layers, less than a bridge to the old statements |

---

## 9. Risks

1. **A false statement in P2** (most likely: `copy.spec`'s budget, `Walk.post`, `Inv`'s frame clauses). Effect: a lane stalls. Mitigation: a second strong agent reviews every statement; smoke computations on tiny states; the owner fixes a statement within a day, and the ledger records it.
2. **The code-size bound** (`mach.nodes` ≤ 2^16) fails with the cascade inlined at every `M.dec`. Mitigation: P0 measures the headroom; fallback `M.drain` once per round (§2.4).
3. **Canon's subtleties** (poison under binders; `view.deeper`; `canon.subst`). Mitigation: the canon lane starts on day one and proves `canon.subst` and `canon.step` before the copy lane needs them; smoke checks of `Canon.term` on open terms.
4. **Checker cost of Bool invariants** on symbolic states (a big constant inside `H` would be expanded at every match). Mitigation: no literal constant above 2^16 inside `H` or `Inv` (as definitions.bend's note warns); P2 measures the gate's time per file.
5. **gen2's upgrade lags.** The conventions help the current gen2 too; strong reviewers write loop skeletons by hand.
6. **The self-compile does not fit even after P6.** It is a measured goal (3.4.1.4), not a law; P6 then adds the second packing kind. No proof is lost: the kinds are generic.
7. **The pruned book is 2^26 bytes or more** (law audit). Then the compiler compiles itself to `halt(1)`, and the fix (a larger cutoff in Compiler/impl.bend, img_small, need_big) is outside this redesign. P0 measures it first.
8. **Merges from w/laws.** Layer B's interface has no engine, so only layer A's host files and the Lean joining change there. Each merge reruns G2 and G3.
9. **Throwing away proven work** (the easy moves, out_bytes). Accepted: re-proving them in the new layers is cheaper than bridging, and git keeps every line for salvage.

## 10. Deferred items

None. By the lead's update, every choice above is made on merit, and no item waits for the lead. The only text for the lead's file is §7's 3.10.3, which waits for P6's census.
