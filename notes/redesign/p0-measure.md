# P0 measurements (redesign-plan.md §5.2)

Measured on feature/redesign at d57bb26 / 6693442 (= main 4ebef88 plus gen2.ts and the w/laws law
fixes; the machine and its book are those of 4ebef88), in WSL (Ubuntu 24.04, 12 cores, 15 GB),
through ~/lead/heavy.sh. Script: src/Compiler/tests/census.ts (commit d94bad2), a measurement (bend2
kinds: no pass or fail).

## 1. Pruned book size vs Img.small (2^26 bytes)

`write (prune B)` of main.bend's book (lower.ts → Book/scripts/Write.lean): **761,548 bytes = 1.1 % of
2^26** (67,108,864). Far below: no P7 blocker. (main.bendtt itself: 27.2 MB of text.)

## 2. Mach.code node count vs the 2^16 bound of mach.nodes

Computed by `CS.NS(Mc.Mach.code())` (redesign-scratch/measure.bend, bend2 evaluation):

| | NS(Mach.code) | bound | T.dep (bound 50,000) | regs |
|---|---|---|---|---|
| 4ebef88 | 39,318 | 65,536 | 5,184 | 63 |
| after P1 (4908672) | 21,892 | 65,536 | 2,686 | 53 |

Headroom at 4ebef88: 26,218 nodes, enough for D5's inlined cascade. After P1 the code is smaller
(the three `M.dec`s inlined in every `M.alloc` are gone), so D5's fallback is not needed.

## 3. Gate time per file (gate.sh: bend2 + lower + kdiag3; wall time, slots shared)

| File | Host | Time | Kernel |
|---|---|---|---|
| Machine/impl.bend | itself | 2 s | 246 defs, 0 fail |
| Cir/module_valid.bend | itself | 10 s | 67 defs, 0 fail |
| Cir/simulation_code_size.bend | itself | 14–24 s | 23 defs, 0 fail |
| Cir/simulation_host.bend | itself | 25–30 s | 99 defs, 0 fail |
| Machine/runs_as_eval.bend (old, importing moves.bend) | itself | 130 s | 4 defs, 1 fail (mach.memory hole) |
| Machine/heap_facts.bend (old) | moves.bend | 75 s | (kdiag matched 0 names through the host) |
| main.bend, bend2 only (G2) | — | 58 s at 4ebef88; 11 s after P1 | — |

Sizing: a lane file that lowers alone costs about 10–30 s per gate run; a file checked through a large
host (the old moves.bend closure) costs 1–2 min. P2 should keep each new file loadable alone (its
spec.bend imports, not a moves.bend-sized closure), so G1 stays under ~30 s per file.

## 4. Self-compile census

The compiled compiler (compile.ts on main.book, 1,380,365-byte module) run in bun's engine
(JavaScriptCore) on main.book's own bytes, as host.ts runs it.

Trial with a memory maximum of 4,096 pages (256 MiB): out of memory after 200 s, all 13,322,479 own
cells live (the free list is empty at an out-of-memory in `M.alloc`):

| Cells | Count | Share |
|---|---|---|
| Tup | 13,322,171 | 100.0 % |
| — field pairs of WCon (a bit's pair and the rest's pair) | 8,195,546 | 61.5 % |
| — first pairs of WCon (a word's cons cell) | 4,097,773 | 30.8 % |
| — pairs of other constructors (fields + first) | 752,166 | 5.6 % |
| — pairs of Con (list cells) | 276,669 | 2.1 % |
| frames, App, arguments, Prj | 308 | 0.0 % |

The bits themselves are shared (the image's True/False pairs), so each bit of a word costs 3 cells
(60 bytes). **Words are 92 % of the live memory**, lists 2 %.

Full run (no maximum), 4ebef88's machine: **a result in 798 s; peak memory 11,800 pages = 0.720 GiB**
(the memory never shrinks, so its final size is the peak); the whole census (compile.ts's JS run of the
compiler included) peaked at 3.8 GB of RSS, inside heavy.sh's 5 GB. At the end the
live cells are mostly the result itself: the module's 1,380,365 bytes as a list (Con pairs 10.8 %,
their words' WCon pairs 85.9 %), plus 611,893 copy roots and 611,887 argument cells left on the old
pend list (zombies of the old design, freed only on reuse).

The compiled compiler compiling each prog book of run.ts (same module, 4ebef88): 1,404–1,643 pages
(86–100 MiB) and 41–63 s each; the image alone (61,214 cells) is 1.2 MiB, so the rest is the
compiler's working set.

**AGENTS.md 3.10.3's "about 4.6 GB" is stale**: the self-compile needs 0.72 GiB today, well inside
WASM's 4 GiB, so 3.4.1.4 (self-hosting fits) holds as measured. (AGENTS.md is owned by w/laws; the
coordinator should fix 3.10.3's numbers.)

## 5. P6 decision

The rule (§5.2.3): P6 is not needed when the self-compile's peak after P1 is at most 3.5 GiB. The peak
is 0.72 GiB before P1 (and P1's must stay within 5 % of it: §6 below). **P6 is not needed.** Should
it ever be (a much larger compiler), the census favors word cells: words are 86–92 % of the live
cells in every snapshot, lists 2–11 %.

## 6. The census again after P1 (gate §3.4.5 / §5.3)

Same script on ec0f1a0 (the new machine; its own pruned book is 729,914 bytes, its module 1,261,019
bytes, its image 58,564 cells):

| Run | 4ebef88 machine | P1 machine | Change |
|---|---|---|---|
| self-compile: peak pages | 11,800 (0.720 GiB) | 10,797 (0.659 GiB) | −8.5 % |
| self-compile: time (JavaScriptCore) | 798 s | 216 s | 3.7× faster |
| prog books (11, same inputs): peak pages | 1,404–1,643 | 835–1,074 | −35 to −41 % |
| prog books: time | 41–63 s | 7–12 s | 5–6× faster |

The peak does not grow (the gate allows +5 %): it falls. At the end of the new self-compile, 1,170,945
cells are FREE (3.3 %, on the free list, reused before any new cell), and no zombie is left. The
census ran whole inside heavy.sh's 5 GB (max RSS 2.3 GB).
