// census.ts WORK [BOOK...]: a measurement (no pass or fail) of the memory of the compiled compiler
// (AGENTS.md 3.4.1.4, 3.10.3). It writes the pruned book of src/main.bend (main.book) and prints its
// size against the 2^26 bytes of Img.small, compiles it with compile.ts (main.wasm: the compiled
// compiler), and runs that module in bun's engine, as host.ts does, on the bytes of each BOOK
// (main.book when none is given: the self-compile). After each run it reads the module's memory and
// prints its pages and a census of the machine's own cells: by tag (Machine/impl.bend's T.* and
// K.*), and the pairs by shape (the constructor whose fields they hold).
//
// When the run ends out of memory, the machine had no free cell (M.alloc takes a new cell only when
// its free list is empty), so the census is the live cells at the run's peak. CAP=pages gives the
// module a memory maximum, so that a run stops at that size: then its census is the live cells
// when the memory first needs more than CAP pages. Speed is a priority in this file (AGENTS.md
// 2.5.1): the census reads up to 2^28 cells with mutating loops over typed arrays.
//
//   [CAP=pages] bun census.ts WORK [BOOK...]

// imports

import { mkdirSync, readFileSync, statSync } from "node:fs";
import { join, resolve } from "node:path";
import { getBend, getCompile, getLake, getLower, run } from "../../Shared/shared.ts";

// types

// what the module exports to its host (host.ts)
type Exports = {
  readonly memory: WebAssembly.Memory;
  readonly alloc: (size: number) => number;
  readonly run: (at: number, size: number) => number;
};

// constants

const HERE = import.meta.dir;
// Img.small: a book of this many bytes or more compiles to halt(1)
const SMALL = 2 ** 26;
const STATUS = ["result", "out_of_memory", "no_result"];
const PAGE = 65536;
// the tags of Machine/impl.bend (T.*, K.*)
const TAGS: Record<number, string> = {
  0: "Var",
  1: "Ref",
  2: "Ann",
  3: "Let",
  4: "Typ",
  5: "Min",
  6: "All",
  7: "Lam",
  8: "App",
  9: "Sig",
  10: "Tup",
  11: "Prj",
  12: "Enu",
  13: "Lab",
  14: "Mat",
  15: "Efq",
  16: "Eql",
  17: "Rfl",
  18: "Rwt",
  32: "frame app_arg",
  33: "frame app_val",
  34: "frame app_fun",
  35: "frame let_in",
  36: "frame tup_b",
  37: "frame tup_a",
  38: "frame rwt",
  39: "frame min_b",
  40: "frame min_a",
  41: "argument",
  44: "check",
  45: "root",
  46: "free",
};
// the names that the machine numbers first (Machine/impl.bend's N.*)
const NAMES = ["unit", "Nil", "Con", "WNil", "WCon", "True", "False", "Q0", "Q1", "Q2", "main"];
const TUP = 10;
const LAB = 13;
// the shape of a pair, by its constructor (the label of its first pair, NAMES or another, OTHER):
// SHAPE + its number is its first pair (the label in field 2); 2 SHAPE + its number, a pair of the
// chain of its fields (field 3 on from the first); 0, neither
const OTHER = NAMES.length;
const SHAPE = 16;

// functions

// the bytes of a LEB128 number
const getLeb = (n: number): number[] =>
  n < 128 ? [n] : [(n & 127) | 128, ...getLeb(Math.floor(n / 128))];

// the module with a memory maximum of cap pages: Cir.module's memory section (id 5) is one memory
// with no maximum
const getCapped = (wasm: Uint8Array, cap: number): Uint8Array => {
  const getMemory = (i: number): number => {
    const [size, len] = getLebAt(wasm, i + 1);
    return wasm[i] === 5 ? i : getMemory(i + 1 + len + size);
  };
  const at = getMemory(8);
  const [size, len] = getLebAt(wasm, at + 1);
  const [min] = getLebAt(wasm, at + 1 + len + 2);
  const body = [1, 1, ...getLeb(min), ...getLeb(cap)];
  return Uint8Array.from([
    ...wasm.subarray(0, at),
    5,
    ...getLeb(body.length),
    ...body,
    ...wasm.subarray(at + 1 + len + size),
  ]);
};

// the LEB128 number at i, and its length in bytes
const getLebAt = (bytes: Uint8Array, i: number): [number, number] => {
  const b = bytes[i] ?? 0;
  if (b < 128) return [b, 1];
  const [rest, len] = getLebAt(bytes, i + 1);
  return [(b & 127) + rest * 128, len + 1];
};

// the lines of a count, the largest first
const getLines = (counts: Map<string, number>, total: number): string[] =>
  [...counts]
    .toSorted(([, a], [, b]) => b - a)
    .map(([k, n]) => `  ${k}: ${n} (${((100 * n) / Math.max(total, 1)).toFixed(1)}%)`);

// the census of the cells from first to the last that is not all zeros
const getCensus = (memory: ArrayBuffer, first: number): string[] => {
  const f = new Uint32Array(memory);
  let end = Math.floor(f.length / 5);
  while (end > first && f[5 * end - 5] === 0 && f[5 * end - 4] === 0 && f[5 * end - 3] === 0) end -= 1;
  const used = Math.max(end - first, 0);
  const tag = (c: number) => (f[5 * c] ?? 0) & 63;
  const ctor = (c: number) => (tag(c) === LAB ? Math.min(f[5 * c + 2] ?? 0, OTHER) : -1);
  const shape = new Uint8Array(used);
  for (let c = first; c < end; c += 1) {
    const k = ctor(f[5 * c + 2] ?? 0);
    if (tag(c) !== TUP || k < 0 || shape[c - first] !== 0) continue;
    shape[c - first] = SHAPE + k;
    for (let x = f[5 * c + 3] ?? 0; x >= first && x < end && tag(x) === TUP; x = f[5 * x + 3] ?? 0) {
      if (shape[x - first]! >= 2 * SHAPE) break;
      shape[x - first] = 2 * SHAPE + k;
    }
  }
  const byTag = new Map<string, number>();
  const byShape = new Map<string, number>();
  const add = (m: Map<string, number>, k: string) => m.set(k, (m.get(k) ?? 0) + 1);
  for (let c = first; c < end; c += 1) {
    const t = tag(c);
    add(byTag, TAGS[t] ?? `tag ${t}`);
    const s = shape[c - first]!;
    const of = NAMES[s % SHAPE] ?? "another name";
    if (t === TUP) add(byShape, s === 0 ? "other" : `${s < 2 * SHAPE ? "first" : "field"} pair of ${of}`);
  }
  return [
    `own cells: ${used} (${((20 * used) / 2 ** 30).toFixed(3)} GiB), from cell ${first}`,
    "by tag:",
    ...getLines(byTag, used),
    "pairs by shape:",
    ...getLines(byShape, used),
  ];
};

// runs the module on the bytes of the book, and prints its outcome and census
const runCensus = async (wasm: Uint8Array, book: string): Promise<void> => {
  const data = readFileSync(book);
  const { instance } = await WebAssembly.instantiate(wasm, {});
  const { memory, alloc, run: runModule } = instance.exports as Exports;
  const at = alloc(data.length) >>> 0;
  if (at === 0xffffffff) return console.log(`${book}: no room for the input`);
  new Uint8Array(memory.buffer).set(data, at);
  const t0 = performance.now();
  const status = runModule(at, data.length) >>> 0;
  const seconds = ((performance.now() - t0) / 1000).toFixed(1);
  const pages = memory.buffer.byteLength / PAGE;
  console.log(
    [
      `${book} (${data.length} bytes): ${STATUS[status] ?? `status ${status}`} in ${seconds} s`,
      `pages: ${pages} (${((pages * PAGE) / 2 ** 30).toFixed(3)} GiB); image cells: ${at / 20 - 1}`,
      ...getCensus(memory.buffer, Math.ceil((at + data.length) / 20)),
    ].join("\n"),
  );
};

// side effects

const [workArg, ...books] = process.argv.slice(2);
if (workArg === undefined) {
  console.error(`usage: [CAP=pages] bun ${process.argv[1]} WORK [BOOK...]`);
  process.exit(1);
}
const work = resolve(workArg);
const at = (file: string) => join(work, file);
mkdirSync(work, { recursive: true });
run(getBend(join(HERE, "compile.bend"), at("compile.mjs")));
run(getLower(at("main.bendtt")));
run({
  ...getLake(["lean", "src/Book/scripts/Write.lean"], {
    BOOK: at("main.bendtt"),
    OUTPUT: at("main.book"),
  }),
  stdout: "ignore",
});
const size = statSync(at("main.book")).size;
console.log(
  `main.book: ${size} bytes, ${((100 * size) / SMALL).toFixed(1)}% of 2^26 (Img.small)`,
);
run(getCompile(at("compile.mjs"), at("main.book"), at("main.wasm")));
const module = readFileSync(at("main.wasm"));
const cap = process.env.CAP;
const wasm = cap === undefined ? module : getCapped(module, Number(cap));
console.log(`main.wasm: ${module.length} bytes${cap === undefined ? "" : `, memory at most ${cap} pages`}`);
for (const book of books.length === 0 ? [at("main.book")] : books) await runCensus(wasm, book);
