// differential.ts WORK: a test of kind b (bend2 skill) of the Bend version of WASM (the section
// Wasm of src/Wasm/impl.bend) against a source that we do not own: the spec's reference
// interpreter at the commit that the tests pin (spec.ts, AGENTS.md 3.9.1.3.2). Each seed makes a
// module inside the subset (AGENTS.md 3.9.1.2): of the instructions and module parts that the
// compiler emits, in their general forms (each block type, branches with values at each depth,
// any number of results, memory 0 named or not, LEB128 numbers in their fewest bytes or padded),
// but none of the narrowings; most of them valid, with loops that end, and some made invalid or
// cut short. oracle.ml gives what the reference interpreter gives for the module and for calls of
// its exports, which become the assertions of a binary script; WasmTests.lean runs the model on
// them as on the official tests. An assertion that fails, is unsupported or runs out of fuel is a
// mismatch: the script prints the module's bytes in hex and the calls, and stops with 1. The
// reference interpreter makes each memory in full, so a module's memory stays within a few pages:
// a grow is by a few pages, or by one that must fail. It runs with the spec and the tools that
// spec.ts pins; WORK is a folder for what it writes. SEEDS=n runs n seeds, not SEEDS.
//
//   opam exec --switch=wasm-spec -- bun src/Wasm/tests/differential.ts WORK

// imports

import { mkdirSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { join, resolve } from "node:path";
import { getArgs, getBend, getLake, REPO, run } from "../../Shared/shared.ts";
import { getSpec } from "./spec.ts";

// types

// a block's type: its numbers of parameters and results, and how the module writes it (0x40, the
// value type i32, or the index of a type)
type BlockType = { readonly params: number; readonly results: number; readonly index: boolean };

type Instr =
  | { readonly op: "const"; readonly value: number }
  | { readonly op: "local.get" | "local.set" | "local.tee"; readonly index: number }
  | { readonly op: "plain"; readonly code: number }
  | {
      readonly op: "i32.load" | "i32.load8_u" | "i32.store" | "i32.store8";
      readonly align: number;
      readonly offset: number;
    }
  | { readonly op: "memory.size" | "memory.grow" }
  | { readonly op: "block" | "loop"; readonly type: BlockType; readonly body: readonly Instr[] }
  | { readonly op: "br" | "br_if"; readonly depth: number };

type Func = {
  readonly params: number;
  readonly results: number;
  readonly locals: number;
  readonly body: readonly Instr[];
};

type Module = {
  readonly funcs: readonly Func[];
  readonly memory: number | undefined;
  readonly data:
    | { readonly flag: 0 | 2; readonly offset: number; readonly bytes: string }
    | undefined;
  readonly exports: readonly { readonly name: string; readonly func: number | undefined }[];
  // the index of a block type that is out of range, for a module made invalid by it
  readonly extraTypes: number;
};

// a label of the code around an instruction: the values that a branch to it takes, and whether it
// is a loop's (only its own count goes back to it, so that each loop ends)
type Label = { readonly arity: number; readonly loop: boolean };

// what code is generated in: the locals (all of them, those that it may set, and the counters of
// loops, the innermost loop's first), the labels (innermost first), whether there is a memory, and
// how much code is left to make
type Ctx = {
  readonly locals: number;
  readonly free: readonly number[];
  readonly counters: readonly number[];
  readonly labels: readonly Label[];
  readonly memory: boolean;
  readonly size: number;
};

// a seed's module, its bytes, and the calls of its exports, with their arguments
type Case = {
  readonly seed: number;
  readonly bytes: readonly number[];
  readonly calls: readonly { readonly name: string; readonly args: readonly number[] }[];
};

// constants

// about 10 minutes here (0.25 s a seed)
const SEEDS = 2300;
// i32 values at the edges: of each width of a signed LEB128, of a sign, of a shift's count
const VALUES = [
  0, 1, 2, 3, 7, 31, 32, 33, 63, 64, 65, 127, 128, 255, 256, 8191, 8192, 65535, 65536, 0xfffff,
  0x100000, 0x7ffffff, 0x8000000, 0x7fffffff, 0x80000000, 0x80000001, 0xffffffc0, 0xffffffbf,
  0xfffffffe, 0xffffffff, 0xfffe0000, 0xc0000000,
];
// addresses: in the first page, at its end, and near 2^32
const ADDRESSES = [
  0, 1, 3, 4, 5, 16, 20, 21, 100, 255, 256, 1000, 65532, 65533, 65535, 65536, 131068, 0x7ffffffc,
  0xfffffffc, 0xffffffff,
];
const OFFSETS = [0, 0, 0, 1, 2, 3, 4, 8, 20, 255, 256, 65535, 65536, 0xfffffffc];
// grows by a few pages, and by more than 2^16 pages, which must fail
const DELTAS = [0, 0, 1, 1, 2, 65537, 0x80000000, 0xffffffff];
// the opcodes of the binary operators and comparisons that the compiler emits, and eqz
const BINARY = [0x6a, 0x6b, 0x71, 0x72, 0x74, 0x76, 0x46, 0x47, 0x49, 0x4b, 0x4d, 0x4f];
const EQZ = 0x45;
const SUB = 0x6b;
// the opcodes of the instructions with immediates (spec 5.4)
const OPCODES = {
  "local.get": 0x20,
  "local.set": 0x21,
  "local.tee": 0x22,
  "i32.load": 0x28,
  "i32.load8_u": 0x2d,
  "i32.store": 0x36,
  "i32.store8": 0x3a,
  "memory.size": 0x3f,
  "memory.grow": 0x40,
  block: 0x02,
  loop: 0x03,
  br: 0x0c,
  br_if: 0x0d,
} as const;
const HEADER = [0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00];
// how long the reference interpreter may take for all the modules
const ORACLE_MS = 600_000;
const HERE = import.meta.dir;

// functions

// a number in [0, n) that the key picks: the same key always picks the same (FNV-1a of the key)
const getPick = (key: string, n: number): number =>
  [...key].reduce((h, c) => Math.imul(h ^ c.charCodeAt(0), 16777619) >>> 0, 2166136261) % n;

const getOne = <T>(key: string, xs: readonly T[]): T => xs[getPick(key, xs.length)] as T;

const getRange = (n: number): readonly number[] => Array.from({ length: n }, (_, i) => i);

// the context of the code inside a new label, with less code left to make
const getInner = (ctx: Ctx, label: Label, size: number): Ctx => ({
  ...ctx,
  labels: [label, ...ctx.labels],
  size,
});

// n values, each of its own key
const getValues = (key: string, ctx: Ctx, n: number): readonly Instr[] =>
  getRange(n).flatMap((i) => getValue(`${key}.${i}`, { ...ctx, size: ctx.size / Math.max(n, 1) }));

// code that takes n values: each into a local
const getTaken = (key: string, ctx: Ctx, n: number): readonly Instr[] =>
  getRange(n).map((i) => ({ op: "local.set", index: getOne(`${key}.${i}`, ctx.free) }));

// code that leaves n values in place of 1: a value, then each other one joined by an operator
const getJoined = (key: string, ctx: Ctx, n: number): readonly Instr[] =>
  n === 0
    ? getValue(key, ctx)
    : getRange(n - 1).map((i) => ({ op: "plain", code: getOne(`${key}.${i}`, BINARY) }));

// the depth of a label that a branch may go to, not a loop's, and the values that it takes
const getTarget = (key: string, ctx: Ctx): [number, number] => {
  const depth = getOne(
    key,
    getRange(ctx.labels.length).filter((d) => !ctx.labels[d]?.loop),
  );
  return [depth, ctx.labels[depth]?.arity ?? 0];
};

// a memory access's alignment, at most its width's, and its offset
const getMemarg = (key: string, wide: boolean) => ({
  align: wide ? getPick(`${key}a`, 3) : 0,
  offset: getOne(`${key}o`, OFFSETS),
});

// an address: a constant, or one that code computes
const getAddress = (key: string, ctx: Ctx): readonly Instr[] =>
  getPick(`${key}k`, 4) === 0
    ? getValue(`${key}v`, ctx)
    : [{ op: "const", value: getOne(`${key}c`, ADDRESSES) }];

// a block's type of these numbers: 0x40 or i32 when it can be, else (and sometimes anyway) a type
const getBlockType = (key: string, params: number, results: number): BlockType => ({
  params,
  results,
  index: params > 0 || results > 1 || getPick(key, 3) === 0,
});

// the code that ends a block of n results: its values, or a branch with the values of its label
const getEnd = (key: string, ctx: Ctx, n: number): readonly Instr[] => {
  if (getPick(`${key}b`, 4) !== 0) return getValues(`${key}v`, ctx, n);
  const [depth, arity] = getTarget(`${key}d`, ctx);
  return [...getValues(`${key}r`, ctx, arity), { op: "br", depth }];
};

// a block's body, which leaves n values: some code of no values, then its end
const getBody = (key: string, ctx: Ctx, n: number): readonly Instr[] => [
  ...getRange(getPick(`${key}n`, 3)).flatMap((i) =>
    getEffect(`${key}.${i}`, { ...ctx, size: ctx.size / 3 }),
  ),
  ...getEnd(`${key}e`, ctx, n),
];

// a block of p parameters and r results, after its parameters
const getBlock = (key: string, ctx: Ctx, p: number, r: number): readonly Instr[] => {
  const inner = getInner(ctx, { arity: r, loop: false }, ctx.size - 1);
  return [
    ...getValues(`${key}p`, ctx, p),
    {
      op: "block",
      type: getBlockType(`${key}t`, p, r),
      body: [...getTaken(`${key}k`, ctx, p), ...getBody(`${key}b`, inner, r)],
    },
  ];
};

// a loop of p parameters and r results, after its parameters and the start of its counter (which
// the code of its parameters may use too), which it takes 1 from on each round, and goes round
// again while it is not 0: so it runs a few rounds
const getLoop = (key: string, ctx: Ctx, p: number, r: number): readonly Instr[] => {
  const [counter, ...counters] = ctx.counters;
  if (counter === undefined) return getBlock(key, ctx, p, r);
  const inner = { ...getInner(ctx, { arity: p, loop: true }, ctx.size - 1), counters };
  return [
    ...getValues(`${key}p`, ctx, p),
    { op: "const", value: 1 + getPick(`${key}c`, 3) },
    { op: "local.set", index: counter },
    {
      op: "loop",
      type: getBlockType(`${key}t`, p, r),
      body: [
        ...getTaken(`${key}k`, inner, p),
        ...getRange(getPick(`${key}n`, 3)).flatMap((i) => getEffect(`${key}.${i}`, inner)),
        ...getValues(`${key}q`, inner, p),
        { op: "local.get", index: counter },
        { op: "const", value: 1 },
        { op: "plain", code: SUB },
        { op: "local.tee", index: counter },
        { op: "br_if", depth: 0 },
        ...getTaken(`${key}l`, inner, p),
        ...getEnd(`${key}e`, inner, r),
      ],
    },
  ];
};

// code that leaves one value
const getValue = (key: string, ctx: Ctx): readonly Instr[] => {
  const sub = { ...ctx, size: ctx.size - 1 };
  const kinds = [
    "const",
    "const",
    "get",
    ...(ctx.size < 1 ? [] : ["binary", "binary", "eqz", "tee", "block", "loop"]),
    ...(ctx.size < 1 || !ctx.memory ? [] : ["load", "load", "size", "grow"]),
  ];
  switch (getOne(`${key}:`, kinds)) {
    case "get":
      return [{ op: "local.get", index: getPick(`${key}g`, ctx.locals) }];
    case "binary":
      return [
        ...getValue(`${key}a`, { ...ctx, size: sub.size / 2 }),
        ...getValue(`${key}b`, { ...ctx, size: sub.size / 2 }),
        { op: "plain", code: getOne(`${key}o`, BINARY) },
      ];
    case "eqz":
      return [...getValue(`${key}a`, sub), { op: "plain", code: EQZ }];
    case "tee":
      return [...getValue(`${key}a`, sub), { op: "local.tee", index: getOne(`${key}x`, ctx.free) }];
    case "load": {
      const wide = getPick(`${key}w`, 2) === 0;
      return [
        ...getAddress(`${key}a`, sub),
        { op: wide ? "i32.load" : "i32.load8_u", ...getMemarg(`${key}m`, wide) },
      ];
    }
    case "size":
      return [{ op: "memory.size" }];
    case "grow":
      return [{ op: "const", value: getOne(`${key}d`, DELTAS) }, { op: "memory.grow" }];
    case "block": {
      const [p, r] = [getPick(`${key}p`, 3), getPick(`${key}r`, 4)];
      return [...getBlock(`${key}k`, sub, p, r), ...getJoined(`${key}j`, sub, r)];
    }
    case "loop": {
      const [p, r] = [getPick(`${key}p`, 3), getPick(`${key}r`, 3)];
      return [...getLoop(`${key}k`, sub, p, r), ...getJoined(`${key}j`, sub, r)];
    }
    default:
      return [{ op: "const", value: getOne(`${key}c`, VALUES) }];
  }
};

// code that leaves no value
const getEffect = (key: string, ctx: Ctx): readonly Instr[] => {
  const sub = { ...ctx, size: ctx.size - 1 };
  const kinds = [
    "set",
    "set",
    ...(ctx.size < 1 ? [] : ["br_if", "br_if", "block", "loop"]),
    ...(ctx.memory ? ["store", "store", "grow"] : []),
  ];
  switch (getOne(`${key}:`, kinds)) {
    case "br_if": {
      const [depth, arity] = getTarget(`${key}d`, ctx);
      return [
        ...getValues(`${key}v`, sub, arity),
        ...getValue(`${key}c`, sub),
        { op: "br_if", depth },
        ...getTaken(`${key}k`, ctx, arity),
      ];
    }
    case "block":
      return getBlock(`${key}k`, sub, getPick(`${key}p`, 3), 0);
    case "loop":
      return getLoop(`${key}k`, sub, getPick(`${key}p`, 3), 0);
    case "store": {
      const wide = getPick(`${key}w`, 2) === 0;
      return [
        ...getAddress(`${key}a`, sub),
        ...getValue(`${key}v`, sub),
        { op: wide ? "i32.store" : "i32.store8", ...getMemarg(`${key}m`, wide) },
      ];
    }
    case "grow":
      return [
        { op: "const", value: getOne(`${key}d`, DELTAS) },
        { op: "memory.grow" },
        { op: "local.set", index: getOne(`${key}x`, ctx.free) },
      ];
    default:
      return [...getValue(`${key}a`, sub), { op: "local.set", index: getOne(`${key}x`, ctx.free) }];
  }
};

// a function: its parameters, its results, its locals (some for code, then 2 counters of loops)
const getFunc = (key: string, memory: boolean): Func => {
  const params = getPick(`${key}p`, 4);
  const results = getPick(`${key}r`, 5);
  const free = params + 1 + getPick(`${key}l`, 2);
  const ctx: Ctx = {
    locals: free + 2,
    free: getRange(free),
    counters: [free, free + 1],
    labels: [{ arity: results, loop: false }],
    memory,
    size: 6 + getPick(`${key}s`, 20),
  };
  return { params, results, locals: free + 2 - params, body: getBody(`${key}b`, ctx, results) };
};

// the instructions of a body with the one at position at (before each other, depth first) changed
// by change, and how many it holds
const getChanged = (
  body: readonly Instr[],
  at: number,
  change: (i: Instr) => readonly Instr[],
): [readonly Instr[], number] =>
  body.reduce<[readonly Instr[], number]>(
    ([done, n], instr) => {
      if (n === at) return [[...done, ...change(instr)], n + 1];
      if (instr.op !== "block" && instr.op !== "loop") return [[...done, instr], n + 1];
      const [inner, m] = getChanged(instr.body, at - n - 1, change);
      return [[...done, { ...instr, body: inner }], n + 1 + m];
    },
    [[], 0],
  );

// a module made invalid in one way: an instruction gone, a value too many, a local, a label or a
// type that is not there, an alignment past the width, no memory, two exports of one name, or one
// result too many
const getInvalid = (key: string, m: Module): Module => {
  const f = getPick(`${key}f`, m.funcs.length);
  const func = m.funcs[f] as Func;
  const [, size] = getChanged(func.body, -1, (i) => [i]);
  const at = getPick(`${key}a`, Math.max(size, 1));
  const withBody = (change: (i: Instr) => readonly Instr[]): Module => ({
    ...m,
    funcs: m.funcs.map((g, i) => (i === f ? { ...g, body: getChanged(g.body, at, change)[0] } : g)),
  });
  switch (getPick(`${key}k`, 9)) {
    case 0:
      return withBody(() => []);
    case 1:
      return {
        ...m,
        funcs: m.funcs.map((g, i) =>
          i === f ? { ...g, body: [{ op: "const", value: 0 }, ...g.body] } : g,
        ),
      };
    case 2:
      return withBody((i) => [i.op.startsWith("local") ? ({ ...i, index: 64 } as Instr) : i]);
    case 3:
      return withBody((i) => [
        i.op === "br" || i.op === "br_if" ? ({ ...i, depth: 64 } as Instr) : i,
      ]);
    case 4:
      return { ...m, extraTypes: 1 };
    case 5:
      return withBody((i) =>
        ["i32.load", "i32.store", "i32.load8_u", "i32.store8"].includes(i.op)
          ? [{ ...i, align: 3 } as Instr]
          : [i],
      );
    case 6:
      return { ...m, memory: undefined };
    case 7:
      return { ...m, exports: [...m.exports, ...m.exports.slice(0, 1)] };
    default:
      return {
        ...m,
        funcs: m.funcs.map((g, i) => (i === f ? { ...g, results: g.results + 1 } : g)),
      };
  }
};

// a seed's module, and whether it was made invalid (it may stay valid, but then its loops may not
// end: no call runs it)
const getModule = (seed: number): [Module, boolean] => {
  const key = `${seed}`;
  const memory = getPick(`${key}m`, 5) === 0 ? undefined : getPick(`${key}min`, 3);
  const funcs = getRange(1 + getPick(`${key}n`, 3)).map((i) =>
    getFunc(`${key}f${i}`, memory !== undefined),
  );
  const bytes = getRange(getPick(`${key}dl`, 9))
    .map((i) => String.fromCharCode(32 + getPick(`${key}d${i}`, 90)))
    .join("");
  const offset =
    getPick(`${key}do`, 4) === 0
      ? 65536 * (memory ?? 0) - getPick(`${key}dd`, 4)
      : getPick(`${key}dp`, 64);
  const data =
    memory !== undefined && getPick(`${key}d`, 2) === 0
      ? { flag: getPick(`${key}df`, 2) === 0 ? (0 as const) : (2 as const), offset, bytes }
      : undefined;
  const exports = [
    ...funcs.map((_, i) => ({ name: `f${i}`, func: i })),
    ...(memory !== undefined && getPick(`${key}me`, 2) === 0
      ? [{ name: "memory", func: undefined }]
      : []),
  ];
  const m: Module = { funcs, memory, data, exports, extraTypes: 0 };
  return getPick(`${key}i`, 7) === 0 ? [getInvalid(`${key}i`, m), true] : [m, false];
};

// an LEB128 number of the value, in its fewest bytes or more, as the key picks; signed, for a
// two's complement value of 32 bits; at most 5 bytes
const getLeb = (key: string, value: number, signed = false): readonly number[] => {
  const v = signed && value >= 0x80000000 ? value - 0x100000000 : value;
  const digits = (n: number, w: number): readonly number[] =>
    getRange(w).map((i) => ((Math.floor(n / 128 ** i) % 128) + 128) % 128 | (i < w - 1 ? 128 : 0));
  const fits = (w: number) =>
    signed ? v >= -(2 ** (7 * w - 1)) && v < 2 ** (7 * w - 1) : v < 2 ** (7 * w);
  const least = [1, 2, 3, 4, 5].find(fits) ?? 5;
  const width = getPick(`${key}w`, 8) === 0 ? least + getPick(`${key}x`, 6 - least) : least;
  return digits(v, width);
};

// bytes after their number
const getSized = (key: string, bs: readonly number[]): readonly number[] => [
  ...getLeb(key, bs.length),
  ...bs,
];

const getVec = (key: string, items: readonly (readonly number[])[]): readonly number[] => [
  ...getLeb(key, items.length),
  ...items.flat(),
];

// the bytes of instructions; types gives the index of a block's type
const getCode = (
  key: string,
  xs: readonly Instr[],
  types: (t: BlockType) => number,
): readonly number[] =>
  xs.flatMap((x, i): readonly number[] => {
    const k = `${key}.${i}`;
    switch (x.op) {
      case "const":
        return [0x41, ...getLeb(k, x.value, true)];
      case "plain":
        return [x.code];
      case "local.get":
      case "local.set":
      case "local.tee":
        return [OPCODES[x.op], ...getLeb(k, x.index)];
      case "i32.load":
      case "i32.load8_u":
      case "i32.store":
      case "i32.store8": {
        const named = getPick(`${k}n`, 8) === 0;
        return [
          OPCODES[x.op],
          ...getLeb(`${k}a`, x.align + (named ? 64 : 0)),
          ...(named ? getLeb(`${k}m`, 0) : []),
          ...getLeb(`${k}o`, x.offset),
        ];
      }
      case "memory.size":
      case "memory.grow":
        return [OPCODES[x.op], ...getLeb(k, 0)];
      case "br":
      case "br_if":
        return [OPCODES[x.op], ...getLeb(k, x.depth)];
      default: {
        const t = x.type;
        const bt = t.index ? getLeb(k, types(t), true) : t.results === 0 ? [0x40] : [0x7f];
        return [OPCODES[x.op], ...bt, ...getCode(k, x.body, types), 0x0b];
      }
    }
  });

// the block types of instructions
const getBlockTypes = (xs: readonly Instr[]): readonly BlockType[] =>
  xs.flatMap((x) =>
    x.op === "block" || x.op === "loop" ? [x.type, ...getBlockTypes(x.body)] : [],
  );

// a module's bytes, in the order of the compiler's sections: a type for each function, then those
// of blocks
const getBytes = (key: string, m: Module): readonly number[] => {
  const blocks = m.funcs.flatMap((f) => getBlockTypes(f.body)).filter((t) => t.index);
  const shapes = [
    ...m.funcs.map((f) => [f.params, f.results]),
    ...blocks.map((t) => [t.params, t.results]),
  ];
  const types = (t: BlockType) => m.funcs.length + m.extraTypes * shapes.length + blocks.indexOf(t);
  const type = ([p = 0, r = 0]: readonly number[], i: number) => [
    0x60,
    ...getSized(`${key}tp${i}`, Array(p).fill(0x7f)),
    ...getSized(`${key}tr${i}`, Array(r).fill(0x7f)),
  ];
  const section = (id: number, content: readonly number[]) => [
    id,
    ...getSized(`${key}s${id}`, content),
  ];
  const memory =
    m.memory === undefined
      ? []
      : section(5, [...getLeb(`${key}mn`, 1), 0, ...getLeb(`${key}min`, m.memory)]);
  const data =
    m.data === undefined
      ? []
      : section(11, [
          ...getLeb(`${key}dn`, 1),
          ...getLeb(`${key}df`, m.data.flag),
          ...(m.data.flag === 2 ? getLeb(`${key}dm`, 0) : []),
          0x41,
          ...getLeb(`${key}do`, m.data.offset, true),
          0x0b,
          ...getSized(
            `${key}dl`,
            [...m.data.bytes].map((c) => c.charCodeAt(0)),
          ),
        ]);
  return [
    ...HEADER,
    ...section(1, getVec(`${key}t`, shapes.map(type))),
    ...section(
      3,
      getVec(
        `${key}f`,
        m.funcs.map((_, i) => getLeb(`${key}fi${i}`, i)),
      ),
    ),
    ...memory,
    ...section(
      7,
      getVec(
        `${key}e`,
        m.exports.map((e, i) => [
          ...getSized(
            `${key}en${i}`,
            [...e.name].map((c) => c.charCodeAt(0)),
          ),
          ...(e.func === undefined
            ? [2, ...getLeb(`${key}em${i}`, 0)]
            : [0, ...getLeb(`${key}ei${i}`, e.func)]),
        ]),
      ),
    ),
    ...section(
      10,
      getVec(
        `${key}c`,
        m.funcs.map((f, i) =>
          getSized(`${key}cs${i}`, [
            ...(f.locals === 0
              ? getLeb(`${key}cg${i}`, 0)
              : [...getLeb(`${key}cg${i}`, 1), ...getLeb(`${key}cl${i}`, f.locals), 0x7f]),
            ...getCode(`${key}x${i}`, f.body, types),
            0x0b,
          ]),
        ),
      ),
    ),
    ...data,
  ];
};

// a seed's case: its module's bytes, some cut short, and two calls of each function that it
// exports, unless it was made invalid or cut short
const getCase = (seed: number): Case => {
  const [m, invalid] = getModule(seed);
  const full = getBytes(`${seed}b`, m);
  const cut = getPick(`${seed}t`, 30) === 0;
  const bytes = cut ? full.slice(0, 8 + getPick(`${seed}tl`, full.length - 8)) : full;
  const calls = m.exports.flatMap(({ name, func }) => {
    const params = func === undefined || invalid || cut ? undefined : m.funcs[func]?.params;
    return params === undefined
      ? []
      : getRange(2).map((j) => ({
          name,
          args: getRange(params).map((a) => getOne(`${seed}${name}${j}.${a}`, VALUES)),
        }));
  });
  return { seed, bytes, calls };
};

// a module of the text format of a script, of the bytes
const getModuleText = (bs: readonly number[]): string =>
  `(module binary "${bs.map((b) => `\\${b.toString(16).padStart(2, "0")}`).join("")}")`;

const getInvoke = (call: Case["calls"][number]): string =>
  `(invoke "${call.name}"${call.args.map((a) => ` (i32.const 0x${a.toString(16)})`).join("")})`;

// the binary script of a case, whose assertions are what the reference interpreter gives (its lines
// of oracle.ml): a module that it finds valid is defined and instantiated, or traps; a call gives
// its values, or traps. Anything else is no answer of the reference interpreter's, and no script
const getScript = (c: Case, said: readonly string[]): string | undefined => {
  const [module = "", instance = "", ...results] = said;
  const text = getModuleText(c.bytes);
  if (module === "invalid" || module === "malformed") return `(assert_${module} ${text} "")\n`;
  const defined = `(module definition binary "${text.slice('(module binary "'.length)}\n`;
  if (module !== "valid") return undefined;
  if (instance === "trap") return `${defined}(assert_trap (module instance) "")\n`;
  const asserts = c.calls.map((call, i) => {
    const [kind = "", ...values] = (results[i] ?? "").split(" ");
    if (kind === "trap") return `(assert_trap ${getInvoke(call)} "")\n`;
    return kind === "values"
      ? `(assert_return ${getInvoke(call)}${values.map((v) => ` (i32.const 0x${v})`).join("")})\n`
      : undefined;
  });
  return instance !== "instance" || asserts.includes(undefined)
    ? undefined
    : [`${defined}(module instance)\n`, ...asserts].join("");
};

// side effects

const [workArg] = getArgs("WORK");
const work = resolve(workArg);
const at = (file: string) => join(work, file);
const spec = getSpec(work);
run(getBend(join(REPO, "src/Wasm/impl.bend"), at("wasm.bendtt")));

const cases = getRange(Number(process.env.SEEDS ?? SEEDS)).map(getCase);
rmSync(at("gen"), { recursive: true, force: true });
rmSync(at("bin"), { recursive: true, force: true });
mkdirSync(at("gen"));
mkdirSync(at("bin"));
cases.forEach((c) =>
  writeFileSync(
    at(`gen/s${c.seed}.wast`),
    [getModuleText(c.bytes), ...c.calls.map(getInvoke)].join("\n"),
  ),
);
const oracle = Bun.spawnSync([spec.oracle], {
  stdin: Buffer.from(cases.map((c) => `${at(`gen/s${c.seed}.wast`)}\n`).join("")),
  timeout: ORACLE_MS,
});
if (!oracle.success) {
  console.error(`oracle.exe failed (a module that does not end?): ${oracle.stderr.toString()}`);
  process.exit(1);
}
const said = oracle.stdout
  .toString()
  .split("script ")
  .slice(1)
  .map((part) => part.trim().split("\n").slice(1));
const unanswered = cases.filter((c, i) => {
  const script = getScript(c, said[i] ?? []);
  if (script === undefined) {
    console.log(
      `NO ANSWER seed ${c.seed}: the reference interpreter said [${said[i]?.join(", ")}]`,
    );
    return true;
  }
  writeFileSync(at(`bin/s${c.seed}.bin.wast`), script);
  writeFileSync(at(`bin/s${c.seed}.facts`), "");
  return false;
});
run(
  getLake(["lean", "src/Wasm/scripts/WasmTests.lean"], {
    BOOK: at("wasm.bendtt"),
    TESTS: at("bin"),
    OUT: at("wasm.log"),
  }),
);

// the report's line of each script, and the lines under it (its failures and causes)
const report = readFileSync(at("wasm.log"), "utf8").split("\n");
const mismatches = cases
  .filter((c) => !unanswered.includes(c))
  .filter((c) => {
    const line = report.findIndex((l) => l.startsWith(`${at(`bin/s${c.seed}.bin.wast`)}: `));
    const counts = report[line]?.match(
      /: \d+ passed, (\d+) failed, (\d+) unsupported, (\d+) not done/,
    );
    if (counts?.slice(1).every((n) => n === "0")) return false;
    const after = report.slice(line + 1);
    const end = after.findIndex((l) => !l.startsWith("  "));
    console.log(`MISMATCH seed ${c.seed}: ${report[line] ?? "no report"}`);
    console.log(`  module ${c.bytes.map((b) => b.toString(16).padStart(2, "0")).join("")}`);
    c.calls.forEach((call) => console.log(`  call ${getInvoke(call)}`));
    after
      .slice(0, end === -1 ? after.length : end)
      .filter((l) => !l.includes(" commands, "))
      .forEach((l) => console.log(l));
    return true;
  });
const verdicts = said.map((s) => s[0] ?? "?");
console.log(
  `${cases.length} modules (${verdicts.filter((v) => v === "valid").length} valid, ` +
    `${verdicts.filter((v) => v === "invalid").length} invalid, ` +
    `${verdicts.filter((v) => v === "malformed").length} malformed), ` +
    `${cases.reduce((n, c) => n + c.calls.length, 0)} calls; ${mismatches.length} mismatches`,
);
process.exit(mismatches.length + unanswered.length === 0 ? 0 : 1);
