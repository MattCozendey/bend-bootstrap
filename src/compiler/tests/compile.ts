// Runs Compiler.compile on the bytes of a book with the JS that `bend -o` writes for compile.bend:
// a fast run of our compiler, for the tests, by a runtime that we do not trust (run.ts checks it
// against the Lean interpreter when TRUSTED is set). That JS recurses on lists, so run.ts runs this
// file with a large stack. Speed is a priority in this file (AGENTS.md 2.5.1): it reads the
// compiler's output with a mutating loop, because the ways without mutation are quadratic.
//
//   bun compile.ts <compile.mjs of bend -o> <book> <module.wasm>

// imports

import { readFileSync, writeFileSync } from "node:fs";
import { pathToFileURL } from "node:url";
import { getArgs } from "../../shared/shared.ts";

// types

// the list of bytes of AGENTS.md 3.3.1
type List<T> =
  | { readonly $: "Nil" }
  | { readonly $: "Con"; readonly head: T; readonly tail: List<T> };
type Word = { readonly $: "WNil" } | { readonly $: "WCon"; readonly head: boolean; readonly tail: Word };

// functions

const getWord = (b: number, n: number): Word =>
  n === 0 ? { $: "WNil" } : { $: "WCon", head: (b & 1) === 1, tail: getWord(b >> 1, n - 1) };

const getByte = (w: Word): number => (w.$ === "WNil" ? 0 : (w.head ? 1 : 0) | (getByte(w.tail) << 1));

// side effects

const [js, book, out] = getArgs("<compile.mjs of bend -o>", "<book>", "<module.wasm>");
const { default: compiled } = await import(pathToFileURL(js).href);
const bytes = Array.from(readFileSync(book)).reduceRight<List<Word>>(
  (tail, b) => ({ $: "Con", head: getWord(b, 8), tail }),
  { $: "Nil" },
);
const wasm: number[] = [];
for (let r: List<Word> = compiled.main(bytes); r.$ === "Con"; r = r.tail) wasm.push(getByte(r.head));
writeFileSync(out, Uint8Array.from(wasm));
