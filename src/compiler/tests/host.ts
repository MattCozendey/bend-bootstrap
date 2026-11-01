// The host of Wasm.run (src/wasm/impl.bend, Host) in bun's engine, JavaScriptCore: runs a compiled
// module on the bytes of a file, and writes the bytes of its result to a file.
//
//   bun host.ts <module.wasm> <input> <output>
//
// Prints result, out_of_memory or no_result, and exits with 0 on a result.

// imports

import { readFileSync, writeFileSync } from "node:fs";
import { getArgs } from "../../shared/shared.ts";

// types

// what the module exports to its host
type Exports = {
  readonly memory: WebAssembly.Memory;
  readonly alloc: (size: number) => number;
  readonly run: (at: number, size: number) => number;
};

// constants

// what alloc gives when the input does not fit
const NO_ROOM = 0xffffffff;
// what each status of run says
const SAYS = ["result", "out_of_memory", "no_result"];

// side effects

const [wasm, input, output] = getArgs("<module.wasm>", "<input>", "<output>");
const data = readFileSync(input);
const { instance } = await WebAssembly.instantiate(readFileSync(wasm), {});
const { memory, alloc, run } = instance.exports as Exports;
const at = alloc(data.length) >>> 0;
if (at === NO_ROOM) {
  console.log("out_of_memory");
  process.exit(1);
}
new Uint8Array(memory.buffer).set(data, at);
const status = run(at, data.length) >>> 0;
if (status === 0) {
  const view = new DataView(memory.buffer);
  writeFileSync(
    output,
    new Uint8Array(memory.buffer, view.getUint32(0, true), view.getUint32(4, true)),
  );
}
console.log(SAYS[status] ?? `status ${status}`);
process.exit(status === 0 ? 0 : 1);
