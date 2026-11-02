// convert.ts WORK: the binary scripts of the official WebAssembly tests that the Bend version of
// WASM is tested with (AGENTS.md 3.9.1.3), made by cut.ml, which reads each test script with the
// spec's own reference interpreter, keeps in each module that a command defines in the text format
// only its functions and exports inside the subset, and writes the script as wasm -d x.wast -o
// x.bin.wast does, with what it finds of each module in x.facts. It runs with the spec and the tools
// that spec.ts pins. WORK is a folder for the spec's clone and the build. The license, the tests
// (wast/), and their binary scripts and facts (bin/) go next to this script, with the same bytes on
// every system. Our own tests (own/, AGENTS.md 3.9.1.3) become binary scripts there too, as
// own-x.bin.wast, once the spec's reference interpreter passes them; each module of agree.ts,
// host/x.wat, becomes host/x.wasm.
//
//   opam exec --switch=wasm-spec -- bun convert.ts WORK

// imports

import { mkdirSync, rmSync } from "node:fs";
import { join, resolve } from "node:path";
import { getArgs, run } from "../../Shared/shared.ts";
import { COMMIT, getExe, getSpec } from "./spec.ts";

// constants

const TESTS = [
  "binary", "binary-leb128", "int_literals", "i32", "int_exprs", "address", "align", "endianness",
  "load", "store", "memory", "memory_grow", "memory_size", "memory_trap", "data", "block", "loop",
  "br", "br_if", "br_table", "labels", "local_get", "local_set", "local_tee", "func", "func_ptrs",
  "exports", "names", "unreached-invalid",
];
const OWN = ["stores", "loads", "branches", "invalid", "results", "encodings"];
const HOST = ["cases", "init", "nomemory"];
const HERE = import.meta.dir;

// functions

// cut.exe's binary script and facts of the test script wast, as bin/name.bin.wast and
// bin/name.facts
const writeBinary = (cutExe: string, wast: string, name: string): void =>
  run({
    cmd: [cutExe, wast, join(HERE, "bin", `${name}.facts`)],
    stdout: Bun.file(join(HERE, "bin", `${name}.bin.wast`)),
  });

// side effects

const [workArg] = getArgs("WORK");
const spec = getSpec(resolve(workArg));
const git = getExe("git");

// each file of the spec as git holds it, whatever the system's line endings
rmSync(join(HERE, "wast"), { recursive: true, force: true });
rmSync(join(HERE, "bin"), { recursive: true, force: true });
mkdirSync(join(HERE, "wast"));
mkdirSync(join(HERE, "bin"));
run({
  cmd: [git, "-C", spec.clone, "cat-file", "blob", `${COMMIT}:test/LICENSE`],
  stdout: Bun.file(join(HERE, "LICENSE")),
});
TESTS.forEach((test) => {
  const wast = join(HERE, "wast", `${test}.wast`);
  run({
    cmd: [git, "-C", spec.clone, "cat-file", "blob", `${COMMIT}:test/core/${test}.wast`],
    stdout: Bun.file(wast),
  });
  writeBinary(spec.cut, wast, test);
});
OWN.forEach((test) => {
  const wast = join(HERE, "own", `${test}.wast`);
  run({ cmd: [spec.wasm, wast] });
  writeBinary(spec.cut, wast, `own-${test}`);
});
HOST.forEach((module) => {
  const at = join(HERE, "host", module);
  run({ cmd: [spec.wasm, "-d", `${at}.wat`, "-o", `${at}.wasm`] });
});
