// convert.ts WORK: the binary scripts of the official WebAssembly tests that the Bend version of
// WASM is tested with (AGENTS.md 3.9.1.3), made by cut.ml, which reads each test script with the
// spec's own reference interpreter, keeps in each module that a command defines only its functions
// inside the subset, and writes the script as wasm -d x.wast -o x.bin.wast does. The spec's commit
// is pinned: the script refuses any other. It needs ocaml, dune and menhir. WORK is a folder for the
// spec's clone and the build. The license, the tests (wast/), and their binary scripts and lists of
// pure exports (bin/) go next to this script. Our own tests (own/, AGENTS.md 3.9.1.3) become
// binary scripts there too, as own-x.bin.wast, once the spec's reference interpreter passes them.
//
//   bun convert.ts WORK

// imports

import { cpSync, existsSync, mkdirSync, rmSync, writeFileSync } from "node:fs";
import { join, resolve } from "node:path";
import { getArgs, run } from "../../Shared/shared.ts";

// constants

const SPEC = "https://github.com/WebAssembly/spec.git";
const COMMIT = "6057acdb1a213f85369c64454c078a15f11ac4b1";
const TESTS = [
  "binary", "binary-leb128", "i32", "int_exprs", "address", "align", "endianness", "load", "store",
  "memory", "memory_grow", "memory_size", "memory_trap", "data", "block", "loop", "br", "br_if",
  "br_table", "labels", "local_get", "local_set", "local_tee", "exports", "unreached-invalid",
];
const OWN = ["stores", "loads", "branches"];
const HERE = import.meta.dir;
const DUNE_LANG = "(lang dune 3.14)\n";

// functions

// cut.exe's binary script and pure exports of the test script wast, as bin/name.bin.wast and
// bin/name.pure
const writeBinary = (cutExe: string, wast: string, name: string): void =>
  run({
    cmd: [cutExe, wast, join(HERE, "bin", `${name}.pure`)],
    stdout: Bun.file(join(HERE, "bin", `${name}.bin.wast`)),
  });

// side effects

const [workArg] = getArgs("WORK");
const missing = ["ocaml", "dune", "menhir"].find((tool) => Bun.which(tool) === null);
if (missing !== undefined) {
  console.error(`convert.ts needs ${missing}`);
  process.exit(1);
}

const work = resolve(workArg);
const spec = join(work, "spec");
mkdirSync(work, { recursive: true });
if (!existsSync(join(spec, ".git"))) run({ cmd: ["git", "init", "-q", spec] });
run({ cmd: ["git", "-C", spec, "fetch", "-q", "--depth", "1", SPEC, COMMIT] });
run({ cmd: ["git", "-C", spec, "checkout", "-q", "--detach", "FETCH_HEAD"] });
if (Bun.spawnSync(["git", "-C", spec, "rev-parse", "HEAD"]).stdout.toString().trim() !== COMMIT) {
  console.error(`convert.ts: the spec is not at ${COMMIT}`);
  process.exit(1);
}

// a dune workspace of the interpreter's library and cut.ml alone
const cut = join(work, "cut");
rmSync(cut, { recursive: true, force: true });
mkdirSync(join(cut, "cut"), { recursive: true });
cpSync(join(spec, "interpreter"), join(cut, "interpreter"), { recursive: true });
rmSync(join(cut, "interpreter", "_build"), { recursive: true, force: true });
writeFileSync(join(cut, "dune-workspace"), DUNE_LANG);
writeFileSync(join(cut, "cut", "dune-project"), DUNE_LANG);
writeFileSync(
  join(cut, "cut", "dune"),
  "(executable\n  (name cut)\n  (libraries wasm)\n  (flags (:standard -open Wasm)))\n",
);
cpSync(join(HERE, "cut.ml"), join(cut, "cut", "cut.ml"));
run({ cmd: ["dune", "build", "./cut/cut.exe", "./interpreter/wasm.exe"], cwd: cut });
const cutExe = join(cut, "_build", "default", "cut", "cut.exe");
const wasmExe = join(cut, "_build", "default", "interpreter", "wasm.exe");

rmSync(join(HERE, "wast"), { recursive: true, force: true });
rmSync(join(HERE, "bin"), { recursive: true, force: true });
mkdirSync(join(HERE, "wast"));
mkdirSync(join(HERE, "bin"));
cpSync(join(spec, "test", "LICENSE"), join(HERE, "LICENSE"));
TESTS.forEach((test) => {
  const wast = join(spec, "test", "core", `${test}.wast`);
  cpSync(wast, join(HERE, "wast", `${test}.wast`));
  writeBinary(cutExe, wast, test);
});
OWN.forEach((test) => {
  const wast = join(HERE, "own", `${test}.wast`);
  run({ cmd: [wasmExe, wast] });
  writeBinary(cutExe, wast, `own-${test}`);
});
