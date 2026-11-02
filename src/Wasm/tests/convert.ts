// convert.ts WORK: the binary scripts of the official WebAssembly tests that the Bend version of
// WASM is tested with (AGENTS.md 3.9.1.3), made by cut.ml, which reads each test script with the
// spec's own reference interpreter, keeps in each module that a command defines in the text format
// only its functions and exports inside the subset, and writes the script as wasm -d x.wast -o
// x.bin.wast does, with what it finds of each module in x.facts. The spec's commit is pinned, and
// so are the tools that build cut.ml and the reference interpreter: the script refuses any other.
// WORK is a folder for the spec's clone and the build. The license, the tests (wast/), and their
// binary scripts and facts (bin/) go next to this script, with the same bytes on every system. Our
// own tests (own/, AGENTS.md 3.9.1.3) become binary scripts there too, as own-x.bin.wast, once the
// spec's reference interpreter passes them; each module of agree.ts, host/x.wat, becomes
// host/x.wasm.
//
// The tools, with opam 2.2 or later (on Linux, macOS or Windows), once opam init has run:
//
//   opam switch create wasm-spec ocaml-base-compiler.5.4.1
//   opam install --switch=wasm-spec dune.3.24.2 menhir.20260209
//   opam exec --switch=wasm-spec -- bun convert.ts WORK

// imports

import { cpSync, mkdirSync, rmSync, writeFileSync } from "node:fs";
import { join, resolve } from "node:path";
import { getArgs, run } from "../../Shared/shared.ts";

// constants

const SPEC = "https://github.com/WebAssembly/spec.git";
const COMMIT = "6057acdb1a213f85369c64454c078a15f11ac4b1";
// the tools that build cut.ml and the reference interpreter, and the argument that makes each print
// its version, whose last word must be the pinned one; OCaml's is a 5.4 one, as the spec's CI at
// COMMIT takes (.github/workflows/ci-interpreter.yml)
const TOOLS = [
  { name: "ocamlc", flag: "-version", version: "5.4.1" },
  { name: "dune", flag: "--version", version: "3.24.2" },
  { name: "menhir", flag: "--version", version: "20260209" },
];
const TESTS = [
  "binary", "binary-leb128", "int_literals", "i32", "int_exprs", "address", "align", "endianness",
  "load", "store", "memory", "memory_grow", "memory_size", "memory_trap", "data", "block", "loop",
  "br", "br_if", "br_table", "labels", "local_get", "local_set", "local_tee", "func", "func_ptrs",
  "exports", "names", "unreached-invalid",
];
const OWN = ["stores", "loads", "branches", "invalid", "results", "encodings"];
const HOST = ["cases", "init", "nomemory"];
const HERE = import.meta.dir;
const DUNE_LANG = "(lang dune 3.14)\n";

// functions

// the path of the executable (on Windows, its .exe) that PATH finds for the name; without one, the
// script stops
const getExe = (name: string): string => {
  const exe = Bun.which(name);
  if (exe === null) {
    console.error(`convert.ts needs ${name}`);
    process.exit(1);
  }
  return exe;
};

// cut.exe's binary script and facts of the test script wast, as bin/name.bin.wast and
// bin/name.facts
const writeBinary = (cutExe: string, wast: string, name: string): void =>
  run({
    cmd: [cutExe, wast, join(HERE, "bin", `${name}.facts`)],
    stdout: Bun.file(join(HERE, "bin", `${name}.bin.wast`)),
  });

// side effects

const [workArg] = getArgs("WORK");
const git = getExe("git");
TOOLS.forEach(({ name, flag, version }) => {
  const said = Bun.spawnSync([getExe(name), flag]).stdout.toString().trim().split(" ").at(-1);
  if (said !== version) {
    console.error(`convert.ts needs ${name} ${version}, not ${said ?? "none"}`);
    process.exit(1);
  }
});

const work = resolve(workArg);
const spec = join(work, "spec");
mkdirSync(work, { recursive: true });
run({ cmd: [git, "init", "-q", spec] });
run({ cmd: [git, "-C", spec, "fetch", "-q", "--depth", "1", SPEC, COMMIT] });
run({
  cmd: [git, "-C", spec, "-c", "core.autocrlf=false", "checkout", "-q", "--detach", "FETCH_HEAD"],
});
if (Bun.spawnSync([git, "-C", spec, "rev-parse", "HEAD"]).stdout.toString().trim() !== COMMIT) {
  console.error(`convert.ts: the spec is not at ${COMMIT}`);
  process.exit(1);
}

// a dune workspace of the interpreter's library and cut.ml alone; dune rebuilds in it what changed
const cut = join(work, "cut");
mkdirSync(join(cut, "cut"), { recursive: true });
cpSync(join(spec, "interpreter"), join(cut, "interpreter"), { recursive: true });
writeFileSync(join(cut, "dune-workspace"), DUNE_LANG);
writeFileSync(join(cut, "cut", "dune-project"), DUNE_LANG);
writeFileSync(
  join(cut, "cut", "dune"),
  "(executable\n  (name cut)\n  (libraries wasm)\n  (flags (:standard -open Wasm)))\n",
);
cpSync(join(HERE, "cut.ml"), join(cut, "cut", "cut.ml"));
run({ cmd: [getExe("dune"), "build", "./cut/cut.exe", "./interpreter/wasm.exe"], cwd: cut });
const cutExe = join(cut, "_build", "default", "cut", "cut.exe");
const wasmExe = join(cut, "_build", "default", "interpreter", "wasm.exe");

// each file of the spec as git holds it, whatever the system's line endings
rmSync(join(HERE, "wast"), { recursive: true, force: true });
rmSync(join(HERE, "bin"), { recursive: true, force: true });
mkdirSync(join(HERE, "wast"));
mkdirSync(join(HERE, "bin"));
run({
  cmd: [git, "-C", spec, "cat-file", "blob", `${COMMIT}:test/LICENSE`],
  stdout: Bun.file(join(HERE, "LICENSE")),
});
TESTS.forEach((test) => {
  const wast = join(HERE, "wast", `${test}.wast`);
  run({
    cmd: [git, "-C", spec, "cat-file", "blob", `${COMMIT}:test/core/${test}.wast`],
    stdout: Bun.file(wast),
  });
  writeBinary(cutExe, wast, test);
});
OWN.forEach((test) => {
  const wast = join(HERE, "own", `${test}.wast`);
  run({ cmd: [wasmExe, wast] });
  writeBinary(cutExe, wast, `own-${test}`);
});
HOST.forEach((module) => {
  const at = join(HERE, "host", module);
  run({ cmd: [wasmExe, "-d", `${at}.wat`, "-o", `${at}.wasm`] });
});
