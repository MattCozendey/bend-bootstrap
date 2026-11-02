// What the scripts of the WASM tests take from the official WebAssembly spec (AGENTS.md 3.9.1.3):
// its repository at the commit that the tests pin, and the spec's reference interpreter, built from
// it with our OCaml programs on its library (cut.ml for convert.ts, oracle.ml for
// differential.ts). The commit is pinned, and so are the tools that build them: getSpec refuses any
// other. The tools, with opam 2.2 or later (on Linux, macOS or Windows), once opam init has run:
//
//   opam switch create wasm-spec ocaml-base-compiler.5.4.1
//   opam install --switch=wasm-spec dune.3.24.2 menhir.20260209
//   opam exec --switch=wasm-spec -- bun <the script> WORK

// imports

import { cpSync, mkdirSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import { run } from "../../Shared/shared.ts";

// types

// the spec's clone, and the executables built from it: the reference interpreter, cut.ml's and
// oracle.ml's
type Spec = {
  readonly clone: string;
  readonly wasm: string;
  readonly cut: string;
  readonly oracle: string;
};

// constants

export const COMMIT = "6057acdb1a213f85369c64454c078a15f11ac4b1";
const SPEC = "https://github.com/WebAssembly/spec.git";
// the tools that build the programs, and the argument that makes each print its version, whose last
// word must be the pinned one; OCaml's is a 5.4 one, as the spec's CI at COMMIT takes
// (.github/workflows/ci-interpreter.yml)
const TOOLS = [
  { name: "ocamlc", flag: "-version", version: "5.4.1" },
  { name: "dune", flag: "--version", version: "3.24.2" },
  { name: "menhir", flag: "--version", version: "20260209" },
];
// our programs on the interpreter's library, next to this script
const PROGRAMS = ["cut", "oracle"];
const HERE = import.meta.dir;
const DUNE_LANG = "(lang dune 3.14)\n";

// functions

// the path of the executable (on Windows, its .exe) that PATH finds for the name; without one, the
// script stops
export const getExe = (name: string): string => {
  const exe = Bun.which(name);
  if (exe === null) {
    console.error(`${process.argv[1]} needs ${name}`);
    process.exit(1);
  }
  return exe;
};

// the spec at COMMIT, cloned in the folder work, and the executables built from it there, in a dune
// workspace of the interpreter's library and our programs, where dune rebuilds what changed
export const getSpec = (work: string): Spec => {
  const git = getExe("git");
  TOOLS.forEach(({ name, flag, version }) => {
    const said = Bun.spawnSync([getExe(name), flag])
      .stdout.toString()
      .trim()
      .split(" ")
      .at(-1);
    if (said !== version) {
      console.error(`${process.argv[1]} needs ${name} ${version}, not ${said ?? "none"}`);
      process.exit(1);
    }
  });
  const clone = join(work, "spec");
  mkdirSync(work, { recursive: true });
  run({ cmd: [git, "init", "-q", clone] });
  run({ cmd: [git, "-C", clone, "fetch", "-q", "--depth", "1", SPEC, COMMIT] });
  run({
    cmd: [
      git,
      "-C",
      clone,
      "-c",
      "core.autocrlf=false",
      "checkout",
      "-q",
      "--detach",
      "FETCH_HEAD",
    ],
  });
  if (Bun.spawnSync([git, "-C", clone, "rev-parse", "HEAD"]).stdout.toString().trim() !== COMMIT) {
    console.error(`${process.argv[1]}: the spec is not at ${COMMIT}`);
    process.exit(1);
  }
  const build = join(work, "build");
  cpSync(join(clone, "interpreter"), join(build, "interpreter"), { recursive: true });
  writeFileSync(join(build, "dune-workspace"), DUNE_LANG);
  PROGRAMS.forEach((program) => {
    mkdirSync(join(build, program), { recursive: true });
    writeFileSync(join(build, program, "dune-project"), DUNE_LANG);
    writeFileSync(
      join(build, program, "dune"),
      `(executable\n  (name ${program})\n  (libraries wasm)\n  (flags (:standard -open Wasm)))\n`,
    );
    cpSync(join(HERE, `${program}.ml`), join(build, program, `${program}.ml`));
  });
  run({
    cmd: [
      getExe("dune"),
      "build",
      "./interpreter/wasm.exe",
      ...PROGRAMS.map((program) => `./${program}/${program}.exe`),
    ],
    cwd: build,
  });
  const getBuilt = (dir: string, name: string) =>
    join(build, "_build", "default", dir, `${name}.exe`);
  return {
    clone,
    wasm: getBuilt("interpreter", "wasm"),
    cut: getBuilt("cut", "cut"),
    oracle: getBuilt("oracle", "oracle"),
  };
};
