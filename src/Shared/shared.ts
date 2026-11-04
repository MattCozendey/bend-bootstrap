// What the scripts of the tests have in common.

// imports

import { homedir } from "node:os";
import { delimiter, join, resolve } from "node:path";

// types

// a command and how it runs, as Bun.spawnSync takes them
type Command = Bun.SpawnOptions.SpawnSyncOptions<
  "ignore",
  Bun.SpawnOptions.Readable,
  Bun.SpawnOptions.Readable
> & { readonly cmd: string[] };

// constants

export const REPO = resolve(import.meta.dir, "../..");

// the env of lake: elan's folder first on PATH (whose key is Path on Windows)
const PATH_KEY = Object.keys(process.env).find((key) => key.toUpperCase() === "PATH") ?? "PATH";
const LAKE_ENV = {
  ...process.env,
  [PATH_KEY]: [join(homedir(), ".elan", "bin"), process.env[PATH_KEY]].join(delimiter),
};

// the bun that runs Bend: on Windows, WSL's (AGENTS.md 2.4.1), whose shell first turns each
// Windows path (C:\…) into its WSL path
const BEND_BUN =
  process.platform === "win32"
    ? [
        "wsl.exe",
        "-e",
        "bash",
        "-lc",
        'for a; do case $a in [A-Za-z]:[\\\\/]*) a=$(wslpath -a "$a");; esac; set -- "$@" "$a"; shift; done; exec bun "$@"',
        "bun",
      ]
    : [process.execPath];

// The JS that `bend -o` writes recurses deeper than bun's default stack allows, so compile.ts runs
// in a bun whose JavaScriptCore may use STACK_BYTES of stack. On POSIX, the stack limit must allow
// as much too.
const STACK_BYTES = 2_000_000_000;
const BIG_STACK =
  process.platform === "win32"
    ? []
    : ["sh", "-c", `ulimit -s ${STACK_BYTES / 1024} && exec "$0" "$@"`];

// functions

// `bend file -o out`, with the Bend of the bend submodule
export const getBend = (file: string, out: string) => ({
  cmd: [...BEND_BUN, join(REPO, "bend/bend2/main.ts"), file, "-o", out],
  stdout: "ignore" as const,
});

// the BendTT lowering of src/main.bend into out, as `bend -o` writes it but for the holes
// (src/Shared/lower.ts)
export const getLower = (out: string) => ({
  cmd: [...BEND_BUN, "Shared/lower.ts", "main.bend", out],
  cwd: join(REPO, "src"),
  stdout: "ignore" as const,
});

// src/Compiler/tests/compile.ts: the compiler, as the JS that `bend -o` writes for compile.bend
// (js), on the bytes of a book, into a module
export const getCompile = (js: string, book: string, out: string) => ({
  cmd: [...BIG_STACK, process.execPath, join(REPO, "src/Compiler/tests/compile.ts"), js, book, out],
  env: { ...process.env, BUN_JSC_maxPerThreadStackUsage: String(STACK_BYTES) },
});

// `lake <args>` at the root of the Lean project (the repo), with these variables
export const getLake = (args: readonly string[], vars: Record<string, string> = {}) => ({
  cmd: ["lake", ...args],
  cwd: REPO,
  env: { ...LAKE_ENV, ...vars },
});

// the arguments of the script, one for each name; with another number of them, the script stops
// and prints its usage
export const getArgs = <const T extends readonly string[]>(
  ...names: T
): { readonly [K in keyof T]: string } => {
  const args = process.argv.slice(2);
  if (args.length !== names.length) {
    console.error(`usage: bun ${process.argv[1]} ${names.join(" ")}`);
    process.exit(1);
  }
  return args as { readonly [K in keyof T]: string };
};

// runs a command that must succeed, its output to ours unless it says otherwise; on a failure, the
// script stops with the command's exit code
export const run = ({ cmd, ...options }: Command): void => {
  const { success, exitCode } = Bun.spawnSync(cmd, {
    stdout: "inherit",
    stderr: "inherit",
    ...options,
  });
  if (!success) process.exit(exitCode || 1);
};
