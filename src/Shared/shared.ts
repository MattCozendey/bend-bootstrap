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

// functions

// `bend file -o out`, with the Bend of the bend submodule
export const getBend = (file: string, out: string) => ({
  cmd: [process.execPath, join(REPO, "bend/bend2/main.ts"), file, "-o", out],
  stdout: "ignore" as const,
});

// the BendTT lowering of src/main.bend into out, as `bend -o` writes it but for the holes
// (src/Shared/lower.ts)
export const getLower = (out: string) => ({
  cmd: [process.execPath, "Shared/lower.ts", "main.bend", out],
  cwd: join(REPO, "src"),
  stdout: "ignore" as const,
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
