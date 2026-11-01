// run.ts WORK: tests of kind c of the compiler of AGENTS.md 3.8.4, which the laws of
// src/Compiler/spec.bend (no_wrong_result, no_other_failure, enough_memory) replace once they are
// proven. Each program of progs/ is compiled, and its module runs on each input in a real engine,
// bun's JavaScriptCore, as the host of Wasm.run does. It must give the result that the Lean
// interpreter gives (src/Interpreter/scripts/Run.lean, which gives what Eval gives), or no result
// when it gives none. The compiler runs as the JS that `bend -o` writes for compile.bend; with
// TRUSTED=1, the Lean interpreter also runs it on progs/echo.bend, and must write the same bytes
// (this takes a few minutes: about 44.4 million steps of Eval). bun is pinned: the script refuses
// any other. WORK is a folder for what the tests write.
//
//   [TRUSTED=1] bun run.ts WORK

// imports

import { mkdirSync, readdirSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { homedir } from "node:os";
import { basename, delimiter, join, resolve } from "node:path";
import { getArgs, run } from "../../Shared/shared.ts";

// types

// an input of the programs: a text, or the bytes of a file
type Input = string | { readonly file: string; readonly bytes: Uint8Array };

// a line of the report
type Line = { readonly ok: boolean; readonly text: string };

// constants

const BUN = "1.4.4";
const HERE = import.meta.dir;
const REPO = resolve(HERE, "../../..");

// the env of lake: elan's folder first on PATH (whose key is Path on Windows)
const PATH_KEY = Object.keys(process.env).find((key) => key.toUpperCase() === "PATH") ?? "PATH";
const LAKE_ENV = {
  ...process.env,
  [PATH_KEY]: [join(homedir(), ".elan", "bin"), process.env[PATH_KEY]].join(delimiter),
};

// The JS that `bend -o` writes recurses deeper than bun's default stack allows, so compile.ts runs
// in a bun whose JavaScriptCore may use STACK_BYTES of stack. On POSIX, the stack limit must allow
// as much too.
const STACK_BYTES = 2_000_000_000;
const BIG_STACK =
  process.platform === "win32"
    ? []
    : ["sh", "-c", `ulimit -s ${STACK_BYTES / 1024} && exec "$0" "$@"`];

const EVERY: Input = { file: "every", bytes: Uint8Array.from({ length: 256 }, (_, b) => b) };
// the states of a fixed LCG, in doubles (whose products lose bits)
const LCG = Array.from({ length: 500 }).reduce<readonly number[]>(
  (xs) => [...xs, ((xs.at(-1) ?? 7) * 1103515245 + 12345) % 2147483648],
  [],
);
const RANDOM_500: Input = {
  file: "random500",
  bytes: Uint8Array.from(LCG, (x) => Math.floor(x / 65536) % 256),
};
const X_20000: Input = { file: "x20000", bytes: Buffer.from("x".repeat(20000)) };

const INPUTS: Record<string, readonly Input[]> = {
  echo: ["hello, world", "", EVERY],
  rev: ["hello", "", EVERY],
  inc: ["az", EVERY],
  sort: ["hello", "zyxwv", RANDOM_500],
  count: ["", "hello", RANDOM_500],
  adder: ["abc", ""],
  partial: ["abc"],
  quant: ["abc"],
  deep: ["hello", X_20000],
  big: ["x"],
  rwt: ["hello", ""],
};

// functions

// `bend file -o out`, with the Bend of the bend submodule
const getBend = (file: string, out: string) => ({
  cmd: [process.execPath, join(REPO, "bend/bend2/main.ts"), file, "-o", out],
  stdout: "ignore" as const,
});

// `lake lean <script>` at the root of the Lean project (the repo), with these variables
const getLake = (script: string, vars: Record<string, string>) => ({
  cmd: ["lake", "lean", script],
  cwd: REPO,
  env: { ...LAKE_ENV, ...vars },
});

// prints a line of the report, and gives whether it is a failure
const isFail = ({ ok, text }: Line): boolean => {
  console.log(`${ok ? "ok  " : "FAIL"} ${text}`);
  return !ok;
};

// side effects

const [workArg] = getArgs("WORK");
if (Bun.version !== BUN) {
  console.error(`run.ts needs bun ${BUN}, not ${Bun.version}`);
  process.exit(1);
}
const work = resolve(workArg);
mkdirSync(work, { recursive: true });
run(getBend(join(HERE, "compile.bend"), join(work, "compile.mjs")));

const progFails = readdirSync(join(HERE, "progs"))
  .filter((file) => file.endsWith(".bend"))
  .toSorted()
  .flatMap((file) => {
    const n = basename(file, ".bend");
    const at = (ext: string) => join(work, `${n}.${ext}`);
    run(getBend(join(HERE, "progs", file), at("bendtt")));
    run({
      ...getLake("src/Book/scripts/Write.lean", { BOOK: at("bendtt"), OUTPUT: at("book") }),
      stdout: "ignore",
      stderr: "ignore",
    });
    run({
      cmd: [
        ...BIG_STACK,
        process.execPath,
        join(HERE, "compile.ts"),
        join(work, "compile.mjs"),
        at("book"),
        at("wasm"),
      ],
      env: { ...process.env, BUN_JSC_maxPerThreadStackUsage: String(STACK_BYTES) },
    });
    return (INPUTS[n] ?? []).map((input) => {
      const [name, bytes] =
        typeof input === "string"
          ? [`text:${input}`, Buffer.from(input)]
          : [`file:${input.file}`, input.bytes];
      writeFileSync(at("in"), bytes);
      rmSync(at("want"), { force: true });
      rmSync(at("bun"), { force: true });
      const lean = Bun.spawnSync({
        ...getLake("src/Interpreter/scripts/Run.lean", {
          BOOK: at("bendtt"),
          INPUT: at("in"),
          OUTPUT: at("want"),
        }),
        stdout: "pipe",
        stderr: "pipe",
      });
      // lake lean prints a script's error on stdout
      const leanError = lean.stdout.toString() + lean.stderr.toString();
      const says = Bun.spawnSync({
        cmd: [process.execPath, join(HERE, "host.ts"), at("wasm"), at("in"), at("bun")],
        stderr: "inherit",
      })
        .stdout.toString()
        .trimEnd();
      // Run.lean exits with 0 on a result, and with an error "no result: ..." when the run
      // gets stuck or ends in a value that is not a list of bytes; any other end (a crash,
      // or no result within its fuel) says nothing about the run
      const isKnown = lean.exitCode === 0 || leanError.includes("error: no result: ");
      const want = lean.exitCode === 0 ? readFileSync(at("want")) : undefined;
      const got = says === "result" ? readFileSync(at("bun")) : undefined;
      const isSame = want === undefined ? got === undefined : got !== undefined && want.equals(got);
      const text = !isKnown
        ? `the interpreter gives no answer: ${leanError.trim().split("\n").at(-1) ?? ""}`
        : !isSame
          ? `bun ${says}, the interpreter ${want ? "a" : "no"} result`
          : want
            ? `the same ${want.length} bytes`
            : `no result (bun ${says})`;
      return isFail({ ok: isKnown && isSame, text: `${n} ${name}: ${text}` });
    });
  })
  .filter(Boolean).length;

const isTrustedFail =
  Boolean(process.env.TRUSTED) &&
  (() => {
    run(getBend(join(HERE, "compile.bend"), join(work, "compile.bendtt")));
    run({
      ...getLake("src/Interpreter/scripts/Run.lean", {
        BOOK: join(work, "compile.bendtt"),
        INPUT: join(work, "echo.book"),
        OUTPUT: join(work, "echo.trusted.wasm"),
        FUEL: "1000000000000",
      }),
      stdout: "ignore",
    });
    const isSame = readFileSync(join(work, "echo.wasm")).equals(
      readFileSync(join(work, "echo.trusted.wasm")),
    );
    return isFail({
      ok: isSame,
      text: `the Lean interpreter compiles echo to ${isSame ? "the same" : "other"} bytes`,
    });
  })();

const fails = progFails + Number(isTrustedFail);
console.log(`${fails} failed`);
process.exit(fails === 0 ? 0 : 1);
