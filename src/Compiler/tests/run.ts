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
// The interpreter runs all its jobs in one process. Its answers are cached in .cache/interp/, by
// a hash of what decides them: the interpreter's code (each Lean file of src/, the kernel, the
// Lean project's config), the book, the input and the fuel. FRESH=1 runs each job again (AGENTS.md
// 3.10.2: the cache is for development only).
//
//   [TRUSTED=1] [FRESH=1] [FUEL=n] bun run.ts WORK

// imports

import {
  copyFileSync,
  existsSync,
  mkdirSync,
  readdirSync,
  readFileSync,
  rmSync,
  writeFileSync,
} from "node:fs";
import { basename, join, resolve } from "node:path";
import { getArgs, getBend, getCompile, getLake, REPO, run } from "../../Shared/shared.ts";

// types

// an input of the programs: a text, or the bytes of a file
type Input = string | { readonly file: string; readonly bytes: Uint8Array };

// a line of the report
type Line = { readonly ok: boolean; readonly text: string };

// a run of the Lean interpreter: a book, an input file, and where its answer goes
type Job = { readonly book: string; readonly input: string; readonly output: string };

// what the interpreter says of a job: a result; no result (stuck, or a value that is not a list
// of bytes); or no answer (a crash, or no result within its fuel), with why
type Answer =
  | { readonly kind: "result"; readonly bytes: Buffer }
  | { readonly kind: "none" | "unknown"; readonly why: string };

// constants

const BUN = "1.4.4";
const HERE = import.meta.dir;
const RUN = "src/Interpreter/scripts/Run.lean";
const CACHE = join(REPO, ".cache", "interp");

// the hash of the interpreter's code: each Lean file of src/, the kernel, the Lean project's config
const CODE_HASH = [
  ...new Bun.Glob("src/**/*.lean").scanSync({ cwd: REPO }),
  "bend/bend2/bendtt.lean",
  "lakefile.lean",
  "lake-manifest.json",
  "lean-toolchain",
]
  .toSorted()
  .reduce(
    (hasher, file) => hasher.update(`${file}\0`).update(readFileSync(join(REPO, file))),
    new Bun.CryptoHasher("sha256"),
  )
  .digest("hex");

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

// prints a line of the report, and gives whether it is a failure
const isFail = ({ ok, text }: Line): boolean => {
  console.log(`${ok ? "ok  " : "FAIL"} ${text}`);
  return !ok;
};

// the cache file of a job's answer with this fuel
const getCacheFile = ({ book, input }: Job, fuel: string): string => {
  const [b, i] = [readFileSync(book), readFileSync(input)];
  const hasher = new Bun.CryptoHasher("sha256").update(CODE_HASH);
  return join(
    CACHE,
    hasher
      .update(`${b.length}:`)
      .update(b)
      .update(`${i.length}:`)
      .update(i)
      .update(fuel)
      .digest("hex"),
  );
};

// the answer that Run.lean left at output: a result there, or why there is none in output.none
const tryAnswer = (output: string): Answer | undefined => {
  if (existsSync(output)) return { kind: "result", bytes: readFileSync(output) };
  if (!existsSync(`${output}.none`)) return undefined;
  const why = readFileSync(`${output}.none`, "utf8");
  return { kind: why.startsWith("no result: ") ? "none" : "unknown", why };
};

// the answers of the jobs with this fuel: from the cache (but with FRESH=1), else from one run of
// Run.lean over the jobs file, which puts its known answers in the cache
const getAnswers = <J extends Job>(
  jobs: readonly J[],
  fuel: string,
  jobsFile: string,
): readonly (J & { readonly answer: Answer })[] => {
  mkdirSync(CACHE, { recursive: true });
  const keyed = jobs.map((job) => {
    rmSync(job.output, { force: true });
    rmSync(`${job.output}.none`, { force: true });
    const cache = getCacheFile(job, fuel);
    const isCached = !process.env.FRESH && tryAnswer(cache) !== undefined;
    if (isCached && existsSync(cache)) copyFileSync(cache, job.output);
    if (isCached && !existsSync(cache)) copyFileSync(`${cache}.none`, `${job.output}.none`);
    return { job, cache, isCached };
  });
  const todo = keyed.filter(({ isCached }) => !isCached);
  writeFileSync(
    jobsFile,
    todo.map(({ job }) => `${job.book}\t${job.input}\t${job.output}\n`).join(""),
  );
  const lake =
    todo.length === 0
      ? undefined
      : Bun.spawnSync({
          ...getLake(["lean", RUN], { JOBS: jobsFile, FUEL: fuel }),
          stdout: "pipe",
          stderr: "pipe",
        });
  // lake lean prints a script's error on stdout
  const crash =
    lake?.success === false ? `${lake.stdout}${lake.stderr}`.trim().split("\n").at(-1) : undefined;
  return keyed.map(({ job, cache, isCached }) => {
    const answer = tryAnswer(job.output) ?? {
      kind: "unknown" as const,
      why: crash ?? "the interpreter left no answer",
    };
    if (!isCached && answer.kind === "result") copyFileSync(job.output, cache);
    if (!isCached && answer.kind === "none") copyFileSync(`${job.output}.none`, `${cache}.none`);
    return { ...job, answer };
  });
};

// side effects

const [workArg] = getArgs("WORK");
if (Bun.version !== BUN) {
  console.error(`run.ts needs bun ${BUN}, not ${Bun.version}`);
  process.exit(1);
}
const work = resolve(workArg);
const at = (file: string) => join(work, file);
mkdirSync(work, { recursive: true });
run(getBend(join(HERE, "compile.bend"), at("compile.mjs")));

const progs = readdirSync(join(HERE, "progs"))
  .filter((file) => file.endsWith(".bend"))
  .toSorted()
  .map((file) => basename(file, ".bend"));
progs.forEach((n) => run(getBend(join(HERE, "progs", `${n}.bend`), at(`${n}.bendtt`))));
writeFileSync(
  at("write.jobs"),
  progs.map((n) => `${at(`${n}.bendtt`)}\t${at(`${n}.book`)}\n`).join(""),
);
run({
  ...getLake(["lean", "src/Book/scripts/Write.lean"], { JOBS: at("write.jobs") }),
  stdout: "ignore",
});
progs.forEach((n) => run(getCompile(at("compile.mjs"), at(`${n}.book`), at(`${n}.wasm`))));

const cases = progs.flatMap((n) =>
  (INPUTS[n] ?? []).map((input, k) => {
    const [name, bytes] =
      typeof input === "string"
        ? [`text:${input}`, Buffer.from(input)]
        : [`file:${input.file}`, input.bytes];
    writeFileSync(at(`${n}.${k}.in`), bytes);
    return {
      n,
      name,
      book: at(`${n}.bendtt`),
      input: at(`${n}.${k}.in`),
      output: at(`${n}.${k}.want`),
    };
  }),
);
const progFails = getAnswers(cases, process.env.FUEL ?? "", at("run.jobs")).filter(
  ({ n, name, input, output, answer }) => {
    rmSync(`${output}.bun`, { force: true });
    const says = Bun.spawnSync({
      cmd: [process.execPath, join(HERE, "host.ts"), at(`${n}.wasm`), input, `${output}.bun`],
      stderr: "inherit",
    })
      .stdout.toString()
      .trimEnd();
    const want = answer.kind === "result" ? answer.bytes : undefined;
    const got = says === "result" ? readFileSync(`${output}.bun`) : undefined;
    const isSame = want === undefined ? got === undefined : got !== undefined && want.equals(got);
    const text =
      answer.kind === "unknown"
        ? `the interpreter gives no answer: ${answer.why}`
        : !isSame
          ? `bun ${says}, the interpreter ${want ? "a" : "no"} result`
          : want
            ? `the same ${want.length} bytes`
            : `no result (bun ${says})`;
    return isFail({ ok: answer.kind !== "unknown" && isSame, text: `${n} ${name}: ${text}` });
  },
).length;

const isTrustedFail =
  Boolean(process.env.TRUSTED) &&
  (() => {
    run(getBend(join(HERE, "compile.bend"), at("compile.bendtt")));
    const job = {
      book: at("compile.bendtt"),
      input: at("echo.book"),
      output: at("echo.trusted.wasm"),
    };
    const [{ answer } = { answer: { kind: "unknown", why: "no job" } as Answer }] = getAnswers(
      [job],
      "1000000000000",
      at("trusted.jobs"),
    );
    const isSame = answer.kind === "result" && readFileSync(at("echo.wasm")).equals(answer.bytes);
    return isFail({
      ok: isSame,
      text:
        answer.kind === "result"
          ? `the Lean interpreter compiles echo to ${isSame ? "the same" : "other"} bytes`
          : `the Lean interpreter compiles echo to no bytes: ${answer.why}`,
    });
  })();

const fails = progFails + Number(isTrustedFail);
console.log(`${fails} failed`);
process.exit(fails === 0 ? 0 : 1);
