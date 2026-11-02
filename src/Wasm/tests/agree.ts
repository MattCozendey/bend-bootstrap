// agree.ts WORK: tests of kind a (bend2 skill) of the model's Host section (Wasm.run of
// src/Wasm/impl.bend, AGENTS.md 3.9.1.3.3): on each case, the model, run by the Lean interpreter
// (src/Wasm/scripts/Host.lean), and a real host, src/Compiler/tests/host.ts in bun's engine, give
// the same outcome. A law cannot state it: the real host is not Bend. The cases are the paths of
// host/cases.wasm, whose outcomes are also fixed here, and a few compiled programs, which the
// compiler's own code compiles in the Lean interpreter. WORK is a folder for what the tests write.
//
//   bun src/Wasm/tests/agree.ts WORK

// imports

import { mkdirSync, readFileSync, writeFileSync } from "node:fs";
import { join, resolve } from "node:path";
import { getArgs, getBend, getLake, getLower, REPO, run } from "../../Shared/shared.ts";

// types

// a case: a module (a .wasm file, or a program to compile) and an input; for a case of
// host/cases.wasm, the outcome that it must give
type Case = {
  readonly name: string;
  readonly module: { readonly wasm: string } | { readonly program: string };
  readonly input: string;
  readonly want?: string;
};

// constants

const HERE = import.meta.dir;
const HOST = join(REPO, "src/Compiler/tests/host.ts");
const CASES = join(HERE, "host", "cases.wasm");

// the paths of host/cases.wasm, picked by the input's first byte, and what they give: an outcome
// is its name (Wasm.Outcome), with a result's bytes in hex
const HOSTED: readonly Case[] = [
  { name: "e", input: "ehello", want: `result ${Buffer.from("ehello").toString("hex")}` },
  { name: "o", input: "o", want: "out_of_memory" },
  { name: "n", input: "n", want: "no_result" },
  { name: "x", input: "x", want: "trap" },
  { name: "r", input: "r", want: "trap" },
  { name: "z", input: "z", want: "result " },
  { name: "m", input: "m\u0002", want: `result ${Buffer.from("3").toString("hex")}` },
  { name: "big", input: "b".repeat(60001), want: "out_of_memory" },
  { name: "empty", input: "", want: "no_result" },
].map((c) => ({ ...c, module: { wasm: CASES } }));

// compiled programs (src/Compiler/tests/progs) on inputs that the Lean interpreter runs in seconds
const COMPILED: readonly Case[] = [
  ["echo", "hi"],
  ["echo", ""],
  ["rev", "hello"],
  ["inc", "az"],
  ["rwt", "hello"],
  ["big", "x"],
].map(([program = "", input = ""], k) => ({ name: `${program}.${k}`, module: { program }, input }));

// functions

// the outcome that bun's host.ts gives, as Host.lean writes the model's: it prints result,
// out_of_memory or no_result, and anything else (another status, or an error) is a trap
const getRealOutcome = (wasm: string, input: string, output: string): string => {
  const said = Bun.spawnSync({ cmd: [process.execPath, HOST, wasm, input, output] })
    .stdout.toString()
    .trim();
  if (said === "result") return `result ${readFileSync(output).toString("hex")}`;
  return said === "out_of_memory" || said === "no_result" ? said : "trap";
};

// the outcome that Host.lean wrote: its name, and a result's bytes in hex
const getModelOutcome = (file: string): string => {
  const [name = "", bytes = ""] = readFileSync(file, "utf8").split("\n");
  return name === "result" ? `result ${bytes}` : name;
};

// side effects

const [workArg] = getArgs("WORK");
const work = resolve(workArg);
const at = (file: string) => join(work, file);
mkdirSync(work, { recursive: true });

run(getLower(at("main.bendtt")));
const programs = [
  ...new Set(COMPILED.flatMap((c) => ("program" in c.module ? [c.module.program] : []))),
];
programs.forEach((p) =>
  run(getBend(join(REPO, "src/Compiler/tests/progs", `${p}.bend`), at(`${p}.bendtt`))),
);
writeFileSync(
  at("write.jobs"),
  programs.map((p) => `${at(`${p}.bendtt`)}\t${at(`${p}.book`)}\n`).join(""),
);
run({
  ...getLake(["lean", "src/Book/scripts/Write.lean"], { JOBS: at("write.jobs") }),
  stdout: "ignore",
});

const cases = [...HOSTED, ...COMPILED];
cases.forEach((c) => writeFileSync(at(`${c.name}.in`), c.input));
writeFileSync(
  at("host.jobs"),
  cases
    .map((c) => {
      const module = "wasm" in c.module ? c.module.wasm : at(`${c.module.program}.book`);
      return `${module}\t${at(`${c.name}.in`)}\t${at(`${c.name}.model`)}\n`;
    })
    .join(""),
);
run(
  getLake(["lean", "src/Wasm/scripts/Host.lean"], {
    BOOK: at("main.bendtt"),
    JOBS: at("host.jobs"),
  }),
);

const failures = cases.filter((c) => {
  const wasm = "wasm" in c.module ? c.module.wasm : at(`${c.name}.model.wasm`);
  const model = getModelOutcome(at(`${c.name}.model`));
  const real = getRealOutcome(wasm, at(`${c.name}.in`), at(`${c.name}.bun`));
  const ok = model === real && (c.want === undefined || model === c.want);
  const want = c.want === undefined ? "" : `, want ${c.want}`;
  console.log(`${ok ? "ok  " : "FAIL"} ${c.name}: model ${model}, bun ${real}${want}`);
  return !ok;
});
console.log(`${failures.length} failed`);
if (failures.length > 0) process.exit(1);
