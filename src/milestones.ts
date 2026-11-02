// milestones.ts WORK: checks that the milestones of AGENTS.md 3.11 still hold, and stops at the
// first check that fails. WORK is a folder for what the checks write. It needs the bend submodule
// and the Lean toolchain (lake).
//
//   1. `lake build`: each theorem of the Lean library checks, with no axiom but Lean's own
//      (src/Bootstrap.lean's guard). Milestones 1 to 3.
//   2. src/Joining/scripts/Trusted.lean on the book of src/main.bend (src/Shared/lower.ts): the
//      book holds the Bend versions that the theorems are about, exactly. Milestones 2 and 3.
//   3. src/Wasm/scripts/WasmTests.lean on src/Wasm/tests/bin: no assertion fails or runs out of
//      fuel, and passing assertions run each form of instruction that the compiler emits
//      (AGENTS.md 3.9.1.3.2). Milestone 4.
//
//   bun src/milestones.ts WORK

// imports

import { mkdirSync, readFileSync } from "node:fs";
import { join, resolve } from "node:path";
import { getArgs, getBend, getLake, REPO, run } from "./Shared/shared.ts";

// constants

// the lines of WasmTests.lean's report that check 3 reads
const ALL = /^ALL: \d+ passed, (\d+) failed, \d+ unsupported, (\d+) not done$/m;
const FORMS = /^FORMS: \d+ that the compiler emits, not run by a passing test: \[(.*)\]$/m;

// side effects

const [workArg] = getArgs("WORK");
const work = resolve(workArg);
const at = (file: string) => join(work, file);
mkdirSync(work, { recursive: true });

run(getLake(["build"]));
console.log("1. ok: the Lean library checks, with no axiom but Lean's own");

run({
  cmd: [process.execPath, "Shared/lower.ts", "main.bend", at("main.bendtt")],
  cwd: join(REPO, "src"),
  stdout: "ignore",
});
run(getLake(["lean", "src/Joining/scripts/Trusted.lean"], { BOOK: at("main.bendtt") }));
console.log("2. ok: main.bend's book holds the proven Bend versions exactly");

run(getBend(join(REPO, "src/Wasm/impl.bend"), at("wasm.bendtt")));
run({
  ...getLake(["lean", "src/Wasm/scripts/WasmTests.lean"], {
    BOOK: at("wasm.bendtt"),
    MAIN: at("main.bendtt"),
    TESTS: join(REPO, "src/Wasm/tests/bin"),
    OUT: at("wasm.log"),
  }),
});
const report = readFileSync(at("wasm.log"), "utf8");
const [, failed, notDone] = report.match(ALL) ?? [];
const [, notRun] = report.match(FORMS) ?? [];
if (failed !== "0" || notDone !== "0" || notRun !== "") {
  console.error(
    `3. failed: ${failed ?? "?"} failed, ${notDone ?? "?"} not done, forms not run: ` +
      `[${notRun ?? "?"}] (see ${at("wasm.log")})`,
  );
  process.exit(1);
}
console.log("3. ok: no WASM test fails or runs out of fuel, and passing tests run each emitted form");
