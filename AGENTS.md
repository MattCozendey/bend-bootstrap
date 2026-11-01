# AGENTS

Contribution guidelines, for agents and humans alike.

This is human-written and MUST NOT be touched by ANY agent for ANY reason beyond EXPLICIT PERMISSION

This is the ultimate source of truth(over any skill or deterministic tool) for the project and every change must consult it to ensure the code or other docs are fully this-file compliant, so ANY drift must immediately pause the work and I should be communicated in detail what the blocker is and how to objectively best proceed.

## 0. Core

0.1 - If a skill does not load, read its file in `.agents/skills/`.
0.2 - Do not change any `.md` file without asking me.

## 1. Communication

1.1 - Speak the language you are spoken to; but shortly and without dropping important information in
  ASD-STE100 (or the language's equivalent), with learnings from the `i-have-adhd`.
1.2 - Use a global counter for your non-trivial questions that grows through the session. Repeat each
  open question in each response until I answer it or tell you to use common sense.

## 2. Code

These rules hold for every language.

### 2.1 Tools

2.1.1 - Do not work around a lint rule. Suppress/expect a finding only with a directive whose reason says why
  (for example, a measurement).
2.1.2 - When a deterministic tool and a skill disagree, obey the tool.
2.1.3 - Before you show me your changes, do sweeps. A sweep:
  2.1.3.1 - Reads each changed area once with `thermo-nuclear-code-quality-review` and `erasure`, and the
     changed functions with `cyclomatic-complexity`. It fixes what they find.
  2.1.3.2 - Runs the project's lint and type check until they pass.
  2.1.3.3 - Commits its in-area changes, then its cross-area changes.

  Sweep 1 reads the branch diff from its base. Before each later sweep, ask me if it reads the
  whole repo, the whole diff, or the delta (the hunks changed since the previous sweep, and their
  callers). Repeat until a sweep finds nothing to delete, no structural regression, no missed large
  simplification and no spaghetti growth. After sweep 3, stop and ask me.
2.1.4 - A file over 1000 lines can be fine. Ask me before you split one.
2.1.5 - Our own folder structure should be basically the same `experimental-bend-spec` skill states.

### 2.2 Documentation

2.2.1 - Give each fact one location. A comment must not repeat what the docs state or clearly imply.

### 2.3 Checks

2.3.1 - Ask me before you write a check. Check only a property that matters, never an implementation
  detail.
2.3.2 - Do not try to check that generated data, or a copy of a standard's text, matches its source with
  our own code. Check generated data with a test against an independent source (for example,
  another implementation, or the standard's own test vectors). That test does not replace the
  checks of the code. Tell me which copies of standard text you changed, so that I can check them.

### 2.4 Bend(Bootstrapped)

Follow the `bend2` and the `experimental-bend-spec` skills SKEPTICALLY(see 2.4.3). In this project:

2.4.1 - I don't expect you to run bend(the untrusted one) for this project at all, but if you do; you must know that before you build or test, you must run `bend version` in the shell that you build in. As of 2026-11-01, Bend does not run natively on Windows. Use WSL(note: Even with WSL, parallel code won't run on the GPU).
2.4.2 - Do not change, update or rebuild the Bend submodule.
2.4.3 - Since we are bootstrapping, the current UNTRUSTED TypeScript compiler and the Bend guide are only reference guides for ideas: don't assume things from them necessarily apply to us and our decisions. Section 3 reigns. Imports don't exist in the kernel: `bend -o` resolves the imports of our `.bend` source into one flat Book (3.5.4), so our source may use them, and our compiler never sees one (3.4.5). Don't use any bend linter(they assume untrusted code)
2.4.4 - The `bend` submodule is not our source, so it does not belong in `src/`: it stays at the repo root, where 3.1.1 points (`bend/bend2/bendtt.lean`).
  
### 2.5 TypeScript

2.5.1 - Write functional code without mutation, except when speed is a priority for a file (ask me);
  wherein any and all optimization opportunities are fair game.
2.5.2 - Lay out each file in this order, with a comment before each section (if the section is needed):
  imports, types, constants, functions, side effects.
2.5.3 - Write functions as `const` arrow functions.
2.5.4 - Inline a helper that has only one caller; extract one only when it has more than one.
2.5.5 - Name a function by what it gives: `get…` for a value (`getRecord`), `is…` or `has…` for a Bool
  (`isSpan`). Name one that gives nothing by what it does (`writeFiles`, `prune`). `try…` catches
  what it calls, and gives the failure as a value (`undefined`, or a Result) or skips it. The type,
  not the name, says that a value can be `undefined`. Constants are SCREAMING_SNAKE_CASE, types
  PascalCase, other names camelCase. `result.ts` keeps the names of its Result (`ok`, `error`,
  `wrap`, `unwrap`).
2.5.6 - Do not use barrel exports or re-exports (`export { x } from "..."`, `export * from "..."`). Import
  each name from the module that exports it.

## 3. Project

### 3.1 Kernel

3.1.1 - Kernel: `bend/bend2/bendtt.lean`: Unchanged and the source of truth.
3.1.2 - Bend: the language that the kernel gives a meaning to. Its code is a Book, as the kernel's `Book.parse` gives it. Its meaning is the kernel's `Eval`. Nothing more, nothing less. `.bend` text is a way to write Bend, through `bend -o`.

### 3.2 Our choices

The kernel says nothing about these; they are ours (some borrowed from the TypeScript compiler or `base.bend`).

3.2.1 - Program: a Book with a def named `main` (no `main`: fail). `main` takes a list of bytes and gives a list of bytes, as values of these shapes (what `bend -o` gives for `base.bend`'s `List<Word(8)>`):
  3.2.1.1 - list: `(.Nil, ())`, or `(.Con, (byte, (list, ())))`.
  3.2.1.2 - byte: 8 bits, lowest first: `(.WCon, (bit, (rest, ())))` 8 times, then `(.WNil, ())`.
  3.2.1.3 - bit: `(.False, ())` is 0, `(.True, ())` is 1.
3.2.2 - Data form: how a kernel term or Book is written as a Bend value. Each term or Book has exactly one data form (the data form is a Lean function, not a `partial def`), and no two share one (a Lean theorem proves it). 3.4.2 and 3.4.5 compare Lean and Bend through it.
3.2.3 - Start term: a run of a program on an input starts at `(main input)`, that is `App Q1 (Ref "main") input`. Why: the kernel has no entry point.
3.2.4 - Term size: the size of a term is its number of nodes: each constructor of the kernel's `Term` is one node; a name is one node. Why: the compiled code stores each name once, and `Eval` only copies names, never makes them.
3.2.5 - Program size: the size (3.2.4) of the program's data form (3.2.2). Why: the data form writes each name as its bytes and each `Var` index as a unary number, so long names and huge indices count; a plain node count misses both.

### 3.3 Goals

3.3.1 - A PURE, SELF-HOSTING BEND COMPILER, WRITTEN IN BEND, THAT I CAN TRUST. GETTING THIS RIGHT FROM THE START IS AN ABSOLUTE MUST.
  3.3.1.1 - INPUT: A BEND BOOK (3.1.2), ITS OWN BOOK INCLUDED.
  3.3.1.2 - PROMISE: THE COMPILED PROGRAM GIVES WHAT `Eval` GIVES (3.4.1).
  3.3.1.3 - PROOF: `--verdict` PROVES THE PROMISE ABOUT THE COMPILER'S OWN BOOK.
  3.3.1.4 - RUNNING IT: THE TRUST REACHES THE BINARY THAT RUNS ON THE PC. WE ACCEPT SLOWNESS, OR A BEND INTERPRETER-OR-COMPILER WRITTEN IN LEAN, ALONG THE WAY.
3.3.2 - IT CAN GROW: I CAN ADD OPTIMIZATIONS, FEATURES BEYOND BEND, NEW INTERNAL REPRESENTATIONS OR NEW TARGETS. THE LAW FOR BEND (3.4.1 AND 3.4.4) STAYS EXACTLY AS IT IS AND MUST STILL PASS `--verdict`. SO OUR COMPILER ALWAYS STAYS A PROVEN BEND COMPILER.
3.3.3 - TARGETS: OUR LAWS HOLD FOR ANY TARGET WHOSE MEANING IS WRITTEN IN BEND. 3.8 LISTS THEM.

### 3.4 Invariants

3.4.1 - FOR EVERY PROGRAM, NOT ONLY THE ONES THAT THE KERNEL ACCEPTS (SO WE NEED NO BEND VERSION OF THE CHECKER): IF THE COMPILED PROGRAM, RUN BY ITS TARGET'S MEANING (ITS BEND VERSION: 3.8), GIVES A RESULT, IT IS THE RESULT THAT `Eval` GIVES (`Eval` GIVES AT MOST ONE RESULT, AFTER ONE NUMBER OF STEPS: A LEAN THEOREM PROVES IT). IF `Eval` GIVES A RESULT, THE COMPILED PROGRAM GIVES IT OR RUNS OUT OF MEMORY; WITH ENOUGH MEMORY (3.4.4), IT ALWAYS GIVES IT. SO OUR COMPILER DOES NOT CHECK TYPES: A PROGRAM THAT THE KERNEL REJECTS MAY RUN FOREVER OR GET STUCK, AND ITS OWN LAWS HOLD ONLY AFTER `--verdict` ACCEPTS IT.
3.4.2 - THE BEND VERSION OF `Eval`, WHICH THE LAWS OF 3.7.4 USE, GIVES WHAT THE REAL ONE GIVES (EACH TERM AS ITS DATA FORM: 3.2.2), AFTER THE SAME NUMBER OF STEPS, IN BOTH DIRECTIONS (NO EXTRA RESULT, NO MISSING RESULT). A LEAN THEOREM PROVES IT.
3.4.3 - A RUN OF A PROGRAM (3.2.1) STARTS AT ITS START TERM (3.2.3). THE LIST OF BYTES THAT IT GIVES IS ITS RESULT, AND 3.4.1 HOLDS FOR EVERY INPUT. IF `Eval`'S FINAL VALUE IS NOT A LIST OF BYTES, BOTH SIDES COUNT AS "NO RESULT".
3.4.4 - "ENOUGH MEMORY": EACH TARGET'S LAW FIXES A FORMULA F OF MEASURES THAT THE COMPILER CAN'T CHANGE: THE PROGRAM'S SIZE (3.2.5), THE SIZE (3.2.4) OF THE LARGEST TERM THAT `Eval` REACHES BEFORE IT GIVES THE RESULT (THE INPUT IS IN THE FIRST TERM), AND THE NUMBER OF STEPS. WITH AT LEAST F BYTES, THE COMPILED PROGRAM GIVES THE RESULT. THE COMPILER CAN'T CHOOSE F. A TARGET MAY ADD A STRONGER F LATER, NEXT TO ITS FIRST ONE. WHEN F IS MORE THAN THE TARGET CAN HAVE, THE LAW PROMISES NOTHING FOR THAT RUN.
3.4.5 - OUR COMPILER DOES NOT READ .bendtt TEXT. ITS INPUT IS THE BOOK THAT THE KERNEL'S OWN PARSER (`Book.parse`) GIVES FOR THAT TEXT, WRITTEN AS A LIST OF BYTES (3.2.1) BY THE LEAN WRITER (NOT A `partial def`). FOR EVERY BOOK, THE BEND READER, WHICH THE LAWS OF 3.7.4 USE, GIVES BACK EXACTLY THAT BOOK'S DATA FORM (3.2.2) FROM THE BYTES THAT THE LEAN WRITER WRITES FOR IT. A LEAN THEOREM PROVES IT.

### 3.5 Trusted

3.5.1 - Lean itself.
3.5.2 - The LEAN-VALIDATED, PROVEN-SOUND kernel (3.1.1) is the definition of Bend. What it says a program computes IS what the program actually computes. IT IS FIXED: WE CANNOT TOUCH IT IN ANY WAY WHATSOEVER.
3.5.3 - From 3.5.2 follows that every proof in a Bend program that `--verdict` accepts is true (`--verdict` runs the kernel)
3.5.4 - The .bendtt text produced from a .bend file via `bend -o` means what said .bend file says. This is a named exception to 3.6.1, only so that the laws we read in `.bend` are the laws that `--verdict` proves.
3.5.5 - What each target's entry in 3.8 trusts.

### 3.6 Untrusted

3.6.1 - The current Bend compiler written in TypeScript.
3.6.2 - A checker result without --verdict.
3.6.3 - OUR OWN BOOTSTRAP CODE UNTIL IT'S SOMEHOW PROOF-VALIDATED.

### 3.7 Steps

3.7.1 - We must write the BEND VERSION of `Eval` and the LEAN PROOF of 3.4.2. This is because Bend can't use Lean's `Eval`, so 3.7.4 can only state its laws through a version. Without this proof, a wrong version makes 3.7.4 prove the wrong thing.
3.7.2 - We must write the LEAN WRITER, the BEND READER and the LEAN PROOF of 3.4.5. This is because the kernel's parser is made of `partial def`s, so no Lean theorem can say what it returns, and the kernel is fixed (3.5.2): a Bend version of the parser could never be proven to read a text as the kernel does. Without this proof, our compiler could compile a different book than the one the kernel read.
3.7.3 - For each target, we must write the BEND VERSION OF ITS MEANING (3.8), so that the laws of 3.7.4 can say what a compiled program gives. This is because the target's spec is not written in Bend.
3.7.4 - We must write >OUR OWN< compiler and BEND LAWS IN BEND'S SYNTAX about it, so that `--verdict` proves that it is correct by the rules of `Eval`. This is because our compiler is Bend code, and a Bend proof can talk about it directly(a Lean proof could only reason about it from the outside).
3.7.5 - We must write a BEND INTERPRETER IN LEAN, with a Lean proof that it gives what `Eval` gives, so that we have a trusted way to RUN >OUR OWN< compiler (it runs any Bend program, ours included). This is because `Eval` is a list of rules, not a program (it can't run anything), we don't trust the current compiler, and our compiler can't run itself before it is compiled. It needs no earlier step.
3.7.6 - We must write a LEAN PROOF THAT JOINS 3.7.4 AND 3.7.5: when the interpreter runs >OUR OWN< compiler, the bytes it writes follow the laws of 3.7.4 (it works for any Bend program and its laws, ours included). This is because 3.7.4 only says that the compiler is correct by the rules of `Eval`, and 3.7.5 only says that the interpreter follows `Eval`. Without this proof, nothing says that the laws hold for what actually runs on the PC.
3.7.7 - SELF-HOSTING: the interpreter (3.7.5) runs >OUR OWN< compiler on its own Book, and the binary that it writes becomes our compiler. This is because 3.3.1 asks for a self-hosting compiler whose trust reaches the binary that runs on the PC (3.3.1.4): by 3.7.6 and 3.4.1, that binary gives what our compiler gives by `Eval`, so from then on it compiles any Bend program, itself included, without the interpreter.
3.7.8 - For each target, we must do the steps that its entry in 3.8 lists.

### 3.8 Targets

Everything in a target's entry is ours.

3.8.1 - WASM (WEBASSEMBLY):
  3.8.1.1 - WHY: IT IS SMALL AND HAS AN OFFICIAL FORMAL SPEC. NATIVE MACHINE CODE HAS NO COMPACT FORMAL SPEC, AND C'S MEANING IS HUGE AND FULL OF UNDEFINED BEHAVIOR.
  3.8.1.2 - MEANING: Our Bend version of WASM's meaning: only the part of WASM that our compiler uses, its binary format included.
  3.8.1.3 - TRUSTED: A WASM engine follows the WASM spec. Our Bend version of WASM's meaning is reviewed against the WASM spec and tested with the spec's official test suite. It is not proven, because we know of no Lean or Bend version of the spec. This is a named exception to 3.6.3.
  3.8.1.4 - MEMORY (3.4.4): F = 64 × (THE PROGRAM'S SIZE + THE SIZE OF THE LARGEST TERM (3.4.4)) + 2^24 BYTES. THE COMPILED CODE MUST REUSE MEMORY: IT FREES EVERY CELL THAT CAN NO LONGER BE REACHED. ONLY THE PROGRAM'S IMAGE AND THE INPUT'S BYTE CACHE (AT MOST 6144 CELLS) ARE NEVER FREED. THE TARGET CAN HAVE AT MOST 4 GiB (32-BIT ADDRESSES).
  3.8.1.5 - STACK: THE COMPILED CODE KEEPS ITS STACK IN WASM MEMORY, NOT ON THE ENGINE'S CALL STACK. THE WASM SPEC LETS AN ENGINE STOP A PROGRAM WHEN THE ENGINE'S CALL STACK RUNS OUT, SO MEMORY MUST BE THE ONLY RESOURCE LIMIT (3.4.4).
  3.8.1.6 - STEP: We must write a LEAN VERSION OF THE OFFICIAL WASM SEMANTICS of the subset that our compiler uses, TRANSLATED BY A PROGRAM FROM THE SPEC'S OWN FORMAL SOURCE (SpecTec), and a LEAN PROOF that our Bend version of WASM gives what it gives. This is because our Bend version is only reviewed and tested (3.8.1.3). With this proof we trust the spec's SpecTec source and the translator instead. The official tests stay, for historical reasons.

### 3.9 Notes

3.9.1 - PROOF QUALITY DOESN'T MATTER UNLESS PROOFS ARE SO SLOW THEY BLOCK. PROOFS DON'T TAKE PART IN REVIEW SWEEPS UNLESS I TELL YOU TO. LAWS AND THEOREMS (BEND AND LEAN), AND THE DEFINITIONS THEY USE, ON THE OTHER HAND, SHOULD ALWAYS BE DOUBLE-QUESTIONED TO ENSURE THEY REALLY REALLY MATCH MY INTENT; THEN THE LAWS AND THEOREMS ARE PROVEN. THIS DOES NOT MEAN OVERDO LAWS. WE WANT ENOUGH LAWS FOR THE COMPILER TO BE EXACTLY AS SAFE AS IT NEEDS TO BE, NOT MORE NOT LESS.
3.9.2 - EFFECTS LATER: MODEL THEM AS PURE DATA (`main` GIVES REQUESTS, A HOST ANSWERS), SO `Eval` STILL GIVES THEM A MEANING.
