# AGENTS

Contribution guidelines, for agents and humans alike.

This is human-written and MUST NOT be touched by ANY agent for ANY reason beyond EXPLICIT
PERMISSION.

This is the ultimate source of truth (over any skill or deterministic tool) for the project and
every change must consult it to ensure the code or other docs are fully this-file compliant, so ANY
drift must immediately pause the work and I should be communicated in detail what the blocker is and
how to objectively best proceed.

## 0. Core

- **0.1** If a skill does not load, read its file in `.agents/skills/`.
- **0.2** Do not change any `.md` file without asking me.

## 1. Communication

- **1.1** Speak the language you are spoken to; but shortly and without dropping important
  information in ASD-STE100 (or the language's equivalent), with learnings from the `i-have-adhd`.
- **1.2** Use a global counter for your non-trivial questions that grows through the session. Repeat
  each open question in each response until I answer it or tell you to use common sense.

## 2. Code

These rules hold for every language.

### 2.1 Tools

- **2.1.1** Do not work around a lint rule. Suppress/expect a finding only with a directive whose
  reason says why (for example, a measurement).
- **2.1.2** When a deterministic tool and a skill disagree, obey the tool.
- **2.1.3** Before you show me your changes, do sweeps. A sweep:
  - **2.1.3.1** Reads each changed area once with `thermo-nuclear-code-quality-review` and
    `erasure`, and the changed functions with `cyclomatic-complexity`. It fixes what they find.
  - **2.1.3.2** Runs the project's lint and type check until they pass.
  - **2.1.3.3** Commits its in-area changes, then its cross-area changes.

  Sweep 1 reads the branch diff from its base. Before each later sweep, ask me if it reads the whole
  repo, the whole diff, or the delta (the hunks changed since the previous sweep, and their
  callers). Repeat until a sweep finds nothing to delete, no structural regression, no missed large
  simplification and no spaghetti growth. After sweep 3, stop and ask me.
- **2.1.4** A file over 1000 lines can be fine. Ask me before you split one.
- **2.1.5** Our own folder structure should be basically the same `experimental-bend-spec` skill
  states.

### 2.2 Documentation

- **2.2.1** Give each fact one location. A comment must not repeat what the docs state or clearly
  imply.

### 2.3 Checks

- **2.3.1** Ask me before you write a test/check/invariant, and only propose properties that matter over implementation details. Examples of implementation details: whether a list we wrote sorted really is sorted; whether generated data really matches what we generated; etc. Use common sense.
- **2.3.2** Proof quality doesn't matter unless their checking is so slow it blocks you, and they don't take part in review sweeps unless I explicitly tell you to. What DOES matter, and matters A LOT is the invariants/theorems/laws as stated(they must ALWAYS be double-questioned) to ensure they REALLY match my intent on all fronts. I want the rules I need - no more; no less. Don't overdo and check trivial properties I do not care for.

### 2.4 Bend (Bootstrapped)

Follow the `bend2` and the `experimental-bend-spec` skills SKEPTICALLY (see 2.4.3). In this project:

- **2.4.1** I don't expect you to run bend (the untrusted one) for this project at all, but if you
  do; you must know that before you build or test, you must run precisely the one inside the `bend` submodule, via WSL(if you're on Windows). FYI: Parallel code won't run on the GPU if you're on windows, WSL or not.
- **2.4.2** Do not change, update or rebuild the Bend submodule.
- **2.4.3** Since we are bootstrapping, the current UNTRUSTED TypeScript compiler and the Bend guide
  are only reference guides for ideas: don't assume things from them necessarily apply to us and our
  decisions. Section 3 reigns. Imports don't exist in the kernel: `bend -o` resolves the imports of
  our `.bend` source into one flat Book (3.7.3), so our source may use them, and our compiler never
  sees one (3.6.4). Don't use any bend linter (they assume untrusted code)
- **2.4.4** The `bend` submodule is not our source, so it does not belong in `src/`: it stays at the
  repo root, where 3.2.1 points (`bend/bend2/bendtt.lean`).

### 2.5 TypeScript

- **2.5.1** Write functional code without mutation, except when speed is a priority for a file (ask
  me); wherein any and all optimization opportunities are fair game.
- **2.5.2** Lay out each file in this order, with a comment before each section (if the section is
  needed): imports, types, constants, functions, side effects.
- **2.5.3** Write functions as `const` arrow functions.
- **2.5.4** Inline a helper that has only one caller; extract one only when it has more than one.
- **2.5.5** Name a function by what it gives: `get…` for a value (`getRecord`), `is…` or `has…` for
  a Bool (`isSpan`). Name one that gives nothing by what it does (`writeFiles`, `prune`). `try…`
  catches what it calls, and gives the failure as a value (`undefined`, or a Result) or skips it.
  The type, not the name, says that a value can be `undefined`. Constants are SCREAMING_SNAKE_CASE,
  types PascalCase, other names camelCase. `result.ts` keeps the names of its Result (`ok`, `error`,
  `wrap`, `unwrap`).
- **2.5.6** Do not use barrel exports or re-exports (`export { x } from "..."`, `export * from
  "..."`). Import each name from the module that exports it.

## 3. Project

### 3.1 In short

We build a compiler for Bend, written in Bend, that we can trust without trusting its code. The
kernel says what every Bend program means. The compiler comes with laws: its output gives exactly
what the kernel says the program gives. The kernel itself checks those laws (`--verdict`). Lean
theorems connect the remaining pieces, so that the trust reaches the binary that runs on the PC.

### 3.2 Words from the kernel

The kernel fixes these. We cannot change them.

- **3.2.1** Kernel: the file `bend/bend2/bendtt.lean`, at the commit that the `bend` submodule
  pins. It is the only source of truth about Bend.
- **3.2.2** Book: a list of defs. Each def has a name, a type and a body.
- **3.2.3** Bend: the language that the kernel gives a meaning to. Its code is a Book, as the
  kernel's `Book.parse` reads it from `.bendtt` text. Nothing more, nothing less: what the kernel
  gives no meaning to (for example effects, or primitives with no body) is not Bend. We write Bend
  as `.bend` text, which `bend -o` turns into `.bendtt` text.
- **3.2.4** `Eval`: the kernel's rules for running a term, one step at a time. It is the meaning of
  Bend. `Eval` does not check types: it runs any term until it reaches a value or gets stuck.
- **3.2.5** `--verdict`: runs the kernel's checker on a Book. Only "ALL PROOFS CHECK" is an
  acceptance. Anything else, a run out of fuel included, proves nothing.

### 3.3 Words we chose

The kernel says nothing about these. Each says why we chose it. Some are borrowed from the
TypeScript compiler or from `base.bend`.

- **3.3.1** Bytes: a list of bytes is a value of these shapes (the shapes that `bend -o` gives for
  `base.bend`'s `List<Word(8)>`):
  - **3.3.1.1** list: `(.Nil, ())`, or `(.Con, (byte, (list, ())))`.
  - **3.3.1.2** byte: 8 bits, lowest first: `(.WCon, (bit, (rest, ())))` 8 times, then
    `(.WNil, ())`.
  - **3.3.1.3** bit: `(.False, ())` is 0, `(.True, ())` is 1.
- **3.3.2** Program: a Book with a def named `main`. The compiler compiles a Book without `main`
  too: its module gives no result.
- **3.3.3** Run: a run of a program on an input (a list of bytes) is what `Eval` does from the start
  term `(main input)`, that is `App Q1 (Ref "main") input`. Why: the kernel has no entry point.
- **3.3.4** Result: if the run reaches a value that is a list of bytes, that list is the result.
  Any other end (a different value, a stuck term, a run that never ends) is "no result".
- **3.3.5** Data form: how a kernel term or Book is written as a Bend value, so that Bend code can
  work on it. It is a Lean function (not a `partial def`), so each term or Book has exactly one data
  form; 3.6.2 proves that no two share one.
- **3.3.6** Bend version of X: a Bend function that does what X does, where X is written in another
  language (for example `Eval`, or a target's meaning). Each one comes with a Lean theorem that it
  agrees with X.
- **3.3.7** Term size: the number of nodes of a term. Each constructor of the kernel's `Term` is one
  node; a name is part of its node. Why: our machine shares only what a copy leaves unchanged, so it
  may need a cell for each node; a count of distinct subterms would force it to merge equal values
  (3.4.2 allows such a stronger F later). `Eval` never makes a name, it only copies names from the
  program, and the program size (3.3.8) already counts each name's bytes.
- **3.3.8** Program size: the term size of the program's data form. Why: the data form writes each
  name as its bytes and each `Var` index as a unary number, so long names and huge indices count. A
  plain node count misses both. The program is the Book as the compiler gets it: the pruned Book
  (3.6.8).
- **3.3.9** Target: a machine language that we compile to, such as WASM. Its meaning is written as
  a Bend version (3.3.6). 3.9 lists the targets.
- **3.3.10** Memory formula F: the number of bytes that a target promises is enough for a run. Each
  target fixes its own F (3.9). F may only use the program size, the term size of the largest term
  of the run (the input is in the first term), and the number of steps of the run. The compiler
  cannot change any of these.

### 3.4 Goals

- **3.4.1** A pure, self-hosting Bend compiler, written in Bend, that we can trust. Getting this
  right from the start is a must.
  - **3.4.1.1** Input: any Program (3.3.2), the compiler's own Book included.
  - **3.4.1.2** Promise: the laws (3.6) hold, and `--verdict` proves them about the compiler's own
    Book.
  - **3.4.1.3** Running it: the trust reaches the binary that runs on the PC. We accept slowness, or
    a Bend interpreter or compiler written in Lean, on the way there.
  - **3.4.1.4** Self-hosting fits: on each target, the compiled compiler compiles itself within the
    target's limit. This is measured, not proven: its F may be above the limit (3.4.2).
- **3.4.2** It can grow. We can add optimizations, features beyond Bend, new internal
  representations and new targets. The laws stay exactly as they are and must still pass
  `--verdict`. A target may add a stronger F later, next to its first one. So the compiler always
  stays a proven Bend compiler.

### 3.5 The trust chain

How a `.bend` file becomes a trusted binary. Each link is either trusted (3.7) or proven.

1. Our `.bend` source becomes `.bendtt` text through `bend -o`. Trusted: 3.7.3.
2. The kernel reads that text as a Book (`Book.parse`) and checks it (`--verdict`). Trusted:
   3.7.2.
3. The Lean writer writes the pruned Book (3.6.8) as a list of bytes; the Bend reader reads it back
   as that Book's data form. Proven: 3.6.8 and 3.6.4.
4. The compiler turns the data form into the target's bytes. Proven: the laws (3.6), through the
   Bend version of `Eval` (3.6.3) and of the target's meaning (3.9).
5. The Lean interpreter runs the compiler. Proven: 3.6.5, and joined to the laws by 3.6.6.
6. The interpreter compiles the compiler itself; that binary becomes our compiler (3.8.7).
7. A real engine and the host run the binary. Trusted: the target's entry in 3.9.

### 3.6 Laws and theorems

The laws are written in Bend, and `--verdict` proves them. They hold for every program, not only
for the ones that the kernel accepts. So the compiler needs no Bend version of the kernel's checker,
and it does not check types: a program that the kernel rejects may run forever or get stuck, as it
does with `Eval`. A program's own laws hold only after `--verdict` accepts that program.

- **3.6.1** The laws. In each, the compiled program runs by its target's Bend version, and `Eval`
  runs through its Bend version (3.6.3). By 3.6.7, `Eval` gives at most one result.
  - **3.6.1.1** `no_wrong_result`: if the compiled program gives a result, it is the result that
    `Eval` gives.
  - **3.6.1.2** `no_other_failure`: if `Eval` gives a result, the compiled program gives it, or runs
    out of memory.
  - **3.6.1.3** `enough_memory`: if `Eval` gives a result and the compiled program has at least F
    bytes of memory (3.3.10), and the engine says yes each time the program asks for more memory up
    to that limit, it gives that result. When F is more than the target can have, this law promises
    nothing for that run.
  - **3.6.1.4** `in_subset`: the compiled program, run by its target's Bend version, never leaves
    the subset that the version covers (for WASM: it is never `unsupported`). Why: the target's
    trust (3.9.1.3) covers only the subset; a module outside it could give a result that no law
    sees.

The theorems are written in Lean, because only Lean can see the kernel's `Eval` and its parser.

- **3.6.2** Data form: no two terms or Books share a data form. Why: the compiler only sees data
  forms. If two programs shared one, the compiler would treat them the same, while `Eval` could
  treat them differently.
- **3.6.3** Bend version of `Eval`: it gives what `Eval` gives, after the same number of steps, in
  both directions (no extra result, no missing result), each term as its data form. Why: Bend
  cannot see Lean's `Eval`, so the laws can only speak about it through a Bend version. A wrong
  version would make `--verdict` prove the wrong thing.
- **3.6.4** Reader: for every Book, the Bend reader gives back exactly the Book's data form from
  the bytes that the Lean writer writes for it. Why: the compiler does not read `.bendtt` text. The
  kernel's parser is made of `partial def`s, so no theorem can say what it returns, and a Bend
  version of it could never be proven to read text as the kernel does. Without this theorem, the
  compiler could compile a different Book than the one the kernel read.
- **3.6.5** Interpreter: the Lean interpreter gives what `Eval` gives. Why: `Eval` is a list of
  rules, not a program, so it cannot run anything; we do not trust the TypeScript compiler; and our
  compiler cannot run itself before it is compiled.
- **3.6.6** Joining: when the interpreter runs our compiler, the bytes that it writes follow the
  laws. Why: the laws only speak about the compiler by the rules of `Eval`, and 3.6.5 only speaks
  about the interpreter. Without this theorem, nothing says that the laws hold for what really runs.
- **3.6.7** One result: a run of `Eval` reaches at most one value, after one number of steps. Why:
  the laws speak of "the result" of a run.
- **3.6.8** Pruning: the pruned Book of a Book (the Book, less defs that a run from `main` cannot
  call) gives what the Book gives, after the same number of steps. Why: a Book holds its
  proofs, which `Eval` never runs, so the compiler need not read them. Without pruning, the
  compiler's own Book (about 99% proofs) is too large for the interpreter and the targets to
  compile it.

### 3.7 What we trust

Everything not listed here is untrusted until it is proven. For example: the TypeScript compiler, a
checker result without `--verdict`, and all of our own code.

- **3.7.1** Lean: its kernel, which checks our theorems, and its compiler and runtime (with the C
  compiler that its toolchain ships), which run the kernel's parser and checker (3.2.5) and the
  steps of 3.8.7 (the writer, the pruning, the Trusted check and the interpreter), whose answers are
  the premises of 3.6.6 and 3.8.7.
- **3.7.2** The kernel (3.2.1). It is proven sound in Lean: what it says a program computes is what
  the program computes. It is fixed: we never touch it. So every proof that `--verdict` accepts is
  true.
- **3.7.3** `bend -o`: the `.bendtt` text that it writes means what the `.bend` file says. This is
  the only trust we give the TypeScript compiler, and only so that the laws we read in `.bend` are
  the laws that `--verdict` proves.
- **3.7.4** Whatever each target's entry in 3.9 trusts.

### 3.8 Steps

In order. Each step says what to write and what to prove.

- **3.8.1** The Bend version of `Eval`, and its theorem (3.6.3).
- **3.8.2** The Lean writer and the Bend reader, and their theorem (3.6.4); the pruning, and its
  theorem (3.6.8).
- **3.8.3** For each target, the Bend version of its meaning (3.9).
- **3.8.4** The compiler, and its laws (3.6.1), proven by `--verdict`. The laws are in Bend because
  the compiler is Bend code: a Bend proof speaks about it directly, while a Lean proof could only
  speak about it from the outside.
- **3.8.5** The Lean interpreter, and its theorem (3.6.5). It needs no earlier step.
- **3.8.6** The joining theorem (3.6.6).
- **3.8.7** Self-hosting: the interpreter runs the compiler on the compiler's own pruned Book, and
  the binary that it writes becomes our compiler. One run reads the `.bendtt` text of `bend -o`
  once, and checks, prunes, writes and interprets that same Book. By 3.6.6, the laws and 3.6.8, that binary gives
  what our compiler's Book gives by `Eval`. From then on, it compiles any program, itself
  included, without the interpreter(we keep the interpreter tho for posterity).
- **3.8.8** For each target, the extra steps that its entry lists.

### 3.9 Targets

Everything in a target's entry is our choice. Each entry has the same parts:

- Why: why this target.
- Meaning: what our Bend version of its meaning covers.
- Trusted: what we trust about it, and why.
- Memory: its F (3.3.10), its limit, and the rules that its compiled code follows to stay within F.
- Extra steps: what makes it more trusted later.

The entries:

- **3.9.1** WASM (WebAssembly)
  - **3.9.1.1** Why: it is small and has an official formal spec. Native machine code has no
    compact formal spec, and C's meaning is huge and full of undefined behavior.
  - **3.9.1.2** Meaning: our Bend version covers only the subset: the part of WASM that the
    compiler emits, its binary format included. It takes these parts in their general forms, so
    that the official tests can run, except for these narrowings: no instruction after a `br` in
    its block, at most one data segment, no memory maximum, ASCII names, and 32-bit numbers where
    3.0 reads 64 bits. A function may have any number of i32 results. Where the spec lets the
    engine choose (the most memory that it gives, and which memory grows it refuses), the engine's
    choices are an input of our version, and the laws hold for every choice, also for answers to
    grows that never end. The version is WASM
    3.0, at the commit `6057acdb` of the official spec (github.com/WebAssembly/spec), which the
    tests pin.
  - **3.9.1.3** Trusted, and not proven, on the modules of the subset (3.9.1.2):
    - **3.9.1.3.1** A WASM engine follows the WASM spec.
    - **3.9.1.3.2** Our Bend version gives what the spec gives, for each engine choice (3.9.1.2).
      We know of no Lean or Bend version of the spec, so it is reviewed against the spec and tested
      against it: each official test of the pinned commit that stays inside the subset passes, and
      each instruction and module part of the subset, in each form that the compiler emits, is run
      by a passing test. Where no official test runs one, our own test does, and the spec's
      reference interpreter at the pinned commit gives its expected result. Where an engine choice
      matters (a refused grow), our own test takes its expected result from the spec's rule, since
      the reference interpreter never refuses.
    - **3.9.1.3.3** The host follows the Host section of our Bend version. The host is the program
      that runs a compiled module on the PC: it gives the module its input, calls it, and reads its
      output. The WASM spec does not define it; we do. It is reviewed against the Host section.
    - **3.9.1.3.4** Our Bend version is part of what the laws say, so it is fixed as they are: it
      changes only with my approval, and each change runs the WASM tests (`src/milestones.ts`,
      steps 3 to 5) again on the same commit.

    3.9.1.3.2 and 3.9.1.3.3 are named exceptions to "all of our own code is untrusted" (3.7).
  - **3.9.1.4** Memory: F = 64 × (program size + term size of the largest term) + 2^24 bytes. The
    limit is 4 GiB (32-bit addresses). To stay within F, the compiled code:
    - frees every cell that it can no longer reach; only the program's image and the input's byte
      cache (at most 6144 cells) are never freed;
    - stores each name once, and a copy of a term refers to it, so copies never repeat a name's
      bytes;
    - keeps its stack in WASM memory, not on the engine's call stack, because the spec lets an
      engine stop a program when its call stack runs out. Memory must be the only limit.

    Known gap: an engine may refuse a module that is too large (browser engines refuse one over 1
    GiB). Our version takes a module of any size, so for such a program `enough_memory` promises a
    result that the engine does not give. The result is never wrong: the engine gives none.
  - **3.9.1.5** Extra steps: a Lean version of the official WASM semantics of the subset, made by a
    program from the spec's own formal source (SpecTec), and a Lean proof that our Bend version
    gives what it gives. Then we trust SpecTec's source and the translator instead of our review.
    The official tests stay, for historical reasons.

### 3.10 Notes

- **3.10.1** Effects later: model them as pure data (`main` gives requests, a host answers), so
  that `Eval` still gives them a meaning.
- **3.10.2** TODO: `run.ts` caches the answers of the Lean interpreter (`.cache/interp/`), by a
  hash of the interpreter's code, the book, the input and the fuel. The cache is for development
  only: it is a file that anyone can change, so it is not trusted (3.7). The run of 3.8.7 must run
  fresh (`FRESH=1`), and so must any run whose answer we use as proof.
- **3.10.3** TODO, after the bootstrap: word cells. A word cell holds a whole word of at most 32
  bits, where the compiled code now uses 3 cells for each bit. With them, the compiled compiler
  compiling itself needs about 0.7 GB, where it now needs about 4.6 GB, so 3.4.1.4 can hold on WASM.
  The proofs of the machine must then cover word cells.
- **3.10.4** TODO, after the bootstrap: native U32 operations in the compiled code. A call of a Base
  U32 operation, in a book that holds it exactly as Base writes it, runs as WASM instructions, not
  bit by bit. It only makes the compiled code faster.

### 3.11 Milestones

1. **WE HAVE A BEND INTERPRETER, WRITTEN FULLY IN LEAN. PROVEN.**
2. **WE HAVE EVAL WRITTEN IN BEND. PROVEN TO MATCH THE KERNEL'S EVAL, STEP FOR STEP.**
3. **WE HAVE A BOOK READER WRITTEN IN BEND. PROVEN TO GET BACK EXACTLY THE BOOK THAT LEAN WROTE.**
4. **WE HAVE A WASM INTERPRETER FOR THE SUBSET, WRITTEN IN BEND. NOT PROVEN: REVIEWED AND TESTED AS 3.9.1.3 ASKS.**