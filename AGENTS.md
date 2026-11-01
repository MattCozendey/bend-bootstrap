# AGENTS

Contribution guidelines, for agents and humans alike.

This is human-written and MUST NOT be touched by ANY agent for ANY reason beyond EXPLICIT PERMISSION

This is the ultimate source of truth(over any skill or deterministic tool) for the project and every change must consult it to ensure the code or other docs are fully this-file compliant, so ANY drift must immediately pause the work and I should be communicated in detail what the blocker is and how to objectively best proceed.

## 0. Core

- If a skill does not load, read its file in `.agents/skills/`.
- Do not change any `.md` file without asking me.

## 1. Communication

- Speak the language you are spoken to; but shortly and without dropping important information in
  ASD-STE100 (or the language's equivalent), with learnings from the `i-have-adhd`.
- Use a global counter for your non-trivial questions that grows through the session. Repeat each
  open question in each response until I answer it or tell you to use common sense.

## 2. Code

These rules hold for every language.

### Tools

- Do not work around a lint rule. Suppress/expect a finding only with a directive whose reason says why
  (for example, a measurement).
- When a deterministic tool and a skill disagree, obey the tool.
- Before you show me your changes, do sweeps. A sweep:
  1. Reads each changed area once with `thermo-nuclear-code-quality-review` and `erasure`, and the
     changed functions with `cyclomatic-complexity`. It fixes what they find.
  2. Runs the project's lint and type check until they pass.
  3. Commits its in-area changes, then its cross-area changes.

  Sweep 1 reads the branch diff from its base. Before each later sweep, ask me if it reads the
  whole repo, the whole diff, or the delta (the hunks changed since the previous sweep, and their
  callers). Repeat until a sweep finds nothing to delete, no structural regression, no missed large
  simplification and no spaghetti growth. After sweep 3, stop and ask me.

- A file over 1000 lines can be fine. Ask me before you split one.

### Documentation

- Give each fact one location. A comment must not repeat what the docs state or clearly imply.

### Checks

- Ask me before you write a check. Check only a property that matters, never an implementation
  detail.
- Do not try to check that generated data, or a copy of a standard's text, matches its source with
  our own code. Check generated data with a test against an independent source (for example,
  another implementation, or the standard's own test vectors). That test does not replace the
  checks of the code. Tell me which copies of standard text you changed, so that I can check them.

### Bend

Follow the `bend2` and the `experimental-bend-spec` skills SKEPTICALLY(see point 3). In this project:

- I don't expect you to run bend(the untrusted one) for this project at all, but if you do; you must know that before you build or test, you must run `bend version` in the shell that you build in. As of 2026-11-01, Bend does not run natively on Windows. Use WSL(note: Even with WSL, parallel code won't run on the GPU).
- Do not change, update or rebuild the Bend submodule.
- Since we are bootstrapping, don't assume things from the bend guide necessarily apply to us and our decisions. The plan reigns.
  
### TypeScript

- Write functional code without mutation, except when speed is a priority for a file (ask me);
  wherein any and all optimization opportunities are fair game.
- Lay out each file in this order, with a comment before each section (if the section is needed):
  imports, types, constants, functions, side effects.
- Write functions as `const` arrow functions.
- Inline a helper that has only one caller; extract one only when it has more than one.
- Name a function by what it gives: `get…` for a value (`getRecord`), `is…` or `has…` for a Bool
  (`isSpan`). Name one that gives nothing by what it does (`writeFiles`, `prune`). `try…` catches
  what it calls, and gives the failure as a value (`undefined`, or a Result) or skips it. The type,
  not the name, says that a value can be `undefined`. Constants are SCREAMING_SNAKE_CASE, types
  PascalCase, other names camelCase. `result.ts` keeps the names of its Result (`ok`, `error`,
  `wrap`, `unwrap`).
- Do not use barrel exports or re-exports (`export { x } from "..."`, `export * from "..."`). Import
  each name from the module that exports it.

## 3. Project

