import Interpreter.Program
import Shared.Script

-- Run
-- ===
--
-- Runs the program of a .bendtt file on the bytes of a file with interp
-- (src/Interpreter/Program.lean), and writes the bytes it gives to a file.
--
--   BOOK=prog.bendtt INPUT=in OUTPUT=out [FUEL=n] lake lean src/Interpreter/scripts/Run.lean
--   JOBS=jobs [FUEL=n] lake lean src/Interpreter/scripts/Run.lean
--
-- FUEL is defaultFuel when it is not set. On a result, it writes OUTPUT, prints
-- the number of steps and exits with 0. Else it prints the error, and why there
-- is no result, and exits with 1. With JOBS, it runs each line of that file,
-- "book<TAB>input<TAB>output", in one process (each book read once): on a
-- result it writes output, else output.none with why there is no result.

open Quan Term

def defaultFuel : Nat := 100000000

-- why the end (v, n) of a run with this fuel gives no result
def noResult (bk : Book) (fuel : Nat) : Term × Nat → String
  | (v, n) =>
    if (step bk v).isSome then s!"no result within {fuel} steps"
    else if value bk v then s!"no result: after {n} steps, the value is not a list of bytes"
    else s!"no result: stuck after {n} steps"

-- the run of bk on the bytes i: its result and steps, or why there is none
def runOn (bk : Book) (fuel : Nat) (i : List UInt8) : Except String (List UInt8 × Nat) :=
  let e := steps bk fuel (start i) 0
  have _ : result bk e = interp bk fuel i := rfl
  match result bk e with
  | some r => .ok r
  | none => .error (noResult bk fuel e)

-- the books of the jobs, each read once
def booksOf (jobs : List (List String)) : IO (List (String × Book)) :=
  (jobs.filterMap (·.head?)).eraseDups.mapM fun b => return (b, ← Script.bookAt b)

def runJobs (fuel : Nat) (jobs : List (List String)) : IO Unit := do
  let books ← booksOf jobs
  for job in jobs do
    match job, job.head?.bind (List.lookup · books) with
    | [_, input, output], some bk =>
      match runOn bk fuel (← IO.FS.readBinFile input).toList with
      | .ok (r, n) =>
        IO.FS.writeBinFile output ⟨r.toArray⟩
        IO.println s!"{output}: {n} steps"
      | .error msg =>
        IO.FS.writeFile (output ++ ".none") msg
        IO.println s!"{output}: {msg}"
    | _, _ => throw (IO.userError s!"a job is book<TAB>input<TAB>output, not {job}")

def runBook : IO Unit := do
  let fuel := ((← IO.getEnv "FUEL").bind String.toNat?).getD defaultFuel
  match ← Script.jobs with
  | some jobs => runJobs fuel jobs
  | none =>
    let bk ← Script.book
    match runOn bk fuel (← IO.FS.readBinFile (← Script.env "INPUT")).toList with
    | .ok (r, n) =>
      IO.FS.writeBinFile (← Script.env "OUTPUT") ⟨r.toArray⟩
      IO.println s!"{n} steps"
    | .error msg => throw (IO.userError msg)

#eval runBook
