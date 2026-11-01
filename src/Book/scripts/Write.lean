import Shared.DataForm
import Shared.Script

-- Write
-- =====
--
-- Writes the bytes of the book of a .bendtt file, as the Lean writer of
-- src/Shared/DataForm.lean writes them (AGENTS.md 3.6.4): the input of the
-- compiler of 3.8.4.
--
--   BOOK=prog.bendtt OUTPUT=prog.book lake lean src/Book/scripts/Write.lean
--   JOBS=jobs lake lean src/Book/scripts/Write.lean
--
-- With JOBS, it writes each line of that file, "book<TAB>output", in one process.

-- writes the bytes of the book at path to output
def writeTo (path output : String) : IO Unit := do
  let bs := write (← Script.bookAt path)
  IO.FS.writeBinFile output ⟨bs.toArray⟩
  IO.println s!"{output}: {bs.length} bytes"

def writeBook : IO Unit := do
  match ← Script.jobs with
  | some jobs =>
    for job in jobs do
      match job with
      | [path, output] => writeTo path output
      | _ => throw (IO.userError s!"a job is book<TAB>output, not {job}")
  | none => writeTo (← Script.env "BOOK") (← Script.env "OUTPUT")

#eval writeBook
