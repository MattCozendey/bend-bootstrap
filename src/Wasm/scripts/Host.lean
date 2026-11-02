import Interpreter.Run
import Shared.DataForm
import Shared.Script

-- Host
-- ====
--
-- A test of kind a (bend2 skill): the model's Host section (Wasm.run of
-- src/Wasm/impl.bend), run by the Lean interpreter, against a real host
-- (src/Compiler/tests/host.ts in bun's engine). src/Wasm/tests/agree.ts runs
-- both on the same modules and inputs, and compares them.
--
--   BOOK=<main.bendtt> JOBS=<file> lake lean src/Wasm/scripts/Host.lean
--
-- BOOK is the book of src/main.bend (src/Shared/lower.ts), which holds the
-- model and the compiler. A job is a line of three files, separated by tabs: a
-- module, an input and an output. A module that ends in .book holds a
-- program's book (src/Book/scripts/Write.lean): Compiler.compile makes the
-- module of it, which the job writes to <output>.wasm. A job may also give
-- the engine (Wasm.Engine): two more fields, its pages, and its answers to
-- grows, one character each ('0' refuses a grow, '1' grants it); else it is
-- 2^16 pages and no answers. Then the job writes to the output the outcome of
-- Wasm.run on the module and the input, with 2^22 steps, on that engine: its
-- name (Wasm.Outcome), and for a result, a second line of its bytes in hex.

open Quan Term

-- the name of an outcome and, for a result, its bytes; the labels of the book
-- carry the prefix of their file (bend -o)
def outcome : Term → String × Option (List UInt8)
  | Tup Q1 (Lab k) (Tup Q1 bs (Lab "()")) => (Script.unprefixName ["Wasm_2f_impl.Wasm.Outcome."] k, unbytes bs)
  | Tup Q1 (Lab k) (Lab "()") => (Script.unprefixName ["Wasm_2f_impl.Wasm.Outcome."] k, none)
  | _ => ("stuck", none)

def hex (bs : List UInt8) : String :=
  String.join (bs.map fun b => String.ofList ((Nat.toDigits 16 (b.toNat + 256)).drop 1))

-- 2^22, enough for the compiled programs of agree.ts, as Nat.double applied 22
-- times, which the run unfolds as it needs
def fuel : Term := (List.range 22).foldl (fun t _ => App Q1 (Ref "Nat.double") t) (Form.nat 1)

-- the engine of m pages and the answers gs ('0' refuses a grow, '1' grants
-- it); past them, it grants each grow within the pages
def engine (m : Nat) (gs : String) : Term :=
  ctor "Wasm_2f_impl.Wasm.Engine"
    [ctor "U32" [bits 32 m], list (gs.toList.map fun c => ctor (if c == '1' then "True" else "False") [])]

def main' : IO Unit := do
  let B ← Script.book
  let some jobs ← Script.jobs | throw (IO.userError "JOBS is not set")
  for job in jobs do
    let (module, input, out, pages, grows) ← match job with
      | [module, input, out] => pure (module, input, out, 65536, "")
      | [module, input, out, pages, grows] => pure (module, input, out, pages.toNat!, grows)
      | _ => throw (IO.userError s!"bad job {job}")
    let w ← if module.endsWith ".book" then do
        let p := (← IO.FS.readBinFile module).toList
        let (c, _) := steps B 40000000000 (App Q2 (Ref "Compiler_2f_impl.Compiler.compile") (bytes p)) 0
        let some ws := unbytes c | throw (IO.userError s!"{module}: Compiler.compile gave no bytes")
        IO.FS.writeBinFile s!"{out}.wasm" ⟨ws.toArray⟩
        pure ws
      else pure (← IO.FS.readBinFile module).toList
    let i := (← IO.FS.readBinFile input).toList
    let run := App Q1 (App Q1 (App Q1 (App Q1 (Ref "Wasm_2f_impl.Wasm.run") fuel) (bytes w)) (bytes i)) (engine pages grows)
    let (v, _) := steps B 40000000000 run 0
    let (name, bs) := outcome v
    IO.FS.writeFile out (name ++ "\n" ++ (bs.map hex).getD "" ++ "\n")

#eval main'
