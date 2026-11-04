import Shared.Script
import Joining.Trusted

-- Trusted
-- =======
--
-- Checks that the book of a .bendtt file (main.bend's) holds what
-- Trusted (src/Joining/Trusted.lean) asks: each def of trustedDefs and
-- existsVersion, and a def of the type of each law (Trusted.missing).
--
--   bend src/main.bend -o main.bendtt
--   BOOK=main.bendtt lake lean src/Joining/scripts/Trusted.lean
--
-- (While Compiler/proof.bend has open TODOs, `bend -o` refuses main.bend;
-- src/Shared/lower.ts writes the same lowering with each hole read as its own
-- def, which changes no def or type that Trusted names.)

def check : IO Unit := do
  let bad := Trusted.missing (← Script.book)
  IO.println s!"{(trustedDefs ++ existsVersion).length} defs, {laws.length} laws; missing or different: {bad}"
  if !bad.isEmpty then throw (IO.userError "the book does not hold Trusted's defs")

#eval check
