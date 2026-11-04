import Shared.Script
import Joining.SelfHost

-- SelfHost
-- ========
--
-- AGENTS.md 3.8.7 in one process, on one book B: it reads the .bendtt file of
-- main.bend that BOOK names once, and on that B runs the kernel's checker
-- (Book.check B, which --verdict runs), the Trusted check (Trusted.missing),
-- the pruning and the writer (write (prune B)), and the interpreter on those
-- bytes. So the premises hc, hB and hs of trusted_binary (SelfHost.lean) are
-- about the same B. It writes the binary wc to OUTPUT, and prints the SHA-256
-- of the .bendtt file.
--
--   bend src/main.bend -o main.bendtt
--   BOOK=main.bendtt OUTPUT=wc.wasm [FUEL=n] lake lean src/Joining/scripts/SelfHost.lean
--
-- The .bendtt file must come from `bend -o` (AGENTS.md 3.7.3), and the run is
-- fresh: it uses no cache (3.10.2). FUEL is 2^40 when it is not set.

def selfHost : IO Unit := do
  let path ← Script.env "BOOK"
  let fuel := ((← IO.getEnv "FUEL").bind String.toNat?).getD (2 ^ 40)
  let bk ← Script.bookAt path
  match Book.check bk with
  | .ok () => IO.println "Book.check: ALL PROOFS CHECK"
  | .error msg => throw (IO.userError s!"Book.check: {msg}")
  let bad := Trusted.missing bk
  if !bad.isEmpty then throw (IO.userError s!"Trusted: missing or different: {bad}")
  IO.println "Trusted: the book holds the trusted versions"
  let input := write (prune bk)
  IO.println s!"write (prune B): {input.length} bytes"
  match interp bk fuel input with
  | some (wc, n) =>
    IO.FS.writeBinFile (← Script.env "OUTPUT") ⟨wc.toArray⟩
    IO.println s!"interp: {wc.length} bytes in {n} steps"
  | none => throw (IO.userError s!"interp: no result within {fuel} steps")
  let sha ← IO.Process.output { cmd := "sha256sum", args := #[path] }
  IO.print s!"SHA-256 of the book: {sha.stdout}"

#eval selfHost
