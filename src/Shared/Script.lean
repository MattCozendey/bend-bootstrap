import bendtt

-- Script
-- ======
--
-- What the scripts (each feature's scripts/) share. They are scripts and not executables:
-- the kernel's own main has the name that an executable needs. Lean runs a
-- script's #eval with no stdin and keeps its stdout, so a script takes its
-- input from files, and environment variables name them.

namespace Script

-- the value of the environment variable k, which must be set
def env (k : String) : IO String := do
  let some v ← IO.getEnv k | throw (IO.userError s!"{k} is not set")
  pure v

-- the book of the .bendtt file that BOOK names
def book : IO Book := do
  match Book.parse (← IO.FS.readFile (← env "BOOK")) with
  | .error msg => throw (IO.userError msg)
  | .ok bk => pure bk

-- the names of the variable k, separated by commas; none when it is not set
def list (k : String) : IO (List String) := do
  match ← IO.getEnv k with
  | some v => pure ((v.splitOn ",").filter (· != ""))
  | none => pure []

-- k without the first of the prefixes ps that it has, when it has one
def unprefixName (ps : List String) (k : String) : String :=
  match ps.find? (·.isPrefixOf k) with
  | some p => String.ofList (k.toList.drop p.length)
  | none => k

open Term in
def unprefix (ps : List String) : Term → Term
  | Ref k => Ref (unprefixName ps k)
  | Lab k => Lab (unprefixName ps k)
  | Mat k a b => Mat (unprefixName ps k) (unprefix ps a) (unprefix ps b)
  | Enu ks => Enu (ks.map (unprefixName ps))
  | Typ a => Typ (unprefix ps a)
  | Prj a => Prj (unprefix ps a)
  | Lam q a => Lam q (unprefix ps a)
  | Ann a b => Ann (unprefix ps a) (unprefix ps b)
  | Term.Min a b => Term.Min (unprefix ps a) (unprefix ps b)
  | Let q a b => Let q (unprefix ps a) (unprefix ps b)
  | All q a b => All q (unprefix ps a) (unprefix ps b)
  | App q a b => App q (unprefix ps a) (unprefix ps b)
  | Sig q a b => Sig q (unprefix ps a) (unprefix ps b)
  | Tup q a b => Tup q (unprefix ps a) (unprefix ps b)
  | Eql a b c => Eql (unprefix ps a) (unprefix ps b) (unprefix ps c)
  | Rwt a b c => Rwt (unprefix ps a) (unprefix ps b) (unprefix ps c)
  | t => t

end Script
