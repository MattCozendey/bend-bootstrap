import Shared.Refs
import Shared.Script

-- Version
-- =======
--
-- Writes a Lean version of the defs that the kernel's parser reads from a .bendtt
-- file, for the laws about our Bend code (src/Shared/Code.lean): the defs
-- that the defs ROOTS need, them included, in the order of the file.
--
--   bend <file.bend> -o <file.bendtt>
--   BOOK=<file.bendtt> ROOTS=<name>,... NAME=<name> SOURCE=<file.bend> \
--     OUTPUT=<file.lean> [STRIP=<prefix>,..] lake lean src/Shared/scripts/Version.lean
--
-- STRIP: the first of these prefixes that a name has is taken off it, first
-- (bend -o names an imported file's defs with its path); ROOTS are names
-- without them. The Lean file defines a def «NAME.k» per def k, and
-- NAME : List Def.

open Term

-- the names that the names ks need through types and bodies, ks among them
def needs (bk : Book) (ks : List String) : Std.HashSet String :=
  bk.reach (fun d acc => d.T.refs (d.v.refs acc)) ks

-- the Lean def that is the version of d: one atomic name, so that it opens no namespace in
-- which a Bend name such as List hides Lean's
def versionDef (name : String) (d : Def) : String :=
  s!"def «{name}.{d.k}» : Def :=\n  ⟨{repr d.k},\n    {(repr d.T).pretty 100 4},\n" ++
  s!"    {(repr d.v).pretty 100 4},\n    {d.o}⟩\n\n"

def versionBook : IO Unit := do
  let name ← Script.env "NAME"
  let roots ← Script.env "ROOTS"
  let ps ← Script.list "STRIP"
  let bk := Book.of ((← Script.book).defs.map fun d =>
    ⟨Script.unprefixName ps d.k, Script.unprefix ps d.T, Script.unprefix ps d.v, d.o⟩)
  let ks := needs bk (roots.splitOn ",")
  let ds := bk.defs.filter (ks.contains ·.k)
  IO.FS.writeFile (← Script.env "OUTPUT") <|
    s!"import bendtt\n\n-- Made by src/Shared/scripts/Version.lean from the `bend -o` output of {← Script.env "SOURCE"},\n" ++
    s!"-- for the roots {roots}, and the defs that they need. Do not edit it.\n\nopen Quan Term\n\n" ++
    String.join (ds.map (versionDef name)) ++
    s!"def {name} : List Def :=\n  [" ++ ",\n   ".intercalate (ds.map fun d => s!"«{name}.{d.k}»") ++ "]\n"
  IO.println s!"{ds.length} defs"

#eval versionBook
