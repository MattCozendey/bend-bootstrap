import Shared.Refs
import Shared.Script

-- Defs
-- ====
--
-- Writes a Lean version of some defs that the kernel's parser reads from a
-- .bendtt file, as src/Shared/scripts/Version.lean does, but of chosen defs only, for the
-- laws about our Bend code (src/Shared/Code.lean):
--
--   ROOTS    the defs that these names need, them included (as Version.lean),
--   EXCLUDE  minus the defs that these names need (written elsewhere),
--   ONLY     plus these defs alone, without the defs they need,
--   TYPES    plus the name and type of these defs, without their bodies: a
--            law that a Lean theorem uses only needs a def of its type,
--            whatever its proof,
--   STRIP    with the first of these prefixes that a name has taken off it
--            (bend -o names an imported file's defs with its path),
--   NAMES    when 1, also NAME.prefixes, STRIP's prefixes, and NAME.names:
--            each name of the book that has one of them, as the book has it,
--
--   bend <file.bend> -o <file.bendtt>
--   BOOK=<file.bendtt> NAME=<name> SOURCE=<file.bend> OUTPUT=<file.lean> \
--     [ROOTS=..] [EXCLUDE=..] [ONLY=..] [TYPES=..] [STRIP=<prefix>,..] [NAMES=1] \
--     lake lean src/Shared/scripts/Defs.lean
--
-- Each list is names separated by commas, in the file's names (prefix
-- included). The Lean file defines a def «NAME.k» : Def per def k, and
-- NAME : List Def, and a «NAME.k» : String × Term per type. A term that is
-- the form of a Nat n > 1 (as `bend -o` writes it, Succ{..}) is written
-- Form.nat n, which is that term: `bend -o` writes a literal 2^24 as
-- thousands of nested pairs, too deep for Lean to read.

open Term

-- the names that the names ks need through types and bodies, ks among them
def needs (bk : Book) (ks : List String) : Std.HashSet String :=
  bk.reach (fun d acc => d.T.refs (d.v.refs acc)) ks

-- every name and label of t, before acc
def names : Term → List String → List String
  | Ref k, acc | Lab k, acc => k :: acc
  | Mat k a b, acc => k :: names a (names b acc)
  | Enu ks, acc => ks ++ acc
  | Typ a, acc | Prj a, acc | Lam _ a, acc => names a acc
  | Ann a b, acc | Term.Min a b, acc | Let _ a b, acc | All _ a b, acc | App _ a b, acc
  | Sig _ a b, acc | Tup _ a b, acc => names a (names b acc)
  | Eql a b c, acc | Rwt a b c, acc => names a (names b (names c acc))
  | Var _, acc | Efq, acc | Rfl, acc => acc

-- the names of ns, each once, in the order of their first copies
def uniq (ns : List String) : List String :=
  (ns.foldl (init := (#[], ({} : Std.HashSet String))) fun (xs, seen) k =>
    if seen.contains k then (xs, seen) else (xs.push k, seen.insert k)).1.toList

-- the n of a term that is the form of the Nat n
def natOf : Term → Option Nat
  | Tup .Q1 (Lab "Zero") (Lab "()") => some 0
  | Tup .Q1 (Lab "Succ") (Tup .Q1 t (Lab "()")) => (natOf t).map (· + 1)
  | _ => none

def quan : Quan → String
  | .Q0 => "Quan.Q0"
  | .Q1 => "Quan.Q1"
  | .Q2 => "Quan.Q2"

-- t as Lean code, on one line
partial def lean (t : Term) : String :=
  match natOf t with
  | some n => if n > 1 then s!"(Form.nat {n})" else go t
  | none => go t
where
  go : Term → String
  | Var i => s!"(Term.Var {i})"
  | Ref k => s!"(Term.Ref {repr k})"
  | Ann a b => s!"(Term.Ann {lean a} {lean b})"
  | Let q a b => s!"(Term.Let {quan q} {lean a} {lean b})"
  | Typ a => s!"(Term.Typ {lean a})"
  | Term.Min a b => s!"(Term.Min {lean a} {lean b})"
  | All q a b => s!"(Term.All {quan q} {lean a} {lean b})"
  | Lam q a => s!"(Term.Lam {quan q} {lean a})"
  | App q a b => s!"(Term.App {quan q} {lean a} {lean b})"
  | Sig q a b => s!"(Term.Sig {quan q} {lean a} {lean b})"
  | Tup q a b => s!"(Term.Tup {quan q} {lean a} {lean b})"
  | Prj a => s!"(Term.Prj {lean a})"
  | Enu ks => s!"(Term.Enu {repr ks})"
  | Lab k => s!"(Term.Lab {repr k})"
  | Mat k a b => s!"(Term.Mat {repr k} {lean a} {lean b})"
  | Efq => "Term.Efq"
  | Eql a b c => s!"(Term.Eql {lean a} {lean b} {lean c})"
  | Rfl => "Term.Rfl"
  | Rwt a b c => s!"(Term.Rwt {lean a} {lean b} {lean c})"

def versionDefs : IO Unit := do
  let name ← Script.env "NAME"
  let bk ← Script.book
  let ps ← Script.list "STRIP"
  let roots ← Script.list "ROOTS"
  let ex := needs bk (← Script.list "EXCLUDE")
  let ks := needs bk roots
  let only ← Script.list "ONLY"
  let ds := bk.defs.filter fun d => ks.contains d.k && !ex.contains d.k || only.contains d.k
  let ts := (← Script.list "TYPES").filterMap bk.get
  let k' (k : String) := Script.unprefixName ps k
  let defs := String.join <| ds.map fun d =>
    s!"def «{name}.{k' d.k}» : Def :=\n  ⟨{repr (k' d.k)},\n    {lean (Script.unprefix ps d.T)},\n" ++
    s!"    {lean (Script.unprefix ps d.v)},\n    {d.o}⟩\n\n"
  let types := String.join <| ts.map fun d =>
    s!"def «{name}.{k' d.k}» : String × Term :=\n  ({repr (k' d.k)},\n    {lean (Script.unprefix ps d.T)})\n\n"
  let all := uniq (bk.defs.flatMap fun d => d.k :: names d.T (names d.v []))
  let ns := if (← IO.getEnv "NAMES") != some "1" then "" else
    s!"def {name}.prefixes : List String :=\n  {repr ps}\n\n" ++
    s!"def {name}.names : List String :=\n  {repr (all.filter fun k => ps.any (·.isPrefixOf k))}\n\n"
  IO.FS.writeFile (← Script.env "OUTPUT") <|
    s!"import Shared.DataForm\n\n-- Made by src/Shared/scripts/Defs.lean from the `bend -o` output of {← Script.env "SOURCE"}.\n" ++
    "-- Do not edit it.\n\nopen Quan Term\n\nset_option maxRecDepth 100000\n\n" ++ defs ++ types ++ ns ++
    s!"def {name} : List Def :=\n  [" ++ ",\n   ".intercalate (ds.map fun d => s!"«{name}.{k' d.k}»") ++ "]\n"
  IO.println s!"{ds.length} defs, {ts.length} types"

#eval versionDefs
