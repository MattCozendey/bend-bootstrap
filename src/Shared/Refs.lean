import bendtt

-- Refs
-- ====
--
-- The names that terms refer to, and the names that a book's defs reach
-- through them: for the pruned book (src/Book/Prune.lean) and for the scripts
-- that copy a book's defs into Lean (scripts/Defs.lean, scripts/Version.lean).
-- Each is one pass: linear in the terms it reads.

open Term

-- the names of the Refs in t, before acc
def Term.refs : Term → List String → List String
  | Ref k, acc => k :: acc
  | Typ a, acc | Prj a, acc | Lam _ a, acc => a.refs acc
  | Ann a b, acc | Min a b, acc | Let _ a b, acc | All _ a b, acc | App _ a b, acc
  | Sig _ a b, acc | Tup _ a b, acc | Mat _ a b, acc => a.refs (b.refs acc)
  | Eql a b c, acc | Rwt a b c, acc => a.refs (b.refs (c.refs acc))
  | Var _, acc | Enu _, acc | Lab _, acc | Efq, acc | Rfl, acc => acc

-- the names that the names ks reach, ks among them, where a def d names
-- next d acc (its names, before acc): each name is opened once
partial def Book.reach (bk : Book) (next : Def → List String → List String)
    (ks : List String) (seen : Std.HashSet String := {}) : Std.HashSet String :=
  match ks with
  | [] => seen
  | k :: ks =>
    if seen.contains k then Book.reach bk next ks seen
    else Book.reach bk next (((bk.get k).map (next · ks)).getD ks) (seen.insert k)
