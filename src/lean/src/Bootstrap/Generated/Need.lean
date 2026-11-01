import Bootstrap.DataForm.Book

-- Made by scripts/Defs.lean from the `bend -o` output of src/main.bend (src/tools/lower.ts).
-- Do not edit it.

open Quan Term

set_option maxRecDepth 100000

def «needVersion.U32.cmp» : Def :=
  ⟨"U32.cmp",
    (Term.All Quan.Q1 (Term.Ref "U32") (Term.All Quan.Q1 (Term.Ref "U32") (Term.Ref "Cmp"))),
    (Term.Prj (Term.Mat "U32" (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Prj (Term.Mat "U32" (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Word.cmp") (Form.nat 32)) (Term.Var 1)) (Term.Var 0)) Term.Efq))) Term.Efq)) Term.Efq))) Term.Efq)),
    false⟩

def «needVersion.U32.to_nat» : Def :=
  ⟨"U32.to_nat",
    (Term.All Quan.Q1 (Term.Ref "U32") (Term.Ref "Nat")),
    (Term.Prj (Term.Mat "U32" (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Word.to_nat") (Form.nat 32)) (Term.Var 0)) Term.Efq))) Term.Efq)),
    false⟩

def «needVersion.List.length» : Def :=
  ⟨"List.length",
    (Term.All Quan.Q0 (Term.Enu ["Q0", "Q1", "Q2"]) (Term.All Quan.Q0 (Term.Typ (Term.Var 0)) (Term.All Quan.Q1 (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.Ref "List") (Term.Var 1)) (Term.Var 0)) (Term.Ref "Nat")))),
    (Term.Lam Quan.Q0 (Term.Lam Quan.Q0 (Term.Prj (Term.Mat "Nil" (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "Zero") (Term.Lab "()")) Term.Efq) (Term.Mat "Con" (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.Ref "List.length") (Term.Var 3)) (Term.Var 2)) (Term.Var 0)) (Term.Lab "()"))) Term.Efq))))) Term.Efq))))),
    false⟩

def «needVersion.Cmp.is_le» : Def :=
  ⟨"Cmp.is_le",
    (Term.All Quan.Q1 (Term.Ref "Cmp") (Term.Ref "Bool")),
    (Term.Prj (Term.Mat "GT" (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) Term.Efq) (Term.Lam Quan.Q1 (Term.Lam Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "True") (Term.Lab "()")))))),
    false⟩

def «needVersion.U32.is_le» : Def :=
  ⟨"U32.is_le",
    (Term.All Quan.Q1 (Term.Ref "U32") (Term.All Quan.Q1 (Term.Ref "U32") (Term.Ref "Bool"))),
    (Term.Lam Quan.Q1 (Term.Lam Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Cmp.is_le") (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "U32.cmp") (Term.Var 1)) (Term.Var 0))))),
    false⟩

def «needVersion.U32.lit65536» : Def :=
  ⟨"U32.lit65536",
    (Term.Ref "U32"),
    (Term.Tup Quan.Q1 (Term.Lab "U32") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "True") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WCon") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "False") (Term.Lab "()")) (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "WNil") (Term.Lab "()")) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()")))) (Term.Lab "()"))),
    false⟩

def «needVersion.Wasm.min.if» : Def :=
  ⟨"Wasm.min.if",
    (Term.All Quan.Q1 (Term.Ref "Bool") (Term.All Quan.Q1 (Term.Ref "U32") (Term.All Quan.Q1 (Term.Ref "U32") (Term.Ref "U32")))),
    (Term.Prj (Term.Mat "True" (Term.Mat "()" (Term.Lam Quan.Q1 (Term.Lam Quan.Q1 (Term.Var 1))) Term.Efq) (Term.Mat "False" (Term.Mat "()" (Term.Lam Quan.Q1 (Term.Lam Quan.Q1 (Term.Var 0))) Term.Efq) Term.Efq))),
    false⟩

def «needVersion.Wasm.min» : Def :=
  ⟨"Wasm.min",
    (Term.All Quan.Q2 (Term.Ref "U32") (Term.All Quan.Q2 (Term.Ref "U32") (Term.Ref "U32"))),
    (Term.Lam Quan.Q2 (Term.Lam Quan.Q2 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Wasm.min.if") (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "U32.is_le") (Term.Var 1)) (Term.Var 0))) (Term.Var 1)) (Term.Var 0)))),
    false⟩

def «needVersion.Term.size» : Def :=
  ⟨"Term.size",
    (Term.All Quan.Q1 (Term.Ref "Term") (Term.Ref "Nat")),
    (Term.Prj (Term.Mat "Term.Var" (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "Zero") (Term.Lab "()")) (Term.Lab "()"))) Term.Efq))) (Term.Mat "Term.Ref" (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "Zero") (Term.Lab "()")) (Term.Lab "()"))) Term.Efq))) (Term.Mat "Term.Ann" (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Nat.add") (Term.App Quan.Q1 (Term.Ref "Term.size") (Term.Var 1))) (Term.App Quan.Q1 (Term.Ref "Term.size") (Term.Var 0))) (Term.Lab "()"))) Term.Efq))))) (Term.Mat "Term.Let" (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Nat.add") (Term.App Quan.Q1 (Term.Ref "Term.size") (Term.Var 1))) (Term.App Quan.Q1 (Term.Ref "Term.size") (Term.Var 0))) (Term.Lab "()"))) Term.Efq))))))) (Term.Mat "Term.Typ" (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Term.size") (Term.Var 0)) (Term.Lab "()"))) Term.Efq))) (Term.Mat "Term.Min" (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Nat.add") (Term.App Quan.Q1 (Term.Ref "Term.size") (Term.Var 1))) (Term.App Quan.Q1 (Term.Ref "Term.size") (Term.Var 0))) (Term.Lab "()"))) Term.Efq))))) (Term.Mat "Term.All" (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Nat.add") (Term.App Quan.Q1 (Term.Ref "Term.size") (Term.Var 1))) (Term.App Quan.Q1 (Term.Ref "Term.size") (Term.Var 0))) (Term.Lab "()"))) Term.Efq))))))) (Term.Mat "Term.Lam" (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Term.size") (Term.Var 0)) (Term.Lab "()"))) Term.Efq))))) (Term.Mat "Term.App" (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Nat.add") (Term.App Quan.Q1 (Term.Ref "Term.size") (Term.Var 1))) (Term.App Quan.Q1 (Term.Ref "Term.size") (Term.Var 0))) (Term.Lab "()"))) Term.Efq))))))) (Term.Mat "Term.Sig" (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Nat.add") (Term.App Quan.Q1 (Term.Ref "Term.size") (Term.Var 1))) (Term.App Quan.Q1 (Term.Ref "Term.size") (Term.Var 0))) (Term.Lab "()"))) Term.Efq))))))) (Term.Mat "Term.Tup" (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Nat.add") (Term.App Quan.Q1 (Term.Ref "Term.size") (Term.Var 1))) (Term.App Quan.Q1 (Term.Ref "Term.size") (Term.Var 0))) (Term.Lab "()"))) Term.Efq))))))) (Term.Mat "Term.Prj" (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Term.size") (Term.Var 0)) (Term.Lab "()"))) Term.Efq))) (Term.Mat "Term.Enu" (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "Zero") (Term.Lab "()")) (Term.Lab "()"))) Term.Efq))) (Term.Mat "Term.Lab" (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "Zero") (Term.Lab "()")) (Term.Lab "()"))) Term.Efq))) (Term.Mat "Term.Mat" (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Nat.add") (Term.App Quan.Q1 (Term.Ref "Term.size") (Term.Var 1))) (Term.App Quan.Q1 (Term.Ref "Term.size") (Term.Var 0))) (Term.Lab "()"))) Term.Efq))))))) (Term.Mat "Term.Efq" (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "Zero") (Term.Lab "()")) (Term.Lab "()"))) Term.Efq) (Term.Mat "Term.Eql" (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Nat.add") (Term.App Quan.Q1 (Term.Ref "Term.size") (Term.Var 2))) (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Nat.add") (Term.App Quan.Q1 (Term.Ref "Term.size") (Term.Var 1))) (Term.App Quan.Q1 (Term.Ref "Term.size") (Term.Var 0)))) (Term.Lab "()"))) Term.Efq))))))) (Term.Mat "Term.Rfl" (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "Zero") (Term.Lab "()")) (Term.Lab "()"))) Term.Efq) (Term.Mat "Term.Rwt" (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Nat.add") (Term.App Quan.Q1 (Term.Ref "Term.size") (Term.Var 2))) (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Nat.add") (Term.App Quan.Q1 (Term.Ref "Term.size") (Term.Var 1))) (Term.App Quan.Q1 (Term.Ref "Term.size") (Term.Var 0)))) (Term.Lab "()"))) Term.Efq))))))) Term.Efq)))))))))))))))))))),
    false⟩

def «needVersion.Program.largest.next» : Def :=
  ⟨"Program.largest.next",
    (Term.All Quan.Q1 (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.Ref "Maybe") (Term.Lab "Q1")) (Term.Ref "Term")) (Term.All Quan.Q1 (Term.All Quan.Q1 (Term.Ref "Term") (Term.Ref "Nat")) (Term.Ref "Nat"))),
    (Term.Prj (Term.Mat "None" (Term.Mat "()" (Term.Lam Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "Zero") (Term.Lab "()"))) Term.Efq) (Term.Mat "Some" (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Lam Quan.Q1 (Term.App Quan.Q1 (Term.Var 0) (Term.Var 1))) Term.Efq))) Term.Efq))),
    false⟩

def «needVersion.Nat.max» : Def :=
  ⟨"Nat.max",
    (Term.All Quan.Q2 (Term.Ref "Nat") (Term.All Quan.Q2 (Term.Ref "Nat") (Term.Ref "Nat"))),
    (Term.Prj (Term.Mat "Zero" (Term.Mat "()" (Term.Lam Quan.Q2 (Term.Var 0)) Term.Efq) (Term.Mat "Succ" (Term.Prj (Term.Lam Quan.Q2 (Term.Mat "()" (Term.Prj (Term.Mat "Zero" (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.Var 0) (Term.Lab "()"))) Term.Efq) (Term.Mat "Succ" (Term.Prj (Term.Lam Quan.Q2 (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.App Quan.Q2 (Term.App Quan.Q2 (Term.Ref "Nat.max") (Term.Var 1)) (Term.Var 0)) (Term.Lab "()"))) Term.Efq))) Term.Efq))) Term.Efq))) Term.Efq))),
    false⟩

def «needVersion.Program.largest.go» : Def :=
  ⟨"Program.largest.go",
    (Term.All Quan.Q1 (Term.Ref "Nat") (Term.All Quan.Q2 (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "Def")) (Term.All Quan.Q2 (Term.Ref "Term") (Term.Ref "Nat")))),
    (Term.Prj (Term.Mat "Zero" (Term.Mat "()" (Term.Lam Quan.Q2 (Term.Lam Quan.Q2 (Term.App Quan.Q1 (Term.Ref "Term.size") (Term.Var 0)))) Term.Efq) (Term.Mat "Succ" (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Lam Quan.Q2 (Term.Lam Quan.Q2 (Term.App Quan.Q2 (Term.App Quan.Q2 (Term.Ref "Nat.max") (Term.App Quan.Q1 (Term.Ref "Term.size") (Term.Var 0))) (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Program.largest.next") (Term.App Quan.Q2 (Term.App Quan.Q2 (Term.Ref "Eval.step") (Term.Var 1)) (Term.Var 0))) (Term.Lam Quan.Q1 (Term.App Quan.Q2 (Term.App Quan.Q2 (Term.App Quan.Q1 (Term.Ref "Program.largest.go") (Term.Var 3)) (Term.Var 2)) (Term.Var 0))))))) Term.Efq))) Term.Efq))),
    false⟩

def «needVersion.Program.largest.of» : Def :=
  ⟨"Program.largest.of",
    (Term.All Quan.Q1 (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.Ref "Maybe") (Term.Lab "Q1")) (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "Def"))) (Term.All Quan.Q1 (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.Ref "List") (Term.Lab "Q2")) (Term.App Quan.Q1 (Term.Ref "Word") (Form.nat 8))) (Term.All Quan.Q1 (Term.Ref "Nat") (Term.Ref "Nat")))),
    (Term.Prj (Term.Mat "None" (Term.Mat "()" (Term.Lam Quan.Q1 (Term.Lam Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "Zero") (Term.Lab "()")))) Term.Efq) (Term.Mat "Some" (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Lam Quan.Q1 (Term.Lam Quan.Q1 (Term.App Quan.Q2 (Term.App Quan.Q2 (Term.App Quan.Q1 (Term.Ref "Program.largest.go") (Term.Var 0)) (Term.Var 2)) (Term.App Quan.Q1 (Term.Ref "Program.start") (Term.Var 1))))) Term.Efq))) Term.Efq))),
    false⟩

def «needVersion.Program.largest» : Def :=
  ⟨"Program.largest",
    (Term.All Quan.Q1 (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.Ref "List") (Term.Lab "Q2")) (Term.App Quan.Q1 (Term.Ref "Word") (Form.nat 8))) (Term.All Quan.Q1 (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.Ref "List") (Term.Lab "Q2")) (Term.App Quan.Q1 (Term.Ref "Word") (Form.nat 8))) (Term.All Quan.Q1 (Term.Ref "Nat") (Term.Ref "Nat")))),
    (Term.Lam Quan.Q1 (Term.Lam Quan.Q1 (Term.Lam Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Program.largest.of") (Term.App Quan.Q1 (Term.Ref "Book.read") (Term.Var 2))) (Term.Var 1)) (Term.Var 0))))),
    false⟩

def «needVersion.Form.size.ctor» : Def :=
  ⟨"Form.size.ctor",
    (Term.All Quan.Q1 (Term.Ref "Nat") (Term.All Quan.Q1 (Term.Ref "Nat") (Term.Ref "Nat"))),
    (Term.Lam Quan.Q1 (Term.Lam Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Nat.add") (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.Var 1) (Term.Lab "()"))) (Term.Lab "()"))) (Term.Lab "()")))) (Term.Var 0)))),
    false⟩

def «needVersion.Nat.mul» : Def :=
  ⟨"Nat.mul",
    (Term.All Quan.Q1 (Term.Ref "Nat") (Term.All Quan.Q2 (Term.Ref "Nat") (Term.Ref "Nat"))),
    (Term.Prj (Term.Mat "Zero" (Term.Mat "()" (Term.Lam Quan.Q2 (Term.Tup Quan.Q1 (Term.Lab "Zero") (Term.Lab "()"))) Term.Efq) (Term.Mat "Succ" (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Lam Quan.Q2 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Nat.add") (Term.Var 0)) (Term.App Quan.Q2 (Term.App Quan.Q1 (Term.Ref "Nat.mul") (Term.Var 1)) (Term.Var 0)))) Term.Efq))) Term.Efq))),
    false⟩

def «needVersion.Form.size.nat» : Def :=
  ⟨"Form.size.nat",
    (Term.All Quan.Q1 (Term.Ref "Nat") (Term.Ref "Nat")),
    (Term.Lam Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Nat.add") (Form.nat 3)) (Term.App Quan.Q2 (Term.App Quan.Q1 (Term.Ref "Nat.mul") (Form.nat 4)) (Term.Var 0)))),
    false⟩

def «needVersion.Form.size.name» : Def :=
  ⟨"Form.size.name",
    (Term.All Quan.Q1 (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.Ref "List") (Term.Lab "Q2")) (Term.App Quan.Q1 (Term.Ref "Word") (Form.nat 8))) (Term.Ref "Nat")),
    (Term.Lam Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Nat.add") (Form.nat 3)) (Term.App Quan.Q2 (Term.App Quan.Q1 (Term.Ref "Nat.mul") (Form.nat 72)) (Term.App Quan.Q1 (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.Ref "List.length") (Term.Lab "Q2")) (Term.App Quan.Q1 (Term.Ref "Word") (Form.nat 8))) (Term.Var 0))))),
    false⟩

def «needVersion.Form.size.names» : Def :=
  ⟨"Form.size.names",
    (Term.All Quan.Q1 (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.Ref "List") (Term.Lab "Q2")) (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.Ref "List") (Term.Lab "Q2")) (Term.App Quan.Q1 (Term.Ref "Word") (Form.nat 8)))) (Term.Ref "Nat")),
    (Term.Prj (Term.Mat "Nil" (Term.Mat "()" (Form.nat 3) Term.Efq) (Term.Mat "Con" (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Nat.add") (Term.App Quan.Q1 (Term.Ref "Form.size.name") (Term.Var 1))) (Term.App Quan.Q1 (Term.Ref "Form.size.names") (Term.Var 0))) (Term.Lab "()"))) (Term.Lab "()"))) (Term.Lab "()"))) (Term.Lab "()"))) (Term.Lab "()"))) Term.Efq))))) Term.Efq))),
    false⟩

def «needVersion.Form.size.term» : Def :=
  ⟨"Form.size.term",
    (Term.All Quan.Q1 (Term.Ref "Term") (Term.Ref "Nat")),
    (Term.Prj (Term.Mat "Term.Var" (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Form.size.ctor") (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "Zero") (Term.Lab "()")) (Term.Lab "()")))) (Term.App Quan.Q1 (Term.Ref "Form.size.nat") (Term.Var 0))) Term.Efq))) (Term.Mat "Term.Ref" (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Form.size.ctor") (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "Zero") (Term.Lab "()")) (Term.Lab "()")))) (Term.App Quan.Q1 (Term.Ref "Form.size.name") (Term.Var 0))) Term.Efq))) (Term.Mat "Term.Ann" (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Form.size.ctor") (Form.nat 2)) (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Nat.add") (Term.App Quan.Q1 (Term.Ref "Form.size.term") (Term.Var 1))) (Term.App Quan.Q1 (Term.Ref "Form.size.term") (Term.Var 0)))) Term.Efq))))) (Term.Mat "Term.Let" (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Form.size.ctor") (Form.nat 3)) (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Nat.add") (Term.App Quan.Q1 (Term.Ref "Form.size.term") (Term.Var 1))) (Term.App Quan.Q1 (Term.Ref "Form.size.term") (Term.Var 0))) (Term.Lab "()"))) (Term.Lab "()"))) (Term.Lab "()")))) Term.Efq))))))) (Term.Mat "Term.Typ" (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Form.size.ctor") (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "Zero") (Term.Lab "()")) (Term.Lab "()")))) (Term.App Quan.Q1 (Term.Ref "Form.size.term") (Term.Var 0))) Term.Efq))) (Term.Mat "Term.Min" (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Form.size.ctor") (Form.nat 2)) (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Nat.add") (Term.App Quan.Q1 (Term.Ref "Form.size.term") (Term.Var 1))) (Term.App Quan.Q1 (Term.Ref "Form.size.term") (Term.Var 0)))) Term.Efq))))) (Term.Mat "Term.All" (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Form.size.ctor") (Form.nat 3)) (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Nat.add") (Term.App Quan.Q1 (Term.Ref "Form.size.term") (Term.Var 1))) (Term.App Quan.Q1 (Term.Ref "Form.size.term") (Term.Var 0))) (Term.Lab "()"))) (Term.Lab "()"))) (Term.Lab "()")))) Term.Efq))))))) (Term.Mat "Term.Lam" (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Form.size.ctor") (Form.nat 2)) (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Form.size.term") (Term.Var 0)) (Term.Lab "()"))) (Term.Lab "()"))) (Term.Lab "()")))) Term.Efq))))) (Term.Mat "Term.App" (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Form.size.ctor") (Form.nat 3)) (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Nat.add") (Term.App Quan.Q1 (Term.Ref "Form.size.term") (Term.Var 1))) (Term.App Quan.Q1 (Term.Ref "Form.size.term") (Term.Var 0))) (Term.Lab "()"))) (Term.Lab "()"))) (Term.Lab "()")))) Term.Efq))))))) (Term.Mat "Term.Sig" (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Form.size.ctor") (Form.nat 3)) (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Nat.add") (Term.App Quan.Q1 (Term.Ref "Form.size.term") (Term.Var 1))) (Term.App Quan.Q1 (Term.Ref "Form.size.term") (Term.Var 0))) (Term.Lab "()"))) (Term.Lab "()"))) (Term.Lab "()")))) Term.Efq))))))) (Term.Mat "Term.Tup" (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Form.size.ctor") (Form.nat 3)) (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Nat.add") (Term.App Quan.Q1 (Term.Ref "Form.size.term") (Term.Var 1))) (Term.App Quan.Q1 (Term.Ref "Form.size.term") (Term.Var 0))) (Term.Lab "()"))) (Term.Lab "()"))) (Term.Lab "()")))) Term.Efq))))))) (Term.Mat "Term.Prj" (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Form.size.ctor") (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "Zero") (Term.Lab "()")) (Term.Lab "()")))) (Term.App Quan.Q1 (Term.Ref "Form.size.term") (Term.Var 0))) Term.Efq))) (Term.Mat "Term.Enu" (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Form.size.ctor") (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "Zero") (Term.Lab "()")) (Term.Lab "()")))) (Term.App Quan.Q1 (Term.Ref "Form.size.names") (Term.Var 0))) Term.Efq))) (Term.Mat "Term.Lab" (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Form.size.ctor") (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "Zero") (Term.Lab "()")) (Term.Lab "()")))) (Term.App Quan.Q1 (Term.Ref "Form.size.name") (Term.Var 0))) Term.Efq))) (Term.Mat "Term.Mat" (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Form.size.ctor") (Form.nat 3)) (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Nat.add") (Term.App Quan.Q1 (Term.Ref "Form.size.name") (Term.Var 2))) (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Nat.add") (Term.App Quan.Q1 (Term.Ref "Form.size.term") (Term.Var 1))) (Term.App Quan.Q1 (Term.Ref "Form.size.term") (Term.Var 0))))) Term.Efq))))))) (Term.Mat "Term.Efq" (Term.Mat "()" (Form.nat 3) Term.Efq) (Term.Mat "Term.Eql" (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Form.size.ctor") (Form.nat 3)) (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Nat.add") (Term.App Quan.Q1 (Term.Ref "Form.size.term") (Term.Var 2))) (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Nat.add") (Term.App Quan.Q1 (Term.Ref "Form.size.term") (Term.Var 1))) (Term.App Quan.Q1 (Term.Ref "Form.size.term") (Term.Var 0))))) Term.Efq))))))) (Term.Mat "Term.Rfl" (Term.Mat "()" (Form.nat 3) Term.Efq) (Term.Mat "Term.Rwt" (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Form.size.ctor") (Form.nat 3)) (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Nat.add") (Term.App Quan.Q1 (Term.Ref "Form.size.term") (Term.Var 2))) (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Nat.add") (Term.App Quan.Q1 (Term.Ref "Form.size.term") (Term.Var 1))) (Term.App Quan.Q1 (Term.Ref "Form.size.term") (Term.Var 0))))) Term.Efq))))))) Term.Efq)))))))))))))))))))),
    false⟩

def «needVersion.Form.size.defs» : Def :=
  ⟨"Form.size.defs",
    (Term.All Quan.Q1 (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "Def")) (Term.Ref "Nat")),
    (Term.Prj (Term.Mat "Nil" (Term.Mat "()" (Form.nat 3) Term.Efq) (Term.Mat "Con" (Term.Prj (Term.Prj (Term.Mat "Def" (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Nat.add") (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Form.size.ctor") (Form.nat 4)) (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.Tup Quan.Q1 (Term.Lab "Succ") (Term.Tup Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Nat.add") (Term.App Quan.Q1 (Term.Ref "Form.size.name") (Term.Var 4))) (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Nat.add") (Term.App Quan.Q1 (Term.Ref "Form.size.term") (Term.Var 3))) (Term.App Quan.Q1 (Term.Ref "Form.size.term") (Term.Var 2)))) (Term.Lab "()"))) (Term.Lab "()"))) (Term.Lab "()"))))) (Term.App Quan.Q1 (Term.Ref "Form.size.defs") (Term.Var 0))) (Term.Lab "()"))) (Term.Lab "()"))) (Term.Lab "()"))) (Term.Lab "()"))) (Term.Lab "()"))) Term.Efq))) Term.Efq))))))))) Term.Efq))) Term.Efq))),
    false⟩

def «needVersion.Program.size.of» : Def :=
  ⟨"Program.size.of",
    (Term.All Quan.Q1 (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.Ref "Maybe") (Term.Lab "Q1")) (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "Def"))) (Term.Ref "Nat")),
    (Term.Prj (Term.Mat "None" (Term.Mat "()" (Term.Tup Quan.Q1 (Term.Lab "Zero") (Term.Lab "()")) Term.Efq) (Term.Mat "Some" (Term.Prj (Term.Lam Quan.Q1 (Term.Mat "()" (Term.App Quan.Q1 (Term.Ref "Form.size.defs") (Term.Var 0)) Term.Efq))) Term.Efq))),
    false⟩

def «needVersion.Program.size» : Def :=
  ⟨"Program.size",
    (Term.All Quan.Q1 (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.Ref "List") (Term.Lab "Q2")) (Term.App Quan.Q1 (Term.Ref "Word") (Form.nat 8))) (Term.Ref "Nat")),
    (Term.Lam Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Program.size.of") (Term.App Quan.Q1 (Term.Ref "Book.read") (Term.Var 0)))),
    false⟩

def «needVersion.Program.need» : Def :=
  ⟨"Program.need",
    (Term.All Quan.Q2 (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.Ref "List") (Term.Lab "Q2")) (Term.App Quan.Q1 (Term.Ref "Word") (Form.nat 8))) (Term.All Quan.Q1 (Term.App Quan.Q0 (Term.App Quan.Q0 (Term.Ref "List") (Term.Lab "Q2")) (Term.App Quan.Q1 (Term.Ref "Word") (Form.nat 8))) (Term.All Quan.Q1 (Term.Ref "Nat") (Term.Ref "Nat")))),
    (Term.Lam Quan.Q2 (Term.Lam Quan.Q1 (Term.Lam Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Nat.add") (Term.App Quan.Q2 (Term.App Quan.Q1 (Term.Ref "Nat.mul") (Form.nat 64)) (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Nat.add") (Term.App Quan.Q1 (Term.Ref "Program.size") (Term.Var 2))) (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Program.largest") (Term.Var 2)) (Term.Var 1)) (Term.Var 0))))) (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Nat.add") (Term.App Quan.Q2 (Term.App Quan.Q1 (Term.Ref "Nat.mul") (Form.nat 4096)) (Form.nat 4096))) (Term.Tup Quan.Q1 (Term.Lab "Zero") (Term.Lab "()"))))))),
    false⟩

def «needVersion.Program.memory» : Def :=
  ⟨"Program.memory",
    (Term.All Quan.Q1 (Term.Ref "U32") (Term.Ref "Nat")),
    (Term.Lam Quan.Q1 (Term.App Quan.Q2 (Term.App Quan.Q1 (Term.Ref "Nat.mul") (Term.App Quan.Q1 (Term.App Quan.Q1 (Term.Ref "Nat.add") (Term.App Quan.Q2 (Term.App Quan.Q1 (Term.Ref "Nat.mul") (Form.nat 16)) (Form.nat 4096))) (Term.Tup Quan.Q1 (Term.Lab "Zero") (Term.Lab "()")))) (Term.App Quan.Q1 (Term.Ref "U32.to_nat") (Term.App Quan.Q2 (Term.App Quan.Q2 (Term.Ref "Wasm.min") (Term.Var 0)) (Term.Ref "U32.lit65536"))))),
    false⟩

def needVersion : List Def :=
  [«needVersion.U32.cmp»,
   «needVersion.U32.to_nat»,
   «needVersion.List.length»,
   «needVersion.Cmp.is_le»,
   «needVersion.U32.is_le»,
   «needVersion.U32.lit65536»,
   «needVersion.Wasm.min.if»,
   «needVersion.Wasm.min»,
   «needVersion.Term.size»,
   «needVersion.Program.largest.next»,
   «needVersion.Nat.max»,
   «needVersion.Program.largest.go»,
   «needVersion.Program.largest.of»,
   «needVersion.Program.largest»,
   «needVersion.Form.size.ctor»,
   «needVersion.Nat.mul»,
   «needVersion.Form.size.nat»,
   «needVersion.Form.size.name»,
   «needVersion.Form.size.names»,
   «needVersion.Form.size.term»,
   «needVersion.Form.size.defs»,
   «needVersion.Program.size.of»,
   «needVersion.Program.size»,
   «needVersion.Program.need»,
   «needVersion.Program.memory»]
