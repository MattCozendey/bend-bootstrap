import bendtt

-- Made by src/Shared/scripts/Version.lean from the `bend -o` output of src/main.bend (src/Shared/lower.ts),
-- for the roots Eval.steps, and the defs that they need. Do not edit it.

open Quan Term

def «evalVersion.Quan.arms» : Def :=
  ⟨"Quan.arms",
    Term.All (Quan.Q1) (Term.Enu ["Quan.Q0", "Quan.Q1", "Quan.Q2"]) (Term.Typ (Term.Lab "Q2")),
    Term.Mat
      "Quan.Q0"
      (Term.Enu ["()"])
      (Term.Mat "Quan.Q1" (Term.Enu ["()"]) (Term.Mat "Quan.Q2" (Term.Enu ["()"]) (Term.Efq))),
    false⟩

def «evalVersion.Quan» : Def :=
  ⟨"Quan",
    Term.Typ (Term.Lab "Q2"),
    Term.Sig
      (Quan.Q1)
      (Term.Enu ["Quan.Q0", "Quan.Q1", "Quan.Q2"])
      (Term.App (Quan.Q1) (Term.Ref "Quan.arms") (Term.Var 0)),
    false⟩

def «evalVersion.Term.arms» : Def :=
  ⟨"Term.arms",
    Term.All
      (Quan.Q1)
      (Term.Enu
        ["Term.Var", "Term.Ref", "Term.Ann", "Term.Let", "Term.Typ", "Term.Min", "Term.All",
         "Term.Lam", "Term.App", "Term.Sig", "Term.Tup", "Term.Prj", "Term.Enu", "Term.Lab",
         "Term.Mat", "Term.Efq", "Term.Eql", "Term.Rfl", "Term.Rwt"])
      (Term.Typ (Term.Lab "Q2")),
    Term.Mat
      "Term.Var"
      (Term.Sig (Quan.Q1) (Term.Ref "Nat") (Term.Enu ["()"]))
      (Term.Mat
        "Term.Ref"
        (Term.Sig
          (Quan.Q1)
          (Term.App
            (Quan.Q0)
            (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
            (Term.App
              (Quan.Q1)
              (Term.Ref "Word")
              (Term.Tup
                (Quan.Q1)
                (Term.Lab "Succ")
                (Term.Tup
                  (Quan.Q1)
                  (Term.Tup
                    (Quan.Q1)
                    (Term.Lab "Succ")
                    (Term.Tup
                      (Quan.Q1)
                      (Term.Tup
                        (Quan.Q1)
                        (Term.Lab "Succ")
                        (Term.Tup
                          (Quan.Q1)
                          (Term.Tup
                            (Quan.Q1)
                            (Term.Lab "Succ")
                            (Term.Tup
                              (Quan.Q1)
                              (Term.Tup
                                (Quan.Q1)
                                (Term.Lab "Succ")
                                (Term.Tup
                                  (Quan.Q1)
                                  (Term.Tup
                                    (Quan.Q1)
                                    (Term.Lab "Succ")
                                    (Term.Tup
                                      (Quan.Q1)
                                      (Term.Tup
                                        (Quan.Q1)
                                        (Term.Lab "Succ")
                                        (Term.Tup
                                          (Quan.Q1)
                                          (Term.Tup
                                            (Quan.Q1)
                                            (Term.Lab "Succ")
                                            (Term.Tup
                                              (Quan.Q1)
                                              (Term.Tup (Quan.Q1) (Term.Lab "Zero") (Term.Lab "()"))
                                              (Term.Lab "()")))
                                          (Term.Lab "()")))
                                      (Term.Lab "()")))
                                  (Term.Lab "()")))
                              (Term.Lab "()")))
                          (Term.Lab "()")))
                      (Term.Lab "()")))
                  (Term.Lab "()")))))
          (Term.Enu ["()"]))
        (Term.Mat
          "Term.Ann"
          (Term.Sig
            (Quan.Q1)
            (Term.Ref "Term")
            (Term.Sig (Quan.Q1) (Term.Ref "Term") (Term.Enu ["()"])))
          (Term.Mat
            "Term.Let"
            (Term.Sig
              (Quan.Q1)
              (Term.Ref "Quan")
              (Term.Sig
                (Quan.Q1)
                (Term.Ref "Term")
                (Term.Sig (Quan.Q1) (Term.Ref "Term") (Term.Enu ["()"]))))
            (Term.Mat
              "Term.Typ"
              (Term.Sig (Quan.Q1) (Term.Ref "Term") (Term.Enu ["()"]))
              (Term.Mat
                "Term.Min"
                (Term.Sig
                  (Quan.Q1)
                  (Term.Ref "Term")
                  (Term.Sig (Quan.Q1) (Term.Ref "Term") (Term.Enu ["()"])))
                (Term.Mat
                  "Term.All"
                  (Term.Sig
                    (Quan.Q1)
                    (Term.Ref "Quan")
                    (Term.Sig
                      (Quan.Q1)
                      (Term.Ref "Term")
                      (Term.Sig (Quan.Q1) (Term.Ref "Term") (Term.Enu ["()"]))))
                  (Term.Mat
                    "Term.Lam"
                    (Term.Sig
                      (Quan.Q1)
                      (Term.Ref "Quan")
                      (Term.Sig (Quan.Q1) (Term.Ref "Term") (Term.Enu ["()"])))
                    (Term.Mat
                      "Term.App"
                      (Term.Sig
                        (Quan.Q1)
                        (Term.Ref "Quan")
                        (Term.Sig
                          (Quan.Q1)
                          (Term.Ref "Term")
                          (Term.Sig (Quan.Q1) (Term.Ref "Term") (Term.Enu ["()"]))))
                      (Term.Mat
                        "Term.Sig"
                        (Term.Sig
                          (Quan.Q1)
                          (Term.Ref "Quan")
                          (Term.Sig
                            (Quan.Q1)
                            (Term.Ref "Term")
                            (Term.Sig (Quan.Q1) (Term.Ref "Term") (Term.Enu ["()"]))))
                        (Term.Mat
                          "Term.Tup"
                          (Term.Sig
                            (Quan.Q1)
                            (Term.Ref "Quan")
                            (Term.Sig
                              (Quan.Q1)
                              (Term.Ref "Term")
                              (Term.Sig (Quan.Q1) (Term.Ref "Term") (Term.Enu ["()"]))))
                          (Term.Mat
                            "Term.Prj"
                            (Term.Sig (Quan.Q1) (Term.Ref "Term") (Term.Enu ["()"]))
                            (Term.Mat
                              "Term.Enu"
                              (Term.Sig
                                (Quan.Q1)
                                (Term.App
                                  (Quan.Q0)
                                  (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
                                  (Term.App
                                    (Quan.Q0)
                                    (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
                                    (Term.App
                                      (Quan.Q1)
                                      (Term.Ref "Word")
                                      (Term.Tup
                                        (Quan.Q1)
                                        (Term.Lab "Succ")
                                        (Term.Tup
                                          (Quan.Q1)
                                          (Term.Tup
                                            (Quan.Q1)
                                            (Term.Lab "Succ")
                                            (Term.Tup
                                              (Quan.Q1)
                                              (Term.Tup
                                                (Quan.Q1)
                                                (Term.Lab "Succ")
                                                (Term.Tup
                                                  (Quan.Q1)
                                                  (Term.Tup
                                                    (Quan.Q1)
                                                    (Term.Lab "Succ")
                                                    (Term.Tup
                                                      (Quan.Q1)
                                                      (Term.Tup
                                                        (Quan.Q1)
                                                        (Term.Lab "Succ")
                                                        (Term.Tup
                                                          (Quan.Q1)
                                                          (Term.Tup
                                                            (Quan.Q1)
                                                            (Term.Lab "Succ")
                                                            (Term.Tup
                                                              (Quan.Q1)
                                                              (Term.Tup
                                                                (Quan.Q1)
                                                                (Term.Lab "Succ")
                                                                (Term.Tup
                                                                  (Quan.Q1)
                                                                  (Term.Tup
                                                                    (Quan.Q1)
                                                                    (Term.Lab "Succ")
                                                                    (Term.Tup
                                                                      (Quan.Q1)
                                                                      (Term.Tup
                                                                        (Quan.Q1)
                                                                        (Term.Lab "Zero")
                                                                        (Term.Lab "()"))
                                                                      (Term.Lab "()")))
                                                                  (Term.Lab "()")))
                                                              (Term.Lab "()")))
                                                          (Term.Lab "()")))
                                                      (Term.Lab "()")))
                                                  (Term.Lab "()")))
                                              (Term.Lab "()")))
                                          (Term.Lab "()"))))))
                                (Term.Enu ["()"]))
                              (Term.Mat
                                "Term.Lab"
                                (Term.Sig
                                  (Quan.Q1)
                                  (Term.App
                                    (Quan.Q0)
                                    (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
                                    (Term.App
                                      (Quan.Q1)
                                      (Term.Ref "Word")
                                      (Term.Tup
                                        (Quan.Q1)
                                        (Term.Lab "Succ")
                                        (Term.Tup
                                          (Quan.Q1)
                                          (Term.Tup
                                            (Quan.Q1)
                                            (Term.Lab "Succ")
                                            (Term.Tup
                                              (Quan.Q1)
                                              (Term.Tup
                                                (Quan.Q1)
                                                (Term.Lab "Succ")
                                                (Term.Tup
                                                  (Quan.Q1)
                                                  (Term.Tup
                                                    (Quan.Q1)
                                                    (Term.Lab "Succ")
                                                    (Term.Tup
                                                      (Quan.Q1)
                                                      (Term.Tup
                                                        (Quan.Q1)
                                                        (Term.Lab "Succ")
                                                        (Term.Tup
                                                          (Quan.Q1)
                                                          (Term.Tup
                                                            (Quan.Q1)
                                                            (Term.Lab "Succ")
                                                            (Term.Tup
                                                              (Quan.Q1)
                                                              (Term.Tup
                                                                (Quan.Q1)
                                                                (Term.Lab "Succ")
                                                                (Term.Tup
                                                                  (Quan.Q1)
                                                                  (Term.Tup
                                                                    (Quan.Q1)
                                                                    (Term.Lab "Succ")
                                                                    (Term.Tup
                                                                      (Quan.Q1)
                                                                      (Term.Tup
                                                                        (Quan.Q1)
                                                                        (Term.Lab "Zero")
                                                                        (Term.Lab "()"))
                                                                      (Term.Lab "()")))
                                                                  (Term.Lab "()")))
                                                              (Term.Lab "()")))
                                                          (Term.Lab "()")))
                                                      (Term.Lab "()")))
                                                  (Term.Lab "()")))
                                              (Term.Lab "()")))
                                          (Term.Lab "()")))))
                                  (Term.Enu ["()"]))
                                (Term.Mat
                                  "Term.Mat"
                                  (Term.Sig
                                    (Quan.Q1)
                                    (Term.App
                                      (Quan.Q0)
                                      (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
                                      (Term.App
                                        (Quan.Q1)
                                        (Term.Ref "Word")
                                        (Term.Tup
                                          (Quan.Q1)
                                          (Term.Lab "Succ")
                                          (Term.Tup
                                            (Quan.Q1)
                                            (Term.Tup
                                              (Quan.Q1)
                                              (Term.Lab "Succ")
                                              (Term.Tup
                                                (Quan.Q1)
                                                (Term.Tup
                                                  (Quan.Q1)
                                                  (Term.Lab "Succ")
                                                  (Term.Tup
                                                    (Quan.Q1)
                                                    (Term.Tup
                                                      (Quan.Q1)
                                                      (Term.Lab "Succ")
                                                      (Term.Tup
                                                        (Quan.Q1)
                                                        (Term.Tup
                                                          (Quan.Q1)
                                                          (Term.Lab "Succ")
                                                          (Term.Tup
                                                            (Quan.Q1)
                                                            (Term.Tup
                                                              (Quan.Q1)
                                                              (Term.Lab "Succ")
                                                              (Term.Tup
                                                                (Quan.Q1)
                                                                (Term.Tup
                                                                  (Quan.Q1)
                                                                  (Term.Lab "Succ")
                                                                  (Term.Tup
                                                                    (Quan.Q1)
                                                                    (Term.Tup
                                                                      (Quan.Q1)
                                                                      (Term.Lab "Succ")
                                                                      (Term.Tup
                                                                        (Quan.Q1)
                                                                        (Term.Tup
                                                                          (Quan.Q1)
                                                                          (Term.Lab "Zero")
                                                                          (Term.Lab "()"))
                                                                        (Term.Lab "()")))
                                                                    (Term.Lab "()")))
                                                                (Term.Lab "()")))
                                                            (Term.Lab "()")))
                                                        (Term.Lab "()")))
                                                    (Term.Lab "()")))
                                                (Term.Lab "()")))
                                            (Term.Lab "()")))))
                                    (Term.Sig
                                      (Quan.Q1)
                                      (Term.Ref "Term")
                                      (Term.Sig (Quan.Q1) (Term.Ref "Term") (Term.Enu ["()"]))))
                                  (Term.Mat
                                    "Term.Efq"
                                    (Term.Enu ["()"])
                                    (Term.Mat
                                      "Term.Eql"
                                      (Term.Sig
                                        (Quan.Q1)
                                        (Term.Ref "Term")
                                        (Term.Sig
                                          (Quan.Q1)
                                          (Term.Ref "Term")
                                          (Term.Sig (Quan.Q1) (Term.Ref "Term") (Term.Enu ["()"]))))
                                      (Term.Mat
                                        "Term.Rfl"
                                        (Term.Enu ["()"])
                                        (Term.Mat
                                          "Term.Rwt"
                                          (Term.Sig
                                            (Quan.Q1)
                                            (Term.Ref "Term")
                                            (Term.Sig
                                              (Quan.Q1)
                                              (Term.Ref "Term")
                                              (Term.Sig
                                                (Quan.Q1)
                                                (Term.Ref "Term")
                                                (Term.Enu ["()"]))))
                                          (Term.Efq))))))))))))))))))),
    false⟩

def «evalVersion.Term» : Def :=
  ⟨"Term",
    Term.Typ (Term.Lab "Q2"),
    Term.Sig
      (Quan.Q1)
      (Term.Enu
        ["Term.Var", "Term.Ref", "Term.Ann", "Term.Let", "Term.Typ", "Term.Min", "Term.All",
         "Term.Lam", "Term.App", "Term.Sig", "Term.Tup", "Term.Prj", "Term.Enu", "Term.Lab",
         "Term.Mat", "Term.Efq", "Term.Eql", "Term.Rfl", "Term.Rwt"])
      (Term.App (Quan.Q1) (Term.Ref "Term.arms") (Term.Var 0)),
    false⟩

def «evalVersion.Def.arms» : Def :=
  ⟨"Def.arms",
    Term.All (Quan.Q1) (Term.Enu ["Def"]) (Term.Typ (Term.Lab "Q2")),
    Term.Mat
      "Def"
      (Term.Sig
        (Quan.Q1)
        (Term.App
          (Quan.Q0)
          (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
          (Term.App
            (Quan.Q1)
            (Term.Ref "Word")
            (Term.Tup
              (Quan.Q1)
              (Term.Lab "Succ")
              (Term.Tup
                (Quan.Q1)
                (Term.Tup
                  (Quan.Q1)
                  (Term.Lab "Succ")
                  (Term.Tup
                    (Quan.Q1)
                    (Term.Tup
                      (Quan.Q1)
                      (Term.Lab "Succ")
                      (Term.Tup
                        (Quan.Q1)
                        (Term.Tup
                          (Quan.Q1)
                          (Term.Lab "Succ")
                          (Term.Tup
                            (Quan.Q1)
                            (Term.Tup
                              (Quan.Q1)
                              (Term.Lab "Succ")
                              (Term.Tup
                                (Quan.Q1)
                                (Term.Tup
                                  (Quan.Q1)
                                  (Term.Lab "Succ")
                                  (Term.Tup
                                    (Quan.Q1)
                                    (Term.Tup
                                      (Quan.Q1)
                                      (Term.Lab "Succ")
                                      (Term.Tup
                                        (Quan.Q1)
                                        (Term.Tup
                                          (Quan.Q1)
                                          (Term.Lab "Succ")
                                          (Term.Tup
                                            (Quan.Q1)
                                            (Term.Tup (Quan.Q1) (Term.Lab "Zero") (Term.Lab "()"))
                                            (Term.Lab "()")))
                                        (Term.Lab "()")))
                                    (Term.Lab "()")))
                                (Term.Lab "()")))
                            (Term.Lab "()")))
                        (Term.Lab "()")))
                    (Term.Lab "()")))
                (Term.Lab "()")))))
        (Term.Sig
          (Quan.Q1)
          (Term.Ref "Term")
          (Term.Sig
            (Quan.Q1)
            (Term.Ref "Term")
            (Term.Sig (Quan.Q1) (Term.Ref "Bool") (Term.Enu ["()"])))))
      (Term.Efq),
    false⟩

def «evalVersion.Def» : Def :=
  ⟨"Def",
    Term.Typ (Term.Lab "Q2"),
    Term.Sig (Quan.Q1) (Term.Enu ["Def"]) (Term.App (Quan.Q1) (Term.Ref "Def.arms") (Term.Var 0)),
    false⟩

def «evalVersion.Word.low» : Def :=
  ⟨"Word.low",
    Term.All
      (Quan.Q1)
      (Term.Ref "Nat")
      (Term.All
        (Quan.Q1)
        (Term.Ref "Nat")
        (Term.All
          (Quan.Q1)
          (Term.App
            (Quan.Q1)
            (Term.Ref "Word")
            (Term.App
              (Quan.Q1)
              (Term.App (Quan.Q1) (Term.Ref "Nat.add") (Term.Var 1))
              (Term.Var 0)))
          (Term.App (Quan.Q1) (Term.Ref "Word") (Term.Var 2)))),
    Term.Prj
      (Term.Mat
        "Zero"
        (Term.Mat
          "()"
          (Term.Lam
            (Quan.Q1)
            (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "WNil") (Term.Lab "()"))))
          (Term.Efq))
        (Term.Mat
          "Succ"
          (Term.Prj
            (Term.Lam
              (Quan.Q1)
              (Term.Mat
                "()"
                (Term.Lam
                  (Quan.Q1)
                  (Term.Prj
                    (Term.Mat
                      "WCon"
                      (Term.Prj
                        (Term.Lam
                          (Quan.Q1)
                          (Term.Prj
                            (Term.Lam
                              (Quan.Q1)
                              (Term.Mat
                                "()"
                                (Term.Tup
                                  (Quan.Q1)
                                  (Term.Lab "WCon")
                                  (Term.Tup
                                    (Quan.Q1)
                                    (Term.Var 1)
                                    (Term.Tup
                                      (Quan.Q1)
                                      (Term.App
                                        (Quan.Q1)
                                        (Term.App
                                          (Quan.Q1)
                                          (Term.App (Quan.Q1) (Term.Ref "Word.low") (Term.Var 3))
                                          (Term.Var 2))
                                        (Term.Var 0))
                                      (Term.Lab "()"))))
                                (Term.Efq))))))
                      (Term.Efq))))
                (Term.Efq))))
          (Term.Efq))),
    false⟩

def «evalVersion.Byte.from_u32» : Def :=
  ⟨"Byte.from_u32",
    Term.All
      (Quan.Q1)
      (Term.Ref "U32")
      (Term.App
        (Quan.Q1)
        (Term.Ref "Word")
        (Term.Tup
          (Quan.Q1)
          (Term.Lab "Succ")
          (Term.Tup
            (Quan.Q1)
            (Term.Tup
              (Quan.Q1)
              (Term.Lab "Succ")
              (Term.Tup
                (Quan.Q1)
                (Term.Tup
                  (Quan.Q1)
                  (Term.Lab "Succ")
                  (Term.Tup
                    (Quan.Q1)
                    (Term.Tup
                      (Quan.Q1)
                      (Term.Lab "Succ")
                      (Term.Tup
                        (Quan.Q1)
                        (Term.Tup
                          (Quan.Q1)
                          (Term.Lab "Succ")
                          (Term.Tup
                            (Quan.Q1)
                            (Term.Tup
                              (Quan.Q1)
                              (Term.Lab "Succ")
                              (Term.Tup
                                (Quan.Q1)
                                (Term.Tup
                                  (Quan.Q1)
                                  (Term.Lab "Succ")
                                  (Term.Tup
                                    (Quan.Q1)
                                    (Term.Tup
                                      (Quan.Q1)
                                      (Term.Lab "Succ")
                                      (Term.Tup
                                        (Quan.Q1)
                                        (Term.Tup (Quan.Q1) (Term.Lab "Zero") (Term.Lab "()"))
                                        (Term.Lab "()")))
                                    (Term.Lab "()")))
                                (Term.Lab "()")))
                            (Term.Lab "()")))
                        (Term.Lab "()")))
                    (Term.Lab "()")))
                (Term.Lab "()")))
            (Term.Lab "()")))),
    Term.Prj
      (Term.Mat
        "U32"
        (Term.Prj
          (Term.Lam
            (Quan.Q1)
            (Term.Mat
              "()"
              (Term.App
                (Quan.Q1)
                (Term.App
                  (Quan.Q1)
                  (Term.App
                    (Quan.Q1)
                    (Term.Ref "Word.low")
                    (Term.Tup
                      (Quan.Q1)
                      (Term.Lab "Succ")
                      (Term.Tup
                        (Quan.Q1)
                        (Term.Tup
                          (Quan.Q1)
                          (Term.Lab "Succ")
                          (Term.Tup
                            (Quan.Q1)
                            (Term.Tup
                              (Quan.Q1)
                              (Term.Lab "Succ")
                              (Term.Tup
                                (Quan.Q1)
                                (Term.Tup
                                  (Quan.Q1)
                                  (Term.Lab "Succ")
                                  (Term.Tup
                                    (Quan.Q1)
                                    (Term.Tup
                                      (Quan.Q1)
                                      (Term.Lab "Succ")
                                      (Term.Tup
                                        (Quan.Q1)
                                        (Term.Tup
                                          (Quan.Q1)
                                          (Term.Lab "Succ")
                                          (Term.Tup
                                            (Quan.Q1)
                                            (Term.Tup
                                              (Quan.Q1)
                                              (Term.Lab "Succ")
                                              (Term.Tup
                                                (Quan.Q1)
                                                (Term.Tup
                                                  (Quan.Q1)
                                                  (Term.Lab "Succ")
                                                  (Term.Tup
                                                    (Quan.Q1)
                                                    (Term.Tup
                                                      (Quan.Q1)
                                                      (Term.Lab "Zero")
                                                      (Term.Lab "()"))
                                                    (Term.Lab "()")))
                                                (Term.Lab "()")))
                                            (Term.Lab "()")))
                                        (Term.Lab "()")))
                                    (Term.Lab "()")))
                                (Term.Lab "()")))
                            (Term.Lab "()")))
                        (Term.Lab "()"))))
                  (Term.Tup
                    (Quan.Q1)
                    (Term.Lab "Succ")
                    (Term.Tup
                      (Quan.Q1)
                      (Term.Tup
                        (Quan.Q1)
                        (Term.Lab "Succ")
                        (Term.Tup
                          (Quan.Q1)
                          (Term.Tup
                            (Quan.Q1)
                            (Term.Lab "Succ")
                            (Term.Tup
                              (Quan.Q1)
                              (Term.Tup
                                (Quan.Q1)
                                (Term.Lab "Succ")
                                (Term.Tup
                                  (Quan.Q1)
                                  (Term.Tup
                                    (Quan.Q1)
                                    (Term.Lab "Succ")
                                    (Term.Tup
                                      (Quan.Q1)
                                      (Term.Tup
                                        (Quan.Q1)
                                        (Term.Lab "Succ")
                                        (Term.Tup
                                          (Quan.Q1)
                                          (Term.Tup
                                            (Quan.Q1)
                                            (Term.Lab "Succ")
                                            (Term.Tup
                                              (Quan.Q1)
                                              (Term.Tup
                                                (Quan.Q1)
                                                (Term.Lab "Succ")
                                                (Term.Tup
                                                  (Quan.Q1)
                                                  (Term.Tup
                                                    (Quan.Q1)
                                                    (Term.Lab "Succ")
                                                    (Term.Tup
                                                      (Quan.Q1)
                                                      (Term.Tup
                                                        (Quan.Q1)
                                                        (Term.Lab "Succ")
                                                        (Term.Tup
                                                          (Quan.Q1)
                                                          (Term.Tup
                                                            (Quan.Q1)
                                                            (Term.Lab "Succ")
                                                            (Term.Tup
                                                              (Quan.Q1)
                                                              (Term.Tup
                                                                (Quan.Q1)
                                                                (Term.Lab "Succ")
                                                                (Term.Tup
                                                                  (Quan.Q1)
                                                                  (Term.Tup
                                                                    (Quan.Q1)
                                                                    (Term.Lab "Succ")
                                                                    (Term.Tup
                                                                      (Quan.Q1)
                                                                      (Term.Tup
                                                                        (Quan.Q1)
                                                                        (Term.Lab "Succ")
                                                                        (Term.Tup
                                                                          (Quan.Q1)
                                                                          (Term.Tup
                                                                            (Quan.Q1)
                                                                            (Term.Lab "Succ")
                                                                            (Term.Tup
                                                                              (Quan.Q1)
                                                                              (Term.Tup
                                                                                (Quan.Q1)
                                                                                (Term.Lab "Succ")
                                                                                (Term.Tup
                                                                                  (Quan.Q1)
                                                                                  (Term.Tup
                                                                                    (Quan.Q1)
                                                                                    (Term.Lab
                                                                                      "Succ")
                                                                                    (Term.Tup
                                                                                      (Quan.Q1)
                                                                                      (Term.Tup
                                                                                        (Quan.Q1)
                                                                                        (Term.Lab
                                                                                          "Succ")
                                                                                        (Term.Tup
                                                                                          (Quan.Q1)
                                                                                          (Term.Tup
                                                                                            (Quan.Q1)
                                                                                            (Term.Lab
                                                                                              "Succ")
                                                                                            (Term.Tup
                                                                                              (Quan.Q1)
                                                                                              (Term.Tup
                                                                                                (Quan.Q1)
                                                                                                (Term.Lab
                                                                                                  "Succ")
                                                                                                (Term.Tup
                                                                                                  (Quan.Q1)
                                                                                                  (Term.Tup
                                                                                                    (Quan.Q1)
                                                                                                    (Term.Lab
                                                                                                      "Succ")
                                                                                                    (Term.Tup
                                                                                                      (Quan.Q1)
                                                                                                      (Term.Tup
                                                                                                        (Quan.Q1)
                                                                                                        (Term.Lab
                                                                                                          "Succ")
                                                                                                        (Term.Tup
                                                                                                          (Quan.Q1)
                                                                                                          (Term.Tup
                                                                                                            (Quan.Q1)
                                                                                                            (Term.Lab
                                                                                                              "Succ")
                                                                                                            (Term.Tup
                                                                                                              (Quan.Q1)
                                                                                                              (Term.Tup
                                                                                                                (Quan.Q1)
                                                                                                                (Term.Lab
                                                                                                                  "Succ")
                                                                                                                (Term.Tup
                                                                                                                  (Quan.Q1)
                                                                                                                  (Term.Tup
                                                                                                                    (Quan.Q1)
                                                                                                                    (Term.Lab
                                                                                                                      "Zero")
                                                                                                                    (Term.Lab
                                                                                                                      "()"))
                                                                                                                  (Term.Lab
                                                                                                                    "()")))
                                                                                                              (Term.Lab
                                                                                                                "()")))
                                                                                                          (Term.Lab
                                                                                                            "()")))
                                                                                                      (Term.Lab
                                                                                                        "()")))
                                                                                                  (Term.Lab
                                                                                                    "()")))
                                                                                              (Term.Lab
                                                                                                "()")))
                                                                                          (Term.Lab
                                                                                            "()")))
                                                                                      (Term.Lab
                                                                                        "()")))
                                                                                  (Term.Lab "()")))
                                                                              (Term.Lab "()")))
                                                                          (Term.Lab "()")))
                                                                      (Term.Lab "()")))
                                                                  (Term.Lab "()")))
                                                              (Term.Lab "()")))
                                                          (Term.Lab "()")))
                                                      (Term.Lab "()")))
                                                  (Term.Lab "()")))
                                              (Term.Lab "()")))
                                          (Term.Lab "()")))
                                      (Term.Lab "()")))
                                  (Term.Lab "()")))
                              (Term.Lab "()")))
                          (Term.Lab "()")))
                      (Term.Lab "()"))))
                (Term.Var 0))
              (Term.Efq))))
        (Term.Efq)),
    false⟩

def «evalVersion.Cmp.is_eq» : Def :=
  ⟨"Cmp.is_eq",
    Term.All (Quan.Q1) (Term.Ref "Cmp") (Term.Ref "Bool"),
    Term.Prj
      (Term.Mat
        "EQ"
        (Term.Mat "()" (Term.Tup (Quan.Q1) (Term.Lab "True") (Term.Lab "()")) (Term.Efq))
        (Term.Lam
          (Quan.Q1)
          (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "False") (Term.Lab "()"))))),
    false⟩

def «evalVersion.Bool.cmp» : Def :=
  ⟨"Bool.cmp",
    Term.All (Quan.Q1) (Term.Ref "Bool") (Term.All (Quan.Q1) (Term.Ref "Bool") (Term.Ref "Cmp")),
    Term.Prj
      (Term.Mat
        "False"
        (Term.Mat
          "()"
          (Term.Prj
            (Term.Mat
              "False"
              (Term.Mat "()" (Term.Tup (Quan.Q1) (Term.Lab "EQ") (Term.Lab "()")) (Term.Efq))
              (Term.Mat
                "True"
                (Term.Mat "()" (Term.Tup (Quan.Q1) (Term.Lab "LT") (Term.Lab "()")) (Term.Efq))
                (Term.Efq))))
          (Term.Efq))
        (Term.Mat
          "True"
          (Term.Mat
            "()"
            (Term.Prj
              (Term.Mat
                "False"
                (Term.Mat "()" (Term.Tup (Quan.Q1) (Term.Lab "GT") (Term.Lab "()")) (Term.Efq))
                (Term.Mat
                  "True"
                  (Term.Mat "()" (Term.Tup (Quan.Q1) (Term.Lab "EQ") (Term.Lab "()")) (Term.Efq))
                  (Term.Efq))))
            (Term.Efq))
          (Term.Efq))),
    false⟩

def «evalVersion.Word.cmp.fin» : Def :=
  ⟨"Word.cmp.fin",
    Term.All
      (Quan.Q1)
      (Term.Ref "Bool")
      (Term.All (Quan.Q1) (Term.Ref "Bool") (Term.All (Quan.Q1) (Term.Ref "Cmp") (Term.Ref "Cmp"))),
    Term.Lam
      (Quan.Q1)
      (Term.Lam
        (Quan.Q1)
        (Term.Prj
          (Term.Mat
            "LT"
            (Term.Mat "()" (Term.Tup (Quan.Q1) (Term.Lab "LT") (Term.Lab "()")) (Term.Efq))
            (Term.Mat
              "EQ"
              (Term.Mat
                "()"
                (Term.App
                  (Quan.Q1)
                  (Term.App (Quan.Q1) (Term.Ref "Bool.cmp") (Term.Var 1))
                  (Term.Var 0))
                (Term.Efq))
              (Term.Mat
                "GT"
                (Term.Mat "()" (Term.Tup (Quan.Q1) (Term.Lab "GT") (Term.Lab "()")) (Term.Efq))
                (Term.Efq)))))),
    false⟩

def «evalVersion.Word.cmp» : Def :=
  ⟨"Word.cmp",
    Term.All
      (Quan.Q1)
      (Term.Ref "Nat")
      (Term.All
        (Quan.Q1)
        (Term.App (Quan.Q1) (Term.Ref "Word") (Term.Var 0))
        (Term.All (Quan.Q1) (Term.App (Quan.Q1) (Term.Ref "Word") (Term.Var 1)) (Term.Ref "Cmp"))),
    Term.Prj
      (Term.Mat
        "Zero"
        (Term.Mat
          "()"
          (Term.Lam
            (Quan.Q1)
            (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "EQ") (Term.Lab "()"))))
          (Term.Efq))
        (Term.Mat
          "Succ"
          (Term.Prj
            (Term.Lam
              (Quan.Q1)
              (Term.Mat
                "()"
                (Term.Prj
                  (Term.Mat
                    "WCon"
                    (Term.Prj
                      (Term.Lam
                        (Quan.Q1)
                        (Term.Prj
                          (Term.Lam
                            (Quan.Q1)
                            (Term.Mat
                              "()"
                              (Term.Prj
                                (Term.Mat
                                  "WCon"
                                  (Term.Prj
                                    (Term.Lam
                                      (Quan.Q1)
                                      (Term.Prj
                                        (Term.Lam
                                          (Quan.Q1)
                                          (Term.Mat
                                            "()"
                                            (Term.App
                                              (Quan.Q1)
                                              (Term.App
                                                (Quan.Q1)
                                                (Term.App
                                                  (Quan.Q1)
                                                  (Term.Ref "Word.cmp.fin")
                                                  (Term.Var 3))
                                                (Term.Var 1))
                                              (Term.App
                                                (Quan.Q1)
                                                (Term.App
                                                  (Quan.Q1)
                                                  (Term.App
                                                    (Quan.Q1)
                                                    (Term.Ref "Word.cmp")
                                                    (Term.Var 4))
                                                  (Term.Var 2))
                                                (Term.Var 0)))
                                            (Term.Efq))))))
                                  (Term.Efq)))
                              (Term.Efq))))))
                    (Term.Efq)))
                (Term.Efq))))
          (Term.Efq))),
    false⟩

def «evalVersion.Byte.is_eq» : Def :=
  ⟨"Byte.is_eq",
    Term.All
      (Quan.Q1)
      (Term.App
        (Quan.Q1)
        (Term.Ref "Word")
        (Term.Tup
          (Quan.Q1)
          (Term.Lab "Succ")
          (Term.Tup
            (Quan.Q1)
            (Term.Tup
              (Quan.Q1)
              (Term.Lab "Succ")
              (Term.Tup
                (Quan.Q1)
                (Term.Tup
                  (Quan.Q1)
                  (Term.Lab "Succ")
                  (Term.Tup
                    (Quan.Q1)
                    (Term.Tup
                      (Quan.Q1)
                      (Term.Lab "Succ")
                      (Term.Tup
                        (Quan.Q1)
                        (Term.Tup
                          (Quan.Q1)
                          (Term.Lab "Succ")
                          (Term.Tup
                            (Quan.Q1)
                            (Term.Tup
                              (Quan.Q1)
                              (Term.Lab "Succ")
                              (Term.Tup
                                (Quan.Q1)
                                (Term.Tup
                                  (Quan.Q1)
                                  (Term.Lab "Succ")
                                  (Term.Tup
                                    (Quan.Q1)
                                    (Term.Tup
                                      (Quan.Q1)
                                      (Term.Lab "Succ")
                                      (Term.Tup
                                        (Quan.Q1)
                                        (Term.Tup (Quan.Q1) (Term.Lab "Zero") (Term.Lab "()"))
                                        (Term.Lab "()")))
                                    (Term.Lab "()")))
                                (Term.Lab "()")))
                            (Term.Lab "()")))
                        (Term.Lab "()")))
                    (Term.Lab "()")))
                (Term.Lab "()")))
            (Term.Lab "()"))))
      (Term.All
        (Quan.Q1)
        (Term.App
          (Quan.Q1)
          (Term.Ref "Word")
          (Term.Tup
            (Quan.Q1)
            (Term.Lab "Succ")
            (Term.Tup
              (Quan.Q1)
              (Term.Tup
                (Quan.Q1)
                (Term.Lab "Succ")
                (Term.Tup
                  (Quan.Q1)
                  (Term.Tup
                    (Quan.Q1)
                    (Term.Lab "Succ")
                    (Term.Tup
                      (Quan.Q1)
                      (Term.Tup
                        (Quan.Q1)
                        (Term.Lab "Succ")
                        (Term.Tup
                          (Quan.Q1)
                          (Term.Tup
                            (Quan.Q1)
                            (Term.Lab "Succ")
                            (Term.Tup
                              (Quan.Q1)
                              (Term.Tup
                                (Quan.Q1)
                                (Term.Lab "Succ")
                                (Term.Tup
                                  (Quan.Q1)
                                  (Term.Tup
                                    (Quan.Q1)
                                    (Term.Lab "Succ")
                                    (Term.Tup
                                      (Quan.Q1)
                                      (Term.Tup
                                        (Quan.Q1)
                                        (Term.Lab "Succ")
                                        (Term.Tup
                                          (Quan.Q1)
                                          (Term.Tup (Quan.Q1) (Term.Lab "Zero") (Term.Lab "()"))
                                          (Term.Lab "()")))
                                      (Term.Lab "()")))
                                  (Term.Lab "()")))
                              (Term.Lab "()")))
                          (Term.Lab "()")))
                      (Term.Lab "()")))
                  (Term.Lab "()")))
              (Term.Lab "()"))))
        (Term.Ref "Bool")),
    Term.Lam
      (Quan.Q1)
      (Term.Lam
        (Quan.Q1)
        (Term.App
          (Quan.Q1)
          (Term.Ref "Cmp.is_eq")
          (Term.App
            (Quan.Q1)
            (Term.App
              (Quan.Q1)
              (Term.App
                (Quan.Q1)
                (Term.Ref "Word.cmp")
                (Term.Tup
                  (Quan.Q1)
                  (Term.Lab "Succ")
                  (Term.Tup
                    (Quan.Q1)
                    (Term.Tup
                      (Quan.Q1)
                      (Term.Lab "Succ")
                      (Term.Tup
                        (Quan.Q1)
                        (Term.Tup
                          (Quan.Q1)
                          (Term.Lab "Succ")
                          (Term.Tup
                            (Quan.Q1)
                            (Term.Tup
                              (Quan.Q1)
                              (Term.Lab "Succ")
                              (Term.Tup
                                (Quan.Q1)
                                (Term.Tup
                                  (Quan.Q1)
                                  (Term.Lab "Succ")
                                  (Term.Tup
                                    (Quan.Q1)
                                    (Term.Tup
                                      (Quan.Q1)
                                      (Term.Lab "Succ")
                                      (Term.Tup
                                        (Quan.Q1)
                                        (Term.Tup
                                          (Quan.Q1)
                                          (Term.Lab "Succ")
                                          (Term.Tup
                                            (Quan.Q1)
                                            (Term.Tup
                                              (Quan.Q1)
                                              (Term.Lab "Succ")
                                              (Term.Tup
                                                (Quan.Q1)
                                                (Term.Tup
                                                  (Quan.Q1)
                                                  (Term.Lab "Zero")
                                                  (Term.Lab "()"))
                                                (Term.Lab "()")))
                                            (Term.Lab "()")))
                                        (Term.Lab "()")))
                                    (Term.Lab "()")))
                                (Term.Lab "()")))
                            (Term.Lab "()")))
                        (Term.Lab "()")))
                    (Term.Lab "()"))))
              (Term.Var 1))
            (Term.Var 0)))),
    false⟩

def «evalVersion.Bool.and» : Def :=
  ⟨"Bool.and",
    Term.All (Quan.Q1) (Term.Ref "Bool") (Term.All (Quan.Q1) (Term.Ref "Bool") (Term.Ref "Bool")),
    Term.Prj
      (Term.Mat
        "False"
        (Term.Mat
          "()"
          (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "False") (Term.Lab "()")))
          (Term.Efq))
        (Term.Mat "True" (Term.Mat "()" (Term.Lam (Quan.Q1) (Term.Var 0)) (Term.Efq)) (Term.Efq))),
    false⟩

def «evalVersion.Name.is_eq» : Def :=
  ⟨"Name.is_eq",
    Term.All
      (Quan.Q1)
      (Term.App
        (Quan.Q0)
        (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
        (Term.App
          (Quan.Q1)
          (Term.Ref "Word")
          (Term.Tup
            (Quan.Q1)
            (Term.Lab "Succ")
            (Term.Tup
              (Quan.Q1)
              (Term.Tup
                (Quan.Q1)
                (Term.Lab "Succ")
                (Term.Tup
                  (Quan.Q1)
                  (Term.Tup
                    (Quan.Q1)
                    (Term.Lab "Succ")
                    (Term.Tup
                      (Quan.Q1)
                      (Term.Tup
                        (Quan.Q1)
                        (Term.Lab "Succ")
                        (Term.Tup
                          (Quan.Q1)
                          (Term.Tup
                            (Quan.Q1)
                            (Term.Lab "Succ")
                            (Term.Tup
                              (Quan.Q1)
                              (Term.Tup
                                (Quan.Q1)
                                (Term.Lab "Succ")
                                (Term.Tup
                                  (Quan.Q1)
                                  (Term.Tup
                                    (Quan.Q1)
                                    (Term.Lab "Succ")
                                    (Term.Tup
                                      (Quan.Q1)
                                      (Term.Tup
                                        (Quan.Q1)
                                        (Term.Lab "Succ")
                                        (Term.Tup
                                          (Quan.Q1)
                                          (Term.Tup (Quan.Q1) (Term.Lab "Zero") (Term.Lab "()"))
                                          (Term.Lab "()")))
                                      (Term.Lab "()")))
                                  (Term.Lab "()")))
                              (Term.Lab "()")))
                          (Term.Lab "()")))
                      (Term.Lab "()")))
                  (Term.Lab "()")))
              (Term.Lab "()")))))
      (Term.All
        (Quan.Q1)
        (Term.App
          (Quan.Q0)
          (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
          (Term.App
            (Quan.Q1)
            (Term.Ref "Word")
            (Term.Tup
              (Quan.Q1)
              (Term.Lab "Succ")
              (Term.Tup
                (Quan.Q1)
                (Term.Tup
                  (Quan.Q1)
                  (Term.Lab "Succ")
                  (Term.Tup
                    (Quan.Q1)
                    (Term.Tup
                      (Quan.Q1)
                      (Term.Lab "Succ")
                      (Term.Tup
                        (Quan.Q1)
                        (Term.Tup
                          (Quan.Q1)
                          (Term.Lab "Succ")
                          (Term.Tup
                            (Quan.Q1)
                            (Term.Tup
                              (Quan.Q1)
                              (Term.Lab "Succ")
                              (Term.Tup
                                (Quan.Q1)
                                (Term.Tup
                                  (Quan.Q1)
                                  (Term.Lab "Succ")
                                  (Term.Tup
                                    (Quan.Q1)
                                    (Term.Tup
                                      (Quan.Q1)
                                      (Term.Lab "Succ")
                                      (Term.Tup
                                        (Quan.Q1)
                                        (Term.Tup
                                          (Quan.Q1)
                                          (Term.Lab "Succ")
                                          (Term.Tup
                                            (Quan.Q1)
                                            (Term.Tup (Quan.Q1) (Term.Lab "Zero") (Term.Lab "()"))
                                            (Term.Lab "()")))
                                        (Term.Lab "()")))
                                    (Term.Lab "()")))
                                (Term.Lab "()")))
                            (Term.Lab "()")))
                        (Term.Lab "()")))
                    (Term.Lab "()")))
                (Term.Lab "()")))))
        (Term.Ref "Bool")),
    Term.Prj
      (Term.Mat
        "Nil"
        (Term.Mat
          "()"
          (Term.Prj
            (Term.Mat
              "Nil"
              (Term.Mat "()" (Term.Tup (Quan.Q1) (Term.Lab "True") (Term.Lab "()")) (Term.Efq))
              (Term.Lam
                (Quan.Q1)
                (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "False") (Term.Lab "()"))))))
          (Term.Efq))
        (Term.Mat
          "Con"
          (Term.Prj
            (Term.Lam
              (Quan.Q1)
              (Term.Prj
                (Term.Lam
                  (Quan.Q1)
                  (Term.Mat
                    "()"
                    (Term.Prj
                      (Term.Mat
                        "Con"
                        (Term.Prj
                          (Term.Lam
                            (Quan.Q1)
                            (Term.Prj
                              (Term.Lam
                                (Quan.Q1)
                                (Term.Mat
                                  "()"
                                  (Term.App
                                    (Quan.Q1)
                                    (Term.App
                                      (Quan.Q1)
                                      (Term.Ref "Bool.and")
                                      (Term.App
                                        (Quan.Q1)
                                        (Term.App (Quan.Q1) (Term.Ref "Byte.is_eq") (Term.Var 3))
                                        (Term.Var 1)))
                                    (Term.App
                                      (Quan.Q1)
                                      (Term.App (Quan.Q1) (Term.Ref "Name.is_eq") (Term.Var 2))
                                      (Term.Var 0)))
                                  (Term.Efq))))))
                        (Term.Lam
                          (Quan.Q1)
                          (Term.Lam
                            (Quan.Q1)
                            (Term.Tup (Quan.Q1) (Term.Lab "False") (Term.Lab "()"))))))
                    (Term.Efq))))))
          (Term.Efq))),
    false⟩

def «evalVersion.Bool.or» : Def :=
  ⟨"Bool.or",
    Term.All (Quan.Q1) (Term.Ref "Bool") (Term.All (Quan.Q1) (Term.Ref "Bool") (Term.Ref "Bool")),
    Term.Prj
      (Term.Mat
        "False"
        (Term.Mat "()" (Term.Lam (Quan.Q1) (Term.Var 0)) (Term.Efq))
        (Term.Mat
          "True"
          (Term.Mat
            "()"
            (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "True") (Term.Lab "()")))
            (Term.Efq))
          (Term.Efq))),
    false⟩

def «evalVersion.Cmp.is_lt» : Def :=
  ⟨"Cmp.is_lt",
    Term.All (Quan.Q1) (Term.Ref "Cmp") (Term.Ref "Bool"),
    Term.Prj
      (Term.Mat
        "LT"
        (Term.Mat "()" (Term.Tup (Quan.Q1) (Term.Lab "True") (Term.Lab "()")) (Term.Efq))
        (Term.Lam
          (Quan.Q1)
          (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "False") (Term.Lab "()"))))),
    false⟩

def «evalVersion.Nat.sub» : Def :=
  ⟨"Nat.sub",
    Term.All (Quan.Q1) (Term.Ref "Nat") (Term.All (Quan.Q1) (Term.Ref "Nat") (Term.Ref "Nat")),
    Term.Prj
      (Term.Mat
        "Zero"
        (Term.Mat
          "()"
          (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "Zero") (Term.Lab "()")))
          (Term.Efq))
        (Term.Mat
          "Succ"
          (Term.Prj
            (Term.Lam
              (Quan.Q2)
              (Term.Mat
                "()"
                (Term.Prj
                  (Term.Mat
                    "Zero"
                    (Term.Mat
                      "()"
                      (Term.Tup
                        (Quan.Q1)
                        (Term.Lab "Succ")
                        (Term.Tup (Quan.Q1) (Term.Var 0) (Term.Lab "()")))
                      (Term.Efq))
                    (Term.Mat
                      "Succ"
                      (Term.Prj
                        (Term.Lam
                          (Quan.Q1)
                          (Term.Mat
                            "()"
                            (Term.App
                              (Quan.Q1)
                              (Term.App (Quan.Q1) (Term.Ref "Nat.sub") (Term.Var 1))
                              (Term.Var 0))
                            (Term.Efq))))
                      (Term.Efq))))
                (Term.Efq))))
          (Term.Efq))),
    false⟩

def «evalVersion.Bool.not» : Def :=
  ⟨"Bool.not",
    Term.All (Quan.Q1) (Term.Ref "Bool") (Term.Ref "Bool"),
    Term.Prj
      (Term.Mat
        "False"
        (Term.Mat "()" (Term.Tup (Quan.Q1) (Term.Lab "True") (Term.Lab "()")) (Term.Efq))
        (Term.Mat
          "True"
          (Term.Mat "()" (Term.Tup (Quan.Q1) (Term.Lab "False") (Term.Lab "()")) (Term.Efq))
          (Term.Efq))),
    false⟩

def «evalVersion.Nat.cmp» : Def :=
  ⟨"Nat.cmp",
    Term.All (Quan.Q1) (Term.Ref "Nat") (Term.All (Quan.Q1) (Term.Ref "Nat") (Term.Ref "Cmp")),
    Term.Prj
      (Term.Mat
        "Zero"
        (Term.Mat
          "()"
          (Term.Prj
            (Term.Mat
              "Zero"
              (Term.Mat "()" (Term.Tup (Quan.Q1) (Term.Lab "EQ") (Term.Lab "()")) (Term.Efq))
              (Term.Mat
                "Succ"
                (Term.Prj
                  (Term.Lam
                    (Quan.Q1)
                    (Term.Mat
                      "()"
                      (Term.Tup (Quan.Q1) (Term.Lab "LT") (Term.Lab "()"))
                      (Term.Efq))))
                (Term.Efq))))
          (Term.Efq))
        (Term.Mat
          "Succ"
          (Term.Prj
            (Term.Lam
              (Quan.Q1)
              (Term.Mat
                "()"
                (Term.Prj
                  (Term.Mat
                    "Zero"
                    (Term.Mat "()" (Term.Tup (Quan.Q1) (Term.Lab "GT") (Term.Lab "()")) (Term.Efq))
                    (Term.Mat
                      "Succ"
                      (Term.Prj
                        (Term.Lam
                          (Quan.Q1)
                          (Term.Mat
                            "()"
                            (Term.App
                              (Quan.Q1)
                              (Term.App (Quan.Q1) (Term.Ref "Nat.cmp") (Term.Var 1))
                              (Term.Var 0))
                            (Term.Efq))))
                      (Term.Efq))))
                (Term.Efq))))
          (Term.Efq))),
    false⟩

def «evalVersion.Nat.add» : Def :=
  ⟨"Nat.add",
    Term.All (Quan.Q1) (Term.Ref "Nat") (Term.All (Quan.Q1) (Term.Ref "Nat") (Term.Ref "Nat")),
    Term.Prj
      (Term.Mat
        "Zero"
        (Term.Mat "()" (Term.Lam (Quan.Q1) (Term.Var 0)) (Term.Efq))
        (Term.Mat
          "Succ"
          (Term.Prj
            (Term.Lam
              (Quan.Q1)
              (Term.Mat
                "()"
                (Term.Lam
                  (Quan.Q1)
                  (Term.Tup
                    (Quan.Q1)
                    (Term.Lab "Succ")
                    (Term.Tup
                      (Quan.Q1)
                      (Term.App
                        (Quan.Q1)
                        (Term.App (Quan.Q1) (Term.Ref "Nat.add") (Term.Var 1))
                        (Term.Var 0))
                      (Term.Lab "()"))))
                (Term.Efq))))
          (Term.Efq))),
    false⟩

def «evalVersion.Nat.is_lt» : Def :=
  ⟨"Nat.is_lt",
    Term.All (Quan.Q1) (Term.Ref "Nat") (Term.All (Quan.Q1) (Term.Ref "Nat") (Term.Ref "Bool")),
    Term.Lam
      (Quan.Q1)
      (Term.Lam
        (Quan.Q1)
        (Term.App
          (Quan.Q1)
          (Term.Ref "Cmp.is_lt")
          (Term.App (Quan.Q1) (Term.App (Quan.Q1) (Term.Ref "Nat.cmp") (Term.Var 1)) (Term.Var 0)))),
    false⟩

def «evalVersion.Arg.arms» : Def :=
  ⟨"Arg.arms",
    Term.All (Quan.Q1) (Term.Enu ["Arg"]) (Term.Typ (Term.Lab "Q2")),
    Term.Mat
      "Arg"
      (Term.Sig
        (Quan.Q1)
        (Term.Ref "Quan")
        (Term.Sig (Quan.Q1) (Term.Ref "Term") (Term.Enu ["()"])))
      (Term.Efq),
    false⟩

def «evalVersion.Arg» : Def :=
  ⟨"Arg",
    Term.Typ (Term.Lab "Q2"),
    Term.Sig (Quan.Q1) (Term.Enu ["Arg"]) (Term.App (Quan.Q1) (Term.Ref "Arg.arms") (Term.Var 0)),
    false⟩

def «evalVersion.Quan.live» : Def :=
  ⟨"Quan.live",
    Term.All (Quan.Q1) (Term.Ref "Quan") (Term.Ref "Bool"),
    Term.Prj
      (Term.Mat
        "Quan.Q0"
        (Term.Mat "()" (Term.Tup (Quan.Q1) (Term.Lab "False") (Term.Lab "()")) (Term.Efq))
        (Term.Mat
          "Quan.Q1"
          (Term.Mat "()" (Term.Tup (Quan.Q1) (Term.Lab "True") (Term.Lab "()")) (Term.Efq))
          (Term.Mat
            "Quan.Q2"
            (Term.Mat "()" (Term.Tup (Quan.Q1) (Term.Lab "True") (Term.Lab "()")) (Term.Efq))
            (Term.Efq)))),
    false⟩

def «evalVersion.Quan.lives_as» : Def :=
  ⟨"Quan.lives_as",
    Term.All (Quan.Q1) (Term.Ref "Quan") (Term.All (Quan.Q1) (Term.Ref "Quan") (Term.Ref "Bool")),
    Term.Prj
      (Term.Mat
        "Quan.Q0"
        (Term.Mat
          "()"
          (Term.Prj
            (Term.Mat
              "Quan.Q0"
              (Term.Mat "()" (Term.Tup (Quan.Q1) (Term.Lab "True") (Term.Lab "()")) (Term.Efq))
              (Term.Lam
                (Quan.Q1)
                (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "False") (Term.Lab "()"))))))
          (Term.Efq))
        (Term.Lam
          (Quan.Q1)
          (Term.Lam
            (Quan.Q1)
            (Term.Prj
              (Term.Mat
                "Quan.Q0"
                (Term.Mat "()" (Term.Tup (Quan.Q1) (Term.Lab "False") (Term.Lab "()")) (Term.Efq))
                (Term.Lam
                  (Quan.Q1)
                  (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "True") (Term.Lab "()"))))))))),
    false⟩

def «evalVersion.Quan.fld» : Def :=
  ⟨"Quan.fld",
    Term.All (Quan.Q1) (Term.Ref "Quan") (Term.All (Quan.Q1) (Term.Ref "Quan") (Term.Ref "Quan")),
    Term.Prj
      (Term.Mat
        "Quan.Q0"
        (Term.Mat
          "()"
          (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "Quan.Q0") (Term.Lab "()")))
          (Term.Efq))
        (Term.Mat
          "Quan.Q1"
          (Term.Mat "()" (Term.Lam (Quan.Q1) (Term.Var 0)) (Term.Efq))
          (Term.Mat
            "Quan.Q2"
            (Term.Mat
              "()"
              (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "Quan.Q2") (Term.Lab "()")))
              (Term.Efq))
            (Term.Efq)))),
    false⟩

def «evalVersion.Term.is_data» : Def :=
  ⟨"Term.is_data",
    Term.All (Quan.Q1) (Term.Ref "Term") (Term.Ref "Bool"),
    Term.Prj
      (Term.Mat
        "Term.Lab"
        (Term.Prj
          (Term.Lam
            (Quan.Q1)
            (Term.Mat "()" (Term.Tup (Quan.Q1) (Term.Lab "True") (Term.Lab "()")) (Term.Efq))))
        (Term.Mat
          "Term.Rfl"
          (Term.Mat "()" (Term.Tup (Quan.Q1) (Term.Lab "True") (Term.Lab "()")) (Term.Efq))
          (Term.Mat
            "Term.Tup"
            (Term.Prj
              (Term.Lam
                (Quan.Q1)
                (Term.Prj
                  (Term.Lam
                    (Quan.Q1)
                    (Term.Prj
                      (Term.Lam
                        (Quan.Q1)
                        (Term.Mat
                          "()"
                          (Term.App
                            (Quan.Q1)
                            (Term.App
                              (Quan.Q1)
                              (Term.Ref "Bool.and")
                              (Term.App
                                (Quan.Q1)
                                (Term.App
                                  (Quan.Q1)
                                  (Term.Ref "Bool.or")
                                  (Term.App
                                    (Quan.Q1)
                                    (Term.Ref "Bool.not")
                                    (Term.App (Quan.Q1) (Term.Ref "Quan.live") (Term.Var 2))))
                                (Term.App (Quan.Q1) (Term.Ref "Term.is_data") (Term.Var 1))))
                            (Term.App (Quan.Q1) (Term.Ref "Term.is_data") (Term.Var 0)))
                          (Term.Efq))))))))
            (Term.Lam
              (Quan.Q1)
              (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "False") (Term.Lab "()"))))))),
    false⟩

def «evalVersion.Quan.fits» : Def :=
  ⟨"Quan.fits",
    Term.All (Quan.Q1) (Term.Ref "Quan") (Term.All (Quan.Q1) (Term.Ref "Term") (Term.Ref "Bool")),
    Term.Prj
      (Term.Mat
        "Quan.Q2"
        (Term.Mat
          "()"
          (Term.Lam (Quan.Q1) (Term.App (Quan.Q1) (Term.Ref "Term.is_data") (Term.Var 0)))
          (Term.Efq))
        (Term.Lam
          (Quan.Q1)
          (Term.Lam
            (Quan.Q1)
            (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "True") (Term.Lab "()")))))),
    false⟩

def «evalVersion.Quan.binds» : Def :=
  ⟨"Quan.binds",
    Term.All
      (Quan.Q2)
      (Term.Ref "Quan")
      (Term.All
        (Quan.Q1)
        (Term.Ref "Quan")
        (Term.All (Quan.Q1) (Term.Ref "Term") (Term.Ref "Bool"))),
    Term.Lam
      (Quan.Q2)
      (Term.Lam
        (Quan.Q1)
        (Term.Lam
          (Quan.Q1)
          (Term.App
            (Quan.Q1)
            (Term.App
              (Quan.Q1)
              (Term.Ref "Bool.and")
              (Term.App
                (Quan.Q1)
                (Term.App (Quan.Q1) (Term.Ref "Quan.lives_as") (Term.Var 2))
                (Term.Var 1)))
            (Term.App
              (Quan.Q1)
              (Term.App (Quan.Q1) (Term.Ref "Quan.fits") (Term.Var 2))
              (Term.Var 0))))),
    false⟩

def «evalVersion.Term.is_former» : Def :=
  ⟨"Term.is_former",
    Term.All (Quan.Q1) (Term.Ref "Term") (Term.Ref "Bool"),
    Term.Prj
      (Term.Mat
        "Term.Typ"
        (Term.Prj
          (Term.Lam
            (Quan.Q1)
            (Term.Mat "()" (Term.Tup (Quan.Q1) (Term.Lab "True") (Term.Lab "()")) (Term.Efq))))
        (Term.Mat
          "Term.All"
          (Term.Prj
            (Term.Lam
              (Quan.Q1)
              (Term.Prj
                (Term.Lam
                  (Quan.Q1)
                  (Term.Prj
                    (Term.Lam
                      (Quan.Q1)
                      (Term.Mat
                        "()"
                        (Term.Tup (Quan.Q1) (Term.Lab "True") (Term.Lab "()"))
                        (Term.Efq))))))))
          (Term.Mat
            "Term.Sig"
            (Term.Prj
              (Term.Lam
                (Quan.Q1)
                (Term.Prj
                  (Term.Lam
                    (Quan.Q1)
                    (Term.Prj
                      (Term.Lam
                        (Quan.Q1)
                        (Term.Mat
                          "()"
                          (Term.Tup (Quan.Q1) (Term.Lab "True") (Term.Lab "()"))
                          (Term.Efq))))))))
            (Term.Mat
              "Term.Enu"
              (Term.Prj
                (Term.Lam
                  (Quan.Q1)
                  (Term.Mat
                    "()"
                    (Term.Tup (Quan.Q1) (Term.Lab "True") (Term.Lab "()"))
                    (Term.Efq))))
              (Term.Mat
                "Term.Eql"
                (Term.Prj
                  (Term.Lam
                    (Quan.Q1)
                    (Term.Prj
                      (Term.Lam
                        (Quan.Q1)
                        (Term.Prj
                          (Term.Lam
                            (Quan.Q1)
                            (Term.Mat
                              "()"
                              (Term.Tup (Quan.Q1) (Term.Lab "True") (Term.Lab "()"))
                              (Term.Efq))))))))
                (Term.Mat
                  "Term.Lam"
                  (Term.Prj
                    (Term.Lam
                      (Quan.Q1)
                      (Term.Prj
                        (Term.Lam
                          (Quan.Q1)
                          (Term.Mat
                            "()"
                            (Term.Tup (Quan.Q1) (Term.Lab "True") (Term.Lab "()"))
                            (Term.Efq))))))
                  (Term.Mat
                    "Term.Prj"
                    (Term.Prj
                      (Term.Lam
                        (Quan.Q1)
                        (Term.Mat
                          "()"
                          (Term.Tup (Quan.Q1) (Term.Lab "True") (Term.Lab "()"))
                          (Term.Efq))))
                    (Term.Mat
                      "Term.Mat"
                      (Term.Prj
                        (Term.Lam
                          (Quan.Q1)
                          (Term.Prj
                            (Term.Lam
                              (Quan.Q1)
                              (Term.Prj
                                (Term.Lam
                                  (Quan.Q1)
                                  (Term.Mat
                                    "()"
                                    (Term.Tup (Quan.Q1) (Term.Lab "True") (Term.Lab "()"))
                                    (Term.Efq))))))))
                      (Term.Mat
                        "Term.Efq"
                        (Term.Mat
                          "()"
                          (Term.Tup (Quan.Q1) (Term.Lab "True") (Term.Lab "()"))
                          (Term.Efq))
                        (Term.Mat
                          "Term.Tup"
                          (Term.Prj
                            (Term.Lam
                              (Quan.Q1)
                              (Term.Prj
                                (Term.Lam
                                  (Quan.Q1)
                                  (Term.Prj
                                    (Term.Lam
                                      (Quan.Q1)
                                      (Term.Mat
                                        "()"
                                        (Term.Tup (Quan.Q1) (Term.Lab "True") (Term.Lab "()"))
                                        (Term.Efq))))))))
                          (Term.Mat
                            "Term.Lab"
                            (Term.Prj
                              (Term.Lam
                                (Quan.Q1)
                                (Term.Mat
                                  "()"
                                  (Term.Tup (Quan.Q1) (Term.Lab "True") (Term.Lab "()"))
                                  (Term.Efq))))
                            (Term.Mat
                              "Term.Rfl"
                              (Term.Mat
                                "()"
                                (Term.Tup (Quan.Q1) (Term.Lab "True") (Term.Lab "()"))
                                (Term.Efq))
                              (Term.Lam
                                (Quan.Q1)
                                (Term.Lam
                                  (Quan.Q1)
                                  (Term.Tup
                                    (Quan.Q1)
                                    (Term.Lab "False")
                                    (Term.Lab "()")))))))))))))))),
    false⟩

def «evalVersion.Term.takes» : Def :=
  ⟨"Term.takes",
    Term.All (Quan.Q1) (Term.Ref "Term") (Term.Ref "Bool"),
    Term.Prj
      (Term.Mat
        "Term.Lam"
        (Term.Prj
          (Term.Lam
            (Quan.Q1)
            (Term.Prj
              (Term.Lam
                (Quan.Q1)
                (Term.Mat
                  "()"
                  (Term.Tup (Quan.Q1) (Term.Lab "True") (Term.Lab "()"))
                  (Term.Efq))))))
        (Term.Mat
          "Term.Prj"
          (Term.Prj
            (Term.Lam
              (Quan.Q1)
              (Term.Mat "()" (Term.Tup (Quan.Q1) (Term.Lab "True") (Term.Lab "()")) (Term.Efq))))
          (Term.Mat
            "Term.Mat"
            (Term.Prj
              (Term.Lam
                (Quan.Q1)
                (Term.Prj
                  (Term.Lam
                    (Quan.Q1)
                    (Term.Prj
                      (Term.Lam
                        (Quan.Q1)
                        (Term.Mat
                          "()"
                          (Term.Tup (Quan.Q1) (Term.Lab "True") (Term.Lab "()"))
                          (Term.Efq))))))))
            (Term.Mat
              "Term.Efq"
              (Term.Mat "()" (Term.Tup (Quan.Q1) (Term.Lab "True") (Term.Lab "()")) (Term.Efq))
              (Term.Lam
                (Quan.Q1)
                (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "False") (Term.Lab "()")))))))),
    false⟩

def «evalVersion.Term.head» : Def :=
  ⟨"Term.head",
    Term.All (Quan.Q1) (Term.Ref "Term") (Term.Ref "Term"),
    Term.Prj
      (Term.Mat
        "Term.App"
        (Term.Prj
          (Term.Lam
            (Quan.Q1)
            (Term.Prj
              (Term.Lam
                (Quan.Q1)
                (Term.Prj
                  (Term.Lam
                    (Quan.Q1)
                    (Term.Mat
                      "()"
                      (Term.App (Quan.Q1) (Term.Ref "Term.head") (Term.Var 1))
                      (Term.Efq))))))))
        (Term.Lam (Quan.Q1) (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Var 1) (Term.Var 0))))),
    false⟩

def «evalVersion.Term.args» : Def :=
  ⟨"Term.args",
    Term.All
      (Quan.Q1)
      (Term.Ref "Term")
      (Term.All
        (Quan.Q1)
        (Term.App (Quan.Q0) (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "Arg"))
        (Term.App
          (Quan.Q0)
          (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
          (Term.Ref "Arg"))),
    Term.Prj
      (Term.Mat
        "Term.App"
        (Term.Prj
          (Term.Lam
            (Quan.Q1)
            (Term.Prj
              (Term.Lam
                (Quan.Q1)
                (Term.Prj
                  (Term.Lam
                    (Quan.Q1)
                    (Term.Mat
                      "()"
                      (Term.Lam
                        (Quan.Q1)
                        (Term.App
                          (Quan.Q1)
                          (Term.App (Quan.Q1) (Term.Ref "Term.args") (Term.Var 2))
                          (Term.Tup
                            (Quan.Q1)
                            (Term.Lab "Con")
                            (Term.Tup
                              (Quan.Q1)
                              (Term.Tup
                                (Quan.Q1)
                                (Term.Lab "Arg")
                                (Term.Tup
                                  (Quan.Q1)
                                  (Term.Var 3)
                                  (Term.Tup (Quan.Q1) (Term.Var 1) (Term.Lab "()"))))
                              (Term.Tup (Quan.Q1) (Term.Var 0) (Term.Lab "()"))))))
                      (Term.Efq))))))))
        (Term.Lam (Quan.Q1) (Term.Lam (Quan.Q1) (Term.Lam (Quan.Q1) (Term.Var 0))))),
    false⟩

def «evalVersion.Term.spine» : Def :=
  ⟨"Term.spine",
    Term.All
      (Quan.Q1)
      (Term.App (Quan.Q0) (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "Arg"))
      (Term.All (Quan.Q1) (Term.Ref "Term") (Term.Ref "Term")),
    Term.Prj
      (Term.Mat
        "Nil"
        (Term.Mat "()" (Term.Lam (Quan.Q1) (Term.Var 0)) (Term.Efq))
        (Term.Mat
          "Con"
          (Term.Prj
            (Term.Prj
              (Term.Mat
                "Arg"
                (Term.Prj
                  (Term.Lam
                    (Quan.Q1)
                    (Term.Prj
                      (Term.Lam
                        (Quan.Q1)
                        (Term.Mat
                          "()"
                          (Term.Prj
                            (Term.Lam
                              (Quan.Q1)
                              (Term.Mat
                                "()"
                                (Term.Lam
                                  (Quan.Q1)
                                  (Term.App
                                    (Quan.Q1)
                                    (Term.App (Quan.Q1) (Term.Ref "Term.spine") (Term.Var 1))
                                    (Term.Tup
                                      (Quan.Q1)
                                      (Term.Lab "Term.App")
                                      (Term.Tup
                                        (Quan.Q1)
                                        (Term.Var 3)
                                        (Term.Tup
                                          (Quan.Q1)
                                          (Term.Var 0)
                                          (Term.Tup (Quan.Q1) (Term.Var 2) (Term.Lab "()")))))))
                                (Term.Efq))))
                          (Term.Efq))))))
                (Term.Efq))))
          (Term.Efq))),
    false⟩

def «evalVersion.Env.sub» : Def :=
  ⟨"Env.sub",
    Term.All
      (Quan.Q1)
      (Term.App (Quan.Q0) (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "Term"))
      (Term.All (Quan.Q1) (Term.Ref "Nat") (Term.Ref "Term")),
    Term.Prj
      (Term.Mat
        "Nil"
        (Term.Mat
          "()"
          (Term.Lam
            (Quan.Q1)
            (Term.Tup
              (Quan.Q1)
              (Term.Lab "Term.Var")
              (Term.Tup (Quan.Q1) (Term.Var 0) (Term.Lab "()"))))
          (Term.Efq))
        (Term.Mat
          "Con"
          (Term.Prj
            (Term.Lam
              (Quan.Q1)
              (Term.Prj
                (Term.Lam
                  (Quan.Q1)
                  (Term.Mat
                    "()"
                    (Term.Prj
                      (Term.Mat
                        "Zero"
                        (Term.Mat "()" (Term.Var 1) (Term.Efq))
                        (Term.Mat
                          "Succ"
                          (Term.Prj
                            (Term.Lam
                              (Quan.Q1)
                              (Term.Mat
                                "()"
                                (Term.App
                                  (Quan.Q1)
                                  (Term.App (Quan.Q1) (Term.Ref "Env.sub") (Term.Var 1))
                                  (Term.Var 0))
                                (Term.Efq))))
                          (Term.Efq))))
                    (Term.Efq))))))
          (Term.Efq))),
    false⟩

def «evalVersion.Term.shift.at» : Def :=
  ⟨"Term.shift.at",
    Term.All
      (Quan.Q1)
      (Term.Ref "Bool")
      (Term.All (Quan.Q1) (Term.Ref "Nat") (Term.All (Quan.Q1) (Term.Ref "Nat") (Term.Ref "Nat"))),
    Term.Prj
      (Term.Mat
        "True"
        (Term.Mat "()" (Term.Lam (Quan.Q1) (Term.Lam (Quan.Q1) (Term.Var 1))) (Term.Efq))
        (Term.Mat
          "False"
          (Term.Mat
            "()"
            (Term.Lam
              (Quan.Q1)
              (Term.Lam
                (Quan.Q1)
                (Term.App
                  (Quan.Q1)
                  (Term.App (Quan.Q1) (Term.Ref "Nat.add") (Term.Var 1))
                  (Term.Var 0))))
            (Term.Efq))
          (Term.Efq))),
    false⟩

def «evalVersion.Term.shift» : Def :=
  ⟨"Term.shift",
    Term.All
      (Quan.Q1)
      (Term.Ref "Term")
      (Term.All (Quan.Q2) (Term.Ref "Nat") (Term.All (Quan.Q2) (Term.Ref "Nat") (Term.Ref "Term"))),
    Term.Prj
      (Term.Mat
        "Term.Var"
        (Term.Prj
          (Term.Lam
            (Quan.Q2)
            (Term.Mat
              "()"
              (Term.Lam
                (Quan.Q2)
                (Term.Lam
                  (Quan.Q2)
                  (Term.Tup
                    (Quan.Q1)
                    (Term.Lab "Term.Var")
                    (Term.Tup
                      (Quan.Q1)
                      (Term.App
                        (Quan.Q1)
                        (Term.App
                          (Quan.Q1)
                          (Term.App
                            (Quan.Q1)
                            (Term.Ref "Term.shift.at")
                            (Term.App
                              (Quan.Q1)
                              (Term.App (Quan.Q1) (Term.Ref "Nat.is_lt") (Term.Var 2))
                              (Term.Var 0)))
                          (Term.Var 2))
                        (Term.Var 1))
                      (Term.Lab "()")))))
              (Term.Efq))))
        (Term.Mat
          "Term.Ref"
          (Term.Prj
            (Term.Lam
              (Quan.Q1)
              (Term.Mat
                "()"
                (Term.Lam
                  (Quan.Q2)
                  (Term.Lam
                    (Quan.Q2)
                    (Term.Tup
                      (Quan.Q1)
                      (Term.Lab "Term.Ref")
                      (Term.Tup (Quan.Q1) (Term.Var 2) (Term.Lab "()")))))
                (Term.Efq))))
          (Term.Mat
            "Term.Ann"
            (Term.Prj
              (Term.Lam
                (Quan.Q1)
                (Term.Prj
                  (Term.Lam
                    (Quan.Q1)
                    (Term.Mat
                      "()"
                      (Term.Lam
                        (Quan.Q2)
                        (Term.Lam
                          (Quan.Q2)
                          (Term.Tup
                            (Quan.Q1)
                            (Term.Lab "Term.Ann")
                            (Term.Tup
                              (Quan.Q1)
                              (Term.App
                                (Quan.Q2)
                                (Term.App
                                  (Quan.Q2)
                                  (Term.App (Quan.Q1) (Term.Ref "Term.shift") (Term.Var 3))
                                  (Term.Var 1))
                                (Term.Var 0))
                              (Term.Tup
                                (Quan.Q1)
                                (Term.App
                                  (Quan.Q2)
                                  (Term.App
                                    (Quan.Q2)
                                    (Term.App (Quan.Q1) (Term.Ref "Term.shift") (Term.Var 2))
                                    (Term.Var 1))
                                  (Term.Var 0))
                                (Term.Lab "()"))))))
                      (Term.Efq))))))
            (Term.Mat
              "Term.Let"
              (Term.Prj
                (Term.Lam
                  (Quan.Q1)
                  (Term.Prj
                    (Term.Lam
                      (Quan.Q1)
                      (Term.Prj
                        (Term.Lam
                          (Quan.Q1)
                          (Term.Mat
                            "()"
                            (Term.Lam
                              (Quan.Q2)
                              (Term.Lam
                                (Quan.Q2)
                                (Term.Tup
                                  (Quan.Q1)
                                  (Term.Lab "Term.Let")
                                  (Term.Tup
                                    (Quan.Q1)
                                    (Term.Var 4)
                                    (Term.Tup
                                      (Quan.Q1)
                                      (Term.App
                                        (Quan.Q2)
                                        (Term.App
                                          (Quan.Q2)
                                          (Term.App (Quan.Q1) (Term.Ref "Term.shift") (Term.Var 3))
                                          (Term.Var 1))
                                        (Term.Var 0))
                                      (Term.Tup
                                        (Quan.Q1)
                                        (Term.App
                                          (Quan.Q2)
                                          (Term.App
                                            (Quan.Q2)
                                            (Term.App
                                              (Quan.Q1)
                                              (Term.Ref "Term.shift")
                                              (Term.Var 2))
                                            (Term.Var 1))
                                          (Term.Tup
                                            (Quan.Q1)
                                            (Term.Lab "Succ")
                                            (Term.Tup (Quan.Q1) (Term.Var 0) (Term.Lab "()"))))
                                        (Term.Lab "()")))))))
                            (Term.Efq))))))))
              (Term.Mat
                "Term.Typ"
                (Term.Prj
                  (Term.Lam
                    (Quan.Q1)
                    (Term.Mat
                      "()"
                      (Term.Lam
                        (Quan.Q2)
                        (Term.Lam
                          (Quan.Q2)
                          (Term.Tup
                            (Quan.Q1)
                            (Term.Lab "Term.Typ")
                            (Term.Tup
                              (Quan.Q1)
                              (Term.App
                                (Quan.Q2)
                                (Term.App
                                  (Quan.Q2)
                                  (Term.App (Quan.Q1) (Term.Ref "Term.shift") (Term.Var 2))
                                  (Term.Var 1))
                                (Term.Var 0))
                              (Term.Lab "()")))))
                      (Term.Efq))))
                (Term.Mat
                  "Term.Min"
                  (Term.Prj
                    (Term.Lam
                      (Quan.Q1)
                      (Term.Prj
                        (Term.Lam
                          (Quan.Q1)
                          (Term.Mat
                            "()"
                            (Term.Lam
                              (Quan.Q2)
                              (Term.Lam
                                (Quan.Q2)
                                (Term.Tup
                                  (Quan.Q1)
                                  (Term.Lab "Term.Min")
                                  (Term.Tup
                                    (Quan.Q1)
                                    (Term.App
                                      (Quan.Q2)
                                      (Term.App
                                        (Quan.Q2)
                                        (Term.App (Quan.Q1) (Term.Ref "Term.shift") (Term.Var 3))
                                        (Term.Var 1))
                                      (Term.Var 0))
                                    (Term.Tup
                                      (Quan.Q1)
                                      (Term.App
                                        (Quan.Q2)
                                        (Term.App
                                          (Quan.Q2)
                                          (Term.App (Quan.Q1) (Term.Ref "Term.shift") (Term.Var 2))
                                          (Term.Var 1))
                                        (Term.Var 0))
                                      (Term.Lab "()"))))))
                            (Term.Efq))))))
                  (Term.Mat
                    "Term.All"
                    (Term.Prj
                      (Term.Lam
                        (Quan.Q1)
                        (Term.Prj
                          (Term.Lam
                            (Quan.Q1)
                            (Term.Prj
                              (Term.Lam
                                (Quan.Q1)
                                (Term.Mat
                                  "()"
                                  (Term.Lam
                                    (Quan.Q2)
                                    (Term.Lam
                                      (Quan.Q2)
                                      (Term.Tup
                                        (Quan.Q1)
                                        (Term.Lab "Term.All")
                                        (Term.Tup
                                          (Quan.Q1)
                                          (Term.Var 4)
                                          (Term.Tup
                                            (Quan.Q1)
                                            (Term.App
                                              (Quan.Q2)
                                              (Term.App
                                                (Quan.Q2)
                                                (Term.App
                                                  (Quan.Q1)
                                                  (Term.Ref "Term.shift")
                                                  (Term.Var 3))
                                                (Term.Var 1))
                                              (Term.Var 0))
                                            (Term.Tup
                                              (Quan.Q1)
                                              (Term.App
                                                (Quan.Q2)
                                                (Term.App
                                                  (Quan.Q2)
                                                  (Term.App
                                                    (Quan.Q1)
                                                    (Term.Ref "Term.shift")
                                                    (Term.Var 2))
                                                  (Term.Var 1))
                                                (Term.Tup
                                                  (Quan.Q1)
                                                  (Term.Lab "Succ")
                                                  (Term.Tup
                                                    (Quan.Q1)
                                                    (Term.Var 0)
                                                    (Term.Lab "()"))))
                                              (Term.Lab "()")))))))
                                  (Term.Efq))))))))
                    (Term.Mat
                      "Term.Lam"
                      (Term.Prj
                        (Term.Lam
                          (Quan.Q1)
                          (Term.Prj
                            (Term.Lam
                              (Quan.Q1)
                              (Term.Mat
                                "()"
                                (Term.Lam
                                  (Quan.Q2)
                                  (Term.Lam
                                    (Quan.Q2)
                                    (Term.Tup
                                      (Quan.Q1)
                                      (Term.Lab "Term.Lam")
                                      (Term.Tup
                                        (Quan.Q1)
                                        (Term.Var 3)
                                        (Term.Tup
                                          (Quan.Q1)
                                          (Term.App
                                            (Quan.Q2)
                                            (Term.App
                                              (Quan.Q2)
                                              (Term.App
                                                (Quan.Q1)
                                                (Term.Ref "Term.shift")
                                                (Term.Var 2))
                                              (Term.Var 1))
                                            (Term.Tup
                                              (Quan.Q1)
                                              (Term.Lab "Succ")
                                              (Term.Tup (Quan.Q1) (Term.Var 0) (Term.Lab "()"))))
                                          (Term.Lab "()"))))))
                                (Term.Efq))))))
                      (Term.Mat
                        "Term.App"
                        (Term.Prj
                          (Term.Lam
                            (Quan.Q1)
                            (Term.Prj
                              (Term.Lam
                                (Quan.Q1)
                                (Term.Prj
                                  (Term.Lam
                                    (Quan.Q1)
                                    (Term.Mat
                                      "()"
                                      (Term.Lam
                                        (Quan.Q2)
                                        (Term.Lam
                                          (Quan.Q2)
                                          (Term.Tup
                                            (Quan.Q1)
                                            (Term.Lab "Term.App")
                                            (Term.Tup
                                              (Quan.Q1)
                                              (Term.Var 4)
                                              (Term.Tup
                                                (Quan.Q1)
                                                (Term.App
                                                  (Quan.Q2)
                                                  (Term.App
                                                    (Quan.Q2)
                                                    (Term.App
                                                      (Quan.Q1)
                                                      (Term.Ref "Term.shift")
                                                      (Term.Var 3))
                                                    (Term.Var 1))
                                                  (Term.Var 0))
                                                (Term.Tup
                                                  (Quan.Q1)
                                                  (Term.App
                                                    (Quan.Q2)
                                                    (Term.App
                                                      (Quan.Q2)
                                                      (Term.App
                                                        (Quan.Q1)
                                                        (Term.Ref "Term.shift")
                                                        (Term.Var 2))
                                                      (Term.Var 1))
                                                    (Term.Var 0))
                                                  (Term.Lab "()")))))))
                                      (Term.Efq))))))))
                        (Term.Mat
                          "Term.Sig"
                          (Term.Prj
                            (Term.Lam
                              (Quan.Q1)
                              (Term.Prj
                                (Term.Lam
                                  (Quan.Q1)
                                  (Term.Prj
                                    (Term.Lam
                                      (Quan.Q1)
                                      (Term.Mat
                                        "()"
                                        (Term.Lam
                                          (Quan.Q2)
                                          (Term.Lam
                                            (Quan.Q2)
                                            (Term.Tup
                                              (Quan.Q1)
                                              (Term.Lab "Term.Sig")
                                              (Term.Tup
                                                (Quan.Q1)
                                                (Term.Var 4)
                                                (Term.Tup
                                                  (Quan.Q1)
                                                  (Term.App
                                                    (Quan.Q2)
                                                    (Term.App
                                                      (Quan.Q2)
                                                      (Term.App
                                                        (Quan.Q1)
                                                        (Term.Ref "Term.shift")
                                                        (Term.Var 3))
                                                      (Term.Var 1))
                                                    (Term.Var 0))
                                                  (Term.Tup
                                                    (Quan.Q1)
                                                    (Term.App
                                                      (Quan.Q2)
                                                      (Term.App
                                                        (Quan.Q2)
                                                        (Term.App
                                                          (Quan.Q1)
                                                          (Term.Ref "Term.shift")
                                                          (Term.Var 2))
                                                        (Term.Var 1))
                                                      (Term.Tup
                                                        (Quan.Q1)
                                                        (Term.Lab "Succ")
                                                        (Term.Tup
                                                          (Quan.Q1)
                                                          (Term.Var 0)
                                                          (Term.Lab "()"))))
                                                    (Term.Lab "()")))))))
                                        (Term.Efq))))))))
                          (Term.Mat
                            "Term.Tup"
                            (Term.Prj
                              (Term.Lam
                                (Quan.Q1)
                                (Term.Prj
                                  (Term.Lam
                                    (Quan.Q1)
                                    (Term.Prj
                                      (Term.Lam
                                        (Quan.Q1)
                                        (Term.Mat
                                          "()"
                                          (Term.Lam
                                            (Quan.Q2)
                                            (Term.Lam
                                              (Quan.Q2)
                                              (Term.Tup
                                                (Quan.Q1)
                                                (Term.Lab "Term.Tup")
                                                (Term.Tup
                                                  (Quan.Q1)
                                                  (Term.Var 4)
                                                  (Term.Tup
                                                    (Quan.Q1)
                                                    (Term.App
                                                      (Quan.Q2)
                                                      (Term.App
                                                        (Quan.Q2)
                                                        (Term.App
                                                          (Quan.Q1)
                                                          (Term.Ref "Term.shift")
                                                          (Term.Var 3))
                                                        (Term.Var 1))
                                                      (Term.Var 0))
                                                    (Term.Tup
                                                      (Quan.Q1)
                                                      (Term.App
                                                        (Quan.Q2)
                                                        (Term.App
                                                          (Quan.Q2)
                                                          (Term.App
                                                            (Quan.Q1)
                                                            (Term.Ref "Term.shift")
                                                            (Term.Var 2))
                                                          (Term.Var 1))
                                                        (Term.Var 0))
                                                      (Term.Lab "()")))))))
                                          (Term.Efq))))))))
                            (Term.Mat
                              "Term.Prj"
                              (Term.Prj
                                (Term.Lam
                                  (Quan.Q1)
                                  (Term.Mat
                                    "()"
                                    (Term.Lam
                                      (Quan.Q2)
                                      (Term.Lam
                                        (Quan.Q2)
                                        (Term.Tup
                                          (Quan.Q1)
                                          (Term.Lab "Term.Prj")
                                          (Term.Tup
                                            (Quan.Q1)
                                            (Term.App
                                              (Quan.Q2)
                                              (Term.App
                                                (Quan.Q2)
                                                (Term.App
                                                  (Quan.Q1)
                                                  (Term.Ref "Term.shift")
                                                  (Term.Var 2))
                                                (Term.Var 1))
                                              (Term.Var 0))
                                            (Term.Lab "()")))))
                                    (Term.Efq))))
                              (Term.Mat
                                "Term.Enu"
                                (Term.Prj
                                  (Term.Lam
                                    (Quan.Q1)
                                    (Term.Mat
                                      "()"
                                      (Term.Lam
                                        (Quan.Q2)
                                        (Term.Lam
                                          (Quan.Q2)
                                          (Term.Tup
                                            (Quan.Q1)
                                            (Term.Lab "Term.Enu")
                                            (Term.Tup (Quan.Q1) (Term.Var 2) (Term.Lab "()")))))
                                      (Term.Efq))))
                                (Term.Mat
                                  "Term.Lab"
                                  (Term.Prj
                                    (Term.Lam
                                      (Quan.Q1)
                                      (Term.Mat
                                        "()"
                                        (Term.Lam
                                          (Quan.Q2)
                                          (Term.Lam
                                            (Quan.Q2)
                                            (Term.Tup
                                              (Quan.Q1)
                                              (Term.Lab "Term.Lab")
                                              (Term.Tup (Quan.Q1) (Term.Var 2) (Term.Lab "()")))))
                                        (Term.Efq))))
                                  (Term.Mat
                                    "Term.Mat"
                                    (Term.Prj
                                      (Term.Lam
                                        (Quan.Q1)
                                        (Term.Prj
                                          (Term.Lam
                                            (Quan.Q1)
                                            (Term.Prj
                                              (Term.Lam
                                                (Quan.Q1)
                                                (Term.Mat
                                                  "()"
                                                  (Term.Lam
                                                    (Quan.Q2)
                                                    (Term.Lam
                                                      (Quan.Q2)
                                                      (Term.Tup
                                                        (Quan.Q1)
                                                        (Term.Lab "Term.Mat")
                                                        (Term.Tup
                                                          (Quan.Q1)
                                                          (Term.Var 4)
                                                          (Term.Tup
                                                            (Quan.Q1)
                                                            (Term.App
                                                              (Quan.Q2)
                                                              (Term.App
                                                                (Quan.Q2)
                                                                (Term.App
                                                                  (Quan.Q1)
                                                                  (Term.Ref "Term.shift")
                                                                  (Term.Var 3))
                                                                (Term.Var 1))
                                                              (Term.Var 0))
                                                            (Term.Tup
                                                              (Quan.Q1)
                                                              (Term.App
                                                                (Quan.Q2)
                                                                (Term.App
                                                                  (Quan.Q2)
                                                                  (Term.App
                                                                    (Quan.Q1)
                                                                    (Term.Ref "Term.shift")
                                                                    (Term.Var 2))
                                                                  (Term.Var 1))
                                                                (Term.Var 0))
                                                              (Term.Lab "()")))))))
                                                  (Term.Efq))))))))
                                    (Term.Mat
                                      "Term.Efq"
                                      (Term.Mat
                                        "()"
                                        (Term.Lam
                                          (Quan.Q2)
                                          (Term.Lam
                                            (Quan.Q2)
                                            (Term.Tup
                                              (Quan.Q1)
                                              (Term.Lab "Term.Efq")
                                              (Term.Lab "()"))))
                                        (Term.Efq))
                                      (Term.Mat
                                        "Term.Eql"
                                        (Term.Prj
                                          (Term.Lam
                                            (Quan.Q1)
                                            (Term.Prj
                                              (Term.Lam
                                                (Quan.Q1)
                                                (Term.Prj
                                                  (Term.Lam
                                                    (Quan.Q1)
                                                    (Term.Mat
                                                      "()"
                                                      (Term.Lam
                                                        (Quan.Q2)
                                                        (Term.Lam
                                                          (Quan.Q2)
                                                          (Term.Tup
                                                            (Quan.Q1)
                                                            (Term.Lab "Term.Eql")
                                                            (Term.Tup
                                                              (Quan.Q1)
                                                              (Term.App
                                                                (Quan.Q2)
                                                                (Term.App
                                                                  (Quan.Q2)
                                                                  (Term.App
                                                                    (Quan.Q1)
                                                                    (Term.Ref "Term.shift")
                                                                    (Term.Var 4))
                                                                  (Term.Var 1))
                                                                (Term.Var 0))
                                                              (Term.Tup
                                                                (Quan.Q1)
                                                                (Term.App
                                                                  (Quan.Q2)
                                                                  (Term.App
                                                                    (Quan.Q2)
                                                                    (Term.App
                                                                      (Quan.Q1)
                                                                      (Term.Ref "Term.shift")
                                                                      (Term.Var 3))
                                                                    (Term.Var 1))
                                                                  (Term.Var 0))
                                                                (Term.Tup
                                                                  (Quan.Q1)
                                                                  (Term.App
                                                                    (Quan.Q2)
                                                                    (Term.App
                                                                      (Quan.Q2)
                                                                      (Term.App
                                                                        (Quan.Q1)
                                                                        (Term.Ref "Term.shift")
                                                                        (Term.Var 2))
                                                                      (Term.Var 1))
                                                                    (Term.Var 0))
                                                                  (Term.Lab "()")))))))
                                                      (Term.Efq))))))))
                                        (Term.Mat
                                          "Term.Rfl"
                                          (Term.Mat
                                            "()"
                                            (Term.Lam
                                              (Quan.Q2)
                                              (Term.Lam
                                                (Quan.Q2)
                                                (Term.Tup
                                                  (Quan.Q1)
                                                  (Term.Lab "Term.Rfl")
                                                  (Term.Lab "()"))))
                                            (Term.Efq))
                                          (Term.Mat
                                            "Term.Rwt"
                                            (Term.Prj
                                              (Term.Lam
                                                (Quan.Q1)
                                                (Term.Prj
                                                  (Term.Lam
                                                    (Quan.Q1)
                                                    (Term.Prj
                                                      (Term.Lam
                                                        (Quan.Q1)
                                                        (Term.Mat
                                                          "()"
                                                          (Term.Lam
                                                            (Quan.Q2)
                                                            (Term.Lam
                                                              (Quan.Q2)
                                                              (Term.Tup
                                                                (Quan.Q1)
                                                                (Term.Lab "Term.Rwt")
                                                                (Term.Tup
                                                                  (Quan.Q1)
                                                                  (Term.App
                                                                    (Quan.Q2)
                                                                    (Term.App
                                                                      (Quan.Q2)
                                                                      (Term.App
                                                                        (Quan.Q1)
                                                                        (Term.Ref "Term.shift")
                                                                        (Term.Var 4))
                                                                      (Term.Var 1))
                                                                    (Term.Var 0))
                                                                  (Term.Tup
                                                                    (Quan.Q1)
                                                                    (Term.App
                                                                      (Quan.Q2)
                                                                      (Term.App
                                                                        (Quan.Q2)
                                                                        (Term.App
                                                                          (Quan.Q1)
                                                                          (Term.Ref "Term.shift")
                                                                          (Term.Var 3))
                                                                        (Term.Var 1))
                                                                      (Term.Tup
                                                                        (Quan.Q1)
                                                                        (Term.Lab "Succ")
                                                                        (Term.Tup
                                                                          (Quan.Q1)
                                                                          (Term.Tup
                                                                            (Quan.Q1)
                                                                            (Term.Lab "Succ")
                                                                            (Term.Tup
                                                                              (Quan.Q1)
                                                                              (Term.Var 0)
                                                                              (Term.Lab "()")))
                                                                          (Term.Lab "()"))))
                                                                    (Term.Tup
                                                                      (Quan.Q1)
                                                                      (Term.App
                                                                        (Quan.Q2)
                                                                        (Term.App
                                                                          (Quan.Q2)
                                                                          (Term.App
                                                                            (Quan.Q1)
                                                                            (Term.Ref "Term.shift")
                                                                            (Term.Var 2))
                                                                          (Term.Var 1))
                                                                        (Term.Var 0))
                                                                      (Term.Lab "()")))))))
                                                          (Term.Efq))))))))
                                            (Term.Efq)))))))))))))))))))),
    false⟩

def «evalVersion.Term.lift.at» : Def :=
  ⟨"Term.lift.at",
    Term.All
      (Quan.Q1)
      (Term.Ref "Bool")
      (Term.All (Quan.Q1) (Term.Ref "Nat") (Term.All (Quan.Q1) (Term.Ref "Term") (Term.Ref "Term"))),
    Term.Prj
      (Term.Mat
        "True"
        (Term.Mat
          "()"
          (Term.Lam
            (Quan.Q1)
            (Term.Lam
              (Quan.Q1)
              (Term.Tup
                (Quan.Q1)
                (Term.Lab "Term.Var")
                (Term.Tup (Quan.Q1) (Term.Var 1) (Term.Lab "()")))))
          (Term.Efq))
        (Term.Mat
          "False"
          (Term.Mat "()" (Term.Lam (Quan.Q1) (Term.Lam (Quan.Q1) (Term.Var 0))) (Term.Efq))
          (Term.Efq))),
    false⟩

def «evalVersion.Term.lift» : Def :=
  ⟨"Term.lift",
    Term.All
      (Quan.Q2)
      (Term.App (Quan.Q0) (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "Term"))
      (Term.All (Quan.Q2) (Term.Ref "Nat") (Term.All (Quan.Q2) (Term.Ref "Nat") (Term.Ref "Term"))),
    Term.Lam
      (Quan.Q2)
      (Term.Prj
        (Term.Mat
          "Zero"
          (Term.Mat
            "()"
            (Term.Lam
              (Quan.Q2)
              (Term.App
                (Quan.Q1)
                (Term.App (Quan.Q1) (Term.Ref "Env.sub") (Term.Var 1))
                (Term.Var 0)))
            (Term.Efq))
          (Term.Mat
            "Succ"
            (Term.Prj
              (Term.Lam
                (Quan.Q2)
                (Term.Mat
                  "()"
                  (Term.Lam
                    (Quan.Q2)
                    (Term.App
                      (Quan.Q1)
                      (Term.App
                        (Quan.Q1)
                        (Term.App
                          (Quan.Q1)
                          (Term.Ref "Term.lift.at")
                          (Term.App
                            (Quan.Q1)
                            (Term.App (Quan.Q1) (Term.Ref "Nat.is_lt") (Term.Var 0))
                            (Term.Tup
                              (Quan.Q1)
                              (Term.Lab "Succ")
                              (Term.Tup (Quan.Q1) (Term.Var 1) (Term.Lab "()")))))
                        (Term.Var 0))
                      (Term.App
                        (Quan.Q2)
                        (Term.App
                          (Quan.Q2)
                          (Term.App
                            (Quan.Q1)
                            (Term.Ref "Term.shift")
                            (Term.App
                              (Quan.Q1)
                              (Term.App (Quan.Q1) (Term.Ref "Env.sub") (Term.Var 2))
                              (Term.App
                                (Quan.Q1)
                                (Term.App (Quan.Q1) (Term.Ref "Nat.sub") (Term.Var 0))
                                (Term.Tup
                                  (Quan.Q1)
                                  (Term.Lab "Succ")
                                  (Term.Tup (Quan.Q1) (Term.Var 1) (Term.Lab "()"))))))
                          (Term.Tup
                            (Quan.Q1)
                            (Term.Lab "Succ")
                            (Term.Tup (Quan.Q1) (Term.Var 1) (Term.Lab "()"))))
                        (Term.Tup (Quan.Q1) (Term.Lab "Zero") (Term.Lab "()")))))
                  (Term.Efq))))
            (Term.Efq)))),
    false⟩

def «evalVersion.Term.subst» : Def :=
  ⟨"Term.subst",
    Term.All
      (Quan.Q1)
      (Term.Ref "Term")
      (Term.All
        (Quan.Q2)
        (Term.App
          (Quan.Q0)
          (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
          (Term.Ref "Term"))
        (Term.All (Quan.Q2) (Term.Ref "Nat") (Term.Ref "Term"))),
    Term.Prj
      (Term.Mat
        "Term.Var"
        (Term.Prj
          (Term.Lam
            (Quan.Q1)
            (Term.Mat
              "()"
              (Term.Lam
                (Quan.Q2)
                (Term.Lam
                  (Quan.Q2)
                  (Term.App
                    (Quan.Q2)
                    (Term.App
                      (Quan.Q2)
                      (Term.App (Quan.Q2) (Term.Ref "Term.lift") (Term.Var 1))
                      (Term.Var 0))
                    (Term.Var 2))))
              (Term.Efq))))
        (Term.Mat
          "Term.Ref"
          (Term.Prj
            (Term.Lam
              (Quan.Q1)
              (Term.Mat
                "()"
                (Term.Lam
                  (Quan.Q2)
                  (Term.Lam
                    (Quan.Q2)
                    (Term.Tup
                      (Quan.Q1)
                      (Term.Lab "Term.Ref")
                      (Term.Tup (Quan.Q1) (Term.Var 2) (Term.Lab "()")))))
                (Term.Efq))))
          (Term.Mat
            "Term.Ann"
            (Term.Prj
              (Term.Lam
                (Quan.Q1)
                (Term.Prj
                  (Term.Lam
                    (Quan.Q1)
                    (Term.Mat
                      "()"
                      (Term.Lam
                        (Quan.Q2)
                        (Term.Lam
                          (Quan.Q2)
                          (Term.Tup
                            (Quan.Q1)
                            (Term.Lab "Term.Ann")
                            (Term.Tup
                              (Quan.Q1)
                              (Term.App
                                (Quan.Q2)
                                (Term.App
                                  (Quan.Q2)
                                  (Term.App (Quan.Q1) (Term.Ref "Term.subst") (Term.Var 3))
                                  (Term.Var 1))
                                (Term.Var 0))
                              (Term.Tup
                                (Quan.Q1)
                                (Term.App
                                  (Quan.Q2)
                                  (Term.App
                                    (Quan.Q2)
                                    (Term.App (Quan.Q1) (Term.Ref "Term.subst") (Term.Var 2))
                                    (Term.Var 1))
                                  (Term.Var 0))
                                (Term.Lab "()"))))))
                      (Term.Efq))))))
            (Term.Mat
              "Term.Let"
              (Term.Prj
                (Term.Lam
                  (Quan.Q1)
                  (Term.Prj
                    (Term.Lam
                      (Quan.Q1)
                      (Term.Prj
                        (Term.Lam
                          (Quan.Q1)
                          (Term.Mat
                            "()"
                            (Term.Lam
                              (Quan.Q2)
                              (Term.Lam
                                (Quan.Q2)
                                (Term.Tup
                                  (Quan.Q1)
                                  (Term.Lab "Term.Let")
                                  (Term.Tup
                                    (Quan.Q1)
                                    (Term.Var 4)
                                    (Term.Tup
                                      (Quan.Q1)
                                      (Term.App
                                        (Quan.Q2)
                                        (Term.App
                                          (Quan.Q2)
                                          (Term.App (Quan.Q1) (Term.Ref "Term.subst") (Term.Var 3))
                                          (Term.Var 1))
                                        (Term.Var 0))
                                      (Term.Tup
                                        (Quan.Q1)
                                        (Term.App
                                          (Quan.Q2)
                                          (Term.App
                                            (Quan.Q2)
                                            (Term.App
                                              (Quan.Q1)
                                              (Term.Ref "Term.subst")
                                              (Term.Var 2))
                                            (Term.Var 1))
                                          (Term.Tup
                                            (Quan.Q1)
                                            (Term.Lab "Succ")
                                            (Term.Tup (Quan.Q1) (Term.Var 0) (Term.Lab "()"))))
                                        (Term.Lab "()")))))))
                            (Term.Efq))))))))
              (Term.Mat
                "Term.Typ"
                (Term.Prj
                  (Term.Lam
                    (Quan.Q1)
                    (Term.Mat
                      "()"
                      (Term.Lam
                        (Quan.Q2)
                        (Term.Lam
                          (Quan.Q2)
                          (Term.Tup
                            (Quan.Q1)
                            (Term.Lab "Term.Typ")
                            (Term.Tup
                              (Quan.Q1)
                              (Term.App
                                (Quan.Q2)
                                (Term.App
                                  (Quan.Q2)
                                  (Term.App (Quan.Q1) (Term.Ref "Term.subst") (Term.Var 2))
                                  (Term.Var 1))
                                (Term.Var 0))
                              (Term.Lab "()")))))
                      (Term.Efq))))
                (Term.Mat
                  "Term.Min"
                  (Term.Prj
                    (Term.Lam
                      (Quan.Q1)
                      (Term.Prj
                        (Term.Lam
                          (Quan.Q1)
                          (Term.Mat
                            "()"
                            (Term.Lam
                              (Quan.Q2)
                              (Term.Lam
                                (Quan.Q2)
                                (Term.Tup
                                  (Quan.Q1)
                                  (Term.Lab "Term.Min")
                                  (Term.Tup
                                    (Quan.Q1)
                                    (Term.App
                                      (Quan.Q2)
                                      (Term.App
                                        (Quan.Q2)
                                        (Term.App (Quan.Q1) (Term.Ref "Term.subst") (Term.Var 3))
                                        (Term.Var 1))
                                      (Term.Var 0))
                                    (Term.Tup
                                      (Quan.Q1)
                                      (Term.App
                                        (Quan.Q2)
                                        (Term.App
                                          (Quan.Q2)
                                          (Term.App (Quan.Q1) (Term.Ref "Term.subst") (Term.Var 2))
                                          (Term.Var 1))
                                        (Term.Var 0))
                                      (Term.Lab "()"))))))
                            (Term.Efq))))))
                  (Term.Mat
                    "Term.All"
                    (Term.Prj
                      (Term.Lam
                        (Quan.Q1)
                        (Term.Prj
                          (Term.Lam
                            (Quan.Q1)
                            (Term.Prj
                              (Term.Lam
                                (Quan.Q1)
                                (Term.Mat
                                  "()"
                                  (Term.Lam
                                    (Quan.Q2)
                                    (Term.Lam
                                      (Quan.Q2)
                                      (Term.Tup
                                        (Quan.Q1)
                                        (Term.Lab "Term.All")
                                        (Term.Tup
                                          (Quan.Q1)
                                          (Term.Var 4)
                                          (Term.Tup
                                            (Quan.Q1)
                                            (Term.App
                                              (Quan.Q2)
                                              (Term.App
                                                (Quan.Q2)
                                                (Term.App
                                                  (Quan.Q1)
                                                  (Term.Ref "Term.subst")
                                                  (Term.Var 3))
                                                (Term.Var 1))
                                              (Term.Var 0))
                                            (Term.Tup
                                              (Quan.Q1)
                                              (Term.App
                                                (Quan.Q2)
                                                (Term.App
                                                  (Quan.Q2)
                                                  (Term.App
                                                    (Quan.Q1)
                                                    (Term.Ref "Term.subst")
                                                    (Term.Var 2))
                                                  (Term.Var 1))
                                                (Term.Tup
                                                  (Quan.Q1)
                                                  (Term.Lab "Succ")
                                                  (Term.Tup
                                                    (Quan.Q1)
                                                    (Term.Var 0)
                                                    (Term.Lab "()"))))
                                              (Term.Lab "()")))))))
                                  (Term.Efq))))))))
                    (Term.Mat
                      "Term.Lam"
                      (Term.Prj
                        (Term.Lam
                          (Quan.Q1)
                          (Term.Prj
                            (Term.Lam
                              (Quan.Q1)
                              (Term.Mat
                                "()"
                                (Term.Lam
                                  (Quan.Q2)
                                  (Term.Lam
                                    (Quan.Q2)
                                    (Term.Tup
                                      (Quan.Q1)
                                      (Term.Lab "Term.Lam")
                                      (Term.Tup
                                        (Quan.Q1)
                                        (Term.Var 3)
                                        (Term.Tup
                                          (Quan.Q1)
                                          (Term.App
                                            (Quan.Q2)
                                            (Term.App
                                              (Quan.Q2)
                                              (Term.App
                                                (Quan.Q1)
                                                (Term.Ref "Term.subst")
                                                (Term.Var 2))
                                              (Term.Var 1))
                                            (Term.Tup
                                              (Quan.Q1)
                                              (Term.Lab "Succ")
                                              (Term.Tup (Quan.Q1) (Term.Var 0) (Term.Lab "()"))))
                                          (Term.Lab "()"))))))
                                (Term.Efq))))))
                      (Term.Mat
                        "Term.App"
                        (Term.Prj
                          (Term.Lam
                            (Quan.Q1)
                            (Term.Prj
                              (Term.Lam
                                (Quan.Q1)
                                (Term.Prj
                                  (Term.Lam
                                    (Quan.Q1)
                                    (Term.Mat
                                      "()"
                                      (Term.Lam
                                        (Quan.Q2)
                                        (Term.Lam
                                          (Quan.Q2)
                                          (Term.Tup
                                            (Quan.Q1)
                                            (Term.Lab "Term.App")
                                            (Term.Tup
                                              (Quan.Q1)
                                              (Term.Var 4)
                                              (Term.Tup
                                                (Quan.Q1)
                                                (Term.App
                                                  (Quan.Q2)
                                                  (Term.App
                                                    (Quan.Q2)
                                                    (Term.App
                                                      (Quan.Q1)
                                                      (Term.Ref "Term.subst")
                                                      (Term.Var 3))
                                                    (Term.Var 1))
                                                  (Term.Var 0))
                                                (Term.Tup
                                                  (Quan.Q1)
                                                  (Term.App
                                                    (Quan.Q2)
                                                    (Term.App
                                                      (Quan.Q2)
                                                      (Term.App
                                                        (Quan.Q1)
                                                        (Term.Ref "Term.subst")
                                                        (Term.Var 2))
                                                      (Term.Var 1))
                                                    (Term.Var 0))
                                                  (Term.Lab "()")))))))
                                      (Term.Efq))))))))
                        (Term.Mat
                          "Term.Sig"
                          (Term.Prj
                            (Term.Lam
                              (Quan.Q1)
                              (Term.Prj
                                (Term.Lam
                                  (Quan.Q1)
                                  (Term.Prj
                                    (Term.Lam
                                      (Quan.Q1)
                                      (Term.Mat
                                        "()"
                                        (Term.Lam
                                          (Quan.Q2)
                                          (Term.Lam
                                            (Quan.Q2)
                                            (Term.Tup
                                              (Quan.Q1)
                                              (Term.Lab "Term.Sig")
                                              (Term.Tup
                                                (Quan.Q1)
                                                (Term.Var 4)
                                                (Term.Tup
                                                  (Quan.Q1)
                                                  (Term.App
                                                    (Quan.Q2)
                                                    (Term.App
                                                      (Quan.Q2)
                                                      (Term.App
                                                        (Quan.Q1)
                                                        (Term.Ref "Term.subst")
                                                        (Term.Var 3))
                                                      (Term.Var 1))
                                                    (Term.Var 0))
                                                  (Term.Tup
                                                    (Quan.Q1)
                                                    (Term.App
                                                      (Quan.Q2)
                                                      (Term.App
                                                        (Quan.Q2)
                                                        (Term.App
                                                          (Quan.Q1)
                                                          (Term.Ref "Term.subst")
                                                          (Term.Var 2))
                                                        (Term.Var 1))
                                                      (Term.Tup
                                                        (Quan.Q1)
                                                        (Term.Lab "Succ")
                                                        (Term.Tup
                                                          (Quan.Q1)
                                                          (Term.Var 0)
                                                          (Term.Lab "()"))))
                                                    (Term.Lab "()")))))))
                                        (Term.Efq))))))))
                          (Term.Mat
                            "Term.Tup"
                            (Term.Prj
                              (Term.Lam
                                (Quan.Q1)
                                (Term.Prj
                                  (Term.Lam
                                    (Quan.Q1)
                                    (Term.Prj
                                      (Term.Lam
                                        (Quan.Q1)
                                        (Term.Mat
                                          "()"
                                          (Term.Lam
                                            (Quan.Q2)
                                            (Term.Lam
                                              (Quan.Q2)
                                              (Term.Tup
                                                (Quan.Q1)
                                                (Term.Lab "Term.Tup")
                                                (Term.Tup
                                                  (Quan.Q1)
                                                  (Term.Var 4)
                                                  (Term.Tup
                                                    (Quan.Q1)
                                                    (Term.App
                                                      (Quan.Q2)
                                                      (Term.App
                                                        (Quan.Q2)
                                                        (Term.App
                                                          (Quan.Q1)
                                                          (Term.Ref "Term.subst")
                                                          (Term.Var 3))
                                                        (Term.Var 1))
                                                      (Term.Var 0))
                                                    (Term.Tup
                                                      (Quan.Q1)
                                                      (Term.App
                                                        (Quan.Q2)
                                                        (Term.App
                                                          (Quan.Q2)
                                                          (Term.App
                                                            (Quan.Q1)
                                                            (Term.Ref "Term.subst")
                                                            (Term.Var 2))
                                                          (Term.Var 1))
                                                        (Term.Var 0))
                                                      (Term.Lab "()")))))))
                                          (Term.Efq))))))))
                            (Term.Mat
                              "Term.Prj"
                              (Term.Prj
                                (Term.Lam
                                  (Quan.Q1)
                                  (Term.Mat
                                    "()"
                                    (Term.Lam
                                      (Quan.Q2)
                                      (Term.Lam
                                        (Quan.Q2)
                                        (Term.Tup
                                          (Quan.Q1)
                                          (Term.Lab "Term.Prj")
                                          (Term.Tup
                                            (Quan.Q1)
                                            (Term.App
                                              (Quan.Q2)
                                              (Term.App
                                                (Quan.Q2)
                                                (Term.App
                                                  (Quan.Q1)
                                                  (Term.Ref "Term.subst")
                                                  (Term.Var 2))
                                                (Term.Var 1))
                                              (Term.Var 0))
                                            (Term.Lab "()")))))
                                    (Term.Efq))))
                              (Term.Mat
                                "Term.Enu"
                                (Term.Prj
                                  (Term.Lam
                                    (Quan.Q1)
                                    (Term.Mat
                                      "()"
                                      (Term.Lam
                                        (Quan.Q2)
                                        (Term.Lam
                                          (Quan.Q2)
                                          (Term.Tup
                                            (Quan.Q1)
                                            (Term.Lab "Term.Enu")
                                            (Term.Tup (Quan.Q1) (Term.Var 2) (Term.Lab "()")))))
                                      (Term.Efq))))
                                (Term.Mat
                                  "Term.Lab"
                                  (Term.Prj
                                    (Term.Lam
                                      (Quan.Q1)
                                      (Term.Mat
                                        "()"
                                        (Term.Lam
                                          (Quan.Q2)
                                          (Term.Lam
                                            (Quan.Q2)
                                            (Term.Tup
                                              (Quan.Q1)
                                              (Term.Lab "Term.Lab")
                                              (Term.Tup (Quan.Q1) (Term.Var 2) (Term.Lab "()")))))
                                        (Term.Efq))))
                                  (Term.Mat
                                    "Term.Mat"
                                    (Term.Prj
                                      (Term.Lam
                                        (Quan.Q1)
                                        (Term.Prj
                                          (Term.Lam
                                            (Quan.Q1)
                                            (Term.Prj
                                              (Term.Lam
                                                (Quan.Q1)
                                                (Term.Mat
                                                  "()"
                                                  (Term.Lam
                                                    (Quan.Q2)
                                                    (Term.Lam
                                                      (Quan.Q2)
                                                      (Term.Tup
                                                        (Quan.Q1)
                                                        (Term.Lab "Term.Mat")
                                                        (Term.Tup
                                                          (Quan.Q1)
                                                          (Term.Var 4)
                                                          (Term.Tup
                                                            (Quan.Q1)
                                                            (Term.App
                                                              (Quan.Q2)
                                                              (Term.App
                                                                (Quan.Q2)
                                                                (Term.App
                                                                  (Quan.Q1)
                                                                  (Term.Ref "Term.subst")
                                                                  (Term.Var 3))
                                                                (Term.Var 1))
                                                              (Term.Var 0))
                                                            (Term.Tup
                                                              (Quan.Q1)
                                                              (Term.App
                                                                (Quan.Q2)
                                                                (Term.App
                                                                  (Quan.Q2)
                                                                  (Term.App
                                                                    (Quan.Q1)
                                                                    (Term.Ref "Term.subst")
                                                                    (Term.Var 2))
                                                                  (Term.Var 1))
                                                                (Term.Var 0))
                                                              (Term.Lab "()")))))))
                                                  (Term.Efq))))))))
                                    (Term.Mat
                                      "Term.Efq"
                                      (Term.Mat
                                        "()"
                                        (Term.Lam
                                          (Quan.Q2)
                                          (Term.Lam
                                            (Quan.Q2)
                                            (Term.Tup
                                              (Quan.Q1)
                                              (Term.Lab "Term.Efq")
                                              (Term.Lab "()"))))
                                        (Term.Efq))
                                      (Term.Mat
                                        "Term.Eql"
                                        (Term.Prj
                                          (Term.Lam
                                            (Quan.Q1)
                                            (Term.Prj
                                              (Term.Lam
                                                (Quan.Q1)
                                                (Term.Prj
                                                  (Term.Lam
                                                    (Quan.Q1)
                                                    (Term.Mat
                                                      "()"
                                                      (Term.Lam
                                                        (Quan.Q2)
                                                        (Term.Lam
                                                          (Quan.Q2)
                                                          (Term.Tup
                                                            (Quan.Q1)
                                                            (Term.Lab "Term.Eql")
                                                            (Term.Tup
                                                              (Quan.Q1)
                                                              (Term.App
                                                                (Quan.Q2)
                                                                (Term.App
                                                                  (Quan.Q2)
                                                                  (Term.App
                                                                    (Quan.Q1)
                                                                    (Term.Ref "Term.subst")
                                                                    (Term.Var 4))
                                                                  (Term.Var 1))
                                                                (Term.Var 0))
                                                              (Term.Tup
                                                                (Quan.Q1)
                                                                (Term.App
                                                                  (Quan.Q2)
                                                                  (Term.App
                                                                    (Quan.Q2)
                                                                    (Term.App
                                                                      (Quan.Q1)
                                                                      (Term.Ref "Term.subst")
                                                                      (Term.Var 3))
                                                                    (Term.Var 1))
                                                                  (Term.Var 0))
                                                                (Term.Tup
                                                                  (Quan.Q1)
                                                                  (Term.App
                                                                    (Quan.Q2)
                                                                    (Term.App
                                                                      (Quan.Q2)
                                                                      (Term.App
                                                                        (Quan.Q1)
                                                                        (Term.Ref "Term.subst")
                                                                        (Term.Var 2))
                                                                      (Term.Var 1))
                                                                    (Term.Var 0))
                                                                  (Term.Lab "()")))))))
                                                      (Term.Efq))))))))
                                        (Term.Mat
                                          "Term.Rfl"
                                          (Term.Mat
                                            "()"
                                            (Term.Lam
                                              (Quan.Q2)
                                              (Term.Lam
                                                (Quan.Q2)
                                                (Term.Tup
                                                  (Quan.Q1)
                                                  (Term.Lab "Term.Rfl")
                                                  (Term.Lab "()"))))
                                            (Term.Efq))
                                          (Term.Mat
                                            "Term.Rwt"
                                            (Term.Prj
                                              (Term.Lam
                                                (Quan.Q1)
                                                (Term.Prj
                                                  (Term.Lam
                                                    (Quan.Q1)
                                                    (Term.Prj
                                                      (Term.Lam
                                                        (Quan.Q1)
                                                        (Term.Mat
                                                          "()"
                                                          (Term.Lam
                                                            (Quan.Q2)
                                                            (Term.Lam
                                                              (Quan.Q2)
                                                              (Term.Tup
                                                                (Quan.Q1)
                                                                (Term.Lab "Term.Rwt")
                                                                (Term.Tup
                                                                  (Quan.Q1)
                                                                  (Term.App
                                                                    (Quan.Q2)
                                                                    (Term.App
                                                                      (Quan.Q2)
                                                                      (Term.App
                                                                        (Quan.Q1)
                                                                        (Term.Ref "Term.subst")
                                                                        (Term.Var 4))
                                                                      (Term.Var 1))
                                                                    (Term.Var 0))
                                                                  (Term.Tup
                                                                    (Quan.Q1)
                                                                    (Term.App
                                                                      (Quan.Q2)
                                                                      (Term.App
                                                                        (Quan.Q2)
                                                                        (Term.App
                                                                          (Quan.Q1)
                                                                          (Term.Ref "Term.subst")
                                                                          (Term.Var 3))
                                                                        (Term.Var 1))
                                                                      (Term.Tup
                                                                        (Quan.Q1)
                                                                        (Term.Lab "Succ")
                                                                        (Term.Tup
                                                                          (Quan.Q1)
                                                                          (Term.Tup
                                                                            (Quan.Q1)
                                                                            (Term.Lab "Succ")
                                                                            (Term.Tup
                                                                              (Quan.Q1)
                                                                              (Term.Var 0)
                                                                              (Term.Lab "()")))
                                                                          (Term.Lab "()"))))
                                                                    (Term.Tup
                                                                      (Quan.Q1)
                                                                      (Term.App
                                                                        (Quan.Q2)
                                                                        (Term.App
                                                                          (Quan.Q2)
                                                                          (Term.App
                                                                            (Quan.Q1)
                                                                            (Term.Ref "Term.subst")
                                                                            (Term.Var 2))
                                                                          (Term.Var 1))
                                                                        (Term.Var 0))
                                                                      (Term.Lab "()")))))))
                                                          (Term.Efq))))))))
                                            (Term.Efq)))))))))))))))))))),
    false⟩

def «evalVersion.Term.inst» : Def :=
  ⟨"Term.inst",
    Term.All (Quan.Q1) (Term.Ref "Term") (Term.All (Quan.Q1) (Term.Ref "Term") (Term.Ref "Term")),
    Term.Lam
      (Quan.Q1)
      (Term.Lam
        (Quan.Q1)
        (Term.App
          (Quan.Q2)
          (Term.App
            (Quan.Q2)
            (Term.App (Quan.Q1) (Term.Ref "Term.subst") (Term.Var 1))
            (Term.Tup
              (Quan.Q1)
              (Term.Lab "Con")
              (Term.Tup
                (Quan.Q1)
                (Term.Var 0)
                (Term.Tup
                  (Quan.Q1)
                  (Term.Tup (Quan.Q1) (Term.Lab "Nil") (Term.Lab "()"))
                  (Term.Lab "()")))))
          (Term.Tup (Quan.Q1) (Term.Lab "Zero") (Term.Lab "()")))),
    false⟩

def «evalVersion.Book.get.if» : Def :=
  ⟨"Book.get.if",
    Term.All
      (Quan.Q1)
      (Term.Ref "Bool")
      (Term.All
        (Quan.Q1)
        (Term.Ref "Def")
        (Term.All
          (Quan.Q1)
          (Term.App
            (Quan.Q0)
            (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
            (Term.Ref "Def"))
          (Term.App
            (Quan.Q0)
            (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
            (Term.Ref "Def")))),
    Term.Prj
      (Term.Mat
        "True"
        (Term.Mat
          "()"
          (Term.Lam
            (Quan.Q1)
            (Term.Lam
              (Quan.Q1)
              (Term.Tup
                (Quan.Q1)
                (Term.Lab "Some")
                (Term.Tup (Quan.Q1) (Term.Var 1) (Term.Lab "()")))))
          (Term.Efq))
        (Term.Mat
          "False"
          (Term.Mat "()" (Term.Lam (Quan.Q1) (Term.Lam (Quan.Q1) (Term.Var 0))) (Term.Efq))
          (Term.Efq))),
    false⟩

def «evalVersion.Book.get» : Def :=
  ⟨"Book.get",
    Term.All
      (Quan.Q1)
      (Term.App (Quan.Q0) (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "Def"))
      (Term.All
        (Quan.Q2)
        (Term.App
          (Quan.Q0)
          (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
          (Term.App
            (Quan.Q1)
            (Term.Ref "Word")
            (Term.Tup
              (Quan.Q1)
              (Term.Lab "Succ")
              (Term.Tup
                (Quan.Q1)
                (Term.Tup
                  (Quan.Q1)
                  (Term.Lab "Succ")
                  (Term.Tup
                    (Quan.Q1)
                    (Term.Tup
                      (Quan.Q1)
                      (Term.Lab "Succ")
                      (Term.Tup
                        (Quan.Q1)
                        (Term.Tup
                          (Quan.Q1)
                          (Term.Lab "Succ")
                          (Term.Tup
                            (Quan.Q1)
                            (Term.Tup
                              (Quan.Q1)
                              (Term.Lab "Succ")
                              (Term.Tup
                                (Quan.Q1)
                                (Term.Tup
                                  (Quan.Q1)
                                  (Term.Lab "Succ")
                                  (Term.Tup
                                    (Quan.Q1)
                                    (Term.Tup
                                      (Quan.Q1)
                                      (Term.Lab "Succ")
                                      (Term.Tup
                                        (Quan.Q1)
                                        (Term.Tup
                                          (Quan.Q1)
                                          (Term.Lab "Succ")
                                          (Term.Tup
                                            (Quan.Q1)
                                            (Term.Tup (Quan.Q1) (Term.Lab "Zero") (Term.Lab "()"))
                                            (Term.Lab "()")))
                                        (Term.Lab "()")))
                                    (Term.Lab "()")))
                                (Term.Lab "()")))
                            (Term.Lab "()")))
                        (Term.Lab "()")))
                    (Term.Lab "()")))
                (Term.Lab "()")))))
        (Term.App
          (Quan.Q0)
          (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
          (Term.Ref "Def"))),
    Term.Prj
      (Term.Mat
        "Nil"
        (Term.Mat
          "()"
          (Term.Lam (Quan.Q2) (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()")))
          (Term.Efq))
        (Term.Mat
          "Con"
          (Term.Prj
            (Term.Prj
              (Term.Mat
                "Def"
                (Term.Prj
                  (Term.Lam
                    (Quan.Q2)
                    (Term.Prj
                      (Term.Lam
                        (Quan.Q1)
                        (Term.Prj
                          (Term.Lam
                            (Quan.Q1)
                            (Term.Prj
                              (Term.Lam
                                (Quan.Q1)
                                (Term.Mat
                                  "()"
                                  (Term.Prj
                                    (Term.Lam
                                      (Quan.Q1)
                                      (Term.Mat
                                        "()"
                                        (Term.Lam
                                          (Quan.Q2)
                                          (Term.App
                                            (Quan.Q1)
                                            (Term.App
                                              (Quan.Q1)
                                              (Term.App
                                                (Quan.Q1)
                                                (Term.Ref "Book.get.if")
                                                (Term.App
                                                  (Quan.Q1)
                                                  (Term.App
                                                    (Quan.Q1)
                                                    (Term.Ref "Name.is_eq")
                                                    (Term.Var 5))
                                                  (Term.Var 0)))
                                              (Term.Tup
                                                (Quan.Q1)
                                                (Term.Lab "Def")
                                                (Term.Tup
                                                  (Quan.Q1)
                                                  (Term.Var 5)
                                                  (Term.Tup
                                                    (Quan.Q1)
                                                    (Term.Var 4)
                                                    (Term.Tup
                                                      (Quan.Q1)
                                                      (Term.Var 3)
                                                      (Term.Tup
                                                        (Quan.Q1)
                                                        (Term.Var 2)
                                                        (Term.Lab "()")))))))
                                            (Term.App
                                              (Quan.Q2)
                                              (Term.App
                                                (Quan.Q1)
                                                (Term.Ref "Book.get")
                                                (Term.Var 1))
                                              (Term.Var 0))))
                                        (Term.Efq))))
                                  (Term.Efq))))))))))
                (Term.Efq))))
          (Term.Efq))),
    false⟩

def «evalVersion.Eval.walk.if» : Def :=
  ⟨"Eval.walk.if",
    Term.All
      (Quan.Q1)
      (Term.Ref "Bool")
      (Term.All
        (Quan.Q1)
        (Term.App
          (Quan.Q0)
          (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
          (Term.App
            (Quan.Q0)
            (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
            (Term.Ref "Term")))
        (Term.App
          (Quan.Q0)
          (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
          (Term.App
            (Quan.Q0)
            (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
            (Term.Ref "Term")))),
    Term.Prj
      (Term.Mat
        "True"
        (Term.Mat "()" (Term.Lam (Quan.Q1) (Term.Var 0)) (Term.Efq))
        (Term.Mat
          "False"
          (Term.Mat
            "()"
            (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()")))
            (Term.Efq))
          (Term.Efq))),
    false⟩

def «evalVersion.Eval.walk.pick» : Def :=
  ⟨"Eval.walk.pick",
    Term.All
      (Quan.Q1)
      (Term.Ref "Bool")
      (Term.All
        (Quan.Q1)
        (Term.App
          (Quan.Q0)
          (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
          (Term.App
            (Quan.Q0)
            (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
            (Term.Ref "Term")))
        (Term.All
          (Quan.Q1)
          (Term.App
            (Quan.Q0)
            (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
            (Term.App
              (Quan.Q0)
              (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
              (Term.Ref "Term")))
          (Term.App
            (Quan.Q0)
            (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
            (Term.App
              (Quan.Q0)
              (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
              (Term.Ref "Term"))))),
    Term.Prj
      (Term.Mat
        "True"
        (Term.Mat "()" (Term.Lam (Quan.Q1) (Term.Lam (Quan.Q1) (Term.Var 1))) (Term.Efq))
        (Term.Mat
          "False"
          (Term.Mat "()" (Term.Lam (Quan.Q1) (Term.Lam (Quan.Q1) (Term.Var 0))) (Term.Efq))
          (Term.Efq))),
    false⟩

def «evalVersion.Eval.walk.app» : Def :=
  ⟨"Eval.walk.app",
    Term.All
      (Quan.Q1)
      (Term.Ref "Bool")
      (Term.All
        (Quan.Q1)
        (Term.App
          (Quan.Q0)
          (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
          (Term.App
            (Quan.Q0)
            (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
            (Term.Ref "Term")))
        (Term.All
          (Quan.Q1)
          (Term.Ref "Term")
          (Term.App
            (Quan.Q0)
            (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
            (Term.App
              (Quan.Q0)
              (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
              (Term.Ref "Term"))))),
    Term.Prj
      (Term.Mat
        "True"
        (Term.Mat "()" (Term.Lam (Quan.Q1) (Term.Lam (Quan.Q1) (Term.Var 1))) (Term.Efq))
        (Term.Mat
          "False"
          (Term.Mat
            "()"
            (Term.Lam
              (Quan.Q1)
              (Term.Lam
                (Quan.Q1)
                (Term.Tup
                  (Quan.Q1)
                  (Term.Lab "Some")
                  (Term.Tup
                    (Quan.Q1)
                    (Term.Tup
                      (Quan.Q1)
                      (Term.Lab "Some")
                      (Term.Tup (Quan.Q1) (Term.Var 0) (Term.Lab "()")))
                    (Term.Lab "()")))))
            (Term.Efq))
          (Term.Efq))),
    false⟩

def «evalVersion.Eval.walk.leaf» : Def :=
  ⟨"Eval.walk.leaf",
    Term.All
      (Quan.Q1)
      (Term.Ref "Bool")
      (Term.All
        (Quan.Q1)
        (Term.App (Quan.Q0) (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "Arg"))
        (Term.All
          (Quan.Q1)
          (Term.Ref "Term")
          (Term.App
            (Quan.Q0)
            (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
            (Term.App
              (Quan.Q0)
              (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
              (Term.Ref "Term"))))),
    Term.Prj
      (Term.Mat
        "True"
        (Term.Mat
          "()"
          (Term.Prj
            (Term.Mat
              "Nil"
              (Term.Mat
                "()"
                (Term.Lam
                  (Quan.Q1)
                  (Term.Tup
                    (Quan.Q1)
                    (Term.Lab "Some")
                    (Term.Tup
                      (Quan.Q1)
                      (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))
                      (Term.Lab "()"))))
                (Term.Efq))
              (Term.Lam
                (Quan.Q1)
                (Term.Lam
                  (Quan.Q1)
                  (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()")))))))
          (Term.Efq))
        (Term.Mat
          "False"
          (Term.Mat
            "()"
            (Term.Lam
              (Quan.Q1)
              (Term.Lam
                (Quan.Q1)
                (Term.Tup
                  (Quan.Q1)
                  (Term.Lab "Some")
                  (Term.Tup
                    (Quan.Q1)
                    (Term.Tup
                      (Quan.Q1)
                      (Term.Lab "Some")
                      (Term.Tup (Quan.Q1) (Term.Var 0) (Term.Lab "()")))
                    (Term.Lab "()")))))
            (Term.Efq))
          (Term.Efq))),
    false⟩

def «evalVersion.Eval.walk» : Def :=
  ⟨"Eval.walk",
    Term.All
      (Quan.Q2)
      (Term.Ref "Term")
      (Term.All
        (Quan.Q2)
        (Term.App
          (Quan.Q0)
          (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
          (Term.Ref "Term"))
        (Term.All
          (Quan.Q2)
          (Term.App
            (Quan.Q0)
            (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
            (Term.Ref "Arg"))
          (Term.App
            (Quan.Q0)
            (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
            (Term.App
              (Quan.Q0)
              (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
              (Term.Ref "Term"))))),
    Term.Prj
      (Term.Mat
        "Term.Lam"
        (Term.Prj
          (Term.Lam
            (Quan.Q2)
            (Term.Prj
              (Term.Lam
                (Quan.Q2)
                (Term.Mat
                  "()"
                  (Term.Lam
                    (Quan.Q2)
                    (Term.Prj
                      (Term.Mat
                        "Con"
                        (Term.Prj
                          (Term.Prj
                            (Term.Mat
                              "Arg"
                              (Term.Prj
                                (Term.Lam
                                  (Quan.Q2)
                                  (Term.Prj
                                    (Term.Lam
                                      (Quan.Q2)
                                      (Term.Mat
                                        "()"
                                        (Term.Prj
                                          (Term.Lam
                                            (Quan.Q2)
                                            (Term.Mat
                                              "()"
                                              (Term.App
                                                (Quan.Q1)
                                                (Term.App
                                                  (Quan.Q1)
                                                  (Term.Ref "Eval.walk.if")
                                                  (Term.App
                                                    (Quan.Q1)
                                                    (Term.App
                                                      (Quan.Q1)
                                                      (Term.App
                                                        (Quan.Q2)
                                                        (Term.Ref "Quan.binds")
                                                        (Term.Var 5))
                                                      (Term.Var 2))
                                                    (Term.Var 1)))
                                                (Term.App
                                                  (Quan.Q2)
                                                  (Term.App
                                                    (Quan.Q2)
                                                    (Term.App
                                                      (Quan.Q2)
                                                      (Term.Ref "Eval.walk")
                                                      (Term.Var 4))
                                                    (Term.Tup
                                                      (Quan.Q1)
                                                      (Term.Lab "Con")
                                                      (Term.Tup
                                                        (Quan.Q1)
                                                        (Term.Var 1)
                                                        (Term.Tup
                                                          (Quan.Q1)
                                                          (Term.Var 3)
                                                          (Term.Lab "()")))))
                                                  (Term.Var 0)))
                                              (Term.Efq))))
                                        (Term.Efq))))))
                              (Term.Efq))))
                        (Term.Lam
                          (Quan.Q2)
                          (Term.Lam
                            (Quan.Q2)
                            (Term.App
                              (Quan.Q1)
                              (Term.App
                                (Quan.Q1)
                                (Term.App
                                  (Quan.Q1)
                                  (Term.Ref "Eval.walk.leaf")
                                  (Term.App
                                    (Quan.Q1)
                                    (Term.Ref "Term.takes")
                                    (Term.Tup
                                      (Quan.Q1)
                                      (Term.Lab "Term.Lam")
                                      (Term.Tup
                                        (Quan.Q1)
                                        (Term.Var 4)
                                        (Term.Tup (Quan.Q1) (Term.Var 3) (Term.Lab "()"))))))
                                (Term.Tup (Quan.Q1) (Term.Var 1) (Term.Var 0)))
                              (Term.App
                                (Quan.Q1)
                                (Term.App
                                  (Quan.Q1)
                                  (Term.Ref "Term.spine")
                                  (Term.Tup (Quan.Q1) (Term.Var 1) (Term.Var 0)))
                                (Term.App
                                  (Quan.Q2)
                                  (Term.App
                                    (Quan.Q2)
                                    (Term.App
                                      (Quan.Q1)
                                      (Term.Ref "Term.subst")
                                      (Term.Tup
                                        (Quan.Q1)
                                        (Term.Lab "Term.Lam")
                                        (Term.Tup
                                          (Quan.Q1)
                                          (Term.Var 4)
                                          (Term.Tup (Quan.Q1) (Term.Var 3) (Term.Lab "()")))))
                                    (Term.Var 2))
                                  (Term.Tup (Quan.Q1) (Term.Lab "Zero") (Term.Lab "()"))))))))))
                  (Term.Efq))))))
        (Term.Mat
          "Term.Prj"
          (Term.Prj
            (Term.Lam
              (Quan.Q2)
              (Term.Mat
                "()"
                (Term.Lam
                  (Quan.Q2)
                  (Term.Prj
                    (Term.Mat
                      "Con"
                      (Term.Prj
                        (Term.Prj
                          (Term.Mat
                            "Arg"
                            (Term.Prj
                              (Term.Lam
                                (Quan.Q2)
                                (Term.Prj
                                  (Term.Prj
                                    (Term.Mat
                                      "Term.Tup"
                                      (Term.Prj
                                        (Term.Lam
                                          (Quan.Q2)
                                          (Term.Prj
                                            (Term.Lam
                                              (Quan.Q2)
                                              (Term.Prj
                                                (Term.Lam
                                                  (Quan.Q2)
                                                  (Term.Mat
                                                    "()"
                                                    (Term.Mat
                                                      "()"
                                                      (Term.Prj
                                                        (Term.Lam
                                                          (Quan.Q2)
                                                          (Term.Mat
                                                            "()"
                                                            (Term.App
                                                              (Quan.Q1)
                                                              (Term.App
                                                                (Quan.Q1)
                                                                (Term.Ref "Eval.walk.if")
                                                                (Term.App
                                                                  (Quan.Q1)
                                                                  (Term.Ref "Quan.live")
                                                                  (Term.Var 4)))
                                                              (Term.App
                                                                (Quan.Q2)
                                                                (Term.App
                                                                  (Quan.Q2)
                                                                  (Term.App
                                                                    (Quan.Q2)
                                                                    (Term.Ref "Eval.walk")
                                                                    (Term.Var 6))
                                                                  (Term.Var 5))
                                                                (Term.Tup
                                                                  (Quan.Q1)
                                                                  (Term.Lab "Con")
                                                                  (Term.Tup
                                                                    (Quan.Q1)
                                                                    (Term.Tup
                                                                      (Quan.Q1)
                                                                      (Term.Lab "Arg")
                                                                      (Term.Tup
                                                                        (Quan.Q1)
                                                                        (Term.App
                                                                          (Quan.Q1)
                                                                          (Term.App
                                                                            (Quan.Q1)
                                                                            (Term.Ref "Quan.fld")
                                                                            (Term.Var 3))
                                                                          (Term.Var 4))
                                                                        (Term.Tup
                                                                          (Quan.Q1)
                                                                          (Term.Var 2)
                                                                          (Term.Lab "()"))))
                                                                    (Term.Tup
                                                                      (Quan.Q1)
                                                                      (Term.Tup
                                                                        (Quan.Q1)
                                                                        (Term.Lab "Con")
                                                                        (Term.Tup
                                                                          (Quan.Q1)
                                                                          (Term.Tup
                                                                            (Quan.Q1)
                                                                            (Term.Lab "Arg")
                                                                            (Term.Tup
                                                                              (Quan.Q1)
                                                                              (Term.Var 4)
                                                                              (Term.Tup
                                                                                (Quan.Q1)
                                                                                (Term.Var 1)
                                                                                (Term.Lab "()"))))
                                                                          (Term.Tup
                                                                            (Quan.Q1)
                                                                            (Term.Var 0)
                                                                            (Term.Lab "()"))))
                                                                      (Term.Lab "()"))))))
                                                            (Term.Efq))))
                                                      (Term.Efq))
                                                    (Term.Efq))))))))
                                      (Term.Lam
                                        (Quan.Q2)
                                        (Term.Lam
                                          (Quan.Q2)
                                          (Term.Mat
                                            "()"
                                            (Term.Prj
                                              (Term.Lam
                                                (Quan.Q2)
                                                (Term.Mat
                                                  "()"
                                                  (Term.App
                                                    (Quan.Q1)
                                                    (Term.App
                                                      (Quan.Q1)
                                                      (Term.App
                                                        (Quan.Q1)
                                                        (Term.Ref "Eval.walk.leaf")
                                                        (Term.App
                                                          (Quan.Q1)
                                                          (Term.Ref "Term.takes")
                                                          (Term.Tup
                                                            (Quan.Q1)
                                                            (Term.Lab "Term.Prj")
                                                            (Term.Tup
                                                              (Quan.Q1)
                                                              (Term.Var 5)
                                                              (Term.Lab "()")))))
                                                      (Term.Tup
                                                        (Quan.Q1)
                                                        (Term.Lab "Con")
                                                        (Term.Tup
                                                          (Quan.Q1)
                                                          (Term.Tup
                                                            (Quan.Q1)
                                                            (Term.Lab "Arg")
                                                            (Term.Tup
                                                              (Quan.Q1)
                                                              (Term.Var 3)
                                                              (Term.Tup
                                                                (Quan.Q1)
                                                                (Term.Tup
                                                                  (Quan.Q1)
                                                                  (Term.Var 2)
                                                                  (Term.Var 1))
                                                                (Term.Lab "()"))))
                                                          (Term.Tup
                                                            (Quan.Q1)
                                                            (Term.Var 0)
                                                            (Term.Lab "()")))))
                                                    (Term.App
                                                      (Quan.Q1)
                                                      (Term.App
                                                        (Quan.Q1)
                                                        (Term.Ref "Term.spine")
                                                        (Term.Tup
                                                          (Quan.Q1)
                                                          (Term.Lab "Con")
                                                          (Term.Tup
                                                            (Quan.Q1)
                                                            (Term.Tup
                                                              (Quan.Q1)
                                                              (Term.Lab "Arg")
                                                              (Term.Tup
                                                                (Quan.Q1)
                                                                (Term.Var 3)
                                                                (Term.Tup
                                                                  (Quan.Q1)
                                                                  (Term.Tup
                                                                    (Quan.Q1)
                                                                    (Term.Var 2)
                                                                    (Term.Var 1))
                                                                  (Term.Lab "()"))))
                                                            (Term.Tup
                                                              (Quan.Q1)
                                                              (Term.Var 0)
                                                              (Term.Lab "()")))))
                                                      (Term.App
                                                        (Quan.Q2)
                                                        (Term.App
                                                          (Quan.Q2)
                                                          (Term.App
                                                            (Quan.Q1)
                                                            (Term.Ref "Term.subst")
                                                            (Term.Tup
                                                              (Quan.Q1)
                                                              (Term.Lab "Term.Prj")
                                                              (Term.Tup
                                                                (Quan.Q1)
                                                                (Term.Var 5)
                                                                (Term.Lab "()"))))
                                                          (Term.Var 4))
                                                        (Term.Tup
                                                          (Quan.Q1)
                                                          (Term.Lab "Zero")
                                                          (Term.Lab "()")))))
                                                  (Term.Efq))))
                                            (Term.Efq)))))))))
                            (Term.Efq))))
                      (Term.Lam
                        (Quan.Q2)
                        (Term.Lam
                          (Quan.Q2)
                          (Term.App
                            (Quan.Q1)
                            (Term.App
                              (Quan.Q1)
                              (Term.App
                                (Quan.Q1)
                                (Term.Ref "Eval.walk.leaf")
                                (Term.App
                                  (Quan.Q1)
                                  (Term.Ref "Term.takes")
                                  (Term.Tup
                                    (Quan.Q1)
                                    (Term.Lab "Term.Prj")
                                    (Term.Tup (Quan.Q1) (Term.Var 3) (Term.Lab "()")))))
                              (Term.Tup (Quan.Q1) (Term.Var 1) (Term.Var 0)))
                            (Term.App
                              (Quan.Q1)
                              (Term.App
                                (Quan.Q1)
                                (Term.Ref "Term.spine")
                                (Term.Tup (Quan.Q1) (Term.Var 1) (Term.Var 0)))
                              (Term.App
                                (Quan.Q2)
                                (Term.App
                                  (Quan.Q2)
                                  (Term.App
                                    (Quan.Q1)
                                    (Term.Ref "Term.subst")
                                    (Term.Tup
                                      (Quan.Q1)
                                      (Term.Lab "Term.Prj")
                                      (Term.Tup (Quan.Q1) (Term.Var 3) (Term.Lab "()"))))
                                  (Term.Var 2))
                                (Term.Tup (Quan.Q1) (Term.Lab "Zero") (Term.Lab "()"))))))))))
                (Term.Efq))))
          (Term.Mat
            "Term.Mat"
            (Term.Prj
              (Term.Lam
                (Quan.Q2)
                (Term.Prj
                  (Term.Lam
                    (Quan.Q2)
                    (Term.Prj
                      (Term.Lam
                        (Quan.Q2)
                        (Term.Mat
                          "()"
                          (Term.Lam
                            (Quan.Q2)
                            (Term.Prj
                              (Term.Mat
                                "Con"
                                (Term.Prj
                                  (Term.Prj
                                    (Term.Mat
                                      "Arg"
                                      (Term.Prj
                                        (Term.Lam
                                          (Quan.Q2)
                                          (Term.Prj
                                            (Term.Prj
                                              (Term.Mat
                                                "Term.Lab"
                                                (Term.Prj
                                                  (Term.Lam
                                                    (Quan.Q2)
                                                    (Term.Mat
                                                      "()"
                                                      (Term.Mat
                                                        "()"
                                                        (Term.Prj
                                                          (Term.Lam
                                                            (Quan.Q2)
                                                            (Term.Mat
                                                              "()"
                                                              (Term.App
                                                                (Quan.Q1)
                                                                (Term.App
                                                                  (Quan.Q1)
                                                                  (Term.Ref "Eval.walk.if")
                                                                  (Term.App
                                                                    (Quan.Q1)
                                                                    (Term.Ref "Quan.live")
                                                                    (Term.Var 2)))
                                                                (Term.App
                                                                  (Quan.Q1)
                                                                  (Term.App
                                                                    (Quan.Q1)
                                                                    (Term.App
                                                                      (Quan.Q1)
                                                                      (Term.Ref "Eval.walk.pick")
                                                                      (Term.App
                                                                        (Quan.Q1)
                                                                        (Term.App
                                                                          (Quan.Q1)
                                                                          (Term.Ref "Name.is_eq")
                                                                          (Term.Var 1))
                                                                        (Term.Var 6)))
                                                                    (Term.App
                                                                      (Quan.Q2)
                                                                      (Term.App
                                                                        (Quan.Q2)
                                                                        (Term.App
                                                                          (Quan.Q2)
                                                                          (Term.Ref "Eval.walk")
                                                                          (Term.Var 5))
                                                                        (Term.Var 3))
                                                                      (Term.Var 0)))
                                                                  (Term.App
                                                                    (Quan.Q2)
                                                                    (Term.App
                                                                      (Quan.Q2)
                                                                      (Term.App
                                                                        (Quan.Q2)
                                                                        (Term.Ref "Eval.walk")
                                                                        (Term.Var 4))
                                                                      (Term.Var 3))
                                                                    (Term.Tup
                                                                      (Quan.Q1)
                                                                      (Term.Lab "Con")
                                                                      (Term.Tup
                                                                        (Quan.Q1)
                                                                        (Term.Tup
                                                                          (Quan.Q1)
                                                                          (Term.Lab "Arg")
                                                                          (Term.Tup
                                                                            (Quan.Q1)
                                                                            (Term.Var 2)
                                                                            (Term.Tup
                                                                              (Quan.Q1)
                                                                              (Term.Tup
                                                                                (Quan.Q1)
                                                                                (Term.Lab
                                                                                  "Term.Lab")
                                                                                (Term.Tup
                                                                                  (Quan.Q1)
                                                                                  (Term.Var 1)
                                                                                  (Term.Lab "()")))
                                                                              (Term.Lab "()"))))
                                                                        (Term.Tup
                                                                          (Quan.Q1)
                                                                          (Term.Var 0)
                                                                          (Term.Lab "()")))))))
                                                              (Term.Efq))))
                                                        (Term.Efq))
                                                      (Term.Efq))))
                                                (Term.Lam
                                                  (Quan.Q2)
                                                  (Term.Lam
                                                    (Quan.Q2)
                                                    (Term.Mat
                                                      "()"
                                                      (Term.Prj
                                                        (Term.Lam
                                                          (Quan.Q2)
                                                          (Term.Mat
                                                            "()"
                                                            (Term.App
                                                              (Quan.Q1)
                                                              (Term.App
                                                                (Quan.Q1)
                                                                (Term.App
                                                                  (Quan.Q1)
                                                                  (Term.Ref "Eval.walk.leaf")
                                                                  (Term.App
                                                                    (Quan.Q1)
                                                                    (Term.Ref "Term.takes")
                                                                    (Term.Tup
                                                                      (Quan.Q1)
                                                                      (Term.Lab "Term.Mat")
                                                                      (Term.Tup
                                                                        (Quan.Q1)
                                                                        (Term.Var 7)
                                                                        (Term.Tup
                                                                          (Quan.Q1)
                                                                          (Term.Var 6)
                                                                          (Term.Tup
                                                                            (Quan.Q1)
                                                                            (Term.Var 5)
                                                                            (Term.Lab "()")))))))
                                                                (Term.Tup
                                                                  (Quan.Q1)
                                                                  (Term.Lab "Con")
                                                                  (Term.Tup
                                                                    (Quan.Q1)
                                                                    (Term.Tup
                                                                      (Quan.Q1)
                                                                      (Term.Lab "Arg")
                                                                      (Term.Tup
                                                                        (Quan.Q1)
                                                                        (Term.Var 3)
                                                                        (Term.Tup
                                                                          (Quan.Q1)
                                                                          (Term.Tup
                                                                            (Quan.Q1)
                                                                            (Term.Var 2)
                                                                            (Term.Var 1))
                                                                          (Term.Lab "()"))))
                                                                    (Term.Tup
                                                                      (Quan.Q1)
                                                                      (Term.Var 0)
                                                                      (Term.Lab "()")))))
                                                              (Term.App
                                                                (Quan.Q1)
                                                                (Term.App
                                                                  (Quan.Q1)
                                                                  (Term.Ref "Term.spine")
                                                                  (Term.Tup
                                                                    (Quan.Q1)
                                                                    (Term.Lab "Con")
                                                                    (Term.Tup
                                                                      (Quan.Q1)
                                                                      (Term.Tup
                                                                        (Quan.Q1)
                                                                        (Term.Lab "Arg")
                                                                        (Term.Tup
                                                                          (Quan.Q1)
                                                                          (Term.Var 3)
                                                                          (Term.Tup
                                                                            (Quan.Q1)
                                                                            (Term.Tup
                                                                              (Quan.Q1)
                                                                              (Term.Var 2)
                                                                              (Term.Var 1))
                                                                            (Term.Lab "()"))))
                                                                      (Term.Tup
                                                                        (Quan.Q1)
                                                                        (Term.Var 0)
                                                                        (Term.Lab "()")))))
                                                                (Term.App
                                                                  (Quan.Q2)
                                                                  (Term.App
                                                                    (Quan.Q2)
                                                                    (Term.App
                                                                      (Quan.Q1)
                                                                      (Term.Ref "Term.subst")
                                                                      (Term.Tup
                                                                        (Quan.Q1)
                                                                        (Term.Lab "Term.Mat")
                                                                        (Term.Tup
                                                                          (Quan.Q1)
                                                                          (Term.Var 7)
                                                                          (Term.Tup
                                                                            (Quan.Q1)
                                                                            (Term.Var 6)
                                                                            (Term.Tup
                                                                              (Quan.Q1)
                                                                              (Term.Var 5)
                                                                              (Term.Lab "()"))))))
                                                                    (Term.Var 4))
                                                                  (Term.Tup
                                                                    (Quan.Q1)
                                                                    (Term.Lab "Zero")
                                                                    (Term.Lab "()")))))
                                                            (Term.Efq))))
                                                      (Term.Efq)))))))))
                                      (Term.Efq))))
                                (Term.Lam
                                  (Quan.Q2)
                                  (Term.Lam
                                    (Quan.Q2)
                                    (Term.App
                                      (Quan.Q1)
                                      (Term.App
                                        (Quan.Q1)
                                        (Term.App
                                          (Quan.Q1)
                                          (Term.Ref "Eval.walk.leaf")
                                          (Term.App
                                            (Quan.Q1)
                                            (Term.Ref "Term.takes")
                                            (Term.Tup
                                              (Quan.Q1)
                                              (Term.Lab "Term.Mat")
                                              (Term.Tup
                                                (Quan.Q1)
                                                (Term.Var 5)
                                                (Term.Tup
                                                  (Quan.Q1)
                                                  (Term.Var 4)
                                                  (Term.Tup
                                                    (Quan.Q1)
                                                    (Term.Var 3)
                                                    (Term.Lab "()")))))))
                                        (Term.Tup (Quan.Q1) (Term.Var 1) (Term.Var 0)))
                                      (Term.App
                                        (Quan.Q1)
                                        (Term.App
                                          (Quan.Q1)
                                          (Term.Ref "Term.spine")
                                          (Term.Tup (Quan.Q1) (Term.Var 1) (Term.Var 0)))
                                        (Term.App
                                          (Quan.Q2)
                                          (Term.App
                                            (Quan.Q2)
                                            (Term.App
                                              (Quan.Q1)
                                              (Term.Ref "Term.subst")
                                              (Term.Tup
                                                (Quan.Q1)
                                                (Term.Lab "Term.Mat")
                                                (Term.Tup
                                                  (Quan.Q1)
                                                  (Term.Var 5)
                                                  (Term.Tup
                                                    (Quan.Q1)
                                                    (Term.Var 4)
                                                    (Term.Tup
                                                      (Quan.Q1)
                                                      (Term.Var 3)
                                                      (Term.Lab "()"))))))
                                            (Term.Var 2))
                                          (Term.Tup
                                            (Quan.Q1)
                                            (Term.Lab "Zero")
                                            (Term.Lab "()"))))))))))
                          (Term.Efq))))))))
            (Term.Mat
              "Term.App"
              (Term.Prj
                (Term.Lam
                  (Quan.Q2)
                  (Term.Prj
                    (Term.Lam
                      (Quan.Q2)
                      (Term.Prj
                        (Term.Prj
                          (Term.Mat
                            "Term.Var"
                            (Term.Prj
                              (Term.Lam
                                (Quan.Q2)
                                (Term.Mat
                                  "()"
                                  (Term.Mat
                                    "()"
                                    (Term.Lam
                                      (Quan.Q2)
                                      (Term.Lam
                                        (Quan.Q2)
                                        (Term.App
                                          (Quan.Q1)
                                          (Term.App
                                            (Quan.Q1)
                                            (Term.App
                                              (Quan.Q1)
                                              (Term.Ref "Eval.walk.app")
                                              (Term.App
                                                (Quan.Q1)
                                                (Term.Ref "Term.takes")
                                                (Term.App
                                                  (Quan.Q1)
                                                  (Term.Ref "Term.head")
                                                  (Term.Var 3))))
                                            (Term.App
                                              (Quan.Q2)
                                              (Term.App
                                                (Quan.Q2)
                                                (Term.App
                                                  (Quan.Q2)
                                                  (Term.Ref "Eval.walk")
                                                  (Term.Var 3))
                                                (Term.Var 1))
                                              (Term.Tup
                                                (Quan.Q1)
                                                (Term.Lab "Con")
                                                (Term.Tup
                                                  (Quan.Q1)
                                                  (Term.Tup
                                                    (Quan.Q1)
                                                    (Term.Lab "Arg")
                                                    (Term.Tup
                                                      (Quan.Q1)
                                                      (Term.Var 4)
                                                      (Term.Tup
                                                        (Quan.Q1)
                                                        (Term.App
                                                          (Quan.Q1)
                                                          (Term.App
                                                            (Quan.Q1)
                                                            (Term.Ref "Env.sub")
                                                            (Term.Var 1))
                                                          (Term.Var 2))
                                                        (Term.Lab "()"))))
                                                  (Term.Tup
                                                    (Quan.Q1)
                                                    (Term.Var 0)
                                                    (Term.Lab "()"))))))
                                          (Term.App
                                            (Quan.Q1)
                                            (Term.App
                                              (Quan.Q1)
                                              (Term.Ref "Term.spine")
                                              (Term.Var 0))
                                            (Term.App
                                              (Quan.Q2)
                                              (Term.App
                                                (Quan.Q2)
                                                (Term.App
                                                  (Quan.Q1)
                                                  (Term.Ref "Term.subst")
                                                  (Term.Tup
                                                    (Quan.Q1)
                                                    (Term.Lab "Term.App")
                                                    (Term.Tup
                                                      (Quan.Q1)
                                                      (Term.Var 4)
                                                      (Term.Tup
                                                        (Quan.Q1)
                                                        (Term.Var 3)
                                                        (Term.Tup
                                                          (Quan.Q1)
                                                          (Term.Tup
                                                            (Quan.Q1)
                                                            (Term.Lab "Term.Var")
                                                            (Term.Tup
                                                              (Quan.Q1)
                                                              (Term.Var 2)
                                                              (Term.Lab "()")))
                                                          (Term.Lab "()"))))))
                                                (Term.Var 1))
                                              (Term.Tup
                                                (Quan.Q1)
                                                (Term.Lab "Zero")
                                                (Term.Lab "()")))))))
                                    (Term.Efq))
                                  (Term.Efq))))
                            (Term.Lam
                              (Quan.Q2)
                              (Term.Lam
                                (Quan.Q2)
                                (Term.Mat
                                  "()"
                                  (Term.Lam
                                    (Quan.Q2)
                                    (Term.Lam
                                      (Quan.Q2)
                                      (Term.App
                                        (Quan.Q1)
                                        (Term.App
                                          (Quan.Q1)
                                          (Term.App
                                            (Quan.Q1)
                                            (Term.Ref "Eval.walk.leaf")
                                            (Term.App
                                              (Quan.Q1)
                                              (Term.Ref "Term.takes")
                                              (Term.Tup
                                                (Quan.Q1)
                                                (Term.Lab "Term.App")
                                                (Term.Tup
                                                  (Quan.Q1)
                                                  (Term.Var 5)
                                                  (Term.Tup
                                                    (Quan.Q1)
                                                    (Term.Var 4)
                                                    (Term.Tup
                                                      (Quan.Q1)
                                                      (Term.Tup (Quan.Q1) (Term.Var 3) (Term.Var 2))
                                                      (Term.Lab "()")))))))
                                          (Term.Var 0))
                                        (Term.App
                                          (Quan.Q1)
                                          (Term.App (Quan.Q1) (Term.Ref "Term.spine") (Term.Var 0))
                                          (Term.App
                                            (Quan.Q2)
                                            (Term.App
                                              (Quan.Q2)
                                              (Term.App
                                                (Quan.Q1)
                                                (Term.Ref "Term.subst")
                                                (Term.Tup
                                                  (Quan.Q1)
                                                  (Term.Lab "Term.App")
                                                  (Term.Tup
                                                    (Quan.Q1)
                                                    (Term.Var 5)
                                                    (Term.Tup
                                                      (Quan.Q1)
                                                      (Term.Var 4)
                                                      (Term.Tup
                                                        (Quan.Q1)
                                                        (Term.Tup
                                                          (Quan.Q1)
                                                          (Term.Var 3)
                                                          (Term.Var 2))
                                                        (Term.Lab "()"))))))
                                              (Term.Var 1))
                                            (Term.Tup
                                              (Quan.Q1)
                                              (Term.Lab "Zero")
                                              (Term.Lab "()")))))))
                                  (Term.Efq)))))))))))
              (Term.Lam
                (Quan.Q2)
                (Term.Lam
                  (Quan.Q2)
                  (Term.Lam
                    (Quan.Q2)
                    (Term.Lam
                      (Quan.Q2)
                      (Term.App
                        (Quan.Q1)
                        (Term.App
                          (Quan.Q1)
                          (Term.App
                            (Quan.Q1)
                            (Term.Ref "Eval.walk.leaf")
                            (Term.App
                              (Quan.Q1)
                              (Term.Ref "Term.takes")
                              (Term.Tup (Quan.Q1) (Term.Var 3) (Term.Var 2))))
                          (Term.Var 0))
                        (Term.App
                          (Quan.Q1)
                          (Term.App (Quan.Q1) (Term.Ref "Term.spine") (Term.Var 0))
                          (Term.App
                            (Quan.Q2)
                            (Term.App
                              (Quan.Q2)
                              (Term.App
                                (Quan.Q1)
                                (Term.Ref "Term.subst")
                                (Term.Tup (Quan.Q1) (Term.Var 3) (Term.Var 2)))
                              (Term.Var 1))
                            (Term.Tup (Quan.Q1) (Term.Lab "Zero") (Term.Lab "()"))))))))))))),
    false⟩

def «evalVersion.Eval.callWalk.def» : Def :=
  ⟨"Eval.callWalk.def",
    Term.All
      (Quan.Q1)
      (Term.App (Quan.Q0) (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1")) (Term.Ref "Def"))
      (Term.All
        (Quan.Q1)
        (Term.App (Quan.Q0) (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "Arg"))
        (Term.App
          (Quan.Q0)
          (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
          (Term.App
            (Quan.Q0)
            (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
            (Term.Ref "Term")))),
    Term.Prj
      (Term.Mat
        "None"
        (Term.Mat
          "()"
          (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()")))
          (Term.Efq))
        (Term.Mat
          "Some"
          (Term.Prj
            (Term.Prj
              (Term.Mat
                "Def"
                (Term.Prj
                  (Term.Lam
                    (Quan.Q1)
                    (Term.Prj
                      (Term.Lam
                        (Quan.Q1)
                        (Term.Prj
                          (Term.Lam
                            (Quan.Q1)
                            (Term.Prj
                              (Term.Lam
                                (Quan.Q1)
                                (Term.Mat
                                  "()"
                                  (Term.Mat
                                    "()"
                                    (Term.Lam
                                      (Quan.Q1)
                                      (Term.App
                                        (Quan.Q2)
                                        (Term.App
                                          (Quan.Q2)
                                          (Term.App (Quan.Q2) (Term.Ref "Eval.walk") (Term.Var 2))
                                          (Term.Tup (Quan.Q1) (Term.Lab "Nil") (Term.Lab "()")))
                                        (Term.Var 0)))
                                    (Term.Efq))
                                  (Term.Efq))))))))))
                (Term.Efq))))
          (Term.Efq))),
    false⟩

def «evalVersion.Eval.callWalk.head» : Def :=
  ⟨"Eval.callWalk.head",
    Term.All
      (Quan.Q1)
      (Term.App (Quan.Q0) (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "Def"))
      (Term.All
        (Quan.Q1)
        (Term.Ref "Term")
        (Term.All
          (Quan.Q1)
          (Term.App
            (Quan.Q0)
            (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
            (Term.Ref "Arg"))
          (Term.App
            (Quan.Q0)
            (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
            (Term.App
              (Quan.Q0)
              (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
              (Term.Ref "Term"))))),
    Term.Lam
      (Quan.Q1)
      (Term.Prj
        (Term.Mat
          "Term.Ref"
          (Term.Prj
            (Term.Lam
              (Quan.Q1)
              (Term.Mat
                "()"
                (Term.Lam
                  (Quan.Q1)
                  (Term.App
                    (Quan.Q1)
                    (Term.App
                      (Quan.Q1)
                      (Term.Ref "Eval.callWalk.def")
                      (Term.App
                        (Quan.Q2)
                        (Term.App (Quan.Q1) (Term.Ref "Book.get") (Term.Var 2))
                        (Term.Var 1)))
                    (Term.Var 0)))
                (Term.Efq))))
          (Term.Lam
            (Quan.Q1)
            (Term.Lam
              (Quan.Q1)
              (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))))))),
    false⟩

def «evalVersion.Eval.callWalk» : Def :=
  ⟨"Eval.callWalk",
    Term.All
      (Quan.Q1)
      (Term.App (Quan.Q0) (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "Def"))
      (Term.All
        (Quan.Q2)
        (Term.Ref "Term")
        (Term.App
          (Quan.Q0)
          (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
          (Term.App
            (Quan.Q0)
            (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
            (Term.Ref "Term")))),
    Term.Lam
      (Quan.Q1)
      (Term.Lam
        (Quan.Q2)
        (Term.App
          (Quan.Q1)
          (Term.App
            (Quan.Q1)
            (Term.App (Quan.Q1) (Term.Ref "Eval.callWalk.head") (Term.Var 1))
            (Term.App (Quan.Q1) (Term.Ref "Term.head") (Term.Var 0)))
          (Term.App
            (Quan.Q1)
            (Term.App (Quan.Q1) (Term.Ref "Term.args") (Term.Var 0))
            (Term.Tup (Quan.Q1) (Term.Lab "Nil") (Term.Lab "()"))))),
    false⟩

def «evalVersion.Eval.waits» : Def :=
  ⟨"Eval.waits",
    Term.All
      (Quan.Q1)
      (Term.App
        (Quan.Q0)
        (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
        (Term.App
          (Quan.Q0)
          (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
          (Term.Ref "Term")))
      (Term.Ref "Bool"),
    Term.Prj
      (Term.Mat
        "Some"
        (Term.Prj
          (Term.Prj
            (Term.Mat
              "None"
              (Term.Mat
                "()"
                (Term.Mat "()" (Term.Tup (Quan.Q1) (Term.Lab "True") (Term.Lab "()")) (Term.Efq))
                (Term.Efq))
              (Term.Lam
                (Quan.Q1)
                (Term.Lam
                  (Quan.Q1)
                  (Term.Mat
                    "()"
                    (Term.Tup (Quan.Q1) (Term.Lab "False") (Term.Lab "()"))
                    (Term.Efq)))))))
        (Term.Lam
          (Quan.Q1)
          (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "False") (Term.Lab "()"))))),
    false⟩

def «evalVersion.Eval.vals.app» : Def :=
  ⟨"Eval.vals.app",
    Term.All
      (Quan.Q1)
      (Term.Ref "Bool")
      (Term.All
        (Quan.Q1)
        (Term.Ref "Bool")
        (Term.All
          (Quan.Q1)
          (Term.App
            (Quan.Q0)
            (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
            (Term.App
              (Quan.Q0)
              (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
              (Term.Ref "Term")))
          (Term.Ref "Bool"))),
    Term.Prj
      (Term.Mat
        "True"
        (Term.Mat "()" (Term.Lam (Quan.Q1) (Term.Lam (Quan.Q1) (Term.Var 1))) (Term.Efq))
        (Term.Mat
          "False"
          (Term.Mat
            "()"
            (Term.Lam
              (Quan.Q1)
              (Term.Lam
                (Quan.Q1)
                (Term.App
                  (Quan.Q1)
                  (Term.App (Quan.Q1) (Term.Ref "Bool.and") (Term.Var 1))
                  (Term.App (Quan.Q1) (Term.Ref "Eval.waits") (Term.Var 0)))))
            (Term.Efq))
          (Term.Efq))),
    false⟩

def «evalVersion.Eval.vals.ref» : Def :=
  ⟨"Eval.vals.ref",
    Term.All
      (Quan.Q1)
      (Term.Ref "Bool")
      (Term.All
        (Quan.Q1)
        (Term.App
          (Quan.Q0)
          (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
          (Term.App
            (Quan.Q0)
            (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
            (Term.Ref "Term")))
        (Term.Ref "Bool")),
    Term.Prj
      (Term.Mat
        "True"
        (Term.Mat
          "()"
          (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "True") (Term.Lab "()")))
          (Term.Efq))
        (Term.Mat
          "False"
          (Term.Mat
            "()"
            (Term.Lam (Quan.Q1) (Term.App (Quan.Q1) (Term.Ref "Eval.waits") (Term.Var 0)))
            (Term.Efq))
          (Term.Efq))),
    false⟩

def «evalVersion.Eval.vals.other» : Def :=
  ⟨"Eval.vals.other",
    Term.All (Quan.Q1) (Term.Ref "Bool") (Term.All (Quan.Q1) (Term.Ref "Bool") (Term.Ref "Bool")),
    Term.Prj
      (Term.Mat
        "True"
        (Term.Mat
          "()"
          (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "False") (Term.Lab "()")))
          (Term.Efq))
        (Term.Mat "False" (Term.Mat "()" (Term.Lam (Quan.Q1) (Term.Var 0)) (Term.Efq)) (Term.Efq))),
    false⟩

def «evalVersion.Eval.vals» : Def :=
  ⟨"Eval.vals",
    Term.All
      (Quan.Q2)
      (Term.App (Quan.Q0) (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "Def"))
      (Term.All
        (Quan.Q2)
        (Term.Ref "Term")
        (Term.All (Quan.Q1) (Term.Ref "Bool") (Term.Ref "Bool"))),
    Term.Lam
      (Quan.Q2)
      (Term.Prj
        (Term.Mat
          "Term.Tup"
          (Term.Prj
            (Term.Lam
              (Quan.Q2)
              (Term.Prj
                (Term.Lam
                  (Quan.Q2)
                  (Term.Prj
                    (Term.Lam
                      (Quan.Q2)
                      (Term.Mat
                        "()"
                        (Term.Prj
                          (Term.Mat
                            "True"
                            (Term.Mat
                              "()"
                              (Term.Tup (Quan.Q1) (Term.Lab "False") (Term.Lab "()"))
                              (Term.Efq))
                            (Term.Mat
                              "False"
                              (Term.Mat
                                "()"
                                (Term.App
                                  (Quan.Q1)
                                  (Term.App
                                    (Quan.Q1)
                                    (Term.Ref "Bool.and")
                                    (Term.App
                                      (Quan.Q1)
                                      (Term.App
                                        (Quan.Q1)
                                        (Term.Ref "Bool.or")
                                        (Term.App
                                          (Quan.Q1)
                                          (Term.Ref "Bool.not")
                                          (Term.App (Quan.Q1) (Term.Ref "Quan.live") (Term.Var 2))))
                                      (Term.App
                                        (Quan.Q1)
                                        (Term.App
                                          (Quan.Q2)
                                          (Term.App (Quan.Q2) (Term.Ref "Eval.vals") (Term.Var 3))
                                          (Term.Var 1))
                                        (Term.Tup (Quan.Q1) (Term.Lab "False") (Term.Lab "()")))))
                                  (Term.App
                                    (Quan.Q1)
                                    (Term.App
                                      (Quan.Q2)
                                      (Term.App (Quan.Q2) (Term.Ref "Eval.vals") (Term.Var 3))
                                      (Term.Var 0))
                                    (Term.Tup (Quan.Q1) (Term.Lab "False") (Term.Lab "()"))))
                                (Term.Efq))
                              (Term.Efq))))
                        (Term.Efq))))))))
          (Term.Mat
            "Term.App"
            (Term.Prj
              (Term.Lam
                (Quan.Q2)
                (Term.Prj
                  (Term.Lam
                    (Quan.Q2)
                    (Term.Prj
                      (Term.Lam
                        (Quan.Q2)
                        (Term.Mat
                          "()"
                          (Term.Lam
                            (Quan.Q1)
                            (Term.App
                              (Quan.Q1)
                              (Term.App
                                (Quan.Q1)
                                (Term.App (Quan.Q1) (Term.Ref "Eval.vals.app") (Term.Var 0))
                                (Term.App
                                  (Quan.Q1)
                                  (Term.App
                                    (Quan.Q1)
                                    (Term.Ref "Bool.and")
                                    (Term.App
                                      (Quan.Q1)
                                      (Term.App
                                        (Quan.Q2)
                                        (Term.App (Quan.Q2) (Term.Ref "Eval.vals") (Term.Var 4))
                                        (Term.Var 2))
                                      (Term.Tup (Quan.Q1) (Term.Lab "True") (Term.Lab "()"))))
                                  (Term.App
                                    (Quan.Q1)
                                    (Term.App
                                      (Quan.Q1)
                                      (Term.Ref "Bool.or")
                                      (Term.App
                                        (Quan.Q1)
                                        (Term.Ref "Bool.not")
                                        (Term.App (Quan.Q1) (Term.Ref "Quan.live") (Term.Var 3))))
                                    (Term.App
                                      (Quan.Q1)
                                      (Term.App
                                        (Quan.Q2)
                                        (Term.App (Quan.Q2) (Term.Ref "Eval.vals") (Term.Var 4))
                                        (Term.Var 1))
                                      (Term.Tup (Quan.Q1) (Term.Lab "False") (Term.Lab "()"))))))
                              (Term.App
                                (Quan.Q2)
                                (Term.App (Quan.Q1) (Term.Ref "Eval.callWalk") (Term.Var 4))
                                (Term.Tup
                                  (Quan.Q1)
                                  (Term.Lab "Term.App")
                                  (Term.Tup
                                    (Quan.Q1)
                                    (Term.Var 3)
                                    (Term.Tup
                                      (Quan.Q1)
                                      (Term.Var 2)
                                      (Term.Tup (Quan.Q1) (Term.Var 1) (Term.Lab "()"))))))))
                          (Term.Efq))))))))
            (Term.Mat
              "Term.Ref"
              (Term.Prj
                (Term.Lam
                  (Quan.Q2)
                  (Term.Mat
                    "()"
                    (Term.Lam
                      (Quan.Q1)
                      (Term.App
                        (Quan.Q1)
                        (Term.App (Quan.Q1) (Term.Ref "Eval.vals.ref") (Term.Var 0))
                        (Term.App
                          (Quan.Q2)
                          (Term.App (Quan.Q1) (Term.Ref "Eval.callWalk") (Term.Var 2))
                          (Term.Tup
                            (Quan.Q1)
                            (Term.Lab "Term.Ref")
                            (Term.Tup (Quan.Q1) (Term.Var 1) (Term.Lab "()"))))))
                    (Term.Efq))))
              (Term.Lam
                (Quan.Q2)
                (Term.Lam
                  (Quan.Q2)
                  (Term.Lam
                    (Quan.Q1)
                    (Term.App
                      (Quan.Q1)
                      (Term.App (Quan.Q1) (Term.Ref "Eval.vals.other") (Term.Var 0))
                      (Term.App
                        (Quan.Q1)
                        (Term.Ref "Term.is_former")
                        (Term.Tup (Quan.Q1) (Term.Var 2) (Term.Var 1))))))))))),
    false⟩

def «evalVersion.Eval.call.if» : Def :=
  ⟨"Eval.call.if",
    Term.All
      (Quan.Q1)
      (Term.Ref "Bool")
      (Term.All
        (Quan.Q1)
        (Term.App
          (Quan.Q0)
          (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
          (Term.App
            (Quan.Q0)
            (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
            (Term.Ref "Term")))
        (Term.App
          (Quan.Q0)
          (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
          (Term.Ref "Term"))),
    Term.Prj
      (Term.Mat
        "True"
        (Term.Mat
          "()"
          (Term.Prj
            (Term.Mat
              "Some"
              (Term.Prj
                (Term.Prj
                  (Term.Mat
                    "Some"
                    (Term.Prj
                      (Term.Lam
                        (Quan.Q1)
                        (Term.Mat
                          "()"
                          (Term.Mat
                            "()"
                            (Term.Tup
                              (Quan.Q1)
                              (Term.Lab "Some")
                              (Term.Tup (Quan.Q1) (Term.Var 0) (Term.Lab "()")))
                            (Term.Efq))
                          (Term.Efq))))
                    (Term.Lam
                      (Quan.Q1)
                      (Term.Lam
                        (Quan.Q1)
                        (Term.Mat
                          "()"
                          (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))
                          (Term.Efq)))))))
              (Term.Lam
                (Quan.Q1)
                (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))))))
          (Term.Efq))
        (Term.Lam
          (Quan.Q1)
          (Term.Lam
            (Quan.Q1)
            (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()")))))),
    false⟩

def «evalVersion.Eval.call» : Def :=
  ⟨"Eval.call",
    Term.All
      (Quan.Q2)
      (Term.App (Quan.Q0) (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "Def"))
      (Term.All
        (Quan.Q2)
        (Term.Ref "Term")
        (Term.App
          (Quan.Q0)
          (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
          (Term.Ref "Term"))),
    Term.Lam
      (Quan.Q2)
      (Term.Lam
        (Quan.Q2)
        (Term.App
          (Quan.Q1)
          (Term.App
            (Quan.Q1)
            (Term.Ref "Eval.call.if")
            (Term.App
              (Quan.Q1)
              (Term.App
                (Quan.Q2)
                (Term.App (Quan.Q2) (Term.Ref "Eval.vals") (Term.Var 1))
                (Term.Var 0))
              (Term.Tup (Quan.Q1) (Term.Lab "True") (Term.Lab "()"))))
          (Term.App
            (Quan.Q2)
            (Term.App (Quan.Q1) (Term.Ref "Eval.callWalk") (Term.Var 1))
            (Term.Var 0)))),
    false⟩

def «evalVersion.Eval.redex.if» : Def :=
  ⟨"Eval.redex.if",
    Term.All
      (Quan.Q1)
      (Term.Ref "Bool")
      (Term.All
        (Quan.Q1)
        (Term.Ref "Term")
        (Term.App
          (Quan.Q0)
          (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
          (Term.Ref "Term"))),
    Term.Prj
      (Term.Mat
        "True"
        (Term.Mat
          "()"
          (Term.Lam
            (Quan.Q1)
            (Term.Tup
              (Quan.Q1)
              (Term.Lab "Some")
              (Term.Tup (Quan.Q1) (Term.Var 0) (Term.Lab "()"))))
          (Term.Efq))
        (Term.Mat
          "False"
          (Term.Mat
            "()"
            (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()")))
            (Term.Efq))
          (Term.Efq))),
    false⟩

def «evalVersion.Eval.redex.pick» : Def :=
  ⟨"Eval.redex.pick",
    Term.All
      (Quan.Q1)
      (Term.Ref "Bool")
      (Term.All
        (Quan.Q1)
        (Term.Ref "Term")
        (Term.All (Quan.Q1) (Term.Ref "Term") (Term.Ref "Term"))),
    Term.Prj
      (Term.Mat
        "True"
        (Term.Mat "()" (Term.Lam (Quan.Q1) (Term.Lam (Quan.Q1) (Term.Var 1))) (Term.Efq))
        (Term.Mat
          "False"
          (Term.Mat "()" (Term.Lam (Quan.Q1) (Term.Lam (Quan.Q1) (Term.Var 0))) (Term.Efq))
          (Term.Efq))),
    false⟩

def «evalVersion.Eval.redex» : Def :=
  ⟨"Eval.redex",
    Term.All
      (Quan.Q1)
      (Term.App (Quan.Q0) (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "Def"))
      (Term.All
        (Quan.Q2)
        (Term.Ref "Quan")
        (Term.All
          (Quan.Q2)
          (Term.Ref "Term")
          (Term.All
            (Quan.Q2)
            (Term.Ref "Term")
            (Term.App
              (Quan.Q0)
              (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
              (Term.Ref "Term"))))),
    Term.Lam
      (Quan.Q2)
      (Term.Lam
        (Quan.Q2)
        (Term.Prj
          (Term.Mat
            "Term.Lam"
            (Term.Prj
              (Term.Lam
                (Quan.Q2)
                (Term.Prj
                  (Term.Lam
                    (Quan.Q2)
                    (Term.Mat
                      "()"
                      (Term.Lam
                        (Quan.Q2)
                        (Term.App
                          (Quan.Q1)
                          (Term.App
                            (Quan.Q1)
                            (Term.Ref "Eval.redex.if")
                            (Term.App
                              (Quan.Q1)
                              (Term.App
                                (Quan.Q1)
                                (Term.App (Quan.Q2) (Term.Ref "Quan.binds") (Term.Var 2))
                                (Term.Var 3))
                              (Term.Var 0)))
                          (Term.App
                            (Quan.Q1)
                            (Term.App (Quan.Q1) (Term.Ref "Term.inst") (Term.Var 1))
                            (Term.Var 0))))
                      (Term.Efq))))))
            (Term.Mat
              "Term.Prj"
              (Term.Prj
                (Term.Lam
                  (Quan.Q2)
                  (Term.Mat
                    "()"
                    (Term.Prj
                      (Term.Mat
                        "Term.Tup"
                        (Term.Prj
                          (Term.Lam
                            (Quan.Q2)
                            (Term.Prj
                              (Term.Lam
                                (Quan.Q2)
                                (Term.Prj
                                  (Term.Lam
                                    (Quan.Q2)
                                    (Term.Mat
                                      "()"
                                      (Term.App
                                        (Quan.Q1)
                                        (Term.App
                                          (Quan.Q1)
                                          (Term.Ref "Eval.redex.if")
                                          (Term.App (Quan.Q1) (Term.Ref "Quan.live") (Term.Var 4)))
                                        (Term.Tup
                                          (Quan.Q1)
                                          (Term.Lab "Term.App")
                                          (Term.Tup
                                            (Quan.Q1)
                                            (Term.Var 4)
                                            (Term.Tup
                                              (Quan.Q1)
                                              (Term.Tup
                                                (Quan.Q1)
                                                (Term.Lab "Term.App")
                                                (Term.Tup
                                                  (Quan.Q1)
                                                  (Term.App
                                                    (Quan.Q1)
                                                    (Term.App
                                                      (Quan.Q1)
                                                      (Term.Ref "Quan.fld")
                                                      (Term.Var 2))
                                                    (Term.Var 4))
                                                  (Term.Tup
                                                    (Quan.Q1)
                                                    (Term.Var 3)
                                                    (Term.Tup
                                                      (Quan.Q1)
                                                      (Term.Var 1)
                                                      (Term.Lab "()")))))
                                              (Term.Tup (Quan.Q1) (Term.Var 0) (Term.Lab "()"))))))
                                      (Term.Efq))))))))
                        (Term.Lam
                          (Quan.Q2)
                          (Term.Lam
                            (Quan.Q2)
                            (Term.App
                              (Quan.Q2)
                              (Term.App (Quan.Q2) (Term.Ref "Eval.call") (Term.Var 4))
                              (Term.Tup
                                (Quan.Q1)
                                (Term.Lab "Term.App")
                                (Term.Tup
                                  (Quan.Q1)
                                  (Term.Var 3)
                                  (Term.Tup
                                    (Quan.Q1)
                                    (Term.Tup
                                      (Quan.Q1)
                                      (Term.Lab "Term.Prj")
                                      (Term.Tup (Quan.Q1) (Term.Var 2) (Term.Lab "()")))
                                    (Term.Tup
                                      (Quan.Q1)
                                      (Term.Tup (Quan.Q1) (Term.Var 1) (Term.Var 0))
                                      (Term.Lab "()"))))))))))
                    (Term.Efq))))
              (Term.Mat
                "Term.Mat"
                (Term.Prj
                  (Term.Lam
                    (Quan.Q2)
                    (Term.Prj
                      (Term.Lam
                        (Quan.Q2)
                        (Term.Prj
                          (Term.Lam
                            (Quan.Q2)
                            (Term.Mat
                              "()"
                              (Term.Prj
                                (Term.Mat
                                  "Term.Lab"
                                  (Term.Prj
                                    (Term.Lam
                                      (Quan.Q2)
                                      (Term.Mat
                                        "()"
                                        (Term.App
                                          (Quan.Q1)
                                          (Term.App
                                            (Quan.Q1)
                                            (Term.Ref "Eval.redex.if")
                                            (Term.App
                                              (Quan.Q1)
                                              (Term.Ref "Quan.live")
                                              (Term.Var 4)))
                                          (Term.App
                                            (Quan.Q1)
                                            (Term.App
                                              (Quan.Q1)
                                              (Term.App
                                                (Quan.Q1)
                                                (Term.Ref "Eval.redex.pick")
                                                (Term.App
                                                  (Quan.Q1)
                                                  (Term.App
                                                    (Quan.Q1)
                                                    (Term.Ref "Name.is_eq")
                                                    (Term.Var 0))
                                                  (Term.Var 3)))
                                              (Term.Var 2))
                                            (Term.Tup
                                              (Quan.Q1)
                                              (Term.Lab "Term.App")
                                              (Term.Tup
                                                (Quan.Q1)
                                                (Term.Var 4)
                                                (Term.Tup
                                                  (Quan.Q1)
                                                  (Term.Var 1)
                                                  (Term.Tup
                                                    (Quan.Q1)
                                                    (Term.Tup
                                                      (Quan.Q1)
                                                      (Term.Lab "Term.Lab")
                                                      (Term.Tup
                                                        (Quan.Q1)
                                                        (Term.Var 0)
                                                        (Term.Lab "()")))
                                                    (Term.Lab "()")))))))
                                        (Term.Efq))))
                                  (Term.Lam
                                    (Quan.Q2)
                                    (Term.Lam
                                      (Quan.Q2)
                                      (Term.App
                                        (Quan.Q2)
                                        (Term.App (Quan.Q2) (Term.Ref "Eval.call") (Term.Var 6))
                                        (Term.Tup
                                          (Quan.Q1)
                                          (Term.Lab "Term.App")
                                          (Term.Tup
                                            (Quan.Q1)
                                            (Term.Var 5)
                                            (Term.Tup
                                              (Quan.Q1)
                                              (Term.Tup
                                                (Quan.Q1)
                                                (Term.Lab "Term.Mat")
                                                (Term.Tup
                                                  (Quan.Q1)
                                                  (Term.Var 4)
                                                  (Term.Tup
                                                    (Quan.Q1)
                                                    (Term.Var 3)
                                                    (Term.Tup
                                                      (Quan.Q1)
                                                      (Term.Var 2)
                                                      (Term.Lab "()")))))
                                              (Term.Tup
                                                (Quan.Q1)
                                                (Term.Tup (Quan.Q1) (Term.Var 1) (Term.Var 0))
                                                (Term.Lab "()"))))))))))
                              (Term.Efq))))))))
                (Term.Lam
                  (Quan.Q2)
                  (Term.Lam
                    (Quan.Q2)
                    (Term.Lam
                      (Quan.Q2)
                      (Term.App
                        (Quan.Q2)
                        (Term.App (Quan.Q2) (Term.Ref "Eval.call") (Term.Var 4))
                        (Term.Tup
                          (Quan.Q1)
                          (Term.Lab "Term.App")
                          (Term.Tup
                            (Quan.Q1)
                            (Term.Var 3)
                            (Term.Tup
                              (Quan.Q1)
                              (Term.Tup (Quan.Q1) (Term.Var 2) (Term.Var 1))
                              (Term.Tup (Quan.Q1) (Term.Var 0) (Term.Lab "()")))))))))))))),
    false⟩

def «evalVersion.Quan.read.if» : Def :=
  ⟨"Quan.read.if",
    Term.All
      (Quan.Q1)
      (Term.Ref "Bool")
      (Term.All
        (Quan.Q1)
        (Term.Ref "Quan")
        (Term.All
          (Quan.Q1)
          (Term.App
            (Quan.Q0)
            (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
            (Term.Ref "Quan"))
          (Term.App
            (Quan.Q0)
            (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
            (Term.Ref "Quan")))),
    Term.Prj
      (Term.Mat
        "True"
        (Term.Mat
          "()"
          (Term.Lam
            (Quan.Q1)
            (Term.Lam
              (Quan.Q1)
              (Term.Tup
                (Quan.Q1)
                (Term.Lab "Some")
                (Term.Tup (Quan.Q1) (Term.Var 1) (Term.Lab "()")))))
          (Term.Efq))
        (Term.Mat
          "False"
          (Term.Mat "()" (Term.Lam (Quan.Q1) (Term.Lam (Quan.Q1) (Term.Var 0))) (Term.Efq))
          (Term.Efq))),
    false⟩

def «evalVersion.U32.lit81» : Def :=
  ⟨"U32.lit81",
    Term.Ref "U32",
    Term.Tup
      (Quan.Q1)
      (Term.Lab "U32")
      (Term.Tup
        (Quan.Q1)
        (Term.Tup
          (Quan.Q1)
          (Term.Lab "WCon")
          (Term.Tup
            (Quan.Q1)
            (Term.Tup (Quan.Q1) (Term.Lab "True") (Term.Lab "()"))
            (Term.Tup
              (Quan.Q1)
              (Term.Tup
                (Quan.Q1)
                (Term.Lab "WCon")
                (Term.Tup
                  (Quan.Q1)
                  (Term.Tup (Quan.Q1) (Term.Lab "False") (Term.Lab "()"))
                  (Term.Tup
                    (Quan.Q1)
                    (Term.Tup
                      (Quan.Q1)
                      (Term.Lab "WCon")
                      (Term.Tup
                        (Quan.Q1)
                        (Term.Tup (Quan.Q1) (Term.Lab "False") (Term.Lab "()"))
                        (Term.Tup
                          (Quan.Q1)
                          (Term.Tup
                            (Quan.Q1)
                            (Term.Lab "WCon")
                            (Term.Tup
                              (Quan.Q1)
                              (Term.Tup (Quan.Q1) (Term.Lab "False") (Term.Lab "()"))
                              (Term.Tup
                                (Quan.Q1)
                                (Term.Tup
                                  (Quan.Q1)
                                  (Term.Lab "WCon")
                                  (Term.Tup
                                    (Quan.Q1)
                                    (Term.Tup (Quan.Q1) (Term.Lab "True") (Term.Lab "()"))
                                    (Term.Tup
                                      (Quan.Q1)
                                      (Term.Tup
                                        (Quan.Q1)
                                        (Term.Lab "WCon")
                                        (Term.Tup
                                          (Quan.Q1)
                                          (Term.Tup (Quan.Q1) (Term.Lab "False") (Term.Lab "()"))
                                          (Term.Tup
                                            (Quan.Q1)
                                            (Term.Tup
                                              (Quan.Q1)
                                              (Term.Lab "WCon")
                                              (Term.Tup
                                                (Quan.Q1)
                                                (Term.Tup
                                                  (Quan.Q1)
                                                  (Term.Lab "True")
                                                  (Term.Lab "()"))
                                                (Term.Tup
                                                  (Quan.Q1)
                                                  (Term.Tup
                                                    (Quan.Q1)
                                                    (Term.Lab "WCon")
                                                    (Term.Tup
                                                      (Quan.Q1)
                                                      (Term.Tup
                                                        (Quan.Q1)
                                                        (Term.Lab "False")
                                                        (Term.Lab "()"))
                                                      (Term.Tup
                                                        (Quan.Q1)
                                                        (Term.Tup
                                                          (Quan.Q1)
                                                          (Term.Lab "WCon")
                                                          (Term.Tup
                                                            (Quan.Q1)
                                                            (Term.Tup
                                                              (Quan.Q1)
                                                              (Term.Lab "False")
                                                              (Term.Lab "()"))
                                                            (Term.Tup
                                                              (Quan.Q1)
                                                              (Term.Tup
                                                                (Quan.Q1)
                                                                (Term.Lab "WCon")
                                                                (Term.Tup
                                                                  (Quan.Q1)
                                                                  (Term.Tup
                                                                    (Quan.Q1)
                                                                    (Term.Lab "False")
                                                                    (Term.Lab "()"))
                                                                  (Term.Tup
                                                                    (Quan.Q1)
                                                                    (Term.Tup
                                                                      (Quan.Q1)
                                                                      (Term.Lab "WCon")
                                                                      (Term.Tup
                                                                        (Quan.Q1)
                                                                        (Term.Tup
                                                                          (Quan.Q1)
                                                                          (Term.Lab "False")
                                                                          (Term.Lab "()"))
                                                                        (Term.Tup
                                                                          (Quan.Q1)
                                                                          (Term.Tup
                                                                            (Quan.Q1)
                                                                            (Term.Lab "WCon")
                                                                            (Term.Tup
                                                                              (Quan.Q1)
                                                                              (Term.Tup
                                                                                (Quan.Q1)
                                                                                (Term.Lab "False")
                                                                                (Term.Lab "()"))
                                                                              (Term.Tup
                                                                                (Quan.Q1)
                                                                                (Term.Tup
                                                                                  (Quan.Q1)
                                                                                  (Term.Lab "WCon")
                                                                                  (Term.Tup
                                                                                    (Quan.Q1)
                                                                                    (Term.Tup
                                                                                      (Quan.Q1)
                                                                                      (Term.Lab
                                                                                        "False")
                                                                                      (Term.Lab
                                                                                        "()"))
                                                                                    (Term.Tup
                                                                                      (Quan.Q1)
                                                                                      (Term.Tup
                                                                                        (Quan.Q1)
                                                                                        (Term.Lab
                                                                                          "WCon")
                                                                                        (Term.Tup
                                                                                          (Quan.Q1)
                                                                                          (Term.Tup
                                                                                            (Quan.Q1)
                                                                                            (Term.Lab
                                                                                              "False")
                                                                                            (Term.Lab
                                                                                              "()"))
                                                                                          (Term.Tup
                                                                                            (Quan.Q1)
                                                                                            (Term.Tup
                                                                                              (Quan.Q1)
                                                                                              (Term.Lab
                                                                                                "WCon")
                                                                                              (Term.Tup
                                                                                                (Quan.Q1)
                                                                                                (Term.Tup
                                                                                                  (Quan.Q1)
                                                                                                  (Term.Lab
                                                                                                    "False")
                                                                                                  (Term.Lab
                                                                                                    "()"))
                                                                                                (Term.Tup
                                                                                                  (Quan.Q1)
                                                                                                  (Term.Tup
                                                                                                    (Quan.Q1)
                                                                                                    (Term.Lab
                                                                                                      "WCon")
                                                                                                    (Term.Tup
                                                                                                      (Quan.Q1)
                                                                                                      (Term.Tup
                                                                                                        (Quan.Q1)
                                                                                                        (Term.Lab
                                                                                                          "False")
                                                                                                        (Term.Lab
                                                                                                          "()"))
                                                                                                      (Term.Tup
                                                                                                        (Quan.Q1)
                                                                                                        (Term.Tup
                                                                                                          (Quan.Q1)
                                                                                                          (Term.Lab
                                                                                                            "WCon")
                                                                                                          (Term.Tup
                                                                                                            (Quan.Q1)
                                                                                                            (Term.Tup
                                                                                                              (Quan.Q1)
                                                                                                              (Term.Lab
                                                                                                                "False")
                                                                                                              (Term.Lab
                                                                                                                "()"))
                                                                                                            (Term.Tup
                                                                                                              (Quan.Q1)
                                                                                                              (Term.Tup
                                                                                                                (Quan.Q1)
                                                                                                                (Term.Lab
                                                                                                                  "WCon")
                                                                                                                (Term.Tup
                                                                                                                  (Quan.Q1)
                                                                                                                  (Term.Tup
                                                                                                                    (Quan.Q1)
                                                                                                                    (Term.Lab
                                                                                                                      "False")
                                                                                                                    (Term.Lab
                                                                                                                      "()"))
                                                                                                                  (Term.Tup
                                                                                                                    (Quan.Q1)
                                                                                                                    (Term.Tup
                                                                                                                      (Quan.Q1)
                                                                                                                      (Term.Lab
                                                                                                                        "WCon")
                                                                                                                      (Term.Tup
                                                                                                                        (Quan.Q1)
                                                                                                                        (Term.Tup
                                                                                                                          (Quan.Q1)
                                                                                                                          (Term.Lab
                                                                                                                            "False")
                                                                                                                          (Term.Lab
                                                                                                                            "()"))
                                                                                                                        (Term.Tup
                                                                                                                          (Quan.Q1)
                                                                                                                          (Term.Tup
                                                                                                                            (Quan.Q1)
                                                                                                                            (Term.Lab
                                                                                                                              "WCon")
                                                                                                                            (Term.Tup
                                                                                                                              (Quan.Q1)
                                                                                                                              (Term.Tup
                                                                                                                                (Quan.Q1)
                                                                                                                                (Term.Lab
                                                                                                                                  "False")
                                                                                                                                (Term.Lab
                                                                                                                                  "()"))
                                                                                                                              (Term.Tup
                                                                                                                                (Quan.Q1)
                                                                                                                                (Term.Tup
                                                                                                                                  (Quan.Q1)
                                                                                                                                  (Term.Lab
                                                                                                                                    "WCon")
                                                                                                                                  (Term.Tup
                                                                                                                                    (Quan.Q1)
                                                                                                                                    (Term.Tup
                                                                                                                                      (Quan.Q1)
                                                                                                                                      (Term.Lab
                                                                                                                                        "False")
                                                                                                                                      (Term.Lab
                                                                                                                                        "()"))
                                                                                                                                    (Term.Tup
                                                                                                                                      (Quan.Q1)
                                                                                                                                      (Term.Tup
                                                                                                                                        (Quan.Q1)
                                                                                                                                        (Term.Lab
                                                                                                                                          "WCon")
                                                                                                                                        (Term.Tup
                                                                                                                                          (Quan.Q1)
                                                                                                                                          (Term.Tup
                                                                                                                                            (Quan.Q1)
                                                                                                                                            (Term.Lab
                                                                                                                                              "False")
                                                                                                                                            (Term.Lab
                                                                                                                                              "()"))
                                                                                                                                          (Term.Tup
                                                                                                                                            (Quan.Q1)
                                                                                                                                            (Term.Tup
                                                                                                                                              (Quan.Q1)
                                                                                                                                              (Term.Lab
                                                                                                                                                "WCon")
                                                                                                                                              (Term.Tup
                                                                                                                                                (Quan.Q1)
                                                                                                                                                (Term.Tup
                                                                                                                                                  (Quan.Q1)
                                                                                                                                                  (Term.Lab
                                                                                                                                                    "False")
                                                                                                                                                  (Term.Lab
                                                                                                                                                    "()"))
                                                                                                                                                (Term.Tup
                                                                                                                                                  (Quan.Q1)
                                                                                                                                                  (Term.Tup
                                                                                                                                                    (Quan.Q1)
                                                                                                                                                    (Term.Lab
                                                                                                                                                      "WCon")
                                                                                                                                                    (Term.Tup
                                                                                                                                                      (Quan.Q1)
                                                                                                                                                      (Term.Tup
                                                                                                                                                        (Quan.Q1)
                                                                                                                                                        (Term.Lab
                                                                                                                                                          "False")
                                                                                                                                                        (Term.Lab
                                                                                                                                                          "()"))
                                                                                                                                                      (Term.Tup
                                                                                                                                                        (Quan.Q1)
                                                                                                                                                        (Term.Tup
                                                                                                                                                          (Quan.Q1)
                                                                                                                                                          (Term.Lab
                                                                                                                                                            "WCon")
                                                                                                                                                          (Term.Tup
                                                                                                                                                            (Quan.Q1)
                                                                                                                                                            (Term.Tup
                                                                                                                                                              (Quan.Q1)
                                                                                                                                                              (Term.Lab
                                                                                                                                                                "False")
                                                                                                                                                              (Term.Lab
                                                                                                                                                                "()"))
                                                                                                                                                            (Term.Tup
                                                                                                                                                              (Quan.Q1)
                                                                                                                                                              (Term.Tup
                                                                                                                                                                (Quan.Q1)
                                                                                                                                                                (Term.Lab
                                                                                                                                                                  "WCon")
                                                                                                                                                                (Term.Tup
                                                                                                                                                                  (Quan.Q1)
                                                                                                                                                                  (Term.Tup
                                                                                                                                                                    (Quan.Q1)
                                                                                                                                                                    (Term.Lab
                                                                                                                                                                      "False")
                                                                                                                                                                    (Term.Lab
                                                                                                                                                                      "()"))
                                                                                                                                                                  (Term.Tup
                                                                                                                                                                    (Quan.Q1)
                                                                                                                                                                    (Term.Tup
                                                                                                                                                                      (Quan.Q1)
                                                                                                                                                                      (Term.Lab
                                                                                                                                                                        "WCon")
                                                                                                                                                                      (Term.Tup
                                                                                                                                                                        (Quan.Q1)
                                                                                                                                                                        (Term.Tup
                                                                                                                                                                          (Quan.Q1)
                                                                                                                                                                          (Term.Lab
                                                                                                                                                                            "False")
                                                                                                                                                                          (Term.Lab
                                                                                                                                                                            "()"))
                                                                                                                                                                        (Term.Tup
                                                                                                                                                                          (Quan.Q1)
                                                                                                                                                                          (Term.Tup
                                                                                                                                                                            (Quan.Q1)
                                                                                                                                                                            (Term.Lab
                                                                                                                                                                              "WCon")
                                                                                                                                                                            (Term.Tup
                                                                                                                                                                              (Quan.Q1)
                                                                                                                                                                              (Term.Tup
                                                                                                                                                                                (Quan.Q1)
                                                                                                                                                                                (Term.Lab
                                                                                                                                                                                  "False")
                                                                                                                                                                                (Term.Lab
                                                                                                                                                                                  "()"))
                                                                                                                                                                              (Term.Tup
                                                                                                                                                                                (Quan.Q1)
                                                                                                                                                                                (Term.Tup
                                                                                                                                                                                  (Quan.Q1)
                                                                                                                                                                                  (Term.Lab
                                                                                                                                                                                    "WCon")
                                                                                                                                                                                  (Term.Tup
                                                                                                                                                                                    (Quan.Q1)
                                                                                                                                                                                    (Term.Tup
                                                                                                                                                                                      (Quan.Q1)
                                                                                                                                                                                      (Term.Lab
                                                                                                                                                                                        "False")
                                                                                                                                                                                      (Term.Lab
                                                                                                                                                                                        "()"))
                                                                                                                                                                                    (Term.Tup
                                                                                                                                                                                      (Quan.Q1)
                                                                                                                                                                                      (Term.Tup
                                                                                                                                                                                        (Quan.Q1)
                                                                                                                                                                                        (Term.Lab
                                                                                                                                                                                          "WCon")
                                                                                                                                                                                        (Term.Tup
                                                                                                                                                                                          (Quan.Q1)
                                                                                                                                                                                          (Term.Tup
                                                                                                                                                                                            (Quan.Q1)
                                                                                                                                                                                            (Term.Lab
                                                                                                                                                                                              "False")
                                                                                                                                                                                            (Term.Lab
                                                                                                                                                                                              "()"))
                                                                                                                                                                                          (Term.Tup
                                                                                                                                                                                            (Quan.Q1)
                                                                                                                                                                                            (Term.Tup
                                                                                                                                                                                              (Quan.Q1)
                                                                                                                                                                                              (Term.Lab
                                                                                                                                                                                                "WCon")
                                                                                                                                                                                              (Term.Tup
                                                                                                                                                                                                (Quan.Q1)
                                                                                                                                                                                                (Term.Tup
                                                                                                                                                                                                  (Quan.Q1)
                                                                                                                                                                                                  (Term.Lab
                                                                                                                                                                                                    "False")
                                                                                                                                                                                                  (Term.Lab
                                                                                                                                                                                                    "()"))
                                                                                                                                                                                                (Term.Tup
                                                                                                                                                                                                  (Quan.Q1)
                                                                                                                                                                                                  (Term.Tup
                                                                                                                                                                                                    (Quan.Q1)
                                                                                                                                                                                                    (Term.Lab
                                                                                                                                                                                                      "WCon")
                                                                                                                                                                                                    (Term.Tup
                                                                                                                                                                                                      (Quan.Q1)
                                                                                                                                                                                                      (Term.Tup
                                                                                                                                                                                                        (Quan.Q1)
                                                                                                                                                                                                        (Term.Lab
                                                                                                                                                                                                          "False")
                                                                                                                                                                                                        (Term.Lab
                                                                                                                                                                                                          "()"))
                                                                                                                                                                                                      (Term.Tup
                                                                                                                                                                                                        (Quan.Q1)
                                                                                                                                                                                                        (Term.Tup
                                                                                                                                                                                                          (Quan.Q1)
                                                                                                                                                                                                          (Term.Lab
                                                                                                                                                                                                            "WNil")
                                                                                                                                                                                                          (Term.Lab
                                                                                                                                                                                                            "()"))
                                                                                                                                                                                                        (Term.Lab
                                                                                                                                                                                                          "()"))))
                                                                                                                                                                                                  (Term.Lab
                                                                                                                                                                                                    "()"))))
                                                                                                                                                                                            (Term.Lab
                                                                                                                                                                                              "()"))))
                                                                                                                                                                                      (Term.Lab
                                                                                                                                                                                        "()"))))
                                                                                                                                                                                (Term.Lab
                                                                                                                                                                                  "()"))))
                                                                                                                                                                          (Term.Lab
                                                                                                                                                                            "()"))))
                                                                                                                                                                    (Term.Lab
                                                                                                                                                                      "()"))))
                                                                                                                                                              (Term.Lab
                                                                                                                                                                "()"))))
                                                                                                                                                        (Term.Lab
                                                                                                                                                          "()"))))
                                                                                                                                                  (Term.Lab
                                                                                                                                                    "()"))))
                                                                                                                                            (Term.Lab
                                                                                                                                              "()"))))
                                                                                                                                      (Term.Lab
                                                                                                                                        "()"))))
                                                                                                                                (Term.Lab
                                                                                                                                  "()"))))
                                                                                                                          (Term.Lab
                                                                                                                            "()"))))
                                                                                                                    (Term.Lab
                                                                                                                      "()"))))
                                                                                                              (Term.Lab
                                                                                                                "()"))))
                                                                                                        (Term.Lab
                                                                                                          "()"))))
                                                                                                  (Term.Lab
                                                                                                    "()"))))
                                                                                            (Term.Lab
                                                                                              "()"))))
                                                                                      (Term.Lab
                                                                                        "()"))))
                                                                                (Term.Lab "()"))))
                                                                          (Term.Lab "()"))))
                                                                    (Term.Lab "()"))))
                                                              (Term.Lab "()"))))
                                                        (Term.Lab "()"))))
                                                  (Term.Lab "()"))))
                                            (Term.Lab "()"))))
                                      (Term.Lab "()"))))
                                (Term.Lab "()"))))
                          (Term.Lab "()"))))
                    (Term.Lab "()"))))
              (Term.Lab "()"))))
        (Term.Lab "()")),
    false⟩

def «evalVersion.U32.lit48» : Def :=
  ⟨"U32.lit48",
    Term.Ref "U32",
    Term.Tup
      (Quan.Q1)
      (Term.Lab "U32")
      (Term.Tup
        (Quan.Q1)
        (Term.Tup
          (Quan.Q1)
          (Term.Lab "WCon")
          (Term.Tup
            (Quan.Q1)
            (Term.Tup (Quan.Q1) (Term.Lab "False") (Term.Lab "()"))
            (Term.Tup
              (Quan.Q1)
              (Term.Tup
                (Quan.Q1)
                (Term.Lab "WCon")
                (Term.Tup
                  (Quan.Q1)
                  (Term.Tup (Quan.Q1) (Term.Lab "False") (Term.Lab "()"))
                  (Term.Tup
                    (Quan.Q1)
                    (Term.Tup
                      (Quan.Q1)
                      (Term.Lab "WCon")
                      (Term.Tup
                        (Quan.Q1)
                        (Term.Tup (Quan.Q1) (Term.Lab "False") (Term.Lab "()"))
                        (Term.Tup
                          (Quan.Q1)
                          (Term.Tup
                            (Quan.Q1)
                            (Term.Lab "WCon")
                            (Term.Tup
                              (Quan.Q1)
                              (Term.Tup (Quan.Q1) (Term.Lab "False") (Term.Lab "()"))
                              (Term.Tup
                                (Quan.Q1)
                                (Term.Tup
                                  (Quan.Q1)
                                  (Term.Lab "WCon")
                                  (Term.Tup
                                    (Quan.Q1)
                                    (Term.Tup (Quan.Q1) (Term.Lab "True") (Term.Lab "()"))
                                    (Term.Tup
                                      (Quan.Q1)
                                      (Term.Tup
                                        (Quan.Q1)
                                        (Term.Lab "WCon")
                                        (Term.Tup
                                          (Quan.Q1)
                                          (Term.Tup (Quan.Q1) (Term.Lab "True") (Term.Lab "()"))
                                          (Term.Tup
                                            (Quan.Q1)
                                            (Term.Tup
                                              (Quan.Q1)
                                              (Term.Lab "WCon")
                                              (Term.Tup
                                                (Quan.Q1)
                                                (Term.Tup
                                                  (Quan.Q1)
                                                  (Term.Lab "False")
                                                  (Term.Lab "()"))
                                                (Term.Tup
                                                  (Quan.Q1)
                                                  (Term.Tup
                                                    (Quan.Q1)
                                                    (Term.Lab "WCon")
                                                    (Term.Tup
                                                      (Quan.Q1)
                                                      (Term.Tup
                                                        (Quan.Q1)
                                                        (Term.Lab "False")
                                                        (Term.Lab "()"))
                                                      (Term.Tup
                                                        (Quan.Q1)
                                                        (Term.Tup
                                                          (Quan.Q1)
                                                          (Term.Lab "WCon")
                                                          (Term.Tup
                                                            (Quan.Q1)
                                                            (Term.Tup
                                                              (Quan.Q1)
                                                              (Term.Lab "False")
                                                              (Term.Lab "()"))
                                                            (Term.Tup
                                                              (Quan.Q1)
                                                              (Term.Tup
                                                                (Quan.Q1)
                                                                (Term.Lab "WCon")
                                                                (Term.Tup
                                                                  (Quan.Q1)
                                                                  (Term.Tup
                                                                    (Quan.Q1)
                                                                    (Term.Lab "False")
                                                                    (Term.Lab "()"))
                                                                  (Term.Tup
                                                                    (Quan.Q1)
                                                                    (Term.Tup
                                                                      (Quan.Q1)
                                                                      (Term.Lab "WCon")
                                                                      (Term.Tup
                                                                        (Quan.Q1)
                                                                        (Term.Tup
                                                                          (Quan.Q1)
                                                                          (Term.Lab "False")
                                                                          (Term.Lab "()"))
                                                                        (Term.Tup
                                                                          (Quan.Q1)
                                                                          (Term.Tup
                                                                            (Quan.Q1)
                                                                            (Term.Lab "WCon")
                                                                            (Term.Tup
                                                                              (Quan.Q1)
                                                                              (Term.Tup
                                                                                (Quan.Q1)
                                                                                (Term.Lab "False")
                                                                                (Term.Lab "()"))
                                                                              (Term.Tup
                                                                                (Quan.Q1)
                                                                                (Term.Tup
                                                                                  (Quan.Q1)
                                                                                  (Term.Lab "WCon")
                                                                                  (Term.Tup
                                                                                    (Quan.Q1)
                                                                                    (Term.Tup
                                                                                      (Quan.Q1)
                                                                                      (Term.Lab
                                                                                        "False")
                                                                                      (Term.Lab
                                                                                        "()"))
                                                                                    (Term.Tup
                                                                                      (Quan.Q1)
                                                                                      (Term.Tup
                                                                                        (Quan.Q1)
                                                                                        (Term.Lab
                                                                                          "WCon")
                                                                                        (Term.Tup
                                                                                          (Quan.Q1)
                                                                                          (Term.Tup
                                                                                            (Quan.Q1)
                                                                                            (Term.Lab
                                                                                              "False")
                                                                                            (Term.Lab
                                                                                              "()"))
                                                                                          (Term.Tup
                                                                                            (Quan.Q1)
                                                                                            (Term.Tup
                                                                                              (Quan.Q1)
                                                                                              (Term.Lab
                                                                                                "WCon")
                                                                                              (Term.Tup
                                                                                                (Quan.Q1)
                                                                                                (Term.Tup
                                                                                                  (Quan.Q1)
                                                                                                  (Term.Lab
                                                                                                    "False")
                                                                                                  (Term.Lab
                                                                                                    "()"))
                                                                                                (Term.Tup
                                                                                                  (Quan.Q1)
                                                                                                  (Term.Tup
                                                                                                    (Quan.Q1)
                                                                                                    (Term.Lab
                                                                                                      "WCon")
                                                                                                    (Term.Tup
                                                                                                      (Quan.Q1)
                                                                                                      (Term.Tup
                                                                                                        (Quan.Q1)
                                                                                                        (Term.Lab
                                                                                                          "False")
                                                                                                        (Term.Lab
                                                                                                          "()"))
                                                                                                      (Term.Tup
                                                                                                        (Quan.Q1)
                                                                                                        (Term.Tup
                                                                                                          (Quan.Q1)
                                                                                                          (Term.Lab
                                                                                                            "WCon")
                                                                                                          (Term.Tup
                                                                                                            (Quan.Q1)
                                                                                                            (Term.Tup
                                                                                                              (Quan.Q1)
                                                                                                              (Term.Lab
                                                                                                                "False")
                                                                                                              (Term.Lab
                                                                                                                "()"))
                                                                                                            (Term.Tup
                                                                                                              (Quan.Q1)
                                                                                                              (Term.Tup
                                                                                                                (Quan.Q1)
                                                                                                                (Term.Lab
                                                                                                                  "WCon")
                                                                                                                (Term.Tup
                                                                                                                  (Quan.Q1)
                                                                                                                  (Term.Tup
                                                                                                                    (Quan.Q1)
                                                                                                                    (Term.Lab
                                                                                                                      "False")
                                                                                                                    (Term.Lab
                                                                                                                      "()"))
                                                                                                                  (Term.Tup
                                                                                                                    (Quan.Q1)
                                                                                                                    (Term.Tup
                                                                                                                      (Quan.Q1)
                                                                                                                      (Term.Lab
                                                                                                                        "WCon")
                                                                                                                      (Term.Tup
                                                                                                                        (Quan.Q1)
                                                                                                                        (Term.Tup
                                                                                                                          (Quan.Q1)
                                                                                                                          (Term.Lab
                                                                                                                            "False")
                                                                                                                          (Term.Lab
                                                                                                                            "()"))
                                                                                                                        (Term.Tup
                                                                                                                          (Quan.Q1)
                                                                                                                          (Term.Tup
                                                                                                                            (Quan.Q1)
                                                                                                                            (Term.Lab
                                                                                                                              "WCon")
                                                                                                                            (Term.Tup
                                                                                                                              (Quan.Q1)
                                                                                                                              (Term.Tup
                                                                                                                                (Quan.Q1)
                                                                                                                                (Term.Lab
                                                                                                                                  "False")
                                                                                                                                (Term.Lab
                                                                                                                                  "()"))
                                                                                                                              (Term.Tup
                                                                                                                                (Quan.Q1)
                                                                                                                                (Term.Tup
                                                                                                                                  (Quan.Q1)
                                                                                                                                  (Term.Lab
                                                                                                                                    "WCon")
                                                                                                                                  (Term.Tup
                                                                                                                                    (Quan.Q1)
                                                                                                                                    (Term.Tup
                                                                                                                                      (Quan.Q1)
                                                                                                                                      (Term.Lab
                                                                                                                                        "False")
                                                                                                                                      (Term.Lab
                                                                                                                                        "()"))
                                                                                                                                    (Term.Tup
                                                                                                                                      (Quan.Q1)
                                                                                                                                      (Term.Tup
                                                                                                                                        (Quan.Q1)
                                                                                                                                        (Term.Lab
                                                                                                                                          "WCon")
                                                                                                                                        (Term.Tup
                                                                                                                                          (Quan.Q1)
                                                                                                                                          (Term.Tup
                                                                                                                                            (Quan.Q1)
                                                                                                                                            (Term.Lab
                                                                                                                                              "False")
                                                                                                                                            (Term.Lab
                                                                                                                                              "()"))
                                                                                                                                          (Term.Tup
                                                                                                                                            (Quan.Q1)
                                                                                                                                            (Term.Tup
                                                                                                                                              (Quan.Q1)
                                                                                                                                              (Term.Lab
                                                                                                                                                "WCon")
                                                                                                                                              (Term.Tup
                                                                                                                                                (Quan.Q1)
                                                                                                                                                (Term.Tup
                                                                                                                                                  (Quan.Q1)
                                                                                                                                                  (Term.Lab
                                                                                                                                                    "False")
                                                                                                                                                  (Term.Lab
                                                                                                                                                    "()"))
                                                                                                                                                (Term.Tup
                                                                                                                                                  (Quan.Q1)
                                                                                                                                                  (Term.Tup
                                                                                                                                                    (Quan.Q1)
                                                                                                                                                    (Term.Lab
                                                                                                                                                      "WCon")
                                                                                                                                                    (Term.Tup
                                                                                                                                                      (Quan.Q1)
                                                                                                                                                      (Term.Tup
                                                                                                                                                        (Quan.Q1)
                                                                                                                                                        (Term.Lab
                                                                                                                                                          "False")
                                                                                                                                                        (Term.Lab
                                                                                                                                                          "()"))
                                                                                                                                                      (Term.Tup
                                                                                                                                                        (Quan.Q1)
                                                                                                                                                        (Term.Tup
                                                                                                                                                          (Quan.Q1)
                                                                                                                                                          (Term.Lab
                                                                                                                                                            "WCon")
                                                                                                                                                          (Term.Tup
                                                                                                                                                            (Quan.Q1)
                                                                                                                                                            (Term.Tup
                                                                                                                                                              (Quan.Q1)
                                                                                                                                                              (Term.Lab
                                                                                                                                                                "False")
                                                                                                                                                              (Term.Lab
                                                                                                                                                                "()"))
                                                                                                                                                            (Term.Tup
                                                                                                                                                              (Quan.Q1)
                                                                                                                                                              (Term.Tup
                                                                                                                                                                (Quan.Q1)
                                                                                                                                                                (Term.Lab
                                                                                                                                                                  "WCon")
                                                                                                                                                                (Term.Tup
                                                                                                                                                                  (Quan.Q1)
                                                                                                                                                                  (Term.Tup
                                                                                                                                                                    (Quan.Q1)
                                                                                                                                                                    (Term.Lab
                                                                                                                                                                      "False")
                                                                                                                                                                    (Term.Lab
                                                                                                                                                                      "()"))
                                                                                                                                                                  (Term.Tup
                                                                                                                                                                    (Quan.Q1)
                                                                                                                                                                    (Term.Tup
                                                                                                                                                                      (Quan.Q1)
                                                                                                                                                                      (Term.Lab
                                                                                                                                                                        "WCon")
                                                                                                                                                                      (Term.Tup
                                                                                                                                                                        (Quan.Q1)
                                                                                                                                                                        (Term.Tup
                                                                                                                                                                          (Quan.Q1)
                                                                                                                                                                          (Term.Lab
                                                                                                                                                                            "False")
                                                                                                                                                                          (Term.Lab
                                                                                                                                                                            "()"))
                                                                                                                                                                        (Term.Tup
                                                                                                                                                                          (Quan.Q1)
                                                                                                                                                                          (Term.Tup
                                                                                                                                                                            (Quan.Q1)
                                                                                                                                                                            (Term.Lab
                                                                                                                                                                              "WCon")
                                                                                                                                                                            (Term.Tup
                                                                                                                                                                              (Quan.Q1)
                                                                                                                                                                              (Term.Tup
                                                                                                                                                                                (Quan.Q1)
                                                                                                                                                                                (Term.Lab
                                                                                                                                                                                  "False")
                                                                                                                                                                                (Term.Lab
                                                                                                                                                                                  "()"))
                                                                                                                                                                              (Term.Tup
                                                                                                                                                                                (Quan.Q1)
                                                                                                                                                                                (Term.Tup
                                                                                                                                                                                  (Quan.Q1)
                                                                                                                                                                                  (Term.Lab
                                                                                                                                                                                    "WCon")
                                                                                                                                                                                  (Term.Tup
                                                                                                                                                                                    (Quan.Q1)
                                                                                                                                                                                    (Term.Tup
                                                                                                                                                                                      (Quan.Q1)
                                                                                                                                                                                      (Term.Lab
                                                                                                                                                                                        "False")
                                                                                                                                                                                      (Term.Lab
                                                                                                                                                                                        "()"))
                                                                                                                                                                                    (Term.Tup
                                                                                                                                                                                      (Quan.Q1)
                                                                                                                                                                                      (Term.Tup
                                                                                                                                                                                        (Quan.Q1)
                                                                                                                                                                                        (Term.Lab
                                                                                                                                                                                          "WCon")
                                                                                                                                                                                        (Term.Tup
                                                                                                                                                                                          (Quan.Q1)
                                                                                                                                                                                          (Term.Tup
                                                                                                                                                                                            (Quan.Q1)
                                                                                                                                                                                            (Term.Lab
                                                                                                                                                                                              "False")
                                                                                                                                                                                            (Term.Lab
                                                                                                                                                                                              "()"))
                                                                                                                                                                                          (Term.Tup
                                                                                                                                                                                            (Quan.Q1)
                                                                                                                                                                                            (Term.Tup
                                                                                                                                                                                              (Quan.Q1)
                                                                                                                                                                                              (Term.Lab
                                                                                                                                                                                                "WCon")
                                                                                                                                                                                              (Term.Tup
                                                                                                                                                                                                (Quan.Q1)
                                                                                                                                                                                                (Term.Tup
                                                                                                                                                                                                  (Quan.Q1)
                                                                                                                                                                                                  (Term.Lab
                                                                                                                                                                                                    "False")
                                                                                                                                                                                                  (Term.Lab
                                                                                                                                                                                                    "()"))
                                                                                                                                                                                                (Term.Tup
                                                                                                                                                                                                  (Quan.Q1)
                                                                                                                                                                                                  (Term.Tup
                                                                                                                                                                                                    (Quan.Q1)
                                                                                                                                                                                                    (Term.Lab
                                                                                                                                                                                                      "WCon")
                                                                                                                                                                                                    (Term.Tup
                                                                                                                                                                                                      (Quan.Q1)
                                                                                                                                                                                                      (Term.Tup
                                                                                                                                                                                                        (Quan.Q1)
                                                                                                                                                                                                        (Term.Lab
                                                                                                                                                                                                          "False")
                                                                                                                                                                                                        (Term.Lab
                                                                                                                                                                                                          "()"))
                                                                                                                                                                                                      (Term.Tup
                                                                                                                                                                                                        (Quan.Q1)
                                                                                                                                                                                                        (Term.Tup
                                                                                                                                                                                                          (Quan.Q1)
                                                                                                                                                                                                          (Term.Lab
                                                                                                                                                                                                            "WNil")
                                                                                                                                                                                                          (Term.Lab
                                                                                                                                                                                                            "()"))
                                                                                                                                                                                                        (Term.Lab
                                                                                                                                                                                                          "()"))))
                                                                                                                                                                                                  (Term.Lab
                                                                                                                                                                                                    "()"))))
                                                                                                                                                                                            (Term.Lab
                                                                                                                                                                                              "()"))))
                                                                                                                                                                                      (Term.Lab
                                                                                                                                                                                        "()"))))
                                                                                                                                                                                (Term.Lab
                                                                                                                                                                                  "()"))))
                                                                                                                                                                          (Term.Lab
                                                                                                                                                                            "()"))))
                                                                                                                                                                    (Term.Lab
                                                                                                                                                                      "()"))))
                                                                                                                                                              (Term.Lab
                                                                                                                                                                "()"))))
                                                                                                                                                        (Term.Lab
                                                                                                                                                          "()"))))
                                                                                                                                                  (Term.Lab
                                                                                                                                                    "()"))))
                                                                                                                                            (Term.Lab
                                                                                                                                              "()"))))
                                                                                                                                      (Term.Lab
                                                                                                                                        "()"))))
                                                                                                                                (Term.Lab
                                                                                                                                  "()"))))
                                                                                                                          (Term.Lab
                                                                                                                            "()"))))
                                                                                                                    (Term.Lab
                                                                                                                      "()"))))
                                                                                                              (Term.Lab
                                                                                                                "()"))))
                                                                                                        (Term.Lab
                                                                                                          "()"))))
                                                                                                  (Term.Lab
                                                                                                    "()"))))
                                                                                            (Term.Lab
                                                                                              "()"))))
                                                                                      (Term.Lab
                                                                                        "()"))))
                                                                                (Term.Lab "()"))))
                                                                          (Term.Lab "()"))))
                                                                    (Term.Lab "()"))))
                                                              (Term.Lab "()"))))
                                                        (Term.Lab "()"))))
                                                  (Term.Lab "()"))))
                                            (Term.Lab "()"))))
                                      (Term.Lab "()"))))
                                (Term.Lab "()"))))
                          (Term.Lab "()"))))
                    (Term.Lab "()"))))
              (Term.Lab "()"))))
        (Term.Lab "()")),
    false⟩

def «evalVersion.U32.lit49» : Def :=
  ⟨"U32.lit49",
    Term.Ref "U32",
    Term.Tup
      (Quan.Q1)
      (Term.Lab "U32")
      (Term.Tup
        (Quan.Q1)
        (Term.Tup
          (Quan.Q1)
          (Term.Lab "WCon")
          (Term.Tup
            (Quan.Q1)
            (Term.Tup (Quan.Q1) (Term.Lab "True") (Term.Lab "()"))
            (Term.Tup
              (Quan.Q1)
              (Term.Tup
                (Quan.Q1)
                (Term.Lab "WCon")
                (Term.Tup
                  (Quan.Q1)
                  (Term.Tup (Quan.Q1) (Term.Lab "False") (Term.Lab "()"))
                  (Term.Tup
                    (Quan.Q1)
                    (Term.Tup
                      (Quan.Q1)
                      (Term.Lab "WCon")
                      (Term.Tup
                        (Quan.Q1)
                        (Term.Tup (Quan.Q1) (Term.Lab "False") (Term.Lab "()"))
                        (Term.Tup
                          (Quan.Q1)
                          (Term.Tup
                            (Quan.Q1)
                            (Term.Lab "WCon")
                            (Term.Tup
                              (Quan.Q1)
                              (Term.Tup (Quan.Q1) (Term.Lab "False") (Term.Lab "()"))
                              (Term.Tup
                                (Quan.Q1)
                                (Term.Tup
                                  (Quan.Q1)
                                  (Term.Lab "WCon")
                                  (Term.Tup
                                    (Quan.Q1)
                                    (Term.Tup (Quan.Q1) (Term.Lab "True") (Term.Lab "()"))
                                    (Term.Tup
                                      (Quan.Q1)
                                      (Term.Tup
                                        (Quan.Q1)
                                        (Term.Lab "WCon")
                                        (Term.Tup
                                          (Quan.Q1)
                                          (Term.Tup (Quan.Q1) (Term.Lab "True") (Term.Lab "()"))
                                          (Term.Tup
                                            (Quan.Q1)
                                            (Term.Tup
                                              (Quan.Q1)
                                              (Term.Lab "WCon")
                                              (Term.Tup
                                                (Quan.Q1)
                                                (Term.Tup
                                                  (Quan.Q1)
                                                  (Term.Lab "False")
                                                  (Term.Lab "()"))
                                                (Term.Tup
                                                  (Quan.Q1)
                                                  (Term.Tup
                                                    (Quan.Q1)
                                                    (Term.Lab "WCon")
                                                    (Term.Tup
                                                      (Quan.Q1)
                                                      (Term.Tup
                                                        (Quan.Q1)
                                                        (Term.Lab "False")
                                                        (Term.Lab "()"))
                                                      (Term.Tup
                                                        (Quan.Q1)
                                                        (Term.Tup
                                                          (Quan.Q1)
                                                          (Term.Lab "WCon")
                                                          (Term.Tup
                                                            (Quan.Q1)
                                                            (Term.Tup
                                                              (Quan.Q1)
                                                              (Term.Lab "False")
                                                              (Term.Lab "()"))
                                                            (Term.Tup
                                                              (Quan.Q1)
                                                              (Term.Tup
                                                                (Quan.Q1)
                                                                (Term.Lab "WCon")
                                                                (Term.Tup
                                                                  (Quan.Q1)
                                                                  (Term.Tup
                                                                    (Quan.Q1)
                                                                    (Term.Lab "False")
                                                                    (Term.Lab "()"))
                                                                  (Term.Tup
                                                                    (Quan.Q1)
                                                                    (Term.Tup
                                                                      (Quan.Q1)
                                                                      (Term.Lab "WCon")
                                                                      (Term.Tup
                                                                        (Quan.Q1)
                                                                        (Term.Tup
                                                                          (Quan.Q1)
                                                                          (Term.Lab "False")
                                                                          (Term.Lab "()"))
                                                                        (Term.Tup
                                                                          (Quan.Q1)
                                                                          (Term.Tup
                                                                            (Quan.Q1)
                                                                            (Term.Lab "WCon")
                                                                            (Term.Tup
                                                                              (Quan.Q1)
                                                                              (Term.Tup
                                                                                (Quan.Q1)
                                                                                (Term.Lab "False")
                                                                                (Term.Lab "()"))
                                                                              (Term.Tup
                                                                                (Quan.Q1)
                                                                                (Term.Tup
                                                                                  (Quan.Q1)
                                                                                  (Term.Lab "WCon")
                                                                                  (Term.Tup
                                                                                    (Quan.Q1)
                                                                                    (Term.Tup
                                                                                      (Quan.Q1)
                                                                                      (Term.Lab
                                                                                        "False")
                                                                                      (Term.Lab
                                                                                        "()"))
                                                                                    (Term.Tup
                                                                                      (Quan.Q1)
                                                                                      (Term.Tup
                                                                                        (Quan.Q1)
                                                                                        (Term.Lab
                                                                                          "WCon")
                                                                                        (Term.Tup
                                                                                          (Quan.Q1)
                                                                                          (Term.Tup
                                                                                            (Quan.Q1)
                                                                                            (Term.Lab
                                                                                              "False")
                                                                                            (Term.Lab
                                                                                              "()"))
                                                                                          (Term.Tup
                                                                                            (Quan.Q1)
                                                                                            (Term.Tup
                                                                                              (Quan.Q1)
                                                                                              (Term.Lab
                                                                                                "WCon")
                                                                                              (Term.Tup
                                                                                                (Quan.Q1)
                                                                                                (Term.Tup
                                                                                                  (Quan.Q1)
                                                                                                  (Term.Lab
                                                                                                    "False")
                                                                                                  (Term.Lab
                                                                                                    "()"))
                                                                                                (Term.Tup
                                                                                                  (Quan.Q1)
                                                                                                  (Term.Tup
                                                                                                    (Quan.Q1)
                                                                                                    (Term.Lab
                                                                                                      "WCon")
                                                                                                    (Term.Tup
                                                                                                      (Quan.Q1)
                                                                                                      (Term.Tup
                                                                                                        (Quan.Q1)
                                                                                                        (Term.Lab
                                                                                                          "False")
                                                                                                        (Term.Lab
                                                                                                          "()"))
                                                                                                      (Term.Tup
                                                                                                        (Quan.Q1)
                                                                                                        (Term.Tup
                                                                                                          (Quan.Q1)
                                                                                                          (Term.Lab
                                                                                                            "WCon")
                                                                                                          (Term.Tup
                                                                                                            (Quan.Q1)
                                                                                                            (Term.Tup
                                                                                                              (Quan.Q1)
                                                                                                              (Term.Lab
                                                                                                                "False")
                                                                                                              (Term.Lab
                                                                                                                "()"))
                                                                                                            (Term.Tup
                                                                                                              (Quan.Q1)
                                                                                                              (Term.Tup
                                                                                                                (Quan.Q1)
                                                                                                                (Term.Lab
                                                                                                                  "WCon")
                                                                                                                (Term.Tup
                                                                                                                  (Quan.Q1)
                                                                                                                  (Term.Tup
                                                                                                                    (Quan.Q1)
                                                                                                                    (Term.Lab
                                                                                                                      "False")
                                                                                                                    (Term.Lab
                                                                                                                      "()"))
                                                                                                                  (Term.Tup
                                                                                                                    (Quan.Q1)
                                                                                                                    (Term.Tup
                                                                                                                      (Quan.Q1)
                                                                                                                      (Term.Lab
                                                                                                                        "WCon")
                                                                                                                      (Term.Tup
                                                                                                                        (Quan.Q1)
                                                                                                                        (Term.Tup
                                                                                                                          (Quan.Q1)
                                                                                                                          (Term.Lab
                                                                                                                            "False")
                                                                                                                          (Term.Lab
                                                                                                                            "()"))
                                                                                                                        (Term.Tup
                                                                                                                          (Quan.Q1)
                                                                                                                          (Term.Tup
                                                                                                                            (Quan.Q1)
                                                                                                                            (Term.Lab
                                                                                                                              "WCon")
                                                                                                                            (Term.Tup
                                                                                                                              (Quan.Q1)
                                                                                                                              (Term.Tup
                                                                                                                                (Quan.Q1)
                                                                                                                                (Term.Lab
                                                                                                                                  "False")
                                                                                                                                (Term.Lab
                                                                                                                                  "()"))
                                                                                                                              (Term.Tup
                                                                                                                                (Quan.Q1)
                                                                                                                                (Term.Tup
                                                                                                                                  (Quan.Q1)
                                                                                                                                  (Term.Lab
                                                                                                                                    "WCon")
                                                                                                                                  (Term.Tup
                                                                                                                                    (Quan.Q1)
                                                                                                                                    (Term.Tup
                                                                                                                                      (Quan.Q1)
                                                                                                                                      (Term.Lab
                                                                                                                                        "False")
                                                                                                                                      (Term.Lab
                                                                                                                                        "()"))
                                                                                                                                    (Term.Tup
                                                                                                                                      (Quan.Q1)
                                                                                                                                      (Term.Tup
                                                                                                                                        (Quan.Q1)
                                                                                                                                        (Term.Lab
                                                                                                                                          "WCon")
                                                                                                                                        (Term.Tup
                                                                                                                                          (Quan.Q1)
                                                                                                                                          (Term.Tup
                                                                                                                                            (Quan.Q1)
                                                                                                                                            (Term.Lab
                                                                                                                                              "False")
                                                                                                                                            (Term.Lab
                                                                                                                                              "()"))
                                                                                                                                          (Term.Tup
                                                                                                                                            (Quan.Q1)
                                                                                                                                            (Term.Tup
                                                                                                                                              (Quan.Q1)
                                                                                                                                              (Term.Lab
                                                                                                                                                "WCon")
                                                                                                                                              (Term.Tup
                                                                                                                                                (Quan.Q1)
                                                                                                                                                (Term.Tup
                                                                                                                                                  (Quan.Q1)
                                                                                                                                                  (Term.Lab
                                                                                                                                                    "False")
                                                                                                                                                  (Term.Lab
                                                                                                                                                    "()"))
                                                                                                                                                (Term.Tup
                                                                                                                                                  (Quan.Q1)
                                                                                                                                                  (Term.Tup
                                                                                                                                                    (Quan.Q1)
                                                                                                                                                    (Term.Lab
                                                                                                                                                      "WCon")
                                                                                                                                                    (Term.Tup
                                                                                                                                                      (Quan.Q1)
                                                                                                                                                      (Term.Tup
                                                                                                                                                        (Quan.Q1)
                                                                                                                                                        (Term.Lab
                                                                                                                                                          "False")
                                                                                                                                                        (Term.Lab
                                                                                                                                                          "()"))
                                                                                                                                                      (Term.Tup
                                                                                                                                                        (Quan.Q1)
                                                                                                                                                        (Term.Tup
                                                                                                                                                          (Quan.Q1)
                                                                                                                                                          (Term.Lab
                                                                                                                                                            "WCon")
                                                                                                                                                          (Term.Tup
                                                                                                                                                            (Quan.Q1)
                                                                                                                                                            (Term.Tup
                                                                                                                                                              (Quan.Q1)
                                                                                                                                                              (Term.Lab
                                                                                                                                                                "False")
                                                                                                                                                              (Term.Lab
                                                                                                                                                                "()"))
                                                                                                                                                            (Term.Tup
                                                                                                                                                              (Quan.Q1)
                                                                                                                                                              (Term.Tup
                                                                                                                                                                (Quan.Q1)
                                                                                                                                                                (Term.Lab
                                                                                                                                                                  "WCon")
                                                                                                                                                                (Term.Tup
                                                                                                                                                                  (Quan.Q1)
                                                                                                                                                                  (Term.Tup
                                                                                                                                                                    (Quan.Q1)
                                                                                                                                                                    (Term.Lab
                                                                                                                                                                      "False")
                                                                                                                                                                    (Term.Lab
                                                                                                                                                                      "()"))
                                                                                                                                                                  (Term.Tup
                                                                                                                                                                    (Quan.Q1)
                                                                                                                                                                    (Term.Tup
                                                                                                                                                                      (Quan.Q1)
                                                                                                                                                                      (Term.Lab
                                                                                                                                                                        "WCon")
                                                                                                                                                                      (Term.Tup
                                                                                                                                                                        (Quan.Q1)
                                                                                                                                                                        (Term.Tup
                                                                                                                                                                          (Quan.Q1)
                                                                                                                                                                          (Term.Lab
                                                                                                                                                                            "False")
                                                                                                                                                                          (Term.Lab
                                                                                                                                                                            "()"))
                                                                                                                                                                        (Term.Tup
                                                                                                                                                                          (Quan.Q1)
                                                                                                                                                                          (Term.Tup
                                                                                                                                                                            (Quan.Q1)
                                                                                                                                                                            (Term.Lab
                                                                                                                                                                              "WCon")
                                                                                                                                                                            (Term.Tup
                                                                                                                                                                              (Quan.Q1)
                                                                                                                                                                              (Term.Tup
                                                                                                                                                                                (Quan.Q1)
                                                                                                                                                                                (Term.Lab
                                                                                                                                                                                  "False")
                                                                                                                                                                                (Term.Lab
                                                                                                                                                                                  "()"))
                                                                                                                                                                              (Term.Tup
                                                                                                                                                                                (Quan.Q1)
                                                                                                                                                                                (Term.Tup
                                                                                                                                                                                  (Quan.Q1)
                                                                                                                                                                                  (Term.Lab
                                                                                                                                                                                    "WCon")
                                                                                                                                                                                  (Term.Tup
                                                                                                                                                                                    (Quan.Q1)
                                                                                                                                                                                    (Term.Tup
                                                                                                                                                                                      (Quan.Q1)
                                                                                                                                                                                      (Term.Lab
                                                                                                                                                                                        "False")
                                                                                                                                                                                      (Term.Lab
                                                                                                                                                                                        "()"))
                                                                                                                                                                                    (Term.Tup
                                                                                                                                                                                      (Quan.Q1)
                                                                                                                                                                                      (Term.Tup
                                                                                                                                                                                        (Quan.Q1)
                                                                                                                                                                                        (Term.Lab
                                                                                                                                                                                          "WCon")
                                                                                                                                                                                        (Term.Tup
                                                                                                                                                                                          (Quan.Q1)
                                                                                                                                                                                          (Term.Tup
                                                                                                                                                                                            (Quan.Q1)
                                                                                                                                                                                            (Term.Lab
                                                                                                                                                                                              "False")
                                                                                                                                                                                            (Term.Lab
                                                                                                                                                                                              "()"))
                                                                                                                                                                                          (Term.Tup
                                                                                                                                                                                            (Quan.Q1)
                                                                                                                                                                                            (Term.Tup
                                                                                                                                                                                              (Quan.Q1)
                                                                                                                                                                                              (Term.Lab
                                                                                                                                                                                                "WCon")
                                                                                                                                                                                              (Term.Tup
                                                                                                                                                                                                (Quan.Q1)
                                                                                                                                                                                                (Term.Tup
                                                                                                                                                                                                  (Quan.Q1)
                                                                                                                                                                                                  (Term.Lab
                                                                                                                                                                                                    "False")
                                                                                                                                                                                                  (Term.Lab
                                                                                                                                                                                                    "()"))
                                                                                                                                                                                                (Term.Tup
                                                                                                                                                                                                  (Quan.Q1)
                                                                                                                                                                                                  (Term.Tup
                                                                                                                                                                                                    (Quan.Q1)
                                                                                                                                                                                                    (Term.Lab
                                                                                                                                                                                                      "WCon")
                                                                                                                                                                                                    (Term.Tup
                                                                                                                                                                                                      (Quan.Q1)
                                                                                                                                                                                                      (Term.Tup
                                                                                                                                                                                                        (Quan.Q1)
                                                                                                                                                                                                        (Term.Lab
                                                                                                                                                                                                          "False")
                                                                                                                                                                                                        (Term.Lab
                                                                                                                                                                                                          "()"))
                                                                                                                                                                                                      (Term.Tup
                                                                                                                                                                                                        (Quan.Q1)
                                                                                                                                                                                                        (Term.Tup
                                                                                                                                                                                                          (Quan.Q1)
                                                                                                                                                                                                          (Term.Lab
                                                                                                                                                                                                            "WNil")
                                                                                                                                                                                                          (Term.Lab
                                                                                                                                                                                                            "()"))
                                                                                                                                                                                                        (Term.Lab
                                                                                                                                                                                                          "()"))))
                                                                                                                                                                                                  (Term.Lab
                                                                                                                                                                                                    "()"))))
                                                                                                                                                                                            (Term.Lab
                                                                                                                                                                                              "()"))))
                                                                                                                                                                                      (Term.Lab
                                                                                                                                                                                        "()"))))
                                                                                                                                                                                (Term.Lab
                                                                                                                                                                                  "()"))))
                                                                                                                                                                          (Term.Lab
                                                                                                                                                                            "()"))))
                                                                                                                                                                    (Term.Lab
                                                                                                                                                                      "()"))))
                                                                                                                                                              (Term.Lab
                                                                                                                                                                "()"))))
                                                                                                                                                        (Term.Lab
                                                                                                                                                          "()"))))
                                                                                                                                                  (Term.Lab
                                                                                                                                                    "()"))))
                                                                                                                                            (Term.Lab
                                                                                                                                              "()"))))
                                                                                                                                      (Term.Lab
                                                                                                                                        "()"))))
                                                                                                                                (Term.Lab
                                                                                                                                  "()"))))
                                                                                                                          (Term.Lab
                                                                                                                            "()"))))
                                                                                                                    (Term.Lab
                                                                                                                      "()"))))
                                                                                                              (Term.Lab
                                                                                                                "()"))))
                                                                                                        (Term.Lab
                                                                                                          "()"))))
                                                                                                  (Term.Lab
                                                                                                    "()"))))
                                                                                            (Term.Lab
                                                                                              "()"))))
                                                                                      (Term.Lab
                                                                                        "()"))))
                                                                                (Term.Lab "()"))))
                                                                          (Term.Lab "()"))))
                                                                    (Term.Lab "()"))))
                                                              (Term.Lab "()"))))
                                                        (Term.Lab "()"))))
                                                  (Term.Lab "()"))))
                                            (Term.Lab "()"))))
                                      (Term.Lab "()"))))
                                (Term.Lab "()"))))
                          (Term.Lab "()"))))
                    (Term.Lab "()"))))
              (Term.Lab "()"))))
        (Term.Lab "()")),
    false⟩

def «evalVersion.U32.lit50» : Def :=
  ⟨"U32.lit50",
    Term.Ref "U32",
    Term.Tup
      (Quan.Q1)
      (Term.Lab "U32")
      (Term.Tup
        (Quan.Q1)
        (Term.Tup
          (Quan.Q1)
          (Term.Lab "WCon")
          (Term.Tup
            (Quan.Q1)
            (Term.Tup (Quan.Q1) (Term.Lab "False") (Term.Lab "()"))
            (Term.Tup
              (Quan.Q1)
              (Term.Tup
                (Quan.Q1)
                (Term.Lab "WCon")
                (Term.Tup
                  (Quan.Q1)
                  (Term.Tup (Quan.Q1) (Term.Lab "True") (Term.Lab "()"))
                  (Term.Tup
                    (Quan.Q1)
                    (Term.Tup
                      (Quan.Q1)
                      (Term.Lab "WCon")
                      (Term.Tup
                        (Quan.Q1)
                        (Term.Tup (Quan.Q1) (Term.Lab "False") (Term.Lab "()"))
                        (Term.Tup
                          (Quan.Q1)
                          (Term.Tup
                            (Quan.Q1)
                            (Term.Lab "WCon")
                            (Term.Tup
                              (Quan.Q1)
                              (Term.Tup (Quan.Q1) (Term.Lab "False") (Term.Lab "()"))
                              (Term.Tup
                                (Quan.Q1)
                                (Term.Tup
                                  (Quan.Q1)
                                  (Term.Lab "WCon")
                                  (Term.Tup
                                    (Quan.Q1)
                                    (Term.Tup (Quan.Q1) (Term.Lab "True") (Term.Lab "()"))
                                    (Term.Tup
                                      (Quan.Q1)
                                      (Term.Tup
                                        (Quan.Q1)
                                        (Term.Lab "WCon")
                                        (Term.Tup
                                          (Quan.Q1)
                                          (Term.Tup (Quan.Q1) (Term.Lab "True") (Term.Lab "()"))
                                          (Term.Tup
                                            (Quan.Q1)
                                            (Term.Tup
                                              (Quan.Q1)
                                              (Term.Lab "WCon")
                                              (Term.Tup
                                                (Quan.Q1)
                                                (Term.Tup
                                                  (Quan.Q1)
                                                  (Term.Lab "False")
                                                  (Term.Lab "()"))
                                                (Term.Tup
                                                  (Quan.Q1)
                                                  (Term.Tup
                                                    (Quan.Q1)
                                                    (Term.Lab "WCon")
                                                    (Term.Tup
                                                      (Quan.Q1)
                                                      (Term.Tup
                                                        (Quan.Q1)
                                                        (Term.Lab "False")
                                                        (Term.Lab "()"))
                                                      (Term.Tup
                                                        (Quan.Q1)
                                                        (Term.Tup
                                                          (Quan.Q1)
                                                          (Term.Lab "WCon")
                                                          (Term.Tup
                                                            (Quan.Q1)
                                                            (Term.Tup
                                                              (Quan.Q1)
                                                              (Term.Lab "False")
                                                              (Term.Lab "()"))
                                                            (Term.Tup
                                                              (Quan.Q1)
                                                              (Term.Tup
                                                                (Quan.Q1)
                                                                (Term.Lab "WCon")
                                                                (Term.Tup
                                                                  (Quan.Q1)
                                                                  (Term.Tup
                                                                    (Quan.Q1)
                                                                    (Term.Lab "False")
                                                                    (Term.Lab "()"))
                                                                  (Term.Tup
                                                                    (Quan.Q1)
                                                                    (Term.Tup
                                                                      (Quan.Q1)
                                                                      (Term.Lab "WCon")
                                                                      (Term.Tup
                                                                        (Quan.Q1)
                                                                        (Term.Tup
                                                                          (Quan.Q1)
                                                                          (Term.Lab "False")
                                                                          (Term.Lab "()"))
                                                                        (Term.Tup
                                                                          (Quan.Q1)
                                                                          (Term.Tup
                                                                            (Quan.Q1)
                                                                            (Term.Lab "WCon")
                                                                            (Term.Tup
                                                                              (Quan.Q1)
                                                                              (Term.Tup
                                                                                (Quan.Q1)
                                                                                (Term.Lab "False")
                                                                                (Term.Lab "()"))
                                                                              (Term.Tup
                                                                                (Quan.Q1)
                                                                                (Term.Tup
                                                                                  (Quan.Q1)
                                                                                  (Term.Lab "WCon")
                                                                                  (Term.Tup
                                                                                    (Quan.Q1)
                                                                                    (Term.Tup
                                                                                      (Quan.Q1)
                                                                                      (Term.Lab
                                                                                        "False")
                                                                                      (Term.Lab
                                                                                        "()"))
                                                                                    (Term.Tup
                                                                                      (Quan.Q1)
                                                                                      (Term.Tup
                                                                                        (Quan.Q1)
                                                                                        (Term.Lab
                                                                                          "WCon")
                                                                                        (Term.Tup
                                                                                          (Quan.Q1)
                                                                                          (Term.Tup
                                                                                            (Quan.Q1)
                                                                                            (Term.Lab
                                                                                              "False")
                                                                                            (Term.Lab
                                                                                              "()"))
                                                                                          (Term.Tup
                                                                                            (Quan.Q1)
                                                                                            (Term.Tup
                                                                                              (Quan.Q1)
                                                                                              (Term.Lab
                                                                                                "WCon")
                                                                                              (Term.Tup
                                                                                                (Quan.Q1)
                                                                                                (Term.Tup
                                                                                                  (Quan.Q1)
                                                                                                  (Term.Lab
                                                                                                    "False")
                                                                                                  (Term.Lab
                                                                                                    "()"))
                                                                                                (Term.Tup
                                                                                                  (Quan.Q1)
                                                                                                  (Term.Tup
                                                                                                    (Quan.Q1)
                                                                                                    (Term.Lab
                                                                                                      "WCon")
                                                                                                    (Term.Tup
                                                                                                      (Quan.Q1)
                                                                                                      (Term.Tup
                                                                                                        (Quan.Q1)
                                                                                                        (Term.Lab
                                                                                                          "False")
                                                                                                        (Term.Lab
                                                                                                          "()"))
                                                                                                      (Term.Tup
                                                                                                        (Quan.Q1)
                                                                                                        (Term.Tup
                                                                                                          (Quan.Q1)
                                                                                                          (Term.Lab
                                                                                                            "WCon")
                                                                                                          (Term.Tup
                                                                                                            (Quan.Q1)
                                                                                                            (Term.Tup
                                                                                                              (Quan.Q1)
                                                                                                              (Term.Lab
                                                                                                                "False")
                                                                                                              (Term.Lab
                                                                                                                "()"))
                                                                                                            (Term.Tup
                                                                                                              (Quan.Q1)
                                                                                                              (Term.Tup
                                                                                                                (Quan.Q1)
                                                                                                                (Term.Lab
                                                                                                                  "WCon")
                                                                                                                (Term.Tup
                                                                                                                  (Quan.Q1)
                                                                                                                  (Term.Tup
                                                                                                                    (Quan.Q1)
                                                                                                                    (Term.Lab
                                                                                                                      "False")
                                                                                                                    (Term.Lab
                                                                                                                      "()"))
                                                                                                                  (Term.Tup
                                                                                                                    (Quan.Q1)
                                                                                                                    (Term.Tup
                                                                                                                      (Quan.Q1)
                                                                                                                      (Term.Lab
                                                                                                                        "WCon")
                                                                                                                      (Term.Tup
                                                                                                                        (Quan.Q1)
                                                                                                                        (Term.Tup
                                                                                                                          (Quan.Q1)
                                                                                                                          (Term.Lab
                                                                                                                            "False")
                                                                                                                          (Term.Lab
                                                                                                                            "()"))
                                                                                                                        (Term.Tup
                                                                                                                          (Quan.Q1)
                                                                                                                          (Term.Tup
                                                                                                                            (Quan.Q1)
                                                                                                                            (Term.Lab
                                                                                                                              "WCon")
                                                                                                                            (Term.Tup
                                                                                                                              (Quan.Q1)
                                                                                                                              (Term.Tup
                                                                                                                                (Quan.Q1)
                                                                                                                                (Term.Lab
                                                                                                                                  "False")
                                                                                                                                (Term.Lab
                                                                                                                                  "()"))
                                                                                                                              (Term.Tup
                                                                                                                                (Quan.Q1)
                                                                                                                                (Term.Tup
                                                                                                                                  (Quan.Q1)
                                                                                                                                  (Term.Lab
                                                                                                                                    "WCon")
                                                                                                                                  (Term.Tup
                                                                                                                                    (Quan.Q1)
                                                                                                                                    (Term.Tup
                                                                                                                                      (Quan.Q1)
                                                                                                                                      (Term.Lab
                                                                                                                                        "False")
                                                                                                                                      (Term.Lab
                                                                                                                                        "()"))
                                                                                                                                    (Term.Tup
                                                                                                                                      (Quan.Q1)
                                                                                                                                      (Term.Tup
                                                                                                                                        (Quan.Q1)
                                                                                                                                        (Term.Lab
                                                                                                                                          "WCon")
                                                                                                                                        (Term.Tup
                                                                                                                                          (Quan.Q1)
                                                                                                                                          (Term.Tup
                                                                                                                                            (Quan.Q1)
                                                                                                                                            (Term.Lab
                                                                                                                                              "False")
                                                                                                                                            (Term.Lab
                                                                                                                                              "()"))
                                                                                                                                          (Term.Tup
                                                                                                                                            (Quan.Q1)
                                                                                                                                            (Term.Tup
                                                                                                                                              (Quan.Q1)
                                                                                                                                              (Term.Lab
                                                                                                                                                "WCon")
                                                                                                                                              (Term.Tup
                                                                                                                                                (Quan.Q1)
                                                                                                                                                (Term.Tup
                                                                                                                                                  (Quan.Q1)
                                                                                                                                                  (Term.Lab
                                                                                                                                                    "False")
                                                                                                                                                  (Term.Lab
                                                                                                                                                    "()"))
                                                                                                                                                (Term.Tup
                                                                                                                                                  (Quan.Q1)
                                                                                                                                                  (Term.Tup
                                                                                                                                                    (Quan.Q1)
                                                                                                                                                    (Term.Lab
                                                                                                                                                      "WCon")
                                                                                                                                                    (Term.Tup
                                                                                                                                                      (Quan.Q1)
                                                                                                                                                      (Term.Tup
                                                                                                                                                        (Quan.Q1)
                                                                                                                                                        (Term.Lab
                                                                                                                                                          "False")
                                                                                                                                                        (Term.Lab
                                                                                                                                                          "()"))
                                                                                                                                                      (Term.Tup
                                                                                                                                                        (Quan.Q1)
                                                                                                                                                        (Term.Tup
                                                                                                                                                          (Quan.Q1)
                                                                                                                                                          (Term.Lab
                                                                                                                                                            "WCon")
                                                                                                                                                          (Term.Tup
                                                                                                                                                            (Quan.Q1)
                                                                                                                                                            (Term.Tup
                                                                                                                                                              (Quan.Q1)
                                                                                                                                                              (Term.Lab
                                                                                                                                                                "False")
                                                                                                                                                              (Term.Lab
                                                                                                                                                                "()"))
                                                                                                                                                            (Term.Tup
                                                                                                                                                              (Quan.Q1)
                                                                                                                                                              (Term.Tup
                                                                                                                                                                (Quan.Q1)
                                                                                                                                                                (Term.Lab
                                                                                                                                                                  "WCon")
                                                                                                                                                                (Term.Tup
                                                                                                                                                                  (Quan.Q1)
                                                                                                                                                                  (Term.Tup
                                                                                                                                                                    (Quan.Q1)
                                                                                                                                                                    (Term.Lab
                                                                                                                                                                      "False")
                                                                                                                                                                    (Term.Lab
                                                                                                                                                                      "()"))
                                                                                                                                                                  (Term.Tup
                                                                                                                                                                    (Quan.Q1)
                                                                                                                                                                    (Term.Tup
                                                                                                                                                                      (Quan.Q1)
                                                                                                                                                                      (Term.Lab
                                                                                                                                                                        "WCon")
                                                                                                                                                                      (Term.Tup
                                                                                                                                                                        (Quan.Q1)
                                                                                                                                                                        (Term.Tup
                                                                                                                                                                          (Quan.Q1)
                                                                                                                                                                          (Term.Lab
                                                                                                                                                                            "False")
                                                                                                                                                                          (Term.Lab
                                                                                                                                                                            "()"))
                                                                                                                                                                        (Term.Tup
                                                                                                                                                                          (Quan.Q1)
                                                                                                                                                                          (Term.Tup
                                                                                                                                                                            (Quan.Q1)
                                                                                                                                                                            (Term.Lab
                                                                                                                                                                              "WCon")
                                                                                                                                                                            (Term.Tup
                                                                                                                                                                              (Quan.Q1)
                                                                                                                                                                              (Term.Tup
                                                                                                                                                                                (Quan.Q1)
                                                                                                                                                                                (Term.Lab
                                                                                                                                                                                  "False")
                                                                                                                                                                                (Term.Lab
                                                                                                                                                                                  "()"))
                                                                                                                                                                              (Term.Tup
                                                                                                                                                                                (Quan.Q1)
                                                                                                                                                                                (Term.Tup
                                                                                                                                                                                  (Quan.Q1)
                                                                                                                                                                                  (Term.Lab
                                                                                                                                                                                    "WCon")
                                                                                                                                                                                  (Term.Tup
                                                                                                                                                                                    (Quan.Q1)
                                                                                                                                                                                    (Term.Tup
                                                                                                                                                                                      (Quan.Q1)
                                                                                                                                                                                      (Term.Lab
                                                                                                                                                                                        "False")
                                                                                                                                                                                      (Term.Lab
                                                                                                                                                                                        "()"))
                                                                                                                                                                                    (Term.Tup
                                                                                                                                                                                      (Quan.Q1)
                                                                                                                                                                                      (Term.Tup
                                                                                                                                                                                        (Quan.Q1)
                                                                                                                                                                                        (Term.Lab
                                                                                                                                                                                          "WCon")
                                                                                                                                                                                        (Term.Tup
                                                                                                                                                                                          (Quan.Q1)
                                                                                                                                                                                          (Term.Tup
                                                                                                                                                                                            (Quan.Q1)
                                                                                                                                                                                            (Term.Lab
                                                                                                                                                                                              "False")
                                                                                                                                                                                            (Term.Lab
                                                                                                                                                                                              "()"))
                                                                                                                                                                                          (Term.Tup
                                                                                                                                                                                            (Quan.Q1)
                                                                                                                                                                                            (Term.Tup
                                                                                                                                                                                              (Quan.Q1)
                                                                                                                                                                                              (Term.Lab
                                                                                                                                                                                                "WCon")
                                                                                                                                                                                              (Term.Tup
                                                                                                                                                                                                (Quan.Q1)
                                                                                                                                                                                                (Term.Tup
                                                                                                                                                                                                  (Quan.Q1)
                                                                                                                                                                                                  (Term.Lab
                                                                                                                                                                                                    "False")
                                                                                                                                                                                                  (Term.Lab
                                                                                                                                                                                                    "()"))
                                                                                                                                                                                                (Term.Tup
                                                                                                                                                                                                  (Quan.Q1)
                                                                                                                                                                                                  (Term.Tup
                                                                                                                                                                                                    (Quan.Q1)
                                                                                                                                                                                                    (Term.Lab
                                                                                                                                                                                                      "WCon")
                                                                                                                                                                                                    (Term.Tup
                                                                                                                                                                                                      (Quan.Q1)
                                                                                                                                                                                                      (Term.Tup
                                                                                                                                                                                                        (Quan.Q1)
                                                                                                                                                                                                        (Term.Lab
                                                                                                                                                                                                          "False")
                                                                                                                                                                                                        (Term.Lab
                                                                                                                                                                                                          "()"))
                                                                                                                                                                                                      (Term.Tup
                                                                                                                                                                                                        (Quan.Q1)
                                                                                                                                                                                                        (Term.Tup
                                                                                                                                                                                                          (Quan.Q1)
                                                                                                                                                                                                          (Term.Lab
                                                                                                                                                                                                            "WNil")
                                                                                                                                                                                                          (Term.Lab
                                                                                                                                                                                                            "()"))
                                                                                                                                                                                                        (Term.Lab
                                                                                                                                                                                                          "()"))))
                                                                                                                                                                                                  (Term.Lab
                                                                                                                                                                                                    "()"))))
                                                                                                                                                                                            (Term.Lab
                                                                                                                                                                                              "()"))))
                                                                                                                                                                                      (Term.Lab
                                                                                                                                                                                        "()"))))
                                                                                                                                                                                (Term.Lab
                                                                                                                                                                                  "()"))))
                                                                                                                                                                          (Term.Lab
                                                                                                                                                                            "()"))))
                                                                                                                                                                    (Term.Lab
                                                                                                                                                                      "()"))))
                                                                                                                                                              (Term.Lab
                                                                                                                                                                "()"))))
                                                                                                                                                        (Term.Lab
                                                                                                                                                          "()"))))
                                                                                                                                                  (Term.Lab
                                                                                                                                                    "()"))))
                                                                                                                                            (Term.Lab
                                                                                                                                              "()"))))
                                                                                                                                      (Term.Lab
                                                                                                                                        "()"))))
                                                                                                                                (Term.Lab
                                                                                                                                  "()"))))
                                                                                                                          (Term.Lab
                                                                                                                            "()"))))
                                                                                                                    (Term.Lab
                                                                                                                      "()"))))
                                                                                                              (Term.Lab
                                                                                                                "()"))))
                                                                                                        (Term.Lab
                                                                                                          "()"))))
                                                                                                  (Term.Lab
                                                                                                    "()"))))
                                                                                            (Term.Lab
                                                                                              "()"))))
                                                                                      (Term.Lab
                                                                                        "()"))))
                                                                                (Term.Lab "()"))))
                                                                          (Term.Lab "()"))))
                                                                    (Term.Lab "()"))))
                                                              (Term.Lab "()"))))
                                                        (Term.Lab "()"))))
                                                  (Term.Lab "()"))))
                                            (Term.Lab "()"))))
                                      (Term.Lab "()"))))
                                (Term.Lab "()"))))
                          (Term.Lab "()"))))
                    (Term.Lab "()"))))
              (Term.Lab "()"))))
        (Term.Lab "()")),
    false⟩

def «evalVersion.Quan.name» : Def :=
  ⟨"Quan.name",
    Term.All
      (Quan.Q1)
      (Term.Ref "Quan")
      (Term.App
        (Quan.Q0)
        (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
        (Term.App
          (Quan.Q1)
          (Term.Ref "Word")
          (Term.Tup
            (Quan.Q1)
            (Term.Lab "Succ")
            (Term.Tup
              (Quan.Q1)
              (Term.Tup
                (Quan.Q1)
                (Term.Lab "Succ")
                (Term.Tup
                  (Quan.Q1)
                  (Term.Tup
                    (Quan.Q1)
                    (Term.Lab "Succ")
                    (Term.Tup
                      (Quan.Q1)
                      (Term.Tup
                        (Quan.Q1)
                        (Term.Lab "Succ")
                        (Term.Tup
                          (Quan.Q1)
                          (Term.Tup
                            (Quan.Q1)
                            (Term.Lab "Succ")
                            (Term.Tup
                              (Quan.Q1)
                              (Term.Tup
                                (Quan.Q1)
                                (Term.Lab "Succ")
                                (Term.Tup
                                  (Quan.Q1)
                                  (Term.Tup
                                    (Quan.Q1)
                                    (Term.Lab "Succ")
                                    (Term.Tup
                                      (Quan.Q1)
                                      (Term.Tup
                                        (Quan.Q1)
                                        (Term.Lab "Succ")
                                        (Term.Tup
                                          (Quan.Q1)
                                          (Term.Tup (Quan.Q1) (Term.Lab "Zero") (Term.Lab "()"))
                                          (Term.Lab "()")))
                                      (Term.Lab "()")))
                                  (Term.Lab "()")))
                              (Term.Lab "()")))
                          (Term.Lab "()")))
                      (Term.Lab "()")))
                  (Term.Lab "()")))
              (Term.Lab "()"))))),
    Term.Prj
      (Term.Mat
        "Quan.Q0"
        (Term.Mat
          "()"
          (Term.Tup
            (Quan.Q1)
            (Term.Lab "Con")
            (Term.Tup
              (Quan.Q1)
              (Term.App (Quan.Q1) (Term.Ref "Byte.from_u32") (Term.Ref "U32.lit81"))
              (Term.Tup
                (Quan.Q1)
                (Term.Tup
                  (Quan.Q1)
                  (Term.Lab "Con")
                  (Term.Tup
                    (Quan.Q1)
                    (Term.App (Quan.Q1) (Term.Ref "Byte.from_u32") (Term.Ref "U32.lit48"))
                    (Term.Tup
                      (Quan.Q1)
                      (Term.Tup (Quan.Q1) (Term.Lab "Nil") (Term.Lab "()"))
                      (Term.Lab "()"))))
                (Term.Lab "()"))))
          (Term.Efq))
        (Term.Mat
          "Quan.Q1"
          (Term.Mat
            "()"
            (Term.Tup
              (Quan.Q1)
              (Term.Lab "Con")
              (Term.Tup
                (Quan.Q1)
                (Term.App (Quan.Q1) (Term.Ref "Byte.from_u32") (Term.Ref "U32.lit81"))
                (Term.Tup
                  (Quan.Q1)
                  (Term.Tup
                    (Quan.Q1)
                    (Term.Lab "Con")
                    (Term.Tup
                      (Quan.Q1)
                      (Term.App (Quan.Q1) (Term.Ref "Byte.from_u32") (Term.Ref "U32.lit49"))
                      (Term.Tup
                        (Quan.Q1)
                        (Term.Tup (Quan.Q1) (Term.Lab "Nil") (Term.Lab "()"))
                        (Term.Lab "()"))))
                  (Term.Lab "()"))))
            (Term.Efq))
          (Term.Mat
            "Quan.Q2"
            (Term.Mat
              "()"
              (Term.Tup
                (Quan.Q1)
                (Term.Lab "Con")
                (Term.Tup
                  (Quan.Q1)
                  (Term.App (Quan.Q1) (Term.Ref "Byte.from_u32") (Term.Ref "U32.lit81"))
                  (Term.Tup
                    (Quan.Q1)
                    (Term.Tup
                      (Quan.Q1)
                      (Term.Lab "Con")
                      (Term.Tup
                        (Quan.Q1)
                        (Term.App (Quan.Q1) (Term.Ref "Byte.from_u32") (Term.Ref "U32.lit50"))
                        (Term.Tup
                          (Quan.Q1)
                          (Term.Tup (Quan.Q1) (Term.Lab "Nil") (Term.Lab "()"))
                          (Term.Lab "()"))))
                    (Term.Lab "()"))))
              (Term.Efq))
            (Term.Efq)))),
    false⟩

def «evalVersion.Quan.read» : Def :=
  ⟨"Quan.read",
    Term.All
      (Quan.Q2)
      (Term.App
        (Quan.Q0)
        (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2"))
        (Term.App
          (Quan.Q1)
          (Term.Ref "Word")
          (Term.Tup
            (Quan.Q1)
            (Term.Lab "Succ")
            (Term.Tup
              (Quan.Q1)
              (Term.Tup
                (Quan.Q1)
                (Term.Lab "Succ")
                (Term.Tup
                  (Quan.Q1)
                  (Term.Tup
                    (Quan.Q1)
                    (Term.Lab "Succ")
                    (Term.Tup
                      (Quan.Q1)
                      (Term.Tup
                        (Quan.Q1)
                        (Term.Lab "Succ")
                        (Term.Tup
                          (Quan.Q1)
                          (Term.Tup
                            (Quan.Q1)
                            (Term.Lab "Succ")
                            (Term.Tup
                              (Quan.Q1)
                              (Term.Tup
                                (Quan.Q1)
                                (Term.Lab "Succ")
                                (Term.Tup
                                  (Quan.Q1)
                                  (Term.Tup
                                    (Quan.Q1)
                                    (Term.Lab "Succ")
                                    (Term.Tup
                                      (Quan.Q1)
                                      (Term.Tup
                                        (Quan.Q1)
                                        (Term.Lab "Succ")
                                        (Term.Tup
                                          (Quan.Q1)
                                          (Term.Tup (Quan.Q1) (Term.Lab "Zero") (Term.Lab "()"))
                                          (Term.Lab "()")))
                                      (Term.Lab "()")))
                                  (Term.Lab "()")))
                              (Term.Lab "()")))
                          (Term.Lab "()")))
                      (Term.Lab "()")))
                  (Term.Lab "()")))
              (Term.Lab "()")))))
      (Term.App (Quan.Q0) (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1")) (Term.Ref "Quan")),
    Term.Lam
      (Quan.Q2)
      (Term.App
        (Quan.Q1)
        (Term.App
          (Quan.Q1)
          (Term.App
            (Quan.Q1)
            (Term.Ref "Quan.read.if")
            (Term.App
              (Quan.Q1)
              (Term.App (Quan.Q1) (Term.Ref "Name.is_eq") (Term.Var 0))
              (Term.App
                (Quan.Q1)
                (Term.Ref "Quan.name")
                (Term.Tup (Quan.Q1) (Term.Lab "Quan.Q0") (Term.Lab "()")))))
          (Term.Tup (Quan.Q1) (Term.Lab "Quan.Q0") (Term.Lab "()")))
        (Term.App
          (Quan.Q1)
          (Term.App
            (Quan.Q1)
            (Term.App
              (Quan.Q1)
              (Term.Ref "Quan.read.if")
              (Term.App
                (Quan.Q1)
                (Term.App (Quan.Q1) (Term.Ref "Name.is_eq") (Term.Var 0))
                (Term.App
                  (Quan.Q1)
                  (Term.Ref "Quan.name")
                  (Term.Tup (Quan.Q1) (Term.Lab "Quan.Q1") (Term.Lab "()")))))
            (Term.Tup (Quan.Q1) (Term.Lab "Quan.Q1") (Term.Lab "()")))
          (Term.App
            (Quan.Q1)
            (Term.App
              (Quan.Q1)
              (Term.App
                (Quan.Q1)
                (Term.Ref "Quan.read.if")
                (Term.App
                  (Quan.Q1)
                  (Term.App (Quan.Q1) (Term.Ref "Name.is_eq") (Term.Var 0))
                  (Term.App
                    (Quan.Q1)
                    (Term.Ref "Quan.name")
                    (Term.Tup (Quan.Q1) (Term.Lab "Quan.Q2") (Term.Lab "()")))))
              (Term.Tup (Quan.Q1) (Term.Lab "Quan.Q2") (Term.Lab "()")))
            (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))))),
    false⟩

def «evalVersion.Quan.min» : Def :=
  ⟨"Quan.min",
    Term.All (Quan.Q1) (Term.Ref "Quan") (Term.All (Quan.Q1) (Term.Ref "Quan") (Term.Ref "Quan")),
    Term.Prj
      (Term.Mat
        "Quan.Q2"
        (Term.Mat
          "()"
          (Term.Prj
            (Term.Mat
              "Quan.Q2"
              (Term.Mat "()" (Term.Tup (Quan.Q1) (Term.Lab "Quan.Q2") (Term.Lab "()")) (Term.Efq))
              (Term.Mat
                "Quan.Q0"
                (Term.Mat "()" (Term.Tup (Quan.Q1) (Term.Lab "Quan.Q0") (Term.Lab "()")) (Term.Efq))
                (Term.Lam
                  (Quan.Q1)
                  (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Var 1) (Term.Var 0)))))))
          (Term.Efq))
        (Term.Mat
          "Quan.Q0"
          (Term.Mat
            "()"
            (Term.Prj
              (Term.Mat
                "Quan.Q2"
                (Term.Mat "()" (Term.Tup (Quan.Q1) (Term.Lab "Quan.Q0") (Term.Lab "()")) (Term.Efq))
                (Term.Mat
                  "Quan.Q0"
                  (Term.Mat
                    "()"
                    (Term.Tup (Quan.Q1) (Term.Lab "Quan.Q0") (Term.Lab "()"))
                    (Term.Efq))
                  (Term.Lam
                    (Quan.Q1)
                    (Term.Lam
                      (Quan.Q1)
                      (Term.Tup (Quan.Q1) (Term.Lab "Quan.Q0") (Term.Lab "()")))))))
            (Term.Efq))
          (Term.Lam
            (Quan.Q1)
            (Term.Lam
              (Quan.Q1)
              (Term.Prj
                (Term.Mat
                  "Quan.Q2"
                  (Term.Mat "()" (Term.Tup (Quan.Q1) (Term.Var 1) (Term.Var 0)) (Term.Efq))
                  (Term.Mat
                    "Quan.Q0"
                    (Term.Mat
                      "()"
                      (Term.Tup (Quan.Q1) (Term.Lab "Quan.Q0") (Term.Lab "()"))
                      (Term.Efq))
                    (Term.Lam
                      (Quan.Q1)
                      (Term.Lam
                        (Quan.Q1)
                        (Term.Tup (Quan.Q1) (Term.Lab "Quan.Q1") (Term.Lab "()"))))))))))),
    false⟩

def «evalVersion.Eval.meet.of» : Def :=
  ⟨"Eval.meet.of",
    Term.All
      (Quan.Q1)
      (Term.App (Quan.Q0) (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1")) (Term.Ref "Quan"))
      (Term.All
        (Quan.Q1)
        (Term.App
          (Quan.Q0)
          (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
          (Term.Ref "Quan"))
        (Term.App
          (Quan.Q0)
          (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
          (Term.Ref "Term"))),
    Term.Prj
      (Term.Mat
        "Some"
        (Term.Prj
          (Term.Lam
            (Quan.Q1)
            (Term.Mat
              "()"
              (Term.Prj
                (Term.Mat
                  "Some"
                  (Term.Prj
                    (Term.Lam
                      (Quan.Q1)
                      (Term.Mat
                        "()"
                        (Term.Tup
                          (Quan.Q1)
                          (Term.Lab "Some")
                          (Term.Tup
                            (Quan.Q1)
                            (Term.Tup
                              (Quan.Q1)
                              (Term.Lab "Term.Lab")
                              (Term.Tup
                                (Quan.Q1)
                                (Term.App
                                  (Quan.Q1)
                                  (Term.Ref "Quan.name")
                                  (Term.App
                                    (Quan.Q1)
                                    (Term.App (Quan.Q1) (Term.Ref "Quan.min") (Term.Var 1))
                                    (Term.Var 0)))
                                (Term.Lab "()")))
                            (Term.Lab "()")))
                        (Term.Efq))))
                  (Term.Lam
                    (Quan.Q1)
                    (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))))))
              (Term.Efq))))
        (Term.Lam
          (Quan.Q1)
          (Term.Lam
            (Quan.Q1)
            (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()")))))),
    false⟩

def «evalVersion.Eval.meet» : Def :=
  ⟨"Eval.meet",
    Term.All
      (Quan.Q1)
      (Term.Ref "Term")
      (Term.All
        (Quan.Q1)
        (Term.Ref "Term")
        (Term.App
          (Quan.Q0)
          (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
          (Term.Ref "Term"))),
    Term.Prj
      (Term.Mat
        "Term.Lab"
        (Term.Prj
          (Term.Lam
            (Quan.Q1)
            (Term.Mat
              "()"
              (Term.Prj
                (Term.Mat
                  "Term.Lab"
                  (Term.Prj
                    (Term.Lam
                      (Quan.Q1)
                      (Term.Mat
                        "()"
                        (Term.App
                          (Quan.Q1)
                          (Term.App
                            (Quan.Q1)
                            (Term.Ref "Eval.meet.of")
                            (Term.App (Quan.Q2) (Term.Ref "Quan.read") (Term.Var 1)))
                          (Term.App (Quan.Q2) (Term.Ref "Quan.read") (Term.Var 0)))
                        (Term.Efq))))
                  (Term.Lam
                    (Quan.Q1)
                    (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))))))
              (Term.Efq))))
        (Term.Lam
          (Quan.Q1)
          (Term.Lam
            (Quan.Q1)
            (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()")))))),
    false⟩

def «evalVersion.Eval.step.app» : Def :=
  ⟨"Eval.step.app",
    Term.All
      (Quan.Q1)
      (Term.Ref "Quan")
      (Term.All
        (Quan.Q1)
        (Term.Ref "Term")
        (Term.All
          (Quan.Q1)
          (Term.Ref "Term")
          (Term.All
            (Quan.Q1)
            (Term.App
              (Quan.Q0)
              (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
              (Term.Ref "Term"))
            (Term.All
              (Quan.Q1)
              (Term.Ref "Bool")
              (Term.All
                (Quan.Q1)
                (Term.Ref "Bool")
                (Term.All
                  (Quan.Q1)
                  (Term.App
                    (Quan.Q0)
                    (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
                    (Term.Ref "Term"))
                  (Term.All
                    (Quan.Q1)
                    (Term.Ref "Bool")
                    (Term.All
                      (Quan.Q1)
                      (Term.App
                        (Quan.Q0)
                        (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
                        (Term.Ref "Term"))
                      (Term.App
                        (Quan.Q0)
                        (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
                        (Term.Ref "Term")))))))))),
    Term.Lam
      (Quan.Q2)
      (Term.Lam
        (Quan.Q1)
        (Term.Lam
          (Quan.Q1)
          (Term.Prj
            (Term.Mat
              "Some"
              (Term.Prj
                (Term.Lam
                  (Quan.Q1)
                  (Term.Mat
                    "()"
                    (Term.Lam
                      (Quan.Q1)
                      (Term.Lam
                        (Quan.Q1)
                        (Term.Lam
                          (Quan.Q1)
                          (Term.Lam
                            (Quan.Q1)
                            (Term.Lam
                              (Quan.Q1)
                              (Term.Tup
                                (Quan.Q1)
                                (Term.Lab "Some")
                                (Term.Tup
                                  (Quan.Q1)
                                  (Term.Tup
                                    (Quan.Q1)
                                    (Term.Lab "Term.App")
                                    (Term.Tup
                                      (Quan.Q1)
                                      (Term.Var 8)
                                      (Term.Tup
                                        (Quan.Q1)
                                        (Term.Var 5)
                                        (Term.Tup (Quan.Q1) (Term.Var 6) (Term.Lab "()")))))
                                  (Term.Lab "()"))))))))
                    (Term.Efq))))
              (Term.Mat
                "None"
                (Term.Mat
                  "()"
                  (Term.Prj
                    (Term.Mat
                      "False"
                      (Term.Mat
                        "()"
                        (Term.Lam
                          (Quan.Q1)
                          (Term.Lam
                            (Quan.Q1)
                            (Term.Lam
                              (Quan.Q1)
                              (Term.Lam
                                (Quan.Q1)
                                (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))))))
                        (Term.Efq))
                      (Term.Mat
                        "True"
                        (Term.Mat
                          "()"
                          (Term.Prj
                            (Term.Mat
                              "False"
                              (Term.Mat
                                "()"
                                (Term.Lam
                                  (Quan.Q1)
                                  (Term.Lam (Quan.Q1) (Term.Lam (Quan.Q1) (Term.Var 0))))
                                (Term.Efq))
                              (Term.Mat
                                "True"
                                (Term.Mat
                                  "()"
                                  (Term.Prj
                                    (Term.Mat
                                      "Some"
                                      (Term.Prj
                                        (Term.Lam
                                          (Quan.Q1)
                                          (Term.Mat
                                            "()"
                                            (Term.Lam
                                              (Quan.Q1)
                                              (Term.Lam
                                                (Quan.Q1)
                                                (Term.Tup
                                                  (Quan.Q1)
                                                  (Term.Lab "Some")
                                                  (Term.Tup
                                                    (Quan.Q1)
                                                    (Term.Tup
                                                      (Quan.Q1)
                                                      (Term.Lab "Term.App")
                                                      (Term.Tup
                                                        (Quan.Q1)
                                                        (Term.Var 5)
                                                        (Term.Tup
                                                          (Quan.Q1)
                                                          (Term.Var 4)
                                                          (Term.Tup
                                                            (Quan.Q1)
                                                            (Term.Var 2)
                                                            (Term.Lab "()")))))
                                                    (Term.Lab "()")))))
                                            (Term.Efq))))
                                      (Term.Mat
                                        "None"
                                        (Term.Mat
                                          "()"
                                          (Term.Prj
                                            (Term.Mat
                                              "True"
                                              (Term.Mat
                                                "()"
                                                (Term.Lam (Quan.Q1) (Term.Var 0))
                                                (Term.Efq))
                                              (Term.Mat
                                                "False"
                                                (Term.Mat
                                                  "()"
                                                  (Term.Lam
                                                    (Quan.Q1)
                                                    (Term.Tup
                                                      (Quan.Q1)
                                                      (Term.Lab "None")
                                                      (Term.Lab "()")))
                                                  (Term.Efq))
                                                (Term.Efq))))
                                          (Term.Efq))
                                        (Term.Efq))))
                                  (Term.Efq))
                                (Term.Efq))))
                          (Term.Efq))
                        (Term.Efq))))
                  (Term.Efq))
                (Term.Efq)))))),
    false⟩

def «evalVersion.Eval.step.unlet» : Def :=
  ⟨"Eval.step.unlet",
    Term.All
      (Quan.Q1)
      (Term.Ref "Bool")
      (Term.All
        (Quan.Q1)
        (Term.Ref "Term")
        (Term.All
          (Quan.Q1)
          (Term.Ref "Term")
          (Term.App
            (Quan.Q0)
            (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
            (Term.Ref "Term")))),
    Term.Prj
      (Term.Mat
        "True"
        (Term.Mat
          "()"
          (Term.Lam
            (Quan.Q1)
            (Term.Lam
              (Quan.Q1)
              (Term.Tup
                (Quan.Q1)
                (Term.Lab "Some")
                (Term.Tup
                  (Quan.Q1)
                  (Term.App
                    (Quan.Q1)
                    (Term.App (Quan.Q1) (Term.Ref "Term.inst") (Term.Var 1))
                    (Term.Var 0))
                  (Term.Lab "()")))))
          (Term.Efq))
        (Term.Mat
          "False"
          (Term.Mat
            "()"
            (Term.Lam
              (Quan.Q1)
              (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))))
            (Term.Efq))
          (Term.Efq))),
    false⟩

def «evalVersion.Eval.step.let» : Def :=
  ⟨"Eval.step.let",
    Term.All
      (Quan.Q1)
      (Term.Ref "Quan")
      (Term.All
        (Quan.Q1)
        (Term.Ref "Term")
        (Term.All
          (Quan.Q1)
          (Term.Ref "Term")
          (Term.All
            (Quan.Q1)
            (Term.Ref "Bool")
            (Term.All
              (Quan.Q1)
              (Term.App
                (Quan.Q0)
                (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
                (Term.Ref "Term"))
              (Term.All
                (Quan.Q1)
                (Term.Ref "Bool")
                (Term.All
                  (Quan.Q1)
                  (Term.Ref "Bool")
                  (Term.App
                    (Quan.Q0)
                    (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
                    (Term.Ref "Term")))))))),
    Term.Lam
      (Quan.Q1)
      (Term.Lam
        (Quan.Q2)
        (Term.Lam
          (Quan.Q2)
          (Term.Prj
            (Term.Mat
              "False"
              (Term.Mat
                "()"
                (Term.Lam
                  (Quan.Q1)
                  (Term.Lam
                    (Quan.Q1)
                    (Term.Lam
                      (Quan.Q1)
                      (Term.App
                        (Quan.Q1)
                        (Term.App
                          (Quan.Q1)
                          (Term.App (Quan.Q1) (Term.Ref "Eval.step.unlet") (Term.Var 0))
                          (Term.Var 3))
                        (Term.Var 4)))))
                (Term.Efq))
              (Term.Mat
                "True"
                (Term.Mat
                  "()"
                  (Term.Prj
                    (Term.Mat
                      "Some"
                      (Term.Prj
                        (Term.Lam
                          (Quan.Q1)
                          (Term.Mat
                            "()"
                            (Term.Lam
                              (Quan.Q1)
                              (Term.Lam
                                (Quan.Q1)
                                (Term.Tup
                                  (Quan.Q1)
                                  (Term.Lab "Some")
                                  (Term.Tup
                                    (Quan.Q1)
                                    (Term.Tup
                                      (Quan.Q1)
                                      (Term.Lab "Term.Let")
                                      (Term.Tup
                                        (Quan.Q1)
                                        (Term.Var 5)
                                        (Term.Tup
                                          (Quan.Q1)
                                          (Term.Var 2)
                                          (Term.Tup (Quan.Q1) (Term.Var 3) (Term.Lab "()")))))
                                    (Term.Lab "()")))))
                            (Term.Efq))))
                      (Term.Mat
                        "None"
                        (Term.Mat
                          "()"
                          (Term.Prj
                            (Term.Mat
                              "True"
                              (Term.Mat
                                "()"
                                (Term.Lam
                                  (Quan.Q1)
                                  (Term.App
                                    (Quan.Q1)
                                    (Term.App
                                      (Quan.Q1)
                                      (Term.App (Quan.Q1) (Term.Ref "Eval.step.unlet") (Term.Var 0))
                                      (Term.Var 1))
                                    (Term.Var 2)))
                                (Term.Efq))
                              (Term.Mat
                                "False"
                                (Term.Mat
                                  "()"
                                  (Term.Lam
                                    (Quan.Q1)
                                    (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()")))
                                  (Term.Efq))
                                (Term.Efq))))
                          (Term.Efq))
                        (Term.Efq))))
                  (Term.Efq))
                (Term.Efq)))))),
    false⟩

def «evalVersion.Eval.step.tup_b» : Def :=
  ⟨"Eval.step.tup_b",
    Term.All
      (Quan.Q1)
      (Term.Ref "Quan")
      (Term.All
        (Quan.Q1)
        (Term.Ref "Term")
        (Term.All
          (Quan.Q1)
          (Term.App
            (Quan.Q0)
            (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
            (Term.Ref "Term"))
          (Term.App
            (Quan.Q0)
            (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
            (Term.Ref "Term")))),
    Term.Lam
      (Quan.Q1)
      (Term.Lam
        (Quan.Q1)
        (Term.Prj
          (Term.Mat
            "Some"
            (Term.Prj
              (Term.Lam
                (Quan.Q1)
                (Term.Mat
                  "()"
                  (Term.Tup
                    (Quan.Q1)
                    (Term.Lab "Some")
                    (Term.Tup
                      (Quan.Q1)
                      (Term.Tup
                        (Quan.Q1)
                        (Term.Lab "Term.Tup")
                        (Term.Tup
                          (Quan.Q1)
                          (Term.Var 2)
                          (Term.Tup
                            (Quan.Q1)
                            (Term.Var 1)
                            (Term.Tup (Quan.Q1) (Term.Var 0) (Term.Lab "()")))))
                      (Term.Lab "()")))
                  (Term.Efq))))
            (Term.Mat
              "None"
              (Term.Mat "()" (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()")) (Term.Efq))
              (Term.Efq))))),
    false⟩

def «evalVersion.Eval.step.tup» : Def :=
  ⟨"Eval.step.tup",
    Term.All
      (Quan.Q1)
      (Term.Ref "Quan")
      (Term.All
        (Quan.Q1)
        (Term.Ref "Term")
        (Term.All
          (Quan.Q1)
          (Term.Ref "Term")
          (Term.All
            (Quan.Q1)
            (Term.Ref "Bool")
            (Term.All
              (Quan.Q1)
              (Term.App
                (Quan.Q0)
                (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
                (Term.Ref "Term"))
              (Term.All
                (Quan.Q1)
                (Term.Ref "Bool")
                (Term.All
                  (Quan.Q1)
                  (Term.App
                    (Quan.Q0)
                    (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
                    (Term.Ref "Term"))
                  (Term.App
                    (Quan.Q0)
                    (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
                    (Term.Ref "Term")))))))),
    Term.Lam
      (Quan.Q2)
      (Term.Lam
        (Quan.Q2)
        (Term.Lam
          (Quan.Q1)
          (Term.Prj
            (Term.Mat
              "False"
              (Term.Mat
                "()"
                (Term.Lam
                  (Quan.Q1)
                  (Term.Lam
                    (Quan.Q1)
                    (Term.Lam
                      (Quan.Q1)
                      (Term.App
                        (Quan.Q1)
                        (Term.App
                          (Quan.Q1)
                          (Term.App (Quan.Q1) (Term.Ref "Eval.step.tup_b") (Term.Var 5))
                          (Term.Var 4))
                        (Term.Var 0)))))
                (Term.Efq))
              (Term.Mat
                "True"
                (Term.Mat
                  "()"
                  (Term.Prj
                    (Term.Mat
                      "Some"
                      (Term.Prj
                        (Term.Lam
                          (Quan.Q1)
                          (Term.Mat
                            "()"
                            (Term.Lam
                              (Quan.Q1)
                              (Term.Lam
                                (Quan.Q1)
                                (Term.Tup
                                  (Quan.Q1)
                                  (Term.Lab "Some")
                                  (Term.Tup
                                    (Quan.Q1)
                                    (Term.Tup
                                      (Quan.Q1)
                                      (Term.Lab "Term.Tup")
                                      (Term.Tup
                                        (Quan.Q1)
                                        (Term.Var 5)
                                        (Term.Tup
                                          (Quan.Q1)
                                          (Term.Var 2)
                                          (Term.Tup (Quan.Q1) (Term.Var 3) (Term.Lab "()")))))
                                    (Term.Lab "()")))))
                            (Term.Efq))))
                      (Term.Mat
                        "None"
                        (Term.Mat
                          "()"
                          (Term.Prj
                            (Term.Mat
                              "True"
                              (Term.Mat
                                "()"
                                (Term.Lam
                                  (Quan.Q1)
                                  (Term.App
                                    (Quan.Q1)
                                    (Term.App
                                      (Quan.Q1)
                                      (Term.App (Quan.Q1) (Term.Ref "Eval.step.tup_b") (Term.Var 3))
                                      (Term.Var 2))
                                    (Term.Var 0)))
                                (Term.Efq))
                              (Term.Mat
                                "False"
                                (Term.Mat
                                  "()"
                                  (Term.Lam
                                    (Quan.Q1)
                                    (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()")))
                                  (Term.Efq))
                                (Term.Efq))))
                          (Term.Efq))
                        (Term.Efq))))
                  (Term.Efq))
                (Term.Efq)))))),
    false⟩

def «evalVersion.Eval.step.cast» : Def :=
  ⟨"Eval.step.cast",
    Term.All
      (Quan.Q1)
      (Term.Ref "Term")
      (Term.All
        (Quan.Q1)
        (Term.Ref "Term")
        (Term.App
          (Quan.Q0)
          (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
          (Term.Ref "Term"))),
    Term.Prj
      (Term.Mat
        "Term.Rfl"
        (Term.Mat
          "()"
          (Term.Lam
            (Quan.Q1)
            (Term.Tup
              (Quan.Q1)
              (Term.Lab "Some")
              (Term.Tup (Quan.Q1) (Term.Var 0) (Term.Lab "()"))))
          (Term.Efq))
        (Term.Lam
          (Quan.Q1)
          (Term.Lam
            (Quan.Q1)
            (Term.Lam (Quan.Q1) (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()")))))),
    false⟩

def «evalVersion.Eval.step.rwt» : Def :=
  ⟨"Eval.step.rwt",
    Term.All
      (Quan.Q1)
      (Term.Ref "Term")
      (Term.All
        (Quan.Q1)
        (Term.Ref "Term")
        (Term.All
          (Quan.Q1)
          (Term.Ref "Term")
          (Term.All
            (Quan.Q1)
            (Term.App
              (Quan.Q0)
              (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
              (Term.Ref "Term"))
            (Term.All
              (Quan.Q1)
              (Term.Ref "Bool")
              (Term.App
                (Quan.Q0)
                (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
                (Term.Ref "Term")))))),
    Term.Lam
      (Quan.Q1)
      (Term.Lam
        (Quan.Q1)
        (Term.Lam
          (Quan.Q2)
          (Term.Prj
            (Term.Mat
              "Some"
              (Term.Prj
                (Term.Lam
                  (Quan.Q1)
                  (Term.Mat
                    "()"
                    (Term.Lam
                      (Quan.Q1)
                      (Term.Tup
                        (Quan.Q1)
                        (Term.Lab "Some")
                        (Term.Tup
                          (Quan.Q1)
                          (Term.Tup
                            (Quan.Q1)
                            (Term.Lab "Term.Rwt")
                            (Term.Tup
                              (Quan.Q1)
                              (Term.Var 1)
                              (Term.Tup
                                (Quan.Q1)
                                (Term.Var 3)
                                (Term.Tup (Quan.Q1) (Term.Var 2) (Term.Lab "()")))))
                          (Term.Lab "()"))))
                    (Term.Efq))))
              (Term.Mat
                "None"
                (Term.Mat
                  "()"
                  (Term.Prj
                    (Term.Mat
                      "True"
                      (Term.Mat
                        "()"
                        (Term.App
                          (Quan.Q1)
                          (Term.App (Quan.Q1) (Term.Ref "Eval.step.cast") (Term.Var 2))
                          (Term.Var 0))
                        (Term.Efq))
                      (Term.Mat
                        "False"
                        (Term.Mat
                          "()"
                          (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))
                          (Term.Efq))
                        (Term.Efq))))
                  (Term.Efq))
                (Term.Efq)))))),
    false⟩

def «evalVersion.Eval.step.min» : Def :=
  ⟨"Eval.step.min",
    Term.All
      (Quan.Q1)
      (Term.Ref "Term")
      (Term.All
        (Quan.Q1)
        (Term.Ref "Term")
        (Term.All
          (Quan.Q1)
          (Term.App
            (Quan.Q0)
            (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
            (Term.Ref "Term"))
          (Term.All
            (Quan.Q1)
            (Term.Ref "Bool")
            (Term.All
              (Quan.Q1)
              (Term.App
                (Quan.Q0)
                (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
                (Term.Ref "Term"))
              (Term.All
                (Quan.Q1)
                (Term.Ref "Bool")
                (Term.All
                  (Quan.Q1)
                  (Term.App
                    (Quan.Q0)
                    (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
                    (Term.Ref "Term"))
                  (Term.App
                    (Quan.Q0)
                    (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
                    (Term.Ref "Term")))))))),
    Term.Lam
      (Quan.Q1)
      (Term.Lam
        (Quan.Q1)
        (Term.Prj
          (Term.Mat
            "Some"
            (Term.Prj
              (Term.Lam
                (Quan.Q1)
                (Term.Mat
                  "()"
                  (Term.Lam
                    (Quan.Q1)
                    (Term.Lam
                      (Quan.Q1)
                      (Term.Lam
                        (Quan.Q1)
                        (Term.Lam
                          (Quan.Q1)
                          (Term.Tup
                            (Quan.Q1)
                            (Term.Lab "Some")
                            (Term.Tup
                              (Quan.Q1)
                              (Term.Tup
                                (Quan.Q1)
                                (Term.Lab "Term.Min")
                                (Term.Tup
                                  (Quan.Q1)
                                  (Term.Var 4)
                                  (Term.Tup (Quan.Q1) (Term.Var 5) (Term.Lab "()"))))
                              (Term.Lab "()")))))))
                  (Term.Efq))))
            (Term.Mat
              "None"
              (Term.Mat
                "()"
                (Term.Prj
                  (Term.Mat
                    "False"
                    (Term.Mat
                      "()"
                      (Term.Lam
                        (Quan.Q1)
                        (Term.Lam
                          (Quan.Q1)
                          (Term.Lam
                            (Quan.Q1)
                            (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()")))))
                      (Term.Efq))
                    (Term.Mat
                      "True"
                      (Term.Mat
                        "()"
                        (Term.Prj
                          (Term.Mat
                            "Some"
                            (Term.Prj
                              (Term.Lam
                                (Quan.Q1)
                                (Term.Mat
                                  "()"
                                  (Term.Lam
                                    (Quan.Q1)
                                    (Term.Lam
                                      (Quan.Q1)
                                      (Term.Tup
                                        (Quan.Q1)
                                        (Term.Lab "Some")
                                        (Term.Tup
                                          (Quan.Q1)
                                          (Term.Tup
                                            (Quan.Q1)
                                            (Term.Lab "Term.Min")
                                            (Term.Tup
                                              (Quan.Q1)
                                              (Term.Var 4)
                                              (Term.Tup (Quan.Q1) (Term.Var 2) (Term.Lab "()"))))
                                          (Term.Lab "()")))))
                                  (Term.Efq))))
                            (Term.Mat
                              "None"
                              (Term.Mat
                                "()"
                                (Term.Prj
                                  (Term.Mat
                                    "True"
                                    (Term.Mat "()" (Term.Lam (Quan.Q1) (Term.Var 0)) (Term.Efq))
                                    (Term.Mat
                                      "False"
                                      (Term.Mat
                                        "()"
                                        (Term.Lam
                                          (Quan.Q1)
                                          (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()")))
                                        (Term.Efq))
                                      (Term.Efq))))
                                (Term.Efq))
                              (Term.Efq))))
                        (Term.Efq))
                      (Term.Efq))))
                (Term.Efq))
              (Term.Efq))))),
    false⟩

def «evalVersion.Eval.step» : Def :=
  ⟨"Eval.step",
    Term.All
      (Quan.Q2)
      (Term.App (Quan.Q0) (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "Def"))
      (Term.All
        (Quan.Q2)
        (Term.Ref "Term")
        (Term.App
          (Quan.Q0)
          (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
          (Term.Ref "Term"))),
    Term.Lam
      (Quan.Q2)
      (Term.Prj
        (Term.Mat
          "Term.Ann"
          (Term.Prj
            (Term.Lam
              (Quan.Q2)
              (Term.Prj
                (Term.Lam
                  (Quan.Q2)
                  (Term.Mat
                    "()"
                    (Term.Tup
                      (Quan.Q1)
                      (Term.Lab "Some")
                      (Term.Tup (Quan.Q1) (Term.Var 1) (Term.Lab "()")))
                    (Term.Efq))))))
          (Term.Mat
            "Term.Ref"
            (Term.Prj
              (Term.Lam
                (Quan.Q2)
                (Term.Mat
                  "()"
                  (Term.App
                    (Quan.Q2)
                    (Term.App (Quan.Q2) (Term.Ref "Eval.call") (Term.Var 1))
                    (Term.Tup
                      (Quan.Q1)
                      (Term.Lab "Term.Ref")
                      (Term.Tup (Quan.Q1) (Term.Var 0) (Term.Lab "()"))))
                  (Term.Efq))))
            (Term.Mat
              "Term.App"
              (Term.Prj
                (Term.Lam
                  (Quan.Q2)
                  (Term.Prj
                    (Term.Lam
                      (Quan.Q2)
                      (Term.Prj
                        (Term.Lam
                          (Quan.Q2)
                          (Term.Mat
                            "()"
                            (Term.App
                              (Quan.Q1)
                              (Term.App
                                (Quan.Q1)
                                (Term.App
                                  (Quan.Q1)
                                  (Term.App
                                    (Quan.Q1)
                                    (Term.App
                                      (Quan.Q1)
                                      (Term.App
                                        (Quan.Q1)
                                        (Term.App
                                          (Quan.Q1)
                                          (Term.App
                                            (Quan.Q1)
                                            (Term.App
                                              (Quan.Q1)
                                              (Term.Ref "Eval.step.app")
                                              (Term.Var 2))
                                            (Term.Var 1))
                                          (Term.Var 0))
                                        (Term.App
                                          (Quan.Q2)
                                          (Term.App (Quan.Q2) (Term.Ref "Eval.step") (Term.Var 3))
                                          (Term.Var 1)))
                                      (Term.App
                                        (Quan.Q1)
                                        (Term.App
                                          (Quan.Q2)
                                          (Term.App (Quan.Q2) (Term.Ref "Eval.vals") (Term.Var 3))
                                          (Term.Var 1))
                                        (Term.Tup (Quan.Q1) (Term.Lab "False") (Term.Lab "()"))))
                                    (Term.App (Quan.Q1) (Term.Ref "Quan.live") (Term.Var 2)))
                                  (Term.App
                                    (Quan.Q2)
                                    (Term.App (Quan.Q2) (Term.Ref "Eval.step") (Term.Var 3))
                                    (Term.Var 0)))
                                (Term.App
                                  (Quan.Q1)
                                  (Term.App
                                    (Quan.Q2)
                                    (Term.App (Quan.Q2) (Term.Ref "Eval.vals") (Term.Var 3))
                                    (Term.Var 0))
                                  (Term.Tup (Quan.Q1) (Term.Lab "False") (Term.Lab "()"))))
                              (Term.App
                                (Quan.Q2)
                                (Term.App
                                  (Quan.Q2)
                                  (Term.App
                                    (Quan.Q2)
                                    (Term.App (Quan.Q1) (Term.Ref "Eval.redex") (Term.Var 3))
                                    (Term.Var 2))
                                  (Term.Var 1))
                                (Term.Var 0)))
                            (Term.Efq))))))))
              (Term.Mat
                "Term.Let"
                (Term.Prj
                  (Term.Lam
                    (Quan.Q2)
                    (Term.Prj
                      (Term.Lam
                        (Quan.Q2)
                        (Term.Prj
                          (Term.Lam
                            (Quan.Q2)
                            (Term.Mat
                              "()"
                              (Term.App
                                (Quan.Q1)
                                (Term.App
                                  (Quan.Q1)
                                  (Term.App
                                    (Quan.Q1)
                                    (Term.App
                                      (Quan.Q1)
                                      (Term.App
                                        (Quan.Q1)
                                        (Term.App
                                          (Quan.Q1)
                                          (Term.App
                                            (Quan.Q1)
                                            (Term.Ref "Eval.step.let")
                                            (Term.Var 2))
                                          (Term.Var 1))
                                        (Term.Var 0))
                                      (Term.App (Quan.Q1) (Term.Ref "Quan.live") (Term.Var 2)))
                                    (Term.App
                                      (Quan.Q2)
                                      (Term.App (Quan.Q2) (Term.Ref "Eval.step") (Term.Var 3))
                                      (Term.Var 1)))
                                  (Term.App
                                    (Quan.Q1)
                                    (Term.App
                                      (Quan.Q2)
                                      (Term.App (Quan.Q2) (Term.Ref "Eval.vals") (Term.Var 3))
                                      (Term.Var 1))
                                    (Term.Tup (Quan.Q1) (Term.Lab "False") (Term.Lab "()"))))
                                (Term.App
                                  (Quan.Q1)
                                  (Term.App (Quan.Q1) (Term.Ref "Quan.fits") (Term.Var 2))
                                  (Term.Var 1)))
                              (Term.Efq))))))))
                (Term.Mat
                  "Term.Tup"
                  (Term.Prj
                    (Term.Lam
                      (Quan.Q2)
                      (Term.Prj
                        (Term.Lam
                          (Quan.Q2)
                          (Term.Prj
                            (Term.Lam
                              (Quan.Q2)
                              (Term.Mat
                                "()"
                                (Term.App
                                  (Quan.Q1)
                                  (Term.App
                                    (Quan.Q1)
                                    (Term.App
                                      (Quan.Q1)
                                      (Term.App
                                        (Quan.Q1)
                                        (Term.App
                                          (Quan.Q1)
                                          (Term.App
                                            (Quan.Q1)
                                            (Term.App
                                              (Quan.Q1)
                                              (Term.Ref "Eval.step.tup")
                                              (Term.Var 2))
                                            (Term.Var 1))
                                          (Term.Var 0))
                                        (Term.App (Quan.Q1) (Term.Ref "Quan.live") (Term.Var 2)))
                                      (Term.App
                                        (Quan.Q2)
                                        (Term.App (Quan.Q2) (Term.Ref "Eval.step") (Term.Var 3))
                                        (Term.Var 1)))
                                    (Term.App
                                      (Quan.Q1)
                                      (Term.App
                                        (Quan.Q2)
                                        (Term.App (Quan.Q2) (Term.Ref "Eval.vals") (Term.Var 3))
                                        (Term.Var 1))
                                      (Term.Tup (Quan.Q1) (Term.Lab "False") (Term.Lab "()"))))
                                  (Term.App
                                    (Quan.Q2)
                                    (Term.App (Quan.Q2) (Term.Ref "Eval.step") (Term.Var 3))
                                    (Term.Var 0)))
                                (Term.Efq))))))))
                  (Term.Mat
                    "Term.Rwt"
                    (Term.Prj
                      (Term.Lam
                        (Quan.Q2)
                        (Term.Prj
                          (Term.Lam
                            (Quan.Q2)
                            (Term.Prj
                              (Term.Lam
                                (Quan.Q2)
                                (Term.Mat
                                  "()"
                                  (Term.App
                                    (Quan.Q1)
                                    (Term.App
                                      (Quan.Q1)
                                      (Term.App
                                        (Quan.Q1)
                                        (Term.App
                                          (Quan.Q1)
                                          (Term.App
                                            (Quan.Q1)
                                            (Term.Ref "Eval.step.rwt")
                                            (Term.Var 2))
                                          (Term.Var 1))
                                        (Term.Var 0))
                                      (Term.App
                                        (Quan.Q2)
                                        (Term.App (Quan.Q2) (Term.Ref "Eval.step") (Term.Var 3))
                                        (Term.Var 2)))
                                    (Term.App
                                      (Quan.Q1)
                                      (Term.App
                                        (Quan.Q2)
                                        (Term.App (Quan.Q2) (Term.Ref "Eval.vals") (Term.Var 3))
                                        (Term.Var 2))
                                      (Term.Tup (Quan.Q1) (Term.Lab "False") (Term.Lab "()"))))
                                  (Term.Efq))))))))
                    (Term.Mat
                      "Term.Min"
                      (Term.Prj
                        (Term.Lam
                          (Quan.Q2)
                          (Term.Prj
                            (Term.Lam
                              (Quan.Q2)
                              (Term.Mat
                                "()"
                                (Term.App
                                  (Quan.Q1)
                                  (Term.App
                                    (Quan.Q1)
                                    (Term.App
                                      (Quan.Q1)
                                      (Term.App
                                        (Quan.Q1)
                                        (Term.App
                                          (Quan.Q1)
                                          (Term.App
                                            (Quan.Q1)
                                            (Term.App
                                              (Quan.Q1)
                                              (Term.Ref "Eval.step.min")
                                              (Term.Var 1))
                                            (Term.Var 0))
                                          (Term.App
                                            (Quan.Q2)
                                            (Term.App (Quan.Q2) (Term.Ref "Eval.step") (Term.Var 2))
                                            (Term.Var 1)))
                                        (Term.App
                                          (Quan.Q1)
                                          (Term.App
                                            (Quan.Q2)
                                            (Term.App (Quan.Q2) (Term.Ref "Eval.vals") (Term.Var 2))
                                            (Term.Var 1))
                                          (Term.Tup (Quan.Q1) (Term.Lab "False") (Term.Lab "()"))))
                                      (Term.App
                                        (Quan.Q2)
                                        (Term.App (Quan.Q2) (Term.Ref "Eval.step") (Term.Var 2))
                                        (Term.Var 0)))
                                    (Term.App
                                      (Quan.Q1)
                                      (Term.App
                                        (Quan.Q2)
                                        (Term.App (Quan.Q2) (Term.Ref "Eval.vals") (Term.Var 2))
                                        (Term.Var 0))
                                      (Term.Tup (Quan.Q1) (Term.Lab "False") (Term.Lab "()"))))
                                  (Term.App
                                    (Quan.Q1)
                                    (Term.App (Quan.Q1) (Term.Ref "Eval.meet") (Term.Var 1))
                                    (Term.Var 0)))
                                (Term.Efq))))))
                      (Term.Lam
                        (Quan.Q2)
                        (Term.Lam
                          (Quan.Q2)
                          (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()")))))))))))),
    false⟩

def «evalVersion.Eval.run» : Def :=
  ⟨"Eval.run",
    Term.All
      (Quan.Q1)
      (Term.Ref "Nat")
      (Term.All
        (Quan.Q2)
        (Term.App (Quan.Q0) (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "Def"))
        (Term.All
          (Quan.Q1)
          (Term.App
            (Quan.Q0)
            (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
            (Term.Ref "Term"))
          (Term.App
            (Quan.Q0)
            (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
            (Term.Ref "Term")))),
    Term.Prj
      (Term.Mat
        "Zero"
        (Term.Mat "()" (Term.Lam (Quan.Q2) (Term.Lam (Quan.Q1) (Term.Var 0))) (Term.Efq))
        (Term.Mat
          "Succ"
          (Term.Prj
            (Term.Lam
              (Quan.Q1)
              (Term.Mat
                "()"
                (Term.Lam
                  (Quan.Q2)
                  (Term.Prj
                    (Term.Mat
                      "None"
                      (Term.Mat
                        "()"
                        (Term.Tup (Quan.Q1) (Term.Lab "None") (Term.Lab "()"))
                        (Term.Efq))
                      (Term.Mat
                        "Some"
                        (Term.Prj
                          (Term.Lam
                            (Quan.Q1)
                            (Term.Mat
                              "()"
                              (Term.App
                                (Quan.Q1)
                                (Term.App
                                  (Quan.Q2)
                                  (Term.App (Quan.Q1) (Term.Ref "Eval.run") (Term.Var 2))
                                  (Term.Var 1))
                                (Term.App
                                  (Quan.Q2)
                                  (Term.App (Quan.Q2) (Term.Ref "Eval.step") (Term.Var 1))
                                  (Term.Var 0)))
                              (Term.Efq))))
                        (Term.Efq)))))
                (Term.Efq))))
          (Term.Efq))),
    false⟩

def «evalVersion.Eval.steps» : Def :=
  ⟨"Eval.steps",
    Term.All
      (Quan.Q1)
      (Term.Ref "Nat")
      (Term.All
        (Quan.Q1)
        (Term.App (Quan.Q0) (Term.App (Quan.Q0) (Term.Ref "List") (Term.Lab "Q2")) (Term.Ref "Def"))
        (Term.All
          (Quan.Q1)
          (Term.Ref "Term")
          (Term.App
            (Quan.Q0)
            (Term.App (Quan.Q0) (Term.Ref "Maybe") (Term.Lab "Q1"))
            (Term.Ref "Term")))),
    Term.Lam
      (Quan.Q1)
      (Term.Lam
        (Quan.Q1)
        (Term.Lam
          (Quan.Q1)
          (Term.App
            (Quan.Q1)
            (Term.App
              (Quan.Q2)
              (Term.App (Quan.Q1) (Term.Ref "Eval.run") (Term.Var 2))
              (Term.Var 1))
            (Term.Tup
              (Quan.Q1)
              (Term.Lab "Some")
              (Term.Tup (Quan.Q1) (Term.Var 0) (Term.Lab "()")))))),
    false⟩

def «evalVersion.U32.arms» : Def :=
  ⟨"U32.arms",
    Term.All (Quan.Q1) (Term.Enu ["U32"]) (Term.Typ (Term.Lab "Q2")),
    Term.Mat
      "U32"
      (Term.Sig
        (Quan.Q1)
        (Term.App
          (Quan.Q1)
          (Term.Ref "Word")
          (Term.Tup
            (Quan.Q1)
            (Term.Lab "Succ")
            (Term.Tup
              (Quan.Q1)
              (Term.Tup
                (Quan.Q1)
                (Term.Lab "Succ")
                (Term.Tup
                  (Quan.Q1)
                  (Term.Tup
                    (Quan.Q1)
                    (Term.Lab "Succ")
                    (Term.Tup
                      (Quan.Q1)
                      (Term.Tup
                        (Quan.Q1)
                        (Term.Lab "Succ")
                        (Term.Tup
                          (Quan.Q1)
                          (Term.Tup
                            (Quan.Q1)
                            (Term.Lab "Succ")
                            (Term.Tup
                              (Quan.Q1)
                              (Term.Tup
                                (Quan.Q1)
                                (Term.Lab "Succ")
                                (Term.Tup
                                  (Quan.Q1)
                                  (Term.Tup
                                    (Quan.Q1)
                                    (Term.Lab "Succ")
                                    (Term.Tup
                                      (Quan.Q1)
                                      (Term.Tup
                                        (Quan.Q1)
                                        (Term.Lab "Succ")
                                        (Term.Tup
                                          (Quan.Q1)
                                          (Term.Tup
                                            (Quan.Q1)
                                            (Term.Lab "Succ")
                                            (Term.Tup
                                              (Quan.Q1)
                                              (Term.Tup
                                                (Quan.Q1)
                                                (Term.Lab "Succ")
                                                (Term.Tup
                                                  (Quan.Q1)
                                                  (Term.Tup
                                                    (Quan.Q1)
                                                    (Term.Lab "Succ")
                                                    (Term.Tup
                                                      (Quan.Q1)
                                                      (Term.Tup
                                                        (Quan.Q1)
                                                        (Term.Lab "Succ")
                                                        (Term.Tup
                                                          (Quan.Q1)
                                                          (Term.Tup
                                                            (Quan.Q1)
                                                            (Term.Lab "Succ")
                                                            (Term.Tup
                                                              (Quan.Q1)
                                                              (Term.Tup
                                                                (Quan.Q1)
                                                                (Term.Lab "Succ")
                                                                (Term.Tup
                                                                  (Quan.Q1)
                                                                  (Term.Tup
                                                                    (Quan.Q1)
                                                                    (Term.Lab "Succ")
                                                                    (Term.Tup
                                                                      (Quan.Q1)
                                                                      (Term.Tup
                                                                        (Quan.Q1)
                                                                        (Term.Lab "Succ")
                                                                        (Term.Tup
                                                                          (Quan.Q1)
                                                                          (Term.Tup
                                                                            (Quan.Q1)
                                                                            (Term.Lab "Succ")
                                                                            (Term.Tup
                                                                              (Quan.Q1)
                                                                              (Term.Tup
                                                                                (Quan.Q1)
                                                                                (Term.Lab "Succ")
                                                                                (Term.Tup
                                                                                  (Quan.Q1)
                                                                                  (Term.Tup
                                                                                    (Quan.Q1)
                                                                                    (Term.Lab
                                                                                      "Succ")
                                                                                    (Term.Tup
                                                                                      (Quan.Q1)
                                                                                      (Term.Tup
                                                                                        (Quan.Q1)
                                                                                        (Term.Lab
                                                                                          "Succ")
                                                                                        (Term.Tup
                                                                                          (Quan.Q1)
                                                                                          (Term.Tup
                                                                                            (Quan.Q1)
                                                                                            (Term.Lab
                                                                                              "Succ")
                                                                                            (Term.Tup
                                                                                              (Quan.Q1)
                                                                                              (Term.Tup
                                                                                                (Quan.Q1)
                                                                                                (Term.Lab
                                                                                                  "Succ")
                                                                                                (Term.Tup
                                                                                                  (Quan.Q1)
                                                                                                  (Term.Tup
                                                                                                    (Quan.Q1)
                                                                                                    (Term.Lab
                                                                                                      "Succ")
                                                                                                    (Term.Tup
                                                                                                      (Quan.Q1)
                                                                                                      (Term.Tup
                                                                                                        (Quan.Q1)
                                                                                                        (Term.Lab
                                                                                                          "Succ")
                                                                                                        (Term.Tup
                                                                                                          (Quan.Q1)
                                                                                                          (Term.Tup
                                                                                                            (Quan.Q1)
                                                                                                            (Term.Lab
                                                                                                              "Succ")
                                                                                                            (Term.Tup
                                                                                                              (Quan.Q1)
                                                                                                              (Term.Tup
                                                                                                                (Quan.Q1)
                                                                                                                (Term.Lab
                                                                                                                  "Succ")
                                                                                                                (Term.Tup
                                                                                                                  (Quan.Q1)
                                                                                                                  (Term.Tup
                                                                                                                    (Quan.Q1)
                                                                                                                    (Term.Lab
                                                                                                                      "Succ")
                                                                                                                    (Term.Tup
                                                                                                                      (Quan.Q1)
                                                                                                                      (Term.Tup
                                                                                                                        (Quan.Q1)
                                                                                                                        (Term.Lab
                                                                                                                          "Succ")
                                                                                                                        (Term.Tup
                                                                                                                          (Quan.Q1)
                                                                                                                          (Term.Tup
                                                                                                                            (Quan.Q1)
                                                                                                                            (Term.Lab
                                                                                                                              "Succ")
                                                                                                                            (Term.Tup
                                                                                                                              (Quan.Q1)
                                                                                                                              (Term.Tup
                                                                                                                                (Quan.Q1)
                                                                                                                                (Term.Lab
                                                                                                                                  "Succ")
                                                                                                                                (Term.Tup
                                                                                                                                  (Quan.Q1)
                                                                                                                                  (Term.Tup
                                                                                                                                    (Quan.Q1)
                                                                                                                                    (Term.Lab
                                                                                                                                      "Succ")
                                                                                                                                    (Term.Tup
                                                                                                                                      (Quan.Q1)
                                                                                                                                      (Term.Tup
                                                                                                                                        (Quan.Q1)
                                                                                                                                        (Term.Lab
                                                                                                                                          "Succ")
                                                                                                                                        (Term.Tup
                                                                                                                                          (Quan.Q1)
                                                                                                                                          (Term.Tup
                                                                                                                                            (Quan.Q1)
                                                                                                                                            (Term.Lab
                                                                                                                                              "Zero")
                                                                                                                                            (Term.Lab
                                                                                                                                              "()"))
                                                                                                                                          (Term.Lab
                                                                                                                                            "()")))
                                                                                                                                      (Term.Lab
                                                                                                                                        "()")))
                                                                                                                                  (Term.Lab
                                                                                                                                    "()")))
                                                                                                                              (Term.Lab
                                                                                                                                "()")))
                                                                                                                          (Term.Lab
                                                                                                                            "()")))
                                                                                                                      (Term.Lab
                                                                                                                        "()")))
                                                                                                                  (Term.Lab
                                                                                                                    "()")))
                                                                                                              (Term.Lab
                                                                                                                "()")))
                                                                                                          (Term.Lab
                                                                                                            "()")))
                                                                                                      (Term.Lab
                                                                                                        "()")))
                                                                                                  (Term.Lab
                                                                                                    "()")))
                                                                                              (Term.Lab
                                                                                                "()")))
                                                                                          (Term.Lab
                                                                                            "()")))
                                                                                      (Term.Lab
                                                                                        "()")))
                                                                                  (Term.Lab "()")))
                                                                              (Term.Lab "()")))
                                                                          (Term.Lab "()")))
                                                                      (Term.Lab "()")))
                                                                  (Term.Lab "()")))
                                                              (Term.Lab "()")))
                                                          (Term.Lab "()")))
                                                      (Term.Lab "()")))
                                                  (Term.Lab "()")))
                                              (Term.Lab "()")))
                                          (Term.Lab "()")))
                                      (Term.Lab "()")))
                                  (Term.Lab "()")))
                              (Term.Lab "()")))
                          (Term.Lab "()")))
                      (Term.Lab "()")))
                  (Term.Lab "()")))
              (Term.Lab "()"))))
        (Term.Enu ["()"]))
      (Term.Efq),
    false⟩

def «evalVersion.U32» : Def :=
  ⟨"U32",
    Term.Typ (Term.Lab "Q2"),
    Term.Sig (Quan.Q1) (Term.Enu ["U32"]) (Term.App (Quan.Q1) (Term.Ref "U32.arms") (Term.Var 0)),
    false⟩

def «evalVersion.Cmp.arms» : Def :=
  ⟨"Cmp.arms",
    Term.All (Quan.Q1) (Term.Enu ["LT", "EQ", "GT"]) (Term.Typ (Term.Lab "Q2")),
    Term.Mat
      "LT"
      (Term.Enu ["()"])
      (Term.Mat "EQ" (Term.Enu ["()"]) (Term.Mat "GT" (Term.Enu ["()"]) (Term.Efq))),
    false⟩

def «evalVersion.Cmp» : Def :=
  ⟨"Cmp",
    Term.Typ (Term.Lab "Q2"),
    Term.Sig
      (Quan.Q1)
      (Term.Enu ["LT", "EQ", "GT"])
      (Term.App (Quan.Q1) (Term.Ref "Cmp.arms") (Term.Var 0)),
    false⟩

def «evalVersion.Maybe.arms» : Def :=
  ⟨"Maybe.arms",
    Term.All
      (Quan.Q0)
      (Term.Enu ["Q0", "Q1", "Q2"])
      (Term.All
        (Quan.Q0)
        (Term.Typ (Term.Var 0))
        (Term.All (Quan.Q1) (Term.Enu ["None", "Some"]) (Term.Typ (Term.Var 2)))),
    Term.Lam
      (Quan.Q0)
      (Term.Lam
        (Quan.Q0)
        (Term.Mat
          "None"
          (Term.Enu ["()"])
          (Term.Mat "Some" (Term.Sig (Quan.Q1) (Term.Var 0) (Term.Enu ["()"])) (Term.Efq)))),
    false⟩

def «evalVersion.Maybe» : Def :=
  ⟨"Maybe",
    Term.All
      (Quan.Q0)
      (Term.Enu ["Q0", "Q1", "Q2"])
      (Term.All (Quan.Q0) (Term.Typ (Term.Var 0)) (Term.Typ (Term.Var 1))),
    Term.Lam
      (Quan.Q0)
      (Term.Lam
        (Quan.Q0)
        (Term.Sig
          (Quan.Q1)
          (Term.Enu ["None", "Some"])
          (Term.App
            (Quan.Q1)
            (Term.App
              (Quan.Q0)
              (Term.App (Quan.Q0) (Term.Ref "Maybe.arms") (Term.Var 2))
              (Term.Var 1))
            (Term.Var 0)))),
    false⟩

def «evalVersion.Bool.arms» : Def :=
  ⟨"Bool.arms",
    Term.All (Quan.Q1) (Term.Enu ["False", "True"]) (Term.Typ (Term.Lab "Q2")),
    Term.Mat "False" (Term.Enu ["()"]) (Term.Mat "True" (Term.Enu ["()"]) (Term.Efq)),
    false⟩

def «evalVersion.Bool» : Def :=
  ⟨"Bool",
    Term.Typ (Term.Lab "Q2"),
    Term.Sig
      (Quan.Q1)
      (Term.Enu ["False", "True"])
      (Term.App (Quan.Q1) (Term.Ref "Bool.arms") (Term.Var 0)),
    false⟩

def «evalVersion.Nat.arms» : Def :=
  ⟨"Nat.arms",
    Term.All (Quan.Q1) (Term.Enu ["Zero", "Succ"]) (Term.Typ (Term.Lab "Q2")),
    Term.Mat
      "Zero"
      (Term.Enu ["()"])
      (Term.Mat "Succ" (Term.Sig (Quan.Q1) (Term.Ref "Nat") (Term.Enu ["()"])) (Term.Efq)),
    false⟩

def «evalVersion.Nat» : Def :=
  ⟨"Nat",
    Term.Typ (Term.Lab "Q2"),
    Term.Sig
      (Quan.Q1)
      (Term.Enu ["Zero", "Succ"])
      (Term.App (Quan.Q1) (Term.Ref "Nat.arms") (Term.Var 0)),
    false⟩

def «evalVersion.Word.Nil.arms» : Def :=
  ⟨"Word.Nil.arms",
    Term.All (Quan.Q1) (Term.Enu ["WNil"]) (Term.Typ (Term.Lab "Q2")),
    Term.Mat "WNil" (Term.Enu ["()"]) (Term.Efq),
    false⟩

def «evalVersion.Word.Nil» : Def :=
  ⟨"Word.Nil",
    Term.Typ (Term.Lab "Q2"),
    Term.Sig (Quan.Q1) (Term.Enu ["WNil"]) (Term.App (Quan.Q1) (Term.Ref "Word.Nil.arms") (Term.Var 0)),
    false⟩

def «evalVersion.Word.Con.arms» : Def :=
  ⟨"Word.Con.arms",
    Term.All
      (Quan.Q0)
      (Term.Ref "Nat")
      (Term.All (Quan.Q1) (Term.Enu ["WCon"]) (Term.Typ (Term.Lab "Q2"))),
    Term.Lam
      (Quan.Q0)
      (Term.Mat
        "WCon"
        (Term.Sig
          (Quan.Q1)
          (Term.Ref "Bool")
          (Term.Sig
            (Quan.Q1)
            (Term.App (Quan.Q1) (Term.Ref "Word") (Term.Var 1))
            (Term.Enu ["()"])))
        (Term.Efq)),
    false⟩

def «evalVersion.Word.Con» : Def :=
  ⟨"Word.Con",
    Term.All (Quan.Q0) (Term.Ref "Nat") (Term.Typ (Term.Lab "Q2")),
    Term.Lam
      (Quan.Q0)
      (Term.Sig
        (Quan.Q1)
        (Term.Enu ["WCon"])
        (Term.App
          (Quan.Q1)
          (Term.App (Quan.Q0) (Term.Ref "Word.Con.arms") (Term.Var 1))
          (Term.Var 0))),
    false⟩

def «evalVersion.Word» : Def :=
  ⟨"Word",
    Term.All (Quan.Q1) (Term.Ref "Nat") (Term.Typ (Term.Lab "Q2")),
    Term.Prj
      (Term.Mat
        "Zero"
        (Term.Mat "()" (Term.Ref "Word.Nil") (Term.Efq))
        (Term.Mat
          "Succ"
          (Term.Prj
            (Term.Lam
              (Quan.Q1)
              (Term.Mat "()" (Term.App (Quan.Q0) (Term.Ref "Word.Con") (Term.Var 0)) (Term.Efq))))
          (Term.Efq))),
    false⟩

def «evalVersion.List.arms» : Def :=
  ⟨"List.arms",
    Term.All
      (Quan.Q0)
      (Term.Enu ["Q0", "Q1", "Q2"])
      (Term.All
        (Quan.Q0)
        (Term.Typ (Term.Var 0))
        (Term.All (Quan.Q1) (Term.Enu ["Nil", "Con"]) (Term.Typ (Term.Var 2)))),
    Term.Lam
      (Quan.Q0)
      (Term.Lam
        (Quan.Q0)
        (Term.Mat
          "Nil"
          (Term.Enu ["()"])
          (Term.Mat
            "Con"
            (Term.Sig
              (Quan.Q1)
              (Term.Var 0)
              (Term.Sig
                (Quan.Q1)
                (Term.App
                  (Quan.Q0)
                  (Term.App (Quan.Q0) (Term.Ref "List") (Term.Var 2))
                  (Term.Var 1))
                (Term.Enu ["()"])))
            (Term.Efq)))),
    false⟩

def «evalVersion.List» : Def :=
  ⟨"List",
    Term.All
      (Quan.Q0)
      (Term.Enu ["Q0", "Q1", "Q2"])
      (Term.All (Quan.Q0) (Term.Typ (Term.Var 0)) (Term.Typ (Term.Var 1))),
    Term.Lam
      (Quan.Q0)
      (Term.Lam
        (Quan.Q0)
        (Term.Sig
          (Quan.Q1)
          (Term.Enu ["Nil", "Con"])
          (Term.App
            (Quan.Q1)
            (Term.App
              (Quan.Q0)
              (Term.App (Quan.Q0) (Term.Ref "List.arms") (Term.Var 2))
              (Term.Var 1))
            (Term.Var 0)))),
    false⟩

def evalVersion : List Def :=
  [«evalVersion.Quan.arms»,
   «evalVersion.Quan»,
   «evalVersion.Term.arms»,
   «evalVersion.Term»,
   «evalVersion.Def.arms»,
   «evalVersion.Def»,
   «evalVersion.Word.low»,
   «evalVersion.Byte.from_u32»,
   «evalVersion.Cmp.is_eq»,
   «evalVersion.Bool.cmp»,
   «evalVersion.Word.cmp.fin»,
   «evalVersion.Word.cmp»,
   «evalVersion.Byte.is_eq»,
   «evalVersion.Bool.and»,
   «evalVersion.Name.is_eq»,
   «evalVersion.Bool.or»,
   «evalVersion.Cmp.is_lt»,
   «evalVersion.Nat.sub»,
   «evalVersion.Bool.not»,
   «evalVersion.Nat.cmp»,
   «evalVersion.Nat.add»,
   «evalVersion.Nat.is_lt»,
   «evalVersion.Arg.arms»,
   «evalVersion.Arg»,
   «evalVersion.Quan.live»,
   «evalVersion.Quan.lives_as»,
   «evalVersion.Quan.fld»,
   «evalVersion.Term.is_data»,
   «evalVersion.Quan.fits»,
   «evalVersion.Quan.binds»,
   «evalVersion.Term.is_former»,
   «evalVersion.Term.takes»,
   «evalVersion.Term.head»,
   «evalVersion.Term.args»,
   «evalVersion.Term.spine»,
   «evalVersion.Env.sub»,
   «evalVersion.Term.shift.at»,
   «evalVersion.Term.shift»,
   «evalVersion.Term.lift.at»,
   «evalVersion.Term.lift»,
   «evalVersion.Term.subst»,
   «evalVersion.Term.inst»,
   «evalVersion.Book.get.if»,
   «evalVersion.Book.get»,
   «evalVersion.Eval.walk.if»,
   «evalVersion.Eval.walk.pick»,
   «evalVersion.Eval.walk.app»,
   «evalVersion.Eval.walk.leaf»,
   «evalVersion.Eval.walk»,
   «evalVersion.Eval.callWalk.def»,
   «evalVersion.Eval.callWalk.head»,
   «evalVersion.Eval.callWalk»,
   «evalVersion.Eval.waits»,
   «evalVersion.Eval.vals.app»,
   «evalVersion.Eval.vals.ref»,
   «evalVersion.Eval.vals.other»,
   «evalVersion.Eval.vals»,
   «evalVersion.Eval.call.if»,
   «evalVersion.Eval.call»,
   «evalVersion.Eval.redex.if»,
   «evalVersion.Eval.redex.pick»,
   «evalVersion.Eval.redex»,
   «evalVersion.Quan.read.if»,
   «evalVersion.U32.lit81»,
   «evalVersion.U32.lit48»,
   «evalVersion.U32.lit49»,
   «evalVersion.U32.lit50»,
   «evalVersion.Quan.name»,
   «evalVersion.Quan.read»,
   «evalVersion.Quan.min»,
   «evalVersion.Eval.meet.of»,
   «evalVersion.Eval.meet»,
   «evalVersion.Eval.step.app»,
   «evalVersion.Eval.step.unlet»,
   «evalVersion.Eval.step.let»,
   «evalVersion.Eval.step.tup_b»,
   «evalVersion.Eval.step.tup»,
   «evalVersion.Eval.step.cast»,
   «evalVersion.Eval.step.rwt»,
   «evalVersion.Eval.step.min»,
   «evalVersion.Eval.step»,
   «evalVersion.Eval.run»,
   «evalVersion.Eval.steps»,
   «evalVersion.U32.arms»,
   «evalVersion.U32»,
   «evalVersion.Cmp.arms»,
   «evalVersion.Cmp»,
   «evalVersion.Maybe.arms»,
   «evalVersion.Maybe»,
   «evalVersion.Bool.arms»,
   «evalVersion.Bool»,
   «evalVersion.Nat.arms»,
   «evalVersion.Nat»,
   «evalVersion.Word.Nil.arms»,
   «evalVersion.Word.Nil»,
   «evalVersion.Word.Con.arms»,
   «evalVersion.Word.Con»,
   «evalVersion.Word»,
   «evalVersion.List.arms»,
   «evalVersion.List»]
