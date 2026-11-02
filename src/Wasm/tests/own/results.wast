;; Results
;; =======
;;
;; Tests of kind b (bend2 skill): the Bend version of WASM against the spec,
;; for functions with more than one result, which the model takes and no
;; official test of the pinned commit runs inside the subset (AGENTS.md
;; 3.9.1.3). A law cannot state them: we know of no Lean or Bend version of the
;; spec. Each expected result is the spec's (convert.ts).

(module
  (func (export "two") (result i32 i32) (i32.const 1) (i32.const 2))
  (func (export "three") (result i32 i32 i32) (i32.const 1) (i32.const 2) (i32.const 3))
  (func (export "swap") (param i32 i32) (result i32 i32) (local.get 1) (local.get 0))
  ;; br to the function's label takes the values on top, and drops the 9 under them
  (func (export "br") (result i32 i32) (i32.const 9) (i32.const 1) (i32.const 2) (br 0))
  ;; br_if to the function's label, taken or not
  (func (export "br_if") (param i32) (result i32 i32)
    (i32.const 1) (i32.const 2) (local.get 0) (br_if 0))
)

;; A function gives its results in order, the first result first.
(assert_return (invoke "two") (i32.const 1) (i32.const 2))
(assert_return (invoke "three") (i32.const 1) (i32.const 2) (i32.const 3))
(assert_return (invoke "swap" (i32.const 1) (i32.const 2)) (i32.const 2) (i32.const 1))
(assert_return (invoke "br") (i32.const 1) (i32.const 2))
(assert_return (invoke "br_if" (i32.const 0)) (i32.const 1) (i32.const 2))
(assert_return (invoke "br_if" (i32.const 1)) (i32.const 1) (i32.const 2))

;; A function's body ends with exactly its results.
(assert_invalid (module (func (result i32 i32) (i32.const 1))) "type mismatch")
(assert_invalid (module (func (result i32 i32) (i32.const 1) (i32.const 2) (i32.const 3))) "type mismatch")
