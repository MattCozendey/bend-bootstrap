;; Invalid
;; =======
;;
;; Tests of kind b (bend2 skill): the Bend version of WASM against the spec,
;; for the rules of validation and decoding that no official test of the
;; pinned commit reaches: their official modules also use instructions outside
;; the subset, which the model refuses first (AGENTS.md 3.9.1.3). Each module
;; here is otherwise inside the subset and breaks exactly one rule, so only that
;; rule can refuse it. A law cannot state them: we know of no Lean or Bend
;; version of the spec. Each expected result is the spec's (convert.ts).

;; br needs its label's values: 1 for the function's label here.
(assert_invalid (module (func (result i32) (br 0))) "type mismatch")

;; br_if needs its label's values and the condition.
(assert_invalid (module (func (result i32) i32.const 0 br_if 0 i32.const 1)) "type mismatch")

;; A local's index is below the number of locals.
(assert_invalid (module (func (param i32) (result i32) (local.get 1))) "unknown local")

;; A load needs a memory.
(assert_invalid (module (func (result i32) (i32.load (i32.const 0)))) "unknown memory")

;; A store needs a memory.
(assert_invalid (module (func (i32.store (i32.const 0) (i32.const 0)))) "unknown memory")

;; A binary operator needs 2 operands.
(assert_invalid (module (func (result i32) i32.const 1 i32.add i32.const 2)) "type mismatch")

;; The last byte of i32.const's signed LEB128 repeats its sign bit in its
;; unused bits: here 0x0f, which has them 0 under a sign bit of 1.
(assert_malformed
  (module binary
    "\00asm" "\01\00\00\00"
    "\01\05\01\60\00\01\7f"
    "\03\02\01\00"
    "\0a\0a\01\08\00\41\ff\ff\ff\ff\0f\0b")
  "integer")

;; A function's code takes exactly the bytes of its code entry: here one more
;; byte after its end.
(assert_malformed
  (module binary
    "\00asm" "\01\00\00\00"
    "\01\05\01\60\00\01\7f"
    "\03\02\01\00"
    "\0a\07\01\05\00\41\00\0b\0b")
  "section size mismatch")

;; A name is UTF-8: here the export's name is the byte 0xff.
(assert_malformed
  (module binary
    "\00asm" "\01\00\00\00"
    "\01\05\01\60\00\01\7f"
    "\03\02\01\00"
    "\07\05\01\01\ff\00\00"
    "\0a\06\01\04\00\41\00\0b")
  "malformed UTF-8 encoding")
