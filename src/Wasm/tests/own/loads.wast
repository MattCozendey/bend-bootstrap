;; Loads
;; =====
;;
;; Tests of kind b (bend2 skill): the Bend version of WASM against the spec,
;; for the offsets of loads that the compiler emits and that no official test
;; of the pinned commit runs (AGENTS.md 3.9.1.3). A law cannot state them: we
;; know of no Lean or Bend version of the spec. Each expected result is the
;; spec's (convert.ts).

(module
  (memory 1)
  (func (export "store") (param i32 i32) (i32.store (local.get 0) (local.get 1)))
  (func (export "load_off4") (param i32) (result i32) (i32.load offset=4 (local.get 0)))
  (func (export "load_off8") (param i32) (result i32) (i32.load offset=8 (local.get 0)))
  (func (export "load_off12") (param i32) (result i32) (i32.load offset=12 (local.get 0)))
  (func (export "load_off16") (param i32) (result i32) (i32.load offset=16 (local.get 0)))
)

;; A load with an offset reads at the address plus the offset, not at the
;; address (which holds 0 here).
(assert_return (invoke "store" (i32.const 104) (i32.const 0x01020304)))
(assert_return (invoke "load_off4" (i32.const 100)) (i32.const 0x01020304))
(assert_return (invoke "store" (i32.const 208) (i32.const 0x05060708)))
(assert_return (invoke "load_off8" (i32.const 200)) (i32.const 0x05060708))
(assert_return (invoke "store" (i32.const 312) (i32.const 0x090a0b0c)))
(assert_return (invoke "load_off12" (i32.const 300)) (i32.const 0x090a0b0c))
(assert_return (invoke "store" (i32.const 416) (i32.const 0x0d0e0f10)))
(assert_return (invoke "load_off16" (i32.const 400)) (i32.const 0x0d0e0f10))

;; A load that would pass the end of the memory traps.
(assert_return (invoke "store" (i32.const 65532) (i32.const 0x11111111)))
(assert_return (invoke "load_off16" (i32.const 65516)) (i32.const 0x11111111))
(assert_trap (invoke "load_off16" (i32.const 65517)) "out of bounds memory access")

;; An address plus an offset past 2^32 traps: it does not wrap around to a
;; small address (here 4).
(assert_return (invoke "store" (i32.const 4) (i32.const 0x22222222)))
(assert_trap (invoke "load_off16" (i32.const -12)) "out of bounds memory access")
