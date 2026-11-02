;; Stores
;; ======
;;
;; Tests of kind b (bend2 skill): the Bend version of WASM against the spec,
;; for the forms of stores that the compiler emits and that no official test
;; of the pinned commit runs (AGENTS.md 3.9.1.3). A law cannot state them: we
;; know of no Lean or Bend version of the spec. Each expected result is the
;; spec's (convert.ts).

(module
  (memory 1)
  (func (export "store") (param i32 i32) (i32.store (local.get 0) (local.get 1)))
  (func (export "store_off4") (param i32 i32) (i32.store offset=4 (local.get 0) (local.get 1)))
  (func (export "store_off8") (param i32 i32) (i32.store offset=8 (local.get 0) (local.get 1)))
  (func (export "store_off12") (param i32 i32) (i32.store offset=12 (local.get 0) (local.get 1)))
  (func (export "store_off16") (param i32 i32) (i32.store offset=16 (local.get 0) (local.get 1)))
  (func (export "store_byte") (param i32 i32) (i32.store8 (local.get 0) (local.get 1)))
  (func (export "load") (param i32) (result i32) (i32.load (local.get 0)))
  (func (export "load_byte") (param i32) (result i32) (i32.load8_u (local.get 0)))
)

;; A store with an offset writes at the address plus the offset, not at the
;; address.
(assert_return (invoke "store_off4" (i32.const 100) (i32.const 0x01020304)))
(assert_return (invoke "load" (i32.const 104)) (i32.const 0x01020304))
(assert_return (invoke "load" (i32.const 100)) (i32.const 0))
(assert_return (invoke "store_off8" (i32.const 200) (i32.const 0x05060708)))
(assert_return (invoke "load" (i32.const 208)) (i32.const 0x05060708))
(assert_return (invoke "load" (i32.const 200)) (i32.const 0))
(assert_return (invoke "store_off12" (i32.const 300) (i32.const 0x090a0b0c)))
(assert_return (invoke "load" (i32.const 312)) (i32.const 0x090a0b0c))
(assert_return (invoke "load" (i32.const 300)) (i32.const 0))
(assert_return (invoke "store_off16" (i32.const 400) (i32.const 0x0d0e0f10)))
(assert_return (invoke "load" (i32.const 416)) (i32.const 0x0d0e0f10))
(assert_return (invoke "load" (i32.const 400)) (i32.const 0))

;; A store that would pass the end of the memory traps and writes nothing:
;; the last 4 bytes keep what the store before wrote.
(assert_return (invoke "store_off16" (i32.const 65516) (i32.const 0x11111111)))
(assert_return (invoke "load" (i32.const 65532)) (i32.const 0x11111111))
(assert_trap (invoke "store_off16" (i32.const 65517) (i32.const 0x22222222)) "out of bounds memory access")
(assert_return (invoke "load" (i32.const 65532)) (i32.const 0x11111111))
(assert_return (invoke "store_byte" (i32.const 65535) (i32.const 0xab)))
(assert_return (invoke "load_byte" (i32.const 65535)) (i32.const 0xab))
(assert_trap (invoke "store_byte" (i32.const 65536) (i32.const 0xcd)) "out of bounds memory access")

;; An address plus an offset past 2^32 traps: it does not wrap around to a
;; small address (here 4).
(assert_trap (invoke "store_off16" (i32.const -12) (i32.const 0x33333333)) "out of bounds memory access")
(assert_return (invoke "load" (i32.const 4)) (i32.const 0))

;; i32.store8 writes only the lowest byte of the value: the bytes next to it
;; stay as they were.
(assert_return (invoke "store" (i32.const 500) (i32.const 0xaabbccdd)))
(assert_return (invoke "store_byte" (i32.const 501) (i32.const 0x12345678)))
(assert_return (invoke "load" (i32.const 500)) (i32.const 0xaabb78dd))

;; i32.store writes the lowest byte at the lowest address.
(assert_return (invoke "store" (i32.const 600) (i32.const 0x11223344)))
(assert_return (invoke "load_byte" (i32.const 600)) (i32.const 0x44))
(assert_return (invoke "load_byte" (i32.const 601)) (i32.const 0x33))
(assert_return (invoke "load_byte" (i32.const 602)) (i32.const 0x22))
(assert_return (invoke "load_byte" (i32.const 603)) (i32.const 0x11))
