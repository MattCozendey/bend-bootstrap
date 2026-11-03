;; A module for src/Wasm/tests/agree.ts, of the Host protocol of
;; src/Wasm/impl.bend: its data segment does not fit in its memory, so it
;; traps when it is instantiated.

(module
  (memory (export "memory") 1)
  (data (i32.const 65536) "a")
  (func (export "alloc") (param i32) (result i32) (i32.const 0))
  (func (export "run") (param i32 i32) (result i32) (i32.const 2))
)
