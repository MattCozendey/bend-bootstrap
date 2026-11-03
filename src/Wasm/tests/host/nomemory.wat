;; A module for src/Wasm/tests/agree.ts, of the Host protocol of
;; src/Wasm/impl.bend: its memory has no pages, so it holds no output's address
;; and length when run gives a result.

(module
  (memory (export "memory") 0)
  (func (export "alloc") (param i32) (result i32) (i32.const 0))
  (func (export "run") (param i32 i32) (result i32) (i32.const 0))
)
