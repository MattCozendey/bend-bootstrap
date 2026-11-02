;; Host cases
;; ==========
;;
;; A module for src/Wasm/tests/agree.ts: it follows the Host protocol of
;; src/Wasm/impl.bend (memory, alloc, run), and the first byte of its input
;; picks the path that it takes through the host. alloc gives -1 for an input
;; of more than 60000 bytes, else address 4096. convert.ts writes cases.wasm.
;; A grow that fails is left out: the spec lets any grow fail, so its outcome
;; is not fixed.

(module
  (memory (export "memory") 1)
  (func (export "alloc") (param i32) (result i32) (local i32)
    (local.set 1 (i32.const -1))
    (block
      (br_if 0 (i32.gt_u (local.get 0) (i32.const 60000)))
      (local.set 1 (i32.const 4096)))
    (local.get 1))
  (func (export "run") (param i32 i32) (result i32) (local i32 i32)
    (local.set 2 (i32.load8_u (local.get 0)))
    (local.set 3 (i32.const 2))
    (block
      ;; 'e': the output is the input
      (block (br_if 0 (i32.ne (local.get 2) (i32.const 101)))
        (i32.store (i32.const 0) (local.get 0)) (i32.store (i32.const 4) (local.get 1))
        (local.set 3 (i32.const 0)) (br 1))
      ;; 'o': out of memory
      (block (br_if 0 (i32.ne (local.get 2) (i32.const 111))) (local.set 3 (i32.const 1)) (br 1))
      ;; 'x': an unknown status
      (block (br_if 0 (i32.ne (local.get 2) (i32.const 120))) (local.set 3 (i32.const 7)) (br 1))
      ;; 'r': an output past the end of the memory
      (block (br_if 0 (i32.ne (local.get 2) (i32.const 114)))
        (i32.store (i32.const 0) (i32.const 65535)) (i32.store (i32.const 4) (i32.const 2))
        (local.set 3 (i32.const 0)) (br 1))
      ;; 'z': an empty output at the very end of the memory
      (block (br_if 0 (i32.ne (local.get 2) (i32.const 122)))
        (i32.store (i32.const 0) (i32.const 65536)) (i32.store (i32.const 4) (i32.const 0))
        (local.set 3 (i32.const 0)) (br 1))
      ;; 'm': the memory's size in pages after a grow by the input's second byte, as one byte
      (block (br_if 0 (i32.ne (local.get 2) (i32.const 109)))
        (local.set 2 (memory.grow (i32.load8_u offset=1 (local.get 0))))
        (i32.store8 (i32.const 256) (i32.add (i32.const 48) (memory.size)))
        (i32.store (i32.const 0) (i32.const 256)) (i32.store (i32.const 4) (i32.const 1))
        (local.set 3 (i32.const 0)) (br 1))
    )
    (local.get 3))
)
