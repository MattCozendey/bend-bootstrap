;; Branches
;; ========
;;
;; Tests of kind b (bend2 skill): the Bend version of WASM against the spec,
;; for the forms of br that the compiler emits and that no official test of
;; the pinned commit runs (AGENTS.md 3.9.1.3). A law cannot state them: we
;; know of no Lean or Bend version of the spec. Each expected result is the
;; spec's (convert.ts).

(module
  ;; i counts the runs of the loop's body; br 0 goes back to its start, br_if 1
  ;; leaves it once i reaches n
  (func (export "count") (param $n i32) (result i32)
    (local $i i32)
    (block
      (loop
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br_if 1 (i32.ge_u (local.get $i) (local.get $n)))
        (br 0)))
    (local.get $i))

  ;; br 1 and br 2 from the innermost of three blocks: each block that it
  ;; leaves skips its rest, which would set a bit of x
  (func (export "out1") (result i32)
    (local $x i32)
    (block
      (block
        (block
          (local.set $x (i32.const 1))
          (br 1))
        (local.set $x (i32.or (local.get $x) (i32.const 2))))
      (local.set $x (i32.or (local.get $x) (i32.const 4))))
    (local.get $x))
  (func (export "out2") (result i32)
    (local $x i32)
    (block
      (block
        (block
          (local.set $x (i32.const 1))
          (br 2))
        (local.set $x (i32.or (local.get $x) (i32.const 2))))
      (local.set $x (i32.or (local.get $x) (i32.const 4))))
    (local.get $x))

  ;; br 1 drops the values that its blocks pushed, and keeps the 7 under them
  (func (export "kept") (result i32)
    (i32.const 7)
    (block
      (block
        (i32.const 5)
        (i32.const 6)
        (br 1)))
    (i32.const 1)
    (i32.add))

  ;; br 1 in a loop's body leaves the block around the loop, and does not run
  ;; the loop again
  (func (export "out_of_loop") (result i32)
    (local $x i32)
    (block
      (loop
        (local.set $x (i32.add (local.get $x) (i32.const 1)))
        (br 1)))
    (local.get $x))
)

;; br 0 in a loop goes back to the loop's start: its body runs exactly n times.
(assert_return (invoke "count" (i32.const 1)) (i32.const 1))
(assert_return (invoke "count" (i32.const 5)) (i32.const 5))
(assert_return (invoke "count" (i32.const 1000)) (i32.const 1000))

;; br k with k > 0 leaves k + 1 nested blocks at once, skips the rest of each,
;; and leaves the stack as it was.
(assert_return (invoke "out1") (i32.const 5))
(assert_return (invoke "out2") (i32.const 1))
(assert_return (invoke "kept") (i32.const 8))
(assert_return (invoke "out_of_loop") (i32.const 1))
