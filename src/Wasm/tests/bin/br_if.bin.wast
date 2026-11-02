(module definition binary
  "\00\61\73\6d\01\00\00\00\01\8b\80\80\80\00\02\60"
  "\00\00\60\03\7f\7f\7f\01\7f\03\85\80\80\80\00\04"
  "\00\00\01\01\05\83\80\80\80\00\01\00\01\07\91\80"
  "\80\80\00\01\0d\61\73\2d\62\72\5f\69\66\2d\63\6f"
  "\6e\64\00\01\0a\ac\80\80\80\00\04\82\80\80\80\00"
  "\00\0b\8d\80\80\80\00\00\02\40\41\01\41\01\0d\00"
  "\0d\00\0b\0b\84\80\80\80\00\00\41\7f\0b\84\80\80"
  "\80\00\00\20\00\0b"
)
(module instance)
(assert_return (invoke "type-i32"))
(assert_return (invoke "type-i64"))
(assert_return (invoke "type-f32"))
(assert_return (invoke "type-f64"))
(assert_return (invoke "type-i32-value") (i32.const 0x1))
(assert_return (invoke "type-i64-value") (i64.const 0x2))
(assert_return (invoke "type-f32-value") (f32.const 0x1.8p+1))
(assert_return (invoke "type-f64-value") (f64.const 0x1p+2))
(assert_return (invoke "as-block-first" (i32.const 0x0)) (i32.const 0x2))
(assert_return (invoke "as-block-first" (i32.const 0x1)) (i32.const 0x3))
(assert_return (invoke "as-block-mid" (i32.const 0x0)) (i32.const 0x2))
(assert_return (invoke "as-block-mid" (i32.const 0x1)) (i32.const 0x3))
(assert_return (invoke "as-block-last" (i32.const 0x0)))
(assert_return (invoke "as-block-last" (i32.const 0x1)))
(assert_return (invoke "as-block-first-value" (i32.const 0x0)) (i32.const 0xb))
(assert_return (invoke "as-block-first-value" (i32.const 0x1)) (i32.const 0xa))
(assert_return (invoke "as-block-mid-value" (i32.const 0x0)) (i32.const 0x15))
(assert_return (invoke "as-block-mid-value" (i32.const 0x1)) (i32.const 0x14))
(assert_return (invoke "as-block-last-value" (i32.const 0x0)) (i32.const 0xb))
(assert_return (invoke "as-block-last-value" (i32.const 0x1)) (i32.const 0xb))
(assert_return (invoke "as-loop-first" (i32.const 0x0)) (i32.const 0x2))
(assert_return (invoke "as-loop-first" (i32.const 0x1)) (i32.const 0x3))
(assert_return (invoke "as-loop-mid" (i32.const 0x0)) (i32.const 0x2))
(assert_return (invoke "as-loop-mid" (i32.const 0x1)) (i32.const 0x4))
(assert_return (invoke "as-loop-last" (i32.const 0x0)))
(assert_return (invoke "as-loop-last" (i32.const 0x1)))
(assert_return (invoke "as-br-value") (i32.const 0x1))
(assert_return (invoke "as-br_if-cond"))
(assert_return (invoke "as-br_if-value") (i32.const 0x1))
(assert_return (invoke "as-br_if-value-cond" (i32.const 0x0)) (i32.const 0x2))
(assert_return (invoke "as-br_if-value-cond" (i32.const 0x1)) (i32.const 0x1))
(assert_return (invoke "as-br_table-index"))
(assert_return (invoke "as-br_table-value") (i32.const 0x1))
(assert_return (invoke "as-br_table-value-index") (i32.const 0x1))
(assert_return (invoke "as-return-value") (i64.const 0x1))
(assert_return (invoke "as-if-cond" (i32.const 0x0)) (i32.const 0x2))
(assert_return (invoke "as-if-cond" (i32.const 0x1)) (i32.const 0x1))
(assert_return (invoke "as-if-then" (i32.const 0x0) (i32.const 0x0)))
(assert_return (invoke "as-if-then" (i32.const 0x4) (i32.const 0x0)))
(assert_return (invoke "as-if-then" (i32.const 0x0) (i32.const 0x1)))
(assert_return (invoke "as-if-then" (i32.const 0x4) (i32.const 0x1)))
(assert_return (invoke "as-if-else" (i32.const 0x0) (i32.const 0x0)))
(assert_return (invoke "as-if-else" (i32.const 0x3) (i32.const 0x0)))
(assert_return (invoke "as-if-else" (i32.const 0x0) (i32.const 0x1)))
(assert_return (invoke "as-if-else" (i32.const 0x3) (i32.const 0x1)))
(assert_return (invoke "as-select-first" (i32.const 0x0)) (i32.const 0x3))
(assert_return (invoke "as-select-first" (i32.const 0x1)) (i32.const 0x3))
(assert_return (invoke "as-select-second" (i32.const 0x0)) (i32.const 0x3))
(assert_return (invoke "as-select-second" (i32.const 0x1)) (i32.const 0x3))
(assert_return (invoke "as-select-cond") (i32.const 0x3))
(assert_return (invoke "as-call-first") (i32.const 0xc))
(assert_return (invoke "as-call-mid") (i32.const 0xd))
(assert_return (invoke "as-call-last") (i32.const 0xe))
(assert_return (invoke "as-call_indirect-func") (i32.const 0x4))
(assert_return (invoke "as-call_indirect-first") (i32.const 0x4))
(assert_return (invoke "as-call_indirect-mid") (i32.const 0x4))
(assert_return (invoke "as-call_indirect-last") (i32.const 0x4))
(assert_return
  (invoke "as-local.set-value" (i32.const 0x0))
  (i32.const 0xffff_ffff)
)
(assert_return (invoke "as-local.set-value" (i32.const 0x1)) (i32.const 0x11))
(assert_return
  (invoke "as-local.tee-value" (i32.const 0x0))
  (i32.const 0xffff_ffff)
)
(assert_return (invoke "as-local.tee-value" (i32.const 0x1)) (i32.const 0x1))
(assert_return
  (invoke "as-global.set-value" (i32.const 0x0))
  (i32.const 0xffff_ffff)
)
(assert_return (invoke "as-global.set-value" (i32.const 0x1)) (i32.const 0x1))
(assert_return (invoke "as-load-address") (i32.const 0x1))
(assert_return (invoke "as-loadN-address") (i32.const 0x1e))
(assert_return (invoke "as-store-address") (i32.const 0x1e))
(assert_return (invoke "as-store-value") (i32.const 0x1f))
(assert_return (invoke "as-storeN-address") (i32.const 0x20))
(assert_return (invoke "as-storeN-value") (i32.const 0x21))
(assert_return (invoke "as-unary-operand") (f64.const 0x1p+0))
(assert_return (invoke "as-binary-left") (i32.const 0x1))
(assert_return (invoke "as-binary-right") (i32.const 0x1))
(assert_return (invoke "as-test-operand") (i32.const 0x0))
(assert_return (invoke "as-compare-left") (i32.const 0x1))
(assert_return (invoke "as-compare-right") (i32.const 0x1))
(assert_return (invoke "as-memory.grow-size") (i32.const 0x1))
(assert_return (invoke "nested-block-value" (i32.const 0x0)) (i32.const 0x15))
(assert_return (invoke "nested-block-value" (i32.const 0x1)) (i32.const 0x9))
(assert_return (invoke "nested-br-value" (i32.const 0x0)) (i32.const 0x5))
(assert_return (invoke "nested-br-value" (i32.const 0x1)) (i32.const 0x9))
(assert_return (invoke "nested-br_if-value" (i32.const 0x0)) (i32.const 0x5))
(assert_return (invoke "nested-br_if-value" (i32.const 0x1)) (i32.const 0x9))
(assert_return
  (invoke "nested-br_if-value-cond" (i32.const 0x0))
  (i32.const 0x5)
)
(assert_return
  (invoke "nested-br_if-value-cond" (i32.const 0x1))
  (i32.const 0x9)
)
(assert_return (invoke "nested-br_table-value" (i32.const 0x0)) (i32.const 0x5))
(assert_return (invoke "nested-br_table-value" (i32.const 0x1)) (i32.const 0x9))
(assert_return
  (invoke "nested-br_table-value-index" (i32.const 0x0))
  (i32.const 0x5)
)
(assert_return
  (invoke "nested-br_table-value-index" (i32.const 0x1))
  (i32.const 0x9)
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\90\80\80\80\00"
    "\01\8a\80\80\80\00\00\02\40\41\00\0d\00\68\0b\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\90\80\80\80\00"
    "\01\8a\80\80\80\00\00\02\40\41\00\0d\00\7a\0b\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\90\80\80\80\00"
    "\01\8a\80\80\80\00\00\02\40\41\00\0d\00\8c\0b\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\90\80\80\80\00"
    "\01\8a\80\80\80\00\00\02\40\41\00\0d\00\9a\0b\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\90\80\80\80\00"
    "\01\8a\80\80\80\00\00\02\40\41\01\0d\00\68\0b\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\90\80\80\80\00"
    "\01\8a\80\80\80\00\00\02\40\42\01\0d\00\7a\0b\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\93\80\80\80\00"
    "\01\8d\80\80\80\00\00\02\40\43\00\00\80\3f\0d\00"
    "\8c\0b\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\90\80\80\80\00"
    "\01\8a\80\80\80\00\00\02\40\42\01\0d\00\9a\0b\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
    "\00\01\7f\03\82\80\80\80\00\01\00\0a\91\80\80\80"
    "\00\01\8b\80\80\80\00\00\02\7f\41\00\0d\00\41\01"
    "\0b\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
    "\00\01\7f\03\82\80\80\80\00\01\00\0a\91\80\80\80"
    "\00\01\8b\80\80\80\00\00\02\7f\41\01\0d\00\41\01"
    "\0b\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\91\80\80\80\00"
    "\01\8b\80\80\80\00\00\02\40\41\00\41\00\0d\00\0b"
    "\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\91\80\80\80\00"
    "\01\8b\80\80\80\00\00\02\40\41\00\41\01\0d\00\0b"
    "\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
    "\00\01\7f\03\82\80\80\80\00\01\00\0a\92\80\80\80"
    "\00\01\8c\80\80\80\00\00\02\7f\01\41\00\0d\00\41"
    "\01\0b\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
    "\00\01\7f\03\82\80\80\80\00\01\00\0a\92\80\80\80"
    "\00\01\8c\80\80\80\00\00\02\7f\01\41\01\0d\00\41"
    "\01\0b\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
    "\00\01\7f\03\82\80\80\80\00\01\00\0a\94\80\80\80"
    "\00\01\8e\80\80\80\00\00\02\7f\42\01\41\00\0d\00"
    "\1a\41\01\0b\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
    "\00\01\7f\03\82\80\80\80\00\01\00\0a\94\80\80\80"
    "\00\01\8e\80\80\80\00\00\02\7f\42\01\41\00\0d\00"
    "\1a\41\01\0b\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\8d\80\80\80\00"
    "\01\87\80\80\80\00\00\02\40\0d\00\0b\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\8e\80\80\80\00"
    "\01\88\80\80\80\00\00\02\40\01\0d\00\0b\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\8f\80\80\80\00"
    "\01\89\80\80\80\00\00\02\40\42\00\0d\00\0b\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
    "\00\01\7f\03\82\80\80\80\00\01\00\0a\92\80\80\80"
    "\00\01\8c\80\80\80\00\00\02\7f\41\00\01\0d\00\41"
    "\01\0b\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
    "\00\01\7f\03\82\80\80\80\00\01\00\0a\94\80\80\80"
    "\00\01\8e\80\80\80\00\00\02\7f\41\00\02\40\41\01"
    "\0d\01\0b\0b\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
    "\00\01\7f\03\82\80\80\80\00\01\00\0a\93\80\80\80"
    "\00\01\8d\80\80\80\00\00\02\7f\41\00\42\00\0d\00"
    "\41\01\0b\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\96\80\80\80\00"
    "\01\90\80\80\80\00\00\02\40\41\00\41\00\04\7f\0d"
    "\00\0b\0b\45\1a\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\98\80\80\80\00"
    "\01\92\80\80\80\00\00\02\40\41\00\41\00\04\7f\41"
    "\01\0d\00\0b\0b\45\1a\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\90\80\80\80\00"
    "\01\8a\80\80\80\00\00\02\7f\0d\00\0f\0b\45\1a\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\92\80\80\80\00"
    "\01\8c\80\80\80\00\00\02\7f\41\01\0d\00\0f\0b\45"
    "\1a\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\8c\80\80\80\00"
    "\01\86\80\80\80\00\00\41\01\0d\01\0b"
  )
  "unknown label"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\92\80\80\80\00"
    "\01\8c\80\80\80\00\00\02\40\02\40\41\01\0d\05\0b"
    "\0b\0b"
  )
  "unknown label"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\90\80\80\80\00"
    "\01\8a\80\80\80\00\00\41\01\0d\81\80\80\80\01\0b"
  )
  "unknown label"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\8e\80\80\80\00\03\60"
    "\00\00\60\01\63\00\01\70\60\00\01\70\03\83\80\80"
    "\80\00\02\01\02\0a\99\80\80\80\00\02\84\80\80\80"
    "\00\00\20\00\0b\8a\80\80\80\00\00\d0\00\41\00\0d"
    "\00\10\00\0b"
  )
  "type mismatch"
)
