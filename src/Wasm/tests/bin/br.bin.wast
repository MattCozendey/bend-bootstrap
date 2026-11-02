(module definition binary
  "\00\61\73\6d\01\00\00\00\01\8b\80\80\80\00\02\60"
  "\00\00\60\03\7f\7f\7f\01\7f\03\84\80\80\80\00\03"
  "\00\00\01\05\83\80\80\80\00\01\00\01\07\91\80\80"
  "\80\00\01\0d\61\73\2d\62\72\5f\69\66\2d\63\6f\6e"
  "\64\00\01\0a\9f\80\80\80\00\03\82\80\80\80\00\00"
  "\0b\89\80\80\80\00\00\02\40\0c\00\0d\00\0b\0b\84"
  "\80\80\80\00\00\41\7f\0b"
)
(module instance)
(assert_return (invoke "type-i32"))
(assert_return (invoke "type-i64"))
(assert_return (invoke "type-f32"))
(assert_return (invoke "type-f64"))
(assert_return (invoke "type-i32-i32"))
(assert_return (invoke "type-i64-i64"))
(assert_return (invoke "type-f32-f32"))
(assert_return (invoke "type-f64-f64"))
(assert_return (invoke "type-i32-value") (i32.const 0x1))
(assert_return (invoke "type-i64-value") (i64.const 0x2))
(assert_return (invoke "type-f32-value") (f32.const 0x1.8p+1))
(assert_return (invoke "type-f64-value") (f64.const 0x1p+2))
(assert_return
  (invoke "type-f64-f64-value")
  (f64.const 0x1p+2)
  (f64.const 0x1.4p+2)
)
(assert_return (invoke "as-block-first"))
(assert_return (invoke "as-block-mid"))
(assert_return (invoke "as-block-last"))
(assert_return (invoke "as-block-value") (i32.const 0x2))
(assert_return (invoke "as-loop-first") (i32.const 0x3))
(assert_return (invoke "as-loop-mid") (i32.const 0x4))
(assert_return (invoke "as-loop-last") (i32.const 0x5))
(assert_return (invoke "as-br-value") (i32.const 0x9))
(assert_return (invoke "as-br_if-cond"))
(assert_return (invoke "as-br_if-value") (i32.const 0x8))
(assert_return (invoke "as-br_if-value-cond") (i32.const 0x9))
(assert_return (invoke "as-br_table-index"))
(assert_return (invoke "as-br_table-value") (i32.const 0xa))
(assert_return (invoke "as-br_table-value-index") (i32.const 0xb))
(assert_return (invoke "as-return-value") (i64.const 0x7))
(assert_return (invoke "as-return-values") (i32.const 0x2) (i64.const 0x7))
(assert_return (invoke "as-if-cond") (i32.const 0x2))
(assert_return
  (invoke "as-if-then" (i32.const 0x1) (i32.const 0x6))
  (i32.const 0x3)
)
(assert_return
  (invoke "as-if-then" (i32.const 0x0) (i32.const 0x6))
  (i32.const 0x6)
)
(assert_return
  (invoke "as-if-else" (i32.const 0x0) (i32.const 0x6))
  (i32.const 0x4)
)
(assert_return
  (invoke "as-if-else" (i32.const 0x1) (i32.const 0x6))
  (i32.const 0x6)
)
(assert_return
  (invoke "as-select-first" (i32.const 0x0) (i32.const 0x6))
  (i32.const 0x5)
)
(assert_return
  (invoke "as-select-first" (i32.const 0x1) (i32.const 0x6))
  (i32.const 0x5)
)
(assert_return
  (invoke "as-select-second" (i32.const 0x0) (i32.const 0x6))
  (i32.const 0x6)
)
(assert_return
  (invoke "as-select-second" (i32.const 0x1) (i32.const 0x6))
  (i32.const 0x6)
)
(assert_return (invoke "as-select-cond") (i32.const 0x7))
(assert_return (invoke "as-select-all") (i32.const 0x8))
(assert_return (invoke "as-call-first") (i32.const 0xc))
(assert_return (invoke "as-call-mid") (i32.const 0xd))
(assert_return (invoke "as-call-last") (i32.const 0xe))
(assert_return (invoke "as-call-all") (i32.const 0xf))
(assert_return (invoke "as-call_indirect-func") (i32.const 0x14))
(assert_return (invoke "as-call_indirect-first") (i32.const 0x15))
(assert_return (invoke "as-call_indirect-mid") (i32.const 0x16))
(assert_return (invoke "as-call_indirect-last") (i32.const 0x17))
(assert_return (invoke "as-call_indirect-all") (i32.const 0x18))
(assert_return (invoke "as-local.set-value") (i32.const 0x11))
(assert_return (invoke "as-local.tee-value") (i32.const 0x1))
(assert_return (invoke "as-global.set-value") (i32.const 0x1))
(assert_return (invoke "as-load-address") (f32.const 0x1.b333_34p+0))
(assert_return (invoke "as-loadN-address") (i64.const 0x1e))
(assert_return (invoke "as-store-address") (i32.const 0x1e))
(assert_return (invoke "as-store-value") (i32.const 0x1f))
(assert_return (invoke "as-store-both") (i32.const 0x20))
(assert_return (invoke "as-storeN-address") (i32.const 0x20))
(assert_return (invoke "as-storeN-value") (i32.const 0x21))
(assert_return (invoke "as-storeN-both") (i32.const 0x22))
(assert_return (invoke "as-unary-operand") (f32.const 0x1.b333_34p+1))
(assert_return (invoke "as-binary-left") (i32.const 0x3))
(assert_return (invoke "as-binary-right") (i64.const 0x2d))
(assert_return (invoke "as-binary-both") (i32.const 0x2e))
(assert_return (invoke "as-test-operand") (i32.const 0x2c))
(assert_return (invoke "as-compare-left") (i32.const 0x2b))
(assert_return (invoke "as-compare-right") (i32.const 0x2a))
(assert_return (invoke "as-compare-both") (i32.const 0x2c))
(assert_return (invoke "as-convert-operand") (i32.const 0x29))
(assert_return (invoke "as-memory.grow-size") (i32.const 0x28))
(assert_return (invoke "nested-block-value") (i32.const 0x9))
(assert_return (invoke "nested-br-value") (i32.const 0x9))
(assert_return (invoke "nested-br_if-value") (i32.const 0x9))
(assert_return (invoke "nested-br_if-value-cond") (i32.const 0x9))
(assert_return (invoke "nested-br_table-value") (i32.const 0x9))
(assert_return (invoke "nested-br_table-value-index") (i32.const 0x9))
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
    "\00\01\7f\03\82\80\80\80\00\01\00\0a\8f\80\80\80"
    "\00\01\89\80\80\80\00\00\02\7f\0c\00\41\01\0b\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
    "\00\01\7f\03\82\80\80\80\00\01\00\0a\90\80\80\80"
    "\00\01\8a\80\80\80\00\00\02\7f\01\0c\00\41\01\0b"
    "\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
    "\00\01\7f\03\82\80\80\80\00\01\00\0a\92\80\80\80"
    "\00\01\8c\80\80\80\00\00\02\7f\41\00\02\40\0c\01"
    "\0b\0b\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
    "\00\01\7f\03\82\80\80\80\00\01\00\0a\91\80\80\80"
    "\00\01\8b\80\80\80\00\00\02\7f\42\01\0c\00\41\01"
    "\0b\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\93\80\80\80\00"
    "\01\8d\80\80\80\00\00\41\00\02\7f\0c\00\0c\00\0b"
    "\45\1a\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\95\80\80\80\00"
    "\01\8f\80\80\80\00\00\41\00\02\7f\0c\00\41\01\0d"
    "\00\0b\45\1a\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\94\80\80\80\00"
    "\01\8e\80\80\80\00\00\41\00\02\7f\0c\00\0e\00\00"
    "\0b\45\1a\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\90\80\80\80\00"
    "\01\8a\80\80\80\00\00\02\7f\0c\00\0f\0b\45\1a\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\94\80\80\80\00"
    "\01\8e\80\80\80\00\00\02\7f\0c\00\41\01\41\02\1b"
    "\0b\45\1a\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\89\80\80\80\00\02\60"
    "\00\00\60\01\7f\01\7f\03\83\80\80\80\00\02\00\01"
    "\0a\9a\80\80\80\00\02\8b\80\80\80\00\00\02\7f\0c"
    "\00\10\01\0b\45\1a\0b\84\80\80\80\00\00\20\00\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\89\80\80\80\00\02\60"
    "\01\7f\01\7f\60\00\00\03\83\80\80\80\00\02\00\01"
    "\04\85\80\80\80\00\01\70\01\01\01\09\89\80\80\80"
    "\00\01\04\41\00\0b\01\d2\00\0b\0a\9d\80\80\80\00"
    "\02\84\80\80\80\00\00\20\00\0b\8e\80\80\80\00\00"
    "\02\7f\0c\00\41\00\11\00\00\0b\45\1a\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\95\80\80\80\00"
    "\01\8f\80\80\80\00\01\01\7f\02\7f\0c\00\21\00\20"
    "\00\0b\45\1a\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\93\80\80\80\00"
    "\01\8d\80\80\80\00\01\01\7f\02\7f\0c\00\22\00\0b"
    "\45\1a\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\06\86\80\80\80\00"
    "\01\7f\01\41\00\0b\0a\93\80\80\80\00\01\8d\80\80"
    "\80\00\00\02\7f\0c\00\24\00\23\00\0b\45\1a\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\05\83\80\80\80\00"
    "\01\00\00\0a\91\80\80\80\00\01\8b\80\80\80\00\00"
    "\02\7f\0c\00\40\00\0b\45\1a\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\05\83\80\80\80\00"
    "\01\00\01\0a\92\80\80\80\00\01\8c\80\80\80\00\00"
    "\02\7f\0c\00\28\02\00\0b\45\1a\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\05\83\80\80\80\00"
    "\01\00\01\0a\94\80\80\80\00\01\8e\80\80\80\00\00"
    "\02\7f\0c\00\41\00\36\02\00\0b\45\1a\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\8a\80\80\80\00"
    "\01\84\80\80\80\00\00\0c\01\0b"
  )
  "unknown label"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\90\80\80\80\00"
    "\01\8a\80\80\80\00\00\02\40\02\40\0c\05\0b\0b\0b"
  )
  "unknown label"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\8e\80\80\80\00"
    "\01\88\80\80\80\00\00\0c\81\80\80\80\01\0b"
  )
  "unknown label"
)
