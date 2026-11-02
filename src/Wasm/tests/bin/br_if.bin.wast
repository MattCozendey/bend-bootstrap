(module definition binary
  "\00\61\73\6d\01\00\00\00\01\94\80\80\80\00\04\60"
  "\00\00\60\00\01\7f\60\01\7f\01\7f\60\03\7f\7f\7f"
  "\01\7f\03\91\80\80\80\00\10\00\01\00\03\03\02\01"
  "\01\01\01\01\01\01\01\01\01\05\83\80\80\80\00\01"
  "\00\01\07\ee\81\80\80\00\0d\0b\61\73\2d\62\72\2d"
  "\76\61\6c\75\65\00\01\0d\61\73\2d\62\72\5f\69\66"
  "\2d\63\6f\6e\64\00\02\12\61\73\2d\6c\6f\63\61\6c"
  "\2e\73\65\74\2d\76\61\6c\75\65\00\05\0f\61\73\2d"
  "\6c\6f\61\64\2d\61\64\64\72\65\73\73\00\06\10\61"
  "\73\2d\73\74\6f\72\65\2d\61\64\64\72\65\73\73\00"
  "\07\0e\61\73\2d\73\74\6f\72\65\2d\76\61\6c\75\65"
  "\00\08\11\61\73\2d\73\74\6f\72\65\4e\2d\61\64\64"
  "\72\65\73\73\00\09\0e\61\73\2d\62\69\6e\61\72\79"
  "\2d\6c\65\66\74\00\0a\0f\61\73\2d\62\69\6e\61\72"
  "\79\2d\72\69\67\68\74\00\0b\0f\61\73\2d\74\65\73"
  "\74\2d\6f\70\65\72\61\6e\64\00\0c\0f\61\73\2d\63"
  "\6f\6d\70\61\72\65\2d\6c\65\66\74\00\0d\10\61\73"
  "\2d\63\6f\6d\70\61\72\65\2d\72\69\67\68\74\00\0e"
  "\13\61\73\2d\6d\65\6d\6f\72\79\2e\67\72\6f\77\2d"
  "\73\69\7a\65\00\0f\0a\9b\82\80\80\00\10\82\80\80"
  "\80\00\00\0b\8d\80\80\80\00\00\02\7f\41\01\41\02"
  "\0d\00\0c\00\0b\0b\8d\80\80\80\00\00\02\40\41\01"
  "\41\01\0d\00\0d\00\0b\0b\84\80\80\80\00\00\41\7f"
  "\0b\84\80\80\80\00\00\20\00\0b\91\80\80\80\00\01"
  "\01\7f\02\7f\41\11\20\00\0d\00\21\00\41\7f\0b\0b"
  "\8e\80\80\80\00\00\02\7f\41\01\41\01\0d\00\28\02"
  "\00\0b\0b\92\80\80\80\00\00\02\7f\41\1e\41\01\0d"
  "\00\41\07\36\02\00\41\7f\0b\0b\92\80\80\80\00\00"
  "\02\7f\41\02\41\1f\41\01\0d\00\36\02\00\41\7f\0b"
  "\0b\92\80\80\80\00\00\02\7f\41\20\41\01\0d\00\41"
  "\07\3a\00\00\41\7f\0b\0b\8e\80\80\80\00\00\02\7f"
  "\41\01\41\01\0d\00\41\0a\6a\0b\0b\8e\80\80\80\00"
  "\00\02\7f\41\0a\41\01\41\01\0d\00\6b\0b\0b\8c\80"
  "\80\80\00\00\02\7f\41\00\41\01\0d\00\45\0b\0b\8e"
  "\80\80\80\00\00\02\7f\41\01\41\01\0d\00\41\0a\4d"
  "\0b\0b\8e\80\80\80\00\00\02\7f\41\0a\41\01\41\2a"
  "\0d\00\47\0b\0b\8d\80\80\80\00\00\02\7f\41\01\41"
  "\01\0d\00\40\00\0b\0b"
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
