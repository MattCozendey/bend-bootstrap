(module definition binary
  "\00\61\73\6d\01\00\00\00\01\8b\80\80\80\00\02\60"
  "\00\00\60\03\7f\7f\7f\01\7f\03\84\80\80\80\00\03"
  "\00\01\00\05\83\80\80\80\00\01\00\01\0a\98\80\80"
  "\80\00\03\82\80\80\80\00\00\0b\84\80\80\80\00\00"
  "\41\7f\0b\82\80\80\80\00\00\0b"
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
(assert_return (invoke "empty" (i32.const 0x0)) (i32.const 0x16))
(assert_return (invoke "empty" (i32.const 0x1)) (i32.const 0x16))
(assert_return (invoke "empty" (i32.const 0xb)) (i32.const 0x16))
(assert_return (invoke "empty" (i32.const 0xffff_ffff)) (i32.const 0x16))
(assert_return (invoke "empty" (i32.const 0xffff_ff9c)) (i32.const 0x16))
(assert_return (invoke "empty" (i32.const 0xffff_ffff)) (i32.const 0x16))
(assert_return (invoke "empty-value" (i32.const 0x0)) (i32.const 0x21))
(assert_return (invoke "empty-value" (i32.const 0x1)) (i32.const 0x21))
(assert_return (invoke "empty-value" (i32.const 0xb)) (i32.const 0x21))
(assert_return (invoke "empty-value" (i32.const 0xffff_ffff)) (i32.const 0x21))
(assert_return (invoke "empty-value" (i32.const 0xffff_ff9c)) (i32.const 0x21))
(assert_return (invoke "empty-value" (i32.const 0xffff_ffff)) (i32.const 0x21))
(assert_return (invoke "singleton" (i32.const 0x0)) (i32.const 0x16))
(assert_return (invoke "singleton" (i32.const 0x1)) (i32.const 0x14))
(assert_return (invoke "singleton" (i32.const 0xb)) (i32.const 0x14))
(assert_return (invoke "singleton" (i32.const 0xffff_ffff)) (i32.const 0x14))
(assert_return (invoke "singleton" (i32.const 0xffff_ff9c)) (i32.const 0x14))
(assert_return (invoke "singleton" (i32.const 0xffff_ffff)) (i32.const 0x14))
(assert_return (invoke "singleton-value" (i32.const 0x0)) (i32.const 0x20))
(assert_return (invoke "singleton-value" (i32.const 0x1)) (i32.const 0x21))
(assert_return (invoke "singleton-value" (i32.const 0xb)) (i32.const 0x21))
(assert_return
  (invoke "singleton-value" (i32.const 0xffff_ffff))
  (i32.const 0x21)
)
(assert_return
  (invoke "singleton-value" (i32.const 0xffff_ff9c))
  (i32.const 0x21)
)
(assert_return
  (invoke "singleton-value" (i32.const 0xffff_ffff))
  (i32.const 0x21)
)
(assert_return (invoke "multiple" (i32.const 0x0)) (i32.const 0x67))
(assert_return (invoke "multiple" (i32.const 0x1)) (i32.const 0x66))
(assert_return (invoke "multiple" (i32.const 0x2)) (i32.const 0x65))
(assert_return (invoke "multiple" (i32.const 0x3)) (i32.const 0x64))
(assert_return (invoke "multiple" (i32.const 0x4)) (i32.const 0x68))
(assert_return (invoke "multiple" (i32.const 0x5)) (i32.const 0x68))
(assert_return (invoke "multiple" (i32.const 0x6)) (i32.const 0x68))
(assert_return (invoke "multiple" (i32.const 0xa)) (i32.const 0x68))
(assert_return (invoke "multiple" (i32.const 0xffff_ffff)) (i32.const 0x68))
(assert_return (invoke "multiple" (i32.const 0xffff_ffff)) (i32.const 0x68))
(assert_return (invoke "multiple-value" (i32.const 0x0)) (i32.const 0xd5))
(assert_return (invoke "multiple-value" (i32.const 0x1)) (i32.const 0xd4))
(assert_return (invoke "multiple-value" (i32.const 0x2)) (i32.const 0xd3))
(assert_return (invoke "multiple-value" (i32.const 0x3)) (i32.const 0xd2))
(assert_return (invoke "multiple-value" (i32.const 0x4)) (i32.const 0xd6))
(assert_return (invoke "multiple-value" (i32.const 0x5)) (i32.const 0xd6))
(assert_return (invoke "multiple-value" (i32.const 0x6)) (i32.const 0xd6))
(assert_return (invoke "multiple-value" (i32.const 0xa)) (i32.const 0xd6))
(assert_return
  (invoke "multiple-value" (i32.const 0xffff_ffff))
  (i32.const 0xd6)
)
(assert_return
  (invoke "multiple-value" (i32.const 0xffff_ffff))
  (i32.const 0xd6)
)
(assert_return (invoke "large" (i32.const 0x0)) (i32.const 0x0))
(assert_return (invoke "large" (i32.const 0x1)) (i32.const 0x1))
(assert_return (invoke "large" (i32.const 0x64)) (i32.const 0x0))
(assert_return (invoke "large" (i32.const 0x65)) (i32.const 0x1))
(assert_return (invoke "large" (i32.const 0x2710)) (i32.const 0x0))
(assert_return (invoke "large" (i32.const 0x2711)) (i32.const 0x1))
(assert_return (invoke "large" (i32.const 0xf_4240)) (i32.const 0x1))
(assert_return (invoke "large" (i32.const 0xf_4241)) (i32.const 0x1))
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
(assert_return (invoke "as-call-first") (i32.const 0xc))
(assert_return (invoke "as-call-mid") (i32.const 0xd))
(assert_return (invoke "as-call-last") (i32.const 0xe))
(assert_return (invoke "as-call_indirect-first") (i32.const 0x14))
(assert_return (invoke "as-call_indirect-mid") (i32.const 0x15))
(assert_return (invoke "as-call_indirect-last") (i32.const 0x16))
(assert_return (invoke "as-call_indirect-func") (i32.const 0x17))
(assert_return (invoke "as-local.set-value") (i32.const 0x11))
(assert_return (invoke "as-local.tee-value") (i32.const 0x1))
(assert_return (invoke "as-global.set-value") (i32.const 0x1))
(assert_return (invoke "as-load-address") (f32.const 0x1.b333_34p+0))
(assert_return (invoke "as-loadN-address") (i64.const 0x1e))
(assert_return (invoke "as-store-address") (i32.const 0x1e))
(assert_return (invoke "as-store-value") (i32.const 0x1f))
(assert_return (invoke "as-storeN-address") (i32.const 0x20))
(assert_return (invoke "as-storeN-value") (i32.const 0x21))
(assert_return (invoke "as-unary-operand") (f32.const 0x1.b333_34p+1))
(assert_return (invoke "as-binary-left") (i32.const 0x3))
(assert_return (invoke "as-binary-right") (i64.const 0x2d))
(assert_return (invoke "as-test-operand") (i32.const 0x2c))
(assert_return (invoke "as-compare-left") (i32.const 0x2b))
(assert_return (invoke "as-compare-right") (i32.const 0x2a))
(assert_return (invoke "as-convert-operand") (i32.const 0x29))
(assert_return (invoke "as-memory.grow-size") (i32.const 0x28))
(assert_return (invoke "nested-block-value" (i32.const 0x0)) (i32.const 0x13))
(assert_return (invoke "nested-block-value" (i32.const 0x1)) (i32.const 0x11))
(assert_return (invoke "nested-block-value" (i32.const 0x2)) (i32.const 0x10))
(assert_return (invoke "nested-block-value" (i32.const 0xa)) (i32.const 0x10))
(assert_return
  (invoke "nested-block-value" (i32.const 0xffff_ffff))
  (i32.const 0x10)
)
(assert_return
  (invoke "nested-block-value" (i32.const 0x1_86a0))
  (i32.const 0x10)
)
(assert_return (invoke "nested-br-value" (i32.const 0x0)) (i32.const 0x8))
(assert_return (invoke "nested-br-value" (i32.const 0x1)) (i32.const 0x9))
(assert_return (invoke "nested-br-value" (i32.const 0x2)) (i32.const 0x11))
(assert_return (invoke "nested-br-value" (i32.const 0xb)) (i32.const 0x11))
(assert_return
  (invoke "nested-br-value" (i32.const 0xffff_fffc))
  (i32.const 0x11)
)
(assert_return
  (invoke "nested-br-value" (i32.const 0x9b_d75a))
  (i32.const 0x11)
)
(assert_return (invoke "nested-br_if-value" (i32.const 0x0)) (i32.const 0x11))
(assert_return (invoke "nested-br_if-value" (i32.const 0x1)) (i32.const 0x9))
(assert_return (invoke "nested-br_if-value" (i32.const 0x2)) (i32.const 0x8))
(assert_return (invoke "nested-br_if-value" (i32.const 0x9)) (i32.const 0x8))
(assert_return
  (invoke "nested-br_if-value" (i32.const 0xffff_fff7))
  (i32.const 0x8)
)
(assert_return
  (invoke "nested-br_if-value" (i32.const 0xf_423f))
  (i32.const 0x8)
)
(assert_return
  (invoke "nested-br_if-value-cond" (i32.const 0x0))
  (i32.const 0x9)
)
(assert_return
  (invoke "nested-br_if-value-cond" (i32.const 0x1))
  (i32.const 0x8)
)
(assert_return
  (invoke "nested-br_if-value-cond" (i32.const 0x2))
  (i32.const 0x9)
)
(assert_return
  (invoke "nested-br_if-value-cond" (i32.const 0x3))
  (i32.const 0x9)
)
(assert_return
  (invoke "nested-br_if-value-cond" (i32.const 0xfff0_bdc0))
  (i32.const 0x9)
)
(assert_return
  (invoke "nested-br_if-value-cond" (i32.const 0x8f_cc67))
  (i32.const 0x9)
)
(assert_return
  (invoke "nested-br_table-value" (i32.const 0x0))
  (i32.const 0x11)
)
(assert_return (invoke "nested-br_table-value" (i32.const 0x1)) (i32.const 0x9))
(assert_return (invoke "nested-br_table-value" (i32.const 0x2)) (i32.const 0x8))
(assert_return (invoke "nested-br_table-value" (i32.const 0x9)) (i32.const 0x8))
(assert_return
  (invoke "nested-br_table-value" (i32.const 0xffff_fff7))
  (i32.const 0x8)
)
(assert_return
  (invoke "nested-br_table-value" (i32.const 0xf_423f))
  (i32.const 0x8)
)
(assert_return
  (invoke "nested-br_table-value-index" (i32.const 0x0))
  (i32.const 0x9)
)
(assert_return
  (invoke "nested-br_table-value-index" (i32.const 0x1))
  (i32.const 0x8)
)
(assert_return
  (invoke "nested-br_table-value-index" (i32.const 0x2))
  (i32.const 0x9)
)
(assert_return
  (invoke "nested-br_table-value-index" (i32.const 0x3))
  (i32.const 0x9)
)
(assert_return
  (invoke "nested-br_table-value-index" (i32.const 0xfff0_bdc0))
  (i32.const 0x9)
)
(assert_return
  (invoke "nested-br_table-value-index" (i32.const 0x8f_cc67))
  (i32.const 0x9)
)
(assert_return
  (invoke "nested-br_table-loop-block" (i32.const 0x1))
  (i32.const 0x3)
)
(assert_return
  (invoke "meet-externref" (i32.const 0x0) (ref.extern 1))
  (ref.extern 1)
)
(assert_return
  (invoke "meet-externref" (i32.const 0x1) (ref.extern 1))
  (ref.extern 1)
)
(assert_return
  (invoke "meet-externref" (i32.const 0x2) (ref.extern 1))
  (ref.extern 1)
)
(assert_return (invoke "meet-funcref-1" (i32.const 0x0)) (ref.func))
(assert_return (invoke "meet-funcref-1" (i32.const 0x1)) (ref.func))
(assert_return (invoke "meet-funcref-1" (i32.const 0x2)) (ref.func))
(assert_return (invoke "meet-funcref-2" (i32.const 0x0)) (ref.func))
(assert_return (invoke "meet-funcref-2" (i32.const 0x1)) (ref.func))
(assert_return (invoke "meet-funcref-2" (i32.const 0x2)) (ref.func))
(assert_return (invoke "meet-funcref-3" (i32.const 0x0)) (ref.func))
(assert_return (invoke "meet-funcref-3" (i32.const 0x1)) (ref.func))
(assert_return (invoke "meet-funcref-3" (i32.const 0x2)) (ref.func))
(assert_return (invoke "meet-funcref-4" (i32.const 0x0)) (ref.func))
(assert_return (invoke "meet-funcref-4" (i32.const 0x1)) (ref.func))
(assert_return (invoke "meet-funcref-4" (i32.const 0x2)) (ref.func))
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
    "\00\01\7f\03\82\80\80\80\00\01\00\0a\92\80\80\80"
    "\00\01\8c\80\80\80\00\00\02\40\41\01\0e\00\00\41"
    "\01\0b\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
    "\00\01\7f\03\82\80\80\80\00\01\00\0a\90\80\80\80"
    "\00\01\8a\80\80\80\00\00\02\40\0e\00\00\41\01\0b"
    "\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
    "\00\01\7f\03\82\80\80\80\00\01\00\0a\93\80\80\80"
    "\00\01\8d\80\80\80\00\00\02\7f\01\41\01\0e\00\00"
    "\41\01\0b\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
    "\00\01\7f\03\82\80\80\80\00\01\00\0a\96\80\80\80"
    "\00\01\90\80\80\80\00\00\02\7f\42\01\41\01\0e\02"
    "\00\00\00\41\01\0b\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\9a\80\80\80\00"
    "\01\94\80\80\80\00\00\02\40\02\7d\43\00\00\00\00"
    "\41\00\0e\01\00\01\0b\1a\0b\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\96\80\80\80\00"
    "\01\90\80\80\80\00\00\02\7f\02\7e\41\00\41\00\0e"
    "\01\00\01\0b\0b\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\91\80\80\80\00"
    "\01\8b\80\80\80\00\00\02\40\01\0e\02\00\00\00\0b"
    "\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\90\80\80\80\00"
    "\01\8a\80\80\80\00\00\02\40\42\00\0e\00\00\0b\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
    "\00\01\7f\03\82\80\80\80\00\01\00\0a\94\80\80\80"
    "\00\01\8e\80\80\80\00\00\02\7f\41\00\01\0e\01\00"
    "\00\41\01\0b\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
    "\00\01\7f\03\82\80\80\80\00\01\00\0a\95\80\80\80"
    "\00\01\8f\80\80\80\00\00\02\7f\41\00\02\40\41\00"
    "\0e\00\01\0b\0b\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
    "\00\01\7f\03\82\80\80\80\00\01\00\0a\95\80\80\80"
    "\00\01\8f\80\80\80\00\00\02\7f\41\00\42\00\0e\01"
    "\00\00\41\01\0b\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
    "\00\01\7f\03\82\80\80\80\00\01\00\0a\92\80\80\80"
    "\00\01\8c\80\80\80\00\00\02\40\41\01\0e\00\00\41"
    "\01\0b\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\97\80\80\80\00"
    "\01\91\80\80\80\00\00\02\40\41\00\41\00\04\7f\0e"
    "\00\00\0b\0b\45\1a\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\99\80\80\80\00"
    "\01\93\80\80\80\00\00\02\40\41\00\41\00\04\7f\41"
    "\01\0e\00\00\0b\0b\45\1a\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\91\80\80\80\00"
    "\01\8b\80\80\80\00\00\02\7f\0e\00\00\0f\0b\45\1a"
    "\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\93\80\80\80\00"
    "\01\8d\80\80\80\00\00\02\7f\41\01\0e\00\00\0f\0b"
    "\45\1a\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\86\80\80\80\00\01\60"
    "\01\7f\01\7f\03\82\80\80\80\00\01\00\0a\96\80\80"
    "\80\00\01\90\80\80\80\00\00\03\7f\02\7f\41\01\20"
    "\00\0e\01\00\01\0b\0b\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\86\80\80\80\00\01\60"
    "\01\7f\01\7f\03\82\80\80\80\00\01\00\0a\96\80\80"
    "\80\00\01\90\80\80\80\00\00\02\7f\03\7f\41\01\20"
    "\00\0e\01\00\01\0b\0b\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\91\80\80\80\00"
    "\01\8b\80\80\80\00\00\02\40\41\01\0e\01\02\01\0b"
    "\0b"
  )
  "unknown label"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\94\80\80\80\00"
    "\01\8e\80\80\80\00\00\02\40\02\40\41\01\0e\01\00"
    "\05\0b\0b\0b"
  )
  "unknown label"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\96\80\80\80\00"
    "\01\90\80\80\80\00\00\02\40\41\01\0e\02\00\81\80"
    "\80\80\01\00\0b\0b"
  )
  "unknown label"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\91\80\80\80\00"
    "\01\8b\80\80\80\00\00\02\40\41\01\0e\01\01\02\0b"
    "\0b"
  )
  "unknown label"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\94\80\80\80\00"
    "\01\8e\80\80\80\00\00\02\40\02\40\41\01\0e\01\00"
    "\05\0b\0b\0b"
  )
  "unknown label"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\96\80\80\80\00"
    "\01\90\80\80\80\00\00\02\40\41\01\0e\02\00\00\81"
    "\80\80\80\01\0b\0b"
  )
  "unknown label"
)
