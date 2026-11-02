(module definition binary
  "\00\61\73\6d\01\00\00\00\01\9e\80\80\80\00\06\60"
  "\00\00\60\00\01\7f\60\01\7f\00\60\01\7f\01\7f\60"
  "\02\7f\7f\01\7f\60\02\7f\7f\02\7f\7f\03\94\80\80"
  "\80\00\13\00\00\01\01\04\00\00\01\03\01\01\01\01"
  "\01\01\01\01\01\01\05\83\80\80\80\00\01\00\01\07"
  "\f7\81\80\80\00\10\05\65\6d\70\74\79\00\01\0e\61"
  "\73\2d\62\72\5f\69\66\2d\66\69\72\73\74\00\02\0d"
  "\61\73\2d\62\72\5f\69\66\2d\6c\61\73\74\00\03\0e"
  "\61\73\2d\73\74\6f\72\65\2d\66\69\72\73\74\00\05"
  "\0d\61\73\2d\73\74\6f\72\65\2d\6c\61\73\74\00\06"
  "\14\61\73\2d\6d\65\6d\6f\72\79\2e\67\72\6f\77\2d"
  "\76\61\6c\75\65\00\07\0b\61\73\2d\62\72\2d\76\61"
  "\6c\75\65\00\09\12\61\73\2d\6c\6f\63\61\6c\2e\73"
  "\65\74\2d\76\61\6c\75\65\00\0a\12\61\73\2d\6c\6f"
  "\63\61\6c\2e\74\65\65\2d\76\61\6c\75\65\00\0b\0f"
  "\61\73\2d\6c\6f\61\64\2d\6f\70\65\72\61\6e\64\00"
  "\0c\0b\62\72\65\61\6b\2d\76\61\6c\75\65\00\0d\05"
  "\70\61\72\61\6d\00\0e\06\70\61\72\61\6d\73\00\0f"
  "\09\70\61\72\61\6d\73\2d\69\64\00\10\0b\70\61\72"
  "\61\6d\2d\62\72\65\61\6b\00\11\0f\70\61\72\61\6d"
  "\73\2d\69\64\2d\62\72\65\61\6b\00\12\0a\c5\82\80"
  "\80\00\13\82\80\80\80\00\00\0b\88\80\80\80\00\00"
  "\03\40\0b\03\40\0b\0b\8e\80\80\80\00\00\02\7f\03"
  "\7f\41\01\0b\41\02\0d\00\0b\0b\8e\80\80\80\00\00"
  "\02\7f\41\02\03\7f\41\01\0b\0d\00\0b\0b\84\80\80"
  "\80\00\00\20\00\0b\8c\80\80\80\00\00\03\7f\41\01"
  "\0b\41\01\36\02\00\0b\8c\80\80\80\00\00\41\0a\03"
  "\7f\41\01\0b\36\02\00\0b\89\80\80\80\00\00\03\7f"
  "\41\01\0b\40\00\0b\84\80\80\80\00\00\20\00\0b\8c"
  "\80\80\80\00\00\02\7f\03\7f\41\01\0b\0c\00\0b\0b"
  "\8d\80\80\80\00\01\01\7f\03\7f\41\01\0b\21\00\20"
  "\00\0b\8b\80\80\80\00\01\01\7f\03\7f\41\01\0b\22"
  "\00\0b\8a\80\80\80\00\00\03\7f\41\01\0b\28\02\00"
  "\0b\97\80\80\80\00\00\02\7f\41\00\03\02\02\40\41"
  "\12\0c\02\0b\41\14\0c\00\0b\41\13\0b\0b\8a\80\80"
  "\80\00\00\41\01\03\03\41\02\6a\0b\0b\8a\80\80\80"
  "\00\00\41\01\41\02\03\04\6a\0b\0b\8a\80\80\80\00"
  "\00\41\01\41\02\03\05\0b\6a\0b\95\80\80\80\00\01"
  "\01\7f\41\01\03\03\41\04\6a\22\00\20\00\41\0a\49"
  "\0d\00\0b\0b\9e\80\80\80\00\01\01\7f\41\00\21\00"
  "\41\01\41\02\03\05\20\00\41\01\6a\21\00\20\00\41"
  "\0a\49\0d\00\0b\6a\0b"
)
(module instance)
(assert_return (invoke "empty"))
(assert_return (invoke "singular") (i32.const 0x7))
(assert_return (invoke "multi") (i32.const 0x8))
(assert_return (invoke "nested") (i32.const 0x9))
(assert_return (invoke "deep") (i32.const 0x96))
(assert_return (invoke "as-select-first") (i32.const 0x1))
(assert_return (invoke "as-select-mid") (i32.const 0x2))
(assert_return (invoke "as-select-last") (i32.const 0x2))
(assert_return (invoke "as-if-condition"))
(assert_return (invoke "as-if-then") (i32.const 0x1))
(assert_return (invoke "as-if-else") (i32.const 0x2))
(assert_return (invoke "as-br_if-first") (i32.const 0x1))
(assert_return (invoke "as-br_if-last") (i32.const 0x2))
(assert_return (invoke "as-br_table-first") (i32.const 0x1))
(assert_return (invoke "as-br_table-last") (i32.const 0x2))
(assert_return (invoke "as-call_indirect-first") (i32.const 0x1))
(assert_return (invoke "as-call_indirect-mid") (i32.const 0x2))
(assert_return (invoke "as-call_indirect-last") (i32.const 0x1))
(assert_return (invoke "as-store-first"))
(assert_return (invoke "as-store-last"))
(assert_return (invoke "as-memory.grow-value") (i32.const 0x1))
(assert_return (invoke "as-call-value") (i32.const 0x1))
(assert_return (invoke "as-return-value") (i32.const 0x1))
(assert_return (invoke "as-drop-operand"))
(assert_return (invoke "as-br-value") (i32.const 0x1))
(assert_return (invoke "as-local.set-value") (i32.const 0x1))
(assert_return (invoke "as-local.tee-value") (i32.const 0x1))
(assert_return (invoke "as-global.set-value") (i32.const 0x1))
(assert_return (invoke "as-load-operand") (i32.const 0x1))
(assert_return (invoke "as-unary-operand") (i32.const 0x0))
(assert_return (invoke "as-binary-operand") (i32.const 0xc))
(assert_return (invoke "as-test-operand") (i32.const 0x0))
(assert_return (invoke "as-compare-operand") (i32.const 0x0))
(assert_return (invoke "as-binary-operands") (i32.const 0xc))
(assert_return (invoke "as-compare-operands") (i32.const 0x0))
(assert_return (invoke "as-mixed-operands") (i32.const 0x1b))
(assert_return (invoke "break-bare") (i32.const 0x13))
(assert_return (invoke "break-value") (i32.const 0x12))
(assert_return
  (invoke "break-multi-value")
  (i32.const 0x12)
  (i32.const 0xffff_ffee)
  (i64.const 0x12)
)
(assert_return (invoke "break-repeated") (i32.const 0x12))
(assert_return (invoke "break-inner") (i32.const 0x1f))
(assert_return (invoke "param") (i32.const 0x3))
(assert_return (invoke "params") (i32.const 0x3))
(assert_return (invoke "params-id") (i32.const 0x3))
(assert_return (invoke "param-break") (i32.const 0xd))
(assert_return (invoke "params-break") (i32.const 0xc))
(assert_return (invoke "params-id-break") (i32.const 0x3))
(assert_return (invoke "effects") (i32.const 0x1))
(assert_return (invoke "while" (i64.const 0x0)) (i64.const 0x1))
(assert_return (invoke "while" (i64.const 0x1)) (i64.const 0x1))
(assert_return (invoke "while" (i64.const 0x2)) (i64.const 0x2))
(assert_return (invoke "while" (i64.const 0x3)) (i64.const 0x6))
(assert_return (invoke "while" (i64.const 0x5)) (i64.const 0x78))
(assert_return
  (invoke "while" (i64.const 0x14))
  (i64.const 0x21c3_677c_82b4_0000)
)
(assert_return (invoke "for" (i64.const 0x0)) (i64.const 0x1))
(assert_return (invoke "for" (i64.const 0x1)) (i64.const 0x1))
(assert_return (invoke "for" (i64.const 0x2)) (i64.const 0x2))
(assert_return (invoke "for" (i64.const 0x3)) (i64.const 0x6))
(assert_return (invoke "for" (i64.const 0x5)) (i64.const 0x78))
(assert_return
  (invoke "for" (i64.const 0x14))
  (i64.const 0x21c3_677c_82b4_0000)
)
(assert_return
  (invoke "nesting" (f32.const 0x0p+0) (f32.const 0x1.cp+2))
  (f32.const 0x0p+0)
)
(assert_return
  (invoke "nesting" (f32.const 0x1.cp+2) (f32.const 0x0p+0))
  (f32.const 0x0p+0)
)
(assert_return
  (invoke "nesting" (f32.const 0x1p+0) (f32.const 0x1p+0))
  (f32.const 0x1p+0)
)
(assert_return
  (invoke "nesting" (f32.const 0x1p+0) (f32.const 0x1p+1))
  (f32.const 0x1p+1)
)
(assert_return
  (invoke "nesting" (f32.const 0x1p+0) (f32.const 0x1.8p+1))
  (f32.const 0x1p+2)
)
(assert_return
  (invoke "nesting" (f32.const 0x1p+0) (f32.const 0x1p+2))
  (f32.const 0x1.8p+2)
)
(assert_return
  (invoke "nesting" (f32.const 0x1p+0) (f32.const 0x1.9p+6))
  (f32.const 0x1.3ecp+11)
)
(assert_return
  (invoke "nesting" (f32.const 0x1p+0) (f32.const 0x1.94p+6))
  (f32.const 0x1.452p+11)
)
(assert_return
  (invoke "nesting" (f32.const 0x1p+1) (f32.const 0x1p+0))
  (f32.const 0x1p+0)
)
(assert_return
  (invoke "nesting" (f32.const 0x1.8p+1) (f32.const 0x1p+0))
  (f32.const 0x1p+0)
)
(assert_return
  (invoke "nesting" (f32.const 0x1.4p+3) (f32.const 0x1p+0))
  (f32.const 0x1p+0)
)
(assert_return
  (invoke "nesting" (f32.const 0x1p+1) (f32.const 0x1p+1))
  (f32.const 0x1.8p+1)
)
(assert_return
  (invoke "nesting" (f32.const 0x1p+1) (f32.const 0x1.8p+1))
  (f32.const 0x1p+2)
)
(assert_return
  (invoke "nesting" (f32.const 0x1.cp+2) (f32.const 0x1p+2))
  (f32.const 0x1.49e7_9ep+3)
)
(assert_return
  (invoke "nesting" (f32.const 0x1.cp+2) (f32.const 0x1.9p+6))
  (f32.const 0x1.11d8_c4p+12)
)
(assert_return
  (invoke "nesting" (f32.const 0x1.cp+2) (f32.const 0x1.94p+6))
  (f32.const 0x1.452p+11)
)
(assert_return (invoke "type-use"))
(assert_return (invoke "br-implicit-drop") (i32.const 0x1))
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\8d\80\80\80\00"
    "\01\87\80\80\80\00\00\03\00\41\00\0b\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
    "\00\01\7f\03\82\80\80\80\00\01\00\0a\8b\80\80\80"
    "\00\01\85\80\80\80\00\00\03\40\0b\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
    "\00\01\7e\03\82\80\80\80\00\01\00\0a\8b\80\80\80"
    "\00\01\85\80\80\80\00\00\03\40\0b\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
    "\00\01\7d\03\82\80\80\80\00\01\00\0a\8b\80\80\80"
    "\00\01\85\80\80\80\00\00\03\40\0b\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
    "\00\01\7c\03\82\80\80\80\00\01\00\0a\8b\80\80\80"
    "\00\01\85\80\80\80\00\00\03\40\0b\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\8d\80\80\80\00"
    "\01\87\80\80\80\00\00\03\40\41\01\0b\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\8f\80\80\80\00"
    "\01\89\80\80\80\00\00\03\40\41\01\41\02\0b\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
    "\00\01\7f\03\82\80\80\80\00\01\00\0a\8b\80\80\80"
    "\00\01\85\80\80\80\00\00\03\7f\0b\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\86\80\80\80\00\01\60"
    "\00\02\7f\7f\03\82\80\80\80\00\01\00\0a\8b\80\80"
    "\80\00\01\85\80\80\80\00\00\03\00\0b\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
    "\00\01\7f\03\82\80\80\80\00\01\00\0a\8c\80\80\80"
    "\00\01\86\80\80\80\00\00\03\7f\01\0b\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\86\80\80\80\00\01\60"
    "\00\02\7f\7f\03\82\80\80\80\00\01\00\0a\8c\80\80"
    "\80\00\01\86\80\80\80\00\00\03\00\01\0b\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
    "\00\01\7f\03\82\80\80\80\00\01\00\0a\90\80\80\80"
    "\00\01\8a\80\80\80\00\00\03\7f\43\00\00\00\00\0b"
    "\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\86\80\80\80\00\01\60"
    "\00\02\7f\7f\03\82\80\80\80\00\01\00\0a\8d\80\80"
    "\80\00\01\87\80\80\80\00\00\03\00\41\00\0b\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\86\80\80\80\00\01\60"
    "\00\02\7f\7f\03\82\80\80\80\00\01\00\0a\8f\80\80"
    "\80\00\01\89\80\80\80\00\00\41\01\03\00\41\02\0b"
    "\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
    "\00\01\7f\03\82\80\80\80\00\01\00\0a\8f\80\80\80"
    "\00\01\89\80\80\80\00\00\03\7f\41\01\41\02\0b\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
    "\00\01\7f\03\82\80\80\80\00\01\00\0a\8f\80\80\80"
    "\00\01\89\80\80\80\00\00\03\7e\00\00\00\1b\0b\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\91\80\80\80\00"
    "\01\8b\80\80\80\00\00\41\00\02\40\03\7f\0b\1a\0b"
    "\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\91\80\80\80\00"
    "\01\8b\80\80\80\00\00\41\00\03\40\03\7f\0b\1a\0b"
    "\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\93\80\80\80\00"
    "\01\8d\80\80\80\00\00\41\00\41\00\04\40\03\7f\0b"
    "\1a\0b\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\88\80\80\80\00\02\60"
    "\00\00\60\01\7f\00\03\82\80\80\80\00\01\00\0a\8c"
    "\80\80\80\00\01\86\80\80\80\00\00\03\01\1a\0b\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\89\80\80\80\00\02\60"
    "\00\00\60\02\7f\7c\00\03\82\80\80\80\00\01\00\0a"
    "\8d\80\80\80\00\01\87\80\80\80\00\00\03\01\1a\1a"
    "\0b\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\88\80\80\80\00\02\60"
    "\00\00\60\01\7f\00\03\82\80\80\80\00\01\00\0a\91"
    "\80\80\80\00\01\8b\80\80\80\00\00\43\00\00\00\00"
    "\03\01\1a\0b\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\89\80\80\80\00\02\60"
    "\00\00\60\02\7d\7f\00\03\82\80\80\80\00\01\00\0a"
    "\92\80\80\80\00\01\8c\80\80\80\00\00\43\00\00\00"
    "\00\03\01\1a\1a\0b\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\88\80\80\80\00\02\60"
    "\00\00\60\01\7f\00\03\82\80\80\80\00\01\00\0a\8f"
    "\80\80\80\00\01\89\80\80\80\00\00\02\40\03\01\1a"
    "\0b\0b\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\89\80\80\80\00\02\60"
    "\00\00\60\02\7f\7c\00\03\82\80\80\80\00\01\00\0a"
    "\90\80\80\80\00\01\8a\80\80\80\00\00\02\40\03\01"
    "\1a\1a\0b\0b\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\88\80\80\80\00\02\60"
    "\00\00\60\01\7f\00\03\82\80\80\80\00\01\00\0a\94"
    "\80\80\80\00\01\8e\80\80\80\00\00\02\40\43\00\00"
    "\00\00\03\01\1a\0b\0b\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\89\80\80\80\00\02\60"
    "\00\00\60\02\7d\7f\00\03\82\80\80\80\00\01\00\0a"
    "\95\80\80\80\00\01\8f\80\80\80\00\00\02\40\43\00"
    "\00\00\00\03\01\1a\1a\0b\0b\0b"
  )
  "type mismatch"
)
