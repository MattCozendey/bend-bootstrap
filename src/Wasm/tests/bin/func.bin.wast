(module definition binary
  "\00\61\73\6d\01\00\00\00\01\98\80\80\80\00\05\60"
  "\00\00\60\00\01\7f\60\00\03\7f\7f\7f\60\01\7f\00"
  "\60\02\7f\7f\01\7f\03\a3\80\80\80\00\22\00\00\00"
  "\00\00\00\00\00\00\00\00\03\03\00\00\00\01\03\01"
  "\03\00\00\01\01\04\04\00\01\02\00\01\02\03\01\07"
  "\8f\82\80\80\00\13\01\66\00\02\01\67\00\04\0a\74"
  "\79\70\65\2d\75\73\65\2d\31\00\0f\0a\74\79\70\65"
  "\2d\75\73\65\2d\32\00\10\0a\74\79\70\65\2d\75\73"
  "\65\2d\33\00\11\0a\74\79\70\65\2d\75\73\65\2d\35"
  "\00\12\0a\74\79\70\65\2d\75\73\65\2d\36\00\13\0f"
  "\6c\6f\63\61\6c\2d\66\69\72\73\74\2d\69\33\32\00"
  "\16\10\6c\6f\63\61\6c\2d\73\65\63\6f\6e\64\2d\69"
  "\33\32\00\17\0f\70\61\72\61\6d\2d\66\69\72\73\74"
  "\2d\69\33\32\00\18\10\70\61\72\61\6d\2d\73\65\63"
  "\6f\6e\64\2d\69\33\32\00\19\05\65\6d\70\74\79\00"
  "\1a\09\76\61\6c\75\65\2d\69\33\32\00\1b\11\76\61"
  "\6c\75\65\2d\69\33\32\2d\69\33\32\2d\69\33\32\00"
  "\1c\0b\62\72\65\61\6b\2d\65\6d\70\74\79\00\1d\09"
  "\62\72\65\61\6b\2d\69\33\32\00\1e\11\62\72\65\61"
  "\6b\2d\69\33\32\2d\69\33\32\2d\69\33\32\00\1f\11"
  "\62\72\65\61\6b\2d\62\72\5f\69\66\2d\65\6d\70\74"
  "\79\00\20\0e\69\6e\69\74\2d\6c\6f\63\61\6c\2d\69"
  "\33\32\00\21\0a\a3\82\80\80\00\22\82\80\80\80\00"
  "\00\0b\82\80\80\80\00\00\0b\82\80\80\80\00\00\0b"
  "\82\80\80\80\00\00\0b\82\80\80\80\00\00\0b\82\80"
  "\80\80\00\00\0b\82\80\80\80\00\00\0b\84\80\80\80"
  "\00\01\01\7f\0b\84\80\80\80\00\01\01\7f\0b\82\80"
  "\80\80\00\00\0b\82\80\80\80\00\00\0b\82\80\80\80"
  "\00\00\0b\82\80\80\80\00\00\0b\82\80\80\80\00\00"
  "\0b\82\80\80\80\00\00\0b\82\80\80\80\00\00\0b\84"
  "\80\80\80\00\00\41\00\0b\82\80\80\80\00\00\0b\84"
  "\80\80\80\00\00\41\00\0b\82\80\80\80\00\00\0b\82"
  "\80\80\80\00\00\0b\82\80\80\80\00\00\0b\86\80\80"
  "\80\00\01\02\7f\20\00\0b\86\80\80\80\00\01\02\7f"
  "\20\01\0b\84\80\80\80\00\00\20\00\0b\84\80\80\80"
  "\00\00\20\01\0b\82\80\80\80\00\00\0b\85\80\80\80"
  "\00\00\41\cd\00\0b\88\80\80\80\00\00\41\01\41\02"
  "\41\03\0b\84\80\80\80\00\00\0c\00\0b\87\80\80\80"
  "\00\00\41\cf\00\0c\00\0b\8a\80\80\80\00\00\41\01"
  "\41\02\41\03\0c\00\0b\86\80\80\80\00\00\20\00\0d"
  "\00\0b\86\80\80\80\00\01\01\7f\20\00\0b"
)
(module instance)
(assert_return (invoke "type-use-1"))
(assert_return (invoke "type-use-2") (i32.const 0x0))
(assert_return (invoke "type-use-3" (i32.const 0x1)))
(assert_return
  (invoke "type-use-4" (i32.const 0x1) (f64.const 0x1p+0) (i32.const 0x1))
  (i32.const 0x0)
)
(assert_return (invoke "type-use-5") (i32.const 0x0))
(assert_return (invoke "type-use-6" (i32.const 0x1)))
(assert_return
  (invoke "type-use-7" (i32.const 0x1) (f64.const 0x1p+0) (i32.const 0x1))
  (i32.const 0x0)
)
(assert_return (invoke "local-first-i32") (i32.const 0x0))
(assert_return (invoke "local-first-i64") (i64.const 0x0))
(assert_return (invoke "local-first-f32") (f32.const 0x0p+0))
(assert_return (invoke "local-first-f64") (f64.const 0x0p+0))
(assert_return (invoke "local-second-i32") (i32.const 0x0))
(assert_return (invoke "local-second-i64") (i64.const 0x0))
(assert_return (invoke "local-second-f32") (f32.const 0x0p+0))
(assert_return (invoke "local-second-f64") (f64.const 0x0p+0))
(assert_return (invoke "local-mixed") (f64.const 0x0p+0))
(assert_return
  (invoke "param-first-i32" (i32.const 0x2) (i32.const 0x3))
  (i32.const 0x2)
)
(assert_return
  (invoke "param-first-i64" (i64.const 0x2) (i64.const 0x3))
  (i64.const 0x2)
)
(assert_return
  (invoke "param-first-f32" (f32.const 0x1p+1) (f32.const 0x1.8p+1))
  (f32.const 0x1p+1)
)
(assert_return
  (invoke "param-first-f64" (f64.const 0x1p+1) (f64.const 0x1.8p+1))
  (f64.const 0x1p+1)
)
(assert_return
  (invoke "param-second-i32" (i32.const 0x2) (i32.const 0x3))
  (i32.const 0x3)
)
(assert_return
  (invoke "param-second-i64" (i64.const 0x2) (i64.const 0x3))
  (i64.const 0x3)
)
(assert_return
  (invoke "param-second-f32" (f32.const 0x1p+1) (f32.const 0x1.8p+1))
  (f32.const 0x1.8p+1)
)
(assert_return
  (invoke "param-second-f64" (f64.const 0x1p+1) (f64.const 0x1.8p+1))
  (f64.const 0x1.8p+1)
)
(assert_return
  (invoke "param-mixed"
    (f32.const 0x1p+0)
    (i32.const 0x2)
    (i64.const 0x3)
    (i32.const 0x4)
    (f64.const 0x1.6p+2)
    (i32.const 0x6)
  )
  (f64.const 0x1.6p+2)
)
(assert_return (invoke "empty"))
(assert_return (invoke "value-void"))
(assert_return (invoke "value-i32") (i32.const 0x4d))
(assert_return (invoke "value-i64") (i64.const 0x1e61))
(assert_return (invoke "value-f32") (f32.const 0x1.36cc_ccp+6))
(assert_return (invoke "value-f64") (f64.const 0x1.3714_7ae1_47ae_1p+6))
(assert_return (invoke "value-i32-f64") (i32.const 0x4d) (f64.const 0x1.cp+2))
(assert_return
  (invoke "value-i32-i32-i32")
  (i32.const 0x1)
  (i32.const 0x2)
  (i32.const 0x3)
)
(assert_return (invoke "value-block-void"))
(assert_return (invoke "value-block-i32") (i32.const 0x4d))
(assert_return (invoke "value-block-i32-i64") (i32.const 0x1) (i64.const 0x2))
(assert_return (invoke "return-empty"))
(assert_return (invoke "return-i32") (i32.const 0x4e))
(assert_return (invoke "return-i64") (i64.const 0x1ec6))
(assert_return (invoke "return-f32") (f32.const 0x1.3acc_ccp+6))
(assert_return (invoke "return-f64") (f64.const 0x1.3b1e_b851_eb85_2p+6))
(assert_return
  (invoke "return-i32-f64")
  (i32.const 0x4e)
  (f64.const 0x1.3b1e_b851_eb85_2p+6)
)
(assert_return
  (invoke "return-i32-i32-i32")
  (i32.const 0x1)
  (i32.const 0x2)
  (i32.const 0x3)
)
(assert_return (invoke "return-block-i32") (i32.const 0x4d))
(assert_return (invoke "return-block-i32-i64") (i32.const 0x1) (i64.const 0x2))
(assert_return (invoke "break-empty"))
(assert_return (invoke "break-i32") (i32.const 0x4f))
(assert_return (invoke "break-i64") (i64.const 0x1f2b))
(assert_return (invoke "break-f32") (f32.const 0x1.3f99_9ap+6))
(assert_return (invoke "break-f64") (f64.const 0x1.3f28_f5c2_8f5c_3p+6))
(assert_return
  (invoke "break-i32-f64")
  (i32.const 0x4f)
  (f64.const 0x1.3f28_f5c2_8f5c_3p+6)
)
(assert_return
  (invoke "break-i32-i32-i32")
  (i32.const 0x1)
  (i32.const 0x2)
  (i32.const 0x3)
)
(assert_return (invoke "break-block-i32") (i32.const 0x4d))
(assert_return (invoke "break-block-i32-i64") (i32.const 0x1) (i64.const 0x2))
(assert_return (invoke "break-br_if-empty" (i32.const 0x0)))
(assert_return (invoke "break-br_if-empty" (i32.const 0x2)))
(assert_return (invoke "break-br_if-num" (i32.const 0x0)) (i32.const 0x33))
(assert_return (invoke "break-br_if-num" (i32.const 0x1)) (i32.const 0x32))
(assert_return
  (invoke "break-br_if-num-num" (i32.const 0x0))
  (i32.const 0x33)
  (i64.const 0x34)
)
(assert_return
  (invoke "break-br_if-num-num" (i32.const 0x1))
  (i32.const 0x32)
  (i64.const 0x33)
)
(assert_return (invoke "break-br_table-empty" (i32.const 0x0)))
(assert_return (invoke "break-br_table-empty" (i32.const 0x1)))
(assert_return (invoke "break-br_table-empty" (i32.const 0x5)))
(assert_return (invoke "break-br_table-empty" (i32.const 0xffff_ffff)))
(assert_return (invoke "break-br_table-num" (i32.const 0x0)) (i32.const 0x32))
(assert_return (invoke "break-br_table-num" (i32.const 0x1)) (i32.const 0x32))
(assert_return (invoke "break-br_table-num" (i32.const 0xa)) (i32.const 0x32))
(assert_return
  (invoke "break-br_table-num" (i32.const 0xffff_ff9c))
  (i32.const 0x32)
)
(assert_return
  (invoke "break-br_table-num-num" (i32.const 0x0))
  (f32.const 0x1.9p+5)
  (i64.const 0x33)
)
(assert_return
  (invoke "break-br_table-num-num" (i32.const 0x1))
  (f32.const 0x1.9p+5)
  (i64.const 0x33)
)
(assert_return
  (invoke "break-br_table-num-num" (i32.const 0xa))
  (f32.const 0x1.9p+5)
  (i64.const 0x33)
)
(assert_return
  (invoke "break-br_table-num-num" (i32.const 0xffff_ff9c))
  (f32.const 0x1.9p+5)
  (i64.const 0x33)
)
(assert_return (invoke "break-br_table-nested-empty" (i32.const 0x0)))
(assert_return (invoke "break-br_table-nested-empty" (i32.const 0x1)))
(assert_return (invoke "break-br_table-nested-empty" (i32.const 0x3)))
(assert_return (invoke "break-br_table-nested-empty" (i32.const 0xffff_fffe)))
(assert_return
  (invoke "break-br_table-nested-num" (i32.const 0x0))
  (i32.const 0x34)
)
(assert_return
  (invoke "break-br_table-nested-num" (i32.const 0x1))
  (i32.const 0x32)
)
(assert_return
  (invoke "break-br_table-nested-num" (i32.const 0x2))
  (i32.const 0x34)
)
(assert_return
  (invoke "break-br_table-nested-num" (i32.const 0xffff_fffd))
  (i32.const 0x34)
)
(assert_return
  (invoke "break-br_table-nested-num-num" (i32.const 0x0))
  (i32.const 0x65)
  (i32.const 0x34)
)
(assert_return
  (invoke "break-br_table-nested-num-num" (i32.const 0x1))
  (i32.const 0x32)
  (i32.const 0x33)
)
(assert_return
  (invoke "break-br_table-nested-num-num" (i32.const 0x2))
  (i32.const 0x65)
  (i32.const 0x34)
)
(assert_return
  (invoke "break-br_table-nested-num-num" (i32.const 0xffff_fffd))
  (i32.const 0x65)
  (i32.const 0x34)
)
(assert_return
  (invoke "large-sig"
    (i32.const 0x0)
    (i64.const 0x1)
    (f32.const 0x1p+1)
    (f32.const 0x1.8p+1)
    (i32.const 0x4)
    (f64.const 0x1.4p+2)
    (f32.const 0x1.8p+2)
    (i32.const 0x7)
    (i32.const 0x8)
    (i32.const 0x9)
    (f32.const 0x1.4p+3)
    (f64.const 0x1.6p+3)
    (f64.const 0x1.8p+3)
    (f64.const 0x1.ap+3)
    (i32.const 0xe)
    (i32.const 0xf)
    (f32.const 0x1p+4)
  )
  (f64.const 0x1.4p+2)
  (f32.const 0x1p+1)
  (i32.const 0x0)
  (i32.const 0x8)
  (i32.const 0x7)
  (i64.const 0x1)
  (f32.const 0x1.8p+1)
  (i32.const 0x9)
  (i32.const 0x4)
  (f32.const 0x1.8p+2)
  (f64.const 0x1.ap+3)
  (f64.const 0x1.6p+3)
  (i32.const 0xf)
  (f32.const 0x1p+4)
  (i32.const 0xe)
  (f64.const 0x1.8p+3)
)
(assert_return (invoke "init-local-i32") (i32.const 0x0))
(assert_return (invoke "init-local-i64") (i64.const 0x0))
(assert_return (invoke "init-local-f32") (f32.const 0x0p+0))
(assert_return (invoke "init-local-f64") (f64.const 0x0p+0))
(module definition binary
  "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
  "\01\7f\00\03\83\80\80\80\00\02\00\00\0a\8f\80\80"
  "\80\00\02\82\80\80\80\00\00\0b\82\80\80\80\00\00"
  "\0b"
)
(module instance)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\89\80\80\80\00\02\60"
    "\01\7f\00\60\00\01\7c\03\85\80\80\80\00\04\01\00"
    "\01\02\0a\af\80\80\80\00\04\8b\80\80\80\00\00\44"
    "\00\00\00\00\00\00\00\00\0b\82\80\80\80\00\00\0b"
    "\8b\80\80\80\00\00\44\00\00\00\00\00\00\f0\3f\0b"
    "\82\80\80\80\00\00\0b"
  )
  "unknown type"
)
(module definition binary
  "\00\61\73\6d\01\00\00\00\01\8a\80\80\80\00\02\60"
  "\00\01\7f\60\01\7f\01\7f\03\84\80\80\80\00\03\01"
  "\01\00\07\89\80\80\80\00\02\01\66\00\00\01\70\00"
  "\02\0a\a6\80\80\80\00\03\86\80\80\80\00\01\01\7f"
  "\20\01\0b\86\80\80\80\00\01\01\7f\20\01\0b\8a\80"
  "\80\80\00\01\01\7f\41\2a\21\00\20\00\0b"
)
(module instance)
(assert_return (invoke "f" (i32.const 0x2a)) (i32.const 0x0))
(assert_return (invoke "g" (i32.const 0x2a)) (i32.const 0x0))
(assert_return (invoke "p") (i32.const 0x2a))
(module definition binary
  "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
  "\00\00\03\83\80\80\80\00\02\00\00\0a\8f\80\80\80"
  "\00\02\82\80\80\80\00\00\0b\82\80\80\80\00\00\0b"
)
(module instance)
(assert_return (invoke "signature-explicit-reused"))
(assert_return (invoke "signature-implicit-reused"))
(assert_return (invoke "signature-explicit-duplicate"))
(assert_return (invoke "signature-implicit-duplicate"))
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\03\82\80\80\80\00\01\04"
    "\0a\88\80\80\80\00\01\82\80\80\80\00\00\0b"
  )
  "unknown type"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\83\80\80\80\00\02\00\04\09\85\80\80\80"
    "\00\01\03\00\01\01\0a\92\80\80\80\00\02\85\80\80"
    "\80\00\00\d2\01\1a\0b\82\80\80\80\00\00\0b"
  )
  "unknown type"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
    "\00\01\7e\03\82\80\80\80\00\01\00\0a\8c\80\80\80"
    "\00\01\86\80\80\80\00\01\01\7f\20\00\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\8d\80\80\80\00"
    "\01\87\80\80\80\00\01\01\7d\20\00\45\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\8f\80\80\80\00"
    "\01\89\80\80\80\00\02\01\7c\01\7e\20\01\9a\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\8e\80\80\80\00"
    "\01\88\80\80\80\00\01\01\64\00\20\00\1a\0b"
  )
  "uninitialized local"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\86\80\80\80\00\01\60"
    "\01\7f\01\7e\03\82\80\80\80\00\01\00\0a\8a\80\80"
    "\80\00\01\84\80\80\80\00\00\20\00\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
    "\01\7d\00\03\82\80\80\80\00\01\00\0a\8b\80\80\80"
    "\00\01\85\80\80\80\00\00\20\00\45\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\86\80\80\80\00\01\60"
    "\02\7c\7e\00\03\82\80\80\80\00\01\00\0a\8b\80\80"
    "\80\00\01\85\80\80\80\00\00\20\01\9a\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
    "\00\01\7f\03\82\80\80\80\00\01\00\0a\88\80\80\80"
    "\00\01\82\80\80\80\00\00\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
    "\00\01\7e\03\82\80\80\80\00\01\00\0a\88\80\80\80"
    "\00\01\82\80\80\80\00\00\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
    "\00\01\7d\03\82\80\80\80\00\01\00\0a\88\80\80\80"
    "\00\01\82\80\80\80\00\00\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
    "\00\01\7c\03\82\80\80\80\00\01\00\0a\88\80\80\80"
    "\00\01\82\80\80\80\00\00\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\86\80\80\80\00\01\60"
    "\00\02\7c\7f\03\82\80\80\80\00\01\00\0a\88\80\80"
    "\80\00\01\82\80\80\80\00\00\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
    "\00\01\7f\03\82\80\80\80\00\01\00\0a\89\80\80\80"
    "\00\01\83\80\80\80\00\00\01\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\86\80\80\80\00\01\60"
    "\00\02\7f\7f\03\82\80\80\80\00\01\00\0a\89\80\80"
    "\80\00\01\83\80\80\80\00\00\01\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\8a\80\80\80\00"
    "\01\84\80\80\80\00\00\41\00\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\8c\80\80\80\00"
    "\01\86\80\80\80\00\00\41\00\42\00\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
    "\00\01\7f\03\82\80\80\80\00\01\00\0a\8d\80\80\80"
    "\00\01\87\80\80\80\00\00\43\00\00\00\00\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\86\80\80\80\00\01\60"
    "\00\02\7d\7d\03\82\80\80\80\00\01\00\0a\8d\80\80"
    "\80\00\01\87\80\80\80\00\00\43\00\00\00\00\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
    "\00\01\7d\03\82\80\80\80\00\01\00\0a\92\80\80\80"
    "\00\01\8c\80\80\80\00\00\43\00\00\00\00\43\00\00"
    "\00\00\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
    "\00\01\7f\03\82\80\80\80\00\01\00\0a\89\80\80\80"
    "\00\01\83\80\80\80\00\00\0f\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\86\80\80\80\00\01\60"
    "\00\02\7f\7f\03\82\80\80\80\00\01\00\0a\89\80\80"
    "\80\00\01\83\80\80\80\00\00\0f\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
    "\00\01\7f\03\82\80\80\80\00\01\00\0a\8a\80\80\80"
    "\00\01\84\80\80\80\00\00\01\0f\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\86\80\80\80\00\01\60"
    "\00\02\7f\7e\03\82\80\80\80\00\01\00\0a\8a\80\80"
    "\80\00\01\84\80\80\80\00\00\01\0f\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
    "\00\01\7f\03\82\80\80\80\00\01\00\0a\8b\80\80\80"
    "\00\01\85\80\80\80\00\00\42\00\0f\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\86\80\80\80\00\01\60"
    "\00\02\7e\7e\03\82\80\80\80\00\01\00\0a\8b\80\80"
    "\80\00\01\85\80\80\80\00\00\42\00\0f\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
    "\00\01\7f\03\82\80\80\80\00\01\00\0a\8b\80\80\80"
    "\00\01\85\80\80\80\00\00\0f\41\01\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\86\80\80\80\00\01\60"
    "\00\02\7f\7f\03\82\80\80\80\00\01\00\0a\8d\80\80"
    "\80\00\01\87\80\80\80\00\00\0f\41\01\41\02\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\86\80\80\80\00\01\60"
    "\00\02\7f\7f\03\82\80\80\80\00\01\00\0a\8d\80\80"
    "\80\00\01\87\80\80\80\00\00\41\01\0f\41\02\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
    "\00\01\7f\03\82\80\80\80\00\01\00\0a\8c\80\80\80"
    "\00\01\86\80\80\80\00\00\01\0f\41\01\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\86\80\80\80\00\01\60"
    "\00\02\7f\7f\03\82\80\80\80\00\01\00\0a\8c\80\80"
    "\80\00\01\86\80\80\80\00\00\01\0f\41\01\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
    "\00\01\7f\03\82\80\80\80\00\01\00\0a\8d\80\80\80"
    "\00\01\87\80\80\80\00\00\42\01\0f\41\01\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\86\80\80\80\00\01\60"
    "\00\02\7f\7f\03\82\80\80\80\00\01\00\0a\8f\80\80"
    "\80\00\01\89\80\80\80\00\00\42\01\0f\41\01\41\02"
    "\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
    "\00\01\7f\03\82\80\80\80\00\01\00\0a\8e\80\80\80"
    "\00\01\88\80\80\80\00\00\42\01\0f\41\01\0f\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\86\80\80\80\00\01\60"
    "\00\02\7f\7f\03\82\80\80\80\00\01\00\0a\90\80\80"
    "\80\00\01\8a\80\80\80\00\00\41\01\0f\41\01\41\02"
    "\0f\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
    "\00\01\7f\03\82\80\80\80\00\01\00\0a\8a\80\80\80"
    "\00\01\84\80\80\80\00\00\0c\00\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\86\80\80\80\00\01\60"
    "\00\02\7f\7f\03\82\80\80\80\00\01\00\0a\8a\80\80"
    "\80\00\01\84\80\80\80\00\00\0c\00\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
    "\00\01\7f\03\82\80\80\80\00\01\00\0a\8f\80\80\80"
    "\00\01\89\80\80\80\00\00\43\00\00\00\00\0c\00\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\86\80\80\80\00\01\60"
    "\00\02\7f\7f\03\82\80\80\80\00\01\00\0a\8c\80\80"
    "\80\00\01\86\80\80\80\00\00\41\00\0c\00\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
    "\00\01\7f\03\82\80\80\80\00\01\00\0a\8c\80\80\80"
    "\00\01\86\80\80\80\00\00\0c\00\41\01\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\86\80\80\80\00\01\60"
    "\00\02\7f\7f\03\82\80\80\80\00\01\00\0a\8e\80\80"
    "\80\00\01\88\80\80\80\00\00\0c\00\41\01\41\02\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
    "\00\01\7f\03\82\80\80\80\00\01\00\0a\8e\80\80\80"
    "\00\01\88\80\80\80\00\00\42\01\0c\00\41\01\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\86\80\80\80\00\01\60"
    "\00\02\7f\7f\03\82\80\80\80\00\01\00\0a\90\80\80"
    "\80\00\01\8a\80\80\80\00\00\41\01\0c\00\41\01\41"
    "\02\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
    "\00\01\7f\03\82\80\80\80\00\01\00\0a\90\80\80\80"
    "\00\01\8a\80\80\80\00\00\42\01\0c\00\41\01\0c\00"
    "\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
    "\00\01\7f\03\82\80\80\80\00\01\00\0a\91\80\80\80"
    "\00\01\8b\80\80\80\00\00\02\40\0c\01\0b\41\01\0c"
    "\00\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\86\80\80\80\00\01\60"
    "\00\02\7f\7f\03\82\80\80\80\00\01\00\0a\93\80\80"
    "\80\00\01\8d\80\80\80\00\00\02\40\0c\01\0b\41\01"
    "\41\02\0c\00\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
    "\00\01\7f\03\82\80\80\80\00\01\00\0a\92\80\80\80"
    "\00\01\8c\80\80\80\00\00\02\40\01\0c\01\0b\41\01"
    "\0c\00\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\86\80\80\80\00\01\60"
    "\00\02\7f\7f\03\82\80\80\80\00\01\00\0a\94\80\80"
    "\80\00\01\8e\80\80\80\00\00\02\40\01\0c\01\0b\41"
    "\01\41\02\0c\00\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
    "\00\01\7f\03\82\80\80\80\00\01\00\0a\93\80\80\80"
    "\00\01\8d\80\80\80\00\00\02\40\42\01\0c\01\0b\41"
    "\01\0c\00\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\86\80\80\80\00\01\60"
    "\00\02\7f\7f\03\82\80\80\80\00\01\00\0a\95\80\80"
    "\80\00\01\8f\80\80\80\00\00\02\7f\41\01\0c\01\0b"
    "\41\01\41\02\0c\00\0b"
  )
  "type mismatch"
)
