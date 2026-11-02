(module definition binary
  "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
  "\00\01\7f\03\85\80\80\80\00\04\00\00\00\00\07\bd"
  "\80\80\80\00\04\0c\69\33\32\2d\64\65\63\2d\73\65"
  "\70\31\00\00\0c\69\33\32\2d\64\65\63\2d\73\65\70"
  "\32\00\01\0c\69\33\32\2d\68\65\78\2d\73\65\70\31"
  "\00\02\0c\69\33\32\2d\68\65\78\2d\73\65\70\32\00"
  "\03\0a\ae\80\80\80\00\04\86\80\80\80\00\00\41\c0"
  "\84\3d\0b\85\80\80\80\00\00\41\e8\07\0b\88\80\80"
  "\80\00\00\41\99\81\bc\d0\00\0b\86\80\80\80\00\00"
  "\41\8f\d4\06\0b"
)
(module instance)
(assert_return (invoke "i32.test") (i32.const 0xbad_d00d))
(assert_return (invoke "i32.umax") (i32.const 0xffff_ffff))
(assert_return (invoke "i32.smax") (i32.const 0x7fff_ffff))
(assert_return (invoke "i32.neg_smax") (i32.const 0x8000_0001))
(assert_return (invoke "i32.smin") (i32.const 0x8000_0000))
(assert_return (invoke "i32.alt_smin") (i32.const 0x8000_0000))
(assert_return (invoke "i32.inc_smin") (i32.const 0x8000_0001))
(assert_return (invoke "i32.neg_zero") (i32.const 0x0))
(assert_return (invoke "i32.not_octal") (i32.const 0xa))
(assert_return (invoke "i32.unsigned_decimal") (i32.const 0xffff_ffff))
(assert_return (invoke "i32.plus_sign") (i32.const 0x2a))
(assert_return (invoke "i64.test") (i64.const 0xcab_ba6e_0ba6_6a6e))
(assert_return (invoke "i64.umax") (i64.const 0xffff_ffff_ffff_ffff))
(assert_return (invoke "i64.smax") (i64.const 0x7fff_ffff_ffff_ffff))
(assert_return (invoke "i64.neg_smax") (i64.const 0x8000_0000_0000_0001))
(assert_return (invoke "i64.smin") (i64.const 0x8000_0000_0000_0000))
(assert_return (invoke "i64.alt_smin") (i64.const 0x8000_0000_0000_0000))
(assert_return (invoke "i64.inc_smin") (i64.const 0x8000_0000_0000_0001))
(assert_return (invoke "i64.neg_zero") (i64.const 0x0))
(assert_return (invoke "i64.not_octal") (i64.const 0xa))
(assert_return
  (invoke "i64.unsigned_decimal")
  (i64.const 0xffff_ffff_ffff_ffff)
)
(assert_return (invoke "i64.plus_sign") (i64.const 0x2a))
(assert_return (invoke "i32-dec-sep1") (i32.const 0xf_4240))
(assert_return (invoke "i32-dec-sep2") (i32.const 0x3e8))
(assert_return (invoke "i32-hex-sep1") (i32.const 0xa0f_0099))
(assert_return (invoke "i32-hex-sep2") (i32.const 0x1_aa0f))
(assert_return (invoke "i64-dec-sep1") (i64.const 0xf_4240))
(assert_return (invoke "i64-dec-sep2") (i64.const 0x3e8))
(assert_return (invoke "i64-hex-sep1") (i64.const 0xa_f00f_0000_9999))
(assert_return (invoke "i64-hex-sep2") (i64.const 0x1_aa0f))
