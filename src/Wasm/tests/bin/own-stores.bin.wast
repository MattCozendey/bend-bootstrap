(module definition binary
  "\00\61\73\6d\01\00\00\00\01\8b\80\80\80\00\02\60"
  "\01\7f\01\7f\60\02\7f\7f\00\03\89\80\80\80\00\08"
  "\01\01\01\01\01\01\00\00\05\83\80\80\80\00\01\00"
  "\01\07\df\80\80\80\00\08\05\73\74\6f\72\65\00\00"
  "\0a\73\74\6f\72\65\5f\6f\66\66\34\00\01\0a\73\74"
  "\6f\72\65\5f\6f\66\66\38\00\02\0b\73\74\6f\72\65"
  "\5f\6f\66\66\31\32\00\03\0b\73\74\6f\72\65\5f\6f"
  "\66\66\31\36\00\04\0a\73\74\6f\72\65\5f\62\79\74"
  "\65\00\05\04\6c\6f\61\64\00\06\09\6c\6f\61\64\5f"
  "\62\79\74\65\00\07\0a\ed\80\80\80\00\08\89\80\80"
  "\80\00\00\20\00\20\01\36\02\00\0b\89\80\80\80\00"
  "\00\20\00\20\01\36\02\04\0b\89\80\80\80\00\00\20"
  "\00\20\01\36\02\08\0b\89\80\80\80\00\00\20\00\20"
  "\01\36\02\0c\0b\89\80\80\80\00\00\20\00\20\01\36"
  "\02\10\0b\89\80\80\80\00\00\20\00\20\01\3a\00\00"
  "\0b\87\80\80\80\00\00\20\00\28\02\00\0b\87\80\80"
  "\80\00\00\20\00\2d\00\00\0b"
)
(module instance)
(assert_return (invoke "store_off4" (i32.const 0x64) (i32.const 0x102_0304)))
(assert_return (invoke "load" (i32.const 0x68)) (i32.const 0x102_0304))
(assert_return (invoke "load" (i32.const 0x64)) (i32.const 0x0))
(assert_return (invoke "store_off8" (i32.const 0xc8) (i32.const 0x506_0708)))
(assert_return (invoke "load" (i32.const 0xd0)) (i32.const 0x506_0708))
(assert_return (invoke "load" (i32.const 0xc8)) (i32.const 0x0))
(assert_return (invoke "store_off12" (i32.const 0x12c) (i32.const 0x90a_0b0c)))
(assert_return (invoke "load" (i32.const 0x138)) (i32.const 0x90a_0b0c))
(assert_return (invoke "load" (i32.const 0x12c)) (i32.const 0x0))
(assert_return (invoke "store_off16" (i32.const 0x190) (i32.const 0xd0e_0f10)))
(assert_return (invoke "load" (i32.const 0x1a0)) (i32.const 0xd0e_0f10))
(assert_return (invoke "load" (i32.const 0x190)) (i32.const 0x0))
(assert_return
  (invoke "store_off16" (i32.const 0xffec) (i32.const 0x1111_1111))
)
(assert_return (invoke "load" (i32.const 0xfffc)) (i32.const 0x1111_1111))
(assert_trap
  (invoke "store_off16" (i32.const 0xffed) (i32.const 0x2222_2222))
  "out of bounds memory access"
)
(assert_return (invoke "load" (i32.const 0xfffc)) (i32.const 0x1111_1111))
(assert_return (invoke "store_byte" (i32.const 0xffff) (i32.const 0xab)))
(assert_return (invoke "load_byte" (i32.const 0xffff)) (i32.const 0xab))
(assert_trap
  (invoke "store_byte" (i32.const 0x1_0000) (i32.const 0xcd))
  "out of bounds memory access"
)
(assert_trap
  (invoke "store_off16" (i32.const 0xffff_fff4) (i32.const 0x3333_3333))
  "out of bounds memory access"
)
(assert_return (invoke "load" (i32.const 0x4)) (i32.const 0x0))
(assert_return (invoke "store" (i32.const 0x1f4) (i32.const 0xaabb_ccdd)))
(assert_return (invoke "store_byte" (i32.const 0x1f5) (i32.const 0x1234_5678)))
(assert_return (invoke "load" (i32.const 0x1f4)) (i32.const 0xaabb_78dd))
(assert_return (invoke "store" (i32.const 0x258) (i32.const 0x1122_3344)))
(assert_return (invoke "load_byte" (i32.const 0x258)) (i32.const 0x44))
(assert_return (invoke "load_byte" (i32.const 0x259)) (i32.const 0x33))
(assert_return (invoke "load_byte" (i32.const 0x25a)) (i32.const 0x22))
(assert_return (invoke "load_byte" (i32.const 0x25b)) (i32.const 0x11))
