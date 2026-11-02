(module definition binary
  "\00\61\73\6d\01\00\00\00\01\8b\80\80\80\00\02\60"
  "\01\7f\01\7f\60\02\7f\7f\00\03\86\80\80\80\00\05"
  "\01\00\00\00\00\05\83\80\80\80\00\01\00\01\07\bb"
  "\80\80\80\00\05\05\73\74\6f\72\65\00\00\09\6c\6f"
  "\61\64\5f\6f\66\66\34\00\01\09\6c\6f\61\64\5f\6f"
  "\66\66\38\00\02\0a\6c\6f\61\64\5f\6f\66\66\31\32"
  "\00\03\0a\6c\6f\61\64\5f\6f\66\66\31\36\00\04\0a"
  "\bf\80\80\80\00\05\89\80\80\80\00\00\20\00\20\01"
  "\36\02\00\0b\87\80\80\80\00\00\20\00\28\02\04\0b"
  "\87\80\80\80\00\00\20\00\28\02\08\0b\87\80\80\80"
  "\00\00\20\00\28\02\0c\0b\87\80\80\80\00\00\20\00"
  "\28\02\10\0b"
)
(module instance)
(assert_return (invoke "store" (i32.const 0x68) (i32.const 0x102_0304)))
(assert_return (invoke "load_off4" (i32.const 0x64)) (i32.const 0x102_0304))
(assert_return (invoke "store" (i32.const 0xd0) (i32.const 0x506_0708)))
(assert_return (invoke "load_off8" (i32.const 0xc8)) (i32.const 0x506_0708))
(assert_return (invoke "store" (i32.const 0x138) (i32.const 0x90a_0b0c)))
(assert_return (invoke "load_off12" (i32.const 0x12c)) (i32.const 0x90a_0b0c))
(assert_return (invoke "store" (i32.const 0x1a0) (i32.const 0xd0e_0f10)))
(assert_return (invoke "load_off16" (i32.const 0x190)) (i32.const 0xd0e_0f10))
(assert_return (invoke "store" (i32.const 0xfffc) (i32.const 0x1111_1111)))
(assert_return (invoke "load_off16" (i32.const 0xffec)) (i32.const 0x1111_1111))
(assert_trap
  (invoke "load_off16" (i32.const 0xffed))
  "out of bounds memory access"
)
(assert_return (invoke "store" (i32.const 0x4) (i32.const 0x2222_2222)))
(assert_trap
  (invoke "load_off16" (i32.const 0xffff_fff4))
  "out of bounds memory access"
)
