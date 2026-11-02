(module definition binary
  "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
  "\00\01\7f\03\84\80\80\80\00\03\00\00\00\07\a0\80"
  "\80\80\00\03\05\6c\6f\6f\70\35\00\00\05\6c\6f\6f"
  "\70\36\00\01\0c\72\65\64\65\66\69\6e\69\74\69\6f"
  "\6e\00\02\0a\b7\80\80\80\00\03\8a\80\80\80\00\00"
  "\03\7f\41\01\0b\41\01\6a\0b\8b\80\80\80\00\00\03"
  "\7f\41\00\0d\00\41\03\0b\0b\92\80\80\80\00\00\02"
  "\7f\02\7f\41\02\0b\02\7f\41\03\0c\00\0b\6a\0b\0b"
)
(module instance)
(assert_return (invoke "block") (i32.const 0x1))
(assert_return (invoke "loop1") (i32.const 0x5))
(assert_return (invoke "loop2") (i32.const 0x8))
(assert_return (invoke "loop3") (i32.const 0x1))
(assert_return (invoke "loop4" (i32.const 0x8)) (i32.const 0x10))
(assert_return (invoke "loop5") (i32.const 0x2))
(assert_return (invoke "loop6") (i32.const 0x3))
(assert_return (invoke "if") (i32.const 0x5))
(assert_return (invoke "if2") (i32.const 0x5))
(assert_return (invoke "switch" (i32.const 0x0)) (i32.const 0x32))
(assert_return (invoke "switch" (i32.const 0x1)) (i32.const 0x14))
(assert_return (invoke "switch" (i32.const 0x2)) (i32.const 0x14))
(assert_return (invoke "switch" (i32.const 0x3)) (i32.const 0x3))
(assert_return (invoke "switch" (i32.const 0x4)) (i32.const 0x32))
(assert_return (invoke "switch" (i32.const 0x5)) (i32.const 0x32))
(assert_return (invoke "return" (i32.const 0x0)) (i32.const 0x0))
(assert_return (invoke "return" (i32.const 0x1)) (i32.const 0x2))
(assert_return (invoke "return" (i32.const 0x2)) (i32.const 0x2))
(assert_return (invoke "br_if0") (i32.const 0x1d))
(assert_return (invoke "br_if1") (i32.const 0x1))
(assert_return (invoke "br_if2") (i32.const 0x1))
(assert_return (invoke "br_if3") (i32.const 0x2))
(assert_return (invoke "br") (i32.const 0x1))
(assert_return (invoke "shadowing") (i32.const 0x1))
(assert_return (invoke "redefinition") (i32.const 0x5))
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\91\80\80\80\00"
    "\01\8b\80\80\80\00\00\02\40\41\01\0d\00\8c\01\0b"
    "\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\94\80\80\80\00"
    "\01\8e\80\80\80\00\00\02\40\43\00\00\00\00\41\01"
    "\0d\00\0b\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\94\80\80\80\00"
    "\01\8e\80\80\80\00\00\02\40\43\00\00\00\00\41\01"
    "\0d\00\0b\0b"
  )
  "type mismatch"
)
