(module definition binary
  "\00\61\73\6d\01\00\00\00\01\9b\80\80\80\00\07\60"
  "\00\00\60\00\00\60\00\00\60\00\01\7f\60\00\01\7f"
  "\60\01\7f\01\7f\60\01\7f\00\02\96\80\80\80\00\01"
  "\08\73\70\65\63\74\65\73\74\09\70\72\69\6e\74\5f"
  "\69\33\32\00\06\03\87\80\80\80\00\06\00\01\04\05"
  "\05\06\07\9c\80\80\80\00\04\03\6f\6e\65\00\03\03"
  "\74\77\6f\00\04\05\74\68\72\65\65\00\05\04\66\6f"
  "\75\72\00\06\0a\bb\80\80\80\00\06\82\80\80\80\00"
  "\00\0b\82\80\80\80\00\00\0b\84\80\80\80\00\00\41"
  "\0d\0b\87\80\80\80\00\00\20\00\41\01\6a\0b\87\80"
  "\80\80\00\00\20\00\41\02\6b\0b\86\80\80\80\00\00"
  "\20\00\10\00\0b"
)
(module instance)
(assert_return (invoke "one") (i32.const 0xd))
(assert_return (invoke "two" (i32.const 0xd)) (i32.const 0xe))
(assert_return (invoke "three" (i32.const 0xd)) (i32.const 0xb))
(invoke "four" (i32.const 0x53))
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\09\86\80\80\80\00\01\00"
    "\41\00\0b\00"
  )
  "unknown table"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\09\87\80\80\80\00"
    "\01\00\41\00\0b\01\00\0a\88\80\80\80\00\01\82\80"
    "\80\80\00\00\0b"
  )
  "unknown table"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\04\84\80\80\80\00\01\70"
    "\00\01\09\86\80\80\80\00\01\00\42\00\0b\00"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\04\84\80\80\80\00\01\70"
    "\00\01\09\87\80\80\80\00\01\00\41\00\68\0b\00"
  )
  "constant expression required"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\04\84\80\80\80\00\01\70"
    "\00\01\09\85\80\80\80\00\01\00\01\0b\00"
  )
  "constant expression required"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\03\82\80\80\80\00\01\2a"
    "\0a\88\80\80\80\00\01\82\80\80\80\00\00\0b"
  )
  "unknown type"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\02\96\80\80\80\00\01\08"
    "\73\70\65\63\74\65\73\74\09\70\72\69\6e\74\5f\69"
    "\33\32\00\2b"
  )
  "unknown type"
)
(module definition binary
  "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
  "\00\01\7f\03\86\80\80\80\00\05\00\00\00\00\00\0a"
  "\ae\80\80\80\00\05\84\80\80\80\00\00\41\01\0b\84"
  "\80\80\80\00\00\41\02\0b\84\80\80\80\00\00\41\03"
  "\0b\84\80\80\80\00\00\41\04\0b\84\80\80\80\00\00"
  "\41\05\0b"
)
(module instance)
(assert_return (invoke "callt" (i32.const 0x0)) (i32.const 0x1))
(assert_return (invoke "callt" (i32.const 0x1)) (i32.const 0x2))
(assert_return (invoke "callt" (i32.const 0x2)) (i32.const 0x3))
(assert_return (invoke "callt" (i32.const 0x3)) (i32.const 0x4))
(assert_return (invoke "callt" (i32.const 0x4)) (i32.const 0x5))
(assert_return (invoke "callt" (i32.const 0x5)) (i32.const 0x1))
(assert_return (invoke "callt" (i32.const 0x6)) (i32.const 0x3))
(assert_trap (invoke "callt" (i32.const 0x7)) "undefined element")
(assert_trap (invoke "callt" (i32.const 0x64)) "undefined element")
(assert_trap (invoke "callt" (i32.const 0xffff_ffff)) "undefined element")
(assert_return (invoke "callu" (i32.const 0x0)) (i32.const 0x1))
(assert_return (invoke "callu" (i32.const 0x1)) (i32.const 0x2))
(assert_return (invoke "callu" (i32.const 0x2)) (i32.const 0x3))
(assert_return (invoke "callu" (i32.const 0x3)) (i32.const 0x4))
(assert_return (invoke "callu" (i32.const 0x4)) (i32.const 0x5))
(assert_return (invoke "callu" (i32.const 0x5)) (i32.const 0x1))
(assert_return (invoke "callu" (i32.const 0x6)) (i32.const 0x3))
(assert_trap (invoke "callu" (i32.const 0x7)) "undefined element")
(assert_trap (invoke "callu" (i32.const 0x64)) "undefined element")
(assert_trap (invoke "callu" (i32.const 0xffff_ffff)) "undefined element")
(module definition binary
  "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
  "\00\01\7f\03\83\80\80\80\00\02\00\00\0a\93\80\80"
  "\80\00\02\84\80\80\80\00\00\41\01\0b\84\80\80\80"
  "\00\00\41\02\0b"
)
(module instance)
(assert_return (invoke "callt" (i32.const 0x0)) (i32.const 0x1))
(assert_return (invoke "callt" (i32.const 0x1)) (i32.const 0x2))
