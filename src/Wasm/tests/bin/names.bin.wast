(module definition binary
  "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
  "\00\01\7f\03\82\80\80\80\00\01\00\07\87\80\80\80"
  "\00\01\03\66\6f\6f\00\00\0a\8a\80\80\80\00\01\84"
  "\80\80\80\00\00\41\00\0b"
)
(module instance)
(assert_return (invoke "foo") (i32.const 0x0))
(module definition binary
  "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
  "\00\01\7f\03\82\80\80\80\00\01\00\07\87\80\80\80"
  "\00\01\03\66\6f\6f\00\00\0a\8a\80\80\80\00\01\84"
  "\80\80\80\00\00\41\01\0b"
)
(module instance)
(assert_return (invoke "foo") (i32.const 0x1))
(module definition binary
  "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
  "\00\01\7f\03\e1\83\80\80\00\df\03\00\00\00\00\00"
  "\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00"
  "\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00"
  "\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00"
  "\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00"
  "\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00"
  "\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00"
  "\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00"
  "\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00"
  "\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00"
  "\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00"
  "\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00"
  "\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00"
  "\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00"
  "\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00"
  "\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00"
  "\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00"
  "\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00"
  "\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00"
  "\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00"
  "\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00"
  "\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00"
  "\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00"
  "\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00"
  "\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00"
  "\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00"
  "\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00"
  "\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00"
  "\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00"
  "\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00"
  "\00\00\00\00\00\00\00\00\00\00\07\fe\81\80\80\00"
  "\23\00\00\00\01\30\00\01\02\2d\30\00\02\01\5f\00"
  "\03\01\24\00\04\01\40\00\05\21\7e\21\40\23\24\25"
  "\5e\26\2a\28\29\5f\2b\60\2d\3d\7b\7d\7c\5b\5d\5c"
  "\3a\22\3b\27\3c\3e\3f\2c\2e\2f\20\00\06\03\4e\61"
  "\4e\00\07\08\49\6e\66\69\6e\69\74\79\00\08\02\69"
  "\66\00\09\06\6d\61\6c\6c\6f\63\00\0a\07\5f\6d\61"
  "\6c\6c\6f\63\00\0b\08\5f\5f\6d\61\6c\6c\6f\63\00"
  "\0c\01\61\00\0d\01\41\00\0e\03\66\66\69\00\15\10"
  "\00\01\02\03\04\05\06\07\08\09\0a\0b\0c\0d\0e\0f"
  "\00\16\10\10\11\12\13\14\15\16\17\18\19\1a\1b\1c"
  "\1d\1e\1f\00\17\02\20\7f\00\18\01\0a\00\34\01\0d"
  "\00\37\02\0d\0a\00\38\02\0a\0d\00\39\01\1e\00\3a"
  "\01\0b\00\3b\01\0c\00\3c\03\61\62\63\00\8f\01\06"
  "\55\2b\30\30\34\31\00\a8\01\03\31\2f\32\00\95\03"
  "\01\7f\00\a0\03\01\08\00\a1\03\01\0f\00\a7\03\01"
  "\1a\00\ae\03\01\3f\00\b2\03\01\14\00\d6\03\0a\f8"
  "\a4\80\80\00\df\03\84\80\80\80\00\00\41\00\0b\84"
  "\80\80\80\00\00\41\01\0b\84\80\80\80\00\00\41\02"
  "\0b\84\80\80\80\00\00\41\03\0b\84\80\80\80\00\00"
  "\41\04\0b\84\80\80\80\00\00\41\05\0b\84\80\80\80"
  "\00\00\41\06\0b\84\80\80\80\00\00\41\07\0b\84\80"
  "\80\80\00\00\41\08\0b\84\80\80\80\00\00\41\09\0b"
  "\84\80\80\80\00\00\41\0a\0b\84\80\80\80\00\00\41"
  "\0b\0b\84\80\80\80\00\00\41\0c\0b\84\80\80\80\00"
  "\00\41\0d\0b\84\80\80\80\00\00\41\0e\0b\84\80\80"
  "\80\00\00\41\0f\0b\84\80\80\80\00\00\41\10\0b\84"
  "\80\80\80\00\00\41\11\0b\84\80\80\80\00\00\41\12"
  "\0b\84\80\80\80\00\00\41\13\0b\84\80\80\80\00\00"
  "\41\14\0b\84\80\80\80\00\00\41\15\0b\84\80\80\80"
  "\00\00\41\16\0b\84\80\80\80\00\00\41\17\0b\84\80"
  "\80\80\00\00\41\18\0b\84\80\80\80\00\00\41\19\0b"
  "\84\80\80\80\00\00\41\1a\0b\84\80\80\80\00\00\41"
  "\1b\0b\84\80\80\80\00\00\41\1c\0b\84\80\80\80\00"
  "\00\41\1d\0b\84\80\80\80\00\00\41\1e\0b\84\80\80"
  "\80\00\00\41\1f\0b\84\80\80\80\00\00\41\20\0b\84"
  "\80\80\80\00\00\41\21\0b\84\80\80\80\00\00\41\22"
  "\0b\84\80\80\80\00\00\41\23\0b\84\80\80\80\00\00"
  "\41\24\0b\84\80\80\80\00\00\41\25\0b\84\80\80\80"
  "\00\00\41\26\0b\84\80\80\80\00\00\41\27\0b\84\80"
  "\80\80\00\00\41\28\0b\84\80\80\80\00\00\41\29\0b"
  "\84\80\80\80\00\00\41\2a\0b\84\80\80\80\00\00\41"
  "\2b\0b\84\80\80\80\00\00\41\2c\0b\84\80\80\80\00"
  "\00\41\2d\0b\84\80\80\80\00\00\41\2e\0b\84\80\80"
  "\80\00\00\41\2f\0b\84\80\80\80\00\00\41\30\0b\84"
  "\80\80\80\00\00\41\31\0b\84\80\80\80\00\00\41\32"
  "\0b\84\80\80\80\00\00\41\33\0b\84\80\80\80\00\00"
  "\41\34\0b\84\80\80\80\00\00\41\35\0b\84\80\80\80"
  "\00\00\41\36\0b\84\80\80\80\00\00\41\37\0b\84\80"
  "\80\80\00\00\41\38\0b\84\80\80\80\00\00\41\39\0b"
  "\84\80\80\80\00\00\41\3a\0b\84\80\80\80\00\00\41"
  "\3b\0b\84\80\80\80\00\00\41\3c\0b\84\80\80\80\00"
  "\00\41\3d\0b\84\80\80\80\00\00\41\3e\0b\84\80\80"
  "\80\00\00\41\3f\0b\85\80\80\80\00\00\41\c0\00\0b"
  "\85\80\80\80\00\00\41\c1\00\0b\85\80\80\80\00\00"
  "\41\c2\00\0b\85\80\80\80\00\00\41\c3\00\0b\85\80"
  "\80\80\00\00\41\c4\00\0b\85\80\80\80\00\00\41\c5"
  "\00\0b\85\80\80\80\00\00\41\c6\00\0b\85\80\80\80"
  "\00\00\41\c7\00\0b\85\80\80\80\00\00\41\c8\00\0b"
  "\85\80\80\80\00\00\41\c9\00\0b\85\80\80\80\00\00"
  "\41\ca\00\0b\85\80\80\80\00\00\41\cb\00\0b\85\80"
  "\80\80\00\00\41\cc\00\0b\85\80\80\80\00\00\41\cd"
  "\00\0b\85\80\80\80\00\00\41\ce\00\0b\85\80\80\80"
  "\00\00\41\cf\00\0b\85\80\80\80\00\00\41\d0\00\0b"
  "\85\80\80\80\00\00\41\d1\00\0b\85\80\80\80\00\00"
  "\41\d2\00\0b\85\80\80\80\00\00\41\d3\00\0b\85\80"
  "\80\80\00\00\41\d4\00\0b\85\80\80\80\00\00\41\d5"
  "\00\0b\85\80\80\80\00\00\41\d6\00\0b\85\80\80\80"
  "\00\00\41\d7\00\0b\85\80\80\80\00\00\41\d8\00\0b"
  "\85\80\80\80\00\00\41\d9\00\0b\85\80\80\80\00\00"
  "\41\da\00\0b\85\80\80\80\00\00\41\db\00\0b\85\80"
  "\80\80\00\00\41\dc\00\0b\85\80\80\80\00\00\41\dd"
  "\00\0b\85\80\80\80\00\00\41\de\00\0b\85\80\80\80"
  "\00\00\41\df\00\0b\85\80\80\80\00\00\41\e0\00\0b"
  "\85\80\80\80\00\00\41\e1\00\0b\85\80\80\80\00\00"
  "\41\e2\00\0b\85\80\80\80\00\00\41\e3\00\0b\85\80"
  "\80\80\00\00\41\e4\00\0b\85\80\80\80\00\00\41\e5"
  "\00\0b\85\80\80\80\00\00\41\e6\00\0b\85\80\80\80"
  "\00\00\41\e7\00\0b\85\80\80\80\00\00\41\e8\00\0b"
  "\85\80\80\80\00\00\41\e9\00\0b\85\80\80\80\00\00"
  "\41\ea\00\0b\85\80\80\80\00\00\41\eb\00\0b\85\80"
  "\80\80\00\00\41\ec\00\0b\85\80\80\80\00\00\41\ed"
  "\00\0b\85\80\80\80\00\00\41\ee\00\0b\85\80\80\80"
  "\00\00\41\ef\00\0b\85\80\80\80\00\00\41\f0\00\0b"
  "\85\80\80\80\00\00\41\f1\00\0b\85\80\80\80\00\00"
  "\41\f2\00\0b\85\80\80\80\00\00\41\f3\00\0b\85\80"
  "\80\80\00\00\41\f4\00\0b\85\80\80\80\00\00\41\f5"
  "\00\0b\85\80\80\80\00\00\41\f6\00\0b\85\80\80\80"
  "\00\00\41\f7\00\0b\85\80\80\80\00\00\41\f8\00\0b"
  "\85\80\80\80\00\00\41\f9\00\0b\85\80\80\80\00\00"
  "\41\fa\00\0b\85\80\80\80\00\00\41\fb\00\0b\85\80"
  "\80\80\00\00\41\fc\00\0b\85\80\80\80\00\00\41\fd"
  "\00\0b\85\80\80\80\00\00\41\fe\00\0b\85\80\80\80"
  "\00\00\41\ff\00\0b\85\80\80\80\00\00\41\80\01\0b"
  "\85\80\80\80\00\00\41\81\01\0b\85\80\80\80\00\00"
  "\41\82\01\0b\85\80\80\80\00\00\41\83\01\0b\85\80"
  "\80\80\00\00\41\84\01\0b\85\80\80\80\00\00\41\85"
  "\01\0b\85\80\80\80\00\00\41\86\01\0b\85\80\80\80"
  "\00\00\41\87\01\0b\85\80\80\80\00\00\41\88\01\0b"
  "\85\80\80\80\00\00\41\89\01\0b\85\80\80\80\00\00"
  "\41\8a\01\0b\85\80\80\80\00\00\41\8b\01\0b\85\80"
  "\80\80\00\00\41\8c\01\0b\85\80\80\80\00\00\41\8d"
  "\01\0b\85\80\80\80\00\00\41\8e\01\0b\85\80\80\80"
  "\00\00\41\8f\01\0b\85\80\80\80\00\00\41\90\01\0b"
  "\85\80\80\80\00\00\41\91\01\0b\85\80\80\80\00\00"
  "\41\92\01\0b\85\80\80\80\00\00\41\93\01\0b\85\80"
  "\80\80\00\00\41\94\01\0b\85\80\80\80\00\00\41\95"
  "\01\0b\85\80\80\80\00\00\41\96\01\0b\85\80\80\80"
  "\00\00\41\97\01\0b\85\80\80\80\00\00\41\98\01\0b"
  "\85\80\80\80\00\00\41\99\01\0b\85\80\80\80\00\00"
  "\41\9a\01\0b\85\80\80\80\00\00\41\9b\01\0b\85\80"
  "\80\80\00\00\41\9c\01\0b\85\80\80\80\00\00\41\9d"
  "\01\0b\85\80\80\80\00\00\41\9e\01\0b\85\80\80\80"
  "\00\00\41\9f\01\0b\85\80\80\80\00\00\41\a0\01\0b"
  "\85\80\80\80\00\00\41\a1\01\0b\85\80\80\80\00\00"
  "\41\a2\01\0b\85\80\80\80\00\00\41\a3\01\0b\85\80"
  "\80\80\00\00\41\a4\01\0b\85\80\80\80\00\00\41\a5"
  "\01\0b\85\80\80\80\00\00\41\a6\01\0b\85\80\80\80"
  "\00\00\41\a7\01\0b\85\80\80\80\00\00\41\a8\01\0b"
  "\85\80\80\80\00\00\41\a9\01\0b\85\80\80\80\00\00"
  "\41\aa\01\0b\85\80\80\80\00\00\41\ab\01\0b\85\80"
  "\80\80\00\00\41\ac\01\0b\85\80\80\80\00\00\41\ad"
  "\01\0b\85\80\80\80\00\00\41\ae\01\0b\85\80\80\80"
  "\00\00\41\af\01\0b\85\80\80\80\00\00\41\b0\01\0b"
  "\85\80\80\80\00\00\41\b1\01\0b\85\80\80\80\00\00"
  "\41\b2\01\0b\85\80\80\80\00\00\41\b3\01\0b\85\80"
  "\80\80\00\00\41\b4\01\0b\85\80\80\80\00\00\41\b5"
  "\01\0b\85\80\80\80\00\00\41\b6\01\0b\85\80\80\80"
  "\00\00\41\b7\01\0b\85\80\80\80\00\00\41\b8\01\0b"
  "\85\80\80\80\00\00\41\b9\01\0b\85\80\80\80\00\00"
  "\41\ba\01\0b\85\80\80\80\00\00\41\bb\01\0b\85\80"
  "\80\80\00\00\41\bc\01\0b\85\80\80\80\00\00\41\bd"
  "\01\0b\85\80\80\80\00\00\41\be\01\0b\85\80\80\80"
  "\00\00\41\bf\01\0b\85\80\80\80\00\00\41\c0\01\0b"
  "\85\80\80\80\00\00\41\c1\01\0b\85\80\80\80\00\00"
  "\41\c2\01\0b\85\80\80\80\00\00\41\c3\01\0b\85\80"
  "\80\80\00\00\41\c4\01\0b\85\80\80\80\00\00\41\c5"
  "\01\0b\85\80\80\80\00\00\41\c6\01\0b\85\80\80\80"
  "\00\00\41\c7\01\0b\85\80\80\80\00\00\41\c8\01\0b"
  "\85\80\80\80\00\00\41\c9\01\0b\85\80\80\80\00\00"
  "\41\ca\01\0b\85\80\80\80\00\00\41\cb\01\0b\85\80"
  "\80\80\00\00\41\cc\01\0b\85\80\80\80\00\00\41\cd"
  "\01\0b\85\80\80\80\00\00\41\ce\01\0b\85\80\80\80"
  "\00\00\41\cf\01\0b\85\80\80\80\00\00\41\d0\01\0b"
  "\85\80\80\80\00\00\41\d1\01\0b\85\80\80\80\00\00"
  "\41\d2\01\0b\85\80\80\80\00\00\41\d3\01\0b\85\80"
  "\80\80\00\00\41\d4\01\0b\85\80\80\80\00\00\41\d5"
  "\01\0b\85\80\80\80\00\00\41\d6\01\0b\85\80\80\80"
  "\00\00\41\d7\01\0b\85\80\80\80\00\00\41\d8\01\0b"
  "\85\80\80\80\00\00\41\d9\01\0b\85\80\80\80\00\00"
  "\41\da\01\0b\85\80\80\80\00\00\41\db\01\0b\85\80"
  "\80\80\00\00\41\dc\01\0b\85\80\80\80\00\00\41\dd"
  "\01\0b\85\80\80\80\00\00\41\de\01\0b\85\80\80\80"
  "\00\00\41\df\01\0b\85\80\80\80\00\00\41\e0\01\0b"
  "\85\80\80\80\00\00\41\e1\01\0b\85\80\80\80\00\00"
  "\41\e2\01\0b\85\80\80\80\00\00\41\e3\01\0b\85\80"
  "\80\80\00\00\41\e4\01\0b\85\80\80\80\00\00\41\e5"
  "\01\0b\85\80\80\80\00\00\41\e6\01\0b\85\80\80\80"
  "\00\00\41\e7\01\0b\85\80\80\80\00\00\41\e8\01\0b"
  "\85\80\80\80\00\00\41\e9\01\0b\85\80\80\80\00\00"
  "\41\ea\01\0b\85\80\80\80\00\00\41\eb\01\0b\85\80"
  "\80\80\00\00\41\ec\01\0b\85\80\80\80\00\00\41\ed"
  "\01\0b\85\80\80\80\00\00\41\ee\01\0b\85\80\80\80"
  "\00\00\41\ef\01\0b\85\80\80\80\00\00\41\f0\01\0b"
  "\85\80\80\80\00\00\41\f1\01\0b\85\80\80\80\00\00"
  "\41\f2\01\0b\85\80\80\80\00\00\41\f3\01\0b\85\80"
  "\80\80\00\00\41\f4\01\0b\85\80\80\80\00\00\41\f5"
  "\01\0b\85\80\80\80\00\00\41\f6\01\0b\85\80\80\80"
  "\00\00\41\f7\01\0b\85\80\80\80\00\00\41\f8\01\0b"
  "\85\80\80\80\00\00\41\f9\01\0b\85\80\80\80\00\00"
  "\41\fa\01\0b\85\80\80\80\00\00\41\fb\01\0b\85\80"
  "\80\80\00\00\41\fc\01\0b\85\80\80\80\00\00\41\fd"
  "\01\0b\85\80\80\80\00\00\41\fe\01\0b\85\80\80\80"
  "\00\00\41\ff\01\0b\85\80\80\80\00\00\41\80\02\0b"
  "\85\80\80\80\00\00\41\81\02\0b\85\80\80\80\00\00"
  "\41\82\02\0b\85\80\80\80\00\00\41\83\02\0b\85\80"
  "\80\80\00\00\41\84\02\0b\85\80\80\80\00\00\41\85"
  "\02\0b\85\80\80\80\00\00\41\86\02\0b\85\80\80\80"
  "\00\00\41\87\02\0b\85\80\80\80\00\00\41\88\02\0b"
  "\85\80\80\80\00\00\41\89\02\0b\85\80\80\80\00\00"
  "\41\8a\02\0b\85\80\80\80\00\00\41\8b\02\0b\85\80"
  "\80\80\00\00\41\8c\02\0b\85\80\80\80\00\00\41\8d"
  "\02\0b\85\80\80\80\00\00\41\8e\02\0b\85\80\80\80"
  "\00\00\41\8f\02\0b\85\80\80\80\00\00\41\90\02\0b"
  "\85\80\80\80\00\00\41\91\02\0b\85\80\80\80\00\00"
  "\41\92\02\0b\85\80\80\80\00\00\41\93\02\0b\85\80"
  "\80\80\00\00\41\94\02\0b\85\80\80\80\00\00\41\95"
  "\02\0b\85\80\80\80\00\00\41\96\02\0b\85\80\80\80"
  "\00\00\41\97\02\0b\85\80\80\80\00\00\41\98\02\0b"
  "\85\80\80\80\00\00\41\99\02\0b\85\80\80\80\00\00"
  "\41\9a\02\0b\85\80\80\80\00\00\41\9b\02\0b\85\80"
  "\80\80\00\00\41\9c\02\0b\85\80\80\80\00\00\41\9d"
  "\02\0b\85\80\80\80\00\00\41\9e\02\0b\85\80\80\80"
  "\00\00\41\9f\02\0b\85\80\80\80\00\00\41\a0\02\0b"
  "\85\80\80\80\00\00\41\a1\02\0b\85\80\80\80\00\00"
  "\41\a2\02\0b\85\80\80\80\00\00\41\a3\02\0b\85\80"
  "\80\80\00\00\41\a4\02\0b\85\80\80\80\00\00\41\a5"
  "\02\0b\85\80\80\80\00\00\41\a6\02\0b\85\80\80\80"
  "\00\00\41\a7\02\0b\85\80\80\80\00\00\41\a8\02\0b"
  "\85\80\80\80\00\00\41\a9\02\0b\85\80\80\80\00\00"
  "\41\aa\02\0b\85\80\80\80\00\00\41\ab\02\0b\85\80"
  "\80\80\00\00\41\ac\02\0b\85\80\80\80\00\00\41\ad"
  "\02\0b\85\80\80\80\00\00\41\ae\02\0b\85\80\80\80"
  "\00\00\41\af\02\0b\85\80\80\80\00\00\41\b0\02\0b"
  "\85\80\80\80\00\00\41\b1\02\0b\85\80\80\80\00\00"
  "\41\b2\02\0b\85\80\80\80\00\00\41\b3\02\0b\85\80"
  "\80\80\00\00\41\b4\02\0b\85\80\80\80\00\00\41\b5"
  "\02\0b\85\80\80\80\00\00\41\b6\02\0b\85\80\80\80"
  "\00\00\41\b7\02\0b\85\80\80\80\00\00\41\b8\02\0b"
  "\85\80\80\80\00\00\41\b9\02\0b\85\80\80\80\00\00"
  "\41\ba\02\0b\85\80\80\80\00\00\41\bb\02\0b\85\80"
  "\80\80\00\00\41\bc\02\0b\85\80\80\80\00\00\41\bd"
  "\02\0b\85\80\80\80\00\00\41\be\02\0b\85\80\80\80"
  "\00\00\41\bf\02\0b\85\80\80\80\00\00\41\c0\02\0b"
  "\85\80\80\80\00\00\41\c1\02\0b\85\80\80\80\00\00"
  "\41\c2\02\0b\85\80\80\80\00\00\41\c3\02\0b\85\80"
  "\80\80\00\00\41\c4\02\0b\85\80\80\80\00\00\41\c5"
  "\02\0b\85\80\80\80\00\00\41\c6\02\0b\85\80\80\80"
  "\00\00\41\c7\02\0b\85\80\80\80\00\00\41\c8\02\0b"
  "\85\80\80\80\00\00\41\c9\02\0b\85\80\80\80\00\00"
  "\41\ca\02\0b\85\80\80\80\00\00\41\cb\02\0b\85\80"
  "\80\80\00\00\41\cc\02\0b\85\80\80\80\00\00\41\cd"
  "\02\0b\85\80\80\80\00\00\41\ce\02\0b\85\80\80\80"
  "\00\00\41\cf\02\0b\85\80\80\80\00\00\41\d0\02\0b"
  "\85\80\80\80\00\00\41\d1\02\0b\85\80\80\80\00\00"
  "\41\d2\02\0b\85\80\80\80\00\00\41\d3\02\0b\85\80"
  "\80\80\00\00\41\d4\02\0b\85\80\80\80\00\00\41\d5"
  "\02\0b\85\80\80\80\00\00\41\d6\02\0b\85\80\80\80"
  "\00\00\41\d7\02\0b\85\80\80\80\00\00\41\d8\02\0b"
  "\85\80\80\80\00\00\41\d9\02\0b\85\80\80\80\00\00"
  "\41\da\02\0b\85\80\80\80\00\00\41\db\02\0b\85\80"
  "\80\80\00\00\41\dc\02\0b\85\80\80\80\00\00\41\dd"
  "\02\0b\85\80\80\80\00\00\41\de\02\0b\85\80\80\80"
  "\00\00\41\df\02\0b\85\80\80\80\00\00\41\e0\02\0b"
  "\85\80\80\80\00\00\41\e1\02\0b\85\80\80\80\00\00"
  "\41\e2\02\0b\85\80\80\80\00\00\41\e3\02\0b\85\80"
  "\80\80\00\00\41\e4\02\0b\85\80\80\80\00\00\41\e5"
  "\02\0b\85\80\80\80\00\00\41\e6\02\0b\85\80\80\80"
  "\00\00\41\e7\02\0b\85\80\80\80\00\00\41\e8\02\0b"
  "\85\80\80\80\00\00\41\e9\02\0b\85\80\80\80\00\00"
  "\41\ea\02\0b\85\80\80\80\00\00\41\eb\02\0b\85\80"
  "\80\80\00\00\41\ec\02\0b\85\80\80\80\00\00\41\ed"
  "\02\0b\85\80\80\80\00\00\41\ee\02\0b\85\80\80\80"
  "\00\00\41\ef\02\0b\85\80\80\80\00\00\41\f0\02\0b"
  "\85\80\80\80\00\00\41\f1\02\0b\85\80\80\80\00\00"
  "\41\f2\02\0b\85\80\80\80\00\00\41\f3\02\0b\85\80"
  "\80\80\00\00\41\f4\02\0b\85\80\80\80\00\00\41\f5"
  "\02\0b\85\80\80\80\00\00\41\f6\02\0b\85\80\80\80"
  "\00\00\41\f7\02\0b\85\80\80\80\00\00\41\f8\02\0b"
  "\85\80\80\80\00\00\41\f9\02\0b\85\80\80\80\00\00"
  "\41\fa\02\0b\85\80\80\80\00\00\41\fb\02\0b\85\80"
  "\80\80\00\00\41\fc\02\0b\85\80\80\80\00\00\41\fd"
  "\02\0b\85\80\80\80\00\00\41\fe\02\0b\85\80\80\80"
  "\00\00\41\ff\02\0b\85\80\80\80\00\00\41\80\03\0b"
  "\85\80\80\80\00\00\41\81\03\0b\85\80\80\80\00\00"
  "\41\82\03\0b\85\80\80\80\00\00\41\83\03\0b\85\80"
  "\80\80\00\00\41\84\03\0b\85\80\80\80\00\00\41\85"
  "\03\0b\85\80\80\80\00\00\41\86\03\0b\85\80\80\80"
  "\00\00\41\87\03\0b\85\80\80\80\00\00\41\88\03\0b"
  "\85\80\80\80\00\00\41\89\03\0b\85\80\80\80\00\00"
  "\41\8a\03\0b\85\80\80\80\00\00\41\8b\03\0b\85\80"
  "\80\80\00\00\41\8c\03\0b\85\80\80\80\00\00\41\8d"
  "\03\0b\85\80\80\80\00\00\41\8e\03\0b\85\80\80\80"
  "\00\00\41\8f\03\0b\85\80\80\80\00\00\41\90\03\0b"
  "\85\80\80\80\00\00\41\91\03\0b\85\80\80\80\00\00"
  "\41\92\03\0b\85\80\80\80\00\00\41\93\03\0b\85\80"
  "\80\80\00\00\41\94\03\0b\85\80\80\80\00\00\41\95"
  "\03\0b\85\80\80\80\00\00\41\96\03\0b\85\80\80\80"
  "\00\00\41\97\03\0b\85\80\80\80\00\00\41\98\03\0b"
  "\85\80\80\80\00\00\41\99\03\0b\85\80\80\80\00\00"
  "\41\9a\03\0b\85\80\80\80\00\00\41\9b\03\0b\85\80"
  "\80\80\00\00\41\9c\03\0b\85\80\80\80\00\00\41\9d"
  "\03\0b\85\80\80\80\00\00\41\9e\03\0b\85\80\80\80"
  "\00\00\41\9f\03\0b\85\80\80\80\00\00\41\a0\03\0b"
  "\85\80\80\80\00\00\41\a1\03\0b\85\80\80\80\00\00"
  "\41\a2\03\0b\85\80\80\80\00\00\41\a3\03\0b\85\80"
  "\80\80\00\00\41\a4\03\0b\85\80\80\80\00\00\41\a5"
  "\03\0b\85\80\80\80\00\00\41\a6\03\0b\85\80\80\80"
  "\00\00\41\a7\03\0b\85\80\80\80\00\00\41\a8\03\0b"
  "\85\80\80\80\00\00\41\a9\03\0b\85\80\80\80\00\00"
  "\41\aa\03\0b\85\80\80\80\00\00\41\ab\03\0b\85\80"
  "\80\80\00\00\41\ac\03\0b\85\80\80\80\00\00\41\ad"
  "\03\0b\85\80\80\80\00\00\41\ae\03\0b\85\80\80\80"
  "\00\00\41\af\03\0b\85\80\80\80\00\00\41\b0\03\0b"
  "\85\80\80\80\00\00\41\b1\03\0b\85\80\80\80\00\00"
  "\41\b2\03\0b\85\80\80\80\00\00\41\b3\03\0b\85\80"
  "\80\80\00\00\41\b4\03\0b\85\80\80\80\00\00\41\b5"
  "\03\0b\85\80\80\80\00\00\41\b6\03\0b\85\80\80\80"
  "\00\00\41\b7\03\0b\85\80\80\80\00\00\41\b8\03\0b"
  "\85\80\80\80\00\00\41\b9\03\0b\85\80\80\80\00\00"
  "\41\ba\03\0b\85\80\80\80\00\00\41\bb\03\0b\85\80"
  "\80\80\00\00\41\bc\03\0b\85\80\80\80\00\00\41\bd"
  "\03\0b\85\80\80\80\00\00\41\be\03\0b\85\80\80\80"
  "\00\00\41\bf\03\0b\85\80\80\80\00\00\41\c0\03\0b"
  "\85\80\80\80\00\00\41\c1\03\0b\85\80\80\80\00\00"
  "\41\c2\03\0b\85\80\80\80\00\00\41\c3\03\0b\85\80"
  "\80\80\00\00\41\c4\03\0b\85\80\80\80\00\00\41\c5"
  "\03\0b\85\80\80\80\00\00\41\c6\03\0b\85\80\80\80"
  "\00\00\41\c7\03\0b\85\80\80\80\00\00\41\c8\03\0b"
  "\85\80\80\80\00\00\41\c9\03\0b\85\80\80\80\00\00"
  "\41\ca\03\0b\85\80\80\80\00\00\41\cb\03\0b\85\80"
  "\80\80\00\00\41\cc\03\0b\85\80\80\80\00\00\41\cd"
  "\03\0b\85\80\80\80\00\00\41\ce\03\0b\85\80\80\80"
  "\00\00\41\cf\03\0b\85\80\80\80\00\00\41\d0\03\0b"
  "\85\80\80\80\00\00\41\d1\03\0b\85\80\80\80\00\00"
  "\41\d2\03\0b\85\80\80\80\00\00\41\d3\03\0b\85\80"
  "\80\80\00\00\41\d4\03\0b\85\80\80\80\00\00\41\d5"
  "\03\0b\85\80\80\80\00\00\41\d6\03\0b\85\80\80\80"
  "\00\00\41\d7\03\0b\85\80\80\80\00\00\41\d8\03\0b"
  "\85\80\80\80\00\00\41\d9\03\0b\85\80\80\80\00\00"
  "\41\da\03\0b\85\80\80\80\00\00\41\db\03\0b\85\80"
  "\80\80\00\00\41\dc\03\0b\85\80\80\80\00\00\41\dd"
  "\03\0b\85\80\80\80\00\00\41\de\03\0b"
)
(module instance)
(assert_return (invoke "") (i32.const 0x0))
(assert_return (invoke "0") (i32.const 0x1))
(assert_return (invoke "-0") (i32.const 0x2))
(assert_return (invoke "_") (i32.const 0x3))
(assert_return (invoke "$") (i32.const 0x4))
(assert_return (invoke "@") (i32.const 0x5))
(assert_return (invoke "~!@#$%^&*()_+`-={}|[]\\:\";'<>?,./ ") (i32.const 0x6))
(assert_return (invoke "NaN") (i32.const 0x7))
(assert_return (invoke "Infinity") (i32.const 0x8))
(assert_return (invoke "if") (i32.const 0x9))
(assert_return (invoke "malloc") (i32.const 0xa))
(assert_return (invoke "_malloc") (i32.const 0xb))
(assert_return (invoke "__malloc") (i32.const 0xc))
(assert_return (invoke "a") (i32.const 0xd))
(assert_return (invoke "A") (i32.const 0xe))
(assert_return (invoke "\u{feff}") (i32.const 0xf))
(assert_return (invoke "\u{c5}") (i32.const 0x10))
(assert_return (invoke "A\u{30a}") (i32.const 0x11))
(assert_return (invoke "\u{212b}") (i32.const 0x12))
(assert_return (invoke "\u{fb03}") (i32.const 0x13))
(assert_return (invoke "f\u{fb01}") (i32.const 0x14))
(assert_return (invoke "ffi") (i32.const 0x15))
(assert_return
  (invoke "\u{00}\u{01}\u{02}\u{03}\u{04}\u{05}\u{06}\u{07}\u{08}\t\n\u{0b}\u{0c}\r\u{0e}\u{0f}"
  )
  (i32.const 0x16)
)
(assert_return
  (invoke "\u{10}\u{11}\u{12}\u{13}\u{14}\u{15}\u{16}\u{17}\u{18}\u{19}\u{1a}\u{1b}\u{1c}\u{1d}\u{1e}\u{1f}"
  )
  (i32.const 0x17)
)
(assert_return (invoke " \u{7f}") (i32.const 0x18))
(assert_return
  (invoke "\u{80}\u{81}\u{82}\u{83}\u{84}\u{85}\u{86}\u{87}\u{88}\u{89}\u{8a}\u{8b}\u{8c}\u{8d}\u{8e}\u{8f}"
  )
  (i32.const 0x19)
)
(assert_return
  (invoke "\u{90}\u{91}\u{92}\u{93}\u{94}\u{95}\u{96}\u{97}\u{98}\u{99}\u{9a}\u{9b}\u{9c}\u{9d}\u{9e}\u{9f}"
  )
  (i32.const 0x1a)
)
(assert_return
  (invoke "\u{fff0}\u{fff1}\u{fff2}\u{fff3}\u{fff4}\u{fff5}\u{fff6}\u{fff7}")
  (i32.const 0x1b)
)
(assert_return
  (invoke "\u{fff8}\u{fff9}\u{fffa}\u{fffb}\u{fffc}\u{fffd}\u{fffe}\u{ffff}")
  (i32.const 0x1c)
)
(assert_return
  (invoke "\u{2400}\u{2401}\u{2402}\u{2403}\u{2404}\u{2405}\u{2406}\u{2407}\u{2408}\u{2409}\u{240a}\u{240b}\u{240c}\u{240d}\u{240e}\u{240f}"
  )
  (i32.const 0x1d)
)
(assert_return
  (invoke "\u{2410}\u{2411}\u{2412}\u{2413}\u{2414}\u{2415}\u{2416}\u{2417}\u{2418}\u{2419}\u{241a}\u{241b}\u{241c}\u{241d}\u{241e}\u{241f}"
  )
  (i32.const 0x1e)
)
(assert_return (invoke "\u{2420}\u{2421}") (i32.const 0x1f))
(assert_return
  (invoke "\u{fff0}\u{fff1}\u{fff2}\u{fff3}\u{fff4}\u{fff5}\u{fff6}\u{fff7}\u{fff8}\u{fff9}\u{fffa}\u{fffb}\u{fffc}\u{fffd}"
  )
  (i32.const 0x20)
)
(assert_return (invoke "\u{200d}") (i32.const 0x21))
(assert_return (invoke "\u{200c}") (i32.const 0x22))
(assert_return (invoke "\u{34f}") (i32.const 0x23))
(assert_return (invoke "\u{2060}") (i32.const 0x24))
(assert_return (invoke "\u{2d7f}") (i32.const 0x25))
(assert_return (invoke "\u{1107f}") (i32.const 0x26))
(assert_return (invoke "\u{180e}") (i32.const 0x27))
(assert_return
  (invoke "\u{ffef}\u{200b}\u{a0}\u{ad}\u{2060}\u{1680}\u{202e}\u{202d}")
  (i32.const 0x28)
)
(assert_return
  (invoke "\u{200e}\u{200f}\u{2011}\u{2028}\u{2029}\u{202a}\u{202b}\u{202c}\u{202f}\u{2066}\u{2067}\u{2068}\u{2069}"
  )
  (i32.const 0x29)
)
(assert_return
  (invoke "\u{206a}\u{206b}\u{206c}\u{206d}\u{206e}\u{206f}")
  (i32.const 0x2a)
)
(assert_return (invoke "\u{2061}\u{2062}\u{2063}\u{2064}") (i32.const 0x2b))
(assert_return (invoke "\u{10000}\u{dffff}\u{10ffff}") (i32.const 0x2c))
(assert_return
  (invoke "Z\u{30f}\u{346}\u{306}\u{35b}\u{34c}\u{334}\u{358}\u{35e}\u{347}\u{32b}\u{325}\u{32a}\u{353}\u{348}\u{354}\u{34e}\u{317}\u{31e}\u{33a}\u{32f}\u{331}\u{31e}\u{319}\u{331}\u{31c}\u{316}\u{320}a\u{357}\u{368}\u{30e}\u{304}\u{306}\u{357}\u{33f}\u{361}\u{35f}\u{340}\u{336}\u{341}\u{325}\u{330}\u{333}\u{32d}\u{359}\u{332}\u{331}\u{339}\u{31d}\u{34e}\u{33c}l\u{344}\u{34a}\u{31a}\u{357}\u{366}\u{344}\u{36b}\u{307}\u{341}\u{336}\u{337}\u{349}\u{329}\u{339}\u{32b}\u{31d}\u{356}\u{345}\u{319}\u{332}\u{33c}\u{347}\u{35a}\u{34d}\u{32e}\u{34e}\u{325}\u{345}\u{31e}g\u{343}\u{310}\u{305}\u{36e}\u{314}\u{310}\u{30e}\u{302}\u{30f}\u{33e}\u{34a}\u{30d}\u{34b}\u{34a}\u{367}\u{301}\u{306}\u{366}\u{35e}\u{336}\u{355}\u{354}\u{35a}\u{329}o\u{34b}\u{314}\u{350}\u{36a}\u{369}\u{321}\u{34f}\u{322}\u{327}\u{341}\u{32b}\u{319}\u{324}\u{32e}\u{356}\u{359}\u{353}\u{33a}\u{31c}\u{329}\u{33c}\u{318}\u{320}"
  )
  (i32.const 0x2d)
)
(assert_return (invoke "\u{115f}\u{1160}\u{3164}\u{ffa0}") (i32.const 0x2e))
(assert_return (invoke "\u{fe00}") (i32.const 0x2f))
(assert_return (invoke "\u{fe04}") (i32.const 0x30))
(assert_return (invoke "\u{e0100}") (i32.const 0x31))
(assert_return (invoke "\u{e01ef}") (i32.const 0x32))
(assert_return (invoke "\u{308}") (i32.const 0x33))
(assert_return (invoke "\n") (i32.const 0x34))
(assert_return (invoke "\u{2424}") (i32.const 0x35))
(assert_return (invoke "\u{2028}") (i32.const 0x36))
(assert_return (invoke "\r") (i32.const 0x37))
(assert_return (invoke "\r\n") (i32.const 0x38))
(assert_return (invoke "\n\r") (i32.const 0x39))
(assert_return (invoke "\u{1e}") (i32.const 0x3a))
(assert_return (invoke "\u{0b}") (i32.const 0x3b))
(assert_return (invoke "\u{0c}") (i32.const 0x3c))
(assert_return (invoke "\u{85}") (i32.const 0x3d))
(assert_return (invoke "\u{2029}") (i32.const 0x3e))
(assert_return (invoke "\u{2026}") (i32.const 0x3f))
(assert_return (invoke "\u{23ce}") (i32.const 0x40))
(assert_return (invoke "\u{8b}") (i32.const 0x41))
(assert_return (invoke "\u{8c}") (i32.const 0x42))
(assert_return (invoke "\u{8d}") (i32.const 0x43))
(assert_return (invoke "\u{21b5}") (i32.const 0x44))
(assert_return (invoke "\u{21a9}") (i32.const 0x45))
(assert_return (invoke "\u{2324}") (i32.const 0x46))
(assert_return (invoke "\u{2936}") (i32.const 0x47))
(assert_return (invoke "\u{21b2}") (i32.const 0x48))
(assert_return (invoke "\u{2ba8}") (i32.const 0x49))
(assert_return (invoke "\u{2bb0}") (i32.const 0x4a))
(assert_return (invoke "\u{fffd}") (i32.const 0x4b))
(assert_return (invoke "\u{fdd0}") (i32.const 0x4c))
(assert_return (invoke "\u{fdd1}") (i32.const 0x4d))
(assert_return (invoke "\u{fdd2}") (i32.const 0x4e))
(assert_return (invoke "\u{fdd3}") (i32.const 0x4f))
(assert_return (invoke "\u{fdd4}") (i32.const 0x50))
(assert_return (invoke "\u{fdd5}") (i32.const 0x51))
(assert_return (invoke "\u{fdd6}") (i32.const 0x52))
(assert_return (invoke "\u{fdd7}") (i32.const 0x53))
(assert_return (invoke "\u{fdd8}") (i32.const 0x54))
(assert_return (invoke "\u{fdd9}") (i32.const 0x55))
(assert_return (invoke "\u{fdda}") (i32.const 0x56))
(assert_return (invoke "\u{fddb}") (i32.const 0x57))
(assert_return (invoke "\u{fddc}") (i32.const 0x58))
(assert_return (invoke "\u{fddd}") (i32.const 0x59))
(assert_return (invoke "\u{fdde}") (i32.const 0x5a))
(assert_return (invoke "\u{fddf}") (i32.const 0x5b))
(assert_return (invoke "\u{fde0}") (i32.const 0x5c))
(assert_return (invoke "\u{fde1}") (i32.const 0x5d))
(assert_return (invoke "\u{fde2}") (i32.const 0x5e))
(assert_return (invoke "\u{fde3}") (i32.const 0x5f))
(assert_return (invoke "\u{fde4}") (i32.const 0x60))
(assert_return (invoke "\u{fde5}") (i32.const 0x61))
(assert_return (invoke "\u{fde6}") (i32.const 0x62))
(assert_return (invoke "\u{fde7}") (i32.const 0x63))
(assert_return (invoke "\u{fde8}") (i32.const 0x64))
(assert_return (invoke "\u{fde9}") (i32.const 0x65))
(assert_return (invoke "\u{fdea}") (i32.const 0x66))
(assert_return (invoke "\u{fdeb}") (i32.const 0x67))
(assert_return (invoke "\u{fdec}") (i32.const 0x68))
(assert_return (invoke "\u{fded}") (i32.const 0x69))
(assert_return (invoke "\u{fdee}") (i32.const 0x6a))
(assert_return (invoke "\u{fdef}") (i32.const 0x6b))
(assert_return (invoke "\u{fffe}") (i32.const 0x6c))
(assert_return (invoke "\u{ffff}") (i32.const 0x6d))
(assert_return (invoke "\u{1fffe}") (i32.const 0x6e))
(assert_return (invoke "\u{1ffff}") (i32.const 0x6f))
(assert_return (invoke "\u{2fffe}") (i32.const 0x70))
(assert_return (invoke "\u{2ffff}") (i32.const 0x71))
(assert_return (invoke "\u{3fffe}") (i32.const 0x72))
(assert_return (invoke "\u{3ffff}") (i32.const 0x73))
(assert_return (invoke "\u{4fffe}") (i32.const 0x74))
(assert_return (invoke "\u{4ffff}") (i32.const 0x75))
(assert_return (invoke "\u{5fffe}") (i32.const 0x76))
(assert_return (invoke "\u{5ffff}") (i32.const 0x77))
(assert_return (invoke "\u{6fffe}") (i32.const 0x78))
(assert_return (invoke "\u{6ffff}") (i32.const 0x79))
(assert_return (invoke "\u{7fffe}") (i32.const 0x7a))
(assert_return (invoke "\u{7ffff}") (i32.const 0x7b))
(assert_return (invoke "\u{8fffe}") (i32.const 0x7c))
(assert_return (invoke "\u{8ffff}") (i32.const 0x7d))
(assert_return (invoke "\u{9fffe}") (i32.const 0x7e))
(assert_return (invoke "\u{9ffff}") (i32.const 0x7f))
(assert_return (invoke "\u{afffe}") (i32.const 0x80))
(assert_return (invoke "\u{affff}") (i32.const 0x81))
(assert_return (invoke "\u{bfffe}") (i32.const 0x82))
(assert_return (invoke "\u{bffff}") (i32.const 0x83))
(assert_return (invoke "\u{cfffe}") (i32.const 0x84))
(assert_return (invoke "\u{cffff}") (i32.const 0x85))
(assert_return (invoke "\u{dfffe}") (i32.const 0x86))
(assert_return (invoke "\u{dffff}") (i32.const 0x87))
(assert_return (invoke "\u{efffe}") (i32.const 0x88))
(assert_return (invoke "\u{effff}") (i32.const 0x89))
(assert_return (invoke "\u{ffffe}") (i32.const 0x8a))
(assert_return (invoke "\u{fffff}") (i32.const 0x8b))
(assert_return (invoke "\u{10fffe}") (i32.const 0x8c))
(assert_return (invoke "\u{10ffff}") (i32.const 0x8d))
(assert_return (invoke "\u{308}\u{203d}\u{308}\u{309}") (i32.const 0x8e))
(assert_return (invoke "abc") (i32.const 0x8f))
(assert_return (invoke "\u{202d}abc") (i32.const 0x90))
(assert_return (invoke "\u{202e}cba") (i32.const 0x91))
(assert_return (invoke "\u{202d}abc\u{202e}") (i32.const 0x92))
(assert_return (invoke "\u{202e}cba\u{202d}") (i32.const 0x93))
(assert_return (invoke "\u{1d468}") (i32.const 0x94))
(assert_return (invoke "\u{1d434}") (i32.const 0x95))
(assert_return (invoke "\u{1d608}") (i32.const 0x96))
(assert_return (invoke "\u{1d63c}") (i32.const 0x97))
(assert_return (invoke "\u{1d400}") (i32.const 0x98))
(assert_return (invoke "\u{1d4d0}") (i32.const 0x99))
(assert_return (invoke "\u{1d56c}") (i32.const 0x9a))
(assert_return (invoke "\u{1d5d4}") (i32.const 0x9b))
(assert_return (invoke "\u{1d49c}") (i32.const 0x9c))
(assert_return (invoke "\u{1d504}") (i32.const 0x9d))
(assert_return (invoke "\u{1d538}") (i32.const 0x9e))
(assert_return (invoke "\u{1d5a0}") (i32.const 0x9f))
(assert_return (invoke "\u{1d670}") (i32.const 0xa0))
(assert_return (invoke "\u{1d00}") (i32.const 0xa1))
(assert_return (invoke "\u{1d2c}") (i32.const 0xa2))
(assert_return (invoke "\u{24b6}") (i32.const 0xa3))
(assert_return (invoke "\u{ff21}") (i32.const 0xa4))
(assert_return (invoke "\u{1f110}") (i32.const 0xa5))
(assert_return (invoke "\u{1f130}") (i32.const 0xa6))
(assert_return (invoke "\u{e0041}") (i32.const 0xa7))
(assert_return (invoke "U+0041") (i32.const 0xa8))
(assert_return (invoke "A\u{200b}") (i32.const 0xa9))
(assert_return (invoke "\u{410}") (i32.const 0xaa))
(assert_return (invoke "\u{a656}") (i32.const 0xab))
(assert_return (invoke "\u{2dfc}") (i32.const 0xac))
(assert_return (invoke "\u{2df6}") (i32.const 0xad))
(assert_return (invoke "\u{2c6f}") (i32.const 0xae))
(assert_return (invoke "\u{1f150}") (i32.const 0xaf))
(assert_return (invoke "\u{1f170}") (i32.const 0xb0))
(assert_return (invoke "\u{2c2d}") (i32.const 0xb1))
(assert_return (invoke "\u{10402}") (i32.const 0xb2))
(assert_return (invoke "\u{10408}") (i32.const 0xb3))
(assert_return (invoke "\u{104b0}") (i32.const 0xb4))
(assert_return (invoke "\u{c0}") (i32.const 0xb5))
(assert_return (invoke "\u{c1}") (i32.const 0xb6))
(assert_return (invoke "\u{c2}") (i32.const 0xb7))
(assert_return (invoke "\u{c3}") (i32.const 0xb8))
(assert_return (invoke "\u{c4}") (i32.const 0xb9))
(assert_return (invoke "\u{100}") (i32.const 0xba))
(assert_return (invoke "\u{102}") (i32.const 0xbb))
(assert_return (invoke "\u{104}") (i32.const 0xbc))
(assert_return (invoke "\u{1cd}") (i32.const 0xbd))
(assert_return (invoke "\u{1de}") (i32.const 0xbe))
(assert_return (invoke "\u{1e0}") (i32.const 0xbf))
(assert_return (invoke "\u{1fa}") (i32.const 0xc0))
(assert_return (invoke "\u{200}") (i32.const 0xc1))
(assert_return (invoke "\u{202}") (i32.const 0xc2))
(assert_return (invoke "\u{226}") (i32.const 0xc3))
(assert_return (invoke "\u{23a}") (i32.const 0xc4))
(assert_return (invoke "\u{4d0}") (i32.const 0xc5))
(assert_return (invoke "\u{4d2}") (i32.const 0xc6))
(assert_return (invoke "\u{7ca}") (i32.const 0xc7))
(assert_return (invoke "\u{821}") (i32.const 0xc8))
(assert_return (invoke "\u{822}") (i32.const 0xc9))
(assert_return (invoke "\u{823}") (i32.const 0xca))
(assert_return (invoke "\u{824}") (i32.const 0xcb))
(assert_return (invoke "\u{825}") (i32.const 0xcc))
(assert_return (invoke "\u{904}") (i32.const 0xcd))
(assert_return (invoke "\u{905}") (i32.const 0xce))
(assert_return (invoke "\u{972}") (i32.const 0xcf))
(assert_return (invoke "\u{985}") (i32.const 0xd0))
(assert_return (invoke "\u{a05}") (i32.const 0xd1))
(assert_return (invoke "\u{a85}") (i32.const 0xd2))
(assert_return (invoke "\u{b05}") (i32.const 0xd3))
(assert_return (invoke "\u{b85}") (i32.const 0xd4))
(assert_return (invoke "\u{c05}") (i32.const 0xd5))
(assert_return (invoke "\u{c85}") (i32.const 0xd6))
(assert_return (invoke "\u{d05}") (i32.const 0xd7))
(assert_return (invoke "\u{e30}") (i32.const 0xd8))
(assert_return (invoke "\u{eb0}") (i32.const 0xd9))
(assert_return (invoke "\u{f01}") (i32.const 0xda))
(assert_return (invoke "\u{f68}") (i32.const 0xdb))
(assert_return (invoke "\u{fb8}") (i32.const 0xdc))
(assert_return (invoke "\u{1021}") (i32.const 0xdd))
(assert_return (invoke "\u{1022}") (i32.const 0xde))
(assert_return (invoke "\u{109c}") (i32.const 0xdf))
(assert_return (invoke "\u{1161}") (i32.const 0xe0))
(assert_return (invoke "\u{12a0}") (i32.const 0xe1))
(assert_return (invoke "\u{12d0}") (i32.const 0xe2))
(assert_return (invoke "\u{13a0}") (i32.const 0xe3))
(assert_return (invoke "\u{140a}") (i32.const 0xe4))
(assert_return (invoke "\u{15b3}") (i32.const 0xe5))
(assert_return (invoke "\u{16a8}") (i32.const 0xe6))
(assert_return (invoke "\u{16aa}") (i32.const 0xe7))
(assert_return (invoke "\u{16c6}") (i32.const 0xe8))
(assert_return (invoke "\u{1700}") (i32.const 0xe9))
(assert_return (invoke "\u{1720}") (i32.const 0xea))
(assert_return (invoke "\u{1740}") (i32.const 0xeb))
(assert_return (invoke "\u{1760}") (i32.const 0xec))
(assert_return (invoke "\u{1820}") (i32.const 0xed))
(assert_return (invoke "\u{1887}") (i32.const 0xee))
(assert_return (invoke "\u{1920}") (i32.const 0xef))
(assert_return (invoke "\u{1963}") (i32.const 0xf0))
(assert_return (invoke "\u{1a15}") (i32.const 0xf1))
(assert_return (invoke "\u{1a4b}") (i32.const 0xf2))
(assert_return (invoke "\u{1a61}") (i32.const 0xf3))
(assert_return (invoke "\u{1b83}") (i32.const 0xf4))
(assert_return (invoke "\u{1bc0}") (i32.const 0xf5))
(assert_return (invoke "\u{1bc1}") (i32.const 0xf6))
(assert_return (invoke "\u{1c23}") (i32.const 0xf7))
(assert_return (invoke "\u{1e00}") (i32.const 0xf8))
(assert_return (invoke "\u{1ea0}") (i32.const 0xf9))
(assert_return (invoke "\u{1ea2}") (i32.const 0xfa))
(assert_return (invoke "\u{1ea4}") (i32.const 0xfb))
(assert_return (invoke "\u{1ea6}") (i32.const 0xfc))
(assert_return (invoke "\u{1ea8}") (i32.const 0xfd))
(assert_return (invoke "\u{1eaa}") (i32.const 0xfe))
(assert_return (invoke "\u{1eac}") (i32.const 0xff))
(assert_return (invoke "\u{1eae}") (i32.const 0x100))
(assert_return (invoke "\u{1eb0}") (i32.const 0x101))
(assert_return (invoke "\u{1eb2}") (i32.const 0x102))
(assert_return (invoke "\u{1eb4}") (i32.const 0x103))
(assert_return (invoke "\u{1eb6}") (i32.const 0x104))
(assert_return (invoke "\u{3042}") (i32.const 0x105))
(assert_return (invoke "\u{30a2}") (i32.const 0x106))
(assert_return (invoke "\u{311a}") (i32.const 0x107))
(assert_return (invoke "\u{314f}") (i32.const 0x108))
(assert_return (invoke "\u{320e}") (i32.const 0x109))
(assert_return (invoke "\u{320f}") (i32.const 0x10a))
(assert_return (invoke "\u{3210}") (i32.const 0x10b))
(assert_return (invoke "\u{3211}") (i32.const 0x10c))
(assert_return (invoke "\u{3212}") (i32.const 0x10d))
(assert_return (invoke "\u{3213}") (i32.const 0x10e))
(assert_return (invoke "\u{3214}") (i32.const 0x10f))
(assert_return (invoke "\u{3215}") (i32.const 0x110))
(assert_return (invoke "\u{3216}") (i32.const 0x111))
(assert_return (invoke "\u{3217}") (i32.const 0x112))
(assert_return (invoke "\u{3218}") (i32.const 0x113))
(assert_return (invoke "\u{3219}") (i32.const 0x114))
(assert_return (invoke "\u{321a}") (i32.const 0x115))
(assert_return (invoke "\u{321b}") (i32.const 0x116))
(assert_return (invoke "\u{326e}") (i32.const 0x117))
(assert_return (invoke "\u{326f}") (i32.const 0x118))
(assert_return (invoke "\u{3270}") (i32.const 0x119))
(assert_return (invoke "\u{3271}") (i32.const 0x11a))
(assert_return (invoke "\u{3272}") (i32.const 0x11b))
(assert_return (invoke "\u{3273}") (i32.const 0x11c))
(assert_return (invoke "\u{3274}") (i32.const 0x11d))
(assert_return (invoke "\u{3275}") (i32.const 0x11e))
(assert_return (invoke "\u{3276}") (i32.const 0x11f))
(assert_return (invoke "\u{3277}") (i32.const 0x120))
(assert_return (invoke "\u{3278}") (i32.const 0x121))
(assert_return (invoke "\u{3279}") (i32.const 0x122))
(assert_return (invoke "\u{327a}") (i32.const 0x123))
(assert_return (invoke "\u{327b}") (i32.const 0x124))
(assert_return (invoke "\u{32d0}") (i32.const 0x125))
(assert_return (invoke "\u{a00a}") (i32.const 0x126))
(assert_return (invoke "\u{a4ee}") (i32.const 0x127))
(assert_return (invoke "\u{a549}") (i32.const 0x128))
(assert_return (invoke "\u{a6a0}") (i32.const 0x129))
(assert_return (invoke "\u{a800}") (i32.const 0x12a))
(assert_return (invoke "\u{a823}") (i32.const 0x12b))
(assert_return (invoke "\u{a85d}") (i32.const 0x12c))
(assert_return (invoke "\u{a882}") (i32.const 0x12d))
(assert_return (invoke "\u{a8ea}") (i32.const 0x12e))
(assert_return (invoke "\u{a922}") (i32.const 0x12f))
(assert_return (invoke "\u{a946}") (i32.const 0x130))
(assert_return (invoke "\u{a984}") (i32.const 0x131))
(assert_return (invoke "\u{aa00}") (i32.const 0x132))
(assert_return (invoke "\u{ff71}") (i32.const 0x133))
(assert_return (invoke "\u{ffc2}") (i32.const 0x134))
(assert_return (invoke "\u{10000}") (i32.const 0x135))
(assert_return (invoke "\u{10280}") (i32.const 0x136))
(assert_return (invoke "\u{102a0}") (i32.const 0x137))
(assert_return (invoke "\u{10300}") (i32.const 0x138))
(assert_return (invoke "\u{103a0}") (i32.const 0x139))
(assert_return (invoke "\u{10496}") (i32.const 0x13a))
(assert_return (invoke "\u{10500}") (i32.const 0x13b))
(assert_return (invoke "\u{10740}") (i32.const 0x13c))
(assert_return (invoke "\u{10800}") (i32.const 0x13d))
(assert_return (invoke "\u{10920}") (i32.const 0x13e))
(assert_return (invoke "\u{10980}") (i32.const 0x13f))
(assert_return (invoke "\u{109a0}") (i32.const 0x140))
(assert_return (invoke "\u{10a00}") (i32.const 0x141))
(assert_return (invoke "\u{10b00}") (i32.const 0x142))
(assert_return (invoke "\u{10c00}") (i32.const 0x143))
(assert_return (invoke "\u{10c01}") (i32.const 0x144))
(assert_return (invoke "\u{10c80}") (i32.const 0x145))
(assert_return (invoke "\u{11005}") (i32.const 0x146))
(assert_return (invoke "\u{11083}") (i32.const 0x147))
(assert_return (invoke "\u{11127}") (i32.const 0x148))
(assert_return (invoke "\u{11150}") (i32.const 0x149))
(assert_return (invoke "\u{11183}") (i32.const 0x14a))
(assert_return (invoke "\u{11200}") (i32.const 0x14b))
(assert_return (invoke "\u{11280}") (i32.const 0x14c))
(assert_return (invoke "\u{112b0}") (i32.const 0x14d))
(assert_return (invoke "\u{11305}") (i32.const 0x14e))
(assert_return (invoke "\u{11370}") (i32.const 0x14f))
(assert_return (invoke "\u{11400}") (i32.const 0x150))
(assert_return (invoke "\u{11481}") (i32.const 0x151))
(assert_return (invoke "\u{11580}") (i32.const 0x152))
(assert_return (invoke "\u{11600}") (i32.const 0x153))
(assert_return (invoke "\u{11680}") (i32.const 0x154))
(assert_return (invoke "\u{11712}") (i32.const 0x155))
(assert_return (invoke "\u{11720}") (i32.const 0x156))
(assert_return (invoke "\u{118a1}") (i32.const 0x157))
(assert_return (invoke "\u{11ad5}") (i32.const 0x158))
(assert_return (invoke "\u{11c00}") (i32.const 0x159))
(assert_return (invoke "\u{11c8f}") (i32.const 0x15a))
(assert_return (invoke "\u{11caf}") (i32.const 0x15b))
(assert_return (invoke "\u{12000}") (i32.const 0x15c))
(assert_return (invoke "\u{169d5}") (i32.const 0x15d))
(assert_return (invoke "\u{16a46}") (i32.const 0x15e))
(assert_return (invoke "\u{16ae7}") (i32.const 0x15f))
(assert_return (invoke "\u{16f54}") (i32.const 0x160))
(assert_return (invoke "\u{1bc41}") (i32.const 0x161))
(assert_return (invoke "\u{1bc64}") (i32.const 0x162))
(assert_return (invoke "\u{1e823}") (i32.const 0x163))
(assert_return (invoke "\u{1f1e6}") (i32.const 0x164))
(assert_return (invoke "\u{2c6d}") (i32.const 0x165))
(assert_return (invoke "\u{39b}") (i32.const 0x166))
(assert_return (invoke "\u{2c70}") (i32.const 0x167))
(assert_return (invoke "\u{aa}") (i32.const 0x168))
(assert_return (invoke "\u{2200}") (i32.const 0x169))
(assert_return (invoke "\u{20b3}") (i32.const 0x16a))
(assert_return (invoke "\u{10900}") (i32.const 0x16b))
(assert_return (invoke "\u{2c80}") (i32.const 0x16c))
(assert_return (invoke "\u{10330}") (i32.const 0x16d))
(assert_return (invoke "\u{386}") (i32.const 0x16e))
(assert_return (invoke "\u{391}") (i32.const 0x16f))
(assert_return (invoke "\u{1f08}") (i32.const 0x170))
(assert_return (invoke "\u{1f09}") (i32.const 0x171))
(assert_return (invoke "\u{1f0a}") (i32.const 0x172))
(assert_return (invoke "\u{1f0b}") (i32.const 0x173))
(assert_return (invoke "\u{1f0c}") (i32.const 0x174))
(assert_return (invoke "\u{1f0d}") (i32.const 0x175))
(assert_return (invoke "\u{1f0e}") (i32.const 0x176))
(assert_return (invoke "\u{1f0f}") (i32.const 0x177))
(assert_return (invoke "\u{1f88}") (i32.const 0x178))
(assert_return (invoke "\u{1f89}") (i32.const 0x179))
(assert_return (invoke "\u{1f8a}") (i32.const 0x17a))
(assert_return (invoke "\u{1f8b}") (i32.const 0x17b))
(assert_return (invoke "\u{1f8c}") (i32.const 0x17c))
(assert_return (invoke "\u{1f8d}") (i32.const 0x17d))
(assert_return (invoke "\u{1f8e}") (i32.const 0x17e))
(assert_return (invoke "\u{1f8f}") (i32.const 0x17f))
(assert_return (invoke "\u{1fb8}") (i32.const 0x180))
(assert_return (invoke "\u{1fb9}") (i32.const 0x181))
(assert_return (invoke "\u{1fba}") (i32.const 0x182))
(assert_return (invoke "\u{1fbb}") (i32.const 0x183))
(assert_return (invoke "\u{1fbc}") (i32.const 0x184))
(assert_return (invoke "\u{1d6a8}") (i32.const 0x185))
(assert_return (invoke "\u{1d6e2}") (i32.const 0x186))
(assert_return (invoke "\u{1d71c}") (i32.const 0x187))
(assert_return (invoke "\u{1d756}") (i32.const 0x188))
(assert_return (invoke "\u{1d790}") (i32.const 0x189))
(assert_return (invoke "\u{2376}") (i32.const 0x18a))
(assert_return (invoke "\u{237a}") (i32.const 0x18b))
(assert_return (invoke "\u{2a5c}") (i32.const 0x18c))
(assert_return (invoke "\u{15c5}") (i32.const 0x18d))
(assert_return (invoke "\u{13aa}") (i32.const 0x18e))
(assert_return
  (invoke ")\u{2fa}\u{2fc}\u{145cf}\u{1d174}\u{1d176}\u{1d178}\u{1d17a}\u{207e}\u{208e}\u{2769}\u{276b}\u{27ef}\u{fd3f}\u{fe36}\u{fe5a}\u{ff09}\u{ff60}\u{e0029}\u{2773}\u{2775}\u{27e7}\u{27e9}\u{27eb}\u{27ed}\u{2988}\u{298a}\u{2996}\u{2e23}\u{2e25}\u{fe18}\u{fe38}\u{fe3a}\u{fe3c}\u{fe3e}\u{fe40}\u{fe42}\u{fe44}\u{fe48}\u{fe5c}\u{fe5e}\u{ff3d}\u{ff5d}\u{ff63}\u{e005d}\u{e007d}\u{bb}\u{2019}\u{201d}\u{203a}\u{276f}"
  )
  (i32.const 0x18f)
)
(assert_return
  (invoke "(\u{2f9}\u{2fb}\u{145ce}\u{1d173}\u{1d175}\u{1d177}\u{1d179}\u{207d}\u{208d}\u{2768}\u{276a}\u{27ee}\u{fd3e}\u{fe35}\u{fe59}\u{ff08}\u{ff5f}\u{e0028}\u{2772}\u{2774}\u{27e6}\u{27e8}\u{27ea}\u{27ec}\u{2987}\u{2989}\u{2995}\u{2e22}\u{2e24}\u{fe17}\u{fe37}\u{fe39}\u{fe3b}\u{fe3d}\u{fe3f}\u{fe41}\u{fe43}\u{fe47}\u{fe5b}\u{fe5d}\u{ff3b}\u{ff5b}\u{ff62}\u{e005b}\u{e007b}\u{ab}\u{2018}\u{201c}\u{2039}\u{276e}"
  )
  (i32.const 0x190)
)
(assert_return (invoke "\u{1da8b}\u{1daa4}") (i32.const 0x191))
(assert_return (invoke "\u{1da8b}") (i32.const 0x192))
(assert_return (invoke "\u{bd}") (i32.const 0x193))
(assert_return (invoke "1\u{2044}2") (i32.const 0x194))
(assert_return (invoke "1/2") (i32.const 0x195))
(assert_return (invoke "\u{b73}") (i32.const 0x196))
(assert_return (invoke "\u{d74}") (i32.const 0x197))
(assert_return (invoke "\u{2cfd}") (i32.const 0x198))
(assert_return (invoke "\u{a831}") (i32.const 0x199))
(assert_return (invoke "\u{10141}") (i32.const 0x19a))
(assert_return (invoke "\u{10175}") (i32.const 0x19b))
(assert_return (invoke "\u{10176}") (i32.const 0x19c))
(assert_return (invoke "\u{109bd}") (i32.const 0x19d))
(assert_return (invoke "\u{10e7b}") (i32.const 0x19e))
(assert_return (invoke "\u{ff02}") (i32.const 0x19f))
(assert_return (invoke "\u{7f}") (i32.const 0x1a0))
(assert_return (invoke "\u{08}") (i32.const 0x1a1))
(assert_return (invoke "\u{232b}") (i32.const 0x1a2))
(assert_return (invoke "\u{2326}") (i32.const 0x1a3))
(assert_return (invoke "\u{2408}") (i32.const 0x1a4))
(assert_return (invoke "\u{2421}") (i32.const 0x1a5))
(assert_return (invoke "\u{1dfb}") (i32.const 0x1a6))
(assert_return (invoke "\u{0f}") (i32.const 0x1a7))
(assert_return (invoke "\u{2190}") (i32.const 0x1a8))
(assert_return (invoke "\u{2327}") (i32.const 0x1a9))
(assert_return (invoke "\u{2352}") (i32.const 0x1aa))
(assert_return (invoke "\u{2354}") (i32.const 0x1ab))
(assert_return (invoke "\u{2362}") (i32.const 0x1ac))
(assert_return (invoke "\u{236b}") (i32.const 0x1ad))
(assert_return (invoke "\u{1a}") (i32.const 0x1ae))
(assert_return (invoke "\u{2426}") (i32.const 0x1af))
(assert_return (invoke "\u{241a}") (i32.const 0x1b0))
(assert_return (invoke "\u{fffc}") (i32.const 0x1b1))
(assert_return (invoke "?") (i32.const 0x1b2))
(assert_return (invoke "\u{bf}") (i32.const 0x1b3))
(assert_return (invoke "\u{1945}") (i32.const 0x1b4))
(assert_return (invoke "\u{37e}") (i32.const 0x1b5))
(assert_return (invoke "\u{55e}") (i32.const 0x1b6))
(assert_return (invoke "\u{61f}") (i32.const 0x1b7))
(assert_return (invoke "\u{1367}") (i32.const 0x1b8))
(assert_return (invoke "\u{2047}") (i32.const 0x1b9))
(assert_return (invoke "\u{2370}") (i32.const 0x1ba))
(assert_return (invoke "\u{2753}") (i32.const 0x1bb))
(assert_return (invoke "\u{2754}") (i32.const 0x1bc))
(assert_return (invoke "\u{2cfa}") (i32.const 0x1bd))
(assert_return (invoke "\u{2cfb}") (i32.const 0x1be))
(assert_return (invoke "\u{2e2e}") (i32.const 0x1bf))
(assert_return (invoke "\u{3244}") (i32.const 0x1c0))
(assert_return (invoke "\u{a60f}") (i32.const 0x1c1))
(assert_return (invoke "\u{a6f7}") (i32.const 0x1c2))
(assert_return (invoke "\u{fe16}") (i32.const 0x1c3))
(assert_return (invoke "\u{fe56}") (i32.const 0x1c4))
(assert_return (invoke "\u{ff1f}") (i32.const 0x1c5))
(assert_return (invoke "\u{11143}") (i32.const 0x1c6))
(assert_return (invoke "\u{1e95f}") (i32.const 0x1c7))
(assert_return (invoke "\u{e003f}") (i32.const 0x1c8))
(assert_return (invoke "\u{16844}") (i32.const 0x1c9))
(assert_return (invoke "\u{2bd1}") (i32.const 0x1ca))
(assert_return (invoke "\u{b6}") (i32.const 0x1cb))
(assert_return (invoke "\u{204b}") (i32.const 0x1cc))
(assert_return (invoke "\u{700}") (i32.const 0x1cd))
(assert_return (invoke "\u{10fb}") (i32.const 0x1ce))
(assert_return (invoke "\u{1368}") (i32.const 0x1cf))
(assert_return (invoke "\u{3037}") (i32.const 0x1d0))
(assert_return (invoke "\u{2761}") (i32.const 0x1d1))
(assert_return (invoke "\u{2e0f}") (i32.const 0x1d2))
(assert_return (invoke "\u{2e10}") (i32.const 0x1d3))
(assert_return (invoke "\u{2e11}") (i32.const 0x1d4))
(assert_return (invoke "\u{2e0e}") (i32.const 0x1d5))
(assert_return (invoke "\u{14}") (i32.const 0x1d6))
(assert_return (invoke "\u{2619}") (i32.const 0x1d7))
(assert_return (invoke "\u{2e3f}") (i32.const 0x1d8))
(assert_return (invoke "\u{3007}") (i32.const 0x1d9))
(assert_return (invoke "\u{e5b}") (i32.const 0x1da))
(assert_return (invoke "\u{a66e}") (i32.const 0x1db))
(assert_return (invoke "\u{3d3}") (i32.const 0x1dc))
(assert_return (invoke "\u{3d4}") (i32.const 0x1dd))
(assert_return (invoke "\u{1e9b}") (i32.const 0x1de))
(module definition binary
  "\00\61\73\6d\01\00\00\00\01\8a\80\80\80\00\02\60"
  "\01\7f\00\60\02\7f\7f\00\02\ab\80\80\80\00\02\08"
  "\73\70\65\63\74\65\73\74\09\70\72\69\6e\74\5f\69"
  "\33\32\00\00\08\73\70\65\63\74\65\73\74\09\70\72"
  "\69\6e\74\5f\69\33\32\00\00\03\82\80\80\80\00\01"
  "\01\07\8b\80\80\80\00\01\07\70\72\69\6e\74\33\32"
  "\00\02\0a\90\80\80\80\00\01\8a\80\80\80\00\00\20"
  "\00\10\00\20\01\10\01\0b"
)
(module instance)
(assert_return (invoke "print32" (i32.const 0x2a) (i32.const 0x7b)))
