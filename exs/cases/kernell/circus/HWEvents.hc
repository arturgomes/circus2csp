CircChannel [CChan "tick"]
CircChannel [CChan "tock"]
ZAbbreviation ("A",[],"") (ZSetDisplay [ZInt 0,ZInt 1])
ZAbbreviation ("D",[],"") (ZSetDisplay [ZInt 0,ZInt 1])
ZFreeTypeDef ("Dir",[],"") [ZBranch0 ("R",[],""),ZBranch0 ("W",[],"")]
CircChannel [CChanDecl "ma" (ZCross [ZVar ("Dir",[],""),ZVar ("A",[],"")])]
CircChannel [CChanDecl "md" (ZCross [ZVar ("Dir",[],""),ZVar ("D",[],"")])]
CircChannel [CChan "iTMR",CChan "rTMR"]
CircChannel [CChan "iMMU",CChan "rMMU"]
CircChannel [CChan "iDEV",CChan "rDEV"]
CircChannel [CChan "iTRP",CChan "rTRP"]
ZFreeTypeDef ("I",[],"") [ZBranch0 ("NOP",[],""),ZBranch0 ("S0",[],""),ZBranch0 ("S1",[],"")]
ZAbbreviation ("OP",[],"") (ZSetDisplay [ZCall (ZVar ("\\upto",[],"")) (ZTuple [ZInt 0,ZInt 1])])
ZFreeTypeDef ("PM",[],"") [ZBranch0 ("USR",[],""),ZBranch0 ("SUP",[],"")]
CircChannel [CChanDecl "pm" (ZVar ("PM",[],""))]
ZFreeTypeDef ("UNIVERSE",[],"") []
ZFreeTypeDef ("NAME",[],"") []
ZAbbreviation ("BINDINGS",[],"") (ZCall (ZVar ("\\cup",[],"")) (ZTuple []))
CircChannel [CChanDecl "mget" (ZCross [ZVar ("NAME",[],""),ZVar ("UNIVERSE",[],"")]),CChanDecl "mset" (ZCross [ZVar ("NAME",[],""),ZVar ("UNIVERSE",[],"")])]
CircChannel [CChan "terminate"]
CircChanSet "MEMI" (CChanSet ["mset","mget","terminate"])
CircChannel [CChanDecl "lget" (ZCross [ZVar ("NAME",[],""),ZVar ("UNIVERSE",[],"")]),CChanDecl "lset" (ZCross [ZVar ("NAME",[],""),ZVar ("UNIVERSE",[],"")])]
CircChannel [CChan "lterminate"]
CircChanSet "MEML" (CChanSet ["lset","lget","lterminate"])
