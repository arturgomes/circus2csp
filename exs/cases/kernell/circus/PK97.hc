Assert "include Platform.csp"
CircChannel [CChan "pk97fail"]
Process (CProcess "PK97" (ProcDef (ProcStalessMain [CParAction "PK97knl" (CircusAction (CSPExtChoice (CSPExtChoice (CSPExtChoice (CSPCommAction (ChanComm "fi" [ChanDotExp (ZVar ("KNL",[],"")),ChanInp "i",ChanInp "op"]) (CActionName "PK97knl")) (CSPCommAction (ChanComm "fi" [ChanDotExp (ZVar ("P1",[],"")),ChanInp "i",ChanInp "op"]) (CActionName "PK97part"))) (CSPCommAction (ChanComm "st" [ChanDotExp (ZVar ("P1",[],"")),ChanDotExp (ZVar ("CLD",[],""))]) (CActionName "PK97cold"))) (CSPCommAction (ChanComm "st" [ChanDotExp (ZVar ("P1",[],"")),ChanDotExp (ZVar ("WRM",[],""))]) (CActionName "PK97warm")))),CParAction "PK97part" (CircusAction (CSPExtChoice (CSPCommAction (ChanComm "fi" [ChanDotExp (ZVar ("KNL",[],"")),ChanInp "i",ChanInp "op"]) (CActionName "PK97knl")) (CSPCommAction (ChanComm "fi" [ChanDotExp (ZVar ("P1",[],"")),ChanInp "i",ChanInp "op"]) (CActionName "PK97part")))),CParAction "PK97cold" (CircusAction (CSPCommAction (ChanComm "lbl" [ChanDotExp (ZVar ("CLD",[],""))]) (CSPCommAction (ChanComm "fi" [ChanInp "P1",ChanInp "i",ChanInp "op"]) (CActionName "PK97warm")))),CParAction "PK97warm" (CircusAction (CSPCommAction (ChanComm "lbl" [ChanDotExp (ZVar ("WRM",[],""))]) (CSPCommAction (ChanComm "fi" [ChanInp "P1",ChanInp "i",ChanInp "op"]) (CActionName "PK97part"))))] (CActionName "PK97knl"))))
Assert "assert PK97 :[divergence free]"
Assert "assert PK97 :[deadlock free[F]]"
Assert "PK97TEST(CODE) = (PK97 [| {| fi, st, lbl |} |] (PMM [| {| fi |} |] CODE))"
Process (CProcess "PK97GOODCODE" (ProcDef (ProcStalessMain [CParAction "PK97GOODCODEAct" (CircusAction (CSPCommAction (ChanComm "fi" [ChanDotExp (ZVar ("KNL",[],"")),ChanDotExp (ZVar ("S0",[],"")),ChanDotExp (ZInt 0)]) (CSPCommAction (ChanComm "st" [ChanDotExp (ZVar ("P1",[],"")),ChanDotExp (ZVar ("CLD",[],""))]) (CSPCommAction (ChanComm "lbl" [ChanDotExp (ZVar ("CLD",[],""))]) (CSPCommAction (ChanComm "fi" [ChanDotExp (ZVar ("P1",[],"")),ChanDotExp (ZVar ("NOP",[],"")),ChanDotExp (ZInt 0)]) (CSPCommAction (ChanComm "lbl" [ChanDotExp (ZVar ("WRM",[],""))]) (CSPCommAction (ChanComm "fi" [ChanDotExp (ZVar ("P1",[],"")),ChanDotExp (ZVar ("NOP",[],"")),ChanDotExp (ZInt 1)]) (CSPCommAction (ChanComm "fi" [ChanDotExp (ZVar ("KNL",[],"")),ChanDotExp (ZVar ("S0",[],"")),ChanDotExp (ZInt 0)]) (CSPCommAction (ChanComm "st" [ChanDotExp (ZVar ("P1",[],"")),ChanDotExp (ZVar ("WRM",[],""))]) (CSPCommAction (ChanComm "lbl" [ChanDotExp (ZVar ("WRM",[],""))]) (CSPCommAction (ChanComm "fi" [ChanDotExp (ZVar ("P1",[],"")),ChanDotExp (ZVar ("NOP",[],"")),ChanDotExp (ZInt 1)]) (CActionName "PK97GOODCODEAct"))))))))))))] (CActionName "PK97GOODCODEAct"))))
Assert "assert PK97GOODCODE :[divergence free]"
Assert "assert PK97GOODCODE :[deadlock free[F]]"
Assert "PK97OK = PK97TEST(PK97GOODCODE)"
Assert "assert PK97OK :[divergence free]"
Assert "assert PK97OK :[deadlock free[F]]  -- MUST SUCCEED !!"
Process (CProcess "PK97BAD1CODE" (ProcDef (ProcStalessMain [CParAction "Act" (CircusAction (CSPCommAction (ChanComm "fi" [ChanDotExp (ZVar ("KNL",[],"")),ChanDotExp (ZVar ("S0",[],"")),ChanDotExp (ZInt 0)]) (CSPCommAction (ChanComm "st" [ChanDotExp (ZVar ("P1",[],"")),ChanDotExp (ZVar ("CLD",[],""))]) (CSPCommAction (ChanComm "fi" [ChanDotExp (ZVar ("P1",[],"")),ChanDotExp (ZVar ("NOP",[],"")),ChanDotExp (ZInt 0)]) (CActionName "Act")))))] (CActionName "Act"))))
Process (CProcess "PK97BAD2CODE" (ProcDef (ProcStalessMain [CParAction "Act" (CircusAction (CSPCommAction (ChanComm "fi" [ChanDotExp (ZVar ("KNL",[],"")),ChanDotExp (ZVar ("S0",[],"")),ChanDotExp (ZInt 1)]) (CSPCommAction (ChanComm "lbl" [ChanDotExp (ZVar ("WRM",[],""))]) (CSPCommAction (ChanComm "fi" [ChanDotExp (ZVar ("P1",[],"")),ChanDotExp (ZVar ("NOP",[],"")),ChanDotExp (ZInt 1)]) (CActionName "Act")))))] (CActionName "Act"))))
Assert "assert PK97BAD1CODE :[divergence free]"
Assert "assert PK97BAD1CODE :[deadlock free[F]]"
Assert "assert PK97BAD2CODE :[divergence free]"
Assert "assert PK97BAD2CODE :[deadlock free[F]]"
Assert "PK97BAD1 = PK97TEST(PK97BAD1CODE)"
Assert "PK97BAD2 = PK97TEST(PK97BAD2CODE)"
Assert "assert PK97BAD1 :[divergence free]"
Assert "assert PK97BAD2 :[divergence free]"
Assert "assert PK97BAD1 :[deadlock free[F]]  -- MUST FAIL !!"
Assert "assert PK97BAD2 :[deadlock free[F]]  -- MUST FAIL !!"
ZFreeTypeDef ("UNIVERSE",[],"") []
ZFreeTypeDef ("NAME",[],"") []
ZAbbreviation ("BINDINGS",[],"") (ZCall (ZVar ("\\cup",[],"")) (ZTuple []))
CircChannel [CChanDecl "mget" (ZCross [ZVar ("NAME",[],""),ZVar ("UNIVERSE",[],"")]),CChanDecl "mset" (ZCross [ZVar ("NAME",[],""),ZVar ("UNIVERSE",[],"")])]
CircChannel [CChan "terminate"]
CircChanSet "MEMI" (CChanSet ["mset","mget","terminate"])
CircChannel [CChanDecl "lget" (ZCross [ZVar ("NAME",[],""),ZVar ("UNIVERSE",[],"")]),CChanDecl "lset" (ZCross [ZVar ("NAME",[],""),ZVar ("UNIVERSE",[],"")])]
CircChannel [CChan "lterminate"]
CircChanSet "MEML" (CChanSet ["lset","lget","lterminate"])
