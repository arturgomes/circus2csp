ZAbbreviation ("INDEX",[],"") (ZVar ("\\nat",[],""))
ZAbbreviation ("MONEY",[],"") (ZSetDisplay [ZCall (ZVar ("\\upto",[],"")) (ZTuple [ZInt 0,ZInt 5])])
CircChannel [CChanDecl "pay" (ZCross [ZVar ("INDEX",[],""),ZVar ("INDEX",[],""),ZVar ("MONEY",[],"")])]
CircChannel [CChanDecl "transfer" (ZCross [ZVar ("INDEX",[],""),ZVar ("INDEX",[],""),ZVar ("MONEY",[],"")])]
CircChannel [CChanDecl "accept" (ZVar ("INDEX",[],""))]
CircChannel [CChanDecl "reject" (ZVar ("INDEX",[],""))]
Process (CProcess "Card" (ProcDefSpot [Choose ("i",[],"") (ZVar ("INDEX",[],""))] (ProcDef (ProcMain (ZSchemaDef (ZSPlain "SCard") (ZSchema [Choose ("value",[],"") (ZVar ("INDEX",[],""))])) [CParAction "Init" (CircusAction (CActionCommand (CAssign [("value",[],"")] [ZInt 0]))),CParAction "Credit" (CircusAction (CActionCommand (CVarDecl [Choose ("n",[],"") (ZVar ("INDEX",[],""))] (CActionCommand (CAssign [("value",[],"")] [ZCall (ZVar ("+",[],"")) (ZTuple [ZVar ("value",[],""),ZVar ("n",[],"")])]))))),CParAction "Debit" (CircusAction (CActionCommand (CVarDecl [Choose ("n",[],"") (ZVar ("INDEX",[],""))] (CSPGuard (ZMember (ZTuple [ZVar ("n",[],""),ZVar ("value",[],"")]) (ZVar ("\\leq",[],""))) (CActionCommand (CAssign [("value",[],"")] [ZCall (ZVar ("-",[],"")) (ZTuple [ZVar ("value",[],""),ZVar ("n",[],"")])])))))),CParAction "Transfer" (CircusAction (CSPCommAction (ChanComm "pay" [ChanDotExp (ZVar ("i",[],"")),ChanInp "j",ChanInp "n"]) (CSPExtChoice (CSPGuard (ZMember (ZTuple [ZVar ("n",[],""),ZVar ("value",[],"")]) (ZVar (">",[],""))) (CSPCommAction (ChanComm "reject" [ChanOutExp (ZVar ("i",[],""))]) CSPSkip)) (CSPGuard (ZMember (ZTuple [ZVar ("n",[],""),ZVar ("value",[],"")]) (ZVar ("\\leq",[],""))) (CSPCommAction (ChanComm "transfer" [ChanDotExp (ZVar ("i",[],"")),ChanDotExp (ZVar ("j",[],"")),ChanOutExp (ZVar ("n",[],""))]) (CSPCommAction (ChanComm "accept" [ChanOutExp (ZVar ("i",[],""))]) (CSPParAction "Debit" [ZVar ("n",[],"")]))))))),CParAction "Receive" (CircusAction (CSPCommAction (ChanComm "transfer" [ChanInp "j",ChanDotExp (ZVar ("i",[],"")),ChanInp "n"]) (CSPParAction "Credit" [ZVar ("n",[],"")]))),CParAction "Cycle" (CircusAction (CSPSeq (CSPExtChoice (CActionName "Transfer") (CActionName "Receive")) (CActionName "Cycle")))] (CSPSeq (CActionName "Init") (CActionName "Cycle"))))))
ZFreeTypeDef ("UNIVERSE",[],"") []
ZFreeTypeDef ("NAME",[],"") []
ZAbbreviation ("BINDINGS",[],"") (ZCall (ZVar ("\\cup",[],"")) (ZTuple []))
CircChannel [CChanDecl "mget" (ZCross [ZVar ("NAME",[],""),ZVar ("UNIVERSE",[],"")]),CChanDecl "mset" (ZCross [ZVar ("NAME",[],""),ZVar ("UNIVERSE",[],"")])]
CircChannel [CChan "terminate"]
CircChanSet "MEMI" (CChanSet ["mset","mget","terminate"])
CircChannel [CChanDecl "lget" (ZCross [ZVar ("NAME",[],""),ZVar ("UNIVERSE",[],"")]),CChanDecl "lset" (ZCross [ZVar ("NAME",[],""),ZVar ("UNIVERSE",[],"")])]
CircChannel [CChan "lterminate"]
CircChanSet "MEML" (CChanSet ["lset","lget","lterminate"])
