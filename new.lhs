\section{Introduction}

This is a trivial program that prints the first 20 factorials.

\begin{code}
visitComm = mapping_Comm
visitCAction = mapping_CAction
visitCCommand = mapping_CCommand
visitCDecl = mapping_CDecl
visitCGActions = mapping_CGActions
visitComm = mapping_Comm
visitCParameter = mapping_CParameter
visitCProc = mapping_CProc
visitCSExp = mapping_CSExp
visitNSExp = mapping_NSExp
visitParAction = mapping_ParAction
visitPPar = mapping_PPar
visitProcDecl = mapping_ProcDecl
visitProcessDef = mapping_ProcessDef


mapping_CAction (CActionCommand cc) = undefined
mapping_CAction (CActionName zn) = undefined
mapping_CAction (CActionSchemaExpr zse) = undefined
mapping_CAction (CSPChaos) = undefined
mapping_CAction (CSPSkip) = undefined
mapping_CAction (CSPStop) = undefined
mapping_CAction (CSPCommAction co ca) = undefined
mapping_CAction (CSPExtChoice ca cb) = undefined
mapping_CAction (CSPGuard zp ca) = undefined
mapping_CAction (CSPHide ca cse) = undefined
mapping_CAction (CSPIntChoice ca cb) = undefined
mapping_CAction (CSPInterleave ca cb) = undefined
mapping_CAction (CSPNSInter nse1 nse2 ca cb) = undefined
mapping_CAction (CSPNSParal nse1 cse nse2 ca cb) = undefined
mapping_CAction (CSPParAction zn (x:xs)) = undefined
mapping_CAction (CSPParal cse ca cb) = undefined
mapping_CAction (CSPRecursion zn ca) = undefined
mapping_CAction (CSPRepExtChoice (x:xs) ca) = undefined
mapping_CAction (CSPRepIntChoice (x:xs) ca) = undefined
mapping_CAction (CSPRepInterl (x:xs) ca) = undefined
mapping_CAction (CSPRepInterlNS (x:xs) nse ca) = undefined
mapping_CAction (CSPRepParal cse (x:xs) ca) = undefined
mapping_CAction (CSPRepParalNS cse (x:xs) nse ca) = undefined
mapping_CAction (CSPRepSeq (x:xs) ca) = undefined
mapping_CAction (CSPSeq ca cb) = undefined


mapping_CCommand (CAssign (x:xs) (y:ys)) = undefined
mapping_CCommand (CAssumpt (x:xs) zpa zpb) = undefined
mapping_CCommand (CIf cga) = undefined
mapping_CCommand (CommandBrace zp) = undefined
mapping_CCommand (CommandBracket zp) = undefined
mapping_CCommand (CResDecl (x:xs) ca) = undefined
mapping_CCommand (CVarDecl (x:xs) ca) = undefined
mapping_CCommand (CVResDecl (x:xs) ca) = undefined


mapping_CDecl (CChan zn) = undefined
mapping_CDecl (CChanDecl zn ze) = undefined
mapping_CDecl (CGenChanDecl zn zn ze) = undefined

mapping_CGActions (CircGAction zp ca) = undefined
mapping_CGActions (CircThenElse cga1 cga2) = undefined

mapping_Comm (ChanComm zn (x:xs)) = undefined
mapping_Comm (ChanGenComm zn (x:xs) (y:ys)) = undefined

mapping_CParameter (ChanDotExp ze) = undefined
mapping_CParameter (ChanInp zn) = undefined
mapping_CParameter (ChanInpPred zn zp) = undefined
mapping_CParameter (ChanOutExp ze) = undefined

mapping_CProc (CExtChoice cp1 cp2) = undefined
mapping_CProc (CGenProc zn (x:xs)) = undefined
mapping_CProc (CHide cp cse) = undefined
mapping_CProc (CIntChoice cp1 cp2) = undefined
mapping_CProc (CInterleave cp1 cp2) = undefined
mapping_CProc (CircusProc zn) = undefined
mapping_CProc (CParamProc zn (x:xs)) = undefined
mapping_CProc (CParParal cse cp1 cp2) = undefined
mapping_CProc (CRepExtChProc (x:xs) cp) = undefined
mapping_CProc (CRepIntChProc (x:xs) cp) = undefined
mapping_CProc (CRepInterlProc (x:xs) cp) = undefined
mapping_CProc (CRepParalProc cse (x:xs) cp) = undefined
mapping_CProc (CRepSeqProc (x:xs) cp) = undefined
mapping_CProc (CSeq cp1 cp2) = undefined
mapping_CProc (CSimpIndexProc zn (x:xs)) = undefined
mapping_CProc (ProcMain ZPara (x:xs) ca) = undefined
mapping_CProc (ProcStalessMain (x:xs) ca) = undefined

mapping_CSExp (CChanSet (x:xs)) = undefined
mapping_CSExp (ChanSetHide cse1 cse2) = undefined
mapping_CSExp (ChanSetInter cse1 cse2) = undefined
mapping_CSExp (ChanSetUnion cse1 cse2) = undefined
mapping_CSExp (CSEmpty) = undefined
mapping_CSExp (CSExpr zn) = undefined

mapping_NSExp (NSExpEmpty) = undefined
mapping_NSExp (NSExprMult (x:xs)) = undefined
mapping_NSExp (NSExprSngl zn) = undefined
mapping_NSExp (NSHide nse1 nse2) = undefined
mapping_NSExp (NSIntersect nse1 nse2) = undefined
mapping_NSExp (NSUnion nse1 nse2) = undefined

mapping_ParAction (CircusAction ca) = undefined
mapping_ParAction (ParamActionDecl (x:xs) pa) = undefined

mapping_PPar (CNameSet zn nse) = undefined
mapping_PPar (CParAction zn pa) = undefined
mapping_PPar (ProcZPara zp) = undefined

mapping_ProcDecl (CGenProcess zn (x:xs) pd) = undefined
mapping_ProcDecl (CProcess zn pd) = undefined

mapping_ProcessDef (ProcDef cp) = undefined
mapping_ProcessDef (ProcDefIndex (x:xs) pd) = undefined
mapping_ProcessDef (ProcDefSpot (x:xs) pd) = undefined
\end{code}
