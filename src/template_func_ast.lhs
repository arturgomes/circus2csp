\begin{code}
module Substitution
where
import AST

\end{code}
\section{Susbstitution in Circus}
Both Z and Circus AST are found here.

\subsubsection{Z Relations and Functions}
\begin{code}
subst_ZReln :: ZReln -> ZReln
subst_ZReln (ZLessThan) = undefined
subst_ZReln (ZLessThanEq) = undefined
subst_ZReln (ZGreaterThan) = undefined
subst_ZReln (ZGreaterThanEq) = undefined
subst_ZReln (ZSubset) = undefined
subst_ZReln (ZSubsetEq) = undefined
subst_ZReln (ZPartition) = undefined
subst_ZReln (ZPrefix) = undefined
subst_ZReln (ZSuffix) = undefined
subst_ZReln (ZInSeq) = undefined
subst_ZReln (ZNeq) = undefined
subst_ZReln (ZNotin) = undefined
\end{code}
\begin{code}
subst_ZFunc1 :: ZFunc1 -> ZFunc1
subst_ZFunc1 (ZDom) = undefined
subst_ZFunc1 (ZRan) = undefined
subst_ZFunc1 (ZSizeof) = undefined
subst_ZFunc1 (ZBigCup) = undefined
subst_ZFunc1 (ZBigCap) = undefined
subst_ZFunc1 (ZId) = undefined
subst_ZFunc1 (ZRev) = undefined
subst_ZFunc1 (ZHead) = undefined
subst_ZFunc1 (ZLast) = undefined
subst_ZFunc1 (ZTail) = undefined
subst_ZFunc1 (ZFront) = undefined
subst_ZFunc1 (ZSquash) = undefined
subst_ZFunc1 (ZDCat) = undefined
subst_ZFunc1 (ZSucc) = undefined
subst_ZFunc1 (ZNegate) = undefined
subst_ZFunc1 (ZMax) = undefined
subst_ZFunc1 (ZMin) = undefined
subst_ZFunc1 (ZInv) = undefined
subst_ZFunc1 (ZStar) = undefined
subst_ZFunc1 (ZClosure) = undefined
subst_ZFunc1 (ZSum) = undefined
\end{code}
\begin{code}
subst_ZFunc2 :: ZFunc2 -> ZFunc2
subst_ZFunc2 (ZMapsto) = undefined
subst_ZFunc2 (ZUpto) = undefined
subst_ZFunc2 (ZPlus) = undefined
subst_ZFunc2 (ZMinus) = undefined
subst_ZFunc2 (ZTimes) = undefined
subst_ZFunc2 (ZDiv) = undefined
subst_ZFunc2 (ZMod) = undefined
subst_ZFunc2 (ZUnion) = undefined
subst_ZFunc2 (ZInter) = undefined
subst_ZFunc2 (ZSetMinus) = undefined
subst_ZFunc2 (ZComp) = undefined
subst_ZFunc2 (ZCirc) = undefined
subst_ZFunc2 (ZDRes) = undefined
subst_ZFunc2 (ZRRes) = undefined
subst_ZFunc2 (ZNDRes) = undefined
subst_ZFunc2 (ZNRRes) = undefined
subst_ZFunc2 (ZRelImg) = undefined
subst_ZFunc2 (ZOPlus) = undefined
subst_ZFunc2 (ZCat) = undefined
subst_ZFunc2 (ZExtract) = undefined
subst_ZFunc2 (ZFilter) = undefined
subst_ZFunc2 (ZFirst) = undefined
subst_ZFunc2 (ZSecond) = undefined
\end{code}
\begin{code}
subst_ZStrange :: ZStrange -> ZStrange
subst_ZStrange (ZIter) = undefined
subst_ZStrange (ZDisjoint) = undefined
\end{code}


\begin{code}
subst_ZGenFilt :: ZGenFilt -> ZGenFilt
subst_ZGenFilt (Include vZSExpr) = undefined
subst_ZGenFilt (Choose vZVar vZExpr) = undefined
subst_ZGenFilt (Check vZPred) = undefined
subst_ZGenFilt (Evaluate vZVar v1ZExpr v2ZExpr) = undefined

\end{code}

\subsubsection{Z Expressions}
\begin{code}
subst_ZExpr :: ZExpr -> ZExpr
subst_ZExpr (ZVar v2ZVar) = undefined
subst_ZExpr (ZInt v2ZInt) = undefined
subst_ZExpr (ZGiven vGivenValue) = undefined
subst_ZExpr (ZFree0 vZVar) = undefined
subst_ZExpr (ZFree1 vZVar vZExpr) = undefined
subst_ZExpr (ZTuple vZExpr_lst) = undefined
subst_ZExpr (ZBinding vZVar_ZExpr_pair_lst) = undefined
subst_ZExpr (ZSetDisplay vZExpr_lst) = undefined
subst_ZExpr (ZSeqDisplay vZExpr_lst) = undefined
subst_ZExpr (ZFSet v2ZFSet) = undefined
subst_ZExpr (ZIntSet vmaybe_ZInt vmaybe_ZInt) = undefined
subst_ZExpr (ZGenerator v1ZReln v2ZExpr) = undefined
subst_ZExpr (ZCross vZExpr_lst) = undefined
subst_ZExpr (ZFreeType v1ZZVar vZBranch_lst) = undefined
subst_ZExpr e@(ZPowerSet{baseset=a,
    is_non_empty=b,
    is_finite=v})
subst_ZExpr e@(ZFuncSet{ domseta,
    ranset=b,
    is_function=c,
    is_total=d,
    is_onto=e,
    is_one2one=f,
    is_sequence=g,
    is_non_empty=h,
    is_finite=i})
subst_ZExpr (ZSetComp vZGenFilt_lst vmaybe_ZExpr) = undefined
subst_ZExpr (ZLambda vZGenFilt_lst vZExpr) = undefined
subst_ZExpr (ZESchema vZSExpr) = undefined
subst_ZExpr (ZGivenSet vGivenSet) = undefined
subst_ZExpr (ZUniverse) = undefined
subst_ZExpr (ZCall v1ZExpr v2ZExpr) = undefined
subst_ZExpr (ZReln v2ZReln) = undefined
subst_ZExpr (ZFunc1 v2ZFunc1) = undefined
subst_ZExpr (ZFunc2 v2ZFunc2) = undefined
subst_ZExpr (ZStrange v2ZStrange) = undefined
subst_ZExpr (ZMu vZGenFilt_lst vmaybe_ZExpr) = undefined
subst_ZExpr (ZELet vZVar_ZExpr_pair_lst vZExpr) = undefined
subst_ZExpr (ZIf_Then_Else vZPred v1ZExpr v2ZExpr) = undefined
subst_ZExpr (ZSelect vZExpr vZVar) = undefined
subst_ZExpr (ZTheta vZSExpr) = undefined
\end{code}

\subsubsection{Z Predicates}
\begin{code}
subst_ZPred :: ZPred -> ZPred
subst_ZPred (ZFalse{reason=vZPred_lst}) = undefined
subst_ZPred (ZTrue{reason=vZPred_lst}) = undefined
subst_ZPred (ZAnd v1ZPred v2ZPred) = undefined
subst_ZPred (ZOr v1ZPred v2ZPred) = undefined
subst_ZPred (ZImplies v1ZPred v2ZPred) = undefined
subst_ZPred (ZIff v1ZPred v2ZPred) = undefined
subst_ZPred (ZNot vZPred) = undefined
subst_ZPred (ZExists vZGenFilt_lst vZPred) = undefined
subst_ZPred (ZExists_1 vZGenFilt_lst vZPred) = undefined
subst_ZPred (ZForall vZGenFilt_lst vZPred) = undefined
subst_ZPred (ZPLet vZVar_ZExpr_pair_lst vZPred) = undefined
subst_ZPred (ZEqual v1ZExpr v2ZExpr) = undefined
subst_ZPred (ZMember v1ZExpr v2ZExpr) = undefined
subst_ZPred (ZPre vZSExpr) = undefined
subst_ZPred (ZPSchema vZSExpr) = undefined

\end{code}

\subsubsection{Z Schemas}
\begin{code}
subst_ZSExpr :: ZSExpr -> ZSExpr
subst_ZSExpr (ZSchema vZGenFilt_lst) = undefined
subst_ZSExpr (ZSRef vZSName vZDecor_lst vZReplace_lst) = undefined
subst_ZSExpr (ZS1 vZS1 vZSExpr) = undefined
subst_ZSExpr (ZS2 vZS2 v1ZSExpr v2ZSExpr) = undefined
subst_ZSExpr (ZSHide vZSExpr vZVar_lst) = undefined
subst_ZSExpr (ZSExists vZGenFilt_lst vZSExpr) = undefined
subst_ZSExpr (ZSExists_1 vZGenFilt_lst vZSExpr) = undefined
subst_ZSExpr (ZSForall vZGenFilt_lst vZSExpr) = undefined
\end{code}
\begin{code}
subst_ZReplace :: ZReplace -> ZReplace
subst_ZReplace (ZRename v1ZVar v2ZVar) = undefined
subst_ZReplace (ZAssign vZVar vZExpr) = undefined
\end{code}
\begin{code}
subst_ZSName :: ZSName -> ZSName
subst_ZSName (ZSPlain vString) = undefined
subst_ZSName (ZSDelta vString) = undefined
subst_ZSName (ZSXi vString) = undefined
\end{code}
\begin{code}
subst_ZS1 :: ZS1 -> ZS1
subst_ZS1 (ZSPre) = undefined
subst_ZS1 (ZSNot) = undefined
\end{code}
\begin{code}
subst_ZS2 :: ZS2 -> ZS2
subst_ZS2 (ZSAnd) = undefined
subst_ZS2 (ZSOr) = undefined
subst_ZS2 (ZSImplies) = undefined
subst_ZS2 (ZSIff) = undefined
subst_ZS2 (ZSProject) = undefined
subst_ZS2 (ZSSemi) = undefined
subst_ZS2 (ZSPipe) = undefined
\end{code}

\subsubsection{Z Paragraphs}
\begin{code}
subst_ZPara :: ZPara -> ZPara
subst_ZPara (ZGivenSetDecl vGivenSet) = undefined
subst_ZPara (ZSchemaDef vZSName vZSExpr) = undefined
subst_ZPara (ZAbbreviation vZVar vZExpr) = undefined
subst_ZPara (ZFreeTypeDef vZVar vZBranch_lst) = undefined
subst_ZPara (ZPredicate vZPred) = undefined
subst_ZPara (ZAxDef vZGenFilt_lst) = undefined
subst_ZPara (ZGenDef vZGenFilt_lst) = undefined
subst_ZPara (CircChannel vCDecl_lst) = undefined
subst_ZPara (CircChanSet vZName vCSExp) = undefined
subst_ZPara (Process vProcDecl) = undefined
subst_ZPara _ = undefined
\end{code}
\begin{code}
subst_ZBranch :: ZBranch -> ZBranch
subst_ZBranch (ZBranch0 vZVar) = undefined
subst_ZBranch (ZBranch1 vZVar vZExpr) = undefined

\end{code}


\section{Circus Abstract Syntax}

\subsubsection{Circus Channel Expression}
\begin{code}
subst_CSExp :: CSExp -> CSExp
subst_CSExp (CSExpr vZName) = undefined
subst_CSExp (CSEmpty) = undefined
subst_CSExp (CChanSet vZName_lst) = undefined
subst_CSExp (ChanSetUnion v1CSExp v2CSExp) = undefined
subst_CSExp (ChanSetInter v1CSExp v2CSExp) = undefined
subst_CSExp (ChanSetDiff v1CSExp v2CSExp) = undefined
\end{code}

\subsubsection{Circus Process}
\begin{code}
subst_ProcDecl :: ProcDecl -> ProcDecl
subst_ProcDecl (CProcess vZName vProcessDef) = undefined
subst_ProcDecl (CParamProcess vZName vZName_lst vProcessDef) = undefined
subst_ProcDecl (CGenProcess vZName vZName_lst vProcessDef) = undefined
\end{code}
\begin{code}
subst_ProcessDef :: ProcessDef -> ProcessDef
subst_ProcessDef (ProcDefSpot vZGenFilt_lst vProcessDef) = undefined
subst_ProcDecl (ProcDefIndex vZGenFilt_lst vProcessDef) = undefined
subst_ProcDecl (ProcDef vCProc) = undefined
\end{code}
\begin{code}
subst_CProc :: CProc -> CProc
subst_CProc (CRepSeqProc vZGenFilt_lst vCProc) = undefined
subst_CProc (CRepExtChProc vZGenFilt_lst vCProc) = undefined
subst_CProc (CRepIntChProc vZGenFilt_lst vCProc) = undefined
subst_CProc (CRepParalProc vCSExp vZGenFilt_lst vCProc) = undefined
subst_CProc (CRepInterlProc vZGenFilt_lst vCProc) = undefined
subst_CProc (CHide vCProc vCSExp) = undefined
subst_CProc (CExtChoice v1CProc v2CProc) = undefined
subst_CProc (CIntChoice v1CProc v2CProc) = undefined
subst_CProc (CParParal vCSExp v1CProc v2CProc) = undefined
subst_CProc (CInterleave v1CProc v2CProc) = undefined
subst_CProc (CGenProc vZName vZExpr_lst) = undefined
subst_CProc (CParamProc vZName vZExpr_lst) = undefined
subst_CProc (CProcRename vZName vComm_lst vComm_lst) = undefined
subst_CProc (CSeq v1CProc v2CProc) = undefined
subst_CProc (CSimpIndexProc vZName vZExpr_lst) = undefined
subst_CProc (CircusProc vZName) = undefined
subst_CProc (ProcMain ZPara vPPar_lst vCAction) = undefined
subst_CProc (ProcStalessMain vPPar_lst vCAction) = undefined
\end{code}

\subsubsection{Circus Name-Sets}

\begin{code}
subst_NSExp :: NSExp -> NSExp
subst_NSExp (NSExpEmpty) = undefined
subst_NSExp (NSExprMult vZName_lst) = undefined
subst_NSExp (NSExprSngl vZName) = undefined
subst_NSExp (NSExprParam vZName vZExpr_lst) = undefined
subst_NSExp (NSUnion v1NSExp v2NSExp) = undefined
subst_NSExp (NSIntersect v1NSExp v2NSExp) = undefined
subst_NSExp (NSHide v1NSExp v2NSExp) = undefined
subst_NSExp (NSBigUnion vZExpr) = undefined
\end{code}

\subsubsection{Circus Actions}
\begin{code}
subst_PPar :: PPar -> PPar
subst_PPar (ProcZPara vZPara) = undefined
subst_PPar (CParAction vZName vParAction) = undefined
subst_PPar (CNameSet vZName vNSExp) = undefined
\end{code}
\begin{code}
subst_ParAction :: ParAction -> ParAction
subst_ParAction (CircusAction vCAction) = undefined
subst_ParAction (ParamActionDecl vZGenFilt_lst vParAction) = undefined
\end{code}
\begin{code}
subst_CAction :: CAction -> CAction
subst_CAction (CActionSchemaExpr vZSExpr) = undefined
subst_CAction (CActionCommand vCCommand) = undefined
subst_CAction (CActionName vZName) = undefined
subst_CAction (CSPSkip ) = undefined
subst_CAction (CSPStop) = undefined
subst_CAction (CSPChaos) = undefined
subst_CAction (CSPCommAction vComm vCAction) = undefined
subst_CAction (CSPGuard vZPred vCAction) = undefined
subst_CAction (CSPSeq v1CAction v2CAction) = undefined
subst_CAction (CSPExtChoice v1CAction v2CAction) = undefined
subst_CAction (CSPIntChoice v1CAction v2CAction) = undefined
subst_CAction (CSPNSParal v1NSExp vCSExp v2NSExp v1CAction v2CAction) = undefined
subst_CAction (CSPParal vCSExp v1CAction v2CAction) = undefined
subst_CAction (CSPNSInter v1NSExp v2NSExp v1CAction v2CAction) = undefined
subst_CAction (CSPInterleave v1CAction v2CAction) = undefined
subst_CAction (CSPHide vCAction vCSExp) = undefined
subst_CAction (CSPParAction vZName vZExpr_lst) = undefined
subst_CAction (CSPRenAction vZName vCReplace) = undefined
subst_CAction (CSPRecursion vZName vCAction) = undefined
subst_CAction (CSPUnfAction vZName vCAction) = undefined
subst_CAction (CSPUnParAction vZGenFilt_lst vCAction vZName) = undefined
subst_CAction (CSPRepSeq vZGenFilt_lst vCAction) = undefined
subst_CAction (CSPRepExtChoice vZGenFilt_lst vCAction) = undefined
subst_CAction (CSPRepIntChoice vZGenFilt_lst vCAction) = undefined
subst_CAction (CSPRepParalNS CSExp vZGenFilt_lst vNSExp vCAction) = undefined
subst_CAction (CSPRepParal CSExp vZGenFilt_lst vCAction) = undefined
subst_CAction (CSPRepInterlNS vZGenFilt_lst vNSExp vCAction) = undefined
subst_CAction (CSPRepInterl vZGenFilt_lst vCAction) = undefined
\end{code}

\subsubsection{Circus Communication}

\begin{code}
subst_Comm :: Comm -> Comm
subst_Comm (ChanComm vZName vCParameter_lst) = undefined
subst_Comm (ChanGenComm vZName vZExpr_lst vCParameter_lst) = undefined
\end{code}
\begin{code}

subst_CParameter :: CParameter -> CParameter
subst_CParameter (ChanInp vZName) = undefined
subst_CParameter (ChanInpPred vZName ZPred) = undefined
subst_CParameter (ChanOutExp ZExpr) = undefined
subst_CParameter (ChanDotExp ZExpr) = undefined
\end{code}

\subsubsection{Circus Commands}

\begin{code}
subst_CCommand :: CCommand -> CCommand
subst_CCommand (CAssign vZVar_lst vZExpr_lst) = undefined
subst_CCommand (CIf vCGActions) = undefined
subst_CCommand (CVarDecl vZGenFilt_lst vCAction) = undefined
subst_CCommand (CAssumpt vZName_lst v1ZPred v2ZPred) = undefined
subst_CCommand (CAssumpt1 vZName_lst vZPred) = undefined
subst_CCommand (CPrefix v1ZPred v2ZPred) = undefined
subst_CCommand (CPrefix1 ZPred) = undefined
subst_CCommand (CommandBrace ZPred) = undefined
subst_CCommand (CommandBracket ZPred) = undefined
subst_CCommand (CValDecl vZGenFilt_lst vCAction) = undefined
subst_CCommand (CResDecl vZGenFilt_lst vCAction) = undefined
subst_CCommand (CVResDecl vZGenFilt_lst vCAction) = undefined
\end{code}
\begin{code}
subst_CGActions :: CGActions  -> CGActions
subst_CGActions (CircGAction ZPred vCAction) = undefined
subst_CGActions (CircThenElse v1CGActions v2CGActions) = undefined
subst_CGActions (CircElse ParAction) = undefined
\end{code}
\begin{code}
subst_CReplace :: CReplace -> CReplace
subst_CReplace (CRename vZVar_lst vZVar_lst) = undefined
subst_CReplace (CRenameAssign vZVar_lst vZVar_lst) = undefined
\end{code}
