\begin{code}
module Substitution
where
import AST
\end{code}

\section{Abstract Syntax Trees}
Both Z and Circus AST are found here.

\subsubsection{Z Relations and Functions}
\begin{code}
sub_ZReln :: ZReln -> ZReln
sub_ZReln (ZLessThan) = (ZLessThan)
sub_ZReln (ZLessThanEq) = (ZLessThanEq)
sub_ZReln (ZGreaterThan) = (ZGreaterThan)
sub_ZReln (ZGreaterThanEq) = (ZGreaterThanEq)
sub_ZReln (ZSubset) = (ZSubset)
sub_ZReln (ZSubsetEq) = (ZSubsetEq)
sub_ZReln (ZPartition) = (ZPartition)
sub_ZReln (ZPrefix) = (ZPrefix)
sub_ZReln (ZSuffix) = (ZSuffix)
sub_ZReln (ZInSeq) = (ZInSeq)
sub_ZReln (ZNeq) = (ZNeq)
sub_ZReln (ZNotin) = (ZNotin)
\end{code}
\begin{code}
sub_ZFunc1 :: ZFunc1 -> ZFunc1
sub_ZFunc1 (ZDom) = (ZDom)
sub_ZFunc1 (ZRan) = (ZRan)
sub_ZFunc1 (ZSizeof) = (ZSizeof)
sub_ZFunc1 (ZBigCup) = (ZBigCup)
sub_ZFunc1 (ZBigCap) = (ZBigCap)
sub_ZFunc1 (ZId) = (ZId)
sub_ZFunc1 (ZRev) = (ZRev)
sub_ZFunc1 (ZHead) = (ZHead)
sub_ZFunc1 (ZLast) = (ZLast)
sub_ZFunc1 (ZTail) = (ZTail)
sub_ZFunc1 (ZFront) = (ZFront)
sub_ZFunc1 (ZSquash) = (ZSquash)
sub_ZFunc1 (ZDCat) = (ZDCat)
sub_ZFunc1 (ZSucc) = (ZSucc)
sub_ZFunc1 (ZNegate) = (ZNegate)
sub_ZFunc1 (ZMax) = (ZMax)
sub_ZFunc1 (ZMin) = (ZMin)
sub_ZFunc1 (ZInv) = (ZInv)
sub_ZFunc1 (ZStar) = (ZStar)
sub_ZFunc1 (ZClosure) = (ZClosure)
sub_ZFunc1 (ZSum) = (ZSum)
\end{code}
\begin{code}
sub_ZFunc2 :: ZFunc2 -> ZFunc2
sub_ZFunc2 (ZMapsto) = (ZMapsto)
sub_ZFunc2 (ZUpto) = (ZUpto)
sub_ZFunc2 (ZPlus) = (ZPlus)
sub_ZFunc2 (ZMinus) = (ZMinus)
sub_ZFunc2 (ZTimes) = (ZTimes)
sub_ZFunc2 (ZDiv) = (ZDiv)
sub_ZFunc2 (ZMod) = (ZMod)
sub_ZFunc2 (ZUnion) = (ZUnion)
sub_ZFunc2 (ZInter) = (ZInter)
sub_ZFunc2 (ZSetMinus) = (ZSetMinus)
sub_ZFunc2 (ZComp) = (ZComp)
sub_ZFunc2 (ZCirc) = (ZCirc)
sub_ZFunc2 (ZDRes) = (ZDRes)
sub_ZFunc2 (ZRRes) = (ZRRes)
sub_ZFunc2 (ZNDRes) = (ZNDRes)
sub_ZFunc2 (ZNRRes) = (ZNRRes)
sub_ZFunc2 (ZRelImg) = (ZRelImg)
sub_ZFunc2 (ZOPlus) = (ZOPlus)
sub_ZFunc2 (ZCat) = (ZCat)
sub_ZFunc2 (ZExtract) = (ZExtract)
sub_ZFunc2 (ZFilter) = (ZFilter)
sub_ZFunc2 (ZFirst) = (ZFirst)
sub_ZFunc2 (ZSecond) = (ZSecond)
\end{code}
\begin{code}
sub_ZStrange :: ZStrange -> ZStrange
sub_ZStrange (ZIter) = (ZIter)
sub_ZStrange (ZDisjoint) = (ZDisjoint)
\end{code}


\begin{code}
sub_ZGenFilt :: ZGenFilt -> ZGenFilt
sub_ZGenFilt (Include vZSExpr) = (Include vZSExpr)
sub_ZGenFilt (Choose vZVar vZExpr) = (Choose vZVar vZExpr)
sub_ZGenFilt (Check vZPred) = (Check vZPred)
sub_ZGenFilt (Evaluate vZVar v1ZExpr v2ZExpr) = (Evaluate vZVar v1ZExpr v2ZExpr)

\end{code}

\subsubsection{Z Expressions}
\begin{code}
sub_ZExpr :: ZExpr -> ZExpr
sub_ZExpr (ZVar v2ZVar) = (ZVar v2ZVar)
sub_ZExpr (ZInt v2ZInt) = (ZInt v2ZInt)
sub_ZExpr (ZGiven vGivenValue) = (ZGiven vGivenValue)
sub_ZExpr (ZFree0 vZVar) = (ZFree0 vZVar)
sub_ZExpr (ZFree1 vZVar vZExpr) = (ZFree1 vZVar vZExpr)
sub_ZExpr (ZTuple vZExpr_lst) = (ZTuple vZExpr_lst)
sub_ZExpr (ZBinding vZVar_ZExpr_pair_lst) = (ZBinding vZVar_ZExpr_pair_lst)
sub_ZExpr (ZSetDisplay vZExpr_lst) = (ZSetDisplay vZExpr_lst)
sub_ZExpr (ZSeqDisplay vZExpr_lst) = (ZSeqDisplay vZExpr_lst)
sub_ZExpr (ZFSet v2ZFSet) = (ZFSet v2ZFSet)
sub_ZExpr (ZIntSet v1maybe_ZInt v2maybe_ZInt) = (ZIntSet v1maybe_ZInt v2maybe_ZInt)
sub_ZExpr (ZGenerator vZReln vZExpr) = (ZGenerator vZReln vZExpr)
sub_ZExpr (ZCross vZExpr_lst) = (ZCross vZExpr_lst)
sub_ZExpr (ZFreeType vZVar vZBranch_lst) = (ZFreeType vZVar vZBranch_lst)
sub_ZExpr (ZPowerSet{baseset=vZExpr, is_non_empty=v1Bool, is_finite=v2Bool}) 
    = (ZPowerSet{baseset=vZExpr, is_non_empty=v1Bool, is_finite=v2Bool})
sub_ZExpr (ZFuncSet{ domset=vZExpr,
    ranset=v1ZExpr,
    is_function=v1Bool,
    is_total=v2Bool,
    is_onto=v3Bool,
    is_one2one=v4Bool,
    is_sequence=v5Bool,
    is_non_empty=v6Bool,
    is_finite=v7Bool}) = (ZFuncSet{ domset=vZExpr,
                            ranset=v1ZExpr,
                            is_function=v1Bool,
                            is_total=v2Bool,
                            is_onto=v3Bool,
                            is_one2one=v4Bool,
                            is_sequence=v5Bool,
                            is_non_empty=v6Bool,
                            is_finite=v7Bool})
sub_ZExpr (ZSetComp vZGenFilt_lst vmaybe_ZExpr) = (ZSetComp vZGenFilt_lst vmaybe_ZExpr)
sub_ZExpr (ZLambda vZGenFilt_lst vZExpr) = (ZLambda vZGenFilt_lst vZExpr)
sub_ZExpr (ZESchema vZSExpr) = (ZESchema vZSExpr)
sub_ZExpr (ZGivenSet vGivenSet) = (ZGivenSet vGivenSet)
sub_ZExpr (ZUniverse) = (ZUniverse)
sub_ZExpr (ZCall v1ZExpr v2ZExpr) = (ZCall v1ZExpr v2ZExpr)
sub_ZExpr (ZReln v2ZReln) = (ZReln v2ZReln)
sub_ZExpr (ZFunc1 v2ZFunc1) = (ZFunc1 v2ZFunc1)
sub_ZExpr (ZFunc2 v2ZFunc2) = (ZFunc2 v2ZFunc2)
sub_ZExpr (ZStrange v2ZStrange) = (ZStrange v2ZStrange)
sub_ZExpr (ZMu vZGenFilt_lst vmaybe_ZExpr) = (ZMu vZGenFilt_lst vmaybe_ZExpr)
sub_ZExpr (ZELet vZVar_ZExpr_pair_lst vZExpr) = (ZELet vZVar_ZExpr_pair_lst vZExpr)
sub_ZExpr (ZIf_Then_Else vZPred v1ZExpr v2ZExpr) = (ZIf_Then_Else vZPred v1ZExpr v2ZExpr)
sub_ZExpr (ZSelect vZExpr vZVar) = (ZSelect vZExpr vZVar)
sub_ZExpr (ZTheta vZSExpr) = (ZTheta vZSExpr)
\end{code}

\subsubsection{Z Predicates}
\begin{code}
sub_ZPred :: ZPred -> ZPred
sub_ZPred (ZFalse{reason=vZPred_lst}) = (ZFalse{reason=vZPred_lst})
sub_ZPred (ZTrue{reason=vZPred_lst}) = (ZTrue{reason=vZPred_lst})
sub_ZPred (ZAnd v1ZPred v2ZPred) = (ZAnd v1ZPred v2ZPred)
sub_ZPred (ZOr v1ZPred v2ZPred) = (ZOr v1ZPred v2ZPred)
sub_ZPred (ZImplies v1ZPred v2ZPred) = (ZImplies v1ZPred v2ZPred)
sub_ZPred (ZIff v1ZPred v2ZPred) = (ZIff v1ZPred v2ZPred)
sub_ZPred (ZNot vZPred) = (ZNot vZPred)
sub_ZPred (ZExists vZGenFilt_lst vZPred) = (ZExists vZGenFilt_lst vZPred)
sub_ZPred (ZExists_1 vZGenFilt_lst vZPred) = (ZExists_1 vZGenFilt_lst vZPred)
sub_ZPred (ZForall vZGenFilt_lst vZPred) = (ZForall vZGenFilt_lst vZPred)
sub_ZPred (ZPLet vZVar_ZExpr_pair_lst vZPred) = (ZPLet vZVar_ZExpr_pair_lst vZPred)
sub_ZPred (ZEqual v1ZExpr v2ZExpr) = (ZEqual v1ZExpr v2ZExpr)
sub_ZPred (ZMember v1ZExpr v2ZExpr) = (ZMember v1ZExpr v2ZExpr)
sub_ZPred (ZPre vZSExpr) = (ZPre vZSExpr)
sub_ZPred (ZPSchema vZSExpr) = (ZPSchema vZSExpr)

\end{code}
\begin{code}
is_var_bound_ZPred :: ZVar -> ZPred -> Bool
is_var_bound_ZPred v (ZFalse{reason=vZPred_lst}) = False
is_var_bound_ZPred v (ZTrue{reason=vZPred_lst}) = False
is_var_bound_ZPred v (ZAnd v1ZPred v2ZPred) =  (is_var_bound_ZPred v v1ZPred) || (is_var_bound_ZPred v v2ZPred)
is_var_bound_ZPred v (ZOr v1ZPred v2ZPred) = (is_var_bound_ZPred v v1ZPred) || (is_var_bound_ZPred v v2ZPred)
is_var_bound_ZPred v (ZImplies v1ZPred v2ZPred) = (is_var_bound_ZPred v v1ZPred)|| (is_var_bound_ZPred v v2ZPred)
is_var_bound_ZPred v (ZIff v1ZPred v2ZPred) = (is_var_bound_ZPred v v1ZPred) || (is_var_bound_ZPred v v2ZPred)
is_var_bound_ZPred v (ZNot vZPred) =  (is_var_bound_ZPred v vZPred)
is_var_bound_ZPred v (ZExists vZGenFilt_lst vZPred) = (ZExists vZGenFilt_lst vZPred)
is_var_bound_ZPred v (ZExists_1 vZGenFilt_lst vZPred) = (ZExists_1 vZGenFilt_lst vZPred)
is_var_bound_ZPred v (ZForall vZGenFilt_lst vZPred) = (ZForall vZGenFilt_lst vZPred)
is_var_bound_ZPred v (ZPLet vZVar_ZExpr_pair_lst vZPred) = (ZPLet vZVar_ZExpr_pair_lst vZPred)
is_var_bound_ZPred v (ZEqual v1ZExpr v2ZExpr) = (is_var_bound_ZPred v v1ZPred) || (is_var_bound_ZPred v v2ZPred)
is_var_bound_ZPred v (ZMember v1ZExpr v2ZExpr) = (is_var_bound_ZPred v v1ZPred) || (is_var_bound_ZPred v v2ZPred)
is_var_bound_ZPred v (ZPre vZSExpr) = (ZPre vZSExpr)
is_var_bound_ZPred v (ZPSchema vZSExpr) = (ZPSchema vZSExpr)
\end{code}
\begin{code}
is_var_bound_ZGenFilt :: ZVar -> ZGenFilt -> Bool
is_var_bound_ZGenFilt v (Include e) =is_var_bound_ZSExpr v e
is_var_bound_ZGenFilt v (Choose x e) if v == x then True else False
is_var_bound_ZGenFilt v (Check vZPred) = is_var_bound_ZPred v vZPred
is_var_bound_ZGenFilt v _ = False
  -- | Evaluate ZVar ZExpr ZExpr -- Yet to be defined (Artur, 22/02/2017)
\end{code}
\begin{code}
is_var_bound_ZSExpr v (ZSchema vZGenFilt_lst) 
    = member True (map is_var_bound_ZGenFilt vZGenFilt_lst)
is_var_bound_ZSExpr v (ZS1 v vZSExpr) = (is_var_bound_ZSExpr vZSExpr)
is_var_bound_ZSExpr v (ZS2 v v1ZSExpr v2ZSExpr) 
  = (is_var_bound_ZSExpr v1ZSExpr) || (is_var_bound_ZSExpr v2ZSExpr)
is_var_bound_ZSExpr v (ZSHide vZSExpr vZVar_lst) 
  = (is_var_bound_ZSExpr vZSExpr) 
is_var_bound_ZSExpr v (ZSExists vZGenFilt_lst vZSExpr) 
  = if (member True (map is_var_bound_ZGenFilt v vZGenFilt_lst)) then True else (is_var_bound_ZSExpr v vZSExpr)
is_var_bound_ZSExpr v (ZSExists_1 vZGenFilt_lst vZSExpr) 
  = if (member True (map is_var_bound_ZGenFilt v vZGenFilt_lst)) then True else (is_var_bound_ZSExpr v vZSExpr)
is_var_bound_ZSExpr v (ZSForall vZGenFilt_lst vZSExpr) 
  = if (member True (map is_var_bound_ZGenFilt v vZGenFilt_lst)) then True else (is_var_bound_ZSExpr v vZSExpr)
is_var_bound_ZSExpr v _ = False 
-- is_var_bound_ZSExpr v (ZSRef ZSName [ZDecor] [ZReplace]) = 
\end{code}

\subsubsection{Z Schemas}
\begin{code}
sub_ZSExpr :: ZSExpr -> ZSExpr
sub_ZSExpr (ZSchema vZGenFilt_lst) = (ZSchema vZGenFilt_lst)
sub_ZSExpr (ZSRef vZSName vZDecor_lst vZReplace_lst) = (ZSRef vZSName vZDecor_lst vZReplace_lst)
sub_ZSExpr (ZS1 vZS1 vZSExpr) = (ZS1 vZS1 vZSExpr)
sub_ZSExpr (ZS2 vZS2 v1ZSExpr v2ZSExpr) = (ZS2 vZS2 v1ZSExpr v2ZSExpr)
sub_ZSExpr (ZSHide vZSExpr vZVar_lst) = (ZSHide vZSExpr vZVar_lst)
sub_ZSExpr (ZSExists vZGenFilt_lst vZSExpr) = (ZSExists vZGenFilt_lst vZSExpr)
sub_ZSExpr (ZSExists_1 vZGenFilt_lst vZSExpr) = (ZSExists_1 vZGenFilt_lst vZSExpr)
sub_ZSExpr (ZSForall vZGenFilt_lst vZSExpr) = (ZSForall vZGenFilt_lst vZSExpr)
\end{code}
\begin{code}
sub_ZReplace :: ZReplace -> ZReplace
sub_ZReplace (ZRename v1ZVar v2ZVar) = (ZRename v1ZVar v2ZVar)
sub_ZReplace (ZAssign vZVar vZExpr) = (ZAssign vZVar vZExpr)
\end{code}
\begin{code}
sub_ZSName :: ZSName -> ZSName
sub_ZSName (ZSPlain vString) = (ZSPlain vString)
sub_ZSName (ZSDelta vString) = (ZSDelta vString)
sub_ZSName (ZSXi vString) = (ZSXi vString)
\end{code}
\begin{code}
sub_ZS1 :: ZS1 -> ZS1
sub_ZS1 (ZSPre) = (ZSPre)
sub_ZS1 (ZSNot) = (ZSNot)
\end{code}
\begin{code}
sub_ZS2 :: ZS2 -> ZS2
sub_ZS2 (ZSAnd) = (ZSAnd)
sub_ZS2 (ZSOr) = (ZSOr)
sub_ZS2 (ZSImplies) = (ZSImplies)
sub_ZS2 (ZSIff) = (ZSIff)
sub_ZS2 (ZSProject) = (ZSProject)
sub_ZS2 (ZSSemi) = (ZSSemi)
sub_ZS2 (ZSPipe) = (ZSPipe)
\end{code}

\subsubsection{Z Paragraphs}
\begin{code}
sub_ZPara :: ZPara -> ZPara
sub_ZPara (ZSchemaDef vZSName vZSExpr) = (ZSchemaDef vZSName vZSExpr)
sub_ZPara (Process vProcDecl) = (Process vProcDecl)
sub_ZPara x = x
\end{code}
\begin{code}
sub_ZBranch :: ZBranch -> ZBranch
sub_ZBranch (ZBranch0 vZVar) = (ZBranch0 vZVar)
sub_ZBranch (ZBranch1 vZVar vZExpr) = (ZBranch1 vZVar vZExpr)

\end{code}


\section{Circus Abstract Syntax}

\subsubsection{Circus Channel Expression}
\begin{code}
sub_CSExp :: CSExp -> CSExp
sub_CSExp (CSExpr vZName) = (CSExpr vZName)
sub_CSExp (CSEmpty) = (CSEmpty)
sub_CSExp (CChanSet vZName_lst) = (CChanSet vZName_lst)
sub_CSExp (ChanSetUnion v1CSExp v2CSExp) = (ChanSetUnion v1CSExp v2CSExp)
sub_CSExp (ChanSetInter v1CSExp v2CSExp) = (ChanSetInter v1CSExp v2CSExp)
sub_CSExp (ChanSetDiff v1CSExp v2CSExp) = (ChanSetDiff v1CSExp v2CSExp)
\end{code}

\subsubsection{Circus Process}
\begin{code}
sub_ProcDecl :: ProcDecl -> ProcDecl
sub_ProcDecl (CProcess vZName vProcessDef) = (CProcess vZName vProcessDef)
sub_ProcDecl (CParamProcess vZName vZName_lst vProcessDef) = (CParamProcess vZName vZName_lst vProcessDef)
sub_ProcDecl (CGenProcess vZName vZName_lst vProcessDef) = (CGenProcess vZName vZName_lst vProcessDef)
\end{code}
\begin{code}
sub_ProcessDef :: ProcessDef -> ProcessDef
sub_ProcessDef (ProcDefSpot vZGenFilt_lst vProcessDef) = (ProcDefSpot vZGenFilt_lst vProcessDef)
sub_ProcessDef (ProcDefIndex vZGenFilt_lst vProcessDef) = (ProcDefIndex vZGenFilt_lst vProcessDef)
sub_ProcessDef (ProcDef vCProc) = (ProcDef vCProc)
\end{code}
\begin{code}
sub_CProc :: CProc -> CProc
sub_CProc (CRepSeqProc vZGenFilt_lst vCProc) = (CRepSeqProc vZGenFilt_lst vCProc)
sub_CProc (CRepExtChProc vZGenFilt_lst vCProc) = (CRepExtChProc vZGenFilt_lst vCProc)
sub_CProc (CRepIntChProc vZGenFilt_lst vCProc) = (CRepIntChProc vZGenFilt_lst vCProc)
sub_CProc (CRepParalProc vCSExp vZGenFilt_lst vCProc) = (CRepParalProc vCSExp vZGenFilt_lst vCProc)
sub_CProc (CRepInterlProc vZGenFilt_lst vCProc) = (CRepInterlProc vZGenFilt_lst vCProc)
sub_CProc (CHide vCProc vCSExp) = (CHide vCProc vCSExp)
sub_CProc (CExtChoice v1CProc v2CProc) = (CExtChoice v1CProc v2CProc)
sub_CProc (CIntChoice v1CProc v2CProc) = (CIntChoice v1CProc v2CProc)
sub_CProc (CParParal vCSExp v1CProc v2CProc) = (CParParal vCSExp v1CProc v2CProc)
sub_CProc (CInterleave v1CProc v2CProc) = (CInterleave v1CProc v2CProc)
sub_CProc (CGenProc vZName vZExpr_lst) = (CGenProc vZName vZExpr_lst)
sub_CProc (CParamProc vZName vZExpr_lst) = (CParamProc vZName vZExpr_lst)
sub_CProc (CProcRename vZName v1Comm_lst v2Comm_lst) = (CProcRename vZName v1Comm_lst v2Comm_lst)
sub_CProc (CSeq v1CProc v2CProc) = (CSeq v1CProc v2CProc)
sub_CProc (CSimpIndexProc vZName vZExpr_lst) = (CSimpIndexProc vZName vZExpr_lst)
sub_CProc (CircusProc vZName) = (CircusProc vZName)
sub_CProc (ProcMain zZPara vPPar_lst vCAction) = (ProcMain zZPara vPPar_lst vCAction)
sub_CProc (ProcStalessMain vPPar_lst vCAction) = (ProcStalessMain vPPar_lst vCAction)
\end{code}

\subsubsection{Circus Name-Sets}

\begin{code}
sub_NSExp :: NSExp -> NSExp
sub_NSExp (NSExpEmpty) = (NSExpEmpty)
sub_NSExp (NSExprMult vZName_lst) = (NSExprMult vZName_lst)
sub_NSExp (NSExprSngl vZName) = (NSExprSngl vZName)
sub_NSExp (NSExprParam vZName vZExpr_lst) = (NSExprParam vZName vZExpr_lst)
sub_NSExp (NSUnion v1NSExp v2NSExp) = (NSUnion v1NSExp v2NSExp)
sub_NSExp (NSIntersect v1NSExp v2NSExp) = (NSIntersect v1NSExp v2NSExp)
sub_NSExp (NSHide v1NSExp v2NSExp) = (NSHide v1NSExp v2NSExp)
sub_NSExp (NSBigUnion vZExpr) = (NSBigUnion vZExpr)
\end{code}

\begin{code}
sub_PPar :: PPar -> PPar
sub_PPar (ProcZPara vZPara) = (ProcZPara vZPara)
sub_PPar (CParAction vZName vParAction) = (CParAction vZName vParAction)
sub_PPar (CNameSet vZName vNSExp) = (CNameSet vZName vNSExp)
\end{code}
\begin{code}
sub_ParAction :: ParAction -> ParAction
sub_ParAction (CircusAction vCAction) = (CircusAction vCAction)
sub_ParAction (ParamActionDecl vZGenFilt_lst vParAction) = (ParamActionDecl vZGenFilt_lst vParAction)
\end{code}
\begin{code}
sub_CAction :: CAction -> CAction
sub_CAction (CActionSchemaExpr vZSExpr) = (CActionSchemaExpr vZSExpr)
sub_CAction (CActionCommand vCCommand) = (CActionCommand vCCommand)
sub_CAction (CActionName vZName) = (CActionName vZName)
sub_CAction (CSPSkip ) = (CSPSkip )
sub_CAction (CSPStop) = (CSPStop)
sub_CAction (CSPChaos) = (CSPChaos)
sub_CAction (CSPCommAction vComm vCAction) = (CSPCommAction vComm vCAction)
sub_CAction (CSPGuard vZPred vCAction) = (CSPGuard vZPred vCAction)
sub_CAction (CSPSeq v1CAction v2CAction) = (CSPSeq v1CAction v2CAction)
sub_CAction (CSPExtChoice v1CAction v2CAction) = (CSPExtChoice v1CAction v2CAction)
sub_CAction (CSPIntChoice v1CAction v2CAction) = (CSPIntChoice v1CAction v2CAction)
sub_CAction (CSPNSParal v1NSExp vCSExp v2NSExp v1CAction v2CAction) = (CSPNSParal v1NSExp vCSExp v2NSExp v1CAction v2CAction)
sub_CAction (CSPParal vCSExp v1CAction v2CAction) = (CSPParal vCSExp v1CAction v2CAction)
sub_CAction (CSPNSInter v1NSExp v2NSExp v1CAction v2CAction) = (CSPNSInter v1NSExp v2NSExp v1CAction v2CAction)
sub_CAction (CSPInterleave v1CAction v2CAction) = (CSPInterleave v1CAction v2CAction)
sub_CAction (CSPHide vCAction vCSExp) = (CSPHide vCAction vCSExp)
sub_CAction (CSPParAction vZName vZExpr_lst) = (CSPParAction vZName vZExpr_lst)
sub_CAction (CSPRenAction vZName vCReplace) = (CSPRenAction vZName vCReplace)
sub_CAction (CSPRecursion vZName vCAction) = (CSPRecursion vZName vCAction)
sub_CAction (CSPUnfAction vZName vCAction) = (CSPUnfAction vZName vCAction)
sub_CAction (CSPUnParAction vZGenFilt_lst vCAction vZName) = (CSPUnParAction vZGenFilt_lst vCAction vZName)
sub_CAction (CSPRepSeq vZGenFilt_lst vCAction) = (CSPRepSeq vZGenFilt_lst vCAction)
sub_CAction (CSPRepExtChoice vZGenFilt_lst vCAction) = (CSPRepExtChoice vZGenFilt_lst vCAction)
sub_CAction (CSPRepIntChoice vZGenFilt_lst vCAction) = (CSPRepIntChoice vZGenFilt_lst vCAction)
sub_CAction (CSPRepParalNS vCSExp vZGenFilt_lst vNSExp vCAction) = (CSPRepParalNS vCSExp vZGenFilt_lst vNSExp vCAction)
sub_CAction (CSPRepParal vCSExp vZGenFilt_lst vCAction) = (CSPRepParal vCSExp vZGenFilt_lst vCAction)
sub_CAction (CSPRepInterlNS vZGenFilt_lst vNSExp vCAction) = (CSPRepInterlNS vZGenFilt_lst vNSExp vCAction)
sub_CAction (CSPRepInterl vZGenFilt_lst vCAction) = (CSPRepInterl vZGenFilt_lst vCAction)
\end{code}
