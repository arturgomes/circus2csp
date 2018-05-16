\begin{code}
module TemplateFunAST where
import AST
\end{code}
\section{Z Abstract Syntax}
\subsection{Z Relations and Functions}
\begin{code}
fun_ZReln x = x
fun_ZFunc1 x = x
fun_ZFunc2 x = x
fun_ZStrange x = x
\end{code}

\begin{code}
fun_ZGenFilt (Include _ZSExpr) = undefined
fun_ZGenFilt (Choose _ZVar _ZExpr) = undefined
fun_ZGenFilt (Check _ZPred) = undefined
fun_ZGenFilt (Evaluate _ZVar _ZExpr _ZExpr) = undefined
\end{code}
\subsection{Z Expressions}
\begin{code}
fun_ZExpr (ZVar _ZVar) = undefined
fun_ZExpr (ZInt _ZInt) = undefined
fun_ZExpr (ZGiven _GivenValue) = undefined
fun_ZExpr (ZFree0 _ZVar) = undefined
fun_ZExpr (ZFree1 _ZVar _ZExpr) = undefined
fun_ZExpr (ZTuple _ZExpr_lst) = undefined
fun_ZExpr (ZBinding _ZVar_ZExpr_lst) = undefined
fun_ZExpr (ZSetDisplay _ZExpr_lst) = undefined
fun_ZExpr (ZSeqDisplay _ZExpr_lst) = undefined
fun_ZExpr (ZFSet _ZFSet) = undefined
fun_ZExpr (ZIntSet (Maybe _ZInt) = undefined (Maybe _ZInt) = undefined) = undefined
fun_ZExpr (ZGenerator _ZReln _ZExpr) = undefined
fun_ZExpr (ZCross _ZExpr_lst) = undefined
fun_ZExpr (ZFreeType _ZVar _ZBranch_lst) = undefined
fun_ZExpr (ZPowerSet{baseset::ZExpr,
        is_non_empty::Bool,
        is_finite::Bool}) = undefined
fun_ZExpr (ZFuncSet{ domset::ZExpr,
        ranset::ZExpr,
        is_function::Bool,
        is_total::Bool,
        is_onto::Bool,
        is_one2one::Bool,
        is_sequence::Bool,
        is_non_empty::Bool,
        is_finite::Bool}) = undefined
fun_ZExpr (ZSetComp _ZGenFilt_lst (Maybe _ZExpr) = undefined) = undefined
fun_ZExpr (ZLambda _ZGenFilt_lst _ZExpr) = undefined
fun_ZExpr (ZESchema _ZSExpr) = undefined
fun_ZExpr (ZGivenSet GivenSet) = undefined
fun_ZExpr (ZUniverse) = undefined
fun_ZExpr (ZCall _ZExpr _ZExpr) = undefined
fun_ZExpr (ZReln _ZReln) = undefined
fun_ZExpr (ZFunc1 _ZFunc1) = undefined
fun_ZExpr (ZFunc2 _ZFunc2) = undefined
fun_ZExpr (ZStrange _ZStrange) = undefined
fun_ZExpr (ZMu _ZGenFilt_lst (Maybe _ZExpr) = undefined) = undefined
fun_ZExpr (ZELet _ZVar_ZExpr_lst _ZExpr) = undefined
fun_ZExpr (ZIf_Then_Else _ZPred _ZExpr _ZExpr) = undefined
fun_ZExpr (ZSelect _ZExpr _ZVar) = undefined
fun_ZExpr (ZTheta _ZSExpr) = undefined
\end{code}
\subsection{Z Predicates}
\begin{code}
fun_ZPred (ZFalse{reason::_ZPred_lst}) = undefined
fun_ZPred (ZTrue{reason::_ZPred_lst}) = undefined
fun_ZPred (ZAnd _ZPred1 _ZPred2) = undefined
fun_ZPred (ZOr _ZPred1 _ZPred2) = undefined
fun_ZPred (ZImplies _ZPred1 _ZPred2) = undefined
fun_ZPred (ZIff _ZPred1 _ZPred2) = undefined
fun_ZPred (ZNot _ZPred) = undefined
fun_ZPred (ZExists _ZGenFilt_lst _ZPred) = undefined
fun_ZPred (ZExists_1 _ZGenFilt_lst _ZPred) = undefined
fun_ZPred (ZForall _ZGenFilt_lst _ZPred) = undefined
fun_ZPred (ZPLet _ZVar_ZExpr_lst _ZPred) = undefined
fun_ZPred (ZEqual _ZExpr _ZExpr) = undefined
fun_ZPred (ZMember _ZExpr _ZExpr) = undefined
fun_ZPred (ZPre _ZSExpr) = undefined
fun_ZPred (ZPSchema _ZSExpr
\end{code}
\subsection{Z Schemas}
\begin{code}
fun_ZSExpr (ZSchema _ZGenFilt_lst) = undefined
fun_ZSExpr (ZSRef _ZSName _ZDecor_lst _ZReplace_lst) = undefined
fun_ZSExpr (ZS1 _ZS1 _ZSExpr) = undefined
fun_ZSExpr (ZS2 _ZS2 _ZSExpr _ZSExpr) = undefined
fun_ZSExpr (ZSHide _ZSExpr _ZVar_lst) = undefined
fun_ZSExpr (ZSExists _ZGenFilt_lst _ZSExpr) = undefined
fun_ZSExpr (ZSExists_1 _ZGenFilt_lst _ZSExpr) = undefined
fun_ZSExpr (ZSForall _ZGenFilt_lst _ZSExpr

fun_ZReplace (ZRename _ZVar _ZVar) = undefined
fun_ZReplace (ZAssign _ZVar _ZExpr

fun_ZSName (ZSPlain _String ) = undefined
fun_ZSName (ZSDelta _String ) = undefined
fun_ZSName (ZSXi _String
fun_ZS1 x = x
fun_ZS2 x = x
\end{code}
\begin{code}
fun_ZBranch
  (ZBranch0 _ZVar) = undefined
(ZBranch1 _ZVar _ZExpr
\end{code}
\section{Z Paragraphs}
\begin{code}
fun_ZPara (ZGivenSetDecl GivenSet) = undefined
fun_ZPara (ZSchemaDef _ZSName _ZSExpr) = undefined
fun_ZPara (ZAbbreviation _ZVar _ZExpr) = undefined
fun_ZPara (ZFreeTypeDef _ZVar _ZBranch_lst) = undefined
fun_ZPara (ZPredicate _ZPred) = undefined
fun_ZPara (ZAxDef _ZGenFilt_lst) = undefined
fun_ZPara (ZGenDef _ZGenFilt_lst) = undefined
fun_ZPara (ZMachineDef{machName::_String,
    machState::_String,
    machInit::_String,
    machOps::__String_lst}
\end{code}
\section{Circus Abstract Syntax}
% \begin{code}) = undefined
% (CircChannel _CDecl_lst) = undefined
% (CircChanSet _ZName _CSExp) = undefined
% (Process ProcDecl) = undefined
% (Assert _String
% \end{code}
\subsection{\Circus\ Channel Declaration}
\begin{code}
fun_CDecl (CChan _ZName) = undefined
fun_CDecl (CChanDecl _ZName _ZExpr) = undefined
fun_CDecl (CGenChanDecl _ZName _ZName _ZExpr
\end{code}
\subsection{\Circus\ Channel Expression}
\begin{code}
fun_CSExp (CSExpr _ZName) = undefined
fun_CSExp (CSEmpty) = undefined
fun_CSExp (CChanSet _ZName_lst) = undefined
fun_CSExp (ChanSetUnion _CSExp _CSExp) = undefined
fun_CSExp (ChanSetInter _CSExp _CSExp) = undefined
fun_CSExp (ChanSetDiff _CSExp _CSExp
\end{code}
\subsection{\Circus\ Process}
\begin{code}
fun_ProcDecl (CProcess _ZName ProcessDef) = undefined
fun_ProcDecl (CParamProcess _ZName _ZName_lst _ProcessDef) = undefined
fun_ProcDecl (CGenProcess _ZName _ZName_lst _ProcessDef
\end{code}
\subsection{\Circus\ Process}
\begin{code}
fun_ProcessDef (ProcDefSpot _ZGenFilt_lst _ProcessDef) = undefined
fun_ProcessDef (ProcDefIndex _ZGenFilt_lst _ProcessDef) = undefined
fun_ProcessDef (ProcDef _CProc) = undefined
\end{code}
\subsection{\Circus\ Process}
\begin{code}
fun_CProc (CRepSeqProc _ZGenFilt_lst _CProc) = undefined
fun_CProc (CRepExtChProc _ZGenFilt_lst _CProc) = undefined
fun_CProc (CRepIntChProc _ZGenFilt_lst _CProc) = undefined
fun_CProc (CRepParalProc _CSExp _ZGenFilt_lst _CProc) = undefined
fun_CProc (CRepInterlProc _ZGenFilt_lst _CProc) = undefined
fun_CProc (CHide _CProc _CSExp) = undefined
fun_CProc (CExtChoice _CProc _CProc) = undefined
fun_CProc (CIntChoice _CProc _CProc) = undefined
fun_CProc (CParParal _CSExp _CProc _CProc) = undefined
fun_CProc (CInterleave _CProc _CProc) = undefined
fun_CProc (CGenProc _ZName _ZExpr_lst) = undefined
fun_CProc (CParamProc _ZName _ZExpr_lst) = undefined
fun_CProc (CProcRename _CProc _Comm_lst _Comm_lst) = undefined
fun_CProc (CSeq _CProc _CProc) = undefined
fun_CProc (CSimpIndexProc _ZName _ZExpr_lst) = undefined
fun_CProc (CircusProc _ZName) = undefined
fun_CProc (ProcMain _ZPara _PPar_lst _CAction) = undefined
fun_CProc (ProcStalessMain _PPar_lst _CAction
\end{code}
\subsection{\Circus\ Name-Sets}
\begin{code}
fun_NSExp (NSExpEmpty) = undefined
fun_NSExp (NSExprMult _ZVar_lst) = undefined
fun_NSExp (NSExprSngl _ZName) = undefined
fun_NSExp (NSExprParam _ZName _ZExpr_lst) = undefined
fun_NSExp (NSUnion _NSExp _NSExp) = undefined
fun_NSExp (NSIntersect _NSExp _NSExp) = undefined
fun_NSExp (NSHide _NSExp _NSExp) = undefined
fun_NSExp (NSBigUnion _ZExpr) = undefined
\end{code}
\subsection{Process paragraphs}
\begin{code}
fun_PPar (ProcZPara _ZPara) = undefined
fun_PPar (CParAction _ZName _ParAction) = undefined
fun_PPar (CNameSet _ZName _ZExpr_lst) = undefined
\end{code}
\subsection{Parametrised Actions}
\begin{code}
fun_ParAction (CircusAction _CAction) = undefined
fun_ParAction (ParamActionDecl _ZGenFilt_lst _ParAction) = undefined
\end{code}
\subsection{\Circus\ Actions}
\begin{code}
fun_CAction (CActionSchemaExpr _ZSExpr) = undefined
fun_CAction (CActionCommand _CCommand) = undefined
fun_CAction (CActionName _ZName) = undefined
fun_CAction (CSPSkip ) = undefined
fun_CAction (CSPStop ) = undefined
fun_CAction (CSPChaos) = undefined
fun_CAction (CSPCommAction _Comm _CAction) = undefined
fun_CAction (CSPGuard _ZPred _CAction) = undefined
fun_CAction (CSPSeq _CAction1 _CAction2) = undefined
fun_CAction (CSPExtChoice _CAction1 _CAction2) = undefined
fun_CAction (CSPIntChoice _CAction1 _CAction2) = undefined
fun_CAction (CSPNSParal _ZExpr_lst _CSExp _ZExpr_lst _CAction1 _CAction2) = undefined
fun_CAction (CSPParal _CSExp _CAction1 _CAction2) = undefined
fun_CAction (CSPNSInter _ZExpr_lst _ZExpr_lst _CAction1 _CAction2) = undefined
fun_CAction (CSPInterleave _CAction1 _CAction2) = undefined
fun_CAction (CSPHide _CAction _CSExp) = undefined
fun_CAction (CSPParAction _ZName _ZExpr_lst) = undefined
fun_CAction (CSPRenAction _ZName _CReplace) = undefined
fun_CAction (CSPRecursion _ZName _CAction) = undefined
fun_CAction (CSPUnfAction _ZName _CAction) = undefined
fun_CAction (CSPUnParAction _ZGenFilt_lst _CAction _ZName) = undefined
fun_CAction (CSPRepSeq _ZGenFilt_lst _CAction) = undefined
fun_CAction (CSPRepExtChoice _ZGenFilt_lst _CAction) = undefined
fun_CAction (CSPRepIntChoice _ZGenFilt_lst _CAction) = undefined
fun_CAction (CSPRepParalNS _CSExp _ZGenFilt_lst _ZExpr_lst _CAction) = undefined
fun_CAction (CSPRepParal _CSExp _ZGenFilt_lst _CAction) = undefined
fun_CAction (CSPRepInterlNS _ZGenFilt_lst _ZExpr_lst _CAction) = undefined
fun_CAction (CSPRepInterl _ZGenFilt_lst _CAction) = undefined
\end{code}
\subsection{\Circus\ Communication}
\begin{code}
fun_Comm (ChanComm _ZName _CParameter_lst) = undefined
fun_Comm (ChanGenComm _ZName _ZExpr_lst _CParameter_lst) = undefined
\end{code}
\subsection{\Circus\ Communication}
\begin{code}
fun_CParameter (ChanInp _ZName) = undefined
fun_CParameter (ChanInpPred _ZName _ZPred) = undefined
fun_CParameter (ChanOutExp _ZExpr) = undefined
fun_CParameter (ChanDotExp _ZExpr) = undefined
\end{code}
\subsection{\Circus\ Commands}
\begin{code}
fun_CCommand (CAssign _ZVar_lst _ZExpr_lst) = undefined
fun_CCommand (CIf _CGActions) = undefined
fun_CCommand (CVarDecl _ZGenFilt_lst _CAction) = undefined
fun_CCommand (CValDecl _ZGenFilt_lst _CAction) = undefined
fun_CCommand (CResDecl _ZGenFilt_lst _CAction) = undefined
fun_CCommand (CVResDecl _ZGenFilt_lst _CAction) = undefined
fun_CCommand (CAssumpt _ZName_lst _ZPred1 _ZPred2) = undefined
fun_CCommand (CAssumpt1 _ZName_lst _ZPred) = undefined
fun_CCommand (CPrefix _ZPred1 _ZPred2) = undefined
fun_CCommand (CPrefix1 _ZPred) = undefined
fun_CCommand (CommandBrace _ZPred) = undefined
fun_CCommand (CommandBracket _ZPred) = undefined
\end{code}
\subsection{\Circus\ Guards}
\begin{code}
fun_CGActions (CircGAction _ZPred _CAction) = undefined
fun_CGActions (CircThenElse _CGActions _CGActions1) = undefined
\end{code}
\subsection{Circus Renaming}
\begin{code}
fun_CReplace (CRename _ZVar_lst _ZVar_lst) = undefined
fun_CReplace (CRenameAssign _ZVar_lst _ZVar_lst) = undefined
\end{code}
