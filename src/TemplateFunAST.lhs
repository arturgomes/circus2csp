
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
fun_ZGenFilt (Choose _ZVar _zex) = undefined
fun_ZGenFilt (Check _zpr) = undefined
fun_ZGenFilt (Evaluate _ZVar _zex _zex) = undefined
\end{code}
\subsection{Z Expressions}
\begin{code}
fun_ZExpr (ZVar _ZVar) = undefined
fun_ZExpr (ZInt _ZInt) = undefined
fun_ZExpr (ZGiven _GivenValue) = undefined
fun_ZExpr (ZFree0 _ZVar) = undefined
fun_ZExpr (ZFree1 _ZVar _zex) = undefined
fun_ZExpr (ZTuple _zexls) = undefined
fun_ZExpr (ZBinding _ZVar_ZExpr_lst) = undefined
fun_ZExpr (ZSetDisplay _zexls) = undefined
fun_ZExpr (ZSeqDisplay _zexls) = undefined
fun_ZExpr (ZFSet _ZFSet) = undefined
fun_ZExpr (ZIntSet (Maybe _ZInt) = undefined (Maybe _ZInt) = undefined) = undefined
fun_ZExpr (ZGenerator _ZReln _zex) = undefined
fun_ZExpr (ZCross _zexls) = undefined
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
fun_ZExpr (ZSetComp _zgfs (Maybe _zex) = undefined) = undefined
fun_ZExpr (ZLambda _zgfs _zex) = undefined
fun_ZExpr (ZESchema _ZSExpr) = undefined
fun_ZExpr (ZGivenSet GivenSet) = undefined
fun_ZExpr (ZUniverse) = undefined
fun_ZExpr (ZCall _zex _zex) = undefined
fun_ZExpr (ZReln _ZReln) = undefined
fun_ZExpr (ZFunc1 _ZFunc1) = undefined
fun_ZExpr (ZFunc2 _ZFunc2) = undefined
fun_ZExpr (ZStrange _ZStrange) = undefined
fun_ZExpr (ZMu _zgfs (Maybe _zex) = undefined) = undefined
fun_ZExpr (ZELet _ZVar_ZExpr_lst _zex) = undefined
fun_ZExpr (ZIf_Then_Else _zpr _zex _zex) = undefined
fun_ZExpr (ZSelect _zex _ZVar) = undefined
fun_ZExpr (ZTheta _ZSExpr) = undefined
\end{code}
\subsection{Z Predicates}
\begin{code}
fun_ZPred (ZFalse{reason::_ZPred_lst}) = undefined
fun_ZPred (ZTrue{reason::_ZPred_lst}) = undefined
fun_ZPred (ZAnd _zpr1 _zpr2) = undefined
fun_ZPred (ZOr _zpr1 _zpr2) = undefined
fun_ZPred (ZImplies _zpr1 _zpr2) = undefined
fun_ZPred (ZIff _zpr1 _zpr2) = undefined
fun_ZPred (ZNot _zpr) = undefined
fun_ZPred (ZExists _zgfs _zpr) = undefined
fun_ZPred (ZExists_1 _zgfs _zpr) = undefined
fun_ZPred (ZForall _zgfs _zpr) = undefined
fun_ZPred (ZPLet _ZVar_ZExpr_lst _zpr) = undefined
fun_ZPred (ZEqual _zex _zex) = undefined
fun_ZPred (ZMember _zex _zex) = undefined
fun_ZPred (ZPre _ZSExpr) = undefined
fun_ZPred (ZPSchema _ZSExpr
\end{code}
\subsection{Z Schemas}
\begin{code}
fun_ZSExpr (ZSchema _zgfs) = undefined
fun_ZSExpr (ZSRef _ZSName _ZDecor_lst _ZReplace_lst) = undefined
fun_ZSExpr (ZS1 _ZS1 _ZSExpr) = undefined
fun_ZSExpr (ZS2 _ZS2 _ZSExpr _ZSExpr) = undefined
fun_ZSExpr (ZSHide _ZSExpr _ZVar_lst) = undefined
fun_ZSExpr (ZSExists _zgfs _ZSExpr) = undefined
fun_ZSExpr (ZSExists_1 _zgfs _ZSExpr) = undefined
fun_ZSExpr (ZSForall _zgfs _ZSExpr

fun_ZReplace (ZRename _ZVar _ZVar) = undefined
fun_ZReplace (ZAssign _ZVar _zex

fun_ZSName (ZSPlain _String ) = undefined
fun_ZSName (ZSDelta _String ) = undefined
fun_ZSName (ZSXi _String
fun_ZS1 x = x
fun_ZS2 x = x
\end{code}
\begin{code}
fun_ZBranch
  (ZBranch0 _ZVar) = undefined
(ZBranch1 _ZVar _zex
\end{code}
\section{Z Paragraphs}
\begin{code}
fun_ZPara (ZGivenSetDecl GivenSet) = undefined
fun_ZPara (ZSchemaDef _ZSName _ZSExpr) = undefined
fun_ZPara (ZAbbreviation _ZVar _zex) = undefined
fun_ZPara (ZFreeTypeDef _ZVar _ZBranch_lst) = undefined
fun_ZPara (ZPredicate _zpr) = undefined
fun_ZPara (ZAxDef _zgfs) = undefined
fun_ZPara (ZGenDef _zgfs) = undefined
fun_ZPara (ZMachineDef{machName::_String,
    machState::_String,
    machInit::_String,
    machOps::__String_lst}
\end{code}
\section{Circus Abstract Syntax}
% \begin{code}) = undefined
% (CircChannel _CDecl_lst) = undefined
% (CircChanSet _zn _csx) = undefined
% (Process ProcDecl) = undefined
% (Assert _String
% \end{code}
\subsection{\Circus\ Channel Declaration}
\begin{code}
fun_CDecl (CChan _zn) = undefined
fun_CDecl (CChanDecl _zn _zex) = undefined
fun_CDecl (CGenChanDecl _zn _zn2 _zex) = undefined
\end{code}
\subsection{\Circus\ Channel Expression}
\begin{code}
fun_CSExp (CSExpr _zn) = undefined
fun_CSExp (CSEmpty) = undefined
fun_CSExp (CChanSet _zn_lst) = undefined
fun_CSExp (ChanSetUnion _csx _csx2) = undefined
fun_CSExp (ChanSetInter _csx _csx2) = undefined
fun_CSExp (ChanSetDiff _csx _csx2) = undefined
\end{code}
\subsection{\Circus\ Process}
\begin{code}
fun_ProcDecl (CProcess _zn ProcessDef) = undefined
fun_ProcDecl (CParamProcess _zn _zn2_lst _ProcessDef) = undefined
fun_ProcDecl (CGenProcess _zn _zn2_lst _ProcessDef) = undefined
\end{code}
\subsection{\Circus\ Process}
\begin{code}
fun_ProcessDef (ProcDefSpot _zgfs _ProcessDef) = undefined
fun_ProcessDef (ProcDefIndex _zgfs _ProcessDef) = undefined
fun_ProcessDef (ProcDef _cp) = undefined
\end{code}
\subsection{\Circus\ Process}
\begin{code}
fun_CProc (CRepSeqProc _zgfs _cp) = undefined
fun_CProc (CRepExtChProc _zgfs _cp) = undefined
fun_CProc (CRepIntChProc _zgfs _cp) = undefined
fun_CProc (CRepParalProc _csx _zgfs _cp) = undefined
fun_CProc (CRepInterlProc _zgfs _cp) = undefined
fun_CProc (CHide _cp _csx) = undefined
fun_CProc (CExtChoice _cp _cp2) = undefined
fun_CProc (CIntChoice _cp _cp2) = undefined
fun_CProc (CParParal _csx _cp _cp2) = undefined
fun_CProc (CInterleave _cp _cp2) = undefined
fun_CProc (CGenProc _zn _zexls) = undefined
fun_CProc (CParamProc _zn _zexls) = undefined
fun_CProc (CProcRename _cp _Comm_lst _Comm_lst) = undefined
fun_CProc (CSeq _cp _cp2) = undefined
fun_CProc (CSimpIndexProc _zn _zexls) = undefined
fun_CProc (CircusProc _zn) = undefined
fun_CProc (ProcMain _ZPara _PPar_lst _cact) = undefined
fun_CProc (ProcStalessMain _PPar_lst _cact) = undefined
\end{code}
\subsection{\Circus\ Name-Sets}
\begin{code}
fun_NSExp (NSExpEmpty) = undefined
fun_NSExp (NSExprMult _ZVar_lst) = undefined
fun_NSExp (NSExprSngl _zn) = undefined
fun_NSExp (NSExprParam _zn _zexls) = undefined
fun_NSExp (NSUnion _NSExp _NSExp) = undefined
fun_NSExp (NSIntersect _NSExp _NSExp) = undefined
fun_NSExp (NSHide _NSExp _NSExp) = undefined
fun_NSExp (NSBigUnion _zex) = undefined
\end{code}
\subsection{Process paragraphs}
\begin{code}
fun_PPar (ProcZPara _ZPara) = undefined
fun_PPar (CParAction _zn _ParAction) = undefined
fun_PPar (CNameSet _zn _zexls) = undefined
\end{code}
\subsection{Parametrised Actions}
\begin{code}
fun_ParAction (CircusAction _cact) = undefined
fun_ParAction (ParamActionDecl _zgfs _ParAction) = undefined
\end{code}
\subsection{\Circus\ Actions}
\begin{code}
fun_CAction (CActionSchemaExpr _ZSExpr) = undefined
fun_CAction (CActionCommand _CCommand) = undefined
fun_CAction (CActionName _zn) = undefined
fun_CAction (CSPSkip ) = undefined
fun_CAction (CSPStop ) = undefined
fun_CAction (CSPChaos) = undefined
fun_CAction (CSPCommAction _Comm _cact) = undefined
fun_CAction (CSPGuard _zpr _cact) = undefined
fun_CAction (CSPSeq _cact1 _cact2) = undefined
fun_CAction (CSPExtChoice _cact1 _cact2) = undefined
fun_CAction (CSPIntChoice _cact1 _cact2) = undefined
fun_CAction (CSPNSParal _zexls _csx _zexls _cact1 _cact2) = undefined
fun_CAction (CSPParal _csx _cact1 _cact2) = undefined
fun_CAction (CSPNSInter _zexls _zexls _cact1 _cact2) = undefined
fun_CAction (CSPInterleave _cact1 _cact2) = undefined
fun_CAction (CSPHide _cact _csx) = undefined
fun_CAction (CSPParAction _zn _zexls) = undefined
fun_CAction (CSPRenAction _zn _CReplace) = undefined
fun_CAction (CSPRecursion _zn _cact) = undefined
fun_CAction (CSPUnfAction _zn _cact) = undefined
fun_CAction (CSPUnParAction _zgfs _cact _zn) = undefined
fun_CAction (CSPRepSeq _zgfs _cact) = undefined
fun_CAction (CSPRepExtChoice _zgfs _cact) = undefined
fun_CAction (CSPRepIntChoice _zgfs _cact) = undefined
fun_CAction (CSPRepParalNS _csx _zgfs _zexls _cact) = undefined
fun_CAction (CSPRepParal _csx _zgfs _cact) = undefined
fun_CAction (CSPRepInterlNS _zgfs _zexls _cact) = undefined
fun_CAction (CSPRepInterl _zgfs _cact) = undefined
\end{code}
\subsection{\Circus\ Communication}
\begin{code}
fun_Comm (ChanComm _zn _CParameter_lst) = undefined
fun_Comm (ChanGenComm _zn _zexls _CParameter_lst) = undefined
\end{code}
\subsection{\Circus\ Communication}
\begin{code}
fun_CParameter (ChanInp _zn) = undefined
fun_CParameter (ChanInpPred _zn _zpr) = undefined
fun_CParameter (ChanOutExp _zex) = undefined
fun_CParameter (ChanDotExp _zex) = undefined
\end{code}
\subsection{\Circus\ Commands}
\begin{code}
fun_CCommand (CAssign _ZVar_lst _zexls) = undefined
fun_CCommand (CIf _CGActions) = undefined
fun_CCommand (CVarDecl _zgfs _cact) = undefined
fun_CCommand (CValDecl _zgfs _cact) = undefined
fun_CCommand (CResDecl _zgfs _cact) = undefined
fun_CCommand (CVResDecl _zgfs _cact) = undefined
fun_CCommand (CAssumpt _zn_lst _zpr1 _zpr2) = undefined
fun_CCommand (CAssumpt1 _zn_lst _zpr) = undefined
fun_CCommand (CPrefix _zpr1 _zpr2) = undefined
fun_CCommand (CPrefix1 _zpr) = undefined
fun_CCommand (CommandBrace _zpr) = undefined
fun_CCommand (CommandBracket _zpr) = undefined
\end{code}
\subsection{\Circus\ Guards}
\begin{code}
fun_CGActions (CircGAction _zpr _cact) = undefined
fun_CGActions (CircThenElse _CGActions _CGActions1) = undefined
\end{code}
\subsection{Circus Renaming}
\begin{code}
fun_CReplace (CRename _ZVar_lst _ZVar_lst) = undefined
fun_CReplace (CRenameAssign _ZVar_lst _ZVar_lst) = undefined
\end{code}
