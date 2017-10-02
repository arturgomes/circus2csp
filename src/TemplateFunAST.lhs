\begin{code}
module TemplateFunAST where

import AST

my_fun_ZGenFilt (Include _ZSExpr) = undefined
my_fun_ZGenFilt (Choose _ZVar _ZExpr) = undefined
my_fun_ZGenFilt (Check _ZPred) = undefined
my_fun_ZGenFilt (Evaluate _ZVar _ZExpr1 _ZExpr2) = undefined

my_fun_ZExpr (ZVar _ZVar) = undefined
my_fun_ZExpr (ZInt _ZInt) = undefined
my_fun_ZExpr (ZGiven _GivenValue) = undefined
my_fun_ZExpr (ZFree0 _ZVar) = undefined
my_fun_ZExpr (ZFree1 _ZVar _ZExpr) = undefined
my_fun_ZExpr (ZTuple _ZExpr_lst) = undefined
my_fun_ZExpr (ZBinding _ZVar_ZExpr_lst) = undefined
my_fun_ZExpr (ZSetDisplay _ZExpr_lst) = undefined
my_fun_ZExpr (ZSeqDisplay _ZExpr_lst) = undefined
my_fun_ZExpr (ZFSet _ZFSet) = undefined
my_fun_ZExpr (ZIntSet _ZInt1 _ZInt2) = undefined
my_fun_ZExpr (ZGenerator _ZReln _ZExpr) = undefined
my_fun_ZExpr (ZCross _ZExpr_lst) = undefined
my_fun_ZExpr (ZFreeType _ZVar _ZBranch_lst) = undefined
my_fun_ZExpr (ZSetComp _ZGenFilt_lst ( _ZExpr)) = undefined
my_fun_ZExpr (ZLambda _ZGenFilt_lst _ZExpr) = undefined
my_fun_ZExpr (ZESchema _ZSExpr) = undefined
my_fun_ZExpr (ZGivenSet _GivenSet) = undefined
my_fun_ZExpr (ZUniverse) = undefined
my_fun_ZExpr (ZCall _ZExpr1 _ZExpr2) = undefined
my_fun_ZExpr (ZReln _ZReln) = undefined
my_fun_ZExpr (ZFunc1 _ZFunc1) = undefined
my_fun_ZExpr (ZFunc2 _ZFunc2) = undefined
my_fun_ZExpr (ZStrange _ZStrange) = undefined
my_fun_ZExpr (ZMu _ZGenFilt_lst ( _ZExpr)) = undefined
my_fun_ZExpr (ZELet _ZVar_ZExpr_lst _ZExpr) = undefined
my_fun_ZExpr (ZIf_Then_Else _ZPred _ZExpr1 _ZExpr2) = undefined
my_fun_ZExpr (ZSelect _ZExpr _ZVar) = undefined
my_fun_ZExpr (ZTheta _ZSExpr) = undefined

my_fun_ZPred (ZFalse{reason=_ZPred_lst}) = undefined
my_fun_ZPred (ZTrue{reason=_ZPred_lst}) = undefined
my_fun_ZPred (ZAnd _ZPred1 _ZPred2) = undefined
my_fun_ZPred (ZOr _ZPred1 _ZPred2) = undefined
my_fun_ZPred (ZImplies _ZPred1 _ZPred2) = undefined
my_fun_ZPred (ZIff _ZPred1 _ZPred2) = undefined
my_fun_ZPred (ZNot _ZPred) = undefined
my_fun_ZPred (ZExists _ZGenFilt_lst _ZPred) = undefined
my_fun_ZPred (ZExists_1 _ZGenFilt_lst _ZPred) = undefined
my_fun_ZPred (ZForall _ZGenFilt_lst _ZPred) = undefined
my_fun_ZPred (ZPLet _ZVar_ZExpr_lst _ZPred) = undefined
my_fun_ZPred (ZEqual _ZExpr1 _ZExpr2) = undefined
my_fun_ZPred (ZMember _ZExpr1 _ZExpr2) = undefined
my_fun_ZPred (ZPre _ZSExpr) = undefined
my_fun_ZPred (ZPSchema _ZSExpr) = undefined

my_fun_ZSExpr (ZSchema _ZGenFilt_lst) = undefined
my_fun_ZSExpr (ZSRef _ZSName _ZDecor_lst _ZReplace_lst) = undefined
my_fun_ZSExpr (ZS1 _ZS1 _ZSExpr) = undefined
my_fun_ZSExpr (ZS2 _ZS2 _ZSExpr1 _ZSExpr2) = undefined
my_fun_ZSExpr (ZSHide _ZSExpr _ZVar_lst) = undefined
my_fun_ZSExpr (ZSExists _ZGenFilt_lst _ZSExpr) = undefined
my_fun_ZSExpr (ZSExists_1 _ZGenFilt_lst _ZSExpr) = undefined
my_fun_ZSExpr (ZSForall _ZGenFilt_lst _ZSExpr) = undefined

my_fun_ZReplace (ZRename _ZVar1 _ZVar2) = undefined
my_fun_ZReplace (ZAssign _ZVar _ZExpr) = undefined

my_fun_ZSName (ZSPlain _String ) = undefined
my_fun_ZSName (ZSDelta _String ) = undefined
my_fun_ZSName (ZSXi _String) = undefined

my_fun_ZS1 (ZSPre ) = undefined
my_fun_ZS1 (ZSNot) = undefined

my_fun_ZS2 (ZSAnd ) = undefined
my_fun_ZS2 (ZSOr ) = undefined
my_fun_ZS2 (ZSImplies ) = undefined
my_fun_ZS2 (ZSIff) = undefined
my_fun_ZS2 (ZSProject ) = undefined
my_fun_ZS2 (ZSSemi ) = undefined
my_fun_ZS2 (ZSPipe) = undefined

my_fun_ZBranch (ZBranch0 _ZVar) = undefined
my_fun_ZBranch (ZBranch1 _ZVar _ZExpr) = undefined

my_fun_ZPara (ZGivenSetDecl _GivenSet) = undefined
my_fun_ZPara (ZSchemaDef _ZSName _ZSExpr) = undefined
my_fun_ZPara (Process _ProcDecl) = undefined

my_fun_CDecl (CChan _ZName) = undefined
my_fun_CDecl (CChanDecl _ZName _ZExpr) = undefined
my_fun_CDecl (CGenChanDecl _ZName _ZName1 _ZExpr) = undefined


my_fun_ProcDecl (CProcess _ZName _ProcessDef) = undefined
my_fun_ProcDecl (CParamProcess _ZName _ZName_lst _ProcessDef) = undefined
my_fun_ProcDecl (CGenProcess _ZName _ZName_lst _ProcessDef) = undefined

my_fun_ProcessDef (ProcDefSpot _ZGenFilt_lst _ProcessDef) = undefined
my_fun_ProcessDef (ProcDefIndex _ZGenFilt_lst _ProcessDef) = undefined
my_fun_ProcessDef (ProcDef _CProc) = undefined

my_fun_CProc (CRepSeqProc _ZGenFilt_lst _CProc) = undefined
my_fun_CProc (CRepExtChProc _ZGenFilt_lst _CProc) = undefined
my_fun_CProc (CRepIntChProc _ZGenFilt_lst _CProc) = undefined
my_fun_CProc (CRepParalProc _CSExp1 _ZGenFilt_lst _CProc) = undefined
my_fun_CProc (CRepInterlProc _ZGenFilt_lst _CProc) = undefined
my_fun_CProc (CHide _CProc _CSExp1) = undefined
my_fun_CProc (CExtChoice _CProc1 _CProc2) = undefined
my_fun_CProc (CIntChoice _CProc1 _CProc2) = undefined
my_fun_CProc (CParParal _CSExp1 _CProc1 _CProc2) = undefined
my_fun_CProc (CInterleave _CProc1 _CProc2) = undefined
my_fun_CProc (CGenProc _ZName _ZExpr_lst) = undefined
my_fun_CProc (CParamProc _ZName _ZExpr_lst) = undefined
my_fun_CProc (CProcRename _ZName _Comm_lst _Comm_lst1) = undefined
my_fun_CProc (CSeq _CProc1 _CProc2) = undefined
my_fun_CProc (CSimpIndexProc _ZName _ZExpr_lst) = undefined
my_fun_CProc (CircusProc _ZName) = undefined
my_fun_CProc (ProcMain _ZPara _PPar_lst _CAction) = undefined
my_fun_CProc (ProcStalessMain _PPar_lst _CAction) = undefined

my_fun_NSExp (NSExpEmpty) = undefined
my_fun_NSExp (NSExprMult _ZVar_lst) = undefined
my_fun_NSExp (NSExprSngl _ZName) = undefined
my_fun_NSExp (NSExprParam _ZName _ZExpr_lst) = undefined
my_fun_NSExp (NSUnion _NSExp1 _NSExp2) = undefined
my_fun_NSExp (NSIntersect _NSExp1 _NSExp2) = undefined
my_fun_NSExp (NSHide _NSExp1 _NSExp2) = undefined
my_fun_NSExp (NSBigUnion _ZExpr) = undefined

my_fun_PPar (ProcZPara _ZPara) = undefined
my_fun_PPar (CParAction _ZName _ParAction) = undefined
my_fun_PPar (CNameSet _ZName _ZExpr_lst) = undefined

my_fun_ParAction (CircusAction _CAction) = undefined
my_fun_ParAction (ParamActionDecl _ZGenFilt_lst _ParAction) = undefined

my_fun_CAction (CActionSchemaExpr _ZSExpr) = undefined
my_fun_CAction (CActionCommand _CCommand) = undefined
my_fun_CAction (CActionName _ZName) = undefined
my_fun_CAction (CSPSkip ) = undefined
my_fun_CAction (CSPStop ) = undefined
my_fun_CAction (CSPChaos) = undefined
my_fun_CAction (CSPCommAction _Comm _CAction) = undefined
my_fun_CAction (CSPGuard _ZPred _CAction) = undefined
my_fun_CAction (CSPSeq _CAction1 _CAction2) = undefined
my_fun_CAction (CSPExtChoice _CAction1 _CAction2) = undefined
my_fun_CAction (CSPIntChoice _CAction1 _CAction2) = undefined
my_fun_CAction (CSPNSParal _ZExpr_lst1 _CSExp _ZExpr_lst2 _CAction1 _CAction2) = undefined
my_fun_CAction (CSPParal _CSExp1 _CAction1 _CAction2) = undefined
my_fun_CAction (CSPNSInter _ZExpr_lst1 _ZExpr_lst2 _CAction1 _CAction2) = undefined
my_fun_CAction (CSPInterleave _CAction1 _CAction2) = undefined
my_fun_CAction (CSPHide _CAction _CSExp) = undefined
my_fun_CAction (CSPParAction _ZName _ZExpr_lst) = undefined
my_fun_CAction (CSPRenAction _ZName _CReplace) = undefined
my_fun_CAction (CSPRecursion _ZName _CAction) = undefined
my_fun_CAction (CSPUnfAction _ZName _CAction) = undefined
my_fun_CAction (CSPUnParAction _ZGenFilt_lst _CAction _ZName) = undefined
my_fun_CAction (CSPRepSeq _ZGenFilt_lst _CAction) = undefined
my_fun_CAction (CSPRepExtChoice _ZGenFilt_lst _CAction) = undefined
my_fun_CAction (CSPRepIntChoice _ZGenFilt_lst _CAction) = undefined
my_fun_CAction (CSPRepParalNS _CSExp _ZGenFilt_lst _ZExpr_lst _CAction) = undefined
my_fun_CAction (CSPRepParal _CSExp _ZGenFilt_lst _CAction) = undefined
my_fun_CAction (CSPRepInterlNS _ZGenFilt_lst _ZExpr_lst _CAction) = undefined
my_fun_CAction (CSPRepInterl _ZGenFilt_lst _CAction) = undefined

my_fun_Comm (ChanComm _ZName _CParameter_lst) = undefined
my_fun_Comm (ChanGenComm _ZName _ZExpr_lst _CParameter_lst) = undefined

my_fun_CParameter (ChanInp _ZName) = undefined
my_fun_CParameter (ChanInpPred _ZName _ZPred) = undefined
my_fun_CParameter (ChanOutExp _ZExpr) = undefined
my_fun_CParameter (ChanDotExp _ZExpr) = undefined

my_fun_CCommand (CAssign _ZVar_lst _ZExpr_lst) = undefined
my_fun_CCommand (CIf _CGActions) = undefined
my_fun_CCommand (CVarDecl _ZGenFilt_lst _CAction) = undefined
my_fun_CCommand (CValDecl _ZGenFilt_lst _CAction) = undefined
my_fun_CCommand (CResDecl _ZGenFilt_lst _CAction) = undefined
my_fun_CCommand (CVResDecl _ZGenFilt_lst _CAction) = undefined
my_fun_CCommand (CAssumpt _ZName_lst _ZPred1 _ZPred2) = undefined
my_fun_CCommand (CAssumpt1 _ZName_lst _ZPred) = undefined
my_fun_CCommand (CPrefix _ZPred1 _ZPred2) = undefined
my_fun_CCommand (CPrefix1 _ZPred) = undefined
my_fun_CCommand (CommandBrace _ZPred) = undefined
my_fun_CCommand (CommandBracket _ZPred) = undefined

my_fun_CGActions (CircGAction _ZPred _CAction) = undefined
my_fun_CGActions (CircThenElse _CGActions1 _CGActions2) = undefined

my_fun_CReplace (CRename _ZVar_lst _ZVar_lst1) = undefined
my_fun_CReplace (CRenameAssign _ZVar_lst _ZVar_lst1) = undefined
\end{code}
