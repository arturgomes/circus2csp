\chapter{Bindings functions -- File: Bindings.lhs}
This file is used in order to calculate the range of values that
the bindings will really use within a specification.
\ignore{
\begin{code}
module Bindings where
-- import Data.Text hiding (map,concat,all,take)
import Subs
import AST
import Errors
import OmegaDefs

\end{code}
}
\begin{code}

data TypeVal =  Level ZExpr [TypeVal]
  deriving (Show)

printTabs n
  | n == 0 = ""
  | otherwise = " "++(printTabs (n-1))
printTypeVal x (Level ze [])
  = "\n"++(printTabs x)++"Lvl "++show x++" Expr = "++show ze++"{}"
printTypeVal x (Level ze tp)
  = "\n"++(printTabs x)++"Lvl "++show x++" Expr = "++show ze++"{"
  ++(concat$map (printTypeVal (x+1)) tp)++"\n"++(printTabs x)++"}"

calc_exp_ZGenFilt (Include xZSExpr)
  = calc_exp_ZSExpr xZSExpr
calc_exp_ZGenFilt (Choose x xZExpr)
  = (calc_exp_ZExpr xZExpr)
calc_exp_ZGenFilt (Check xZPred)
  = (calc_exp_ZPred xZPred)
calc_exp_ZGenFilt (Evaluate x xZExpr1 xZExpr2)
  =  (calc_exp_ZExpr xZExpr1)
    ++ (calc_exp_ZExpr xZExpr2)

calc_exp_ZExpr :: ZExpr -> [TypeVal]
calc_exp_ZExpr (ZVar (x,y,z))
  | (not (is_ZVar_st x) && not (isPrefixOf "b_" x)&& not (isPrefixOf "BINDING_" x))
    = [Level (ZVar (x,y,z)) []]
  | otherwise = []
calc_exp_ZExpr (ZInt xZInt)
  = [Level (ZInt xZInt) []]
calc_exp_ZExpr (ZGiven x)
  = [Level (ZGiven x) []]
calc_exp_ZExpr (ZFree0 x)
  = [Level (ZFree0 x) []]
calc_exp_ZExpr (ZFree1 x xZExpr)
  = [Level (ZFree1 x xZExpr) (calc_exp_ZExpr xZExpr)]
calc_exp_ZExpr (ZTuple xZExpr_lst)
  = [Level (ZTuple xZExpr_lst) (concat $ map (calc_exp_ZExpr ) xZExpr_lst)]
-- calc_exp_ZExpr (ZBinding xZExpr_lst)
-- = [Level (ZBinding xZExpr_lst) (concat $ map (calc_exp_ZExpr ) xZExpr_lst)]
calc_exp_ZExpr (ZSetDisplay xZExpr_lst)
  = [Level (ZSetDisplay xZExpr_lst) (concat $ map (calc_exp_ZExpr ) xZExpr_lst)]
calc_exp_ZExpr (ZSeqDisplay xZExpr_lst)
  = [Level (ZSeqDisplay xZExpr_lst) (concat $ map (calc_exp_ZExpr ) xZExpr_lst)]
calc_exp_ZExpr (ZFSet x)
  = [Level (ZFSet x) []]
calc_exp_ZExpr (ZIntSet (Just xZInt1) (Just xZInt2))
  = [Level (ZIntSet (Just xZInt1) (Just xZInt2)) ([Level (ZInt xZInt1) []]++[Level (ZInt xZInt2) []])]
calc_exp_ZExpr (ZIntSet (Just xZInt1) Nothing)
  = [Level  (ZInt xZInt1) []]
calc_exp_ZExpr (ZIntSet Nothing (Just xZInt2))
  = [Level (ZInt xZInt2) []]
calc_exp_ZExpr (ZIntSet Nothing Nothing)
  = [Level (ZIntSet Nothing Nothing) []]
calc_exp_ZExpr (ZGenerator xZReln xZExpr)
  = [Level (ZGenerator xZReln xZExpr) (calc_exp_ZExpr xZExpr)]
calc_exp_ZExpr (ZCross xZExpr_lst)
  = [Level (ZCross xZExpr_lst) (concat $ map (calc_exp_ZExpr ) xZExpr_lst)]
calc_exp_ZExpr (ZFreeType x xZBranch_lst)
  = [Level (ZFreeType x xZBranch_lst) (concat $ map calc_exp_ZBranch xZBranch_lst)]
calc_exp_ZExpr (ZSetComp xZGenFilt_lst (Just xZExpr))
  = [Level (ZSetComp xZGenFilt_lst (Just xZExpr))
  ((concat $ map calc_exp_ZGenFilt xZGenFilt_lst)++
  (calc_exp_ZExpr xZExpr))]
calc_exp_ZExpr (ZSetComp xZGenFilt_lst Nothing)
  = [Level (ZSetComp xZGenFilt_lst Nothing) (concat $ map calc_exp_ZGenFilt xZGenFilt_lst)]
calc_exp_ZExpr (ZLambda xZGenFilt_lst xZExpr)
  = [Level (ZLambda xZGenFilt_lst xZExpr)
    ((calc_exp_ZExpr xZExpr)++
    (concat $ map calc_exp_ZGenFilt xZGenFilt_lst))]
calc_exp_ZExpr (ZESchema xZSExpr)
  = [Level (ZESchema xZSExpr) (calc_exp_ZSExpr xZSExpr)]
calc_exp_ZExpr (ZGivenSet g)
  = [Level (ZGivenSet g) []]
calc_exp_ZExpr (ZUniverse)
  = [Level (ZUniverse) []]
calc_exp_ZExpr (ZCall xZExpr1 xZExpr2)
  = [Level (ZCall xZExpr1 xZExpr2) ((calc_exp_ZExpr xZExpr1)++(calc_exp_ZExpr xZExpr2))]
calc_exp_ZExpr (ZReln xZReln)
  = [Level (ZReln xZReln) []]
calc_exp_ZExpr (ZFunc1 x)
  = [Level (ZFunc1 x) []]
calc_exp_ZExpr (ZFunc2 x)
  = [Level (ZFunc2 x) []]
calc_exp_ZExpr (ZStrange x)
  = [Level (ZStrange x) []]
calc_exp_ZExpr (ZMu xZGenFilt_lst (Just xZExpr))
  = [Level (ZMu xZGenFilt_lst (Just xZExpr)) ((calc_exp_ZExpr xZExpr)++(concat$ map calc_exp_ZGenFilt xZGenFilt_lst))]
calc_exp_ZExpr (ZMu xZGenFilt_lst Nothing)
  = [Level (ZMu xZGenFilt_lst Nothing) (concat$ map calc_exp_ZGenFilt xZGenFilt_lst)]
calc_exp_ZExpr (ZELet xZExpr_lst xZExpr)
  = [Level (ZELet xZExpr_lst xZExpr) ((calc_exp_ZExpr xZExpr)++(concat $ map (calc_exp_ZExpr ) (map snd xZExpr_lst)))]
calc_exp_ZExpr (ZIf_Then_Else xZPred xZExpr1 xZExpr2)
  = [Level (ZIf_Then_Else xZPred xZExpr1 xZExpr2) ((calc_exp_ZPred xZPred)++(calc_exp_ZExpr xZExpr1)++(calc_exp_ZExpr xZExpr2))]
calc_exp_ZExpr (ZSelect xZExpr x)
  = [Level (ZSelect xZExpr x) (calc_exp_ZExpr xZExpr)]
calc_exp_ZExpr (ZTheta xZSExpr)
  = [Level (ZTheta xZSExpr) (calc_exp_ZSExpr xZSExpr)]

calc_exp_ZPred (ZFalse{reason
  = xZPred_lst})
  = (concat$ map calc_exp_ZPred xZPred_lst)
calc_exp_ZPred (ZTrue{reason
  = xZPred_lst})
  = (concat$ map calc_exp_ZPred xZPred_lst)
calc_exp_ZPred (ZAnd xZPred1 xZPred2)
  = (calc_exp_ZPred xZPred1)
    ++(calc_exp_ZPred xZPred2)
calc_exp_ZPred (ZOr xZPred1 xZPred2)
  = (calc_exp_ZPred xZPred1)
    ++(calc_exp_ZPred xZPred2)
calc_exp_ZPred (ZImplies xZPred1 xZPred2)
  = (calc_exp_ZPred xZPred1)
    ++(calc_exp_ZPred xZPred2)
calc_exp_ZPred (ZIff xZPred1 xZPred2)
  = (calc_exp_ZPred xZPred1)
    ++(calc_exp_ZPred xZPred2)
calc_exp_ZPred (ZNot xZPred)
  = (calc_exp_ZPred xZPred)
calc_exp_ZPred (ZExists xZGenFilt_lst xZPred)
  = (calc_exp_ZPred xZPred)
    ++(concat$ map calc_exp_ZGenFilt xZGenFilt_lst)
calc_exp_ZPred (ZExists_1 xZGenFilt_lst xZPred)
  = (calc_exp_ZPred xZPred)
    ++(concat$ map calc_exp_ZGenFilt xZGenFilt_lst)
calc_exp_ZPred (ZForall xZGenFilt_lst xZPred)
  = (calc_exp_ZPred xZPred)
    ++(concat$ map calc_exp_ZGenFilt xZGenFilt_lst)
calc_exp_ZPred (ZPLet xZExpr_lst xZPred)
  = (calc_exp_ZPred xZPred)
    ++(concat$  map (calc_exp_ZExpr ) (map snd xZExpr_lst))
calc_exp_ZPred (ZEqual xZExpr1 xZExpr2)
  = (calc_exp_ZExpr xZExpr1)
    ++(calc_exp_ZExpr xZExpr2)
calc_exp_ZPred (ZMember xZExpr1 xZExpr2)
  = (calc_exp_ZExpr xZExpr1)
    ++(calc_exp_ZExpr xZExpr2)
calc_exp_ZPred (ZPre xZSExpr)
  = calc_exp_ZSExpr xZSExpr
calc_exp_ZPred (ZPSchema xZSExpr)
  = (calc_exp_ZSExpr xZSExpr)

calc_exp_ZSExpr (ZSchema xZGenFilt_lst)
  = (concat $ map calc_exp_ZGenFilt xZGenFilt_lst)
calc_exp_ZSExpr (ZSRef s x xZReplace_lst)
  = (concat$ map calc_exp_ZReplace xZReplace_lst)
calc_exp_ZSExpr (ZS1 sa xZSExpr)
  = calc_exp_ZSExpr xZSExpr
calc_exp_ZSExpr (ZS2 x xZSExpr1 xZSExpr2)
  = (calc_exp_ZSExpr xZSExpr1)
    ++(calc_exp_ZSExpr xZSExpr2)
calc_exp_ZSExpr (ZSHide xZSExpr xZVar_lst)
  = ( calc_exp_ZSExpr xZSExpr)
calc_exp_ZSExpr (ZSExists xZGenFilt_lst xZSExpr)
  = (concat $ map calc_exp_ZGenFilt xZGenFilt_lst)
    ++(calc_exp_ZSExpr xZSExpr)
calc_exp_ZSExpr (ZSExists_1 xZGenFilt_lst xZSExpr)
  = (concat $ map calc_exp_ZGenFilt xZGenFilt_lst)
    ++(calc_exp_ZSExpr xZSExpr)
calc_exp_ZSExpr (ZSForall xZGenFilt_lst xZSExpr)
  = (concat $ map calc_exp_ZGenFilt xZGenFilt_lst)
    ++(calc_exp_ZSExpr xZSExpr)

calc_exp_ZReplace (ZRename xZVar1 xZVar2)
  = []
calc_exp_ZReplace (ZAssign v xZExpr)
  = (calc_exp_ZExpr xZExpr)


calc_exp_ZBranch (ZBranch0 v)
  = []
calc_exp_ZBranch (ZBranch1 v xZExpr)
  = (calc_exp_ZExpr xZExpr)

calc_exp_ZPara (ZGivenSetDecl x)
  = []
calc_exp_ZPara (ZSchemaDef x xZSExpr)
  = (calc_exp_ZSExpr xZSExpr)
calc_exp_ZPara (Process xProcDecl)
  = calc_exp_ProcDecl xProcDecl

calc_exp_CDecl (CChan xname)
  = []
calc_exp_CDecl (CChanDecl xname xZExpr)
  = (calc_exp_ZExpr xZExpr)
calc_exp_CDecl (CGenChanDecl xname xname1 xZExpr)
  = (calc_exp_ZExpr xZExpr)


calc_exp_ProcDecl (CProcess xname xProcessDef)
  = (calc_exp_ProcessDef xProcessDef)
calc_exp_ProcDecl (CParamProcess xname xZName_lst xProcessDef)
  = (calc_exp_ProcessDef xProcessDef)
calc_exp_ProcDecl (CGenProcess xname xZName_lst xProcessDef)
  = (calc_exp_ProcessDef xProcessDef)

calc_exp_ProcessDef (ProcDefSpot xZGenFilt_lst xProcessDef)
  = (calc_exp_ProcessDef xProcessDef)
    ++(concat $ map (calc_exp_ZGenFilt ) xZGenFilt_lst)
calc_exp_ProcessDef (ProcDefIndex xZGenFilt_lst xProcessDef)
  = (concat $ map (calc_exp_ZGenFilt ) xZGenFilt_lst)
    ++(calc_exp_ProcessDef xProcessDef)
calc_exp_ProcessDef (ProcDef c)
  = (calc_exp_CProc  c)

calc_exp_CProc (CRepSeqProc xZGenFilt_lst xCProc)
  = (calc_exp_CProc xCProc)
    ++(concat $ map (calc_exp_ZGenFilt ) xZGenFilt_lst)
calc_exp_CProc (CRepExtChProc xZGenFilt_lst xCProc)
  = (calc_exp_CProc xCProc)
    ++(concat $ map (calc_exp_ZGenFilt ) xZGenFilt_lst)
calc_exp_CProc (CRepIntChProc xZGenFilt_lst xCProc)
  = (calc_exp_CProc xCProc)
    ++(concat $ map (calc_exp_ZGenFilt ) xZGenFilt_lst)
calc_exp_CProc (CRepParalProc xCSExp xZGenFilt_lst xCProc)
  = (calc_exp_CProc xCProc)
    ++(concat $ map (calc_exp_ZGenFilt ) xZGenFilt_lst)
calc_exp_CProc (CRepInterlProc xZGenFilt_lst xCProc)
  = (calc_exp_CProc xCProc)
    ++(concat $ map (calc_exp_ZGenFilt ) xZGenFilt_lst)
calc_exp_CProc (CHide xCProc xCSExp)
  = (calc_exp_CProc xCProc)
calc_exp_CProc (CExtChoice xCProc1 xCProc2)
  = (calc_exp_CProc xCProc1)
    ++(calc_exp_CProc xCProc2)
calc_exp_CProc (CIntChoice xCProc1 xCProc2)
  = (calc_exp_CProc xCProc1)
    ++(calc_exp_CProc xCProc2)
calc_exp_CProc (CParParal xCSExp xCProc1 xCProc2)
  = (calc_exp_CProc xCProc1)
    ++(calc_exp_CProc xCProc2)
calc_exp_CProc (CInterleave xCProc1 xCProc2)
  = (calc_exp_CProc xCProc1)
    ++(calc_exp_CProc xCProc2)
calc_exp_CProc (CGenProc xname xZExpr_lst)
  = (concat$  map (calc_exp_ZExpr ) xZExpr_lst)
calc_exp_CProc (CParamProc xname xZExpr_lst)
  = (concat$  map (calc_exp_ZExpr ) xZExpr_lst)
calc_exp_CProc (CProcRename xname xComm_lst1 xComm_lst2)
  = (concat$ map calc_exp_Comm xComm_lst1)
    ++(concat $ map calc_exp_Comm xComm_lst2)
calc_exp_CProc (CSeq xCProc1 xCProc2)
  = (calc_exp_CProc xCProc1)
    ++(calc_exp_CProc xCProc2)
calc_exp_CProc (CSimpIndexProc xname xZExpr_lst)
  = (concat$ map (calc_exp_ZExpr ) xZExpr_lst)
calc_exp_CProc (CircusProc xname)
  = []
calc_exp_CProc (ProcMain xZPara xPPar_lst xCAction)
  = (calc_exp_ZPara xZPara)
    ++(calc_exp_CAction xCAction)
    ++(concat $ map (calc_exp_PPar ) xPPar_lst)
calc_exp_CProc (ProcStalessMain xPPar_lst xCAction)
  = (calc_exp_CAction xCAction)
    ++(concat $ map (calc_exp_PPar ) xPPar_lst)

-- calc_exp_PPar (ProcZPara xZPara) = (calc_exp_ZPara xZPara)
calc_exp_PPar (CParAction xname xParAction)
  = (calc_exp_ParAction xParAction)
-- calc_exp_PPar (CNameSet xname xZExpr_lst) = (concat $ map (calc_exp_ZExpr ) xZExpr_lst)

calc_exp_ParAction (CircusAction xCAction)
  = (calc_exp_CAction xCAction)
calc_exp_ParAction (ParamActionDecl xZGenFilt_lst xParAction)
  = (concat $ map calc_exp_ZGenFilt xZGenFilt_lst)
    ++(calc_exp_ParAction xParAction)

-- calc_exp_CAction (CActionSchemaExpr xZSExpr) = (calc_exp_ZSExpr xZSExpr)
calc_exp_CAction (CActionCommand xCCommand)
  = calc_exp_CCommand xCCommand
calc_exp_CAction (CActionName xname)
  = []
calc_exp_CAction (CSPSkip )
  = []
calc_exp_CAction (CSPStop )
  = []
calc_exp_CAction (CSPChaos)
  = []
calc_exp_CAction (CSPCommAction xComm xCAction)
  = (calc_exp_Comm xComm)
    ++(calc_exp_CAction xCAction)
calc_exp_CAction (CSPGuard xZPred xCAction)
  = (calc_exp_CAction xCAction)
    ++(calc_exp_ZPred xZPred)
calc_exp_CAction (CSPSeq xCAction1 xCAction2)
  = (calc_exp_CAction xCAction1)
    ++(calc_exp_CAction xCAction2)
calc_exp_CAction (CSPExtChoice xCAction1 xCAction2)
  = (calc_exp_CAction xCAction1)
    ++(calc_exp_CAction xCAction2)
calc_exp_CAction (CSPIntChoice xCAction1 xCAction2)
  = (calc_exp_CAction xCAction1)
    ++(calc_exp_CAction xCAction2)
calc_exp_CAction (CSPNSParal x1 xCSExp x2 xCAction1 xCAction2)
  = (calc_exp_CAction xCAction1)
    ++(calc_exp_CAction xCAction2)
calc_exp_CAction (CSPParal xCSExp xCAction1 xCAction2)
  = (calc_exp_CAction xCAction1)
    ++(calc_exp_CAction xCAction2)
calc_exp_CAction (CSPNSInter xZExpr_lst xZExpr_lst2 xCAction1 xCAction2)
  = (calc_exp_CAction xCAction1)
    ++(calc_exp_CAction xCAction2)
calc_exp_CAction (CSPInterleave xCAction1 xCAction2)
  = (calc_exp_CAction xCAction1)
    ++(calc_exp_CAction xCAction2)
calc_exp_CAction (CSPHide xCAction xCSExp)
  = (calc_exp_CAction xCAction)
calc_exp_CAction (CSPParAction xname xZExpr_lst)
  = (concat $ map (calc_exp_ZExpr ) xZExpr_lst)
calc_exp_CAction (CSPRenAction xname xCReplace)
  = calc_exp_CReplace xCReplace
calc_exp_CAction (CSPRecursion xname xCAction)
  = (calc_exp_CAction xCAction)
calc_exp_CAction (CSPUnfAction xname xCAction)
  = (calc_exp_CAction xCAction)
calc_exp_CAction (CSPUnParAction xZGenFilt_lst xCAction xname)
  = (calc_exp_CAction xCAction)
    ++(concat $ map (calc_exp_ZGenFilt ) xZGenFilt_lst)
calc_exp_CAction (CSPRepSeq xZGenFilt_lst xCAction)
  = (calc_exp_CAction xCAction)
    ++(concat $ map calc_exp_ZGenFilt xZGenFilt_lst)
calc_exp_CAction (CSPRepExtChoice xZGenFilt_lst xCAction)
  = (calc_exp_CAction xCAction)
    ++(concat $ map calc_exp_ZGenFilt xZGenFilt_lst)
calc_exp_CAction (CSPRepIntChoice xZGenFilt_lst xCAction)
  = (calc_exp_CAction xCAction)
    ++(concat $ map calc_exp_ZGenFilt xZGenFilt_lst)
calc_exp_CAction (CSPRepParalNS xCSExp xZGenFilt_lst xZExpr_lst xCAction)
  = (calc_exp_CAction xCAction)
    ++(concat $ map calc_exp_ZGenFilt xZGenFilt_lst)
    ++(concat $ map (calc_exp_ZExpr ) xZExpr_lst)
calc_exp_CAction (CSPRepParal xCSExp xZGenFilt_lst xCAction)
  = (calc_exp_CAction xCAction)
    ++(concat $ map calc_exp_ZGenFilt xZGenFilt_lst)
calc_exp_CAction (CSPRepInterlNS xZGenFilt_lst xZExpr_lst xCAction)
  = (calc_exp_CAction xCAction)
    ++(concat $ map calc_exp_ZGenFilt xZGenFilt_lst)
    ++(concat $ map (calc_exp_ZExpr ) xZExpr_lst)
calc_exp_CAction (CSPRepInterl xZGenFilt_lst xCAction)
  = (calc_exp_CAction xCAction)
    ++(concat $ map calc_exp_ZGenFilt xZGenFilt_lst)

calc_exp_Comm (ChanComm xname xCParameter_lst)
  = (concat $ map calc_exp_CParameter xCParameter_lst)
calc_exp_Comm (ChanGenComm xname xZExpr_lst xCParameter_lst)
  = (concat $ map calc_exp_CParameter xCParameter_lst)
    ++(concat $ map (calc_exp_ZExpr ) xZExpr_lst)

calc_exp_CParameter (ChanInp xname)
  = []
calc_exp_CParameter (ChanInpPred xname xZPred)
  = (calc_exp_ZPred xZPred)
calc_exp_CParameter (ChanOutExp xZExpr)
  = (calc_exp_ZExpr xZExpr)
calc_exp_CParameter (ChanDotExp xZExpr)
  = (calc_exp_ZExpr xZExpr)

calc_exp_CCommand (CAssign xZVar_lst xZExpr_lst)
  = (concat $ map (calc_exp_ZExpr ) xZExpr_lst)
calc_exp_CCommand (CIf xCGActions)
  = (calc_exp_CGActions xCGActions)
calc_exp_CCommand (CVarDecl xZGenFilt_lst xCAction)
  = (calc_exp_CAction xCAction)
    ++(concat $ map calc_exp_ZGenFilt xZGenFilt_lst)
calc_exp_CCommand (CValDecl xZGenFilt_lst xCAction)
  = (calc_exp_CAction xCAction)
    ++(concat $ map calc_exp_ZGenFilt xZGenFilt_lst)
calc_exp_CCommand (CResDecl xZGenFilt_lst xCAction)
  = (calc_exp_CAction xCAction)
    ++(concat $ map calc_exp_ZGenFilt xZGenFilt_lst)
calc_exp_CCommand (CVResDecl xZGenFilt_lst xCAction)
  = (calc_exp_CAction xCAction)
    ++(concat$ map calc_exp_ZGenFilt xZGenFilt_lst)
calc_exp_CCommand (CAssumpt xZName_lst xZPred1 xZPred2)
  = (calc_exp_ZPred xZPred1)
    ++(calc_exp_ZPred xZPred2)
calc_exp_CCommand (CAssumpt1 xZName_lst xZPred)
  = (calc_exp_ZPred xZPred)
calc_exp_CCommand (CPrefix xZPred1 xZPred2)
  = (calc_exp_ZPred xZPred1)
    ++(calc_exp_ZPred xZPred2)
calc_exp_CCommand (CPrefix1 xZPred)
  = (calc_exp_ZPred xZPred)
calc_exp_CCommand (CommandBrace xZPred)
  = (calc_exp_ZPred xZPred)
calc_exp_CCommand (CommandBracket xZPred)
  = (calc_exp_ZPred xZPred)

calc_exp_CGActions (CircGAction xZPred xCAction)
  = (calc_exp_CAction xCAction)
    ++(calc_exp_ZPred xZPred)
calc_exp_CGActions (CircThenElse xCGActions1 xCGActions2)
  = (calc_exp_CGActions xCGActions1)
    ++(calc_exp_CGActions xCGActions2)

calc_exp_CReplace (CRename xZVar_lst xZVar_lst1)
  = []
calc_exp_CReplace (CRenameAssign xZVar_lst xZVar_lst1)
  = []



\end{code}
