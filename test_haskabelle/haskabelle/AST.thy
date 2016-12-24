theory AST
imports Prelude
begin
 
type_synonym GivenValue = string
 
type_synonym ZInt = int
 
type_synonym ZDecor = string
 
type_synonym ZVar = "string * (ZDecor list)"
 
type_synonym GivenSet = ZVar
 
type_synonym ZName = string
 
datatype ZReln = ZLessThan
               | ZLessThanEq
               | ZGreaterThan
               | ZGreaterThanEq
               | ZSubset
               | ZSubsetEq
               | ZPartition
               | ZPrefix
               | ZSuffix
               | ZInSeq
               | ZNeq
               | ZNotin
 
datatype ZFunc1 = ZDom
                | ZRan
                | ZSizeof
                | ZBigCup
                | ZBigCap
                | ZId
                | ZRev
                | ZHead
                | ZLast
                | ZTail
                | ZFront
                | ZSquash
                | ZDCat
                | ZSucc
                | ZNegate
                | ZMax
                | ZMin
                | ZInv
                | ZStar
                | ZClosure
                | ZSum
 
datatype ZFunc2 = ZMapsto
                | ZUpto
                | ZPlus
                | ZMinus
                | ZTimes
                | ZDiv
                | ZMod
                | ZUnion
                | ZInter
                | ZSetMinus
                | ZComp
                | ZCirc
                | ZDRes
                | ZRRes
                | ZNDRes
                | ZNRRes
                | ZRelImg
                | ZOPlus
                | ZCat
                | ZExtract
                | ZFilter
                | ZFirst
                | ZSecond
 
datatype ZStrange = ZIter
                  | ZDisjoint
 
datatype ZSName = ZSPlain string
                | ZSDelta string
                | ZSXi string
 
datatype ZS1 = ZSPre
             | ZSNot
 
datatype ZS2 = ZSAnd
             | ZSOr
             | ZSImplies
             | ZSIff
             | ZSProject
             | ZSSemi
             | ZSPipe
 
datatype ZGenFilt = Include ZSExpr
                  | Choose ZVar ZExpr
                  | Check ZPred
                  | Evaluate ZVar ZExpr ZExpr
and      ZExpr = ZVar ZVar
               | ZInt ZInt
               | ZGiven GivenValue
               | ZFree0 ZVar
               | ZFree1 ZVar ZExpr
               | ZTuple "ZExpr list"
               | ZBinding "(ZVar * ZExpr) list"
               | ZSetDisplay "ZExpr list"
               | ZSeqDisplay "ZExpr list"
               | ZIntSet "ZInt option" "ZInt option"
               | ZGenerator ZReln ZExpr
               | ZCross "ZExpr list"
               | ZFreeType ZVar "ZBranch list"
               | ZPowerSet ZExpr bool bool
               | ZFuncSet ZExpr ZExpr bool bool bool bool bool bool bool
               | ZSetComp "ZGenFilt list" "ZExpr option"
               | ZLambda "ZGenFilt list" ZExpr
               | ZESchema ZSExpr
               | ZGivenSet GivenSet
               | ZUniverse
               | ZCall ZExpr ZExpr
               | ZReln ZReln
               | ZFunc1 ZFunc1
               | ZFunc2 ZFunc2
               | ZStrange ZStrange
               | ZMu "ZGenFilt list" "ZExpr option"
               | ZELet "(ZVar * ZExpr) list" ZExpr
               | ZIf_Then_Else ZPred ZExpr ZExpr
               | ZSelect ZExpr ZVar
               | ZTheta ZSExpr
and      ZPred = ZFalse "ZPred list"
               | ZTrue "ZPred list"
               | ZAnd ZPred ZPred
               | ZOr ZPred ZPred
               | ZImplies ZPred ZPred
               | ZIff ZPred ZPred
               | ZNot ZPred
               | ZExists "ZGenFilt list" ZPred
               | ZExists_1 "ZGenFilt list" ZPred
               | ZForall "ZGenFilt list" ZPred
               | ZPLet "(ZVar * ZExpr) list" ZPred
               | ZEqual ZExpr ZExpr
               | ZMember ZExpr ZExpr
               | ZPre ZSExpr
               | ZPSchema ZSExpr
and      ZSExpr = ZSchema "ZGenFilt list"
                | ZSRef ZSName "ZDecor list" "ZReplace list"
                | ZS1 ZS1 ZSExpr
                | ZS2 ZS2 ZSExpr ZSExpr
                | ZSHide ZSExpr "ZVar list"
                | ZSExists "ZGenFilt list" ZSExpr
                | ZSExists_1 "ZGenFilt list" ZSExpr
                | ZSForall "ZGenFilt list" ZSExpr
and      ZReplace = ZRename ZVar ZVar
                  | ZAssign ZVar ZExpr
and      ZBranch = ZBranch0 ZVar
                 | ZBranch1 ZVar ZExpr
 
 
type_synonym ZValue = ZExpr
 
(* 
datatype CDecl = CChan ZName
               | CChanDecl ZName ZExpr
               | CGenChanDecl ZName ZName ZExpr
 
datatype CSExp = CSExpr ZName
               | CSEmpty
               | CChanSet "ZName list"
               | ChanSetUnion CSExp CSExp
               | ChanSetInter CSExp CSExp
               | ChanSetDiff CSExp CSExp
 
datatype NSExp = NSExpEmpty
               | NSExprMult "ZName list"
               | NSExprSngl ZName
               | NSExprParam ZName "ZExpr list"
               | NSUnion NSExp NSExp
               | NSIntersect NSExp NSExp
               | NSHide NSExp NSExp
               | NSBigUnion ZExpr*)
 
datatype CParameter = ChanInp ZName
                    | ChanInpPred ZName ZPred
                    | ChanOutExp ZExpr
                    | ChanDotExp ZExpr
 
datatype Comm = ChanComm ZName "CParameter list"
              | ChanGenComm ZName "ZExpr list" "CParameter list"
 
datatype CReplace = CRename "ZVar list" "ZVar list"
                  | CRenameAssign "ZVar list" "ZVar list"
 
datatype ParAction = CircusAction CAction
                  (* | ParamActionDecl "ZGenFilt list" ParAction*)
and      CAction = (*CActionSchemaExpr ZSExpr
                 | CActionCommand CCommand
                 | CActionName ZName*)
                  CSPSkip
                 | CSPStop
                 | CSPChaos
                 | CSPCommAction Comm CAction
                 | CSPSeq CAction CAction
                (* | CSPGuard ZPred CAction
                 | CSPExtChoice CAction CAction
                 | CSPIntChoice CAction CAction
                 | CSPNSParal NSExp CSExp NSExp CAction CAction
                 | CSPParal CSExp CAction CAction
                 | CSPNSInter NSExp NSExp CAction CAction
                 | CSPInterleave CAction CAction
                 | CSPHide CAction CSExp
                 *)| CSPParAction ZName "ZExpr list"
                 (*| CSPRenAction ZName CReplace
                 | CSPRecursion ZName CAction
                 | CSPUnParAction "ZGenFilt list" CAction ZName*)
                 | CSPRepSeq "ZGenFilt list" CAction
                (* | CSPRepExtChoice "ZGenFilt list" CAction
                 | CSPRepIntChoice "ZGenFilt list" CAction
                 | CSPRepParalNS CSExp "ZGenFilt list" NSExp CAction
                 | CSPRepParal CSExp "ZGenFilt list" CAction
                 | CSPRepInterlNS "ZGenFilt list" NSExp CAction
                 | CSPRepInterl "ZGenFilt list" CAction*)
(*and      CCommand = CAssign "ZVar list" "ZExpr list"
                  | CIf CGActions
                  | CVarDecl "ZGenFilt list" CAction
                  | CAssumpt "ZName list" ZPred ZPred
                  | CAssumpt1 "ZName list" ZPred
                  | CPrefix ZPred ZPred
                  | CPrefix1 ZPred
                  | CommandBrace ZPred
                  | CommandBracket ZPred
                  | CValDecl "ZGenFilt list" CAction
                  | CResDecl "ZGenFilt list" CAction
                  | CVResDecl "ZGenFilt list" CAction
and      CGActions = CircGAction ZPred CAction
                   | CircThenElse CGActions CGActions
                   | CircElse ParAction*)
 (*
datatype ZPara = ZGivenSetDecl GivenSet
               | ZSchemaDef ZSName ZSExpr
               | ZAbbreviation ZVar ZExpr
               | ZFreeTypeDef ZVar "ZBranch list"
               | ZPredicate ZPred
               | ZAxDef "ZGenFilt list"
               | ZGenDef "ZGenFilt list"
               | ZMachineDef string string string "string list"
               | CircChannel "CDecl list"
               | CircChanSet ZName CSExp
               | Process ProcDecl
and      ProcDecl = CProcess ZName ProcessDef
                  | CParamProcess ZName "ZName list" ProcessDef
                  | CGenProcess ZName "ZName list" ProcessDef
and      ProcessDef = ProcDefSpot "ZGenFilt list" ProcessDef
                    | ProcDefIndex "ZGenFilt list" ProcessDef
                    | ProcDef CProc
and      CProc = CRepSeqProc "ZGenFilt list" CProc
               | CRepExtChProc "ZGenFilt list" CProc
               | CRepIntChProc "ZGenFilt list" CProc
               | CRepParalProc CSExp "ZGenFilt list" CProc
               | CRepInterlProc "ZGenFilt list" CProc
               | CHide CProc CSExp
               | CExtChoice CProc CProc
               | CIntChoice CProc CProc
               | CParParal CSExp CProc CProc
               | CInterleave CProc CProc
               | CGenProc ZName "ZExpr list"
               | CParamProc ZName "ZExpr list"
               | CProcRename ZName "Comm list" "Comm list"
               | CSeq CProc CProc
               | CSimpIndexProc ZName "ZExpr list"
               | CircusProc ZName
               | ProcMain ZPara "PPar list" CAction
               | ProcStalessMain "PPar list" CAction
and      PPar = ProcZPara ZPara
              | CParAction ZName ParAction
              | CNameSet ZName NSExp
 *)
 
datatype ZTerm = ZExpr ZExpr
               | ZPred ZPred
               | ZSExpr ZSExpr
               | ZNull

end
