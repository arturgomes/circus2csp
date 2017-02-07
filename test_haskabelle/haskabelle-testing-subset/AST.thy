theory AST
imports Prelude
begin
 
type_synonym GivenValue = string
 
type_synonym ZInt = int
 
type_synonym ZDecor = string
 
type_synonym ZVar = "string * (ZDecor list)"
 
type_synonym GivenSet = ZVar
 
type_synonym ZName = string
 
datatype ZGenFilt = Choose ZVar ZExpr
                  | Check ZPred
                  | Evaluate ZVar ZExpr ZExpr
and      ZExpr = ZVar ZVar
               | ZInt ZInt
               | ZSetComp "ZGenFilt list" "ZExpr option"
               | ZBinding "(ZVar * ZExpr) list"
               | ZSetDisplay "ZExpr list"
               | ZSeqDisplay "ZExpr list"
               | ZTuple "ZExpr list"
               | ZCross "ZExpr list"
               | ZCall ZExpr ZExpr
and      ZPred = ZFalse "ZPred list"
               | ZTrue "ZPred list"
               | ZAnd ZPred ZPred
               | ZPSchema ZSExpr
and      ZSExpr = ZSchema "ZGenFilt list"
 
primrec reason :: "ZPred \<Rightarrow> ZPred list"
where
  "reason (ZTrue x) = x"
| "reason (ZFalse x) = x"

 
primrec update_reason :: "ZPred list \<Rightarrow> ZPred \<Rightarrow> ZPred"
where
  "update_reason x (ZTrue _) = (ZTrue x)"
| "update_reason x (ZFalse _) = (ZFalse x)"

 
datatype ZSName = ZSPlain string
                | ZSDelta string
                | ZSXi string
 
datatype CSExp = CSExpr ZName
               | CSEmpty
              | CChanSet "ZName list"
              (*  | ChanSetUnion CSExp CSExp
               | ChanSetInter CSExp CSExp
               | ChanSetDiff CSExp CSExp*)
 
datatype NSExp = NSExpEmpty
               (*| NSExprMult "ZName list"
               | NSExprSngl ZName
               | NSUnion NSExp NSExp
               | NSIntersect NSExp NSExp
               | NSHide NSExp NSExp*)
               | NSExprParam ZName "ZExpr list"
               | NSBigUnion ZExpr
 
datatype CParameter = ChanInp ZName
                    | ChanInpPred ZName ZPred
                    | ChanOutExp ZExpr
                    | ChanDotExp ZExpr
 
datatype Comm = ChanComm ZName "CParameter list"
             (* | ChanGenComm ZName "ZExpr list" "CParameter list"*)
 
datatype CReplace = CRename "ZVar list" "ZVar list"
                  | CRenameAssign "ZVar list" "ZVar list"
 
datatype      CAction = (*CActionCommand CCommand*)
                  CActionName ZName
                 | CSPSkip
                 | CSPStop
                 | CSPChaos
                 | CSPCommAction Comm CAction
                 | CSPGuard ZPred CAction
                 | CSPSeq CAction CAction
                 | CSPExtChoice CAction CAction
                 | CSPIntChoice CAction CAction
                 | CSPNSParal NSExp CSExp NSExp CAction CAction
                (* | CSPParal CSExp CAction CAction*)
                 | CSPNSInter NSExp NSExp CAction CAction
                (* | CSPInterleave CAction CAction*)
                 | CSPHide CAction CSExp
                 | CSPParAction ZName "ZExpr list"
               (*  | CSPRenAction ZName CReplace*)
                 | CSPRecursion ZName CAction
                 | CSPUnParAction "ZGenFilt list" CAction ZName
                 | CSPRepSeq "ZGenFilt list" CAction
                 | CSPRepExtChoice "ZGenFilt list" CAction
                 | CSPRepIntChoice "ZGenFilt list" CAction
                 | CSPRepParalNS CSExp "ZGenFilt list" NSExp CAction
                 | CSPRepParal CSExp "ZGenFilt list" CAction
                 | CSPRepInterlNS "ZGenFilt list" NSExp CAction
                 | CSPRepInterl "ZGenFilt list" CAction

datatype      CGActions = CircGAction ZPred CAction
                 | CircThenElse CGActions CGActions
                  (* | CircElse ParAction*)


datatype      CCommand = CAssign "ZVar list" "ZExpr list"
                  | CIf CGActions
                  | CVarDecl "ZGenFilt list" CAction
                  (*| CAssumpt "ZName list" ZPred ZPred
                  | CAssumpt1 "ZName list" ZPred
                  | CPrefix ZPred ZPred
                  | CPrefix1 ZPred*)
                (*  | CommandBrace ZPred
                  | CommandBracket ZPred *)
                  | CValDecl "ZGenFilt list" CAction
                 (* | CResDecl "ZGenFilt list" CAction
                  | CVResDecl "ZGenFilt list" CAction*)

datatype ParAction = CircusAction CAction
                   | ParamActionDecl "ZGenFilt list" ParAction

datatype ZPara = Process ProcDecl
               | ZSchemaDef ZSName ZSExpr
and      ProcDecl = CProcess ZName ProcessDef
                  | CParamProcess ZName "ZName list" ProcessDef
                  | CGenProcess ZName "ZName list" ProcessDef
and      ProcessDef = ProcDefSpot "ZGenFilt list" ProcessDef
                    | ProcDef CProc
and      CProc = CHide CProc CSExp
               | CExtChoice CProc CProc
               | CIntChoice CProc CProc
               | CParParal CSExp CProc CProc
              (* | CInterleave CProc CProc
               | CGenProc ZName "ZExpr list"
               | CParamProc ZName "ZExpr list"
               | CProcRename ZName "Comm list" "Comm list"
               | CSeq CProc CProc
               | CSimpIndexProc ZName "ZExpr list"
               | CircusProc ZName*)
               | ProcMain ZPara "PPar list" CAction
               | ProcStalessMain "PPar list" CAction
and      PPar = ProcZPara ZPara
              | CParAction ZName ParAction
              | CNameSet ZName NSExp
 
type_synonym ZSpec = "ZPara list"
 
type_synonym CProgram = "ZPara list"
 
datatype ZTerm = ZExpr ZExpr
               | ZPred ZPred
               | ZNull

end
