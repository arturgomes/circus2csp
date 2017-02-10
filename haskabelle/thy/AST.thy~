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
               | ZTuple "ZExpr list"
               | ZBinding "(ZVar * ZExpr) list"
               | ZSetDisplay "ZExpr list"
               | ZSeqDisplay "ZExpr list"
               | ZCross "ZExpr list"
               | ZSetComp "ZGenFilt list" "ZExpr option"
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

 
type_synonym ZFSet = "ZExpr list"
 
datatype ZSName = ZSPlain string
                | ZSDelta string
                | ZSXi string
 
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
               | NSBigUnion ZExpr
 
datatype CParameter = ChanInp ZName
                    | ChanInpPred ZName ZPred
                    | ChanOutExp ZExpr
                    | ChanDotExp ZExpr
 
datatype Comm = ChanComm ZName "CParameter list"
              | ChanGenComm ZName "ZExpr list" "CParameter list"
 
datatype CAction = CSPSkip
                 | CSPStop
                 | CSPChaos
                 | CSPCommAction Comm CAction
                 | CSPSeq CAction CAction
                 | CSPExtChoice CAction CAction
 
datatype ParAction = CircusAction CAction
                   | ParamActionDecl "ZGenFilt list" ParAction
 
datatype ZPara = ZSchemaDef ZSName ZSExpr
               | Process ProcDecl
and      ProcDecl = CProcess ZName ProcessDef
                  | CParamProcess ZName "ZName list" ProcessDef
                  | CGenProcess ZName "ZName list" ProcessDef
and      ProcessDef = ProcDefSpot "ZGenFilt list" ProcessDef
                    | ProcDef CProc
and      CProc = ProcMain ZPara "PPar list" CAction
               | ProcStalessMain "PPar list" CAction
and      PPar = ProcZPara ZPara
              | CParAction ZName ParAction
              | CNameSet ZName NSExp
 
type_synonym ZSpec = "ZPara list"
 
type_synonym CProgram = "ZPara list"

end
