theory AST
imports Prelude
begin
 
type_synonym ZInt = int
 
type_synonym ZDecor = string
 
type_synonym ZVar = "string * (ZDecor list)"
 
type_synonym GivenSet = ZVar
 
type_synonym ZName = string
 
datatype ZExpr = ZVar ZVar
               | ZInt ZInt
               | ZBinding "(ZVar * ZExpr) list"
               | ZSetDisplay "ZExpr list"
               | ZSeqDisplay "ZExpr list"
               | ZTuple "ZExpr list"
               | ZCross "ZExpr list"
               | ZCall ZExpr ZExpr
datatype ZPred = ZFalse "ZPred list"
               | ZTrue "ZPred list"
               | ZAnd ZPred ZPred
                 
datatype CParameter = ChanInp ZName
                    | ChanInpPred ZName ZPred
                    | ChanOutExp ZExpr
                    | ChanDotExp ZExpr
 
datatype Comm = ChanComm ZName "CParameter list"
 
datatype CAction = CSPSkip
                 | CSPCommAction Comm CAction
      
end
