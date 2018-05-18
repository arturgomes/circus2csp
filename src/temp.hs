-- I need to create types for the ZExpr
-- Concatenate the type as a string...


-- c2c: src/OmegaDefs.lhs:1756:22-69: Non-exhaustive patterns in lambda

ZVar (tt,_,_) = tt
| ZInt i = "ZInt"
| ZGiven GivenValue
| ZFree0 (tt,_,_) = "ZFree0"++
| ZFree1 (tt,_,_) ZExpr
| ZTuple [ZExpr]
| ZBinding [(ZVar,ZExpr)]
| ZSetDisplay [ZExpr]
| ZSeqDisplay [ZExpr]
| ZFSet ZFSet
| ZIntSet (Maybe ZInt) (Maybe ZInt)
| ZGenerator ZReln ZExpr
| ZCross [ZExpr]
| ZFreeType ZVar [ZBranch]
| ZPowerSet{baseset::ZExpr,
    is_non_empty::Bool,
    is_finite::Bool}
| ZFuncSet{ domset::ZExpr,
    ranset::ZExpr,
    is_function::Bool,
    is_total::Bool,
    is_onto::Bool,
    is_one2one::Bool,
    is_sequence::Bool,
    is_non_empty::Bool,
    is_finite::Bool}
| ZSetComp [ZGenFilt] (Maybe ZExpr)
| ZLambda [ZGenFilt] ZExpr
| ZESchema ZSExpr
| ZGivenSet GivenSet
| ZUniverse
| ZCall ZExpr ZExpr
| ZReln ZReln
| ZFunc1 ZFunc1
| ZFunc2 ZFunc2
| ZStrange ZStrange
| ZMu [ZGenFilt] (Maybe ZExpr)
| ZELet [(ZVar,ZExpr)] ZExpr
| ZIf_Then_Else ZPred ZExpr ZExpr
| ZSelect ZExpr (tt,_,_)
| ZTheta ZSExpr
