theory AST
imports Prelude
begin
 
type_synonym GivenValue = string
 
type_synonym ZInt = int
 
type_synonym ZDecor = string
 
type_synonym ZVar = "string * (ZDecor list)"
 
type_synonym GivenSet = ZVar
 
type_synonym ZName = string
 
fun make_zvar :: "string \<Rightarrow> ZDecor list \<Rightarrow> ZVar"
where
  "make_zvar s dl = (s, dl)"

 
fun decorate_zvar :: "ZVar \<Rightarrow> ZDecor list \<Rightarrow> ZVar"
where
  "decorate_zvar (s, dl) d = (s, (dl @ d))"

 
fun prime_zvar :: "ZVar \<Rightarrow> ZVar"
where
  "prime_zvar v = decorate_zvar v [''''']"

 
fun unprime_zvar :: "ZVar \<Rightarrow> ZVar"
where
  "unprime_zvar (n, [''''']) = (n, Nil)"

 
fun string_to_zvar :: "string \<Rightarrow> ZVar"
where
  "string_to_zvar s = make_zvar s Nil"

 
definition get_zvar_name :: "ZVar \<Rightarrow> string"
where
  "get_zvar_name = fst"

 
definition get_zvar_decor :: "ZVar \<Rightarrow> ZDecor list"
where
  "get_zvar_decor = snd"

 
fun is_unprimed_zvar :: "ZVar \<Rightarrow> bool"
where
  "is_unprimed_zvar (_, Nil) = True"
| "is_unprimed_zvar _ = False"

 
fun is_primed_zvar :: "ZVar \<Rightarrow> bool"
where
  "is_primed_zvar (_, [''''']) = True"
| "is_primed_zvar _ = False"

 
fun is_input_zvar :: "ZVar \<Rightarrow> bool"
where
  "is_input_zvar (_, [''?'']) = True"
| "is_input_zvar _ = False"

 
fun is_output_zvar :: "ZVar \<Rightarrow> bool"
where
  "is_output_zvar (_, [''!'']) = True"
| "is_output_zvar _ = False"

 
fun show_zvar :: "ZVar \<Rightarrow> string"
where
  "show_zvar (s, dl) = (s @ concat dl)"

 
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
 
primrec baseset :: "ZExpr \<Rightarrow> ZExpr"
where
  "baseset (ZPowerSet x _ _) = x"

 
primrec is_non_empty :: "ZExpr \<Rightarrow> bool"
where
  "is_non_empty (ZFuncSet _ _ _ _ _ _ _ x _) = x"
| "is_non_empty (ZPowerSet _ x _) = x"

 
primrec is_finite :: "ZExpr \<Rightarrow> bool"
where
  "is_finite (ZFuncSet _ _ _ _ _ _ _ _ x) = x"
| "is_finite (ZPowerSet _ _ x) = x"

 
primrec domset :: "ZExpr \<Rightarrow> ZExpr"
where
  "domset (ZFuncSet x _ _ _ _ _ _ _ _) = x"

 
primrec ranset :: "ZExpr \<Rightarrow> ZExpr"
where
  "ranset (ZFuncSet _ x _ _ _ _ _ _ _) = x"

 
primrec is_function :: "ZExpr \<Rightarrow> bool"
where
  "is_function (ZFuncSet _ _ x _ _ _ _ _ _) = x"

 
primrec is_total :: "ZExpr \<Rightarrow> bool"
where
  "is_total (ZFuncSet _ _ _ x _ _ _ _ _) = x"

 
primrec is_onto :: "ZExpr \<Rightarrow> bool"
where
  "is_onto (ZFuncSet _ _ _ _ x _ _ _ _) = x"

 
primrec is_one2one :: "ZExpr \<Rightarrow> bool"
where
  "is_one2one (ZFuncSet _ _ _ _ _ x _ _ _) = x"

 
primrec is_sequence :: "ZExpr \<Rightarrow> bool"
where
  "is_sequence (ZFuncSet _ _ _ _ _ _ x _ _) = x"

 
primrec update_baseset :: "ZExpr \<Rightarrow> ZExpr \<Rightarrow> ZExpr"
where
  "update_baseset x (ZPowerSet _ f2 f3) = (ZPowerSet x f2 f3)"

 
primrec update_is_non_empty :: "bool \<Rightarrow> ZExpr \<Rightarrow> ZExpr"
where
  "update_is_non_empty x (ZFuncSet f1 f2 f3 f4 f5 f6 f7 _ f9) = (ZFuncSet f1 f2 f3 f4 f5 f6 f7 x f9)"
| "update_is_non_empty x (ZPowerSet f1 _ f3) = (ZPowerSet f1 x f3)"

 
primrec update_is_finite :: "bool \<Rightarrow> ZExpr \<Rightarrow> ZExpr"
where
  "update_is_finite x (ZFuncSet f1 f2 f3 f4 f5 f6 f7 f8 _) = (ZFuncSet f1 f2 f3 f4 f5 f6 f7 f8 x)"
| "update_is_finite x (ZPowerSet f1 f2 _) = (ZPowerSet f1 f2 x)"

 
primrec update_domset :: "ZExpr \<Rightarrow> ZExpr \<Rightarrow> ZExpr"
where
  "update_domset x (ZFuncSet _ f2 f3 f4 f5 f6 f7 f8 f9) = (ZFuncSet x f2 f3 f4 f5 f6 f7 f8 f9)"

 
primrec update_ranset :: "ZExpr \<Rightarrow> ZExpr \<Rightarrow> ZExpr"
where
  "update_ranset x (ZFuncSet f1 _ f3 f4 f5 f6 f7 f8 f9) = (ZFuncSet f1 x f3 f4 f5 f6 f7 f8 f9)"

 
primrec update_is_function :: "bool \<Rightarrow> ZExpr \<Rightarrow> ZExpr"
where
  "update_is_function x (ZFuncSet f1 f2 _ f4 f5 f6 f7 f8 f9) = (ZFuncSet f1 f2 x f4 f5 f6 f7 f8 f9)"

 
primrec update_is_total :: "bool \<Rightarrow> ZExpr \<Rightarrow> ZExpr"
where
  "update_is_total x (ZFuncSet f1 f2 f3 _ f5 f6 f7 f8 f9) = (ZFuncSet f1 f2 f3 x f5 f6 f7 f8 f9)"

 
primrec update_is_onto :: "bool \<Rightarrow> ZExpr \<Rightarrow> ZExpr"
where
  "update_is_onto x (ZFuncSet f1 f2 f3 f4 _ f6 f7 f8 f9) = (ZFuncSet f1 f2 f3 f4 x f6 f7 f8 f9)"

 
primrec update_is_one2one :: "bool \<Rightarrow> ZExpr \<Rightarrow> ZExpr"
where
  "update_is_one2one x (ZFuncSet f1 f2 f3 f4 f5 _ f7 f8 f9) = (ZFuncSet f1 f2 f3 f4 f5 x f7 f8 f9)"

 
primrec update_is_sequence :: "bool \<Rightarrow> ZExpr \<Rightarrow> ZExpr"
where
  "update_is_sequence x (ZFuncSet f1 f2 f3 f4 f5 f6 _ f8 f9) = (ZFuncSet f1 f2 f3 f4 f5 f6 x f8 f9)"

 
primrec reason :: "ZPred \<Rightarrow> ZPred list"
where
  "reason (ZTrue x) = x"
| "reason (ZFalse x) = x"

 
primrec update_reason :: "ZPred list \<Rightarrow> ZPred \<Rightarrow> ZPred"
where
  "update_reason x (ZTrue _) = (ZTrue x)"
| "update_reason x (ZFalse _) = (ZFalse x)"

 
fun genfilt_names :: "ZGenFilt list \<Rightarrow> ZVar list"
where
  "genfilt_names Nil = Nil"
| "genfilt_names (Choose v _ # gfs) = (v # genfilt_names gfs)"
| "genfilt_names (Check _ # gfs) = genfilt_names gfs"
| "genfilt_names (Evaluate v _ _ # gfs) = (v # genfilt_names gfs)"
| "genfilt_names (Include s # gfs) = error (''genfilt_names called before '' @ (print s @ '' expanded.''))"

 
type_synonym ZValue = ZExpr
 
fun is_pair :: "ZValue \<Rightarrow> bool"
where
  "is_pair (ZTuple [_, _]) = True"
| "is_pair _ = False"

 
fun pair_fst :: "ZValue \<Rightarrow> ZValue"
where
  "pair_fst (ZTuple [x, _]) = x"
| "pair_fst _ = error ''pair_fst applied to non-pair value''"

 
fun pair_snd :: "ZValue \<Rightarrow> ZValue"
where
  "pair_snd (ZTuple [_, y]) = y"
| "pair_snd _ = error ''pair_snd applied to non-pair value''"

 
definition zrelations :: "ZExpr"
where
  "zrelations = ZFuncSet ZUniverse ZUniverse False False False False False False False"

 
definition ztrue
where
  "ztrue = ZTrue Nil"

 
definition zfalse
where
  "zfalse = ZFalse Nil"

 
fun isBranch0 :: "ZBranch \<Rightarrow> bool"
where
  "isBranch0 (ZBranch0 _) = True"
| "isBranch0 _ = False"

 
fun isCanonical :: "ZExpr \<Rightarrow> bool"
where
  "isCanonical (ZInt _) = True"
| "isCanonical (ZTuple v) = list_all isCanonical v"
| "isCanonical (ZGiven _) = True"
| "isCanonical (ZFree0 _) = True"
| "isCanonical (ZFree1 _ v) = isCanonical v"
| "isCanonical (ZBinding bs) = list_all (isCanonical o snd) bs"
| "isCanonical _ = False"

 
fun isDefined :: "ZExpr \<Rightarrow> bool"
where
  "isDefined (ZInt _) = True"
| "isDefined (ZIntSet _ _) = True"
| "isDefined (ZTuple v) = list_all isDefined v"
| "isDefined (ZReln _) = True"
| "isDefined (ZGiven _) = True"
| "isDefined (ZGivenSet _) = True"
| "isDefined (ZSetDisplay vs) = list_all isDefined vs"
| "isDefined (ZSeqDisplay vs) = list_all isDefined vs"
| "isDefined (ZFree0 _) = True"
| "isDefined (ZFree1 _ _) = True"
| "isDefined (ZBinding bs) = list_all (isDefined o snd) bs"
| "isDefined v = False"

 
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
               | NSBigUnion ZExpr
 
datatype CParameter = ChanInp ZName
                    | ChanInpPred ZName ZPred
                    | ChanOutExp ZExpr
                    | ChanDotExp ZExpr
 
datatype Comm = ChanComm ZName "CParameter list"
              | ChanGenComm ZName "ZExpr list" "CParameter list"
 
datatype CReplace = CRename "ZVar list" "ZVar list"
                  | CRenameAssign "ZVar list" "ZVar list"
 
datatype ParAction = CircusAction CAction
                   | ParamActionDecl "ZGenFilt list" ParAction
and      CAction = CActionSchemaExpr ZSExpr
                 | CActionCommand CCommand
                 | CActionName ZName
                 | CSPSkip
                 | CSPStop
                 | CSPChaos
                 | CSPCommAction Comm CAction
                 | CSPGuard ZPred CAction
                 | CSPSeq CAction CAction
                 | CSPExtChoice CAction CAction
                 | CSPIntChoice CAction CAction
                 | CSPNSParal NSExp CSExp NSExp CAction CAction
                 | CSPParal CSExp CAction CAction
                 | CSPNSInter NSExp NSExp CAction CAction
                 | CSPInterleave CAction CAction
                 | CSPHide CAction CSExp
                 | CSPParAction ZName "ZExpr list"
                 | CSPRenAction ZName CReplace
                 | CSPRecursion ZName CAction
                 | CSPUnParAction "ZGenFilt list" CAction ZName
                 | CSPRepSeq "ZGenFilt list" CAction
                 | CSPRepExtChoice "ZGenFilt list" CAction
                 | CSPRepIntChoice "ZGenFilt list" CAction
                 | CSPRepParalNS CSExp "ZGenFilt list" NSExp CAction
                 | CSPRepParal CSExp "ZGenFilt list" CAction
                 | CSPRepInterlNS "ZGenFilt list" NSExp CAction
                 | CSPRepInterl "ZGenFilt list" CAction
and      CCommand = CAssign "ZVar list" "ZExpr list"
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
                   | CircElse ParAction
 
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
 
primrec machName :: "ZPara \<Rightarrow> string"
where
  "machName (ZMachineDef x _ _ _) = x"

 
primrec machState :: "ZPara \<Rightarrow> string"
where
  "machState (ZMachineDef _ x _ _) = x"

 
primrec machInit :: "ZPara \<Rightarrow> string"
where
  "machInit (ZMachineDef _ _ x _) = x"

 
primrec machOps :: "ZPara \<Rightarrow> string list"
where
  "machOps (ZMachineDef _ _ _ x) = x"

 
primrec update_machName :: "string \<Rightarrow> ZPara \<Rightarrow> ZPara"
where
  "update_machName x (ZMachineDef _ f2 f3 f4) = (ZMachineDef x f2 f3 f4)"

 
primrec update_machState :: "string \<Rightarrow> ZPara \<Rightarrow> ZPara"
where
  "update_machState x (ZMachineDef f1 _ f3 f4) = (ZMachineDef f1 x f3 f4)"

 
primrec update_machInit :: "string \<Rightarrow> ZPara \<Rightarrow> ZPara"
where
  "update_machInit x (ZMachineDef f1 f2 _ f4) = (ZMachineDef f1 f2 x f4)"

 
primrec update_machOps :: "string list \<Rightarrow> ZPara \<Rightarrow> ZPara"
where
  "update_machOps x (ZMachineDef f1 f2 f3 _) = (ZMachineDef f1 f2 f3 x)"

 
type_synonym ZSpec = "ZPara list"
 
type_synonym CProgram = "ZPara list"
 
type_synonym SearchSpace = "(ZVar * int) list"
 
type_synonym GlobalDefs = "(ZVar * ZExpr) list"
 
datatype Env = Env int SearchSpace int int GlobalDefs "(ZVar * ZExpr) list"
 
primrec search_space :: "Env \<Rightarrow> int"
where
  "search_space (Env x _ _ _ _ _) = x"

 
primrec search_vars :: "Env \<Rightarrow> SearchSpace"
where
  "search_vars (Env _ x _ _ _ _) = x"

 
primrec max_search_space :: "Env \<Rightarrow> int"
where
  "max_search_space (Env _ _ x _ _ _) = x"

 
primrec max_set_size :: "Env \<Rightarrow> int"
where
  "max_set_size (Env _ _ _ x _ _) = x"

 
primrec global_values :: "Env \<Rightarrow> GlobalDefs"
where
  "global_values (Env _ _ _ _ x _) = x"

 
primrec local_values :: "Env \<Rightarrow> (ZVar * ZExpr) list"
where
  "local_values (Env _ _ _ _ _ x) = x"

 
primrec update_search_space :: "int \<Rightarrow> Env \<Rightarrow> Env"
where
  "update_search_space x (Env _ f2 f3 f4 f5 f6) = (Env x f2 f3 f4 f5 f6)"

 
primrec update_search_vars :: "SearchSpace \<Rightarrow> Env \<Rightarrow> Env"
where
  "update_search_vars x (Env f1 _ f3 f4 f5 f6) = (Env f1 x f3 f4 f5 f6)"

 
primrec update_max_search_space :: "int \<Rightarrow> Env \<Rightarrow> Env"
where
  "update_max_search_space x (Env f1 f2 _ f4 f5 f6) = (Env f1 f2 x f4 f5 f6)"

 
primrec update_max_set_size :: "int \<Rightarrow> Env \<Rightarrow> Env"
where
  "update_max_set_size x (Env f1 f2 f3 _ f5 f6) = (Env f1 f2 f3 x f5 f6)"

 
primrec update_global_values :: "GlobalDefs \<Rightarrow> Env \<Rightarrow> Env"
where
  "update_global_values x (Env f1 f2 f3 f4 _ f6) = (Env f1 f2 f3 f4 x f6)"

 
primrec update_local_values :: "(ZVar * ZExpr) list \<Rightarrow> Env \<Rightarrow> Env"
where
  "update_local_values x (Env f1 f2 f3 f4 f5 _) = (Env f1 f2 f3 f4 f5 x)"

 
fun empty_env :: "GlobalDefs \<Rightarrow> Env"
where
  "empty_env gdefs = Env 1 Nil 100000 1000 gdefs Nil"

 
definition dummy_eval_env
where
  "dummy_eval_env = (update_max_search_space 10000) (empty_env Nil)"

 
fun set_max_search_space :: "int \<Rightarrow> Env \<Rightarrow> Env"
where
  "set_max_search_space i env = (update_max_search_space i) env"

 
fun set_max_set_size :: "int \<Rightarrow> Env \<Rightarrow> Env"
where
  "set_max_set_size i env = (update_max_set_size i) env"

 
fun envPushLocal :: "ZVar \<Rightarrow> ZExpr \<Rightarrow> Env \<Rightarrow> Env"
where
  "envPushLocal v val env = (update_local_values ((v, val) # local_values env)) env"

 
fun envPushLocals :: "(ZVar * ZExpr) list \<Rightarrow> Env \<Rightarrow> Env"
where
  "envPushLocals vs env = (update_local_values (vs @ local_values env)) env"

 
fun envIsLocal :: "Env \<Rightarrow> ZVar \<Rightarrow> bool"
where
  "envIsLocal env v = member v (map fst (local_values env))"

 
fun envIsSchema :: "Env \<Rightarrow> string \<Rightarrow> bool"
where
  "envIsSchema env v = Not (null ([0 . (n, (ZESchema _)) <- global_values env,
                                       eq n (string_to_zvar v)]))"

 
datatype ZTerm = ZExpr ZExpr
               | ZPred ZPred
               | ZSExpr ZSExpr
               | ZNull

end
