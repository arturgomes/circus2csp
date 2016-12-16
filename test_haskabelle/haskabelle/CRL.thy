theory CRL
imports AST Prelude
begin
 
fun getFV :: "'t \<Rightarrow> 't1 list"
where
  "getFV xs = Nil"

 
fun getWrtV :: "'t \<Rightarrow> 't1 list"
where
  "getWrtV xs = Nil"

 
fun crl_var_exp_par2 :: "CAction \<Rightarrow> CAction"
where
  "crl_var_exp_par2 (CSPNSParal ns1 cs ns2 (CActionCommand (CVarDecl d1 a1)) (CActionCommand (CVarDecl d2 a2))) = (case (eq d1 d2) of
                                                                                                                      True \<Rightarrow> (CActionCommand (CVarDecl d1 (CSPNSParal ns1 cs ns2 a1 a2)))
                                                                                                                    | False \<Rightarrow> (CSPNSParal ns1 cs ns2 (CActionCommand (CVarDecl d1 a1)) (CActionCommand (CVarDecl d2 a2))))"

 
fun crl_variableBlockIntroduction :: "CAction \<Rightarrow> ZVar \<Rightarrow> ZExpr \<Rightarrow> CAction"
where
  "crl_variableBlockIntroduction a x t = (let p1 = Not (member x (getFV a))
                                          in case p1 of
                                                True \<Rightarrow> CActionCommand (CVarDecl [(Choose x t)] a)
                                              | False \<Rightarrow> a)"

 
fun crl_seqSkipUnit_a :: "CAction \<Rightarrow> CAction"
where
  "crl_seqSkipUnit_a (CSPSeq CSPSkip a) = a"

 
fun crl_seqSkipUnit_b :: "CAction \<Rightarrow> CAction"
where
  "crl_seqSkipUnit_b a = (CSPSeq a CSPSkip)"

 
fun crl_parallelismExternalChoiceExpansion :: "CAction \<Rightarrow> Comm \<Rightarrow> CAction \<Rightarrow> CAction"
where
  "crl_parallelismExternalChoiceExpansion (CSPNSParal ns1 cs ns2 (CSPRepExtChoice i (CSPCommAction ai aAi)) (CSPRepExtChoice j (CSPCommAction bj aBj))) c aC = (CSPNSParal ns1 cs ns2 (CSPRepExtChoice i (CSPCommAction ai aAi)) (CSPExtChoice (CSPRepExtChoice j (CSPCommAction bj aBj)) (CSPCommAction c aC)))"

 
fun crl_hidingExpansion2 :: "CAction \<Rightarrow> ZName \<Rightarrow> CAction"
where
  "crl_hidingExpansion2 (CSPHide a (CChanSet cs)) c = (let p1 = Not (member c cs)
                                                       in case p1 of
                                                             True \<Rightarrow> (CSPHide a (ChanSetUnion (CChanSet cs) (CChanSet [c])))
                                                           | False \<Rightarrow> (CSPHide a (CChanSet cs)))"

 
fun crl_prefixHiding :: "CAction \<Rightarrow> CAction"
where
  "crl_prefixHiding (CSPHide (CSPCommAction (ChanComm c Nil) CSPSkip) (CChanSet [c1])) = (case (eq c c1) of
                                                                                             True \<Rightarrow> CSPSkip
                                                                                           | otherwise \<Rightarrow> (CSPHide (CSPCommAction (ChanComm c Nil) CSPSkip) (CChanSet [c1])))"
| "crl_prefixHiding (CSPHide (CSPCommAction (ChanComm c [ChanDotExp e]) CSPSkip) (CChanSet [c1])) = (case (eq c c1) of
                                                                                                        True \<Rightarrow> CSPSkip
                                                                                                      | otherwise \<Rightarrow> (CSPHide (CSPCommAction (ChanComm c [ChanDotExp e]) CSPSkip) (CChanSet [c1])))"

 
fun crl_parExtChoiceExchange :: "CAction \<Rightarrow> CAction"
where
  "crl_parExtChoiceExchange (CSPExtChoice (CSPNSParal ns1 cs ns2 a1 a2) (CSPNSParal ns11 cs1 ns21 b1 b2)) = (case ((eq ns1 ns11 & eq cs1 cs) & eq ns2 ns21) of
                                                                                                                True \<Rightarrow> (CSPNSParal ns1 cs ns2 (CSPExtChoice a1 b1) (CSPExtChoice a2 b2))
                                                                                                              | False \<Rightarrow> (CSPExtChoice (CSPNSParal ns1 cs ns2 a1 a2) (CSPNSParal ns11 cs1 ns21 b1 b2)))"

 
fun crl_extChoiceStopUnit :: "CAction \<Rightarrow> CAction"
where
  "crl_extChoiceStopUnit (CSPExtChoice CSPStop a) = a"

 
fun crl_extChoiceSeqDist :: "CAction \<Rightarrow> CAction"
where
  "crl_extChoiceSeqDist (CSPSeq (CSPRepExtChoice i (CSPGuard gi (CSPCommAction ci ai))) b) = (CSPRepExtChoice i (CSPSeq (CSPGuard gi (CSPCommAction ci ai)) b))"

 
fun crl_seqStopZero :: "CAction \<Rightarrow> CAction"
where
  "crl_seqStopZero (CSPSeq CSPStop a) = CSPStop"

 
fun crl_communicationParallelismDistribution :: "CAction \<Rightarrow> CAction"
where
  "crl_communicationParallelismDistribution (CSPNSParal ns1 cs ns2 (CSPCommAction (ChanComm c [ChanOutExp e]) (CActionName a1)) (CSPCommAction (ChanComm c1 [ChanInp x1]) (CSPParAction a2 [ZVar (x, Nil)]))) = (case (eq c c1 & eq x x1) of
                                                                                                                                                                                                                    True \<Rightarrow> (CSPCommAction (ChanComm c [ChanDotExp e]) (CSPNSParal ns1 cs ns2 (CActionName a1) (CSPParAction a2 [e])))
                                                                                                                                                                                                                  | False \<Rightarrow> (CSPNSParal ns1 cs ns2 (CSPCommAction (ChanComm c [ChanOutExp e]) (CActionName a1)) (CSPCommAction (ChanComm c1 [ChanInp x1]) (CSPParAction a2 [ZVar (x, Nil)]))))"

 
fun crl_channelExtension3 :: "CAction \<Rightarrow> ZName \<Rightarrow> ZName \<Rightarrow> CAction"
where
  "crl_channelExtension3 (CSPHide (CSPNSParal ns1 cs1 ns2 a1 (CSPParAction a2 [e])) cs2) c x = (CSPHide (CSPNSParal ns1 cs1 ns2 (CSPCommAction (ChanComm c [ChanOutExp e]) a1) (CSPCommAction (ChanComm c [ChanInp x]) (CSPParAction a2 [ZVar (x, Nil)]))) cs2)"

 
fun crl_channelExtension4 :: "CAction \<Rightarrow> CAction"
where
  "crl_channelExtension4 (CSPHide (CSPNSParal ns1 (CChanSet cs1) ns2 a1 a2) (CChanSet cs2)) (ChanComm c [ChanOutExp e]) = (let p1 = member c cs1;
                                                                                                                               p2 = member c cs2
                                                                                                                           in case p1 & p2 of
                                                                                                                                 True \<Rightarrow> (CSPHide (CSPNSParal ns1 (CChanSet cs1) ns2 (CSPCommAction (ChanComm c [ChanOutExp e]) a1) (CSPCommAction (ChanComm c [ChanOutExp e]) a2)) (CChanSet cs2))
                                                                                                                               | False \<Rightarrow> (CSPHide (CSPNSParal ns1 (CChanSet cs1) ns2 a1 a2) (CChanSet cs2)))"

 
fun crl_promVarState
where
  "crl_promVarState (ProcMain (ZSchemaDef st (ZSchema exsc)) [CParAction lact (ParamActionDecl (xt # zvar1) act)] (CActionCommand (CValDecl [xt1] mact))) = (case (eq xt xt1) of
                                                                                                                                                                True \<Rightarrow> (ProcMain (ZSchemaDef st (ZS2 ZSAnd (ZSchema exsc) (ZSchema [xt]))) [CParAction lact act] mact)
                                                                                                                                                              | False \<Rightarrow> (ProcMain (ZSchemaDef st (ZSchema exsc)) [CParAction lact (ParamActionDecl (xt # zvar1) act)] (CActionCommand (CValDecl [xt1] mact))))"

 
fun crl_promVarState2
where
  "crl_promVarState2 (ProcStalessMain [CParAction lact (ParamActionDecl (xt1 # zvar1) act)] (CActionCommand (CValDecl [xt] mact))) st = (case (eq xt xt1) of
                                                                                                                                            True \<Rightarrow> (ProcMain (ZSchemaDef st (ZSchema [xt])) [CParAction lact act] mact)
                                                                                                                                          | False \<Rightarrow> (ProcStalessMain [CParAction lact (ParamActionDecl (xt1 # zvar1) act)] (CActionCommand (CValDecl [xt] mact))))"

 
fun crl_parallelismUnit1
where
  "crl_parallelismUnit1 (CSPNSParal _ _ _ CSPSkip CSPSkip) = CSPSkip"

 
fun crl_parallInterlEquiv
where
  "crl_parallInterlEquiv (CSPNSInter ns1 ns2 a1 a2) = (CSPNSParal ns1 CSEmpty ns2 a1 a2)"

 
fun crl_parallInterlEquiv_backwards
where
  "crl_parallInterlEquiv_backwards (CSPNSParal ns1 CSEmpty ns2 a1 a2) = (CSPNSInter ns1 ns2 a1 a2)"

 
fun crl_parSeqStep
where
  "crl_parSeqStep (CSPNSParal ns1 cs ns2 (CSPSeq a1 a2) a3) = (CSPSeq a1 (CSPNSParal ns1 cs ns2 a2 a3))"

 
fun crl_hidingSequenceDistribution
where
  "crl_hidingSequenceDistribution (CSPHide (CSPSeq a1 a2) cs) = (CSPSeq (CSPHide a1 cs) (CSPHide a2 cs))"

 
fun crl_guardSeqAssoc
where
  "crl_guardSeqAssoc (CSPSeq (CSPGuard g a1) a2) = (CSPGuard g (CSPSeq a1 a2))"

 
fun crl_inputPrefixParallelismDistribution2
where
  "crl_inputPrefixParallelismDistribution2 (CSPCommAction (ChanComm c [ChanInp x]) (CSPNSParal ns1 cs ns2 a1 a2)) = (CSPNSParal ns1 cs ns2 (CSPCommAction (ChanComm c [ChanInp x]) a1) a2)"

 
fun crl_prefixSkip
where
  "crl_prefixSkip (CSPCommAction (ChanComm c [ChanDotExp x]) a) = (CSPSeq (CSPCommAction (ChanComm c [ChanDotExp x]) CSPSkip) a)"
| "crl_prefixSkip (CSPCommAction c a) = (CSPSeq (CSPCommAction c CSPSkip) a)"

 
fun crl_prefixParDist
where
  "crl_prefixParDist (CSPCommAction (ChanComm cc Nil) (CSPNSParal ns1 cs ns2 a1 a2)) = (CSPNSParal ns1 (ChanSetUnion cs (CChanSet [cc])) ns2 (CSPCommAction (ChanComm cc Nil) a1) (CSPCommAction (ChanComm cc Nil) a2))"
| "crl_prefixParDist (CSPCommAction (ChanComm c [ChanDotExp e]) (CSPNSParal ns1 cs ns2 a1 a2)) = (CSPNSParal ns1 (ChanSetUnion cs (CChanSet [c])) ns2 (CSPCommAction (ChanComm c [ChanDotExp e]) a1) (CSPCommAction (ChanComm c [ChanDotExp e]) a2))"

 
fun crl_externalChoiceSequenceDistribution2
where
  "crl_externalChoiceSequenceDistribution2 (CSPSeq (CSPExtChoice (CSPGuard g1 a1) (CSPGuard g2 a2)) b) = (CSPExtChoice (CSPSeq (CSPGuard g1 a1) b) (CSPSeq (CSPGuard g2 a2) b))"

 
fun crl_trueGuard
where
  "crl_trueGuard (CSPGuard (ZTrue Nil) a) = a"

 
fun crl_falseGuard
where
  "crl_falseGuard (CSPGuard (ZFalse Nil) _) = CSPStop"

 
fun crl_hidingChaos
where
  "crl_hidingChaos (CSPHide CSPChaos _) = CSPChaos"

 
fun crl_seqChaosZero
where
  "crl_seqChaosZero (CSPSeq CSPChaos _) = CSPChaos"

 
fun crl_parallelismZero
where
  "crl_parallelismZero (CSPNSParal _ _ _ CSPChaos _) = CSPChaos"

 
fun crl_internalChoiceParallelismDistribution
where
  "crl_internalChoiceParallelismDistribution (CSPNSParal ns1 cs ns2 (CSPIntChoice a1 a2) a3) = (CSPIntChoice (CSPNSParal ns1 cs ns2 a1 a3) (CSPNSParal ns1 cs ns2 a2 a3))"

 
fun crl43
where
  "crl43 (CSPSeq a1 (CSPIntChoice a2 a3)) = (CSPIntChoice (CSPSeq a1 a2) (CSPSeq a1 a3))"

 
fun crl_sequenceInternalChoiceDistribution
where
  "crl_sequenceInternalChoiceDistribution (CSPHide (CSPNSParal ns1 cs1 ns2 a1 a2) cs2) = (CSPNSParal ns1 cs1 ns2 (CSPHide a1 cs2) (CSPHide a2 cs2))"

 
fun crl_hidingCombination
where
  "crl_hidingCombination (CSPHide (CSPHide a cs1) cs2) = (CSPHide a (ChanSetUnion cs1 cs2))"

 
fun crl_parallelismDeadlocked3
where
  "crl_parallelismDeadlocked3 (CSPNSParal ns1 cs ns2 (CSPRepExtChoice i (CSPCommAction ci ai)) (CSPRepExtChoice j (CSPCommAction cj aj))) = (CSPNSParal ns1 cs ns2 CSPStop (CSPRepExtChoice j (CSPCommAction cj aj)))"

 
fun crl_assignmentRemoval
where
  "crl_assignmentRemoval (CSPSeq (CActionCommand (CAssign _ e)) (CSPParAction a _)) = (CSPParAction a e)"

 
fun crl_innocuousAssignment
where
  "crl_innocuousAssignment (CActionCommand (CAssign [(x1, Nil)] [ZVar (x2, Nil)])) = (case (eq x1 x2) of
                                                                                         True \<Rightarrow> CSPSkip
                                                                                       | False \<Rightarrow> (CActionCommand (CAssign [(x1, Nil)] [ZVar (x2, Nil)])))"

 
fun crl_variableSubstitution2
where
  "crl_variableSubstitution2 (CValDecl [Include (ZSRef (ZSPlain x) Nil Nil)] (CSPParAction a [ZVar (x1, Nil)])) y = (CValDecl [Include (ZSRef (ZSPlain y) Nil Nil)] (CSPParAction a [ZVar (y, Nil)]))"

 
fun crl_inputPrefixSequenceDistribution
where
  "crl_inputPrefixSequenceDistribution (CSPSeq (CSPCommAction (ChanComm c [ChanInp x]) a1) a2) = (CSPCommAction (ChanComm c [ChanInp x]) (CSPSeq a1 a2))"

 
fun crl_inputPrefixHidIdentity
where
  "crl_inputPrefixHidIdentity (CSPSeq (CSPCommAction (ChanComm c [ChanInp x]) a1) a2) = (CSPCommAction (ChanComm c [ChanInp x]) (CSPSeq a1 a2))"

 
fun crl_guardParDist
where
  "crl_guardParDist (CSPNSParal ns1 cs ns2 (CSPGuard g a1) a2) = (CSPGuard g (CSPNSParal ns1 cs ns2 a1 a2))"

 
fun crl_internalChoiceHidingDistribution
where
  "crl_internalChoiceHidingDistribution (CSPHide (CSPIntChoice a1 a2) cs) = (CSPIntChoice (CSPHide a1 cs) (CSPHide a2 cs))"

 
fun crl_assignmentSkip
where
  "crl_assignmentSkip (CActionCommand (CValDecl [Include (ZSRef (ZSPlain x) Nil Nil)] (CActionCommand (CAssign [(x1, Nil)] [ZVar (e, Nil)])))) = (CActionCommand (CValDecl [Include (ZSRef (ZSPlain x) Nil Nil)] CSPSkip))"

 
fun getCommName :: "Comm \<Rightarrow> ZName"
where
  "getCommName (ChanComm n _) = n"
| "getCommName (ChanGenComm n _ _) = n"

 
fun usedC :: "CAction \<Rightarrow> (ZName, 'y) list"
where
  "usedC (CSPCommAction x c) = ([getCommName x] @ usedC c)"
| "usedC (CSPGuard _ c) = usedC c"
| "usedC (CSPSeq ca cb) = ((usedC ca) @ (usedC cb))"
| "usedC (CSPExtChoice ca cb) = ((usedC ca) @ (usedC cb))"
| "usedC (CSPIntChoice ca cb) = ((usedC ca) @ (usedC cb))"
| "usedC (CSPNSParal _ _ _ ca cb) = ((usedC ca) @ (usedC cb))"
| "usedC (CSPParal _ ca cb) = ((usedC ca) @ (usedC cb))"
| "usedC (CSPNSInter _ _ ca cb) = ((usedC ca) @ (usedC cb))"
| "usedC (CSPInterleave ca cb) = ((usedC ca) @ (usedC cb))"
| "usedC (CSPHide c _) = usedC c"
| "usedC (CSPRecursion _ c) = usedC c"
| "usedC (CSPRepSeq _ c) = usedC c"
| "usedC (CSPRepExtChoice _ c) = usedC c"
| "usedC (CSPRepIntChoice _ c) = usedC c"
| "usedC (CSPRepParalNS _ _ _ c) = usedC c"
| "usedC (CSPRepParal _ _ c) = usedC c"
| "usedC (CSPRepInterlNS _ _ c) = usedC c"
| "usedC (CSPRepInterl _ c) = usedC c"
| "usedC _ = Nil"

 
fun initials :: "CAction \<Rightarrow> ZName list"
where
  "initials (CSPCommAction x c) = [getCommName x]"
| "initials (CSPGuard _ c) = initials c"
| "initials (CSPSeq ca cb) = (initials ca)"
| "initials (CSPExtChoice ca cb) = ((initials ca) @ (initials cb))"
| "initials (CSPIntChoice ca cb) = ((initials ca) @ (initials cb))"
| "initials (CSPNSParal _ _ _ ca cb) = ((initials ca) @ (initials cb))"
| "initials (CSPParal _ ca cb) = ((initials ca) @ (initials cb))"
| "initials (CSPNSInter _ _ ca cb) = ((initials ca) @ (initials cb))"
| "initials (CSPInterleave ca cb) = ((initials ca) @ (initials cb))"
| "initials (CSPHide c _) = initials c"
| "initials (CSPRecursion _ c) = initials c"
| "initials (CSPRepSeq _ c) = initials c"
| "initials (CSPRepExtChoice _ c) = initials c"
| "initials (CSPRepIntChoice _ c) = initials c"
| "initials (CSPRepParalNS _ _ _ c) = initials c"
| "initials (CSPRepParal _ _ c) = initials c"
| "initials (CSPRepInterlNS _ _ c) = initials c"
| "initials (CSPRepInterl _ c) = initials c"
| "initials CSPSkip = [''tick'']"
| "initials _ = [Nil]"

 
fun deterministic :: "CAction \<Rightarrow> (char list) option"
where
  "deterministic (CSPCommAction x c) = deterministic c"
| "deterministic (CSPGuard _ c) = deterministic c"
| "deterministic (CSPSeq ca cb) = (let da = (deterministic ca);
                                       db = (deterministic cb)
                                   in case (eq da None) & (eq da db) of
                                         false \<Rightarrow> Some ''Deterministic'')"
| "deterministic (CSPExtChoice ca cb) = (let da = (deterministic ca);
                                             db = (deterministic cb)
                                         in case (eq da None) & (eq da db) of
                                               false \<Rightarrow> Some ''Deterministic'')"
| "deterministic (CSPIntChoice ca cb) = None"
| "deterministic (CSPNSParal _ _ _ ca cb) = None"
| "deterministic (CSPParal _ ca cb) = None"
| "deterministic (CSPNSInter _ _ ca cb) = (let da = (deterministic ca);
                                               db = (deterministic cb)
                                           in case (eq da None) & (eq da db) of
                                                 false \<Rightarrow> Some ''Deterministic'')"
| "deterministic (CSPInterleave ca cb) = (let da = (deterministic ca);
                                              db = (deterministic cb)
                                          in case (eq da None) & (eq da db) of
                                                false \<Rightarrow> Some ''Deterministic'')"
| "deterministic (CSPHide c _) = None"
| "deterministic (CSPRecursion _ c) = deterministic c"
| "deterministic (CSPRepSeq _ c) = deterministic c"
| "deterministic (CSPRepExtChoice _ c) = deterministic c"
| "deterministic (CSPRepIntChoice _ c) = None"
| "deterministic (CSPRepParalNS _ _ _ c) = None"
| "deterministic (CSPRepParal _ _ c) = None"
| "deterministic (CSPRepInterlNS _ _ c) = deterministic c"
| "deterministic (CSPRepInterl _ c) = deterministic c"
| "deterministic CSPSkip = Some ''Deterministic''"
| "deterministic _ = Some ''Undefined''"

 
fun isDeterministic :: "CAction \<Rightarrow> char list"
where
  "isDeterministic a = (let x = (deterministic a)
                        in case x of
                              Some ''Deterministic'' \<Rightarrow> ''Deterministic''
                            | Some x \<Rightarrow> ''undefined''
                            | None \<Rightarrow> ''Non-deterministic'')"

 
fun subset
where
  "subset xs ys = list_all (% arg0 . member arg0 ys) xs"

 
fun crl_parallelismIntroduction1b :: "CAction \<Rightarrow> NSExp \<Rightarrow> ZName list \<Rightarrow> NSExp \<Rightarrow> CActioncrl_parExtChoiceExchange"
where
  "crl_parallelismIntroduction1b (CSPCommAction (ChanComm c [ChanDotExp e]) a) (NSExprMult ns1) cs (NSExprMult ns2) = (let p1 = Not (member c (usedC a));
                                                                                                                           p2 = (subset (getWrtV a) ns1)
                                                                                                                       in case p1 & p2 of
                                                                                                                             True \<Rightarrow> (CSPNSParal (NSExprMult ns1) (CChanSet cs) (NSExprMult ns2) (CSPCommAction (ChanComm c [ChanDotExp e]) a) (CSPCommAction (ChanComm c [ChanDotExp e]) CSPSkip))
                                                                                                                           | False \<Rightarrow> (CSPCommAction (ChanComm c [ChanDotExp e]) a))"

 
fun crl_parallelismIntroduction1a :: "CAction \<Rightarrow> NSExp \<Rightarrow> ZName list \<Rightarrow> NSExp \<Rightarrow> CAction"
where
  "crl_parallelismIntroduction1a (CSPCommAction (ChanComm c e) a) (NSExprMult ns1) cs (NSExprMult ns2) = (let p1 = member c (usedC a);
                                                                                                              p2 = (subset (getWrtV a) ns1)
                                                                                                          in case p1 & p2 of
                                                                                                                True \<Rightarrow> (CSPNSParal (NSExprMult ns1) (CChanSet cs) (NSExprMult ns2) (CSPCommAction (ChanComm c e) a) (CSPCommAction (ChanComm c e) CSPSkip))
                                                                                                              | False \<Rightarrow> (CSPCommAction (ChanComm c e) a))"

 
fun crl_parallelismDeadlocked1 :: "CAction \<Rightarrow> CAction"
where
  "crl_parallelismDeadlocked1 (CSPNSParal ns1 (CChanSet cs) ns2 (CSPCommAction (ChanComm c1 x) a1) (CSPCommAction (ChanComm c2 y) a2)) = (let p1 = (eq c1 c2);
                                                                                                                                              p2 = (subset [c1, c2] cs)
                                                                                                                                          in case p1 & p2 of
                                                                                                                                                True \<Rightarrow> (CSPNSParal ns1 (CChanSet cs) ns2 CSPStop (CSPCommAction (ChanComm c2 y) a2))
                                                                                                                                              | False \<Rightarrow> (CSPNSParal ns1 (CChanSet cs) ns2 (CSPCommAction (ChanComm c1 x) a1) (CSPCommAction (ChanComm c2 y) a2)))"
| "crl_parallelismDeadlocked1 (CSPNSParal ns1 (CChanSet cs) ns2 CSPStop (CSPCommAction c2 a2)) = CSPStop"

 
fun deleteBy :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "deleteBy _ _ Nil = Nil"
| "deleteBy eq2 x (y # ys) = (if eq2 x y then ys
                              else y # deleteBy eq2 x ys)"

 
definition delete :: "('a :: eq) \<Rightarrow> ('a :: eq) list \<Rightarrow> ('a :: eq) list"
where
  "delete = deleteBy eq"

 
fun flip :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'c"
where
  "flip f x y = f y x"

 
definition \\ :: "('a :: eq) list \<Rightarrow> ('a :: eq) list \<Rightarrow> ('a :: eq) list"
where
  "\\ = foldl (flip delete)"

 
fun intersectBy :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "intersectBy eq4 xs ys = ([x . x <- xs,
                                 list_ex (eq4 x) ys])"

 
definition intersect :: "('a :: eq) list \<Rightarrow> ('a :: eq) list \<Rightarrow> ('a :: eq) list"
where
  "intersect = intersectBy eq"

 
fun crl_hidingIdentity :: "CAction \<Rightarrow> CAction"
where
  "crl_hidingIdentity (CSPHide a (CChanSet cs)) = (let p1 = null (intersect cs (usedC a))
                                                   in case p1 of
                                                         True \<Rightarrow> a
                                                       | False \<Rightarrow> (CSPHide a (CChanSet cs)))"

 
fun nub'0
where
  "nub'0 Nil _ = Nil"
| "nub'0 (x # xs) ls = (if member x ls then nub'0 xs ls
                        else x # nub'0 xs (x # ls))"

 
fun nub :: "('a :: eq) list \<Rightarrow> ('a :: eq) list"
where
  "nub l = (let nub' = nub'0
            in nub' l Nil)"

 
fun nubBy :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "nubBy eq5 Nil = Nil"
| "nubBy eq6 (x # xs) = (x # nubBy eq6 (filter (% y .
                                                  Not (eq6 x y)) xs))"

 
fun unionBy :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "unionBy eq3 xs ys = (xs @ foldl (flip (deleteBy eq3)) (nubBy eq3 ys) xs)"

 
definition union :: "('a :: eq) list \<Rightarrow> ('a :: eq) list \<Rightarrow> ('a :: eq) list"
where
  "union = unionBy eq"

 
fun crl_chanExt1 :: "CAction \<Rightarrow> ZName \<Rightarrow> CAction"
where
  "crl_chanExt1 (CSPNSParal ns1 (CChanSet cs) ns2 a1 a2) c = (let p1 = Not (member c (union (usedC a1) (usedC a2)))
                                                              in case p1 of
                                                                    True \<Rightarrow> (CSPNSParal ns1 (ChanSetUnion (CChanSet cs) (CChanSet [c])) ns2 a1 a2)
                                                                  | False \<Rightarrow> (CSPNSParal ns1 (CChanSet cs) ns2 a1 a2))"

 
fun crl_hidingExternalChoiceDistribution :: "CAction \<Rightarrow> CAction"
where
  "crl_hidingExternalChoiceDistribution (CSPHide (CSPExtChoice a1 a2) (CChanSet cs)) = (let p1 = null (intersect (union initials a1 initials a2) cs)
                                                                                        in case p1 of
                                                                                              True \<Rightarrow> (CSPExtChoice (CSPHide a1 (CChanSet cs)) (CSPHide a2 (CChanSet cs)))
                                                                                            | False \<Rightarrow> (CSPHide (CSPExtChoice a1 a2) (CChanSet cs)))"

 
fun elem_by :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "elem_by _ _ Nil = False"
| "elem_by eq7 y (x # xs) = (eq7 y x | elem_by eq7 y xs)"

 
fun isJust :: "'a option \<Rightarrow> bool"
where
  "isJust None = False"
| "isJust _ = True"

 
fun crl_parallelismExternalChoiceDistribution :: "CAction \<Rightarrow> CAction"
where
  "crl_parallelismExternalChoiceDistribution (CSPRepExtChoice i (CSPNSParal ns1 (CChanSet cs) ns2 ai a)) = (let p1 = (subset (initials a) cs);
                                                                                                                p2 = isJust (deterministic a)
                                                                                                            in case p1 & p2 of
                                                                                                                  True \<Rightarrow> (CSPNSParal ns1 (CChanSet cs) ns2 (CSPRepExtChoice i ai) a)
                                                                                                                | False \<Rightarrow> (CSPRepExtChoice i (CSPNSParal ns1 (CChanSet cs) ns2 ai a)))"


end
