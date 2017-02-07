theory MappingFunStatelessCircus
imports AST OmegaDefs Prelude
begin
 
function (sequential) omega_CAction :: "CAction \<Rightarrow> CAction" and 
    omega_prime_CAction :: "CAction \<Rightarrow> CAction"
where
  "omega_CAction CSPSkip = CSPSkip"
| "omega_CAction CSPStop = CSPStop"
| "omega_CAction CSPChaos = CSPChaos"
| "omega_CAction (CSPCommAction (ChanComm c Nil) a) = (CSPCommAction (ChanComm c Nil) (omega_CAction a))"
| "omega_CAction (CSPCommAction (ChanComm c [ChanInp (x#xs)]) a) = (CSPCommAction (ChanComm c [ChanInp (x#xs)]) (omega_CAction a))"
| "omega_CAction (CSPCommAction (ChanComm c [ChanDotExp e]) a )= (let lxs = concat (map get_ZVar_st (free_var_ZExpr e))
                                                                 in make_get_com lxs ( (CSPCommAction (ChanComm c [rename_vars_CParameter (ChanDotExp e)]) (omega_prime_CAction  a))))"
| "omega_CAction (CSPCommAction (ChanComm c [ChanOutExp e]) a) = omega_CAction (CSPCommAction (ChanComm c [ChanDotExp e]) a)"
| "omega_CAction (CSPCommAction (ChanComm c [ChanInpPred (x#xs) p]) a) = (let lsx = concat (map get_ZVar_st (free_var_ZPred p))
                                                             in case Not (member (x#xs) (getWrtV a)) of
                                                                   True \<Rightarrow> make_get_com lsx (rename_vars_CAction (CSPCommAction (ChanComm c [ChanInpPred (x#xs) p]) (omega_CAction a)))
                                                                 | _ \<Rightarrow> (CSPCommAction (ChanComm c [ChanInpPred (x#xs) p]) a))"
(*| "omega_CAction (CActionCommand (CAssign varls valls)) = (if (length varls) > 0 then make_get_com (map fst varls) (rename_vars_CAction (make_set_com omega_CAction varls valls CSPSkip)) else CSPSkip)"
| "omega_CAction (CActionCommand (CIf (CircGAction g a))) = (let lsx = (map fst (remdups (free_var_ZPred g)))
                                                        in make_get_com lsx (rename_vars_CAction (CActionCommand (CIf (CircGAction g (omega_prime_CAction  a))))))"
| "omega_CAction (CActionCommand (CIf (CircThenElse gl glx))) = (let guard_pair = get_guard_pair (CircThenElse gl glx);
                                                                lsx = map fst (remdups (concat (map free_var_ZPred (map fst guard_pair))))
                                                            in make_get_com lsx (rename_vars_CAction (CActionCommand (CIf (mk_guard_pair omega_prime_CAction guard_pair)))))"
*)| "omega_CAction (CSPGuard g a) = (let lxs = concat (map get_ZVar_st (free_var_ZPred g))
                                   in make_get_com lxs ((CSPGuard (rename_ZPred g) (omega_prime_CAction a))))"
| "omega_CAction (CSPSeq ca cb) = (CSPSeq (omega_CAction ca) (omega_CAction cb))"
| "omega_CAction (CSPIntChoice ca cb) = (CSPIntChoice (omega_CAction ca) (omega_CAction cb))"
| "omega_CAction (CSPExtChoice ca cb) = (let lsx = (map fst (remdups (free_var_CAction (CSPExtChoice ca cb))))
                                         in make_get_com lsx (rename_vars_CAction (CSPExtChoice (omega_prime_CAction ca) (omega_prime_CAction cb))))"
| "omega_CAction (CSPNSParal ns1 cs ns2 a1 a2) = (let lsx = union (map fst (remdups (free_var_CAction a1))) (map fst (remdups (free_var_CAction a2)))
                                                  in make_get_com lsx (rename_vars_CAction (CSPHide (CSPNSParal NSExpEmpty (CSExpr ''MEMi'') NSExpEmpty (CSPNSParal NSExpEmpty cs NSExpEmpty (CSPHide (CSPNSParal NSExpEmpty (CSExpr ''MEMi'') NSExpEmpty (CSPSeq a1 (CSPCommAction (ChanComm ''terminate'' Nil) CSPSkip)) (CSPParAction ''MemoryMerge'' [ZSetDisplay Nil, ZVar (''LEFT'', Nil)])) (CSExpr ''MEMi'')) (CSPHide (CSPNSParal NSExpEmpty (CSExpr ''MEMi'') NSExpEmpty (CSPSeq a2 (CSPCommAction (ChanComm ''terminate'' Nil) CSPSkip)) (CSPParAction ''MemoryMerge'' [ZSetDisplay Nil, ZVar (''RIGHT'', Nil)])) (CSExpr ''MEMi''))) (CActionName ''Merge'')) (CChanSet [''mleft'', ''mright'']))))"
| "omega_CAction (CSPHide a cs) = (CSPHide (omega_CAction a) cs)"
| "omega_CAction (CSPRecursion x c) = (CSPRecursion x (omega_CAction c))"
| "omega_CAction x = x"
| "omega_prime_CAction (CSPCommAction (ChanComm c Nil) a) = (CSPCommAction (ChanComm c Nil) (omega_prime_CAction a))"
| "omega_prime_CAction (CSPCommAction (ChanComm c [ChanDotExp e]) a) = (CSPCommAction (ChanComm c [ChanDotExp (rename_ZExpr e)]) (omega_prime_CAction a))"
| "omega_prime_CAction (CSPSeq ca cb) = (CSPSeq (omega_prime_CAction ca) (omega_CAction cb))"
| "omega_prime_CAction x = omega_CAction x"
by pat_completeness auto
termination sorry
end
