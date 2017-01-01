theory MappingFunStatelessCircus
imports AST OmegaDefs Prelude
begin
 
function (sequential) omega_CAction :: "(ZName * ZVar * ZExpr) list \<Rightarrow> CAction \<Rightarrow> CAction" and 
    omega_prime_CAction :: "(ZName * ZVar * ZExpr) list \<Rightarrow> CAction \<Rightarrow> CAction"
where
  "omega_CAction lst CSPSkip = CSPSkip"
| "omega_CAction lst CSPStop = CSPStop"
| "omega_CAction lst CSPChaos = CSPChaos"
| "omega_CAction lst (CSPCommAction (ChanComm c ((ChanOutExp e) # xs)) a) = omega_CAction lst (CSPCommAction (ChanComm c ((ChanDotExp e) # xs)) a)"
| "omega_CAction lst (CSPSeq ca cb) = (CSPSeq (omega_CAction lst ca) (omega_CAction lst cb))"
| "omega_CAction lst (CSPIntChoice ca cb) = (CSPIntChoice (omega_CAction lst ca) (omega_CAction lst cb))"
| "omega_CAction lst (CSPCommAction (ChanComm c Nil) a) = (CSPCommAction (ChanComm c Nil) (omega_CAction lst a))"
| "omega_CAction lst (CSPHide a cs) = (CSPHide (omega_CAction lst a) cs)"
| "omega_CAction lst (CSPRecursion x c) = (CSPRecursion x (omega_CAction lst c))"
| "omega_CAction lst (CActionCommand (CommandBrace g)) = omega_CAction lst (CActionCommand (CPrefix g (ZTrue Nil)))"
| "omega_CAction lst (CActionCommand (CommandBracket g)) = omega_CAction lst (CActionCommand (CPrefix1 g))"
| "omega_CAction lst (CSPRenAction a (CRenameAssign left right)) = (CSPRenAction a (CRename right left))"
(*| "omega_CAction lst (CSPRepSeq [Choose (x, Nil) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1, Nil)])) 
    = (case x = x1 of 
        True \<Rightarrow> omega_CAction lst (rep_CSPRepSeq lst omega_CAction act xs) 
        | _ \<Rightarrow> (CSPRepSeq [Choose (x, Nil) (ZSeqDisplay xs)] (omega_CAction lst (CSPParAction act [ZVar (x1, Nil)]))))"
| "omega_CAction lst (CSPRepExtChoice [Choose (x, Nil) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1, Nil)])) 
    = (case x = x1 of 
        True \<Rightarrow> rep_CSPRepExtChoice lst omega_CAction act xs 
        | _ \<Rightarrow> (CSPRepExtChoice [Choose (x, Nil) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1, Nil)])))"
| "omega_CAction lst (CSPRepIntChoice [Choose (x, Nil) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1, Nil)])) 
    = (case x = x1 of 
        True \<Rightarrow> rep_CSPRepIntChoice lst omega_CAction act xs 
        | _ \<Rightarrow> (CSPRepIntChoice [Choose (x, Nil) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1, Nil)])))"
| "omega_CAction lst (CSPRepParalNS (CSExpr cs) [Choose (x, Nil) (ZSetDisplay lsx)] (NSExprParam ns [ZVar (x1, Nil)]) (CSPParAction a [ZVar (x2, Nil)])) 
    = (case (x = x1) & (x = x2) of 
        True \<Rightarrow> rep_CSPRepParalNS lst omega_CAction a cs ns x lsx 
        | _ \<Rightarrow> (CSPRepParalNS (CSExpr cs) [Choose (x, Nil) (ZSetDisplay lsx)] (NSExprParam ns [ZVar (x1, Nil)]) (omega_CAction lst (CSPParAction a [ZVar (x2, Nil)]))))"
| "omega_CAction lst (CSPRepInterlNS [Choose (x, Nil) (ZSetDisplay lsx)] (NSExprParam ns [ZVar (x1, Nil)]) (CSPParAction a [ZVar (x2, Nil)])) 
    = (case (x = x1) & (x = x2) of 
        True \<Rightarrow> rep_CSPRepInterlNS lst omega_CAction a ns x lsx 
        | _ \<Rightarrow> (CSPRepInterlNS [Choose (x, Nil) (ZSetDisplay lsx)] (NSExprParam ns [ZVar (x1, Nil)]) (omega_CAction lst (CSPParAction a [ZVar (x2, Nil)]))))"
| "omega_CAction lst (CActionCommand (CIf (CircGAction g a))) 
    = (let lsx = free_var_ZPred g 
        in make_get_com lst lsx (rename_vars_CAction (map fst lsx) (CActionCommand (CIf (CircGAction g (omega_prime_CAction lst a))))))"
*)(* | "omega_CAction lst (CSPRepInterlNS [Choose (x, Nil) (ZSetDisplay lsx)] (NSExprParam ns [ZVar (x1, Nil)]) act)
    = (CSPRepInterlNS [Choose (x, Nil) (ZSetDisplay lsx)] (NSExprParam ns [ZVar (x1, Nil)]) (omega_CAction lst act))"*)
(* | "omega_CAction lst (CSPRepParalNS (CSExpr cs) [Choose (x, Nil) (ZSetDisplay lsx)] (NSExprParam ns [ZVar (x1, Nil)]) act) 
    = (CSPRepParalNS (CSExpr cs) [Choose (x, Nil) (ZSetDisplay lsx)] (NSExprParam ns [ZVar (x1, Nil)]) (omega_CAction lst act))"*)
(* | "omega_CAction lst (CSPRepIntChoice [Choose (x, Nil) v] act) = (CSPRepIntChoice [Choose (x, Nil) v] (omega_CAction lst act))"*)
(* | "omega_CAction lst (CSPRepExtChoice [Choose (x, Nil) v] act) = (CSPRepExtChoice [Choose (x, Nil) v] (omega_CAction lst act))"*)
(* | "omega_CAction lst (CSPRepSeq [Choose (x, Nil) v] act) = (CSPRepSeq [Choose (x, Nil) v] (omega_CAction lst act))"*)   
| "omega_CAction lst (CSPCommAction (ChanComm c [ChanInpPred x p]) a) 
    = (let lsx = free_var_ZPred p 
        in case Not (member x (getWrtV a)) of 
            True \<Rightarrow> make_get_com lst lsx (rename_vars_CAction (map fst lsx) (CSPCommAction (ChanComm c [ChanInpPred x p]) (omega_prime_CAction lst a))) 
            | _ \<Rightarrow> (CSPCommAction (ChanComm c [ChanInpPred x p]) a))"
| "omega_CAction lst (CActionCommand (CAssign varls valls)) 
    = make_get_com lst varls (rename_vars_CAction (map fst (filter_state_comp lst)) (make_set_com lst omega_CAction varls valls CSPSkip))"
| "omega_CAction lst (CActionCommand (CIf (CircThenElse gl glx))) 
    = (let guard_pair = get_guard_pair (CircThenElse gl glx); 
           lsx = concat (map free_var_ZPred (map fst guard_pair)) 
      in make_get_com lst lsx (rename_vars_CAction (map fst lsx) (CActionCommand (CIf (mk_guard_pair lst omega_prime_CAction guard_pair)))))"
| "omega_CAction lst (CSPCommAction (ChanComm c ((ChanDotExp e) # xs)) a) 
    = (let lxs = intersect (get_chan_param ((ChanDotExp e) # xs)) (filter_state_comp lst) 
       in make_get_com lst lxs (rename_vars_CAction (map fst lxs) (CSPCommAction (ChanComm c ((ChanDotExp e) # xs)) (omega_prime_CAction lst a))))"
| "omega_CAction lst (CSPExtChoice ca cb) 
    = (let lsx = remdups (intersect (free_var_CAction (CSPExtChoice ca cb)) (filter_state_comp lst)) 
      in make_get_com lst lsx (rename_vars_CAction (map fst lsx) (CSPExtChoice (omega_prime_CAction lst ca) (omega_prime_CAction lst cb))))"
| "omega_CAction lst (CSPGuard g a) 
    = (let lxs = remdups (intersect (free_var_ZPred g) (filter_state_comp lst)) 
      in make_get_com lst lxs (rename_vars_CAction (map fst lxs) (CSPGuard (rename_ZPred (map fst lxs) g) (omega_prime_CAction lst a))))"
| "omega_CAction lst x = x"
| "omega_prime_CAction lst CSPSkip = CSPSkip"
| "omega_prime_CAction lst CSPChaos = CSPChaos"
| "omega_prime_CAction lst CSPStop = CSPStop"
| "omega_prime_CAction lst (CActionCommand (CAssign varls valls)) = (make_set_com lst omega_CAction varls valls CSPSkip)"
| "omega_prime_CAction lst (CActionCommand (CIf (CircGAction g a))) = (CActionCommand (CIf (CircGAction g (omega_prime_CAction lst a))))"
| "omega_prime_CAction lst (CActionCommand (CommandBrace g)) = omega_prime_CAction lst (CActionCommand (CPrefix g (ZTrue Nil)))"
| "omega_prime_CAction lst (CActionCommand (CommandBracket g)) = omega_prime_CAction lst (CActionCommand (CPrefix1 g))"
| "omega_prime_CAction lst (CActionName n) = (CActionName n)"
| "omega_prime_CAction lst (CSPCommAction (ChanComm c Nil) a) = (CSPCommAction (ChanComm c Nil) (omega_prime_CAction lst a))"
| "omega_prime_CAction lst (CSPCommAction (ChanComm c x) a) = (CSPCommAction (ChanComm c x) (omega_prime_CAction lst a))"
| "omega_prime_CAction lst (CSPGuard g a) = (CSPGuard g (omega_prime_CAction lst a))"
| "omega_prime_CAction lst (CSPHide a cs) = (CSPHide (omega_prime_CAction lst a) cs)"
| "omega_prime_CAction lst (CSPIntChoice ca cb) = (CSPIntChoice (omega_prime_CAction lst ca) (omega_prime_CAction lst cb))"
| "omega_prime_CAction lst (CSPRecursion x c) = (CSPRecursion x (omega_prime_CAction lst c))"
| "omega_prime_CAction lst (CSPRenAction a (CRenameAssign left right)) = (CSPRenAction a (CRename right left))"
| "omega_prime_CAction lst (CSPSeq ca cb) = (CSPSeq (omega_prime_CAction lst ca) (omega_prime_CAction lst cb))"
| "omega_prime_CAction lst (CActionCommand (CIf (CircThenElse gl glx))) = (let guard_pair = get_guard_pair (CircThenElse gl glx) in (CActionCommand (CIf (mk_guard_pair lst omega_prime_CAction guard_pair))))"
(*| "omega_prime_CAction lst (CSPRepInterlNS [Choose (x, Nil) (ZSetDisplay lsx)] (NSExprParam ns [ZVar (x1, Nil)]) (CSPParAction a [ZVar (x2, Nil)])) 
    = (case (x = x1) & (x = x2) of 
        True \<Rightarrow> rep_CSPRepInterlNS lst omega_prime_CAction a ns x lsx 
        | _ \<Rightarrow> (CSPRepInterlNS [Choose (x, Nil) (ZSetDisplay lsx)] (NSExprParam ns [ZVar (x1, Nil)]) (omega_prime_CAction lst (CSPParAction a [ZVar (x2, Nil)]))))"
| "omega_prime_CAction lst (CSPRepInterlNS [Choose (x, Nil) (ZSetDisplay lsx)] (NSExprParam ns [ZVar (x1, Nil)]) act) 
    = (CSPRepInterlNS [Choose (x, Nil) (ZSetDisplay lsx)] (NSExprParam ns [ZVar (x1, Nil)]) (omega_prime_CAction lst act))"
| "omega_prime_CAction lst (CSPRepParalNS (CSExpr cs) [Choose (x, Nil) (ZSetDisplay lsx)] (NSExprParam ns [ZVar (x1, Nil)]) (CSPParAction a [ZVar (x2, Nil)])) 
    = (case (x = x1) & (x = x2) of 
        True \<Rightarrow> rep_CSPRepParalNS lst omega_prime_CAction a cs ns x lsx 
        | _ \<Rightarrow> (CSPRepParalNS (CSExpr cs) [Choose (x, Nil) (ZSetDisplay lsx)] (NSExprParam ns [ZVar (x1, Nil)]) (omega_prime_CAction lst (CSPParAction a [ZVar (x2, Nil)]))))"
| "omega_prime_CAction lst (CSPRepParalNS (CSExpr cs) [Choose (x, Nil) (ZSetDisplay lsx)] (NSExprParam ns [ZVar (x1, Nil)]) act) 
    = (CSPRepParalNS (CSExpr cs) [Choose (x, Nil) (ZSetDisplay lsx)] (NSExprParam ns [ZVar (x1, Nil)]) (omega_prime_CAction lst act))"
| "omega_prime_CAction lst (CSPRepSeq [Choose (x, Nil) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1, Nil)])) 
    = (case x = x1 of 
        True \<Rightarrow> omega_prime_CAction lst (rep_CSPRepSeq lst omega_prime_CAction act xs) 
        | _ \<Rightarrow> (CSPRepSeq [Choose (x, Nil) (ZSeqDisplay xs)] (omega_prime_CAction lst (CSPParAction act [ZVar (x1, Nil)]))))"
| "omega_prime_CAction lst (CSPRepSeq [Choose (x, Nil) v] act) 
    = (CSPRepSeq [Choose (x, Nil) v] (omega_prime_CAction lst act))"
| "omega_prime_CAction lst (CSPRepExtChoice [Choose (x, Nil) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1, Nil)])) 
    = (case x = x1 of 
        True \<Rightarrow> rep_CSPRepExtChoice lst omega_prime_CAction act xs 
        | _ \<Rightarrow> (CSPRepExtChoice [Choose (x, Nil) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1, Nil)])))"
| "omega_prime_CAction lst (CSPRepIntChoice [Choose (x, Nil) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1, Nil)])) 
    = (case x = x1 of 
        True \<Rightarrow> rep_CSPRepIntChoice lst omega_prime_CAction act xs 
        | _ \<Rightarrow> (CSPRepIntChoice [Choose (x, Nil) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1, Nil)])))"
| "omega_prime_CAction lst (CSPRepIntChoice [Choose (x, Nil) v] act) 
    = (CSPRepIntChoice [Choose (x, Nil) v] (omega_prime_CAction lst act))"
*)
| "omega_prime_CAction lst x = x"
  by pat_completeness auto
    
end
