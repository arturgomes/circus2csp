theory MappingFunStatelessCircus
imports AST OmegaDefs Prelude
begin

fun omega_CAction :: "(ZName * ZVar * ZExpr) list \<Rightarrow> CAction \<Rightarrow> CAction" and
    omega_prime_CAction :: "(ZName * ZVar * ZExpr) list \<Rightarrow> CAction \<Rightarrow> CAction" and
    rep_CSPRepSeq :: "(ZName * ZVar * ZExpr) list \<Rightarrow> ZName \<Rightarrow> ZExpr list \<Rightarrow> CAction" and
    rep_CSPRepIntChoice :: "(ZName * ZVar * ZExpr) list \<Rightarrow> ZName \<Rightarrow> ZExpr list \<Rightarrow> CAction" and
    rep_CSPRepExtChoice :: "(ZName * ZVar * ZExpr) list \<Rightarrow> ZName \<Rightarrow> ZExpr list \<Rightarrow> CAction" and
    rep_CSPRepParalNS :: "(ZName * ZVar * ZExpr) list \<Rightarrow> ZName \<Rightarrow> ZName \<Rightarrow> ZName \<Rightarrow> string \<Rightarrow> ZExpr list \<Rightarrow> CAction" and
    rep_CSPRepInterlNS :: "(ZName * ZVar * ZExpr) list \<Rightarrow> ZName \<Rightarrow> ZName \<Rightarrow> string \<Rightarrow> ZExpr list \<Rightarrow> CAction" and
    mk_guard_pair :: "(ZName * ZVar * ZExpr) list \<Rightarrow> (ZPred * CAction) list \<Rightarrow> CGActions" and
    make_set_com :: "(ZName * ZVar * ZExpr) list \<Rightarrow> ZVar list \<Rightarrow> ZExpr list \<Rightarrow> CAction \<Rightarrow> CAction"
where
  "omega_CAction lst CSPSkip = CSPSkip"
| "omega_CAction lst CSPStop = CSPStop"
| "omega_CAction lst CSPChaos = CSPChaos"
| "omega_CAction lst (CSPCommAction (ChanComm c Nil) a) = (CSPCommAction (ChanComm c Nil) (omega_CAction lst a))"
| "omega_CAction lst (CSPCommAction (ChanComm c ((ChanOutExp e) # xs)) a) = omega_CAction lst (CSPCommAction (ChanComm c ((ChanDotExp e) # xs)) a)"
| "omega_CAction lst (CSPSeq ca cb) = (CSPSeq (omega_CAction lst ca) (omega_CAction lst cb))"
| "omega_CAction lst (CSPIntChoice ca cb) = (CSPIntChoice (omega_CAction lst ca) (omega_CAction lst cb))"
| "omega_CAction lst (CSPHide a cs) = (CSPHide (omega_CAction lst a) cs)"
| "omega_CAction lst (CSPRecursion x c) = (CSPRecursion x (omega_CAction lst c))"
| "omega_CAction lst (CActionCommand (CommandBrace g)) = omega_CAction lst (CActionCommand (CPrefix g (ZTrue Nil)))"
| "omega_CAction lst (CActionCommand (CommandBracket g)) = omega_CAction lst (CActionCommand (CPrefix1 g))"
| "omega_CAction lst (CSPRenAction a (CRenameAssign left right)) = (CSPRenAction a (CRename right left))"
| "omega_CAction lst (CSPRepSeq [Choose (x, Nil) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1, Nil)])) = (case x = x1 of
                                                                                                              True \<Rightarrow> omega_CAction lst (rep_CSPRepSeq lst act xs)
                                                                                                            | _ \<Rightarrow> (CSPRepSeq [Choose (x, Nil) (ZSeqDisplay xs)] (omega_CAction lst (CSPParAction act [ZVar (x1, Nil)]))))"
| "omega_CAction lst (CSPRepSeq [Choose (x, Nil) v] act) = (CSPRepSeq [Choose (x, Nil) v] (omega_CAction lst act))"
| "omega_CAction lst (CSPRepExtChoice [Choose (x, Nil) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1, Nil)])) = (case x = x1 of
                                                                                                                    True \<Rightarrow> rep_CSPRepExtChoice lst act xs
                                                                                                                  | _ \<Rightarrow> (CSPRepExtChoice [Choose (x, Nil) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1, Nil)])))"
| "omega_CAction lst (CSPRepExtChoice [Choose (x, Nil) v] act) = (CSPRepExtChoice [Choose (x, Nil) v] (omega_CAction lst act))"
| "omega_CAction lst (CSPRepIntChoice [Choose (x, Nil) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1, Nil)])) = (case x = x1 of
                                                                                                                    True \<Rightarrow> rep_CSPRepIntChoice lst act xs
                                                                                                                  | _ \<Rightarrow> (CSPRepIntChoice [Choose (x, Nil) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1, Nil)])))"
| "omega_CAction lst (CSPRepIntChoice [Choose (x, Nil) v] act) = (CSPRepIntChoice [Choose (x, Nil) v] (omega_CAction lst act))"
| "omega_CAction lst (CSPRepParalNS (CSExpr cs) [Choose (x, Nil) (ZSetDisplay lsx)] (NSExprParam ns [ZVar (x1, Nil)]) (CSPParAction a [ZVar (x2, Nil)])) = (case (x = x1) & (x = x2) of
                                                                                                                                                               True \<Rightarrow> rep_CSPRepParalNS lst a cs ns x lsx
                                                                                                                                                             | _ \<Rightarrow> (CSPRepParalNS (CSExpr cs) [Choose (x, Nil) (ZSetDisplay lsx)] (NSExprParam ns [ZVar (x1, Nil)]) (omega_CAction lst (CSPParAction a [ZVar (x2, Nil)]))))"
| "omega_CAction lst (CSPRepParalNS (CSExpr cs) [Choose (x, Nil) (ZSetDisplay lsx)] (NSExprParam ns [ZVar (x1, Nil)]) act) = (CSPRepParalNS (CSExpr cs) [Choose (x, Nil) (ZSetDisplay lsx)] (NSExprParam ns [ZVar (x1, Nil)]) (omega_CAction lst act))"
| "omega_CAction lst (CSPRepInterlNS [Choose (x, Nil) (ZSetDisplay lsx)] (NSExprParam ns [ZVar (x1, Nil)]) (CSPParAction a [ZVar (x2, Nil)])) = (case (x = x1) & (x = x2) of
                                                                                                                                                    True \<Rightarrow> rep_CSPRepInterlNS lst a ns x lsx
                                                                                                                                                  | _ \<Rightarrow> (CSPRepInterlNS [Choose (x, Nil) (ZSetDisplay lsx)] (NSExprParam ns [ZVar (x1, Nil)]) (omega_CAction lst (CSPParAction a [ZVar (x2, Nil)]))))"
| "omega_CAction lst (CSPRepInterlNS [Choose (x, Nil) (ZSetDisplay lsx)] (NSExprParam ns [ZVar (x1, Nil)]) act) = (CSPRepInterlNS [Choose (x, Nil) (ZSetDisplay lsx)] (NSExprParam ns [ZVar (x1, Nil)]) (omega_CAction lst act))"
| "omega_CAction lst (CActionCommand (CIf (CircGAction g a))) = (let lsx = free_var_ZPred g
                                                                 in make_get_com lst lsx (rename_vars_CAction (map fst lsx) (CActionCommand (CIf (CircGAction g (omega_prime_CAction lst a))))))"
| "omega_CAction lst (CSPCommAction (ChanComm c ((ChanDotExp e) # xs)) a) = (let lxs = intersect (get_chan_param ((ChanDotExp e) # xs)) (filter_state_comp lst)
                                                                             in make_get_com lst lxs (rename_vars_CAction (map fst lxs) (CSPCommAction (ChanComm c ((ChanDotExp e) # xs)) (omega_prime_CAction lst a))))"
| "omega_CAction lst (CActionCommand (CAssign varls valls)) = make_get_com lst varls (rename_vars_CAction (map fst (filter_state_comp lst)) (make_set_com lst varls valls CSPSkip))"
| "omega_CAction lst (CActionCommand (CIf (CircThenElse gl glx))) = (let guard_pair = get_guard_pair (CircThenElse gl glx);
                                                                         lsx = remdups (concat (map free_var_ZPred (map fst guard_pair)))
                                                                     in make_get_com lst lsx (rename_vars_CAction (map fst lsx) (CActionCommand (CIf (mk_guard_pair lst guard_pair)))))"
| "omega_CAction lst x = x"
| "omega_prime_CAction lst CSPSkip = CSPSkip"
| "omega_prime_CAction lst CSPChaos = CSPChaos"
| "omega_prime_CAction lst CSPStop = CSPStop"
| "omega_prime_CAction lst (CActionCommand (CAssign varls valls)) = (make_set_com lst varls valls CSPSkip)"
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
| "omega_prime_CAction lst (CActionCommand (CIf (CircThenElse gl glx))) = (let guard_pair = get_guard_pair (CircThenElse gl glx)
                                                                           in (CActionCommand (CIf (mk_guard_pair lst guard_pair))))"
| "omega_prime_CAction lst (CSPRepInterlNS [Choose (x, Nil) (ZSetDisplay lsx)] (NSExprParam ns [ZVar (x1, Nil)]) (CSPParAction a [ZVar (x2, Nil)])) = (case (x = x1) & (x = x2) of
                                                                                                                                                          True \<Rightarrow> rep_CSPRepInterlNS lst a ns x lsx
                                                                                                                                                        | _ \<Rightarrow> (CSPRepInterlNS [Choose (x, Nil) (ZSetDisplay lsx)] (NSExprParam ns [ZVar (x1, Nil)]) (omega_prime_CAction lst (CSPParAction a [ZVar (x2, Nil)]))))"
| "omega_prime_CAction lst (CSPRepInterlNS [Choose (x, Nil) (ZSetDisplay lsx)] (NSExprParam ns [ZVar (x1, Nil)]) act) = (CSPRepInterlNS [Choose (x, Nil) (ZSetDisplay lsx)] (NSExprParam ns [ZVar (x1, Nil)]) (omega_prime_CAction lst act))"
| "omega_prime_CAction lst (CSPRepParalNS (CSExpr cs) [Choose (x, Nil) (ZSetDisplay lsx)] (NSExprParam ns [ZVar (x1, Nil)]) (CSPParAction a [ZVar (x2, Nil)])) = (case (x = x1) & (x = x2) of
                                                                                                                                                                     True \<Rightarrow> rep_CSPRepParalNS lst a cs ns x lsx
                                                                                                                                                                   | _ \<Rightarrow> (CSPRepParalNS (CSExpr cs) [Choose (x, Nil) (ZSetDisplay lsx)] (NSExprParam ns [ZVar (x1, Nil)]) (omega_prime_CAction lst (CSPParAction a [ZVar (x2, Nil)]))))"
| "omega_prime_CAction lst (CSPRepParalNS (CSExpr cs) [Choose (x, Nil) (ZSetDisplay lsx)] (NSExprParam ns [ZVar (x1, Nil)]) act) = (CSPRepParalNS (CSExpr cs) [Choose (x, Nil) (ZSetDisplay lsx)] (NSExprParam ns [ZVar (x1, Nil)]) (omega_prime_CAction lst act))"
| "omega_prime_CAction lst (CSPRepSeq [Choose (x, Nil) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1, Nil)])) = (case x = x1 of
                                                                                                                    True \<Rightarrow> omega_prime_CAction lst (rep_CSPRepSeq lst act xs)
                                                                                                                  | _ \<Rightarrow> (CSPRepSeq [Choose (x, Nil) (ZSeqDisplay xs)] (omega_prime_CAction lst (CSPParAction act [ZVar (x1, Nil)]))))"
| "omega_prime_CAction lst (CSPRepExtChoice [Choose (x, Nil) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1, Nil)])) = (case x = x1 of
                                                                                                                          True \<Rightarrow> rep_CSPRepExtChoice lst act xs
                                                                                                                        | _ \<Rightarrow> (CSPRepExtChoice [Choose (x, Nil) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1, Nil)])))"
| "omega_prime_CAction lst (CSPRepIntChoice [Choose (x, Nil) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1, Nil)])) = (case x = x1 of
                                                                                                                          True \<Rightarrow> rep_CSPRepIntChoice lst act xs
                                                                                                                        | _ \<Rightarrow> (CSPRepIntChoice [Choose (x, Nil) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1, Nil)])))"
| "omega_prime_CAction lst x = x"
| "rep_CSPRepSeq _ _ [] = undefined"
| "rep_CSPRepSeq lst a [x] = omega_CAction lst (CSPParAction a [x])"
| "rep_CSPRepSeq lst a (x # xs) = CSPSeq (omega_CAction lst (CSPParAction a [x])) (rep_CSPRepSeq lst a xs)"
| "rep_CSPRepIntChoice lst a [] = undefined"
| "rep_CSPRepIntChoice lst a [x] = omega_CAction lst (CSPParAction a [x])"
| "rep_CSPRepIntChoice lst a (x # xs) = CSPIntChoice (omega_CAction lst (CSPParAction a [x])) (rep_CSPRepIntChoice lst a xs)"
| "rep_CSPRepExtChoice lst a [] = undefined"
| "rep_CSPRepExtChoice lst a [x] = omega_CAction lst (CSPParAction a [x])"
| "rep_CSPRepExtChoice lst a (x # xs) = CSPExtChoice (omega_CAction lst (CSPParAction a [x])) (rep_CSPRepExtChoice lst a xs)"
| "rep_CSPRepParalNS lst a _ _ _ [] = undefined"
| "rep_CSPRepParalNS lst a _ _ _ [x] = omega_CAction lst (CSPParAction a [x])"
| "rep_CSPRepParalNS lst a cs ns y (x # xs) = (CSPNSParal (NSExprParam ns [x]) (CSExpr cs) (NSBigUnion (ZSetComp [Choose (y, Nil) (ZSetDisplay xs)] (Some (ZCall (ZVar (ns, Nil)) (ZVar (y, Nil)))))) (omega_CAction lst (CSPParAction a [x])) (rep_CSPRepParalNS lst a cs ns y xs))"
| "rep_CSPRepInterlNS lst a _ _ [] = undefined"
| "rep_CSPRepInterlNS lst a _ _ [x] = omega_CAction lst (CSPParAction a [x])"
| "rep_CSPRepInterlNS lst a ns y (x # xs) = (CSPNSInter (NSExprParam ns [x]) (NSBigUnion (ZSetComp [Choose (y, Nil) (ZSetDisplay xs)] (Some (ZCall (ZVar (ns, Nil)) (ZVar (y, Nil)))))) (omega_CAction lst (CSPParAction a [x])) (rep_CSPRepInterlNS lst a ns y xs))"
| "mk_guard_pair lst [] = undefined"
| "mk_guard_pair lst [(g, a)] = (CircGAction g (omega_prime_CAction lst a))"
| "mk_guard_pair lst ((g, a) # ls) = (CircThenElse (CircGAction g (omega_prime_CAction lst a)) (mk_guard_pair lst ls))"
| "make_set_com lst [] _ _ = undefined"
| "make_set_com lst [(x, Nil)] [y] c = (CSPCommAction (ChanComm ''mset'' [ChanDotExp (ZVar ((get_proc_name x lst) @ (''_'' @ x), Nil)), ChanOutExp y]) (omega_CAction lst c))"
| "make_set_com lst ((x, Nil) # xs) (y # ys) c = (CSPCommAction (ChanComm ''mset'' [ChanDotExp (ZVar ((get_proc_name x lst) @ (''_'' @ x), Nil)), ChanOutExp y]) (make_set_com lst xs ys c))"


fun free_var_CAction :: "CAction \<Rightarrow> ZVar list" and
    free_var_comnd :: "CCommand \<Rightarrow> ZVar list" and
    free_var_if :: "CGActions \<Rightarrow> ZVar list"
where
  "free_var_CAction (CActionCommand c) = (free_var_comnd c)"
| "free_var_CAction (CSPCommAction (ChanComm com xs) c) = ((get_chan_param xs) @ (free_var_CAction c))"
| "free_var_CAction (CSPGuard p c) = ((free_var_ZPred p) @ (free_var_CAction c))"
| "free_var_CAction (CSPSeq ca cb) = ((free_var_CAction ca) @ (free_var_CAction cb))"
| "free_var_CAction (CSPExtChoice ca cb) = ((free_var_CAction ca) @ (free_var_CAction cb))"
| "free_var_CAction (CSPIntChoice ca cb) = ((free_var_CAction ca) @ (free_var_CAction cb))"
| "free_var_CAction (CSPNSParal ns1 cs ns2 ca cb) = ((free_var_CAction ca) @ (free_var_CAction cb))"
| "free_var_CAction (CSPParal cs ca cb) = ((free_var_CAction ca) @ (free_var_CAction cb))"
| "free_var_CAction (CSPNSInter ns1 ns2 ca cb) = ((free_var_CAction ca) @ (free_var_CAction cb))"
| "free_var_CAction (CSPInterleave ca cb) = ((free_var_CAction ca) @ (free_var_CAction cb))"
| "free_var_CAction (CSPHide c cs) = (free_var_CAction c)"
| "free_var_CAction (CSPRecursion nm c) = (free_var_CAction c)"
| "free_var_CAction (CSPUnParAction lst c nm) = setminus (free_var_CAction c) (fvs free_var_ZGenFilt lst)"
| "free_var_CAction (CSPRepSeq lst c) = setminus (free_var_CAction c) (fvs free_var_ZGenFilt lst)"
| "free_var_CAction (CSPRepExtChoice lst c) = setminus (free_var_CAction c) (fvs free_var_ZGenFilt lst)"
| "free_var_CAction (CSPRepIntChoice lst c) = setminus (free_var_CAction c) (fvs free_var_ZGenFilt lst)"
| "free_var_CAction (CSPRepParalNS cs lst ns c) = setminus (free_var_CAction c) (fvs free_var_ZGenFilt lst)"
| "free_var_CAction (CSPRepParal cs lst c) = setminus (free_var_CAction c) (fvs free_var_ZGenFilt lst)"
| "free_var_CAction (CSPRepInterlNS lst ns c) = setminus (free_var_CAction c) (fvs free_var_ZGenFilt lst)"
| "free_var_CAction (CSPRepInterl lst c) = setminus (free_var_CAction c) (fvs free_var_ZGenFilt lst)"
| "free_var_CAction _ = Nil"
| "free_var_comnd (CAssign v e) = v"
| "free_var_comnd (CIf ga) = free_var_if ga"
| "free_var_comnd (CVarDecl z c) = setminus (free_var_CAction c) (fvs free_var_ZGenFilt z)"
| "free_var_comnd (CommandBrace z) = (free_var_ZPred z)"
| "free_var_comnd (CommandBracket z) = (free_var_ZPred z)"
| "free_var_comnd (CValDecl z c) = setminus (free_var_CAction c) (fvs free_var_ZGenFilt z)"
| "free_var_comnd (CResDecl z c) = setminus (free_var_CAction c) (fvs free_var_ZGenFilt z)"
| "free_var_comnd (CVResDecl z c) = setminus (free_var_CAction c) (fvs free_var_ZGenFilt z)"
| "free_var_comnd _ = Nil"
| "free_var_if (CircGAction p a) = ((free_var_ZPred p) @ (free_var_CAction a))"
| "free_var_if (CircThenElse ga gb) = ((free_var_if ga) @ (free_var_if gb))"
| "free_var_if (CircElse (CircusAction a)) = (free_var_CAction a)"
| "free_var_if (CircElse (ParamActionDecl x (CircusAction a))) = setminus (free_var_CAction a) (fvs free_var_ZGenFilt x)"


end
