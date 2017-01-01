theory OmegaDefs
imports AST Prelude
begin
 
fun filter_state_comp :: "(ZName * ZVar * ZExpr) list \<Rightarrow> ZVar list"
where
  "filter_state_comp Nil = Nil"
| "filter_state_comp [(_, v, _)] = [v]"
| "filter_state_comp ((_, v, _) # xs) = ([v] @ (filter_state_comp xs))"

 
fun get_guard_pair :: "CGActions \<Rightarrow> (ZPred * CAction) list"
where
  "get_guard_pair (CircThenElse (CircGAction g2 a2) (CircGAction g3 a3)) = [(g2, a2), (g3, a3)]"
| "get_guard_pair (CircThenElse (CircGAction g1 a1) glx) = ([(g1, a1)] @ (get_guard_pair glx))"
| "get_guard_pair _ = Nil"

 
fun get_proc_name :: "ZName \<Rightarrow> (ZName * ZVar * ZExpr) list \<Rightarrow> ZName"
where
  "get_proc_name x [(a, ((va, x1), b))] = (case x = va of
                                              True \<Rightarrow> a
                                            | _ \<Rightarrow> '''')"
| "get_proc_name x ((a, ((va, x1), b)) # vst) = (case x = va of
                                                    True \<Rightarrow> a
                                                  | _ \<Rightarrow> get_proc_name x vst)"

 
fun make_get_com :: "(ZName * ZVar * ZExpr) list \<Rightarrow> ZVar list \<Rightarrow> CAction \<Rightarrow> CAction"
where
  "make_get_com lst [(x, Nil)] c = (CSPCommAction (ChanComm ''mget'' [ChanDotExp (ZVar ((get_proc_name x lst) @ (''_'' @ x), Nil)), ChanInp ((''v'' @ (get_proc_name x lst)) @ (''_'' @ x))]) c)"
| "make_get_com lst ((x, Nil) # xs) c = (CSPCommAction (ChanComm ''mget'' [ChanDotExp (ZVar ((get_proc_name x lst) @ (''_'' @ x), Nil)), ChanInp ((''v'' @ (get_proc_name x lst)) @ (''_'' @ x))]) (make_get_com lst xs c))"
| "make_get_com lst x c = c"

 
fun getWrtV :: "'t \<Rightarrow> 't1 list"
where
  "getWrtV xs = Nil"

 
fun free_var_ZGenFilt :: "ZGenFilt \<Rightarrow> ZVar list"
where
  "free_var_ZGenFilt (Choose v e) = [v]"
| "free_var_ZGenFilt _ = Nil"

 
fun free_var_ZPred :: "ZPred \<Rightarrow> ZVar list"
where
  "free_var_ZPred (ZFalse p) = error ''Don't know what free vars of ZFalse are right now. Check back later''"
| "free_var_ZPred (ZTrue p) = error ''Don't know what free vars of ZTrue are right now. Check back later''"
| "free_var_ZPred (ZAnd a b) = (free_var_ZPred a @ free_var_ZPred b)"

 
fun fvs :: "('t \<Rightarrow> 't1 list) \<Rightarrow> 't list \<Rightarrow> 't1 list"
where
  "fvs f Nil = Nil"
| "fvs f (e # es) = (f e @ (fvs f es))"

 
function (sequential) free_var_ZExpr :: "ZExpr \<Rightarrow> ZVar list"
where
  "free_var_ZExpr (ZVar v) = [v]"
| "free_var_ZExpr (ZInt c) = Nil"
| "free_var_ZExpr (ZSetDisplay exls) = fvs free_var_ZExpr exls"
| "free_var_ZExpr (ZSeqDisplay exls) = fvs free_var_ZExpr exls"
| "free_var_ZExpr (ZCall ex ex2) = free_var_ZExpr ex2"
| "free_var_ZExpr _ = Nil"
by pat_completeness auto
 
fun rename_vars_CReplace :: "'t \<Rightarrow> CReplace \<Rightarrow> CReplace"
where
  "rename_vars_CReplace lst (CRename zvarls1 zvarls) = (CRename zvarls1 zvarls)"
| "rename_vars_CReplace lst (CRenameAssign zvarls1 zvarls) = (CRenameAssign zvarls1 zvarls)"

 
fun rename_ZPred :: "string list \<Rightarrow> ZPred \<Rightarrow> ZPred"
where
  "rename_ZPred lst (ZFalse a) = (ZFalse a)"
| "rename_ZPred lst (ZTrue a) = (ZTrue a)"
| "rename_ZPred lst (ZAnd p1 p2) = (ZAnd (rename_ZPred lst p1) (rename_ZPred lst p2))"

 
fun inListVar :: "'a \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "inListVar x Nil = False"
| "inListVar x [va] = (case x = va of
                          True \<Rightarrow> True
                        | _ \<Rightarrow> False)"
| "inListVar x (va # vst) = (case x = va of
                                True \<Rightarrow> True
                              | _ \<Rightarrow> inListVar x vst)"

 
fun rename_ZExpr :: "string list \<Rightarrow> ZExpr \<Rightarrow> ZExpr"
where
  "rename_ZExpr lst (ZVar (va, x)) = (case (inListVar va lst) of
                                         True \<Rightarrow> (ZVar (''v_'' @ va, x))
                                       | False \<Rightarrow> (ZVar (va, x)))"
| "rename_ZExpr lst (ZInt zi) = (ZInt zi)"
| "rename_ZExpr lst (ZCall xpr1 xpr2) = (ZCall (rename_ZExpr lst xpr1) (rename_ZExpr lst xpr2))"

 
fun bindingsVar :: "string list \<Rightarrow> (ZVar * ZExpr) list \<Rightarrow> (ZVar * ZExpr) list"
where
  "bindingsVar lst Nil = Nil"
| "bindingsVar lst [((va, x), b)] = (case (inListVar va lst) of
                                        True \<Rightarrow> [((''v_'' @ va, x), (rename_ZExpr lst b))]
                                      | False \<Rightarrow> [((va, x), (rename_ZExpr lst b))])"
| "bindingsVar lst (((va, x), b) # xs) = (case (inListVar va lst) of
                                             True \<Rightarrow> [((''v_'' @ va, x), (rename_ZExpr lst b))] @ (bindingsVar lst xs)
                                           | False \<Rightarrow> [((va, x), (rename_ZExpr lst b))] @ (bindingsVar lst xs))"

 
fun rename_vars_CParameter :: "string list \<Rightarrow> CParameter \<Rightarrow> CParameter"
where
  "rename_vars_CParameter lst (ChanInp zn) = (ChanInp zn)"
| "rename_vars_CParameter lst (ChanInpPred zn zp) = (ChanInpPred zn (rename_ZPred lst zp))"
| "rename_vars_CParameter lst (ChanOutExp ze) = (ChanOutExp (rename_ZExpr lst ze))"
| "rename_vars_CParameter lst (ChanDotExp ze) = (ChanDotExp (rename_ZExpr lst ze))"

 
fun rename_vars_Comm :: "string list \<Rightarrow> Comm \<Rightarrow> Comm"
where
  "rename_vars_Comm lst (ChanComm zn cpls) = (ChanComm zn (map (rename_vars_CParameter lst) cpls))"
| "rename_vars_Comm lst (ChanGenComm zn zexprls cpls) = (ChanGenComm zn (map (rename_ZExpr lst) zexprls) (map (rename_vars_CParameter lst) cpls))"

 
fun rename_vars_CAction :: "string list \<Rightarrow> CAction \<Rightarrow> CAction" and 
    rename_vars_CCommand :: "string list \<Rightarrow> CCommand \<Rightarrow> CCommand" and 
    rename_vars_CGActions :: "string list \<Rightarrow> CGActions \<Rightarrow> CGActions"
where
  "rename_vars_CAction lst (CActionCommand cmd) = (CActionCommand (rename_vars_CCommand lst cmd))"
| "rename_vars_CAction lst (CActionName zn) = (CActionName zn)"
| "rename_vars_CAction lst CSPSkip = CSPSkip"
| "rename_vars_CAction lst CSPStop = CSPStop"
| "rename_vars_CAction lst CSPChaos = CSPChaos"
| "rename_vars_CAction lst (CSPCommAction c a) = (CSPCommAction (rename_vars_Comm lst c) (rename_vars_CAction lst a))"
| "rename_vars_CAction lst (CSPGuard zp a) = (CSPGuard (rename_ZPred lst zp) (rename_vars_CAction lst a))"
| "rename_vars_CAction lst (CSPSeq a1 a2) = (CSPSeq (rename_vars_CAction lst a1) (rename_vars_CAction lst a2))"
| "rename_vars_CAction lst (CSPExtChoice a1 a2) = (CSPExtChoice (rename_vars_CAction lst a1) (rename_vars_CAction lst a2))"
| "rename_vars_CAction lst (CSPIntChoice a1 a2) = (CSPIntChoice (rename_vars_CAction lst a1) (rename_vars_CAction lst a2))"
| "rename_vars_CAction lst (CSPNSParal ns1 cs ns2 a1 a2) = (CSPNSParal ns1 cs ns2 (rename_vars_CAction lst a1) (rename_vars_CAction lst a2))"
| "rename_vars_CAction lst (CSPParal cs a1 a2) = (CSPParal cs (rename_vars_CAction lst a1) (rename_vars_CAction lst a2))"
| "rename_vars_CAction lst (CSPNSInter ns1 ns2 a1 a2) = (CSPNSInter ns1 ns2 (rename_vars_CAction lst a1) (rename_vars_CAction lst a2))"
| "rename_vars_CAction lst (CSPInterleave a1 a2) = (CSPInterleave (rename_vars_CAction lst a1) (rename_vars_CAction lst a2))"
| "rename_vars_CAction lst (CSPHide a cs) = (CSPHide (rename_vars_CAction lst a) cs)"
| "rename_vars_CAction lst (CSPParAction zn zexprls) = (CSPParAction zn (map (rename_ZExpr lst) zexprls))"
| "rename_vars_CAction lst (CSPRenAction zn crpl) = (CSPRenAction zn (rename_vars_CReplace lst crpl))"
| "rename_vars_CAction lst (CSPRecursion zn a) = (CSPRecursion zn (rename_vars_CAction lst a))"
| "rename_vars_CAction lst (CSPUnParAction zgf a zn) = (CSPUnParAction zgf (rename_vars_CAction lst a) zn)"
| "rename_vars_CAction lst (CSPRepSeq zgf a) = (CSPRepSeq zgf (rename_vars_CAction lst a))"
| "rename_vars_CAction lst (CSPRepExtChoice zgf a) = (CSPRepExtChoice zgf (rename_vars_CAction lst a))"
| "rename_vars_CAction lst (CSPRepIntChoice zgf a) = (CSPRepIntChoice zgf (rename_vars_CAction lst a))"
| "rename_vars_CAction lst (CSPRepParalNS cs zgf ns a) = (CSPRepParalNS cs zgf ns (rename_vars_CAction lst a))"
| "rename_vars_CAction lst (CSPRepParal cs zgf a) = (CSPRepParal cs zgf (rename_vars_CAction lst a))"
| "rename_vars_CAction lst (CSPRepInterlNS zgf ns a) = (CSPRepInterlNS zgf ns (rename_vars_CAction lst a))"
| "rename_vars_CAction lst (CSPRepInterl zgf a) = (CSPRepInterl zgf (rename_vars_CAction lst a))"
| "rename_vars_CCommand lst (CAssign zvarls1 zexprls) = (CAssign zvarls1 (map (rename_ZExpr lst) zexprls))"
| "rename_vars_CCommand lst (CIf ga) = (CIf (rename_vars_CGActions lst ga))"
| "rename_vars_CCommand lst (CVarDecl zgf a) = (CVarDecl zgf (rename_vars_CAction lst a))"
| "rename_vars_CCommand lst (CAssumpt znls zp1 zp2) = (CAssumpt znls (rename_ZPred lst zp1) zp2)"
| "rename_vars_CCommand lst (CAssumpt1 znls zp) = (CAssumpt1 znls zp)"
| "rename_vars_CCommand lst (CPrefix zp1 zp2) = (CPrefix (rename_ZPred lst zp1) zp2)"
| "rename_vars_CCommand lst (CPrefix1 zp) = (CPrefix1 zp)"
| "rename_vars_CCommand lst (CommandBrace zp) = (CommandBrace zp)"
| "rename_vars_CCommand lst (CommandBracket zp) = (CommandBracket zp)"
| "rename_vars_CCommand lst (CValDecl zgf a) = (CValDecl zgf (rename_vars_CAction lst a))"
| "rename_vars_CCommand lst (CResDecl zgf a) = (CResDecl zgf (rename_vars_CAction lst a))"
| "rename_vars_CCommand lst (CVResDecl zgf a) = (CVResDecl zgf (rename_vars_CAction lst a))"
| "rename_vars_CGActions lst (CircGAction zp a) = (CircGAction (rename_ZPred lst zp) (rename_vars_CAction lst a))"
| "rename_vars_CGActions lst (CircThenElse cga1 cga2) = (CircThenElse (rename_vars_CGActions lst cga1) (rename_vars_CGActions lst cga2))"
| "rename_vars_CGActions lst (CircElse pa) = (CircElse pa)"

fun get_chan_param :: "CParameter list \<Rightarrow> ZVar list"
where
  "get_chan_param Nil = Nil"
| "get_chan_param [ChanDotExp (ZVar (x, _))] = [(x, Nil)]"
| "get_chan_param [ChanOutExp (ZVar (x, _))] = [(x, Nil)]"
| "get_chan_param [_] = Nil"
| "get_chan_param ((ChanDotExp (ZVar (x, _))) # xs) = ([(x, Nil)] @ (get_chan_param xs))"
| "get_chan_param ((ChanOutExp (ZVar (x, _))) # xs) = ([(x, Nil)] @ (get_chan_param xs))"
| "get_chan_param (_ # xs) = (get_chan_param xs)"

 
fun rep_CSPRepSeq
where
  "rep_CSPRepSeq lst f a [x] = f lst (CSPParAction a [x])"
| "rep_CSPRepSeq lst f a (x # xs) = CSPSeq (f lst (CSPParAction a [x])) (rep_CSPRepSeq lst f a xs)"

 
fun rep_CSPRepIntChoice
where
  "rep_CSPRepIntChoice lst f a [x] = f lst (CSPParAction a [x])"
| "rep_CSPRepIntChoice lst f a (x # xs) = CSPIntChoice (f lst (CSPParAction a [x])) (rep_CSPRepIntChoice lst f a xs)"

 
fun rep_CSPRepExtChoice
where
  "rep_CSPRepExtChoice lst f a [x] = f lst (CSPParAction a [x])"
| "rep_CSPRepExtChoice lst f a (x # xs) = CSPExtChoice (f lst (CSPParAction a [x])) (rep_CSPRepExtChoice lst f a xs)"

 
fun rep_CSPRepParalNS
where
  "rep_CSPRepParalNS lst f a _ _ _ [x] = f lst (CSPParAction a [x])"
| "rep_CSPRepParalNS lst f a cs ns y (x # xs) = (CSPNSParal (NSExprParam ns [x]) (CSExpr cs) (NSBigUnion (ZSetComp [Choose (y, Nil) (ZSetDisplay xs)] (Some (ZCall (ZVar (ns, Nil)) (ZVar (y, Nil)))))) (f lst (CSPParAction a [x])) (rep_CSPRepParalNS lst f a cs ns y xs))"

 
fun rep_CSPRepInterlNS
where
  "rep_CSPRepInterlNS lst f a _ _ [x] = f lst (CSPParAction a [x])"
| "rep_CSPRepInterlNS lst f a ns y (x # xs) = (CSPNSInter (NSExprParam ns [x]) (NSBigUnion (ZSetComp [Choose (y, Nil) (ZSetDisplay xs)] (Some (ZCall (ZVar (ns, Nil)) (ZVar (y, Nil)))))) (f lst (CSPParAction a [x])) (rep_CSPRepInterlNS lst f a ns y xs))"

 
fun mk_guard_pair
where
  "mk_guard_pair lst f [(g, a)] = (CircGAction g (f lst a))"
| "mk_guard_pair lst f ((g, a) # ls) = (CircThenElse (CircGAction g (f lst a)) (mk_guard_pair lst f ls))"

 
fun make_set_com
where
  "make_set_com lst f [(x, Nil)] [y] c = (CSPCommAction (ChanComm ''mset'' [ChanDotExp (ZVar ((get_proc_name x lst) @ (''_'' @ x), Nil)), ChanOutExp y]) (f lst c))"
| "make_set_com lst f ((x, Nil) # xs) (y # ys) c = (CSPCommAction (ChanComm ''mset'' [ChanDotExp (ZVar ((get_proc_name x lst) @ (''_'' @ x), Nil)), ChanOutExp y]) (make_set_com lst f xs ys c))"

 
fun delete_from_list
where
  "delete_from_list x Nil = Nil"
| "delete_from_list x [v] = (case x = v of
                                True \<Rightarrow> Nil
                              | False \<Rightarrow> [v])"
| "delete_from_list x (v # va) = (case x = v of
                                     True \<Rightarrow> delete_from_list x va
                                   | False \<Rightarrow> (v # (delete_from_list x va)))"

 
fun setminus :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "setminus Nil _ = Nil"
| "setminus (v # va) Nil = (v # va)"
| "setminus (v # va) (b # vb) = ((delete_from_list b (v # va)) @ (setminus (v # va) vb))"

 
fun member
where
  "member x Nil = False"
| "member x (b # y) = (if x = b then True else member x y)"

 
fun intersect :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "intersect Nil y = Nil"
| "intersect (a # x) y = (if member a y then a # (intersect x y)
                          else intersect x y)"

 
fun union :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "union Nil y = y"
| "union (a # x) y = (if (member a y) then (union x y)
                      else a # (union x y))"

 
fun remdups :: "'a list \<Rightarrow> 'a list"
where
  "remdups Nil = Nil"
| "remdups (x # xs) = (if member x xs then remdups xs
                       else x # remdups xs)"

fun elem_by :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "elem_by _ _ Nil = False"
| "elem_by eq1 y (x # xs) = (eq1 y x | elem_by eq1 y xs)"


 
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
