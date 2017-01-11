theory OmegaDefs
imports AST Prelude
begin
 
fun join_name
where
  "join_name n v = (n @ (''_'' @ v))"

 
fun free_var_ZGenFilt :: "ZGenFilt \<Rightarrow> ZVar list"
where
  "free_var_ZGenFilt (Choose v e) = [v]"
| "free_var_ZGenFilt _ = Nil"

 
fun free_var_ZPred :: "ZPred \<Rightarrow> ZVar list"
where
  "free_var_ZPred (ZFalse p) = error ''Don't know what free vars of ZFalse are right now. Check back later''"
| "free_var_ZPred (ZTrue p) = error ''Don't know what free vars of ZTrue are right now. Check back later''"
| "free_var_ZPred (ZAnd a b) = (free_var_ZPred a @ free_var_ZPred b)"
| "free_var_ZPred x = error ''Don't know what free vars of this right now. Check back later''"

 
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
 
fun get_chan_var :: "CParameter list \<Rightarrow> ZVar list"
where
  "get_chan_var Nil = Nil"
| "get_chan_var [ChanDotExp (ZVar (x, _))] = [(x, Nil)]"
| "get_chan_var [ChanOutExp (ZVar (x, _))] = [(x, Nil)]"
| "get_chan_var [_] = Nil"
| "get_chan_var ((ChanDotExp (ZVar (x, _))) # xs) = ([(x, Nil)] @ (get_chan_var xs))"
| "get_chan_var ((ChanOutExp (ZVar (x, _))) # xs) = ([(x, Nil)] @ (get_chan_var xs))"
| "get_chan_var (_ # xs) = (get_chan_var xs)"

 
fun get_guard_pair :: "CGActions \<Rightarrow> (ZPred * CAction) list"
where
  "get_guard_pair (CircThenElse (CircGAction g2 a2) (CircGAction g3 a3)) = [(g2, a2), (g3, a3)]"
| "get_guard_pair (CircThenElse (CircGAction g1 a1) glx) = ([(g1, a1)] @ (get_guard_pair glx))"
| "get_guard_pair _ = Nil"

 
fun make_get_com :: "ZName list \<Rightarrow> CAction \<Rightarrow> CAction"
where
  "make_get_com [x] c = (CSPCommAction (ChanComm ''mget'' [ChanDotExp (ZVar (x, Nil)), ChanInp (''v_'' @ x)]) c)"
| "make_get_com (x # xs) c = (CSPCommAction (ChanComm ''mget'' [ChanDotExp (ZVar (x, Nil)), ChanInp (''v_'' @ x)]) (make_get_com xs c))"
| "make_get_com x c = c"

 
fun make_set_com
where
  "make_set_com f [(x, _)] [y] c = (CSPCommAction (ChanComm ''mset'' [ChanDotExp (ZVar (x, Nil)), ChanOutExp y]) (f c))"
| "make_set_com f ((x, _) # xs) (y # ys) c = (CSPCommAction (ChanComm ''mset'' [ChanDotExp (ZVar (x, Nil)), ChanOutExp y]) (make_set_com f xs ys c))"

 
fun mk_guard_pair
where
  "mk_guard_pair f [(g, a)] = (CircGAction g (f a))"
| "mk_guard_pair f ((g, a) # ls) = (CircThenElse (CircGAction g (f a)) (mk_guard_pair f ls))"

 
fun getWrtV :: "'t \<Rightarrow> 't1 list"
where
  "getWrtV xs = Nil"

 
fun rename_ZPred :: "ZPred \<Rightarrow> ZPred"
where
  "rename_ZPred (ZFalse a) = (ZFalse a)"
| "rename_ZPred (ZTrue a) = (ZTrue a)"
| "rename_ZPred (ZAnd p1 p2) = (ZAnd (rename_ZPred p1) (rename_ZPred p2))"

 
fun rename_vars_CReplace :: "CReplace \<Rightarrow> CReplace"
where
  "rename_vars_CReplace (CRename zvarls1 zvarls) = (CRename zvarls1 zvarls)"
| "rename_vars_CReplace (CRenameAssign zvarls1 zvarls) = (CRenameAssign zvarls1 zvarls)"

 
fun inListVar :: "'a \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "inListVar x Nil = False"
| "inListVar x [va] = (case x = va of
                          True \<Rightarrow> True
                        | _ \<Rightarrow> False)"
| "inListVar x (va # vst) = (case x = va of
                                True \<Rightarrow> True
                              | _ \<Rightarrow> inListVar x vst)"

 
fun is_Var_or_Int
where
  "is_Var_or_Int [ZVar (a, b)] = True"
| "is_Var_or_Int [ZInt x] = True"
| "is_Var_or_Int ((ZVar (a, b)) # xs) = (True & is_Var_or_Int xs)"
| "is_Var_or_Int ((ZInt x) # xs) = (True & is_Var_or_Int xs)"
| "is_Var_or_Int _ = False"

 
fun rep_CSPRepSeq :: "ZName \<Rightarrow> ZExpr list \<Rightarrow> CAction"
where
  "rep_CSPRepSeq a [x] = (CSPParAction a [x])"
| "rep_CSPRepSeq a (x # xs) = CSPSeq (CSPParAction a [x]) (rep_CSPRepSeq a xs)"

 
fun rep_CSPRepIntChoice :: "ZName \<Rightarrow> ZExpr list \<Rightarrow> CAction"
where
  "rep_CSPRepIntChoice a [x] = (CSPParAction a [x])"
| "rep_CSPRepIntChoice a (x # xs) = CSPIntChoice (CSPParAction a [x]) (rep_CSPRepIntChoice a xs)"

 
fun rep_CSPRepExtChoice :: "ZName \<Rightarrow> ZExpr list \<Rightarrow> CAction"
where
  "rep_CSPRepExtChoice a [x] = (CSPParAction a [x])"
| "rep_CSPRepExtChoice a (x # xs) = CSPExtChoice (CSPParAction a [x]) (rep_CSPRepExtChoice a xs)"

 
fun rep_CSPRepParalNS :: "ZName \<Rightarrow> ZName \<Rightarrow> ZName \<Rightarrow> string \<Rightarrow> ZExpr list \<Rightarrow> CAction"
where
  "rep_CSPRepParalNS a _ _ _ [x] = (CSPParAction a [x])"
| "rep_CSPRepParalNS a cs ns y (x # xs) = (CSPNSParal (NSExprParam ns [x]) (CSExpr cs) (NSBigUnion (ZSetComp [Choose (y, Nil) (ZSetDisplay xs)] (Some (ZCall (ZVar (ns, Nil)) (ZVar (y, Nil)))))) (CSPParAction a [x]) (rep_CSPRepParalNS a cs ns y xs))"

 
fun rep_CSPRepInterlNS :: "ZName \<Rightarrow> ZName \<Rightarrow> string \<Rightarrow> ZExpr list \<Rightarrow> CAction"
where
  "rep_CSPRepInterlNS a _ _ [x] = (CSPParAction a [x])"
| "rep_CSPRepInterlNS a ns y (x # xs) = (CSPNSInter (NSExprParam ns [x]) (NSBigUnion (ZSetComp [Choose (y, Nil) (ZSetDisplay xs)] (Some (ZCall (ZVar (ns, Nil)) (ZVar (y, Nil)))))) (CSPParAction a [x]) (rep_CSPRepInterlNS a ns y xs))"

 
fun delete_from_list
where
  "delete_from_list x Nil = Nil"
| "delete_from_list x [v] = (case x = v of
                                True \<Rightarrow> Nil
                              | False \<Rightarrow> [v])"
| "delete_from_list x (v # va) = (case x = v of
                                     True \<Rightarrow> delete_from_list x va
                                   | False \<Rightarrow> (v # (delete_from_list x va)))"

 
fun setminus
where
  "setminus Nil _ = Nil"
| "setminus (v # va) Nil = (v # va)"
| "setminus (v # va) (b # vb) = ((delete_from_list b (v # va)) @ (setminus (v # va) vb))"

 
fun free_var_CAction :: "CAction \<Rightarrow> ZVar list" and 
    free_var_comnd and 
    free_var_if
where
  "free_var_CAction (CActionCommand c) = (free_var_comnd c)"
| "free_var_CAction (CSPCommAction (ChanComm com xs) c) = ((get_chan_var xs) @ (free_var_CAction c))"
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
| "free_var_CAction (CSPUnParAction lst c nm) = (setminus (free_var_CAction c) (fvs free_var_ZGenFilt lst))"
| "free_var_CAction (CSPRepSeq lst c) = (setminus (free_var_CAction c) (fvs free_var_ZGenFilt lst))"
| "free_var_CAction (CSPRepExtChoice lst c) = (setminus (free_var_CAction c) (fvs free_var_ZGenFilt lst))"
| "free_var_CAction (CSPRepIntChoice lst c) = (setminus (free_var_CAction c) (fvs free_var_ZGenFilt lst))"
| "free_var_CAction (CSPRepParalNS cs lst ns c) = (setminus (free_var_CAction c) (fvs free_var_ZGenFilt lst))"
| "free_var_CAction (CSPRepParal cs lst c) = (setminus (free_var_CAction c) (fvs free_var_ZGenFilt lst))"
| "free_var_CAction (CSPRepInterlNS lst ns c) = (setminus (free_var_CAction c) (fvs free_var_ZGenFilt lst))"
| "free_var_CAction (CSPRepInterl lst c) = (setminus (free_var_CAction c) (fvs free_var_ZGenFilt lst))"
| "free_var_CAction _ = Nil"
| "free_var_comnd (CAssign v e) = v"
| "free_var_comnd (CIf ga) = free_var_if ga"
| "free_var_comnd (CVarDecl z c) = (setminus (free_var_CAction c) (fvs free_var_ZGenFilt z))"
| "free_var_comnd (CAssumpt n p1 p2) = Nil"
| "free_var_comnd (CAssumpt1 n p) = Nil"
| "free_var_comnd (CPrefix p1 p2) = Nil"
| "free_var_comnd (CPrefix1 p) = Nil"
| "free_var_comnd (CommandBrace z) = (free_var_ZPred z)"
| "free_var_comnd (CommandBracket z) = (free_var_ZPred z)"
| "free_var_comnd (CValDecl z c) = (setminus (free_var_CAction c) (fvs free_var_ZGenFilt z))"
| "free_var_comnd (CResDecl z c) = (setminus (free_var_CAction c) (fvs free_var_ZGenFilt z))"
| "free_var_comnd (CVResDecl z c) = (setminus (free_var_CAction c) (fvs free_var_ZGenFilt z))"
| "free_var_if (CircGAction p a) = ((free_var_ZPred p) @ (free_var_CAction a))"
| "free_var_if (CircThenElse ga gb) = ((free_var_if ga) @ (free_var_if gb))"
| "free_var_if (CircElse (CircusAction a)) = (free_var_CAction a)"
| "free_var_if (CircElse (ParamActionDecl x (CircusAction a))) = (setminus (free_var_CAction a) (fvs free_var_ZGenFilt x))"

 
fun member
where
  "member x Nil = False"
| "member x (b # y) = (if  x= b then True else member x y)"

 
fun union
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
| "elem_by eq0 y (x # xs) = (eq0 y x | elem_by eq0 y xs)"

 
fun isPrefixOf :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "isPrefixOf Nil _ = True"
| "isPrefixOf _ Nil = False"
| "isPrefixOf (x # xs) (y # ys) = (x= y & isPrefixOf xs ys)"

 
fun get_ZVar_st
where
  "get_ZVar_st (a, x) = (case (isPrefixOf ''st_var_'' a) of
                            True \<Rightarrow> [a]
                          | _ \<Rightarrow> Nil)"

 
fun is_ZVar_st
where
  "is_ZVar_st a = isPrefixOf ''st_var_'' a"

 
fun rename_ZExpr :: "ZExpr \<Rightarrow> ZExpr"
where
  "rename_ZExpr (ZVar (va, x)) = (case (is_ZVar_st va) of
                                     True \<Rightarrow> (ZVar (''v_'' @ va, x))
                                   | False \<Rightarrow> (ZVar (va, x)))"
| "rename_ZExpr (ZInt zi) = (ZInt zi)"
| "rename_ZExpr (ZCall xpr1 xpr2) = (ZCall (rename_ZExpr xpr1) (rename_ZExpr xpr2))"

 
fun bindingsVar :: "(ZVar * ZExpr) list \<Rightarrow> (ZVar * ZExpr) list"
where
  "bindingsVar Nil = Nil"
| "bindingsVar [((va, x), b)] = (case (is_ZVar_st va) of
                                    True \<Rightarrow> [((''v_'' @ va, x), (rename_ZExpr b))]
                                  | False \<Rightarrow> [((va, x), (rename_ZExpr b))])"
| "bindingsVar (((va, x), b) # xs) = (case (is_ZVar_st va) of
                                         True \<Rightarrow> [((''v_'' @ va, x), (rename_ZExpr b))] @ (bindingsVar xs)
                                       | False \<Rightarrow> [((va, x), (rename_ZExpr b))] @ (bindingsVar xs))"

 
fun rename_vars_CParameter :: "CParameter \<Rightarrow> CParameter"
where
  "rename_vars_CParameter (ChanInp zn) = (ChanInp zn)"
| "rename_vars_CParameter (ChanInpPred zn zp) = (ChanInpPred zn (rename_ZPred zp))"
| "rename_vars_CParameter (ChanOutExp ze) = (ChanOutExp (rename_ZExpr ze))"
| "rename_vars_CParameter (ChanDotExp ze) = (ChanDotExp (rename_ZExpr ze))"

 
fun rename_vars_Comm :: "Comm \<Rightarrow> Comm"
where
  "rename_vars_Comm (ChanComm zn cpls) = (ChanComm zn (map rename_vars_CParameter cpls))"
| "rename_vars_Comm (ChanGenComm zn zexprls cpls) = (ChanGenComm zn (map rename_ZExpr zexprls) (map rename_vars_CParameter cpls))"

 
fun rename_vars_Zvar
where
  "rename_vars_Zvar (a, x) = (case (isPrefixOf ''st_var_'' a) of
                                 True \<Rightarrow> ((join_name ''v'' a), x)
                               | _ \<Rightarrow> (a, x))"

 
fun rename_vars_CAction :: "CAction \<Rightarrow> CAction" and 
    rename_vars_CCommand :: "CCommand \<Rightarrow> CCommand" and 
    rename_vars_CGActions :: "CGActions \<Rightarrow> CGActions"
where
  "rename_vars_CAction (CActionCommand cmd) = (CActionCommand (rename_vars_CCommand cmd))"
| "rename_vars_CAction (CActionName zn) = (CActionName zn)"
| "rename_vars_CAction CSPSkip = CSPSkip"
| "rename_vars_CAction CSPStop = CSPStop"
| "rename_vars_CAction CSPChaos = CSPChaos"
| "rename_vars_CAction (CSPCommAction c a) = (CSPCommAction (rename_vars_Comm c) (rename_vars_CAction a))"
| "rename_vars_CAction (CSPGuard zp a) = (CSPGuard (rename_ZPred zp) (rename_vars_CAction a))"
| "rename_vars_CAction (CSPSeq a1 a2) = (CSPSeq (rename_vars_CAction a1) (rename_vars_CAction a2))"
| "rename_vars_CAction (CSPExtChoice a1 a2) = (CSPExtChoice (rename_vars_CAction a1) (rename_vars_CAction a2))"
| "rename_vars_CAction (CSPIntChoice a1 a2) = (CSPIntChoice (rename_vars_CAction a1) (rename_vars_CAction a2))"
| "rename_vars_CAction (CSPNSParal ns1 cs ns2 a1 a2) = (CSPNSParal ns1 cs ns2 (rename_vars_CAction a1) (rename_vars_CAction a2))"
| "rename_vars_CAction (CSPParal cs a1 a2) = (CSPParal cs (rename_vars_CAction a1) (rename_vars_CAction a2))"
| "rename_vars_CAction (CSPNSInter ns1 ns2 a1 a2) = (CSPNSInter ns1 ns2 (rename_vars_CAction a1) (rename_vars_CAction a2))"
| "rename_vars_CAction (CSPInterleave a1 a2) = (CSPInterleave (rename_vars_CAction a1) (rename_vars_CAction a2))"
| "rename_vars_CAction (CSPHide a cs) = (CSPHide (rename_vars_CAction a) cs)"
| "rename_vars_CAction (CSPParAction zn zexprls) = (CSPParAction zn (map rename_ZExpr zexprls))"
| "rename_vars_CAction (CSPRenAction zn crpl) = (CSPRenAction zn crpl)"
| "rename_vars_CAction (CSPRecursion zn a) = (CSPRecursion zn (rename_vars_CAction a))"
| "rename_vars_CAction (CSPUnParAction zgf a zn) = (CSPUnParAction zgf (rename_vars_CAction a) zn)"
| "rename_vars_CAction (CSPRepSeq zgf a) = (CSPRepSeq zgf (rename_vars_CAction a))"
| "rename_vars_CAction (CSPRepExtChoice zgf a) = (CSPRepExtChoice zgf (rename_vars_CAction a))"
| "rename_vars_CAction (CSPRepIntChoice zgf a) = (CSPRepIntChoice zgf (rename_vars_CAction a))"
| "rename_vars_CAction (CSPRepParalNS cs zgf ns a) = (CSPRepParalNS cs zgf ns (rename_vars_CAction a))"
| "rename_vars_CAction (CSPRepParal cs zgf a) = (CSPRepParal cs zgf (rename_vars_CAction a))"
| "rename_vars_CAction (CSPRepInterlNS zgf ns a) = (CSPRepInterlNS zgf ns (rename_vars_CAction a))"
| "rename_vars_CAction (CSPRepInterl zgf a) = (CSPRepInterl zgf (rename_vars_CAction a))"
| "rename_vars_CCommand (CAssign zvarls1 zexprls) = (CAssign (map rename_vars_Zvar zvarls1) (map rename_ZExpr zexprls))"
| "rename_vars_CCommand (CIf ga) = (CIf (rename_vars_CGActions ga))"
| "rename_vars_CCommand (CVarDecl zgf a) = (CVarDecl zgf (rename_vars_CAction a))"
| "rename_vars_CCommand (CAssumpt znls zp1 zp2) = (CAssumpt znls (rename_ZPred zp1) zp2)"
| "rename_vars_CCommand (CAssumpt1 znls zp) = (CAssumpt1 znls zp)"
| "rename_vars_CCommand (CPrefix zp1 zp2) = (CPrefix (rename_ZPred zp1) zp2)"
| "rename_vars_CCommand (CPrefix1 zp) = (CPrefix1 zp)"
| "rename_vars_CCommand (CommandBrace zp) = (CommandBrace zp)"
| "rename_vars_CCommand (CommandBracket zp) = (CommandBracket zp)"
| "rename_vars_CCommand (CValDecl zgf a) = (CValDecl zgf (rename_vars_CAction a))"
| "rename_vars_CCommand (CResDecl zgf a) = (CResDecl zgf (rename_vars_CAction a))"
| "rename_vars_CCommand (CVResDecl zgf a) = (CVResDecl zgf (rename_vars_CAction a))"
| "rename_vars_CGActions (CircGAction zp a) = (CircGAction (rename_ZPred zp) (rename_vars_CAction a))"
| "rename_vars_CGActions (CircThenElse cga1 cga2) = (CircThenElse (rename_vars_CGActions cga1) (rename_vars_CGActions cga2))"
| "rename_vars_CGActions (CircElse pa) = (CircElse pa)"

 
fun intersect
where
  "intersect Nil y = Nil"
| "intersect (a # x) y = (if member a y then a # (intersect x y)
                          else intersect x y)"


end
