theory OmegaDefs
imports AST Prelude
begin
 
fun join_name
where
  "join_name n v = (n @ (''_'' @ v))"

 
fun free_var_ZGenFilt
where
  "free_var_ZGenFilt (Choose v e) = [v]"
| "free_var_ZGenFilt (Check p) = Nil"
| "free_var_ZGenFilt (Evaluate v e1 e2) = Nil"

 
fun free_var_ZPred :: "ZPred \<Rightarrow> ZVar list"
where
  "free_var_ZPred (ZFalse p) = Nil"
| "free_var_ZPred (ZTrue p) = Nil"
| "free_var_ZPred (ZAnd a b) = (free_var_ZPred a @ free_var_ZPred b)"
| "free_var_ZPred x = Nil"

 
fun fvs
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
 
fun make_get_com :: "ZName list \<Rightarrow> CAction \<Rightarrow> CAction"
where
  "make_get_com [x] c = (CSPCommAction (ChanComm ''mget'' [ChanDotExp (ZVar (x, Nil)), ChanInp (''v_'' @ x)]) c)"
| "make_get_com (x # xs) c = (CSPCommAction (ChanComm ''mget'' [ChanDotExp (ZVar (x, Nil)), ChanInp (''v_'' @ x)]) (make_get_com xs c))"
| "make_get_com x c = c"

 
fun make_set_com :: "(CAction \<Rightarrow> CAction) \<Rightarrow> ZVar list \<Rightarrow> ZExpr list \<Rightarrow> CAction \<Rightarrow> CAction"
where
  "make_set_com f [(x, _)] [y] c = (CSPCommAction (ChanComm ''mset'' [ChanDotExp (ZVar (x, Nil)), ChanOutExp y]) (f c))"
| "make_set_com f ((x, _) # xs) (y # ys) c = (CSPCommAction (ChanComm ''mset'' [ChanDotExp (ZVar (x, Nil)), ChanOutExp y]) (make_set_com f xs ys c))"
| "make_set_com f _ _ c = (f c)"
 
fun getWrtV
where
  "getWrtV xs = Nil"

 
fun rename_ZPred
where
  "rename_ZPred (ZFalse a) = (ZFalse a)"
| "rename_ZPred (ZTrue a) = (ZTrue a)"
| "rename_ZPred (ZAnd p1 p2) = (ZAnd (rename_ZPred p1) (rename_ZPred p2))"
| "rename_ZPred (ZPSchema sp) = (ZPSchema sp)"

 
fun inListVar
where
  "inListVar x Nil = False"
| "inListVar x [va] = (case x = va of
                          True \<Rightarrow> True
                        | _ \<Rightarrow> False)"
| "inListVar x (va # vst) = (case x = va of
                                True \<Rightarrow> True
                              | _ \<Rightarrow> inListVar x vst)"

 
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

 
fun member
where
  "member x Nil = False"
| "member x (b # y) = (if x = b then True else member x y)"

 
fun intersect
where
  "intersect Nil y = Nil"
| "intersect (a # x) y = (if member a y then a # (intersect x y)
                          else intersect x y)"

 
fun union
where
  "union Nil y = y"
| "union (a # x) y = (if (member a y) then (union x y)
                      else a # (union x y))"

 
fun elem_by :: "'a \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "elem_by _ Nil = False"
| "elem_by y (x # xs) = (y = x | elem_by y xs)"

 
fun isPrefixOf
where
  "isPrefixOf Nil _ = True"
| "isPrefixOf _ Nil = False"
| "isPrefixOf (x # xs) (y # ys) = (x = y & isPrefixOf xs ys)"

 
fun get_ZVar_st
where
  "get_ZVar_st (a, x) = (case (isPrefixOf ''st_var_'' a) of
                            True \<Rightarrow> [a]
                          | False \<Rightarrow> Nil)"

 
fun free_var_CAction :: "CAction \<Rightarrow> ZVar list"
where
  "free_var_CAction CSPSkip = Nil"
| "free_var_CAction CSPStop = Nil"
| "free_var_CAction CSPChaos = Nil"
| "free_var_CAction (CSPSeq ca cb) = ((free_var_CAction ca) @ (free_var_CAction cb))"
| "free_var_CAction (CSPExtChoice ca cb) = ((free_var_CAction ca) @ (free_var_CAction cb))"
| "free_var_CAction (CSPCommAction v va) = Nil"
 
fun is_ZVar_st
where
  "is_ZVar_st a = isPrefixOf ''st_var_'' a"

 
fun rename_ZExpr
where
  "rename_ZExpr (ZVar (va, x)) = (case (is_ZVar_st va) of
                                     True \<Rightarrow> (ZVar (''v_'' @ va, x))
                                   | False \<Rightarrow> (ZVar (va, x)))"
| "rename_ZExpr (ZInt zi) = (ZInt zi)"
| "rename_ZExpr (ZCall xpr1 xpr2) = (ZCall (rename_ZExpr xpr1) (rename_ZExpr xpr2))"
| "rename_ZExpr x = x"

 
fun bindingsVar
where
  "bindingsVar Nil = Nil"
| "bindingsVar [((va, x), b)] = (case (is_ZVar_st va) of
                                    True \<Rightarrow> [((''v_'' @ va, x), (rename_ZExpr b))]
                                  | False \<Rightarrow> [((va, x), (rename_ZExpr b))])"
| "bindingsVar (((va, x), b) # xs) = (case (is_ZVar_st va) of
                                         True \<Rightarrow> [((''v_'' @ va, x), (rename_ZExpr b))] @ (bindingsVar xs)
                                       | False \<Rightarrow> [((va, x), (rename_ZExpr b))] @ (bindingsVar xs))"

 
fun rename_vars_CAction
where
  "rename_vars_CAction CSPSkip = CSPSkip"
| "rename_vars_CAction CSPStop = CSPStop"
| "rename_vars_CAction CSPChaos = CSPChaos"
| "rename_vars_CAction (CSPSeq a1 a2) = (CSPSeq (rename_vars_CAction a1) (rename_vars_CAction a2))"
| "rename_vars_CAction (CSPExtChoice a1 a2) = (CSPExtChoice (rename_vars_CAction a1) (rename_vars_CAction a2))"
| "rename_vars_CAction x = x"

 
fun remdups
where
  "remdups Nil = Nil"
| "remdups (x # xs) = (if (member x xs) then remdups xs
                       else x # remdups xs)"

 
fun getFV
where
  "getFV xs = Nil"

 
fun subset
where
  "subset xs ys = list_all (% arg0 . member arg0 ys) xs"


end
