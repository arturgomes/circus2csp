section "Abstract Auxiliary Definitions for Omega functions"

theory AbstractOmegaDefs imports AST Prelude OmegaDefs begin

  

subsection"Production of Get and Set" 
definition set_to_list :: "'a set \<Rightarrow> 'a list"
  where "set_to_list s = (SOME l. set l = s)"
    
lemma  set_set_to_list:
   "finite s \<Longrightarrow> set (set_to_list s) = s"
unfolding set_to_list_def by (metis (mono_tags) finite_list some_eq_ex)    
text{*Concatenation of two names - Used for the CSP renaming of Process+StateVariables*}
fun abs_join_name
where
  "abs_join_name n v = (n @ (''_'' @ v))"
subsection "Manipulating Lists"

fun abs_inListVar
where
  "abs_inListVar x Nil = False"
| "abs_inListVar x [va] = (case x = va of
                          True \<Rightarrow> True
                        | _ \<Rightarrow> False)"
| "abs_inListVar x (va # vst) = (case x = va of
                                True \<Rightarrow> True
                              | _ \<Rightarrow> abs_inListVar x vst)"

 
fun abs_delete_from_list
where
  "abs_delete_from_list x Nil = Nil"
| "abs_delete_from_list x [v] = (case x = v of
                                True \<Rightarrow> Nil
                              | False \<Rightarrow> [v])"
| "abs_delete_from_list x (v # va) = (case x = v of
                                     True \<Rightarrow> abs_delete_from_list x va
                                   | False \<Rightarrow> (v # (abs_delete_from_list x va)))"

 
fun abs_setminus
where
  "abs_setminus Nil _ = Nil"
| "abs_setminus (v # va) Nil = (v # va)"
| "abs_setminus (v # va) (b # vb) = ((abs_delete_from_list b (v # va)) @ (abs_setminus (v # va) vb))"

 
fun abs_member
where
  "abs_member x Nil = False"
| "abs_member x (b # y) = (if x = b then True else abs_member x y)"
 
fun abs_intersect
where
  "abs_intersect Nil y = Nil"
| "abs_intersect (a # x) y = (if abs_member a y then a # (abs_intersect x y)
                          else abs_intersect x y)"

fun abs_union
where
  "abs_union Nil y = y"
| "abs_union (a # x) y = (if (abs_member a y) then (abs_union x y)
                      else a # (abs_union x y))"

 
fun abs_elem_by :: "'a \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "abs_elem_by _ Nil = False"
| "abs_elem_by y (x # xs) = (y = x | abs_elem_by y xs)"

 
fun abs_isPrefixOf
where
  "abs_isPrefixOf Nil _ = True"
| "abs_isPrefixOf _ Nil = False"
| "abs_isPrefixOf (x # xs) (y # ys) = (x = y & abs_isPrefixOf xs ys)"
 
fun abs_remdups
where
  "abs_remdups Nil = Nil"
| "abs_remdups (x # xs) = (if (abs_member x xs) then abs_remdups xs
                       else x # abs_remdups xs)"

fun abs_subset
where
  "abs_subset xs ys = list_all (% arg0 . abs_member arg0 ys) xs"


subsection"Free Variables functions" 
fun abs_free_var_ZGenFilt
where
  "abs_free_var_ZGenFilt (Choose v e) = {v}"
| "abs_free_var_ZGenFilt (Check p) = {}"
| "abs_free_var_ZGenFilt (Evaluate v e1 e2) = {}"

 
fun abs_free_var_ZPred :: "ZPred \<Rightarrow> ZVar set"
where
  "abs_free_var_ZPred (ZFalse p) = {}"
| "abs_free_var_ZPred (ZTrue p) = {}"
| "abs_free_var_ZPred (ZAnd a b) = (abs_free_var_ZPred a \<union> abs_free_var_ZPred b)"
| "abs_free_var_ZPred x = {}"

fun abs_fv_ZExpr
where
  "abs_fv_ZExpr (ZVar v) = {v}"
| "abs_fv_ZExpr (ZInt c) = {}"
| "abs_fv_ZExpr (ZSetDisplay x) = {y. \<exists> a \<in> (set x) . y \<in> abs_fv_ZExpr a}"
| "abs_fv_ZExpr (ZSeqDisplay x) = {y. \<exists> a \<in> (set x) . y \<in> abs_fv_ZExpr a}"
| "abs_fv_ZExpr (ZCall ex ex2) = abs_fv_ZExpr ex2"
| "abs_fv_ZExpr _ = {}"
 
fun abs_fv_CAction :: "CAction \<Rightarrow> ZVar set"
where
  "abs_fv_CAction CSPSkip = {}"
| "abs_fv_CAction CSPStop = {}"
| "abs_fv_CAction CSPChaos = {}"
| "abs_fv_CAction (CSPSeq ca cb) = ((abs_fv_CAction ca) \<union> (abs_fv_CAction cb))"
| "abs_fv_CAction (CSPExtChoice ca cb) = ((abs_fv_CAction ca) \<union> (abs_fv_CAction cb))"
| "abs_fv_CAction (CSPCommAction v va) = {}"   
lemma set_to_list_FV_Union: "set_to_list (abs_fv_CAction  (CSPExtChoice CSPSkip CSPSkip)) =  set_to_list (abs_fv_CAction CSPSkip) @  set_to_list (abs_fv_CAction CSPSkip) "
  apply auto
  by (meson finite.emptyI set_empty set_set_to_list)
    
lemma "set_to_list (abs_fv_CAction  (CSPExtChoice a1 a2)) =  set_to_list (abs_fv_CAction a1) @  set_to_list (abs_fv_CAction a2) "
  apply simp
  sorry

lemma "set_to_list (abs_fv_CAction x) = free_var_CAction x " 
proof (induct x)
  case CSPSkip
  then show ?case
    using set_set_to_list by force
next
  case CSPStop
  then show ?case
    using set_set_to_list by force
next
  case CSPChaos
  then show ?case
    using set_set_to_list by force
next
  case (CSPCommAction x1 x)
  then show ?case
    using set_set_to_list by force
next
  case (CSPSeq x1 x2)
  then show ?case sorry
next
  case (CSPExtChoice x1 x2)
  then show ?case sorry
qed
  
  
  
    
text{*We have to create signals with gets and sets carrying the values of the state variables
before an action can occur when we translate from state-rich Circus processes into stateless ones.*}

fun abs_make_get_com :: "ZName list \<Rightarrow> CAction \<Rightarrow> CAction"
where
  "abs_make_get_com [x] c = (CSPCommAction (ChanComm ''mget'' [ChanDotExp (ZVar (x, Nil)), ChanInp (''v_'' @ x)]) c)"
| "abs_make_get_com (x # xs) c = (CSPCommAction (ChanComm ''mget'' [ChanDotExp (ZVar (x, Nil)), ChanInp (''v_'' @ x)]) (abs_make_get_com xs c))"
| "abs_make_get_com x c = c"

 
fun abs_make_set_com :: "(CAction \<Rightarrow> CAction) \<Rightarrow> ZVar list \<Rightarrow> ZExpr list \<Rightarrow> CAction \<Rightarrow> CAction"
where
  "abs_make_set_com f [(x, _)] [y] c = (CSPCommAction (ChanComm ''mset'' [ChanDotExp (ZVar (x, Nil)), ChanOutExp y]) (f c))"
| "abs_make_set_com f ((x, _) # xs) (y # ys) c = (CSPCommAction (ChanComm ''mset'' [ChanDotExp (ZVar (x, Nil)), ChanOutExp y]) (abs_make_set_com f xs ys c))"
| "abs_make_set_com f _ _ c = (f c)"

subsection"Production of WrtV" 
  
fun abs_getWrtV
where
  "abs_getWrtV xs = Nil"

subsection"Renaming Variables" 
 
 
fun abs_get_ZVar_st
where
  "abs_get_ZVar_st (a, x) = (case (abs_isPrefixOf ''st_var_'' a) of
                            True \<Rightarrow> [a]
                          | False \<Rightarrow> Nil)"
fun abs_is_ZVar_st
where
  "abs_is_ZVar_st a = abs_isPrefixOf ''st_var_'' a"

fun abs_rename_ZPred
where
  "abs_rename_ZPred (ZFalse a) = (ZFalse a)"
| "abs_rename_ZPred (ZTrue a) = (ZTrue a)"
| "abs_rename_ZPred (ZAnd p1 p2) = (ZAnd (abs_rename_ZPred p1) (abs_rename_ZPred p2))"
| "abs_rename_ZPred (ZPSchema sp) = (ZPSchema sp)"

fun abs_rename_ZExpr
where
  "abs_rename_ZExpr (ZVar (va, x)) = (case (abs_is_ZVar_st va) of
                                     True \<Rightarrow> (ZVar (''v_'' @ va, x))
                                   | False \<Rightarrow> (ZVar (va, x)))"
| "abs_rename_ZExpr (ZInt zi) = (ZInt zi)"
| "abs_rename_ZExpr (ZCall xpr1 xpr2) = (ZCall (abs_rename_ZExpr xpr1) (abs_rename_ZExpr xpr2))"
| "abs_rename_ZExpr x = x"

 
fun abs_bindingsVar
where
  "abs_bindingsVar Nil = Nil"
| "abs_bindingsVar [((va, x), b)] = (case (abs_is_ZVar_st va) of
                                    True \<Rightarrow> [((''v_'' @ va, x), (abs_rename_ZExpr b))]
                                  | False \<Rightarrow> [((va, x), (abs_rename_ZExpr b))])"
| "abs_bindingsVar (((va, x), b) # xs) = (case (abs_is_ZVar_st va) of
                                         True \<Rightarrow> [((''v_'' @ va, x), (abs_rename_ZExpr b))] @ (abs_bindingsVar xs)
                                       | False \<Rightarrow> [((va, x), (abs_rename_ZExpr b))] @ (abs_bindingsVar xs))"

 
fun abs_rename_vars_CAction
where
  "abs_rename_vars_CAction CSPSkip = CSPSkip"
| "abs_rename_vars_CAction CSPStop = CSPStop"
| "abs_rename_vars_CAction CSPChaos = CSPChaos"
| "abs_rename_vars_CAction (CSPSeq a1 a2) = (CSPSeq (abs_rename_vars_CAction a1) (abs_rename_vars_CAction a2))"
| "abs_rename_vars_CAction (CSPExtChoice a1 a2) = (CSPExtChoice (abs_rename_vars_CAction a1) (abs_rename_vars_CAction a2))"
| "abs_rename_vars_CAction x = x"

 
 
fun abs_getFV
where
  "abs_getFV xs = Nil"


end
