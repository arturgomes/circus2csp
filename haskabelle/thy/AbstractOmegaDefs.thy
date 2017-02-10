section "Auxiliary Definitions for Omega functions"

theory AbstractOmegaDefs imports OmegaDefs AST Prelude begin

text{*Concatenation of two names - Used for the CSP renaming of Process+StateVariables*}
fun "abs_join_name"
where
  "abs_join_name n v = (n @ (''_'' @ v))"
subsection "Manipulating Lists"

fun "abs_inListVar"
where
  "abs_inListVar x Nil = False"
| "abs_inListVar x [va] = (case x = va of
                          True \<Rightarrow> True
                        | _ \<Rightarrow> False)"
| "abs_inListVar x (va # vst) = (case x = va of
                                True \<Rightarrow> True
                              | _ \<Rightarrow> abs_inListVar x vst)"

 
fun "abs_delete_from_list"
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

lemma thm_member: "abs_member x xs = member x xs"
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case 
  proof (induct xs)
    case Nil
    then show ?case by simp
  next
    case (Cons a xs)
    then show ?case by simp
  qed

qed
  
  
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
lemma thm_remdups: "abs_remdups x = remdups x"
proof (induct x)
  case Nil
  then show ?case by auto
next
  case (Cons a x)
  then show ?case 
  proof (induct x)
    case Nil
    then show ?case by auto
  next
    case (Cons a x)
    then show ?case
      by (simp add: thm_member)
  qed
    
qed
  
  
fun abs_subset
where
  "abs_subset xs ys = list_all (% arg0 . abs_member arg0 ys) xs"


subsection"Free Variables functions" 
fun abs_free_var_ZGenFilt
where
  "abs_free_var_ZGenFilt (Choose v e) = [v]"
| "abs_free_var_ZGenFilt (Check p) = Nil"
| "abs_free_var_ZGenFilt (Evaluate v e1 e2) = Nil"

 
fun abs_free_var_ZPred :: "ZPred \<Rightarrow> ZVar list"
where
  "abs_free_var_ZPred (ZFalse p) = Nil"
| "abs_free_var_ZPred (ZTrue p) = Nil"
| "abs_free_var_ZPred (ZAnd a b) = (abs_free_var_ZPred a @ abs_free_var_ZPred b)"
| "abs_free_var_ZPred x = Nil"

 
fun abs_fvs
where
  "abs_fvs f Nil = Nil"
| "abs_fvs f (e # es) = (f e @ (abs_fvs f es))"

 
function (sequential) abs_free_var_ZExpr :: "ZExpr \<Rightarrow> ZVar list"
where
  "abs_free_var_ZExpr (ZVar v) = [v]"
| "abs_free_var_ZExpr (ZInt c) = Nil"
| "abs_free_var_ZExpr (ZSetDisplay exls) = abs_fvs abs_free_var_ZExpr exls"
| "abs_free_var_ZExpr (ZSeqDisplay exls) = abs_fvs abs_free_var_ZExpr exls"
| "abs_free_var_ZExpr (ZCall ex ex2) = abs_free_var_ZExpr ex2"
| "abs_free_var_ZExpr _ = Nil"
  by pat_completeness auto
 
fun abs_free_var_CAction :: "CAction \<Rightarrow> ZVar list"
where
  "abs_free_var_CAction CSPSkip = Nil"
| "abs_free_var_CAction CSPStop = Nil"
| "abs_free_var_CAction CSPChaos = Nil"
| "abs_free_var_CAction (CSPSeq ca cb) = ((abs_free_var_CAction ca) @ (abs_free_var_CAction cb))"
| "abs_free_var_CAction (CSPExtChoice ca cb) = ((abs_free_var_CAction ca) @ (abs_free_var_CAction cb))"
| "abs_free_var_CAction (CSPCommAction v va) = Nil"    

lemma thm_free_var_CAction: "abs_free_var_CAction c = free_var_CAction c" 
  proof (induction c)
    case CSPSkip
    then show ?case by simp
  next
    case CSPStop
    then show ?case by simp
  next
    case CSPChaos
    then show ?case by simp
  next
    case (CSPCommAction x1 c)
    then show ?case by simp
  next
    case (CSPSeq c1 c2)
    then show ?case by simp
  next
    case (CSPExtChoice c1 c2)
    then show ?case by simp
  qed

subsection"Production of Get and Set" 

text{*We have to create signals with gets and sets carrying the values of the state variables
before an action can occur when we translate from state-rich Circus processes into stateless ones.*}
fun abs_make_get_com :: "ZName list \<Rightarrow> CAction \<Rightarrow> CAction"
where
  "abs_make_get_com [x] c = (CSPCommAction (ChanComm ''mget'' [ChanDotExp (ZVar (x, Nil)), ChanInp (''v_'' @ x)]) c)"
| "abs_make_get_com (x # xs) c = (CSPCommAction (ChanComm ''mget'' [ChanDotExp (ZVar (x, Nil)), ChanInp (''v_'' @ x)]) (abs_make_get_com xs c))"
| "abs_make_get_com x c = c"


lemma thm_make_get_com: "abs_make_get_com ys c = make_get_com ys c" 
  proof (induction ys arbitrary: c)
    case Nil
    then show ?case by simp
  next
    case (Cons a ys)
    then show ?case 
      proof (induct ys)
        case Nil
        then show ?case by simp
      next
        case (Cons a xs)
        then show ?case by simp
      qed
  qed

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

lemma thm_rv_CAction: "abs_rename_vars_CAction x = rename_vars_CAction x" 
  proof (induct x)
    case CSPSkip
    then show ?case by simp
  next
    case CSPStop
    then show ?case  by simp
  next
    case CSPChaos
    then show ?case  by simp
  next
    case (CSPCommAction x1 x)
    then show ?case  by simp
  next
    case (CSPSeq x1 x2)
    then show ?case by simp
  next
    case (CSPExtChoice x1 x2)
    then show ?case by auto
qed
 
fun abs_getFV
where
  "abs_getFV xs = Nil"


end
