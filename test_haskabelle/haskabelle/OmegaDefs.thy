theory OmegaDefs
imports AST Prelude
begin
 
fun join_name
where
  "join_name n v = (n @ (''_'' @ v))"
 
fun fvs :: "('t \<Rightarrow> 't1 list) \<Rightarrow> 't list \<Rightarrow> 't1 list"
where
  "fvs f Nil = Nil"
| "fvs f [e] = f e"
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

 
fun make_get_com :: "ZName list \<Rightarrow> CAction \<Rightarrow> CAction"
where
  "make_get_com [x] c = (CSPCommAction (ChanComm ''mget'' [ChanDotExp (ZVar (x, Nil)), ChanInp (''v_'' @ x)]) c)"
| "make_get_com (x # xs) c = (CSPCommAction (ChanComm ''mget'' [ChanDotExp (ZVar (x, Nil)), ChanInp (''v_'' @ x)]) (make_get_com xs c))"
| "make_get_com x c = c"

 
fun make_set_com
where
  "make_set_com f [(x, _)] [y] c = (CSPCommAction (ChanComm ''mset'' [ChanDotExp (ZVar (x, Nil)), ChanOutExp y]) (f c))"
| "make_set_com f ((x, _) # xs) (y # ys) c = (CSPCommAction (ChanComm ''mset'' [ChanDotExp (ZVar (x, Nil)), ChanOutExp y]) (make_set_com f xs ys c))"

 
fun getWrtV :: "'t \<Rightarrow> 't1 list"
where
  "getWrtV xs = Nil"

 
fun rename_ZPred :: "ZPred \<Rightarrow> ZPred"
where
  "rename_ZPred (ZFalse a) = (ZFalse a)"
| "rename_ZPred (ZTrue a) = (ZTrue a)"
| "rename_ZPred (ZAnd p1 p2) = (ZAnd (rename_ZPred p1) (rename_ZPred p2))"
 
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

 
 
fun delete_from_list :: "'t \<Rightarrow> 't list \<Rightarrow> 't list"
where
  "delete_from_list x Nil = Nil"
| "delete_from_list x [v] = (case x = v of
                                True \<Rightarrow> Nil
                              | False \<Rightarrow> [v])"
| "delete_from_list x (v # va) = (case x = v of
                                     True \<Rightarrow> delete_from_list x va
                                   | False \<Rightarrow> (v # (delete_from_list x va)))"

 
fun setminus :: "'t list \<Rightarrow> 't list \<Rightarrow> 't list"
where
  "setminus Nil _ = Nil"
| "setminus (v # va) Nil = (v # va)"
| "setminus (v # va) (b # vb) = ((delete_from_list b (v # va)) @ (setminus (v # va) vb))"

 
fun free_var_CAction :: "CAction \<Rightarrow> ZVar list"
where
  "free_var_CAction (CSPCommAction (ChanComm com xs) c) = ((get_chan_var xs) @ (free_var_CAction c))"
| "free_var_CAction CSPSkip = Nil"

 
fun member :: "'t \<Rightarrow> 't list \<Rightarrow> bool"
where
  "member x Nil = False"
| "member x (b # y) = (if x = b then True else member x y)"

 
fun union :: "'t list \<Rightarrow> 't list \<Rightarrow> 't list"
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
| "isPrefixOf (x # xs) (y # ys) = (x = y & isPrefixOf xs ys)"

 
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
| "rename_ZExpr x = x"
  

 
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

 
fun rename_vars_CAction :: "CAction \<Rightarrow> CAction"
where
  "rename_vars_CAction CSPSkip = CSPSkip"
| "rename_vars_CAction (CSPCommAction c a) = (CSPCommAction (rename_vars_Comm c) (rename_vars_CAction a))"


 
fun intersect :: "'t list \<Rightarrow> 't list \<Rightarrow> 't list"
where
  "intersect Nil y = Nil"
| "intersect (a # x) y = (if member a y then a # (intersect x y)
                          else intersect x y)"


end
