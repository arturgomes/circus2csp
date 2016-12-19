theory MappingFunStatelessCircus
imports AST Prelude
begin
 
fun filter_state_comp :: "((ZName * ZVar) * ZExpr) list \<Rightarrow> ZVar list"
where
  "filter_state_comp Nil = Nil"
| "filter_state_comp [(u1, (v, u2))] = [v]"
| "filter_state_comp ((u1, (v, u2)) # xs) = ([v] @ (filter_state_comp xs))"

 
fun get_guard_pair :: "CGActions \<Rightarrow> (ZPred * CAction) list"
where
  "get_guard_pair (CircThenElse (CircGAction g2 a2) (CircGAction g3 a3)) = [(g2, a2), (g3, a3)]"
| "get_guard_pair (CircThenElse (CircGAction g1 a1) glx) = ([(g1, a1)] @ (get_guard_pair glx))"
| "get_guard_pair _ = []"

 
fun get_proc_name :: "ZName \<Rightarrow> ((ZName * ZVar) * ZExpr) list \<Rightarrow> ZName"
where
  "get_proc_name x [(a, ((va, x1), b))] 
      = (case eq x va of
              True \<Rightarrow> a
            | _ \<Rightarrow> '''')"
| "get_proc_name x ((a, ((va, x1), b)) # vst)
       = (case eq x va of
              True \<Rightarrow> a
            | _ \<Rightarrow> get_proc_name x vst)"

 
fun make_get_com :: "((ZName * ZVar) * ZExpr) list \<Rightarrow> ZVar list \<Rightarrow> CAction \<Rightarrow> CAction"
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

 
fun fvs :: "('t \<Rightarrow> 't1 list) \<Rightarrow> 't list \<Rightarrow> 't1 list"
where
  "fvs f Nil = Nil"
| "fvs f (e # es) = (f e @ (fvs f es))"

 
fun rename_vars_CReplace :: "'t \<Rightarrow> CReplace \<Rightarrow> CReplace"
where
  "rename_vars_CReplace lst (CRename zvarls1 zvarls) = (CRename zvarls1 zvarls)"
| "rename_vars_CReplace lst (CRenameAssign zvarls1 zvarls) = (CRenameAssign zvarls1 zvarls)"

 
fun inListVar :: "('a :: eq) \<Rightarrow> ('a :: eq) list \<Rightarrow> bool"
where
  "inListVar x Nil = False"
| "inListVar x [va] = (case eq x va of
                          True \<Rightarrow> True
                        | _ \<Rightarrow> False)"
| "inListVar x (va # vst) = (case eq x va of
                                True \<Rightarrow> True
                              | _ \<Rightarrow> inListVar x vst)"

 
fun rename_ZExpr :: "string list \<Rightarrow> ZExpr \<Rightarrow> ZExpr" and 
    bindingsVar :: "string list \<Rightarrow> (ZVar * ZExpr) list \<Rightarrow> (ZVar * ZExpr) list"
where
  "rename_ZExpr lst (ZVar (va, x)) = (case (inListVar va lst) of
                                         True \<Rightarrow> (ZVar (''v_'' @ va, x))
                                       | False \<Rightarrow> (ZVar (va, x)))"
| "rename_ZExpr lst (ZInt zi) = (ZInt zi)"
| "rename_ZExpr lst (ZGiven gv) = (ZGiven gv)"
| "rename_ZExpr lst (ZFree0 va) = (ZFree0 va)"
| "rename_ZExpr lst (ZFree1 va xpr) = (ZFree1 va (rename_ZExpr lst xpr))"
| "rename_ZExpr lst (ZTuple xprlst) = (ZTuple (map (rename_ZExpr lst) xprlst))"
| "rename_ZExpr lst (ZBinding xs) = (ZBinding (bindingsVar lst xs))"
| "rename_ZExpr lst (ZSetDisplay xprlst) = (ZSetDisplay (map (rename_ZExpr lst) xprlst))"
| "rename_ZExpr lst (ZSeqDisplay xprlst) = (ZSeqDisplay (map (rename_ZExpr lst) xprlst))"
| "rename_ZExpr lst (ZIntSet i1 i2) = (ZIntSet i1 i2)"
| "rename_ZExpr lst (ZGenerator zrl xpr) = (ZGenerator zrl (rename_ZExpr lst xpr))"
| "rename_ZExpr lst (ZCross xprlst) = (ZCross (map (rename_ZExpr lst) xprlst))"
| "rename_ZExpr lst (ZFreeType va lst1) = (ZFreeType va lst1)"
| "rename_ZExpr lst (ZPowerSet xpr b1 b2) = (ZPowerSet (rename_ZExpr lst xpr) b1 b2)"
| "rename_ZExpr lst (ZFuncSet expr1 expr2 b1 b2 b3 b4 b5 b6 b7) = (ZFuncSet (rename_ZExpr lst expr1) (rename_ZExpr lst expr2) b1 b2 b3 b4 b5 b6 b7)"
| "rename_ZExpr lst (ZSetComp lst1 (Some xpr)) = (ZSetComp lst1 (Some (rename_ZExpr lst xpr)))"
| "rename_ZExpr lst (ZSetComp lst1 None) = (ZSetComp lst1 None)"
| "rename_ZExpr lst (ZLambda lst1 xpr) = (ZLambda lst1 (rename_ZExpr lst xpr))"
| "rename_ZExpr lst (ZESchema zxp) = (ZESchema zxp)"
| "rename_ZExpr lst (ZGivenSet gs) = (ZGivenSet gs)"
| "rename_ZExpr lst ZUniverse = ZUniverse"
| "rename_ZExpr lst (ZCall xpr1 xpr2) = (ZCall (rename_ZExpr lst xpr1) (rename_ZExpr lst xpr2))"
| "rename_ZExpr lst (ZReln rl) = (ZReln rl)"
| "rename_ZExpr lst (ZFunc1 f1) = (ZFunc1 f1)"
| "rename_ZExpr lst (ZFunc2 f2) = (ZFunc2 f2)"
| "rename_ZExpr lst (ZStrange st) = (ZStrange st)"
| "rename_ZExpr lst (ZMu lst1 (Some xpr)) = (ZMu lst1 (Some (rename_ZExpr lst xpr)))"
| "rename_ZExpr lst (ZELet lst1 xpr1) = (ZELet (bindingsVar lst lst1) (rename_ZExpr lst xpr1))"
| "rename_ZExpr lst (ZIf_Then_Else zp xpr1 xpr2) = (ZIf_Then_Else zp (rename_ZExpr lst xpr1) (rename_ZExpr lst xpr2))"
| "rename_ZExpr lst (ZSelect xpr va) = (ZSelect xpr va)"
| "rename_ZExpr lst (ZTheta zs) = (ZTheta zs)"
| "bindingsVar lst Nil = Nil"
| "bindingsVar lst [((va, x), b)] = (case (inListVar va lst) of
                                        True \<Rightarrow> [((''v_'' @ va, x), (rename_ZExpr lst b))]
                                      | False \<Rightarrow> [((va, x), (rename_ZExpr lst b))])"
| "bindingsVar lst (((va, x), b) # xs) = (case (inListVar va lst) of
                                             True \<Rightarrow> [((''v_'' @ va, x), (rename_ZExpr lst b))] @ (bindingsVar lst xs)
                                           | False \<Rightarrow> [((va, x), (rename_ZExpr lst b))] @ (bindingsVar lst xs))"

 
fun rename_ZPred :: "string list \<Rightarrow> ZPred \<Rightarrow> ZPred"
where
  "rename_ZPred lst (ZFalse a) = (ZFalse a)"
| "rename_ZPred lst (ZTrue a) = (ZTrue a)"
| "rename_ZPred lst (ZAnd p1 p2) = (ZAnd (rename_ZPred lst p1) (rename_ZPred lst p2))"
| "rename_ZPred lst (ZOr p1 p2) = (ZOr (rename_ZPred lst p1) (rename_ZPred lst p2))"
| "rename_ZPred lst (ZImplies p1 p2) = (ZImplies (rename_ZPred lst p1) (rename_ZPred lst p2))"
| "rename_ZPred lst (ZIff p1 p2) = (ZIff (rename_ZPred lst p1) (rename_ZPred lst p2))"
| "rename_ZPred lst (ZNot p) = (ZNot (rename_ZPred lst p))"
| "rename_ZPred lst (ZExists lst1 p) = (ZExists lst1 (rename_ZPred lst p))"
| "rename_ZPred lst (ZExists_1 lst1 p) = (ZExists_1 lst1 (rename_ZPred lst p))"
| "rename_ZPred lst (ZForall lst1 p) = (ZForall lst1 (rename_ZPred lst p))"
| "rename_ZPred lst (ZPLet varxp p) = (ZPLet varxp (rename_ZPred lst p))"
| "rename_ZPred lst (ZEqual xpr1 xpr2) = (ZEqual (rename_ZExpr lst xpr1) (rename_ZExpr lst xpr2))"
| "rename_ZPred lst (ZMember xpr1 xpr2) = (ZMember (rename_ZExpr lst xpr1) (rename_ZExpr lst xpr2))"
| "rename_ZPred lst (ZPre sp) = (ZPre sp)"
| "rename_ZPred lst (ZPSchema sp) = (ZPSchema sp)"

 
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
  "rename_vars_CAction lst (CActionSchemaExpr zsexp) = (CActionSchemaExpr zsexp)"
| "rename_vars_CAction lst (CActionCommand cmd) = (CActionCommand (rename_vars_CCommand lst cmd))"
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
| "rename_vars_CAction lst x = x"
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

 
fun flip :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'c"
where
  "flip f x y = f y x"

 
fun nub'0
where
  "nub'0 Nil _ = Nil"
| "nub'0 (x # xs) ls = (if member x ls then nub'0 xs ls
                        else x # nub'0 xs (x # ls))"

 
fun nub :: "('a :: eq) list \<Rightarrow> ('a :: eq) list"
where
  "nub l = (let nub' = nub'0
            in nub' l Nil)"

 
fun intersectBy :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "intersectBy eq6 xs ys = ([x . x <- xs,
                                 list_ex (eq6 x) ys])"

 
definition intersect :: "('a :: eq) list \<Rightarrow> ('a :: eq) list \<Rightarrow> ('a :: eq) list"
where
  "intersect = intersectBy eq"

 
fun elem_by :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "elem_by _ _ Nil = False"
| "elem_by eq10 y (x # xs) = (eq10 y x | elem_by eq10 y xs)"

 
fun nubBy'2
where
  "nubBy'2 eq11 Nil _ = Nil"
| "nubBy'2 eq12 (y # ys) xs = (let env3 = eq12
                               in if elem_by eq12 y xs then nubBy'2 env3 ys xs
                                  else y # nubBy'2 env3 ys (y # xs))"

 
fun nubBy :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "nubBy eq7 Nil = Nil"
| "nubBy eq8 (x # xs) = (x # nubBy eq8 (filter (% y .
                                                  Not (eq8 x y)) xs))"
| "nubBy eq9 l = (let nubBy' = nubBy'2 eq9
                  in nubBy' l Nil)"

 
fun deleteBy :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "deleteBy _ _ Nil = Nil"
| "deleteBy eq4 x (y # ys) = (if eq4 x y then ys
                              else y # deleteBy eq4 x ys)"

 
definition delete :: "('a :: eq) \<Rightarrow> ('a :: eq) list \<Rightarrow> ('a :: eq) list"
where
  "delete = deleteBy eq"

 
definition \\ :: "('a :: eq) list \<Rightarrow> ('a :: eq) list \<Rightarrow> ('a :: eq) list"
where
  "\\ = foldl (flip delete)"

 
fun free_var_ZExpr :: "ZExpr \<Rightarrow> ZVar list"
where
  "free_var_ZExpr (ZVar v) = [v]"
| "free_var_ZExpr (ZInt c) = Nil"
| "free_var_ZExpr (ZTuple exls) = fvs free_var_ZExpr exls"
| "free_var_ZExpr (ZSetDisplay exls) = fvs free_var_ZExpr exls"
| "free_var_ZExpr (ZSeqDisplay exls) = fvs free_var_ZExpr exls"
| "free_var_ZExpr (ZCross exls) = fvs free_var_ZExpr exls"
| "free_var_ZExpr (ZPowerSet b e fs) = error ''Don't know what free vars of ZPowerSet are right now. Check back later''"
| "free_var_ZExpr (ZFuncSet d r f t (op o) oo s ne ff) = error ''Don't know what free vars of ZFree0 are right now. Check back later''"
| "free_var_ZExpr (ZLambda [Choose v e] a) = \\ (free_var_ZExpr a) [v]"
| "free_var_ZExpr (ZLambda _ a) = Nil"
| "free_var_ZExpr (ZCall ex ex2) = free_var_ZExpr ex2"
| "free_var_ZExpr (ZELet ves pr) = ((\\ (free_var_ZExpr pr) (map fst ves)) @ fvs free_var_ZExpr (map snd ves))"
| "free_var_ZExpr (ZSelect ex zv) = (free_var_ZExpr ex @ [zv])"
| "free_var_ZExpr _ = Nil"

 
fun free_var_ZPred :: "ZPred \<Rightarrow> ZVar list"
where
  "free_var_ZPred (ZFalse p) = error ''Don't know what free vars of ZFalse are right now. Check back later''"
| "free_var_ZPred (ZTrue p) = error ''Don't know what free vars of ZTrue are right now. Check back later''"
| "free_var_ZPred (ZAnd a b) = (free_var_ZPred a @ free_var_ZPred b)"
| "free_var_ZPred (ZOr a b) = (free_var_ZPred a @ free_var_ZPred b)"
| "free_var_ZPred (ZImplies a b) = (free_var_ZPred a @ free_var_ZPred b)"
| "free_var_ZPred (ZIff a b) = (free_var_ZPred a @ free_var_ZPred b)"
| "free_var_ZPred (ZNot a) = free_var_ZPred a"
| "free_var_ZPred (ZExists [Choose v e] a) = \\ (free_var_ZPred a) [v]"
| "free_var_ZPred (ZExists ls a) = error ''Don't know what free vars of ZExists are right now. Check back later''"
| "free_var_ZPred (ZExists_1 [Choose v e] a) = \\ (free_var_ZPred a) [v]"
| "free_var_ZPred (ZExists_1 ls a) = error ''Don't know what free vars of ZExists_1 are right now. Check back later''"
| "free_var_ZPred (ZForall [Choose v e] a) = \\ (free_var_ZPred a) [v]"
| "free_var_ZPred (ZForall ls a) = error ''Don't know what free vars of ZForall are right now. Check back later''"
| "free_var_ZPred (ZPLet ls a) = error ''Don't know what free vars of ZPLet are right now. Check back later''"
| "free_var_ZPred (ZEqual expa expb) = (free_var_ZExpr expa @ free_var_ZExpr expb)"
| "free_var_ZPred (ZMember expa expb) = free_var_ZExpr expa"
| "free_var_ZPred (ZPre zsexpr) = error ''Don't know what free vars of ZPre are right now. Check back later''"
| "free_var_ZPred (ZPSchema zsexpr) = error ''Don't know what free vars of ZPSchema are right now. Check back later''"

 
fun omega_CAction :: "((ZName * ZVar) * ZExpr) list \<Rightarrow> CAction \<Rightarrow> CAction" and 
    omega_prime_CAction :: "((ZName * ZVar) * ZExpr) list \<Rightarrow> CAction \<Rightarrow> CAction" and 
    rep_CSPRepSeq :: "((ZName * ZVar) * ZExpr) list \<Rightarrow> ZName \<Rightarrow> ZExpr list \<Rightarrow> CAction" and 
    rep_CSPRepIntChoice :: "((ZName * ZVar) * ZExpr) list \<Rightarrow> ZName \<Rightarrow> ZExpr list \<Rightarrow> CAction" and 
    rep_CSPRepExtChoice :: "((ZName * ZVar) * ZExpr) list \<Rightarrow> ZName \<Rightarrow> ZExpr list \<Rightarrow> CAction" and 
    rep_CSPRepParalNS :: "((ZName * ZVar) * ZExpr) list \<Rightarrow> ZName \<Rightarrow> ZName \<Rightarrow> ZName \<Rightarrow> string \<Rightarrow> ZExpr list \<Rightarrow> CAction" and 
    rep_CSPRepInterlNS :: "((ZName * ZVar) * ZExpr) list \<Rightarrow> ZName \<Rightarrow> ZName \<Rightarrow> string \<Rightarrow> ZExpr list \<Rightarrow> CAction" and 
    mk_guard_pair :: "((ZName * ZVar) * ZExpr) list \<Rightarrow> (ZPred * CAction) list \<Rightarrow> CGActions" and 
    make_set_com :: "((ZName * ZVar) * ZExpr) list \<Rightarrow> ZVar list \<Rightarrow> ZExpr list \<Rightarrow> CAction \<Rightarrow> CAction"
where
  "omega_CAction lst CSPSkip = CSPSkip"
| "omega_CAction lst CSPStop = CSPStop"
| "omega_CAction lst CSPChaos = CSPChaos"
| "omega_CAction lst (CSPCommAction (ChanComm c Nil) a) = (CSPCommAction (ChanComm c Nil) (omega_CAction lst a))"
| "omega_CAction lst (CSPCommAction (ChanComm c ((ChanOutExp e) # xs)) a) 
    = omega_CAction lst (CSPCommAction (ChanComm c ((ChanDotExp e) # xs)) a)"
| "omega_CAction lst (CSPSeq ca cb) = (CSPSeq (omega_CAction lst ca) (omega_CAction lst cb))"
| "omega_CAction lst (CSPIntChoice ca cb) = (CSPIntChoice (omega_CAction lst ca) (omega_CAction lst cb))"
| "omega_CAction lst (CSPCommAction (ChanComm c Nil) a) = (CSPCommAction (ChanComm c Nil) (omega_CAction lst a))"
| "omega_CAction lst (CSPHide a cs) = (CSPHide (omega_CAction lst a) cs)"
| "omega_CAction lst (CSPRecursion x c) = (CSPRecursion x (omega_CAction lst c))"
| "omega_CAction lst (CActionCommand (CommandBrace g)) = omega_CAction lst (CActionCommand (CPrefix g (ZTrue Nil)))"
| "omega_CAction lst (CActionCommand (CommandBracket g)) = omega_CAction lst (CActionCommand (CPrefix1 g))"
| "omega_CAction lst (CSPRenAction a (CRenameAssign left right)) = (CSPRenAction a (CRename right left))"
| "omega_CAction lst (CSPRepSeq [Choose (x, Nil) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1, Nil)])) 
    = (case eq x x1 of
            True \<Rightarrow> omega_CAction lst (rep_CSPRepSeq lst act xs)
          | _ \<Rightarrow> (CSPRepSeq [Choose (x, Nil) (ZSeqDisplay xs)] 
                              (omega_CAction lst (CSPParAction act [ZVar (x1, Nil)]))))"
| "omega_CAction lst (CSPRepSeq [Choose (x, Nil) v] act) 
    = (CSPRepSeq [Choose (x, Nil) v] (omega_CAction lst act))"
| "omega_CAction lst (CSPRepExtChoice [Choose (x, Nil) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1, Nil)])) 
    = (case eq x x1 of
            True \<Rightarrow> rep_CSPRepExtChoice lst act xs
          | _ \<Rightarrow> (CSPRepExtChoice [Choose (x, Nil) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1, Nil)])))"
| "omega_CAction lst (CSPRepExtChoice [Choose (x, Nil) v] act) 
    = (CSPRepExtChoice [Choose (x, Nil) v] (omega_CAction lst act))"
| "omega_CAction lst (CSPRepIntChoice [Choose (x, Nil) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1, Nil)])) 
    = (case eq x x1 of
            True \<Rightarrow> rep_CSPRepIntChoice lst act xs
          | _ \<Rightarrow> (CSPRepIntChoice [Choose (x, Nil) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1, Nil)])))"
| "omega_CAction lst (CSPRepIntChoice [Choose (x, Nil) v] act) 
    = (CSPRepIntChoice [Choose (x, Nil) v] (omega_CAction lst act))"
| "omega_CAction lst (CSPRepParalNS (CSExpr cs) [Choose (x, Nil) (ZSetDisplay lsx)] 
        (NSExprParam ns [ZVar (x1, Nil)]) (CSPParAction a [ZVar (x2, Nil)])) 
    = (case (eq x x1) & (eq x x2) of
           True \<Rightarrow> rep_CSPRepParalNS lst a cs ns x lsx
          | _ \<Rightarrow> (CSPRepParalNS (CSExpr cs) [Choose (x, Nil) (ZSetDisplay lsx)] 
                                (NSExprParam ns [ZVar (x1, Nil)]) (omega_CAction lst (CSPParAction a [ZVar (x2, Nil)]))))"
| "omega_CAction lst (CSPRepParalNS (CSExpr cs) [Choose (x, Nil) (ZSetDisplay lsx)] (NSExprParam ns [ZVar (x1, Nil)]) act) 
    = (CSPRepParalNS (CSExpr cs) [Choose (x, Nil) (ZSetDisplay lsx)] (NSExprParam ns [ZVar (x1, Nil)]) (omega_CAction lst act))"
| "omega_CAction lst (CSPRepInterlNS [Choose (x, Nil) (ZSetDisplay lsx)] 
        (NSExprParam ns [ZVar (x1, Nil)]) (CSPParAction a [ZVar (x2, Nil)])) 
    = (case (eq x x1) & (eq x x2) of
          True \<Rightarrow> rep_CSPRepInterlNS lst a ns x lsx
          | _ \<Rightarrow> (CSPRepInterlNS [Choose (x, Nil) (ZSetDisplay lsx)] (NSExprParam  ns [ZVar (x1, Nil)]) 
                                (omega_CAction lst (CSPParAction a [ZVar (x2, Nil)]))))"
| "omega_CAction lst (CSPRepInterlNS [Choose (x, Nil) (ZSetDisplay lsx)] (NSExprParam ns [ZVar (x1, Nil)]) act) 
    = (CSPRepInterlNS [Choose (x, Nil) (ZSetDisplay lsx)] (NSExprParam ns [ZVar (x1, Nil)]) (omega_CAction lst act))"
| "omega_CAction lst (CActionCommand (CIf (CircGAction g a))) 
    = (let lsx = free_var_ZPred g
          in make_get_com lst lsx (rename_vars_CAction (map fst lsx) (CActionCommand (CIf (CircGAction g (omega_prime_CAction lst a))))))"
| "omega_CAction lst (CSPCommAction (ChanComm c ((ChanDotExp e) # xs)) a) 
    = (let lxs = intersect (get_chan_param ((ChanDotExp e) # xs)) (filter_state_comp lst)
          in make_get_com lst lxs (rename_vars_CAction (map fst lxs) (CSPCommAction (ChanComm c ((ChanDotExp e) # xs)) (omega_prime_CAction lst a))))"
| "omega_CAction lst (CActionCommand (CAssign varls valls)) 
    = make_get_com lst varls (rename_vars_CAction (map fst (filter_state_comp lst)) (make_set_com lst varls valls CSPSkip))"
| "omega_CAction lst (CActionCommand (CIf (CircThenElse gl glx))) 
    = (let guard_pair = get_guard_pair (CircThenElse gl glx);
           lsx = nub $ (concat $ map free_var_ZPred (map fst guard_pair))
       in make_get_com lst lsx (rename_vars_CAction (map fst lsx) (CActionCommand (CIf (mk_guard_pair lst guard_pair)))))"
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
| "omega_prime_CAction lst (CSPRepIntChoice [Choose (x, Nil) v] act) = (CSPRepIntChoice [Choose (x, Nil) v] (omega_prime_CAction lst act))"
| "omega_prime_CAction lst (CSPRepSeq [Choose (x, Nil) v] act) = (CSPRepSeq [Choose (x, Nil) v] (omega_prime_CAction lst act))"
| "omega_prime_CAction lst (CSPSeq ca cb) = (CSPSeq (omega_prime_CAction lst ca) (omega_prime_CAction lst cb))"
| "omega_prime_CAction lst (CActionCommand (CIf (CircThenElse gl glx))) = (let guard_pair = get_guard_pair (CircThenElse gl glx)
                                                                           in (CActionCommand (CIf (mk_guard_pair lst guard_pair))))"
| "omega_prime_CAction lst (CSPRepInterlNS [Choose (x, Nil) (ZSetDisplay lsx)] (NSExprParam ns [ZVar (x1, Nil)]) (CSPParAction a [ZVar (x2, Nil)])) 
      = (case (eq x x1) & (eq x x2) of
          True \<Rightarrow> rep_CSPRepInterlNS lst a ns x lsx
        | _ \<Rightarrow> (CSPRepInterlNS [Choose (x, Nil) (ZSetDisplay lsx)] (NSExprParam ns [ZVar (x1, Nil)]) 
                            (omega_prime_CAction lst (CSPParAction a [ZVar (x2, Nil)]))))"
| "omega_prime_CAction lst (CSPRepInterlNS [Choose (x, Nil) (ZSetDisplay lsx)] (NSExprParam ns [ZVar (x1, Nil)]) act) 
      = (CSPRepInterlNS [Choose (x, Nil) (ZSetDisplay lsx)] (NSExprParam ns [ZVar (x1, Nil)]) (omega_prime_CAction lst act))"
| "omega_prime_CAction lst (CSPRepParalNS (CSExpr cs) [Choose (x, Nil) (ZSetDisplay lsx)] 
        (NSExprParam ns [ZVar (x1, Nil)]) (CSPParAction a [ZVar (x2, Nil)])) 
      = (case (eq x x1) & (eq x x2) of
          True \<Rightarrow> rep_CSPRepParalNS lst a cs ns x lsx 
          | _ \<Rightarrow> (CSPRepParalNS (CSExpr cs) [Choose (x, Nil) (ZSetDisplay lsx)] 
                              (NSExprParam ns [ZVar (x1, Nil)]) (omega_prime_CAction lst (CSPParAction a [ZVar (x2, Nil)]))))"
| "omega_prime_CAction lst (CSPRepParalNS (CSExpr cs) [Choose (x, Nil) (ZSetDisplay lsx)] (NSExprParam ns [ZVar (x1, Nil)]) act) 
      = (CSPRepParalNS (CSExpr cs) [Choose (x, Nil) (ZSetDisplay lsx)] (NSExprParam ns [ZVar (x1, Nil)]) (omega_prime_CAction lst act))"
| "omega_prime_CAction lst (CSPRepSeq [Choose (x, Nil) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1, Nil)])) 
      = (case eq x x1 of
            True \<Rightarrow> omega_prime_CAction lst (rep_CSPRepSeq lst act xs)
          | _ \<Rightarrow> (CSPRepSeq [Choose (x, Nil) (ZSeqDisplay xs)] (omega_prime_CAction lst (CSPParAction act [ZVar (x1, Nil)]))))"
| "omega_prime_CAction lst (CSPRepExtChoice [Choose (x, Nil) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1, Nil)])) 
      = (case eq x x1 of
            True \<Rightarrow> rep_CSPRepExtChoice lst act xs
          | _ \<Rightarrow> (CSPRepExtChoice [Choose (x, Nil) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1, Nil)])))"
| "omega_prime_CAction lst (CSPRepIntChoice [Choose (x, Nil) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1, Nil)])) 
      = (case eq x x1 of
            True \<Rightarrow> rep_CSPRepIntChoice lst act xs
          | _ \<Rightarrow> (CSPRepIntChoice [Choose (x, Nil) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1, Nil)])))"
| "rep_CSPRepSeq lst a [x] = omega_CAction lst (CSPParAction a [x])"
| "rep_CSPRepSeq lst a (x # xs) = CSPSeq (omega_CAction lst (CSPParAction a [x])) (rep_CSPRepSeq lst a xs)"
| "rep_CSPRepIntChoice lst a [x] = omega_CAction lst (CSPParAction a [x])"
| "rep_CSPRepIntChoice lst a (x # xs) = CSPIntChoice (omega_CAction lst (CSPParAction a [x])) (rep_CSPRepIntChoice lst a xs)"
| "rep_CSPRepExtChoice lst a [x] = omega_CAction lst (CSPParAction a [x])"
| "rep_CSPRepExtChoice lst a (x # xs) = CSPExtChoice (omega_CAction lst (CSPParAction a [x])) (rep_CSPRepExtChoice lst a xs)"
| "rep_CSPRepParalNS lst a _ _ _ [x] = omega_CAction lst (CSPParAction a [x])"
| "rep_CSPRepParalNS lst a cs ns y (x # xs) 
      = (CSPNSParal (NSExprParam ns [x]) (CSExpr cs) 
                (NSBigUnion (ZSetComp [Choose (y, Nil) (ZSetDisplay xs)] (Some (ZCall (ZVar (ns, Nil)) (ZVar (y, Nil)))))) 
                (omega_CAction lst (CSPParAction a [x])) (rep_CSPRepParalNS lst a cs ns y xs))"
| "rep_CSPRepInterlNS lst a _ _ [x] = omega_CAction lst (CSPParAction a [x])"
| "rep_CSPRepInterlNS lst a ns y (x # xs) 
      = (CSPNSInter (NSExprParam ns [x]) (NSBigUnion (ZSetComp [Choose (y, Nil) (ZSetDisplay xs)] 
          (Some (ZCall (ZVar (ns, Nil)) (ZVar (y, Nil)))))) (omega_CAction lst (CSPParAction a [x])) (rep_CSPRepInterlNS lst a ns y xs))"
| "mk_guard_pair lst [(g, a)] = (CircGAction g (omega_prime_CAction lst a))"
| "mk_guard_pair lst ((g, a) # ls) = (CircThenElse (CircGAction g (omega_prime_CAction lst a)) (mk_guard_pair lst ls))"
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
| "free_var_CAction (CSPUnParAction lst c nm) = \\ (free_var_CAction c) (fvs free_var_ZGenFilt lst)"
| "free_var_CAction (CSPRepSeq lst c) = \\ (free_var_CAction c) (fvs free_var_ZGenFilt lst)"
| "free_var_CAction (CSPRepExtChoice lst c) = \\ (free_var_CAction c) (fvs free_var_ZGenFilt lst)"
| "free_var_CAction (CSPRepIntChoice lst c) = \\ (free_var_CAction c) (fvs free_var_ZGenFilt lst)"
| "free_var_CAction (CSPRepParalNS cs lst ns c) = \\ (free_var_CAction c) (fvs free_var_ZGenFilt lst)"
| "free_var_CAction (CSPRepParal cs lst c) = \\ (free_var_CAction c) (fvs free_var_ZGenFilt lst)"
| "free_var_CAction (CSPRepInterlNS lst ns c) = \\ (free_var_CAction c) (fvs free_var_ZGenFilt lst)"
| "free_var_CAction (CSPRepInterl lst c) = \\ (free_var_CAction c) (fvs free_var_ZGenFilt lst)"
| "free_var_CAction _ = Nil"
| "free_var_comnd (CAssign v e) = v"
| "free_var_comnd (CIf ga) = free_var_if ga"
| "free_var_comnd (CVarDecl z c) = \\ (free_var_CAction c) (fvs free_var_ZGenFilt z)"
| "free_var_comnd (CommandBrace z) = (free_var_ZPred z)"
| "free_var_comnd (CommandBracket z) = (free_var_ZPred z)"
| "free_var_comnd (CValDecl z c) = \\ (free_var_CAction c) (fvs free_var_ZGenFilt z)"
| "free_var_comnd (CResDecl z c) = \\ (free_var_CAction c) (fvs free_var_ZGenFilt z)"
| "free_var_comnd (CVResDecl z c) = \\ (free_var_CAction c) (fvs free_var_ZGenFilt z)"
| "free_var_comnd _ = Nil"
| "free_var_if (CircGAction p a) = ((free_var_ZPred p) @ (free_var_CAction a))"
| "free_var_if (CircThenElse ga gb) = ((free_var_if ga) @ (free_var_if gb))"
| "free_var_if (CircElse (CircusAction a)) = (free_var_CAction a)"
| "free_var_if (CircElse (ParamActionDecl x (CircusAction a))) = \\ (free_var_CAction a) (fvs free_var_ZGenFilt x)"

 
fun unionBy :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "unionBy eq5 xs ys = (xs @ foldl (flip (deleteBy eq5)) (nubBy eq5 ys) xs)"

 
definition union :: "('a :: eq) list \<Rightarrow> ('a :: eq) list \<Rightarrow> ('a :: eq) list"
where
  "union = unionBy eq"


end
