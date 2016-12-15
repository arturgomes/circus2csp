-- \section{Misc functions -- File: DefSets.lhs}
-- Functions used for manipulating lists (Z Sets and sequences, as well as calculating the provisos from the Circus Refinement laws)

-- \ignore{
-- \begin{code}
module DefSets where
-- import Data.List
-- import Data.Text hiding (map,concat,all)
import AST



-- TODO: Need to do it
getWrtV xs = []



getFV xs = []



join_name n v = n ++ "_" ++ v



free_var_ZExpr :: ZExpr -> [ZVar]

free_var_ZExpr(ZVar v)
 = [v]
free_var_ZExpr(ZInt c )
 = []
free_var_ZExpr(ZGiven a)
	= error "Don't know what free vars of ZGiven are right now. Check back later"

free_var_ZExpr(ZFree0 a)
	= error "Don't know what free vars of ZFree0 are right now. Check back later"

free_var_ZExpr(ZFree1 v ex)
	= error "Don't know what free vars of ZFree1 are right now. Check back later"
free_var_ZExpr(ZTuple exls )
 = fvs free_var_ZExpr exls
free_var_ZExpr(ZBinding a)
	= error "Don't know what free vars of ZBinding are right now. Check back later"
free_var_ZExpr(ZSetDisplay exls )
 = fvs free_var_ZExpr exls
free_var_ZExpr(ZSeqDisplay exls )
 = fvs free_var_ZExpr exls
free_var_ZExpr(ZFSet fs )
	= error "Don't know what free vars of ZFSet are right now. Check back later"
free_var_ZExpr(ZIntSet zi1 zi2)
	= error "Don't know what free vars of ZIntSet are right now. Check back later"
free_var_ZExpr(ZGenerator rl ex)
	= error "Don't know what free vars of ZGenerator are right now. Check back later"
free_var_ZExpr(ZCross exls )
 = fvs free_var_ZExpr exls
free_var_ZExpr(ZFreeType zv zbls)
	= error "Don't know what free vars of ZFreeType are right now. Check back later"
free_var_ZExpr(ZPowerSet{baseset=b, is_non_empty=e, is_finite=fs})
	= error "Don't know what free vars of ZPowerSet are right now. Check back later"
free_var_ZExpr(ZFuncSet{domset=d, ranset=r, is_function=f, is_total=t, is_onto=o, is_one2one=oo, is_sequence=s, is_non_empty=ne, is_finite=ff})
	= error "Don't know what free vars of ZFree0 are right now. Check back later"
free_var_ZExpr(ZSetComp gfls ma)
	= error "Don't know what free vars of ZSetComp are right now. Check back later"
free_var_ZExpr(ZLambda [Choose v e] a)
 = (free_var_ZExpr a) \\ [v]
free_var_ZExpr(ZLambda _ a)
 = []
free_var_ZExpr(ZESchema a)
	= error "Don't know what free vars of ZESchema are right now. Check back later"
free_var_ZExpr(ZGivenSet a)
	= error "Don't know what free vars of ZGivenSet are right now. Check back later"
free_var_ZExpr(ZUniverse)
	= error "Don't know what free vars of ZUniverse are right now. Check back later"
free_var_ZExpr(ZCall ex ex2)
 = free_var_ZExpr ex2 -- is this right??
free_var_ZExpr(ZReln rl )
	= error "Don't know what free vars of ZReln are right now. Check back later"
free_var_ZExpr(ZFunc1 a)
	= error "Don't know what free vars of ZFunc1 are right now. Check back later"
free_var_ZExpr(ZFunc2 a)
	= error "Don't know what free vars of ZFunc2 are right now. Check back later"
free_var_ZExpr(ZStrange zs )
	= error "Don't know what free vars of ZStrange are right now. Check back later"
free_var_ZExpr(ZMu zgls mex)
	= error "Don't know what free vars of ZMu are right now. Check back later"
free_var_ZExpr(ZELet ves pr)
	= ((free_var_ZExpr(pr)) \\ (map fst ves)) ++ fvs free_var_ZExpr (map snd ves)
free_var_ZExpr(ZIf_Then_Else zp ex ex1)
	= error "Don't know what free vars of ZIf_Then_Else are right now. Check back later"
-- free_var_ZExpr(ZIf_Then_Else zp ex ex1)
 -- = free_var_ZPred zp ++ free_var_ZExpr ex ++ free_var_ZExpr ex1
free_var_ZExpr(ZSelect ex zv)
	= free_var_ZExpr ex ++ [zv] 
free_var_ZExpr(ZTheta zsx)
	= error "Don't know what free vars of ZTheta are right now. Check back later"

free_var_ZPred :: ZPred -> [ZVar]
free_var_ZPred (ZFalse{reason=p})
	= error "Don't know what free vars of ZFalse are right now. Check back later"
free_var_ZPred (ZTrue{reason=p})
	= error "Don't know what free vars of ZTrue are right now. Check back later"
free_var_ZPred (ZAnd a b)
 = free_var_ZPred a ++ free_var_ZPred b
free_var_ZPred (ZOr a b)
 = free_var_ZPred a ++ free_var_ZPred b
free_var_ZPred (ZImplies a b)
 = free_var_ZPred a ++ free_var_ZPred b
free_var_ZPred (ZIff a b)
 = free_var_ZPred a ++ free_var_ZPred b
free_var_ZPred (ZNot a)
 = free_var_ZPred a
free_var_ZPred (ZExists [Choose v e] a)
 = (free_var_ZPred a) \\ [v]
free_var_ZPred (ZExists ls a)
	= error "Don't know what free vars of ZExists are right now. Check back later"
free_var_ZPred (ZExists_1 [Choose v e] a)
 = (free_var_ZPred a) \\ [v]
free_var_ZPred (ZExists_1 ls a)
	= error "Don't know what free vars of ZExists_1 are right now. Check back later"
free_var_ZPred (ZForall [Choose v e] a)
 = (free_var_ZPred a) \\ [v]
free_var_ZPred (ZForall ls a)
	= error "Don't know what free vars of ZForall are right now. Check back later"
free_var_ZPred (ZPLet ls a )
	 = error "Don't know what free vars of ZPLet are right now. Check back later"
free_var_ZPred (ZEqual expa expb)
 = free_var_ZExpr expa ++ free_var_ZExpr expb
free_var_ZPred (ZMember expa expb)
	= free_var_ZExpr expa
free_var_ZPred (ZPre zsexpr)
	= error "Don't know what free vars of ZPre are right now. Check back later"
free_var_ZPred (ZPSchema zsexpr)
	= error "Don't know what free vars of ZPSchema are right now. Check back later"



fvs f [] = []
fvs f (e:es)
 = f(e) ++ (fvs f (es))



subset xs ys = all (`elem` ys) xs



free_var_CAction :: CAction -> [ZVar]
free_var_CAction (CActionSchemaExpr x)
 = []
free_var_CAction (CActionCommand c)
 = (free_var_comnd c)
free_var_CAction (CActionName nm)
 = []
free_var_CAction (CSPSkip)
 = []
free_var_CAction (CSPStop)
 = []
free_var_CAction (CSPChaos)
 = []
free_var_CAction (CSPCommAction (ChanComm com xs) c)
 = (get_chan_param xs)++(free_var_CAction c)
free_var_CAction (CSPGuard p c)
 = (free_var_ZPred p)++(free_var_CAction c)
free_var_CAction (CSPSeq ca cb)
 = (free_var_CAction ca)++(free_var_CAction cb)
free_var_CAction (CSPExtChoice ca cb)
 = (free_var_CAction ca)++(free_var_CAction cb)
free_var_CAction (CSPIntChoice ca cb)
 = (free_var_CAction ca)++(free_var_CAction cb)
free_var_CAction (CSPNSParal ns1 cs ns2 ca cb)
 = (free_var_CAction ca)++(free_var_CAction cb)
free_var_CAction (CSPParal cs ca cb)
 = (free_var_CAction ca)++(free_var_CAction cb)
free_var_CAction (CSPNSInter ns1 ns2 ca cb)
 = (free_var_CAction ca)++(free_var_CAction cb)
free_var_CAction (CSPInterleave ca cb)
 = (free_var_CAction ca)++(free_var_CAction cb)
free_var_CAction (CSPHide c cs)
 = (free_var_CAction c)
free_var_CAction (CSPParAction nm xp)
 = []
free_var_CAction (CSPRenAction nm cr)
 = []
free_var_CAction (CSPRecursion nm c)
 = (free_var_CAction c)
free_var_CAction (CSPUnParAction lst c nm)
 = (free_var_CAction c) \\ (fvs free_var_ZGenFilt lst)
free_var_CAction (CSPRepSeq lst c)
 = (free_var_CAction c) \\ (fvs free_var_ZGenFilt lst)
free_var_CAction (CSPRepExtChoice lst c)
 = (free_var_CAction c) \\ (fvs free_var_ZGenFilt lst)
free_var_CAction (CSPRepIntChoice lst c)
 = (free_var_CAction c) \\ (fvs free_var_ZGenFilt lst)
free_var_CAction (CSPRepParalNS cs lst ns c)
 = (free_var_CAction c) \\ (fvs free_var_ZGenFilt lst)
free_var_CAction (CSPRepParal cs lst c)
 = (free_var_CAction c) \\ (fvs free_var_ZGenFilt lst)
free_var_CAction (CSPRepInterlNS lst ns c)
 = (free_var_CAction c) \\ (fvs free_var_ZGenFilt lst)
free_var_CAction (CSPRepInterl lst c)
 = (free_var_CAction c) \\ (fvs free_var_ZGenFilt lst)



free_var_comnd (CAssign v e) 
 = v
free_var_comnd (CIf ga) 
 = free_var_if ga
free_var_comnd (CVarDecl z c) 
 = (free_var_CAction c) \\ (fvs free_var_ZGenFilt z)
free_var_comnd (CAssumpt n p1 p2) 
 = []
free_var_comnd (CAssumpt1 n p) 
 = []
free_var_comnd (CPrefix p1 p2) 
 = []
free_var_comnd (CPrefix1 p) 
 = []
free_var_comnd (CommandBrace z) 
 = (free_var_ZPred z)
free_var_comnd (CommandBracket z) 
 = (free_var_ZPred z)
free_var_comnd (CValDecl z c) 
 = (free_var_CAction c) \\ (fvs free_var_ZGenFilt z)
free_var_comnd (CResDecl z c) 
 = (free_var_CAction c) \\ (fvs free_var_ZGenFilt z)
free_var_comnd (CVResDecl z c) 
 = (free_var_CAction c) \\ (fvs free_var_ZGenFilt z)



free_var_ZGenFilt (Include s) = []
free_var_ZGenFilt (Choose v e) = [v]
free_var_ZGenFilt (Check p) = []
free_var_ZGenFilt (Evaluate v e1 e2) = []



free_var_if (CircGAction p a)
 = (free_var_ZPred p)++(free_var_CAction a)
free_var_if (CircThenElse ga gb)
 = (free_var_if ga)++(free_var_if gb)
free_var_if (CircElse (CircusAction a))
 = (free_var_CAction a)
free_var_if (CircElse (ParamActionDecl x (CircusAction a)))
 = (free_var_CAction a) \\ (fvs free_var_ZGenFilt x)


   
get_main_action :: [PPar] -> CAction -> CAction
get_main_action lst (CActionSchemaExpr x)
 = (CActionSchemaExpr x)
get_main_action lst (CActionCommand c)
 = (CActionCommand (get_main_action_comnd lst c))
get_main_action lst (CActionName nm)
 = get_action nm lst
get_main_action lst (CSPSkip)
 = (CSPSkip)
get_main_action lst (CSPStop)
 = (CSPStop)
get_main_action lst (CSPChaos)
 = (CSPChaos)
get_main_action lst (CSPCommAction com c)
 = (CSPCommAction com (get_main_action lst c))
get_main_action lst (CSPGuard p c)
 = (CSPGuard p (get_main_action lst c))
get_main_action lst (CSPSeq ca cb)
 = (CSPSeq (get_main_action lst ca) (get_main_action lst cb))
get_main_action lst (CSPExtChoice ca cb)
 = (CSPExtChoice (get_main_action lst ca) (get_main_action lst cb))
get_main_action lst (CSPIntChoice ca cb)
 = (CSPIntChoice (get_main_action lst ca) (get_main_action lst cb))
get_main_action lst (CSPNSParal ns1 cs ns2 ca cb)
 = (CSPNSParal ns1 cs ns2 (get_main_action lst ca) (get_main_action lst cb))
get_main_action lst (CSPParal cs ca cb)
 = (CSPParal cs (get_main_action lst ca) (get_main_action lst cb))
get_main_action lst (CSPNSInter ns1 ns2 ca cb)
 = (CSPNSInter ns1 ns2 (get_main_action lst ca) (get_main_action lst cb))
get_main_action lst (CSPInterleave ca cb)
 = (CSPInterleave (get_main_action lst ca) (get_main_action lst cb))
get_main_action lst (CSPHide c cs)
 = (CSPHide (get_main_action lst c) cs)
get_main_action lst (CSPParAction nm xp)
 = (CSPParAction nm xp)
get_main_action lst (CSPRenAction nm cr)
 = (CSPRenAction nm cr)
get_main_action lst (CSPRecursion n (CSPSeq c (CActionName n1)))
 = case n == n1 of
   True -> (CSPRecursion n (CSPSeq (get_main_action lst c) (CActionName n)))
   False -> (CSPRecursion n (CSPSeq (get_main_action lst c) (CActionName n1)))
get_main_action lst (CSPUnParAction lsta c nm)
 = (CSPUnParAction lsta (get_main_action lst c) nm)
get_main_action lst (CSPRepSeq lsta c)
 = (CSPRepSeq lsta (get_main_action lst c))
get_main_action lst (CSPRepExtChoice lsta c)
 = (CSPRepExtChoice lsta (get_main_action lst c))
get_main_action lst (CSPRepIntChoice lsta c)
 = (CSPRepIntChoice lsta (get_main_action lst c))
get_main_action lst (CSPRepParalNS cs lsta ns c)
 = (CSPRepParalNS cs lsta ns (get_main_action lst c))
get_main_action lst (CSPRepParal cs lsta c)
 = (CSPRepParal cs lsta (get_main_action lst c))
get_main_action lst (CSPRepInterlNS lsta ns c)
 = (CSPRepInterlNS lsta ns (get_main_action lst c))
get_main_action lst (CSPRepInterl lsta c)
 = (CSPRepInterl lsta (get_main_action lst c))



get_main_action_comnd lst (CAssign v e) 
 = (CAssign v e)
get_main_action_comnd lst (CIf ga) 
 = (CIf (get_if lst ga))
get_main_action_comnd lst (CVarDecl z a) 
 = (CVarDecl z (get_main_action lst a))
get_main_action_comnd lst (CAssumpt n p1 p2) 
 = (CAssumpt n p1 p2)
get_main_action_comnd lst (CAssumpt1 n p) 
 = (CAssumpt1 n p)
get_main_action_comnd lst (CPrefix p1 p2) 
 = (CPrefix p1 p2)
get_main_action_comnd lst (CPrefix1 p) 
 = (CPrefix1 p)
get_main_action_comnd lst (CommandBrace p) 
 = (CommandBrace p)
get_main_action_comnd lst (CommandBracket p) 
 = (CommandBracket p)
get_main_action_comnd lst (CValDecl z a) 
 = (CValDecl z (get_main_action lst a))
get_main_action_comnd lst (CResDecl z a) 
 = (CResDecl z (get_main_action lst a))
get_main_action_comnd lst (CVResDecl z a) 
 = (CVResDecl z (get_main_action lst a))



get_if lst (CircGAction p a)
 = (CircGAction p (get_main_action lst a))
get_if lst (CircThenElse ga gb)
 = (CircThenElse (get_if lst ga) (get_if lst gb))
get_if lst (CircElse (CircusAction a))
 = (CircElse (CircusAction (get_main_action lst a)))
get_if lst (CircElse (ParamActionDecl x (CircusAction a)))
 = (CircElse (ParamActionDecl x (CircusAction (get_main_action lst a))))



get_action _ [] = error "Action list is empty" 
get_action name [(CParAction n (CircusAction a))] 
 = case name == n of
   True -> a
   False -> error "Action not found"

get_action name ((CParAction n (CircusAction a)):xs)
 = case name == n of
   True -> a
   False -> get_action name xs



get_chan_param :: [CParameter] -> [ZVar]
get_chan_param [] = [] 
get_chan_param [ChanDotExp (ZVar (x,_))] 
 = [(x,[])]
get_chan_param [ChanOutExp (ZVar (x,_))] 
 = [(x,[])]
get_chan_param [_] 
 = []
get_chan_param ((ChanDotExp (ZVar (x,_))):xs) 
 = [(x,[])]++(get_chan_param xs)
get_chan_param ((ChanOutExp (ZVar (x,_))):xs) 
 = [(x,[])]++(get_chan_param xs)
get_chan_param (_:xs) = (get_chan_param xs)



filter_state_comp :: [(ZName, ZVar, ZExpr)] -> [ZVar]
filter_state_comp [] = []
filter_state_comp [(_, v, _)] = [v]
filter_state_comp ((_, v, _):xs) = [v]++(filter_state_comp xs)



inListVar x []
 = False
inListVar x [va]
 = case x == va of
  True -> True
  _ -> False
inListVar x (va:vst)
 = case x == va of
  True -> True
  _ -> inListVar x vst




bindingsVar lst []
 = []
bindingsVar lst [((va,x),b)]
 = case (inListVar va lst) of
   True -> [(("v_"++va,x),(rename_ZExpr lst b))]
   False -> [((va,x),(rename_ZExpr lst b))]
bindingsVar lst (((va,x),b):xs) 
 = case (inListVar va lst) of
   True -> [(("v_"++va,x),(rename_ZExpr lst b))]++(bindingsVar lst xs)
   False -> [((va,x),(rename_ZExpr lst b))]++(bindingsVar lst xs)




rename_ZVar lst (va,x)
  = case (inListVar va lst) of
     True -> ("v_"++va,x)
     False -> (va,x)
rename_ZExpr lst (ZVar (va,x))
 = case (inListVar va lst) of
   True -> (ZVar ("v_"++va,x))
   False -> (ZVar (va,x))
rename_ZExpr lst (ZInt zi)
 = (ZInt zi)
rename_ZExpr lst (ZGiven gv)
 = (ZGiven gv)
rename_ZExpr lst (ZFree0 va)
 = (ZFree0 va)
rename_ZExpr lst (ZFree1 va xpr)
 = (ZFree1 va (rename_ZExpr lst xpr))
rename_ZExpr lst (ZTuple xprlst)
 = (ZTuple (map (rename_ZExpr lst) xprlst))
rename_ZExpr lst (ZBinding xs)
 = (ZBinding (bindingsVar lst xs))
rename_ZExpr lst (ZSetDisplay xprlst)
 = (ZSetDisplay (map (rename_ZExpr lst) xprlst))
rename_ZExpr lst (ZSeqDisplay xprlst)
 = (ZSeqDisplay (map (rename_ZExpr lst) xprlst))
rename_ZExpr lst (ZFSet zf)
 = (ZFSet zf)
rename_ZExpr lst (ZIntSet i1 i2)
 = (ZIntSet i1 i2)
rename_ZExpr lst (ZGenerator zrl xpr)
 = (ZGenerator zrl (rename_ZExpr lst xpr))
rename_ZExpr lst (ZCross xprlst)
 = (ZCross (map (rename_ZExpr lst) xprlst))
rename_ZExpr lst (ZFreeType va lst1)
 = (ZFreeType va lst1)
rename_ZExpr lst (ZPowerSet{baseset=xpr, is_non_empty=b1, is_finite=b2})
 = (ZPowerSet{baseset=(rename_ZExpr lst xpr), is_non_empty=b1, is_finite=b2})
rename_ZExpr lst (ZFuncSet{ domset=expr1, ranset=expr2, is_function=b1, is_total=b2, is_onto=b3, is_one2one=b4, is_sequence=b5, is_non_empty=b6, is_finite=b7})
 = (ZFuncSet{ domset=(rename_ZExpr lst expr1), ranset=(rename_ZExpr lst expr2), is_function=b1, is_total=b2, is_onto=b3, is_one2one=b4, is_sequence=b5, is_non_empty=b6, is_finite=b7})
rename_ZExpr lst (ZSetComp lst1 (Just xpr)) 
 = (ZSetComp lst1 (Just (rename_ZExpr lst xpr)))
rename_ZExpr lst (ZSetComp lst1 Nothing) 
 = (ZSetComp lst1 Nothing)
rename_ZExpr lst (ZLambda lst1 xpr)
 = (ZLambda lst1 (rename_ZExpr lst xpr))
rename_ZExpr lst (ZESchema zxp)
 = (ZESchema zxp)
rename_ZExpr lst (ZGivenSet gs)
 = (ZGivenSet gs)
rename_ZExpr lst (ZUniverse)
 = (ZUniverse)
rename_ZExpr lst (ZCall xpr1 xpr2)
 = (ZCall (rename_ZExpr lst xpr1) (rename_ZExpr lst xpr2))
rename_ZExpr lst (ZReln rl)
 = (ZReln rl)
rename_ZExpr lst (ZFunc1 f1)
 = (ZFunc1 f1)
rename_ZExpr lst (ZFunc2 f2)
 = (ZFunc2 f2)
rename_ZExpr lst (ZStrange st)
 = (ZStrange st)
rename_ZExpr lst (ZMu lst1 (Just xpr))
 = (ZMu lst1 (Just (rename_ZExpr lst xpr)))
rename_ZExpr lst (ZELet lst1 xpr1)
 = (ZELet (bindingsVar lst lst1) (rename_ZExpr lst xpr1))
rename_ZExpr lst (ZIf_Then_Else zp xpr1 xpr2)
 = (ZIf_Then_Else zp (rename_ZExpr lst xpr1) (rename_ZExpr lst xpr2))
rename_ZExpr lst (ZSelect xpr va)
 = (ZSelect xpr va)
rename_ZExpr lst (ZTheta zs)
 = (ZTheta zs)



rename_ZPred lst (ZFalse{reason=a})
 = (ZFalse{reason=a})
rename_ZPred lst (ZTrue{reason=a})
 = (ZTrue{reason=a})
rename_ZPred lst (ZAnd p1 p2)
 = (ZAnd (rename_ZPred lst p1) (rename_ZPred lst p2))
rename_ZPred lst (ZOr p1 p2)
 = (ZOr (rename_ZPred lst p1) (rename_ZPred lst p2))
rename_ZPred lst (ZImplies p1 p2)
 = (ZImplies (rename_ZPred lst p1) (rename_ZPred lst p2))
rename_ZPred lst (ZIff p1 p2)
 = (ZIff (rename_ZPred lst p1) (rename_ZPred lst p2))
rename_ZPred lst (ZNot p)
 = (ZNot (rename_ZPred lst p))
rename_ZPred lst (ZExists lst1 p)
 = (ZExists lst1 (rename_ZPred lst p))
rename_ZPred lst (ZExists_1 lst1 p)
 = (ZExists_1 lst1 (rename_ZPred lst p))
rename_ZPred lst (ZForall lst1 p)
 = (ZForall lst1 (rename_ZPred lst p))
rename_ZPred lst (ZPLet varxp p)
 = (ZPLet varxp (rename_ZPred lst p))
rename_ZPred lst (ZEqual xpr1 xpr2)
 = (ZEqual (rename_ZExpr lst xpr1) (rename_ZExpr lst xpr2))
rename_ZPred lst (ZMember xpr1 xpr2)
 = (ZMember (rename_ZExpr lst xpr1) (rename_ZExpr lst xpr2))
rename_ZPred lst (ZPre sp)
 = (ZPre sp)
rename_ZPred lst (ZPSchema sp)
 = (ZPSchema sp)



middle (a,b,c) = b



rename_vars_ParAction lst (CircusAction ca) 
  = (CircusAction (rename_vars_CAction lst ca))
rename_vars_ParAction lst (ParamActionDecl zglst pa)
  = (ParamActionDecl zglst (rename_vars_ParAction lst pa))



rename_vars_CAction lst (CActionSchemaExpr zsexp)
 = (CActionSchemaExpr zsexp)
rename_vars_CAction lst (CActionCommand cmd)
 = (CActionCommand (rename_vars_CCommand lst cmd))
rename_vars_CAction lst (CActionName zn)
 = (CActionName zn)
rename_vars_CAction lst (CSPSkip )
 = (CSPSkip )
rename_vars_CAction lst (CSPStop )
 = (CSPStop )
rename_vars_CAction lst (CSPChaos)
 = (CSPChaos)
rename_vars_CAction lst (CSPCommAction c a)
 = (CSPCommAction (rename_vars_Comm lst c) (rename_vars_CAction lst a))
rename_vars_CAction lst (CSPGuard zp a)
 = (CSPGuard (rename_ZPred lst zp) (rename_vars_CAction lst a))
rename_vars_CAction lst (CSPSeq a1 a2)
 = (CSPSeq (rename_vars_CAction lst a1) (rename_vars_CAction lst a2))
rename_vars_CAction lst (CSPExtChoice a1 a2)
 = (CSPExtChoice (rename_vars_CAction lst a1) (rename_vars_CAction lst a2))
rename_vars_CAction lst (CSPIntChoice a1 a2)
 = (CSPIntChoice (rename_vars_CAction lst a1) (rename_vars_CAction lst a2))
rename_vars_CAction lst (CSPNSParal ns1 cs ns2 a1 a2)
 = (CSPNSParal ns1 cs ns2 (rename_vars_CAction lst a1) (rename_vars_CAction lst a2))
rename_vars_CAction lst (CSPParal cs a1 a2)
 = (CSPParal cs (rename_vars_CAction lst a1) (rename_vars_CAction lst a2))
rename_vars_CAction lst (CSPNSInter ns1 ns2 a1 a2)
 = (CSPNSInter ns1 ns2 (rename_vars_CAction lst a1) (rename_vars_CAction lst a2))
rename_vars_CAction lst (CSPInterleave a1 a2)
 = (CSPInterleave (rename_vars_CAction lst a1) (rename_vars_CAction lst a2))
rename_vars_CAction lst (CSPHide a cs)
 = (CSPHide (rename_vars_CAction lst a) cs)
rename_vars_CAction lst (CSPParAction zn zexprls)
 = (CSPParAction zn (map (rename_ZExpr lst) zexprls))
rename_vars_CAction lst (CSPRenAction zn crpl)
 = (CSPRenAction zn (rename_vars_CReplace lst crpl))
rename_vars_CAction lst (CSPRecursion zn a)
 = (CSPRecursion zn (rename_vars_CAction lst a))
rename_vars_CAction lst (CSPUnParAction zgf a zn)
 = (CSPUnParAction zgf (rename_vars_CAction lst a) zn)
rename_vars_CAction lst (CSPRepSeq zgf a)
 = (CSPRepSeq zgf (rename_vars_CAction lst a))
rename_vars_CAction lst (CSPRepExtChoice zgf a)
 = (CSPRepExtChoice zgf (rename_vars_CAction lst a))
rename_vars_CAction lst (CSPRepIntChoice zgf a)
 = (CSPRepIntChoice zgf (rename_vars_CAction lst a))
rename_vars_CAction lst (CSPRepParalNS cs zgf ns a)
 = (CSPRepParalNS cs zgf ns (rename_vars_CAction lst a))
rename_vars_CAction lst (CSPRepParal cs zgf a)
 = (CSPRepParal cs zgf (rename_vars_CAction lst a))
rename_vars_CAction lst (CSPRepInterlNS zgf ns a)
 = (CSPRepInterlNS zgf ns (rename_vars_CAction lst a))
rename_vars_CAction lst (CSPRepInterl zgf a)
 = (CSPRepInterl zgf (rename_vars_CAction lst a))



rename_vars_Comm lst (ChanComm zn cpls)
 = (ChanComm zn (map (rename_vars_CParameter lst) cpls))
rename_vars_Comm lst (ChanGenComm zn zexprls cpls)
 = (ChanGenComm zn (map (rename_ZExpr lst) zexprls) (map (rename_vars_CParameter lst) cpls))



rename_vars_CParameter lst (ChanInp zn)
 = (ChanInp zn)
rename_vars_CParameter lst (ChanInpPred zn zp)
 = (ChanInpPred zn (rename_ZPred lst zp))
rename_vars_CParameter lst (ChanOutExp ze)
 = (ChanOutExp (rename_ZExpr lst ze))
rename_vars_CParameter lst (ChanDotExp ze)
 = (ChanDotExp (rename_ZExpr lst ze))



rename_vars_CCommand lst (CAssign zvarls1 zexprls)
 = (CAssign zvarls1 (map (rename_ZExpr lst) zexprls))
rename_vars_CCommand lst (CIf ga)
 = (CIf (rename_vars_CGActions lst ga))
rename_vars_CCommand lst (CVarDecl zgf a)
 = (CVarDecl zgf (rename_vars_CAction lst a))
rename_vars_CCommand lst (CAssumpt znls zp1 zp2)
 = (CAssumpt znls (rename_ZPred lst zp1) zp2)
rename_vars_CCommand lst (CAssumpt1 znls zp)
 = (CAssumpt1 znls zp)
rename_vars_CCommand lst (CPrefix zp1 zp2)
 = (CPrefix (rename_ZPred lst zp1) zp2)
rename_vars_CCommand lst (CPrefix1 zp)
 = (CPrefix1 zp)
rename_vars_CCommand lst (CommandBrace zp)
 = (CommandBrace zp)
rename_vars_CCommand lst (CommandBracket zp)
 = (CommandBracket zp)
rename_vars_CCommand lst (CValDecl zgf a)
 = (CValDecl zgf (rename_vars_CAction lst a))
rename_vars_CCommand lst (CResDecl zgf a)
 = (CResDecl zgf (rename_vars_CAction lst a))
rename_vars_CCommand lst (CVResDecl zgf a)
 = (CVResDecl zgf (rename_vars_CAction lst a))



rename_vars_CGActions lst (CircGAction zp a)
 = (CircGAction (rename_ZPred lst zp) (rename_vars_CAction lst a))
rename_vars_CGActions lst (CircThenElse cga1 cga2)
 = (CircThenElse (rename_vars_CGActions lst cga1) (rename_vars_CGActions lst cga2))
rename_vars_CGActions lst (CircElse pa)
 = (CircElse pa)



rename_vars_CReplace lst (CRename zvarls1 zvarls)
 = (CRename zvarls1 zvarls)
rename_vars_CReplace lst (CRenameAssign zvarls1 zvarls)
 = (CRenameAssign zvarls1 zvarls)



rename_vars_ZPara1 :: [(ZName, ZVar, ZExpr)] -> ZPara -> ZPara
rename_vars_ZPara1 lst (Process zp)
  = (Process (rename_vars_ProcDecl1 lst zp))
rename_vars_ZPara1 lst x 
  = x 



rename_vars_ProcDecl1 :: [(ZName, ZVar, ZExpr)] -> ProcDecl -> ProcDecl
rename_vars_ProcDecl1 lst (CProcess zn pd)
  = (CProcess zn (rename_vars_ProcessDef1 lst pd))
rename_vars_ProcDecl1 lst (CParamProcess zn znls pd)
  = (CParamProcess zn znls (rename_vars_ProcessDef1 lst pd))
rename_vars_ProcDecl1 lst (CGenProcess zn znls pd)
  = (CParamProcess zn znls (rename_vars_ProcessDef1 lst pd))



rename_vars_ProcessDef1 :: [(ZName, ZVar, ZExpr)] -> ProcessDef -> ProcessDef
rename_vars_ProcessDef1 lst (ProcDefSpot zgf pd)
  = (ProcDefSpot zgf (rename_vars_ProcessDef1 lst pd))
rename_vars_ProcessDef1 lst (ProcDefIndex zgf pd)
  = (ProcDefIndex zgf (rename_vars_ProcessDef1 lst pd))
rename_vars_ProcessDef1 lst (ProcDef cp)
  = (ProcDef (rename_vars_CProc1 lst cp))



rename_vars_CProc1 :: [(ZName, ZVar, ZExpr)] -> CProc -> CProc
rename_vars_CProc1 lst (CRepSeqProc zgf cp)
  = (CRepSeqProc zgf (rename_vars_CProc1 lst cp))
rename_vars_CProc1 lst (CRepExtChProc zgf cp)
  = (CRepExtChProc zgf (rename_vars_CProc1 lst cp))
rename_vars_CProc1 lst (CRepIntChProc zgf cp)
  = (CRepIntChProc zgf (rename_vars_CProc1 lst cp))
rename_vars_CProc1 lst (CRepParalProc cs zgf cp)
  = (CRepParalProc cs zgf (rename_vars_CProc1 lst cp))
rename_vars_CProc1 lst (CRepInterlProc zgf cp)
  = (CRepInterlProc zgf (rename_vars_CProc1 lst cp))
rename_vars_CProc1 lst (CHide cp cxp)
  = (CHide (rename_vars_CProc1 lst cp) cxp)
rename_vars_CProc1 lst (CExtChoice cp1 cp2)
  = (CExtChoice (rename_vars_CProc1 lst cp1) (rename_vars_CProc1 lst cp2))
rename_vars_CProc1 lst (CIntChoice cp1 cp2)
  = (CIntChoice (rename_vars_CProc1 lst cp1) (rename_vars_CProc1 lst cp2))
rename_vars_CProc1 lst (CParParal cs cp1 cp2)
  = (CParParal cs (rename_vars_CProc1 lst cp1) (rename_vars_CProc1 lst cp2))
rename_vars_CProc1 lst (CInterleave cp1 cp2)
  = (CInterleave (rename_vars_CProc1 lst cp1) (rename_vars_CProc1 lst cp2))
rename_vars_CProc1 lst (CGenProc zn zxp)
  = (CGenProc zn zxp)
rename_vars_CProc1 lst (CParamProc zn zxp)
  = (CParamProc zn zxp)
rename_vars_CProc1 lst (CProcRename zn c1 c2)
  = (CProcRename zn c1 c2)
rename_vars_CProc1 lst (CSeq cp1 cp2)
  = (CSeq (rename_vars_CProc1 lst cp1) (rename_vars_CProc1 lst cp2))
rename_vars_CProc1 lst (CSimpIndexProc zn zxp)
  = (CSimpIndexProc zn zxp)
rename_vars_CProc1 lst (CircusProc zn)
  = (CircusProc zn)
rename_vars_CProc1 lst (ProcMain zp ppl ca)
  = (ProcMain zp (map (rename_vars_PPar1 lst) ppl) (rename_vars_CAction1 lst ca))
rename_vars_CProc1 lst (ProcStalessMain ppl ca)
  = (ProcStalessMain ppl (rename_vars_CAction1 lst ca))



rename_vars_PPar1 :: [(ZName, ZVar, ZExpr)] -> PPar -> PPar
rename_vars_PPar1 lst (ProcZPara zp) 
  = (ProcZPara zp)
rename_vars_PPar1 lst (CParAction zn pa) 
  = (CParAction zn (rename_vars_ParAction1 lst pa))
rename_vars_PPar1 lst (CNameSet zn ns) 
  = (CNameSet zn ns)



rename_vars_ParAction1 :: [(ZName, ZVar, ZExpr)] -> ParAction -> ParAction
rename_vars_ParAction1 lst (CircusAction ca) 
  = (CircusAction (rename_vars_CAction1 lst ca))
rename_vars_ParAction1 lst (ParamActionDecl zgf pa) 
  = (ParamActionDecl zgf (rename_vars_ParAction1 lst pa))



rename_vars_CAction1 :: [(ZName, ZVar, ZExpr)] -> CAction -> CAction
rename_vars_CAction1 lst (CActionSchemaExpr zsexp)
 = (CActionSchemaExpr zsexp)
rename_vars_CAction1 lst (CActionCommand cmd)
 = (CActionCommand (rename_vars_CCommand1 lst cmd))
rename_vars_CAction1 lst (CActionName zn)
 = (CActionName zn)
rename_vars_CAction1 lst (CSPSkip )
 = (CSPSkip )
rename_vars_CAction1 lst (CSPStop )
 = (CSPStop )
rename_vars_CAction1 lst (CSPChaos)
 = (CSPChaos)
rename_vars_CAction1 lst (CSPCommAction c a)
 = (CSPCommAction (rename_vars_Comm1 lst c) (rename_vars_CAction1 lst a))
rename_vars_CAction1 lst (CSPGuard zp a)
 = (CSPGuard (rename_vars_ZPred1 lst zp) (rename_vars_CAction1 lst a))
rename_vars_CAction1 lst (CSPSeq a1 a2)
 = (CSPSeq (rename_vars_CAction1 lst a1) (rename_vars_CAction1 lst a2))
rename_vars_CAction1 lst (CSPExtChoice a1 a2)
 = (CSPExtChoice (rename_vars_CAction1 lst a1) (rename_vars_CAction1 lst a2))
rename_vars_CAction1 lst (CSPIntChoice a1 a2)
 = (CSPIntChoice (rename_vars_CAction1 lst a1) (rename_vars_CAction1 lst a2))
rename_vars_CAction1 lst (CSPNSParal ns1 cs ns2 a1 a2)
 = (CSPNSParal ns1 cs ns2 (rename_vars_CAction1 lst a1) (rename_vars_CAction1 lst a2))
rename_vars_CAction1 lst (CSPParal cs a1 a2)
 = (CSPParal cs (rename_vars_CAction1 lst a1) (rename_vars_CAction1 lst a2))
rename_vars_CAction1 lst (CSPNSInter ns1 ns2 a1 a2)
 = (CSPNSInter ns1 ns2 (rename_vars_CAction1 lst a1) (rename_vars_CAction1 lst a2))
rename_vars_CAction1 lst (CSPInterleave a1 a2)
 = (CSPInterleave (rename_vars_CAction1 lst a1) (rename_vars_CAction1 lst a2))
rename_vars_CAction1 lst (CSPHide a cs)
 = (CSPHide (rename_vars_CAction1 lst a) cs)
rename_vars_CAction1 lst (CSPParAction zn zexprls)
 = (CSPParAction zn (map (rename_vars_ZExpr1 lst) zexprls))
rename_vars_CAction1 lst (CSPRenAction zn crpl)
 = (CSPRenAction zn (rename_vars_CReplace1 lst crpl))
rename_vars_CAction1 lst (CSPRecursion zn a)
 = (CSPRecursion zn (rename_vars_CAction1 lst a))
rename_vars_CAction1 lst (CSPUnParAction zgf a zn)
 = (CSPUnParAction zgf (rename_vars_CAction1 lst a) zn)
rename_vars_CAction1 lst (CSPRepSeq zgf a)
 = (CSPRepSeq zgf (rename_vars_CAction1 lst a))
rename_vars_CAction1 lst (CSPRepExtChoice zgf a)
 = (CSPRepExtChoice zgf (rename_vars_CAction1 lst a))
rename_vars_CAction1 lst (CSPRepIntChoice zgf a)
 = (CSPRepIntChoice zgf (rename_vars_CAction1 lst a))
rename_vars_CAction1 lst (CSPRepParalNS cs zgf ns a)
 = (CSPRepParalNS cs zgf ns (rename_vars_CAction1 lst a))
rename_vars_CAction1 lst (CSPRepParal cs zgf a)
 = (CSPRepParal cs zgf (rename_vars_CAction1 lst a))
rename_vars_CAction1 lst (CSPRepInterlNS zgf ns a)
 = (CSPRepInterlNS zgf ns (rename_vars_CAction1 lst a))
rename_vars_CAction1 lst (CSPRepInterl zgf a)
 = (CSPRepInterl zgf (rename_vars_CAction1 lst a))



rename_vars_Comm1 :: [(ZName, ZVar, ZExpr)] -> Comm -> Comm
rename_vars_Comm1 lst (ChanComm zn cpls)
 = (ChanComm zn (map (rename_vars_CParameter1 lst) cpls))
rename_vars_Comm1 lst (ChanGenComm zn zexprls cpls)
 = (ChanGenComm zn (map (rename_vars_ZExpr1 lst) zexprls) (map (rename_vars_CParameter1 lst) cpls))



rename_vars_CParameter1 :: [(ZName, ZVar, ZExpr)] -> CParameter -> CParameter
rename_vars_CParameter1 lst (ChanInp zn)
 = case (inListVar1 zn lst) of
  True -> (ChanInp (join_name (get_proc_name zn lst) zn))
  _ -> (ChanInp zn)
rename_vars_CParameter1 lst (ChanInpPred zn zp)
 = case (inListVar1 zn lst) of
  True -> (ChanInpPred (join_name (get_proc_name zn lst) zn) (rename_vars_ZPred1 lst zp))
  _ -> (ChanInpPred zn zp)
rename_vars_CParameter1 lst (ChanOutExp ze)
 = (ChanOutExp (rename_vars_ZExpr1 lst ze))
rename_vars_CParameter1 lst (ChanDotExp ze)
 = (ChanDotExp (rename_vars_ZExpr1 lst ze))



rename_vars_CCommand1 :: [(ZName, ZVar, ZExpr)] -> CCommand -> CCommand
rename_vars_CCommand1 lst (CAssign zvarls1 zexprls)
 = (CAssign zvarls1 (map (rename_vars_ZExpr1 lst) zexprls))
rename_vars_CCommand1 lst (CIf ga)
 = (CIf (rename_vars_CGActions1 lst ga))
rename_vars_CCommand1 lst (CVarDecl zgf a)
 = (CVarDecl zgf (rename_vars_CAction1 lst a))
rename_vars_CCommand1 lst (CAssumpt znls zp1 zp2)
 = (CAssumpt znls (rename_vars_ZPred1 lst zp1) zp2)
rename_vars_CCommand1 lst (CAssumpt1 znls zp)
 = (CAssumpt1 znls zp)
rename_vars_CCommand1 lst (CPrefix zp1 zp2)
 = (CPrefix (rename_vars_ZPred1 lst zp1) zp2)
rename_vars_CCommand1 lst (CPrefix1 zp)
 = (CPrefix1 zp)
rename_vars_CCommand1 lst (CommandBrace zp)
 = (CommandBrace zp)
rename_vars_CCommand1 lst (CommandBracket zp)
 = (CommandBracket zp)
rename_vars_CCommand1 lst (CValDecl zgf a)
 = (CValDecl zgf (rename_vars_CAction1 lst a))
rename_vars_CCommand1 lst (CResDecl zgf a)
 = (CResDecl zgf (rename_vars_CAction1 lst a))
rename_vars_CCommand1 lst (CVResDecl zgf a)
 = (CVResDecl zgf (rename_vars_CAction1 lst a))



rename_vars_CGActions1 :: [(ZName, ZVar, ZExpr)] -> CGActions -> CGActions
rename_vars_CGActions1 lst (CircGAction zp a)
 = (CircGAction (rename_vars_ZPred1 lst zp) (rename_vars_CAction1 lst a))
rename_vars_CGActions1 lst (CircThenElse cga1 cga2)
 = (CircThenElse (rename_vars_CGActions1 lst cga1) (rename_vars_CGActions1 lst cga2))
rename_vars_CGActions1 lst (CircElse pa)
 = (CircElse pa)



rename_vars_CReplace1 :: [(ZName, ZVar, ZExpr)] -> CReplace -> CReplace
rename_vars_CReplace1 lst (CRename zvarls1 zvarls)
 = (CRename zvarls1 zvarls)
rename_vars_CReplace1 lst (CRenameAssign zvarls1 zvarls)
 = (CRenameAssign zvarls1 zvarls)



bindingsVar1 lst []
 = []
bindingsVar1 lst [((va,x),b)]
 = [(((join_name (get_proc_name va lst) va),x),(rename_vars_ZExpr1 lst b))]
bindingsVar1 lst (((va,x),b):xs) 
 = [(((join_name (get_proc_name va lst) va),x),(rename_vars_ZExpr1 lst b))]++(bindingsVar1 lst xs)



inListVar1 :: ZName -> [(ZName, ZVar, ZExpr)] -> Bool
inListVar1 x []
 = False
inListVar1 x [(a,(va,x1),b)]
 = case x == va of
  True -> True
  _ -> False
inListVar1 x ((a,(va,x1),b):vst)
 = case x == va of
  True -> True
  _ -> inListVar1 x vst



get_proc_name :: ZName -> [(ZName, ZVar, ZExpr)] -> ZName
get_proc_name x [(a,(va,x1),b)]
 = case x == va of
  True -> a
  _ -> ""
get_proc_name x ((a,(va,x1),b):vst)
 = case x == va of
  True -> a
  _ -> get_proc_name x vst



rename_vars_ZExpr1 :: [(ZName, ZVar, ZExpr)] -> ZExpr -> ZExpr
rename_vars_ZExpr1 lst (ZVar (va,x))
 = case (inListVar1 va lst) of
  True -> (ZVar ((join_name (get_proc_name va lst) va),x))
  _ -> (ZVar (va,x))
rename_vars_ZExpr1 lst (ZInt zi)
 = (ZInt zi)
rename_vars_ZExpr1 lst (ZGiven gv)
 = (ZGiven gv)
rename_vars_ZExpr1 lst (ZFree0 va)
 = (ZFree0 va)
rename_vars_ZExpr1 lst (ZFree1 va xpr)
 = (ZFree1 va (rename_vars_ZExpr1 lst xpr))
rename_vars_ZExpr1 lst (ZTuple xpr)
 = (ZTuple (map (rename_vars_ZExpr1 lst) xpr))
rename_vars_ZExpr1 lst (ZBinding xs)
 = (ZBinding (bindingsVar1 lst xs))
rename_vars_ZExpr1 lst (ZSetDisplay xpr)
 = (ZSetDisplay (map (rename_vars_ZExpr1 lst) xpr))
rename_vars_ZExpr1 lst (ZSeqDisplay xpr)
 = (ZSeqDisplay (map (rename_vars_ZExpr1 lst) xpr))
rename_vars_ZExpr1 lst (ZFSet zf)
 = (ZFSet zf)
rename_vars_ZExpr1 lst (ZIntSet i1 i2)
 = (ZIntSet i1 i2)
rename_vars_ZExpr1 lst (ZGenerator zrl xpr)
 = (ZGenerator zrl (rename_vars_ZExpr1 lst xpr))
rename_vars_ZExpr1 lst (ZCross xpr)
 = (ZCross (map (rename_vars_ZExpr1 lst) xpr))
rename_vars_ZExpr1 lst (ZFreeType va pname1)
 = (ZFreeType va pname1)
rename_vars_ZExpr1 lst (ZPowerSet{baseset=xpr, is_non_empty=b1, is_finite=b2})
 = (ZPowerSet{baseset=(rename_vars_ZExpr1 lst xpr), is_non_empty=b1, is_finite=b2})
rename_vars_ZExpr1 lst (ZFuncSet{ domset=expr1, ranset=expr2, is_function=b1, is_total=b2, is_onto=b3, is_one2one=b4, is_sequence=b5, is_non_empty=b6, is_finite=b7})
 = (ZFuncSet{ domset=(rename_vars_ZExpr1 lst expr1), ranset=(rename_vars_ZExpr1 lst expr2), is_function=b1, is_total=b2, is_onto=b3, is_one2one=b4, is_sequence=b5, is_non_empty=b6, is_finite=b7})
rename_vars_ZExpr1 lst (ZSetComp pname1 (Just xpr)) 
 = (ZSetComp pname1 (Just (rename_vars_ZExpr1 lst xpr)))
rename_vars_ZExpr1 lst (ZSetComp pname1 Nothing) 
 = (ZSetComp pname1 Nothing)
rename_vars_ZExpr1 lst (ZLambda pname1 xpr)
 = (ZLambda pname1 (rename_vars_ZExpr1 lst xpr))
rename_vars_ZExpr1 lst (ZESchema zxp)
 = (ZESchema zxp)
rename_vars_ZExpr1 lst (ZGivenSet gs)
 = (ZGivenSet gs)
rename_vars_ZExpr1 lst (ZUniverse)
 = (ZUniverse)
rename_vars_ZExpr1 lst (ZCall xpr1 xpr2)
 = (ZCall (rename_vars_ZExpr1 lst xpr1) (rename_vars_ZExpr1 lst xpr2))
rename_vars_ZExpr1 lst (ZReln rl)
 = (ZReln rl)
rename_vars_ZExpr1 lst (ZFunc1 f1)
 = (ZFunc1 f1)
rename_vars_ZExpr1 lst (ZFunc2 f2)
 = (ZFunc2 f2)
rename_vars_ZExpr1 lst (ZStrange st)
 = (ZStrange st)
rename_vars_ZExpr1 lst (ZMu pname1 (Just xpr))
 = (ZMu pname1 (Just (rename_vars_ZExpr1 lst xpr)))
rename_vars_ZExpr1 lst (ZELet pname1 xpr1)
 = (ZELet (bindingsVar1 lst pname1) (rename_vars_ZExpr1 lst xpr1))
rename_vars_ZExpr1 lst (ZIf_Then_Else zp xpr1 xpr2)
 = (ZIf_Then_Else zp (rename_vars_ZExpr1 lst xpr1) (rename_vars_ZExpr1 lst xpr2))
rename_vars_ZExpr1 lst (ZSelect xpr va)
 = (ZSelect xpr va)
rename_vars_ZExpr1 lst (ZTheta zs)
 = (ZTheta zs)



rename_vars_ZPred1 :: [(ZName, ZVar, ZExpr)] -> ZPred -> ZPred
rename_vars_ZPred1 lst (ZFalse{reason=a})
 = (ZFalse{reason=a})
rename_vars_ZPred1 lst (ZTrue{reason=a})
 = (ZTrue{reason=a})
rename_vars_ZPred1 lst (ZAnd p1 p2)
 = (ZAnd (rename_vars_ZPred1 lst p1) (rename_vars_ZPred1 lst p2))
rename_vars_ZPred1 lst (ZOr p1 p2)
 = (ZOr (rename_vars_ZPred1 lst p1) (rename_vars_ZPred1 lst p2))
rename_vars_ZPred1 lst (ZImplies p1 p2)
 = (ZImplies (rename_vars_ZPred1 lst p1) (rename_vars_ZPred1 lst p2))
rename_vars_ZPred1 lst (ZIff p1 p2)
 = (ZIff (rename_vars_ZPred1 lst p1) (rename_vars_ZPred1 lst p2))
rename_vars_ZPred1 lst (ZNot p)
 = (ZNot (rename_vars_ZPred1 lst p))
rename_vars_ZPred1 lst (ZExists pname1 p)
 = (ZExists pname1 (rename_vars_ZPred1 lst p))
rename_vars_ZPred1 lst (ZExists_1 lst1 p)
 = (ZExists_1 lst1 (rename_vars_ZPred1 lst p))
rename_vars_ZPred1 lst (ZForall pname1 p)
 = (ZForall pname1 (rename_vars_ZPred1 lst p))
rename_vars_ZPred1 lst (ZPLet varxp p)
 = (ZPLet varxp (rename_vars_ZPred1 lst p))
rename_vars_ZPred1 lst (ZEqual xpr1 xpr2)
 = (ZEqual (rename_vars_ZExpr1 lst xpr1) (rename_vars_ZExpr1 lst xpr2))
rename_vars_ZPred1 lst (ZMember xpr1 xpr2)
 = (ZMember (rename_vars_ZExpr1 lst xpr1) (rename_vars_ZExpr1 lst xpr2))
rename_vars_ZPred1 lst (ZPre sp)
 = (ZPre sp)
rename_vars_ZPred1 lst (ZPSchema sp)
 = (ZPSchema sp)



-- extract the delta variables in here'
get_delta_names [(ZFreeTypeDef ("NAME",[]) xs)]
  = get_delta_names_aux xs
get_delta_names ((ZFreeTypeDef ("NAME",[]) xs):xss) 
  = (get_delta_names_aux xs)++(get_delta_names xss)
get_delta_names (_:xs) 
  = (get_delta_names xs)
get_delta_names [] 
  = []



get_delta_names_aux [(ZBranch0 (a,[]))]
  = [a]
get_delta_names_aux ((ZBranch0 (a,[])):xs)
  = [a]++(get_delta_names_aux xs)



def_U_NAME x = ("U_"++(map toUpper (take 3 x)))
def_U_prefix x = (map toTitle (take 3 x))

mk_universe [] 
  = ""
mk_universe [(a,b,c,d)] 
  = c++"."++d
mk_universe ((a,b,c,d):xs)
  = c++"."++d++" | "++(mk_universe xs)

mk_subtype [] 
  = ""
mk_subtype [(a,b,c,d)] 
  = "subtype "++b++" = "++c++"."++d++"\n"
mk_subtype ((a,b,c,d):xs)
  = "subtype "++b++" = "++c++"."++d++"\n"++(mk_subtype xs)

mk_value [] 
  = ""
mk_value [(a,b,c,d)] 
  = "value("++c++".v) = v\n"
mk_value ((a,b,c,d):xs)
  = "value("++c++".v) = v\n"++(mk_value xs)

mk_type [] 
  = ""
mk_type [(a,b,c,d)] 
  = a++" then "++b
mk_type ((a,b,c,d):xs)
  = a++" then "++b++"\n\t else if x == "++(mk_type xs)

mk_tag [] 
  = ""
mk_tag [(a,b,c,d)] 
  = a++" then "++c
mk_tag ((a,b,c,d):xs)
  = a++" then "++c++"\n\t else if x == "++(mk_tag xs)



-- extract the delta variables and types in here'
def_universe [(ZAbbreviation ("\\delta",[]) (ZSetDisplay xs))]
  = def_universe_aux xs
def_universe ((ZAbbreviation ("\\delta",[]) (ZSetDisplay xs)):xss) 
  = (def_universe_aux xs)++(def_universe xss)
def_universe (_:xs) 
  = (def_universe xs)
def_universe [] 
  = []



def_universe_aux []
  = [] 
def_universe_aux [ZCall (ZVar ("\\mapsto",[])) (ZTuple [ZVar (b,[]),ZVar ("\\nat",[])])] = [(b,"U_NAT", "Nat", "NatValue")]
def_universe_aux [ZCall (ZVar ("\\mapsto",[])) (ZTuple [ZVar (b,[]),ZVar (c,[])])] = [(b,(def_U_NAME c), (def_U_prefix c), c)]
def_universe_aux ((ZCall (ZVar ("\\mapsto",[])) (ZTuple [ZVar (b,[]),ZVar ("\\nat",[])])):xs) = ((b,"U_NAT", "Nat", "NatValue"):(def_universe_aux xs))
def_universe_aux ((ZCall (ZVar ("\\mapsto",[])) (ZTuple [ZVar (b,[]),ZVar (c,[])])):xs) = ((b,(def_U_NAME c), (def_U_prefix c), c):(def_universe_aux xs))



filter_types_universe [(a,b,c,d)] = [(b,b,c,d)]
filter_types_universe ((a,b,c,d):xs) = ((b,b,c,d):(filter_types_universe xs))
-- \end{code}


-- From Data.list

-- | The 'union' function returns the list union of the two lists.
-- For example,
--
-- > "dog" `union` "cow" == "dogcw"
--
-- Duplicates, and elements of the first list, are removed from the
-- the second list, but if the first list contains duplicates, so will
-- the result.
-- It is a special case of 'unionBy', which allows the programmer to supply
-- their own equality test.

union                   :: (Eq a) => [a] -> [a] -> [a]
union                   = unionBy (==)

-- | The 'unionBy' function is the non-overloaded version of 'union'.
unionBy                 :: (a -> a -> Bool) -> [a] -> [a] -> [a]
unionBy eq xs ys        =  xs ++ foldl (flip (deleteBy eq)) (nubBy eq ys) xs

-- | The 'intersect' function takes the list intersection of two lists.
-- For example,
--
-- > [1,2,3,4] `intersect` [2,4,6,8] == [2,4]
--
-- If the first list contains duplicates, so will the result.
--
-- > [1,2,2,3,4] `intersect` [6,4,4,2] == [2,2,4]
--
-- It is a special case of 'intersectBy', which allows the programmer to
-- supply their own equality test.

intersect               :: (Eq a) => [a] -> [a] -> [a]
intersect               =  intersectBy (==)

-- | The 'intersectBy' function is the non-overloaded version of 'intersect'.
intersectBy             :: (a -> a -> Bool) -> [a] -> [a] -> [a]
intersectBy eq xs ys    =  [x | x <- xs, any (eq x) ys]


-- | /O(n^2)/. The 'nub' function removes duplicate elements from a list.
-- In particular, it keeps only the first occurrence of each element.
-- (The name 'nub' means \`essence\'.)
-- It is a special case of 'nubBy', which allows the programmer to supply
-- their own equality test.
nub                     :: (Eq a) => [a] -> [a]
-- stolen from HBC
nub l                   = nub' l []             -- '
  where
    nub' [] _           = []                    -- '
    nub' (x:xs) ls                              -- '
        | x `elem` ls   = nub' xs ls            -- '
        | otherwise     = x : nub' xs (x:ls)    -- '


-- | The 'genericTake' function is an overloaded version of 'take', which
-- accepts any 'Integral' value as the number of elements to take.
take             :: (Integral i) => i -> [a] -> [a]
take n _ | n <= 0 = []
take _ []        =  []
take n (x:xs)    =  x : take (n-1) xs



toLower c = chr (fromIntegral (towlower (fromIntegral (ord c))))
toUpper c = chr (fromIntegral (towupper (fromIntegral (ord c))))
toTitle c = chr (fromIntegral (towtitle (fromIntegral (ord c))))