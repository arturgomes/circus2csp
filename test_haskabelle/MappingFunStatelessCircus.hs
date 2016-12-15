-- %!TEX root = MAIN.tex

-- \section{Mapping Functions - Stateless Circus}

-- File: MappingFunStatelessCircus.lhs
-- \ignore{
-- \begin{code}
module MappingFunStatelessCircus
( 
  omega_CAction,
)
where
import AST
-- import DefSets
-- import Data.List
-- import FormatterToCSP

omega_CAction :: [(ZName, ZVar, ZExpr)] -> CAction -> CAction
omega_CAction lst CSPSkip = CSPSkip
omega_CAction lst CSPStop = CSPStop
omega_CAction lst CSPChaos = CSPChaos
omega_CAction lst (CSPCommAction (ChanComm c []) a)
  = (CSPCommAction (ChanComm c []) (omega_CAction lst a))
omega_CAction lst (CSPCommAction (ChanComm c ((ChanOutExp e):xs)) a)
  = omega_CAction lst (CSPCommAction (ChanComm c ((ChanDotExp e):xs)) a)
omega_CAction lst (CSPSeq ca cb)
  = (CSPSeq (omega_CAction lst ca) (omega_CAction lst cb))
omega_CAction lst (CSPIntChoice ca cb)
  = (CSPIntChoice (omega_CAction lst ca) (omega_CAction lst cb))




omega_CAction lst (CSPCommAction (ChanComm c []) a)
  = (CSPCommAction (ChanComm c []) (omega_CAction lst a))


omega_CAction lst (CSPHide a cs) = (CSPHide (omega_CAction lst a) cs)



omega_CAction lst (CSPRecursion x c) = (CSPRecursion x (omega_CAction lst c))




omega_CAction lst (CActionCommand (CommandBrace g))
  = omega_CAction lst (CActionCommand (CPrefix g (ZTrue {reason = []})))



omega_CAction lst (CActionCommand (CommandBracket g))
  = omega_CAction lst (CActionCommand (CPrefix1 g))



omega_CAction lst (CSPRenAction a (CRenameAssign left right))
  = (CSPRenAction a (CRename right left))
omega_CAction lst x = x
-- Omega Prime

omega_prime_CAction :: [(ZName, ZVar, ZExpr)] -> CAction -> CAction
omega_prime_CAction lst CSPSkip = CSPSkip
omega_prime_CAction lst CSPStop = CSPStop
omega_prime_CAction lst CSPChaos = CSPChaos


omega_prime_CAction lst (CSPCommAction (ChanComm c []) a)
  = (CSPCommAction (ChanComm c []) (omega_prime_CAction lst a))



omega_prime_CAction lst (CSPCommAction (ChanComm c x) a)
  = (CSPCommAction (ChanComm c x) (omega_prime_CAction lst a))



omega_prime_CAction lst (CSPGuard g a)
  = (CSPGuard g (omega_prime_CAction lst a))



omega_prime_CAction lst (CSPSeq ca cb)
  = (CSPSeq (omega_prime_CAction lst ca) (omega_prime_CAction lst cb))



omega_prime_CAction lst (CSPIntChoice ca cb)
  = (CSPIntChoice (omega_prime_CAction lst ca) (omega_prime_CAction lst cb))


omega_prime_CAction lst (CActionCommand (CIf (CircGAction g a)))
  = (CActionCommand (CIf (CircGAction g (omega_prime_CAction lst a))))


omega_prime_CAction lst (CSPHide a cs) = (CSPHide (omega_prime_CAction lst a) cs)



omega_prime_CAction lst (CSPRecursion x c) = (CSPRecursion x (omega_prime_CAction lst c))



omega_prime_CAction lst (CActionCommand (CommandBrace g))
  = omega_prime_CAction lst (CActionCommand (CPrefix g (ZTrue {reason = []})))



omega_prime_CAction lst (CActionCommand (CommandBracket g))
  = omega_prime_CAction lst (CActionCommand (CPrefix1 g))



omega_prime_CAction lst (CSPRenAction a (CRenameAssign left right))
  = (CSPRenAction a (CRename right left))



omega_prime_CAction lst (CActionName n)
  = (CActionName n)



omega_prime_CAction lst x 
  = error ("Not defined for Omega'"++ show x)



-- Extra from MappingFunStatelesssCircus.lhs
get_proc_name :: ZName -> [(ZName, ZVar, ZExpr)] -> ZName
get_proc_name x [(a,(va,x1),b)]
 = case x == va of
  True -> a
  _ -> ""
get_proc_name x ((a,(va,x1),b):vst)
 = case x == va of
  True -> a
  _ -> get_proc_name x vst

make_get_com :: [(ZName, ZVar, ZExpr)] -> [ZVar] -> CAction -> CAction
make_get_com lst [(x,[])] c
  = (CSPCommAction (ChanComm "mget"
    [ChanDotExp (ZVar ((get_proc_name x lst)++"_"++x,[])),ChanInp ("v"++(get_proc_name x lst)++"_"++x)]) c)
make_get_com lst ((x,[]):xs) c
  = (CSPCommAction (ChanComm "mget"
    [ChanDotExp (ZVar ((get_proc_name x lst)++"_"++x,[])),ChanInp ("v"++(get_proc_name x lst)++"_"++x)]) (make_get_com lst xs c))
make_get_com lst x c = c   

-- Extra from DefSets.hs

filter_state_comp :: [(ZName, ZVar, ZExpr)] -> [ZVar]
filter_state_comp [] = []
filter_state_comp [(_, v, _)] = [v]
filter_state_comp ((_, v, _):xs) = [v]++(filter_state_comp xs)

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



-- From Data.list


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