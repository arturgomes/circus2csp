module OmegaDefs
(
rename_vars_CAction,
free_var_ZGenFilt,fvs,get_chan_param,setminus,intersect,union,member,remdups,
free_var_ZPred,filter_state_comp,get_guard_pair,get_proc_name,
make_get_com,free_var_ZExpr,free_var_ZPred
)
where
import AST
filter_state_comp :: [(ZName, ZVar, ZExpr)] -> [ZVar]
filter_state_comp [] = []
filter_state_comp [(_, v, _)] = [v]
filter_state_comp ((_, v, _):xs) = [v]++(filter_state_comp xs)


get_guard_pair :: CGActions -> [(ZPred, CAction)]
get_guard_pair (CircThenElse (CircGAction g2 a2) (CircGAction g3 a3)) = [(g2,a2),(g3,a3)]
get_guard_pair (CircThenElse (CircGAction g1 a1) glx) = [(g1,a1)]++(get_guard_pair glx)
get_guard_pair _ = []


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
make_get_com lst [(x,[])] c = (CSPCommAction (ChanComm "mget"[ChanDotExp (ZVar ((get_proc_name x lst)++"_"++x,[])),ChanInp ("v"++(get_proc_name x lst)++"_"++x)]) c)
make_get_com lst ((x,[]):xs) c = (CSPCommAction (ChanComm "mget"[ChanDotExp (ZVar ((get_proc_name x lst)++"_"++x,[])),ChanInp ("v"++(get_proc_name x lst)++"_"++x)]) (make_get_com lst xs c))
make_get_com lst x c = c

-- All that should be found in the Defsets.hs file
getWrtV :: t -> [t1]
getWrtV xs = []

free_var_ZGenFilt :: ZGenFilt -> [ZVar]
free_var_ZGenFilt (Choose v e) = [v]
free_var_ZGenFilt _ = []


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


fvs :: (t -> [t1]) -> [t] -> [t1]
fvs f [] = []
fvs f (e:es) = f(e) ++ (fvs f (es))



free_var_ZExpr :: ZExpr -> [ZVar]
free_var_ZExpr(ZVar v) = [v]
free_var_ZExpr(ZInt c ) = []
free_var_ZExpr(ZTuple exls ) = fvs free_var_ZExpr exls
free_var_ZExpr(ZSetDisplay exls ) = fvs free_var_ZExpr exls
free_var_ZExpr(ZSeqDisplay exls ) = fvs free_var_ZExpr exls
free_var_ZExpr(ZCall ex ex2) = free_var_ZExpr ex2 -- is this right??
free_var_ZExpr _ = []


rename_vars_CReplace :: t -> CReplace -> CReplace
rename_vars_CReplace lst (CRename zvarls1 zvarls) = (CRename zvarls1 zvarls)
rename_vars_CReplace lst (CRenameAssign zvarls1 zvarls) = (CRenameAssign zvarls1 zvarls)


rename_ZPred :: [String] -> ZPred -> ZPred
rename_ZPred lst (ZFalse{reason=a}) = (ZFalse{reason=a})
rename_ZPred lst (ZTrue{reason=a}) = (ZTrue{reason=a})
rename_ZPred lst (ZAnd p1 p2) = (ZAnd (rename_ZPred lst p1) (rename_ZPred lst p2))
rename_ZPred lst (ZOr p1 p2) = (ZOr (rename_ZPred lst p1) (rename_ZPred lst p2))
rename_ZPred lst (ZImplies p1 p2) = (ZImplies (rename_ZPred lst p1) (rename_ZPred lst p2))
rename_ZPred lst (ZIff p1 p2) = (ZIff (rename_ZPred lst p1) (rename_ZPred lst p2))
rename_ZPred lst (ZNot p) = (ZNot (rename_ZPred lst p))


inListVar :: Eq a => a -> [a] -> Bool
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


rename_ZExpr :: [String] -> ZExpr -> ZExpr
rename_ZExpr lst (ZVar (va,x))
  = case (inListVar va lst) of
        True -> (ZVar ("v_"++va,x))
        False -> (ZVar (va,x))
rename_ZExpr lst (ZInt zi) = (ZInt zi)
rename_ZExpr lst (ZTuple xprlst) = (ZTuple (map (rename_ZExpr lst) xprlst))
rename_ZExpr lst (ZBinding xs) = (ZBinding (bindingsVar lst xs))
rename_ZExpr lst (ZSetDisplay xprlst) = (ZSetDisplay (map (rename_ZExpr lst) xprlst))
rename_ZExpr lst (ZSeqDisplay xprlst) = (ZSeqDisplay (map (rename_ZExpr lst) xprlst))
rename_ZExpr lst (ZGivenSet gs) = (ZGivenSet gs)
rename_ZExpr lst (ZUniverse) = (ZUniverse)
rename_ZExpr lst (ZCall xpr1 xpr2) = (ZCall (rename_ZExpr lst xpr1) (rename_ZExpr lst xpr2))


bindingsVar :: [String] -> [(ZVar, ZExpr)] -> [(ZVar, ZExpr)]
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



rename_vars_CAction :: [String] -> CAction -> CAction
rename_vars_CAction lst (CActionCommand cmd) = (CActionCommand (rename_vars_CCommand lst cmd))
rename_vars_CAction lst (CActionName zn) = (CActionName zn)
rename_vars_CAction lst (CSPSkip ) = (CSPSkip )
rename_vars_CAction lst (CSPStop ) = (CSPStop )
rename_vars_CAction lst (CSPChaos) = (CSPChaos)
rename_vars_CAction lst (CSPCommAction c a) = (CSPCommAction (rename_vars_Comm lst c) (rename_vars_CAction lst a))
rename_vars_CAction lst (CSPGuard zp a) = (CSPGuard (rename_ZPred lst zp) (rename_vars_CAction lst a))
rename_vars_CAction lst (CSPSeq a1 a2) = (CSPSeq (rename_vars_CAction lst a1) (rename_vars_CAction lst a2))
rename_vars_CAction lst (CSPExtChoice a1 a2) = (CSPExtChoice (rename_vars_CAction lst a1) (rename_vars_CAction lst a2))
rename_vars_CAction lst (CSPIntChoice a1 a2) = (CSPIntChoice (rename_vars_CAction lst a1) (rename_vars_CAction lst a2))
rename_vars_CAction lst (CSPNSParal ns1 cs ns2 a1 a2) = (CSPNSParal ns1 cs ns2 (rename_vars_CAction lst a1) (rename_vars_CAction lst a2))
rename_vars_CAction lst (CSPParal cs a1 a2) = (CSPParal cs (rename_vars_CAction lst a1) (rename_vars_CAction lst a2))
rename_vars_CAction lst (CSPNSInter ns1 ns2 a1 a2) = (CSPNSInter ns1 ns2 (rename_vars_CAction lst a1) (rename_vars_CAction lst a2))
rename_vars_CAction lst (CSPInterleave a1 a2) = (CSPInterleave (rename_vars_CAction lst a1) (rename_vars_CAction lst a2))
rename_vars_CAction lst (CSPHide a cs) = (CSPHide (rename_vars_CAction lst a) cs)
rename_vars_CAction lst (CSPParAction zn zexprls) = (CSPParAction zn (map (rename_ZExpr lst) zexprls))
rename_vars_CAction lst (CSPRenAction zn crpl) = (CSPRenAction zn (rename_vars_CReplace lst crpl))
rename_vars_CAction lst (CSPRecursion zn a) = (CSPRecursion zn (rename_vars_CAction lst a))
rename_vars_CAction lst (CSPUnParAction zgf a zn) = (CSPUnParAction zgf (rename_vars_CAction lst a) zn)
rename_vars_CAction lst (CSPRepSeq zgf a) = (CSPRepSeq zgf (rename_vars_CAction lst a))
rename_vars_CAction lst (CSPRepExtChoice zgf a) = (CSPRepExtChoice zgf (rename_vars_CAction lst a))
rename_vars_CAction lst (CSPRepIntChoice zgf a) = (CSPRepIntChoice zgf (rename_vars_CAction lst a))
rename_vars_CAction lst (CSPRepParalNS cs zgf ns a) = (CSPRepParalNS cs zgf ns (rename_vars_CAction lst a))
rename_vars_CAction lst (CSPRepParal cs zgf a) = (CSPRepParal cs zgf (rename_vars_CAction lst a))
rename_vars_CAction lst (CSPRepInterlNS zgf ns a) = (CSPRepInterlNS zgf ns (rename_vars_CAction lst a))
rename_vars_CAction lst (CSPRepInterl zgf a) = (CSPRepInterl zgf (rename_vars_CAction lst a))

rename_vars_CCommand :: [String] -> CCommand -> CCommand
rename_vars_CCommand lst (CAssign zvarls1 zexprls) = (CAssign zvarls1 (map (rename_ZExpr lst) zexprls))
rename_vars_CCommand lst (CIf ga) = (CIf (rename_vars_CGActions lst ga))
rename_vars_CCommand lst (CVarDecl zgf a) = (CVarDecl zgf (rename_vars_CAction lst a))
rename_vars_CCommand lst (CAssumpt znls zp1 zp2) = (CAssumpt znls (rename_ZPred lst zp1) zp2)
rename_vars_CCommand lst (CAssumpt1 znls zp) = (CAssumpt1 znls zp)
rename_vars_CCommand lst (CPrefix zp1 zp2) = (CPrefix (rename_ZPred lst zp1) zp2)
rename_vars_CCommand lst (CPrefix1 zp) = (CPrefix1 zp)
rename_vars_CCommand lst (CommandBrace zp) = (CommandBrace zp)
rename_vars_CCommand lst (CommandBracket zp) = (CommandBracket zp)
rename_vars_CCommand lst (CValDecl zgf a) = (CValDecl zgf (rename_vars_CAction lst a))
rename_vars_CCommand lst (CResDecl zgf a) = (CResDecl zgf (rename_vars_CAction lst a))
rename_vars_CCommand lst (CVResDecl zgf a) = (CVResDecl zgf (rename_vars_CAction lst a))

rename_vars_Comm :: [String] -> Comm -> Comm
rename_vars_Comm lst (ChanComm zn cpls) = (ChanComm zn (map (rename_vars_CParameter lst) cpls))
rename_vars_Comm lst (ChanGenComm zn zexprls cpls) = (ChanGenComm zn (map (rename_ZExpr lst) zexprls) (map (rename_vars_CParameter lst) cpls))

rename_vars_CParameter :: [String] -> CParameter -> CParameter
rename_vars_CParameter lst (ChanInp zn) = (ChanInp zn)
rename_vars_CParameter lst (ChanInpPred zn zp) = (ChanInpPred zn (rename_ZPred lst zp))
rename_vars_CParameter lst (ChanOutExp ze) = (ChanOutExp (rename_ZExpr lst ze))
rename_vars_CParameter lst (ChanDotExp ze) = (ChanDotExp (rename_ZExpr lst ze))

rename_vars_CGActions :: [String] -> CGActions -> CGActions
rename_vars_CGActions lst (CircGAction zp a) = (CircGAction (rename_ZPred lst zp) (rename_vars_CAction lst a))
rename_vars_CGActions lst (CircThenElse cga1 cga2) = (CircThenElse (rename_vars_CGActions lst cga1) (rename_vars_CGActions lst cga2))
rename_vars_CGActions lst (CircElse pa) = (CircElse pa)


get_chan_param :: [CParameter] -> [ZVar]
get_chan_param [] = []
get_chan_param [ChanDotExp (ZVar (x,_))] = [(x,[])]
get_chan_param [ChanOutExp (ZVar (x,_))] = [(x,[])]
get_chan_param [_] = []
get_chan_param ((ChanDotExp (ZVar (x,_))):xs) = [(x,[])]++(get_chan_param xs)
get_chan_param ((ChanOutExp (ZVar (x,_))):xs) = [(x,[])]++(get_chan_param xs)
get_chan_param (_:xs) = (get_chan_param xs)


 -- Artur - 15/12/2016
 -- What we find below this line was taken from the Data.List module
 -- It is hard to import such package with Haskabelle, so I had
 -- to put it directly into my code.

delete_from_list x []  = []
delete_from_list x [v]
   = (case x == v of
       True -> []
       False -> [v])
delete_from_list x (v : va)
   = (case x == v of
       True -> delete_from_list x va
       False -> (v : (delete_from_list x va)))

setminus [] _  = []
setminus (v : va) [] = (v : va)
setminus (v : va) (b : vb)
     = (delete_from_list b (v : va)) ++ (setminus (v : va) vb)


-- From Data.List

member x [] = False
member x (b:y) = if x==b then True else member x y

intersect [] y = []
intersect (a:x) y = if member a y then a : (intersect x y) else intersect x y

union [] y = y
union (a:x) y = if (member a y) then (union x y) else a : (union x y);

remdups :: (Eq a) => [a] -> [a]
remdups [] = []
remdups (x:xs)
 | member x xs  = remdups xs
 | otherwise = x : remdups xs
-- | 'delete' @x@ removes the first occurrence of @x@ from its list argument.
-- For example,
--
-- > delete 'a' "banana" == "bnana"
--
-- It is a special case of 'deleteBy', which allows the programmer to
-- supply their own equality test.

delete                  :: (Eq a) => a -> [a] -> [a]
delete                  =  deleteBy (==)

-- | The 'deleteBy' function behaves like 'delete', but takes a
-- user-supplied equality predicate.
deleteBy                :: (a -> a -> Bool) -> a -> [a] -> [a]
deleteBy _  _ []        = []
deleteBy eq x (y:ys)    = if x `eq` y then ys else y : deleteBy eq x ys


-- Not exported:
-- Note that we keep the call to `eq` with arguments in the
-- same order as in the reference implementation
-- 'xs' is the list of things we've seen so far,
-- 'y' is the potential new element
elem_by :: (a -> a -> Bool) -> a -> [a] -> Bool
elem_by _  _ []         =  False
elem_by eq y (x:xs)     =  y `eq` x || elem_by eq y xs
