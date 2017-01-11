module OmegaDefs
where
import AST


join_name n v = n ++ "_" ++ v


free_var_CAction :: CAction -> [ZVar]
free_var_CAction (CActionCommand c)
 = (free_var_comnd c)
free_var_CAction (CSPCommAction (ChanComm com xs) c)
 = (get_chan_var xs)++(free_var_CAction c)
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
free_var_CAction (CSPRecursion nm c)
 = (free_var_CAction c)
free_var_CAction (CSPUnParAction lst c nm)
 =  (setminus (free_var_CAction c) (fvs free_var_ZGenFilt lst))
free_var_CAction (CSPRepSeq lst c)
 =  (setminus (free_var_CAction c) (fvs free_var_ZGenFilt lst))
free_var_CAction (CSPRepExtChoice lst c)
 =  (setminus (free_var_CAction c) (fvs free_var_ZGenFilt lst))
free_var_CAction (CSPRepIntChoice lst c)
 =  (setminus (free_var_CAction c) (fvs free_var_ZGenFilt lst))
free_var_CAction (CSPRepParalNS cs lst ns c)
 =  (setminus (free_var_CAction c) (fvs free_var_ZGenFilt lst))
free_var_CAction (CSPRepParal cs lst c)
 =  (setminus (free_var_CAction c) (fvs free_var_ZGenFilt lst))
free_var_CAction (CSPRepInterlNS lst ns c)
 =  (setminus (free_var_CAction c) (fvs free_var_ZGenFilt lst))
free_var_CAction (CSPRepInterl lst c)
 =  (setminus (free_var_CAction c) (fvs free_var_ZGenFilt lst))
free_var_CAction _ = []

free_var_comnd (CAssign v e)
 = v
free_var_comnd (CIf ga)
 = free_var_if ga
free_var_comnd (CVarDecl z c)
 =  (setminus (free_var_CAction c) (fvs free_var_ZGenFilt z))
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
 =  (setminus (free_var_CAction c) (fvs free_var_ZGenFilt z))
free_var_comnd (CResDecl z c)
 =  (setminus (free_var_CAction c) (fvs free_var_ZGenFilt z))
free_var_comnd (CVResDecl z c)
 =  (setminus (free_var_CAction c) (fvs free_var_ZGenFilt z))

free_var_if (CircGAction p a)
 = (free_var_ZPred p)++(free_var_CAction a)
free_var_if (CircThenElse ga gb)
 = (free_var_if ga)++(free_var_if gb)
free_var_if (CircElse (CircusAction a))
 = (free_var_CAction a)
free_var_if (CircElse (ParamActionDecl x (CircusAction a)))
 =  (setminus (free_var_CAction a) (fvs free_var_ZGenFilt x))

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
free_var_ZPred x = error "Don't know what free vars of this right now. Check back later"

fvs :: (t -> [t1]) -> [t] -> [t1]
fvs f [] = []
fvs f (e:es) = f(e) ++ (fvs f (es))



free_var_ZExpr :: ZExpr -> [ZVar]
free_var_ZExpr(ZVar v) = [v]
free_var_ZExpr(ZInt c ) = []
free_var_ZExpr(ZSetDisplay exls ) = fvs free_var_ZExpr exls
free_var_ZExpr(ZSeqDisplay exls ) = fvs free_var_ZExpr exls
free_var_ZExpr(ZCall ex ex2) = free_var_ZExpr ex2 -- is this right??
free_var_ZExpr _ = []



get_chan_var :: [CParameter] -> [ZVar]
get_chan_var [] = []
get_chan_var [ChanDotExp (ZVar (x,_))]
 = [(x,[])]
get_chan_var [ChanOutExp (ZVar (x,_))]
 = [(x,[])]
get_chan_var [_]
 = []
get_chan_var ((ChanDotExp (ZVar (x,_))):xs)
 = [(x,[])]++(get_chan_var xs)
get_chan_var ((ChanOutExp (ZVar (x,_))):xs)
 = [(x,[])]++(get_chan_var xs)
get_chan_var (_:xs) = (get_chan_var xs)


get_guard_pair :: CGActions -> [(ZPred, CAction)]
get_guard_pair (CircThenElse (CircGAction g2 a2) (CircGAction g3 a3)) = [(g2,a2),(g3,a3)]
get_guard_pair (CircThenElse (CircGAction g1 a1) glx) = [(g1,a1)]++(get_guard_pair glx)
get_guard_pair _ = []


make_get_com :: [ZName] -> CAction -> CAction
make_get_com [x] c = (CSPCommAction (ChanComm "mget"[ChanDotExp (ZVar (x,[])),ChanInp ("v_"++x)]) c)
make_get_com (x:xs) c = (CSPCommAction (ChanComm "mget"[ChanDotExp (ZVar (x,[])),ChanInp ("v_"++x)]) (make_get_com xs c))
make_get_com x c = c    

make_set_com f [(x,_)] [y] c = (CSPCommAction (ChanComm "mset"[ChanDotExp (ZVar (x,[])),ChanOutExp y]) (f c))
make_set_com f ((x,_):xs) (y:ys) c = (CSPCommAction (ChanComm "mset"[ChanDotExp (ZVar (x,[])),ChanOutExp y]) (make_set_com f xs ys c))


mk_guard_pair f [(g,a)] = (CircGAction g (f a))
mk_guard_pair f ((g,a):ls) = (CircThenElse (CircGAction g (f a)) (mk_guard_pair f ls))

-- All that should be found in the Defsets.hs file
getWrtV :: t -> [t1]
getWrtV xs = []



rename_vars_CAction :: CAction -> CAction
rename_vars_CAction (CActionCommand cmd) = (CActionCommand (rename_vars_CCommand cmd))
rename_vars_CAction (CActionName zn) = (CActionName zn)
rename_vars_CAction (CSPSkip ) = (CSPSkip )
rename_vars_CAction (CSPStop ) = (CSPStop )
rename_vars_CAction (CSPChaos) = (CSPChaos)
rename_vars_CAction (CSPCommAction c a) = (CSPCommAction (rename_vars_Comm c) (rename_vars_CAction a))
rename_vars_CAction (CSPGuard zp a) = (CSPGuard (rename_ZPred zp) (rename_vars_CAction a))
rename_vars_CAction (CSPSeq a1 a2) = (CSPSeq (rename_vars_CAction a1) (rename_vars_CAction a2))
rename_vars_CAction (CSPExtChoice a1 a2) = (CSPExtChoice (rename_vars_CAction a1) (rename_vars_CAction a2))
rename_vars_CAction (CSPIntChoice a1 a2) = (CSPIntChoice (rename_vars_CAction a1) (rename_vars_CAction a2))
rename_vars_CAction (CSPNSParal ns1 cs ns2 a1 a2) = (CSPNSParal ns1 cs ns2 (rename_vars_CAction a1) (rename_vars_CAction a2))
rename_vars_CAction (CSPParal cs a1 a2) = (CSPParal cs (rename_vars_CAction a1) (rename_vars_CAction a2))
rename_vars_CAction (CSPNSInter ns1 ns2 a1 a2) = (CSPNSInter ns1 ns2 (rename_vars_CAction a1) (rename_vars_CAction a2))
rename_vars_CAction (CSPInterleave a1 a2) = (CSPInterleave (rename_vars_CAction a1) (rename_vars_CAction a2))
rename_vars_CAction (CSPHide a cs) = (CSPHide (rename_vars_CAction a) cs)
rename_vars_CAction (CSPParAction zn zexprls) = (CSPParAction zn (map (rename_ZExpr) zexprls))
rename_vars_CAction (CSPRenAction zn crpl) = (CSPRenAction zn crpl)
rename_vars_CAction (CSPRecursion zn a) = (CSPRecursion zn (rename_vars_CAction a))
rename_vars_CAction (CSPUnParAction zgf a zn) = (CSPUnParAction zgf (rename_vars_CAction a) zn)
rename_vars_CAction (CSPRepSeq zgf a) = (CSPRepSeq zgf (rename_vars_CAction a))
rename_vars_CAction (CSPRepExtChoice zgf a) = (CSPRepExtChoice zgf (rename_vars_CAction a))
rename_vars_CAction (CSPRepIntChoice zgf a) = (CSPRepIntChoice zgf (rename_vars_CAction a))
rename_vars_CAction (CSPRepParalNS cs zgf ns a) = (CSPRepParalNS cs zgf ns (rename_vars_CAction a))
rename_vars_CAction (CSPRepParal cs zgf a) = (CSPRepParal cs zgf (rename_vars_CAction a))
rename_vars_CAction (CSPRepInterlNS zgf ns a) = (CSPRepInterlNS zgf ns (rename_vars_CAction a))
rename_vars_CAction (CSPRepInterl zgf a) = (CSPRepInterl zgf (rename_vars_CAction a))

rename_vars_CCommand :: CCommand -> CCommand
rename_vars_CCommand (CAssign zvarls1 zexprls) = (CAssign (map rename_vars_Zvar zvarls1) (map (rename_ZExpr) zexprls))
rename_vars_CCommand (CIf ga) = (CIf (rename_vars_CGActions ga))
rename_vars_CCommand (CVarDecl zgf a) = (CVarDecl zgf (rename_vars_CAction a))
rename_vars_CCommand (CAssumpt znls zp1 zp2) = (CAssumpt znls (rename_ZPred zp1) zp2)
rename_vars_CCommand (CAssumpt1 znls zp) = (CAssumpt1 znls zp)
rename_vars_CCommand (CPrefix zp1 zp2) = (CPrefix (rename_ZPred zp1) zp2)
rename_vars_CCommand (CPrefix1 zp) = (CPrefix1 zp)
rename_vars_CCommand (CommandBrace zp) = (CommandBrace zp)
rename_vars_CCommand (CommandBracket zp) = (CommandBracket zp)
rename_vars_CCommand (CValDecl zgf a) = (CValDecl zgf (rename_vars_CAction a))
rename_vars_CCommand (CResDecl zgf a) = (CResDecl zgf (rename_vars_CAction a))
rename_vars_CCommand (CVResDecl zgf a) = (CVResDecl zgf (rename_vars_CAction a))

rename_vars_Comm :: Comm -> Comm
rename_vars_Comm (ChanComm zn cpls) = (ChanComm zn (map (rename_vars_CParameter) cpls))
rename_vars_Comm (ChanGenComm zn zexprls cpls) = (ChanGenComm zn (map (rename_ZExpr) zexprls) (map (rename_vars_CParameter) cpls))

rename_vars_CParameter :: CParameter -> CParameter
rename_vars_CParameter (ChanInp zn) = (ChanInp zn)
rename_vars_CParameter (ChanInpPred zn zp) = (ChanInpPred zn (rename_ZPred zp))
rename_vars_CParameter (ChanOutExp ze) = (ChanOutExp (rename_ZExpr ze))
rename_vars_CParameter (ChanDotExp ze) = (ChanDotExp (rename_ZExpr ze))

rename_vars_CGActions :: CGActions -> CGActions
rename_vars_CGActions (CircGAction zp a) = (CircGAction (rename_ZPred zp) (rename_vars_CAction a))
rename_vars_CGActions (CircThenElse cga1 cga2) = (CircThenElse (rename_vars_CGActions cga1) (rename_vars_CGActions cga2))
rename_vars_CGActions (CircElse pa) = (CircElse pa)

rename_ZPred :: ZPred -> ZPred
rename_ZPred (ZFalse{reason=a}) = (ZFalse{reason=a})
rename_ZPred (ZTrue{reason=a}) = (ZTrue{reason=a})
rename_ZPred (ZAnd p1 p2) = (ZAnd (rename_ZPred p1) (rename_ZPred p2))

rename_ZExpr :: ZExpr -> ZExpr
rename_ZExpr (ZVar (va,x))
  = case (is_ZVar_st va) of
        True -> (ZVar ("v_"++va,x))
        False -> (ZVar (va,x))
rename_ZExpr (ZInt zi) = (ZInt zi)
rename_ZExpr (ZCall xpr1 xpr2) = (ZCall (rename_ZExpr xpr1) (rename_ZExpr xpr2))


rename_vars_CReplace :: CReplace -> CReplace
rename_vars_CReplace (CRename zvarls1 zvarls) = (CRename zvarls1 zvarls)
rename_vars_CReplace (CRenameAssign zvarls1 zvarls) = (CRenameAssign zvarls1 zvarls)

inListVar :: a -> [a] -> Bool
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

bindingsVar :: [(ZVar, ZExpr)] -> [(ZVar, ZExpr)]
bindingsVar [] = []
bindingsVar [((va,x),b)]
  = case (is_ZVar_st va) of
          True -> [(("v_"++va,x),(rename_ZExpr b))]
          False -> [((va,x),(rename_ZExpr b))]
bindingsVar (((va,x),b):xs)
  = case (is_ZVar_st va) of
          True -> [(("v_"++va,x),(rename_ZExpr b))]++(bindingsVar xs)
          False -> [((va,x),(rename_ZExpr b))]++(bindingsVar xs)

rename_vars_Zvar (a,x)
 = case (isPrefixOf "st_var_" a) of
    True -> ((join_name "v" a),x)
    _ -> (a,x)
get_ZVar_st (a,x)
 = case (isPrefixOf "st_var_" a) of
    True -> [a]
    _ -> []
is_ZVar_st a = isPrefixOf "st_var_" a

is_Var_or_Int [ZVar (a,b)] = True
is_Var_or_Int [ZInt x] = True
is_Var_or_Int ((ZVar (a,b)):xs) = True && is_Var_or_Int xs
is_Var_or_Int ((ZInt x):xs) = True && is_Var_or_Int xs
is_Var_or_Int _ = False


rep_CSPRepSeq :: ZName -> [ZExpr] -> CAction
rep_CSPRepSeq a [x]
  = (CSPParAction a [x])
rep_CSPRepSeq a (x:xs)
  = CSPSeq (CSPParAction a [x]) (rep_CSPRepSeq a xs)

rep_CSPRepIntChoice :: ZName -> [ZExpr] -> CAction
rep_CSPRepIntChoice a [x]
  = (CSPParAction a [x])
rep_CSPRepIntChoice a (x:xs)
  = CSPIntChoice (CSPParAction a [x]) (rep_CSPRepIntChoice a xs)

rep_CSPRepExtChoice :: ZName -> [ZExpr] -> CAction
rep_CSPRepExtChoice a [x]
  = (CSPParAction a [x])
rep_CSPRepExtChoice a (x:xs)
  = CSPExtChoice (CSPParAction a [x]) (rep_CSPRepExtChoice a xs)

rep_CSPRepParalNS :: ZName -> ZName -> ZName -> String -> [ZExpr] -> CAction
rep_CSPRepParalNS a _ _ _ [x]
  = (CSPParAction a [x])
rep_CSPRepParalNS a cs ns y (x:xs)
  = (CSPNSParal (NSExprParam ns [x]) (CSExpr cs)
    (NSBigUnion (ZSetComp
           [Choose (y,[]) (ZSetDisplay xs)]
           (Just (ZCall (ZVar (ns,[])) (ZVar (y,[])))) ) )
     (CSPParAction a [x]) (rep_CSPRepParalNS a cs ns y xs) )

rep_CSPRepInterlNS :: ZName -> ZName -> String -> [ZExpr] -> CAction
rep_CSPRepInterlNS a _ _ [x]
  = (CSPParAction a [x])
rep_CSPRepInterlNS a ns y (x:xs)
  = (CSPNSInter (NSExprParam ns [x])
    (NSBigUnion (ZSetComp
           [Choose (y,[]) (ZSetDisplay xs)]
           (Just (ZCall (ZVar (ns,[])) (ZVar (y,[])))) ) )
     (CSPParAction a [x]) (rep_CSPRepInterlNS a ns y xs) )


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

remdups :: [a] -> [a]
remdups [] = []
remdups (x:xs)
 | member x xs  = remdups xs
 | otherwise = x : remdups xs


-- Not exported:
-- Note that we keep the call to `eq` with arguments in the
-- same order as in the reference implementation
-- 'xs' is the list of things we've seen so far,
-- 'y' is the potential new element
elem_by :: (a -> a -> Bool) -> a -> [a] -> Bool
elem_by _  _ []         =  False
elem_by eq y (x:xs)     =  y `eq` x || elem_by eq y xs



-- | The 'isPrefixOf' function takes two lists and returns 'True'
-- iff the first list is a prefix of the second.
isPrefixOf              :: [a] -> [a] -> Bool
isPrefixOf [] _         =  True
isPrefixOf _  []        =  False
isPrefixOf (x:xs) (y:ys)=  x == y && isPrefixOf xs ys