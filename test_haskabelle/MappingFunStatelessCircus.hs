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
omega_CAction lst (CSPCommAction (ChanComm c []) a) = (CSPCommAction (ChanComm c []) (omega_CAction lst a))
omega_CAction lst (CSPCommAction (ChanComm c ((ChanOutExp e):xs)) a) = omega_CAction lst (CSPCommAction (ChanComm c ((ChanDotExp e):xs)) a)
omega_CAction lst (CSPSeq ca cb) = (CSPSeq (omega_CAction lst ca) (omega_CAction lst cb))
omega_CAction lst (CSPIntChoice ca cb) = (CSPIntChoice (omega_CAction lst ca) (omega_CAction lst cb))
omega_CAction lst (CSPCommAction (ChanComm c []) a) = (CSPCommAction (ChanComm c []) (omega_CAction lst a))
omega_CAction lst (CSPHide a cs) = (CSPHide (omega_CAction lst a) cs)
omega_CAction lst (CSPRecursion x c) = (CSPRecursion x (omega_CAction lst c))
omega_CAction lst (CActionCommand (CommandBrace g)) = omega_CAction lst (CActionCommand (CPrefix g (ZTrue {reason = []})))
omega_CAction lst (CActionCommand (CommandBracket g)) = omega_CAction lst (CActionCommand (CPrefix1 g))
omega_CAction lst (CSPRenAction a (CRenameAssign left right)) = (CSPRenAction a (CRename right left))
omega_CAction lst (CSPRepSeq [Choose (x,[]) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1,[])]))
  = case x == x1 of
    True -> omega_CAction lst (rep_CSPRepSeq lst act xs)
    _  -> (CSPRepSeq [Choose (x,[]) (ZSeqDisplay xs)]
          (omega_CAction lst (CSPParAction act [ZVar (x1,[])])))
omega_CAction lst (CSPRepSeq [Choose (x,[]) v] act)
  = (CSPRepSeq [Choose (x,[]) v] (omega_CAction lst act))

omega_CAction lst (CSPRepExtChoice [Choose (x,[]) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1,[])]))
  = case x == x1 of
    True -> rep_CSPRepExtChoice lst act xs
    _  -> (CSPRepExtChoice [Choose (x,[]) (ZSeqDisplay xs)]
          (CSPParAction act [ZVar (x1,[])]))
omega_CAction lst (CSPRepExtChoice [Choose (x,[]) v]
          act)
  = (CSPRepExtChoice [Choose (x,[]) v] (omega_CAction lst act))

omega_CAction lst (CSPRepIntChoice [Choose (x,[]) (ZSeqDisplay xs)]
          (CSPParAction act [ZVar (x1,[])]))
  = case x == x1 of
    True -> rep_CSPRepIntChoice lst act xs
    _  -> (CSPRepIntChoice [Choose (x,[]) (ZSeqDisplay xs)]
          (CSPParAction act [ZVar (x1,[])]))
omega_CAction lst (CSPRepIntChoice [Choose (x,[]) v] act)
  = (CSPRepIntChoice [Choose (x,[]) v] (omega_CAction lst act))

omega_CAction lst (CSPRepParalNS (CSExpr cs) [Choose (x,[]) (ZSetDisplay lsx)]
          (NSExprParam ns [ZVar (x1,[])])
          (CSPParAction a [ZVar (x2,[])]))
  = case (x == x1) && (x == x2) of
    True -> rep_CSPRepParalNS lst a cs ns x lsx
    _  -> (CSPRepParalNS (CSExpr cs) [Choose (x,[]) (ZSetDisplay lsx)]
          (NSExprParam ns [ZVar (x1,[])])
          (omega_CAction lst (CSPParAction a [ZVar (x2,[])])))
omega_CAction lst (CSPRepParalNS (CSExpr cs) [Choose (x,[]) (ZSetDisplay lsx)]
          (NSExprParam ns [ZVar (x1,[])]) act)
  = (CSPRepParalNS (CSExpr cs) [Choose (x,[]) (ZSetDisplay lsx)]
          (NSExprParam ns [ZVar (x1,[])])
          (omega_CAction lst act))
omega_CAction lst (CSPRepInterlNS [Choose (x,[]) (ZSetDisplay lsx)]
          (NSExprParam ns [ZVar (x1,[])])
          (CSPParAction a [ZVar (x2,[])]))
  = case (x == x1) && (x == x2) of
    True -> rep_CSPRepInterlNS lst a ns x lsx
    _  ->  (CSPRepInterlNS [Choose (x,[]) (ZSetDisplay lsx)]
          (NSExprParam ns [ZVar (x1,[])])
          (omega_CAction lst (CSPParAction a [ZVar (x2,[])])))
omega_CAction lst (CSPRepInterlNS [Choose (x,[]) (ZSetDisplay lsx)]
          (NSExprParam ns [ZVar (x1,[])])
          act)
  = (CSPRepInterlNS [Choose (x,[]) (ZSetDisplay lsx)]
          (NSExprParam ns [ZVar (x1,[])])
          (omega_CAction lst act))

omega_CAction lst (CActionCommand (CIf (CircGAction g a)))
  = make_get_com lst lsx (rename_vars_CAction (map fst lsx) (CActionCommand
             (CIf (CircGAction g (omega_prime_CAction lst a)))))
  where
   lsx = free_var_ZPred g

omega_CAction lst (CSPCommAction (ChanComm c ((ChanDotExp e):xs)) a)
  = make_get_com lst lxs (rename_vars_CAction (map fst lxs) (CSPCommAction (ChanComm c ((ChanDotExp e):xs)) (omega_prime_CAction lst a)))
  where lxs = (get_chan_param ((ChanDotExp e):xs)) `intersect` (filter_state_comp lst)

omega_CAction lst (CActionCommand (CAssign varls valls)) 
  = make_get_com lst varls (rename_vars_CAction (map fst (filter_state_comp lst)) (make_set_com lst varls valls CSPSkip))


omega_CAction lst (CActionCommand (CIf (CircThenElse gl glx)))
  = make_get_com lst lsx (rename_vars_CAction (map fst lsx) (CActionCommand (CIf (mk_guard_pair lst guard_pair))))
  where
   guard_pair = get_guard_pair (CircThenElse gl glx)
   lsx = nub $ concat $ map free_var_ZPred (map fst guard_pair)


-- Omega Prime

omega_prime_CAction :: [(ZName, ZVar, ZExpr)] -> CAction -> CAction
omega_prime_CAction lst CSPSkip = CSPSkip
omega_prime_CAction lst CSPChaos = CSPChaos
omega_prime_CAction lst CSPStop = CSPStop
omega_prime_CAction lst (CActionCommand (CAssign varls valls)) = (make_set_com lst varls valls CSPSkip)
omega_prime_CAction lst (CActionCommand (CIf (CircGAction g a))) = (CActionCommand (CIf (CircGAction g (omega_prime_CAction lst a))))
omega_prime_CAction lst (CActionCommand (CommandBrace g)) = omega_prime_CAction lst (CActionCommand (CPrefix g (ZTrue {reason = []})))
omega_prime_CAction lst (CActionCommand (CommandBracket g)) = omega_prime_CAction lst (CActionCommand (CPrefix1 g))
omega_prime_CAction lst (CActionName n) = (CActionName n)
omega_prime_CAction lst (CSPCommAction (ChanComm c []) a) = (CSPCommAction (ChanComm c []) (omega_prime_CAction lst a))
omega_prime_CAction lst (CSPCommAction (ChanComm c x) a) = (CSPCommAction (ChanComm c x) (omega_prime_CAction lst a))
omega_prime_CAction lst (CSPGuard g a) = (CSPGuard g (omega_prime_CAction lst a))
omega_prime_CAction lst (CSPHide a cs) = (CSPHide (omega_prime_CAction lst a) cs)
omega_prime_CAction lst (CSPIntChoice ca cb) = (CSPIntChoice (omega_prime_CAction lst ca) (omega_prime_CAction lst cb))
omega_prime_CAction lst (CSPRecursion x c) = (CSPRecursion x (omega_prime_CAction lst c))
omega_prime_CAction lst (CSPRenAction a (CRenameAssign left right)) = (CSPRenAction a (CRename right left))
omega_prime_CAction lst (CSPRepIntChoice [Choose (x,[]) v] act) = (CSPRepIntChoice [Choose (x,[]) v] (omega_prime_CAction lst act))
omega_prime_CAction lst (CSPRepSeq [Choose (x,[]) v] act) = (CSPRepSeq [Choose (x,[]) v] (omega_prime_CAction lst act))
omega_prime_CAction lst (CSPSeq ca cb) = (CSPSeq (omega_prime_CAction lst ca) (omega_prime_CAction lst cb))

omega_prime_CAction lst (CActionCommand (CIf (CircThenElse gl glx)))
  = (CActionCommand (CIf (mk_guard_pair lst guard_pair)))
  where
   guard_pair = get_guard_pair (CircThenElse gl glx)

omega_prime_CAction lst (CSPRepInterlNS [Choose (x,[]) (ZSetDisplay lsx)]
          (NSExprParam ns [ZVar (x1,[])])
          (CSPParAction a [ZVar (x2,[])]))
  = case (x == x1) && (x == x2) of
    True -> rep_CSPRepInterlNS lst a ns x lsx
    _  ->  (CSPRepInterlNS [Choose (x,[]) (ZSetDisplay lsx)]
          (NSExprParam ns [ZVar (x1,[])])
          (omega_prime_CAction lst (CSPParAction a [ZVar (x2,[])])))
omega_prime_CAction lst (CSPRepInterlNS [Choose (x,[]) (ZSetDisplay lsx)]
          (NSExprParam ns [ZVar (x1,[])])
          act)
  = (CSPRepInterlNS [Choose (x,[]) (ZSetDisplay lsx)]
          (NSExprParam ns [ZVar (x1,[])])
          (omega_prime_CAction lst act))

omega_prime_CAction lst (CSPRepParalNS (CSExpr cs) [Choose (x,[]) (ZSetDisplay lsx)]
          (NSExprParam ns [ZVar (x1,[])])
          (CSPParAction a [ZVar (x2,[])]))
  = case (x == x1) && (x == x2) of
    True -> rep_CSPRepParalNS lst a cs ns x lsx
    _  -> (CSPRepParalNS (CSExpr cs) [Choose (x,[]) (ZSetDisplay lsx)]
          (NSExprParam ns [ZVar (x1,[])])
          (omega_prime_CAction lst (CSPParAction a [ZVar (x2,[])])))
omega_prime_CAction lst (CSPRepParalNS (CSExpr cs) [Choose (x,[]) (ZSetDisplay lsx)]
          (NSExprParam ns [ZVar (x1,[])]) act)
  = (CSPRepParalNS (CSExpr cs) [Choose (x,[]) (ZSetDisplay lsx)]
          (NSExprParam ns [ZVar (x1,[])])
          (omega_prime_CAction lst act))

omega_prime_CAction lst (CSPRepSeq [Choose (x,[]) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1,[])]))
  = case x == x1 of
    True -> omega_prime_CAction lst (rep_CSPRepSeq lst act xs)
    _  -> (CSPRepSeq [Choose (x,[]) (ZSeqDisplay xs)]
          (omega_prime_CAction lst (CSPParAction act [ZVar (x1,[])])))
omega_prime_CAction lst (CSPRepExtChoice [Choose (x,[]) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1,[])]))
  = case x == x1 of
    True -> rep_CSPRepExtChoice lst act xs
    _  -> (CSPRepExtChoice [Choose (x,[]) (ZSeqDisplay xs)]
          (CSPParAction act [ZVar (x1,[])]))

omega_prime_CAction lst (CSPRepIntChoice [Choose (x,[]) (ZSeqDisplay xs)]
          (CSPParAction act [ZVar (x1,[])]))
  = case x == x1 of
    True -> rep_CSPRepIntChoice lst act xs
    _  -> (CSPRepIntChoice [Choose (x,[]) (ZSeqDisplay xs)]
          (CSPParAction act [ZVar (x1,[])]))

-- Extra from MappingFunStatelesssCircus.lhs
rep_CSPRepSeq :: [(ZName, ZVar, ZExpr)] -> ZName -> [ZExpr] -> CAction
rep_CSPRepSeq lst a [x]
  = omega_CAction lst (CSPParAction a [x])
rep_CSPRepSeq lst a (x:xs)
  = CSPSeq (omega_CAction lst (CSPParAction a [x])) (rep_CSPRepSeq lst a xs)

rep_CSPRepIntChoice :: [(ZName, ZVar, ZExpr)] -> ZName -> [ZExpr] -> CAction
rep_CSPRepIntChoice lst a [x]
  = omega_CAction lst (CSPParAction a [x])
rep_CSPRepIntChoice lst a (x:xs)
  = CSPIntChoice (omega_CAction lst (CSPParAction a [x])) (rep_CSPRepIntChoice lst a xs)

rep_CSPRepExtChoice :: [(ZName, ZVar, ZExpr)] -> ZName -> [ZExpr] -> CAction
rep_CSPRepExtChoice lst a [x]
  =  omega_CAction lst (CSPParAction a [x])
rep_CSPRepExtChoice lst a (x:xs)
  = CSPExtChoice ( omega_CAction lst (CSPParAction a [x])) (rep_CSPRepExtChoice lst a xs)

rep_CSPRepParalNS :: [(ZName, ZVar, ZExpr)] -> ZName -> ZName -> ZName -> String -> [ZExpr] -> CAction
rep_CSPRepParalNS lst a _ _ _ [x]
  =  omega_CAction lst (CSPParAction a [x])
rep_CSPRepParalNS lst a cs ns y (x:xs)
  = (CSPNSParal (NSExprParam ns [x]) (CSExpr cs)
    (NSBigUnion (ZSetComp
           [Choose (y,[]) (ZSetDisplay xs)]
           (Just (ZCall (ZVar (ns,[])) (ZVar (y,[])))) ) )
     ( omega_CAction lst (CSPParAction a [x])) (rep_CSPRepParalNS lst a cs ns y xs) )

rep_CSPRepInterlNS :: [(ZName, ZVar, ZExpr)] -> ZName -> ZName -> String -> [ZExpr] -> CAction
rep_CSPRepInterlNS lst a _ _ [x]
  =  omega_CAction lst (CSPParAction a [x])
rep_CSPRepInterlNS lst a ns y (x:xs)
  = (CSPNSInter (NSExprParam ns [x])
    (NSBigUnion (ZSetComp
           [Choose (y,[]) (ZSetDisplay xs)]
           (Just (ZCall (ZVar (ns,[])) (ZVar (y,[])))) ) )
     ( omega_CAction lst (CSPParAction a [x])) (rep_CSPRepInterlNS lst a ns y xs) )

-- 

filter_state_comp :: [(ZName, ZVar, ZExpr)] -> [ZVar]
filter_state_comp [] = []
filter_state_comp [(_, v, _)] = [v]
filter_state_comp ((_, v, _):xs) = [v]++(filter_state_comp xs)

get_guard_pair :: CGActions -> [(ZPred, CAction)]
get_guard_pair (CircThenElse (CircGAction g2 a2) (CircGAction g3 a3)) = [(g2,a2),(g3,a3)]
get_guard_pair (CircThenElse (CircGAction g1 a1) glx) = [(g1,a1)]++(get_guard_pair glx)


mk_guard_pair :: [(ZName, ZVar, ZExpr)] -> [(ZPred, CAction)] -> CGActions
mk_guard_pair lst [(g,a)] = (CircGAction g (omega_prime_CAction lst a))
mk_guard_pair lst ((g,a):ls) = (CircThenElse (CircGAction g (omega_prime_CAction lst a)) (mk_guard_pair lst ls))


make_get_com :: [(ZName, ZVar, ZExpr)] -> [ZVar] -> CAction -> CAction
make_get_com lst [(x,[])] c = (CSPCommAction (ChanComm "mget"[ChanDotExp (ZVar ((get_proc_name x lst)++"_"++x,[])),ChanInp ("v"++(get_proc_name x lst)++"_"++x)]) c)
make_get_com lst ((x,[]):xs) c = (CSPCommAction (ChanComm "mget"[ChanDotExp (ZVar ((get_proc_name x lst)++"_"++x,[])),ChanInp ("v"++(get_proc_name x lst)++"_"++x)]) (make_get_com lst xs c))
make_get_com lst x c = c   

get_proc_name :: ZName -> [(ZName, ZVar, ZExpr)] -> ZName
get_proc_name x [(a,(va,x1),b)]
 = case x == va of
  True -> a
  _ -> ""
get_proc_name x ((a,(va,x1),b):vst)
 = case x == va of
  True -> a
  _ -> get_proc_name x vst


make_set_com :: [(ZName, ZVar, ZExpr)] -> [ZVar] -> [ZExpr] -> CAction -> CAction
make_set_com lst [(x,[])] [y] c = (CSPCommAction (ChanComm "mset"[ChanDotExp (ZVar ((get_proc_name x lst)++"_"++x,[])),ChanOutExp y]) (omega_CAction lst c))
make_set_com lst (((x,[])):xs) (y:ys) c = (CSPCommAction (ChanComm "mset"[ChanDotExp (ZVar ((get_proc_name x lst)++"_"++x,[])),ChanOutExp y]) (make_set_com lst xs ys c))


-- All that should be found in the Defsets.hs file
getWrtV :: t -> [t1]
getWrtV xs = []

free_var_CAction :: CAction -> [ZVar]
free_var_CAction (CActionCommand c) = (free_var_comnd c)
free_var_CAction (CSPCommAction (ChanComm com xs) c) = (get_chan_param xs)++(free_var_CAction c)
free_var_CAction (CSPGuard p c) = (free_var_ZPred p)++(free_var_CAction c)
free_var_CAction (CSPSeq ca cb) = (free_var_CAction ca)++(free_var_CAction cb)
free_var_CAction (CSPExtChoice ca cb) = (free_var_CAction ca)++(free_var_CAction cb)
free_var_CAction (CSPIntChoice ca cb) = (free_var_CAction ca)++(free_var_CAction cb)
free_var_CAction (CSPNSParal ns1 cs ns2 ca cb) = (free_var_CAction ca)++(free_var_CAction cb)
free_var_CAction (CSPParal cs ca cb) = (free_var_CAction ca)++(free_var_CAction cb)
free_var_CAction (CSPNSInter ns1 ns2 ca cb) = (free_var_CAction ca)++(free_var_CAction cb)
free_var_CAction (CSPInterleave ca cb) = (free_var_CAction ca)++(free_var_CAction cb)
free_var_CAction (CSPHide c cs) = (free_var_CAction c)
free_var_CAction (CSPRecursion nm c) = (free_var_CAction c)
free_var_CAction (CSPUnParAction lst c nm) = (free_var_CAction c) \\ (fvs free_var_ZGenFilt lst)
free_var_CAction (CSPRepSeq lst c) = (free_var_CAction c) \\ (fvs free_var_ZGenFilt lst)
free_var_CAction (CSPRepExtChoice lst c) = (free_var_CAction c) \\ (fvs free_var_ZGenFilt lst)
free_var_CAction (CSPRepIntChoice lst c) = (free_var_CAction c) \\ (fvs free_var_ZGenFilt lst)
free_var_CAction (CSPRepParalNS cs lst ns c) = (free_var_CAction c) \\ (fvs free_var_ZGenFilt lst)
free_var_CAction (CSPRepParal cs lst c) = (free_var_CAction c) \\ (fvs free_var_ZGenFilt lst)
free_var_CAction (CSPRepInterlNS lst ns c) = (free_var_CAction c) \\ (fvs free_var_ZGenFilt lst)
free_var_CAction (CSPRepInterl lst c) = (free_var_CAction c) \\ (fvs free_var_ZGenFilt lst)
free_var_CAction _ = []

free_var_ZGenFilt :: ZGenFilt -> [ZVar]
free_var_ZGenFilt (Choose v e) = [v]
free_var_ZGenFilt _ = []

free_var_comnd :: CCommand -> [ZVar]
free_var_comnd (CAssign v e) = v
free_var_comnd (CIf ga) = free_var_if ga
free_var_comnd (CVarDecl z c) = (free_var_CAction c) \\ (fvs free_var_ZGenFilt z)
free_var_comnd (CommandBrace z) = (free_var_ZPred z)
free_var_comnd (CommandBracket z) = (free_var_ZPred z)
free_var_comnd (CValDecl z c) = (free_var_CAction c) \\ (fvs free_var_ZGenFilt z)
free_var_comnd (CResDecl z c) = (free_var_CAction c) \\ (fvs free_var_ZGenFilt z)
free_var_comnd (CVResDecl z c) = (free_var_CAction c) \\ (fvs free_var_ZGenFilt z)
free_var_comnd _ = []
 
free_var_if :: CGActions -> [ZVar]
free_var_if (CircGAction p a) = (free_var_ZPred p)++(free_var_CAction a)
free_var_if (CircThenElse ga gb) = (free_var_if ga)++(free_var_if gb)
free_var_if (CircElse (CircusAction a)) = (free_var_CAction a)
free_var_if (CircElse (ParamActionDecl x (CircusAction a))) = (free_var_CAction a) \\ (fvs free_var_ZGenFilt x)


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

fvs :: (t -> [t1]) -> [t] -> [t1]
fvs f [] = []
fvs f (e:es)
 = f(e) ++ (fvs f (es))

free_var_ZExpr :: ZExpr -> [ZVar]
free_var_ZExpr(ZVar v) = [v]
free_var_ZExpr(ZInt c ) = []
free_var_ZExpr(ZTuple exls ) = fvs free_var_ZExpr exls
free_var_ZExpr(ZSetDisplay exls ) = fvs free_var_ZExpr exls
free_var_ZExpr(ZSeqDisplay exls ) = fvs free_var_ZExpr exls
free_var_ZExpr(ZCross exls ) = fvs free_var_ZExpr exls
free_var_ZExpr(ZPowerSet{baseset=b, is_non_empty=e, is_finite=fs}) = error "Don't know what free vars of ZPowerSet are right now. Check back later"
free_var_ZExpr(ZFuncSet{domset=d, ranset=r, is_function=f, is_total=t, is_onto=o, is_one2one=oo, is_sequence=s, is_non_empty=ne, is_finite=ff}) = error "Don't know what free vars of ZFree0 are right now. Check back later"
free_var_ZExpr(ZLambda [Choose v e] a) = (free_var_ZExpr a) \\ [v]
free_var_ZExpr(ZLambda _ a) = []
free_var_ZExpr(ZCall ex ex2) = free_var_ZExpr ex2 -- is this right??
free_var_ZExpr(ZELet ves pr) = ((free_var_ZExpr(pr)) \\ (map fst ves)) ++ fvs free_var_ZExpr (map snd ves)
-- free_var_ZExpr(ZIf_Then_Else zp ex ex1) -- = free_var_ZPred zp ++ free_var_ZExpr ex ++ free_var_ZExpr ex1
free_var_ZExpr(ZSelect ex zv) = free_var_ZExpr ex ++ [zv]
free_var_ZExpr _ = []



rename_vars_CAction :: [String] -> CAction -> CAction
rename_vars_CAction lst (CActionSchemaExpr zsexp) = (CActionSchemaExpr zsexp)
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
rename_vars_CAction lst x = x

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

rename_vars_CReplace :: t -> CReplace -> CReplace
rename_vars_CReplace lst (CRename zvarls1 zvarls) = (CRename zvarls1 zvarls)
rename_vars_CReplace lst (CRenameAssign zvarls1 zvarls) = (CRenameAssign zvarls1 zvarls)

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

rename_ZExpr :: [String] -> ZExpr -> ZExpr
rename_ZExpr lst (ZVar (va,x))
 = case (inListVar va lst) of
   True -> (ZVar ("v_"++va,x))
   False -> (ZVar (va,x))
rename_ZExpr lst (ZInt zi) = (ZInt zi)
rename_ZExpr lst (ZGiven gv) = (ZGiven gv)
rename_ZExpr lst (ZFree0 va) = (ZFree0 va)
rename_ZExpr lst (ZFree1 va xpr) = (ZFree1 va (rename_ZExpr lst xpr))
rename_ZExpr lst (ZTuple xprlst) = (ZTuple (map (rename_ZExpr lst) xprlst))
rename_ZExpr lst (ZBinding xs) = (ZBinding (bindingsVar lst xs))
rename_ZExpr lst (ZSetDisplay xprlst) = (ZSetDisplay (map (rename_ZExpr lst) xprlst))
rename_ZExpr lst (ZSeqDisplay xprlst) = (ZSeqDisplay (map (rename_ZExpr lst) xprlst))
rename_ZExpr lst (ZIntSet i1 i2) = (ZIntSet i1 i2)
rename_ZExpr lst (ZGenerator zrl xpr) = (ZGenerator zrl (rename_ZExpr lst xpr))
rename_ZExpr lst (ZCross xprlst) = (ZCross (map (rename_ZExpr lst) xprlst))
rename_ZExpr lst (ZFreeType va lst1) = (ZFreeType va lst1)
rename_ZExpr lst (ZPowerSet{baseset=xpr, is_non_empty=b1, is_finite=b2}) = (ZPowerSet{baseset=(rename_ZExpr lst xpr), is_non_empty=b1, is_finite=b2})
rename_ZExpr lst (ZFuncSet{ domset=expr1, ranset=expr2, is_function=b1, is_total=b2, is_onto=b3, is_one2one=b4, is_sequence=b5, is_non_empty=b6, is_finite=b7}) = (ZFuncSet{ domset=(rename_ZExpr lst expr1), ranset=(rename_ZExpr lst expr2), is_function=b1, is_total=b2, is_onto=b3, is_one2one=b4, is_sequence=b5, is_non_empty=b6, is_finite=b7})
rename_ZExpr lst (ZSetComp lst1 (Just xpr)) = (ZSetComp lst1 (Just (rename_ZExpr lst xpr)))
rename_ZExpr lst (ZSetComp lst1 Nothing) = (ZSetComp lst1 Nothing)
rename_ZExpr lst (ZLambda lst1 xpr) = (ZLambda lst1 (rename_ZExpr lst xpr))
rename_ZExpr lst (ZESchema zxp) = (ZESchema zxp)
rename_ZExpr lst (ZGivenSet gs) = (ZGivenSet gs)
rename_ZExpr lst (ZUniverse) = (ZUniverse)
rename_ZExpr lst (ZCall xpr1 xpr2) = (ZCall (rename_ZExpr lst xpr1) (rename_ZExpr lst xpr2))
rename_ZExpr lst (ZReln rl) = (ZReln rl)
rename_ZExpr lst (ZFunc1 f1) = (ZFunc1 f1)
rename_ZExpr lst (ZFunc2 f2) = (ZFunc2 f2)
rename_ZExpr lst (ZStrange st) = (ZStrange st)
rename_ZExpr lst (ZMu lst1 (Just xpr)) = (ZMu lst1 (Just (rename_ZExpr lst xpr)))
rename_ZExpr lst (ZELet lst1 xpr1) = (ZELet (bindingsVar lst lst1) (rename_ZExpr lst xpr1))
rename_ZExpr lst (ZIf_Then_Else zp xpr1 xpr2) = (ZIf_Then_Else zp (rename_ZExpr lst xpr1) (rename_ZExpr lst xpr2))
rename_ZExpr lst (ZSelect xpr va) = (ZSelect xpr va)
rename_ZExpr lst (ZTheta zs) = (ZTheta zs)

rename_ZPred :: [String] -> ZPred -> ZPred
rename_ZPred lst (ZFalse{reason=a}) = (ZFalse{reason=a})
rename_ZPred lst (ZTrue{reason=a}) = (ZTrue{reason=a})
rename_ZPred lst (ZAnd p1 p2) = (ZAnd (rename_ZPred lst p1) (rename_ZPred lst p2))
rename_ZPred lst (ZOr p1 p2) = (ZOr (rename_ZPred lst p1) (rename_ZPred lst p2))
rename_ZPred lst (ZImplies p1 p2) = (ZImplies (rename_ZPred lst p1) (rename_ZPred lst p2))
rename_ZPred lst (ZIff p1 p2) = (ZIff (rename_ZPred lst p1) (rename_ZPred lst p2))
rename_ZPred lst (ZNot p) = (ZNot (rename_ZPred lst p))
rename_ZPred lst (ZExists lst1 p) = (ZExists lst1 (rename_ZPred lst p))
rename_ZPred lst (ZExists_1 lst1 p) = (ZExists_1 lst1 (rename_ZPred lst p))
rename_ZPred lst (ZForall lst1 p) = (ZForall lst1 (rename_ZPred lst p))
rename_ZPred lst (ZPLet varxp p) = (ZPLet varxp (rename_ZPred lst p))
rename_ZPred lst (ZEqual xpr1 xpr2) = (ZEqual (rename_ZExpr lst xpr1) (rename_ZExpr lst xpr2))
rename_ZPred lst (ZMember xpr1 xpr2) = (ZMember (rename_ZExpr lst xpr1) (rename_ZExpr lst xpr2))
rename_ZPred lst (ZPre sp) = (ZPre sp)
rename_ZPred lst (ZPSchema sp) = (ZPSchema sp)

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

-- From Data.List
-- | The '\\' function is list difference ((non-associative).
-- In the result of @xs@ '\\' @ys@, the first occurrence of each element of
-- @ys@ in turn (if any) has been removed from @xs@.  Thus
--
-- > (xs ++ ys) \\ xs == ys.
--
-- It is a special case of 'deleteFirstsBy', which allows the programmer
-- to supply their own equality test.

(\\)                    :: (Eq a) => [a] -> [a] -> [a]
(\\)                    =  foldl (flip delete)


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


flip         :: (a -> b -> c) -> b -> a -> c
flip f x y   =  f y x


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


-- | The 'nubBy' function behaves just like 'nub', except it uses a
-- user-supplied equality predicate instead of the overloaded '=='
-- function.
nubBy                   :: (a -> a -> Bool) -> [a] -> [a]
nubBy eq []             =  []
nubBy eq (x:xs)         =  x : nubBy eq (filter (\ y -> not (eq x y)) xs)
nubBy eq l              = nubBy' l []
  where
    nubBy' [] _         = []
    nubBy' (y:ys) xs
       | elem_by eq y xs = nubBy' ys xs
       | otherwise       = y : nubBy' ys (y:xs)

-- Not exported:
-- Note that we keep the call to `eq` with arguments in the
-- same order as in the reference implementation
-- 'xs' is the list of things we've seen so far, 
-- 'y' is the potential new element
elem_by :: (a -> a -> Bool) -> a -> [a] -> Bool
elem_by _  _ []         =  False
elem_by eq y (x:xs)     =  y `eq` x || elem_by eq y xs
