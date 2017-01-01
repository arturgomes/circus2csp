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
import OmegaDefs
-- import DefSets
-- import Data.List
-- import FormatterToCSP

omega_CAction :: [(ZName, ZVar, ZExpr)] -> CAction -> CAction
omega_CAction lst CSPSkip = CSPSkip
omega_CAction lst CSPStop = CSPStop
omega_CAction lst CSPChaos = CSPChaos
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
    True -> omega_CAction lst (rep_CSPRepSeq lst omega_CAction act xs)
    _  -> (CSPRepSeq [Choose (x,[]) (ZSeqDisplay xs)]
          (omega_CAction lst (CSPParAction act [ZVar (x1,[])])))
omega_CAction lst (CSPRepSeq [Choose (x,[]) v] act)
  = (CSPRepSeq [Choose (x,[]) v] (omega_CAction lst act))

omega_CAction lst (CSPRepExtChoice [Choose (x,[]) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1,[])]))
  = case x == x1 of
    True -> rep_CSPRepExtChoice lst omega_CAction act xs
    _  -> (CSPRepExtChoice [Choose (x,[]) (ZSeqDisplay xs)]
          (CSPParAction act [ZVar (x1,[])]))
omega_CAction lst (CSPRepExtChoice [Choose (x,[]) v] act)
  = (CSPRepExtChoice [Choose (x,[]) v] (omega_CAction lst act))

omega_CAction lst (CSPRepIntChoice [Choose (x,[]) (ZSeqDisplay xs)]
          (CSPParAction act [ZVar (x1,[])]))
  = case x == x1 of
    True -> rep_CSPRepIntChoice lst omega_CAction act xs
    _  -> (CSPRepIntChoice [Choose (x,[]) (ZSeqDisplay xs)]
          (CSPParAction act [ZVar (x1,[])]))
omega_CAction lst (CSPRepIntChoice [Choose (x,[]) v] act)
  = (CSPRepIntChoice [Choose (x,[]) v] (omega_CAction lst act))

omega_CAction lst (CSPRepParalNS (CSExpr cs) [Choose (x,[]) (ZSetDisplay lsx)]
          (NSExprParam ns [ZVar (x1,[])])
          (CSPParAction a [ZVar (x2,[])]))
  = case (x == x1) && (x == x2) of
    True -> rep_CSPRepParalNS lst omega_CAction a cs ns x lsx
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
    True -> rep_CSPRepInterlNS lst omega_CAction a ns x lsx
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
omega_CAction lst (CSPCommAction (ChanComm c [ChanInpPred x p]) a)
  = case not (member x (getWrtV a)) of
    True -> make_get_com lst lsx (rename_vars_CAction (map fst lsx) (CSPCommAction
             (ChanComm c [ChanInpPred x p])
                 (omega_prime_CAction lst a)))
    _  -> (CSPCommAction (ChanComm c [ChanInpPred x p]) a)
  where lsx = free_var_ZPred(p)

omega_CAction lst (CSPCommAction (ChanComm c ((ChanDotExp e):xs)) a)
  = make_get_com lst lxs (rename_vars_CAction (map fst lxs) (CSPCommAction (ChanComm c ((ChanDotExp e):xs)) (omega_prime_CAction lst a)))
  where lxs = (get_chan_param ((ChanDotExp e):xs)) `intersect` (filter_state_comp lst)

omega_CAction lst (CActionCommand (CAssign varls valls))
  = make_get_com lst varls (rename_vars_CAction (map fst (filter_state_comp lst)) (make_set_com lst omega_CAction varls valls CSPSkip))


omega_CAction lst (CActionCommand (CIf (CircThenElse gl glx)))
  = make_get_com lst lsx (rename_vars_CAction (map fst lsx) (CActionCommand (CIf (mk_guard_pair lst omega_prime_CAction guard_pair))))
  where
   guard_pair = get_guard_pair (CircThenElse gl glx)
   lsx = concat (map free_var_ZPred (map fst guard_pair))

omega_CAction lst (CSPExtChoice ca cb)
  = make_get_com lst lsx (rename_vars_CAction (map fst lsx) (CSPExtChoice (omega_prime_CAction lst ca) (omega_prime_CAction lst cb)))
   where
    lsx = remdups ((free_var_CAction (CSPExtChoice ca cb)) `intersect` (filter_state_comp lst))
omega_CAction lst (CSPGuard g a) 
  = make_get_com lst lxs (rename_vars_CAction (map fst lxs) (CSPGuard (rename_ZPred (map fst lxs) g) (omega_prime_CAction lst a))) 
    where lxs = remdups (free_var_ZPred(g) `intersect` (filter_state_comp lst))

-- Omega Prime

omega_prime_CAction :: [(ZName, ZVar, ZExpr)] -> CAction -> CAction
omega_prime_CAction lst CSPSkip = CSPSkip
omega_prime_CAction lst CSPChaos = CSPChaos
omega_prime_CAction lst CSPStop = CSPStop
omega_prime_CAction lst (CActionCommand (CAssign varls valls)) = (make_set_com lst omega_CAction varls valls CSPSkip)
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
omega_prime_CAction lst (CSPSeq ca cb) = (CSPSeq (omega_prime_CAction lst ca) (omega_prime_CAction lst cb))

omega_prime_CAction lst (CActionCommand (CIf (CircThenElse gl glx)))
  = (CActionCommand (CIf (mk_guard_pair lst omega_prime_CAction guard_pair)))
  where
   guard_pair = get_guard_pair (CircThenElse gl glx)

omega_prime_CAction lst (CSPRepInterlNS [Choose (x,[]) (ZSetDisplay lsx)]
          (NSExprParam ns [ZVar (x1,[])])
          (CSPParAction a [ZVar (x2,[])]))
  = case (x == x1) && (x == x2) of
    True -> rep_CSPRepInterlNS lst omega_prime_CAction a ns x lsx
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
    True -> rep_CSPRepParalNS lst omega_prime_CAction a cs ns x lsx
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
    True -> omega_prime_CAction lst (rep_CSPRepSeq lst omega_prime_CAction act xs)
    _  -> (CSPRepSeq [Choose (x,[]) (ZSeqDisplay xs)]
          (omega_prime_CAction lst (CSPParAction act [ZVar (x1,[])])))
omega_prime_CAction lst (CSPRepSeq [Choose (x,[]) v] act) = (CSPRepSeq [Choose (x,[]) v] (omega_prime_CAction lst act))
omega_prime_CAction lst (CSPRepExtChoice [Choose (x,[]) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1,[])]))
  = case x == x1 of
    True -> rep_CSPRepExtChoice lst omega_prime_CAction act xs
    _  -> (CSPRepExtChoice [Choose (x,[]) (ZSeqDisplay xs)]
          (CSPParAction act [ZVar (x1,[])]))

omega_prime_CAction lst (CSPRepIntChoice [Choose (x,[]) (ZSeqDisplay xs)]
          (CSPParAction act [ZVar (x1,[])]))
  = case x == x1 of
    True -> rep_CSPRepIntChoice lst omega_prime_CAction act xs
    _  -> (CSPRepIntChoice [Choose (x,[]) (ZSeqDisplay xs)]
          (CSPParAction act [ZVar (x1,[])]))
omega_prime_CAction lst (CSPRepIntChoice [Choose (x,[]) v] act) = (CSPRepIntChoice [Choose (x,[]) v] (omega_prime_CAction lst act))


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
free_var_CAction (CSPUnParAction lst c nm) =setminus (free_var_CAction c) (fvs free_var_ZGenFilt lst)
free_var_CAction (CSPRepSeq lst c) = setminus (free_var_CAction c) (fvs free_var_ZGenFilt lst)
free_var_CAction (CSPRepExtChoice lst c) = setminus(free_var_CAction c) (fvs free_var_ZGenFilt lst)
free_var_CAction (CSPRepIntChoice lst c) = setminus(free_var_CAction c) (fvs free_var_ZGenFilt lst)
free_var_CAction (CSPRepParalNS cs lst ns c) = setminus (free_var_CAction c) (fvs free_var_ZGenFilt lst)
free_var_CAction (CSPRepParal cs lst c) = setminus (free_var_CAction c) (fvs free_var_ZGenFilt lst)
free_var_CAction (CSPRepInterlNS lst ns c) = setminus (free_var_CAction c) (fvs free_var_ZGenFilt lst)
free_var_CAction (CSPRepInterl lst c) = setminus (free_var_CAction c) (fvs free_var_ZGenFilt lst)
free_var_CAction _ = []


free_var_comnd :: CCommand -> [ZVar]
free_var_comnd (CAssign v e) = v
free_var_comnd (CIf ga) = free_var_if ga
free_var_comnd (CVarDecl z c) = setminus (free_var_CAction c) (fvs free_var_ZGenFilt z)
free_var_comnd (CommandBrace z) = (free_var_ZPred z)
free_var_comnd (CommandBracket z) = (free_var_ZPred z)
free_var_comnd (CValDecl z c) = setminus (free_var_CAction c) (fvs free_var_ZGenFilt z)
free_var_comnd (CResDecl z c) = setminus (free_var_CAction c) (fvs free_var_ZGenFilt z)
free_var_comnd (CVResDecl z c) = setminus (free_var_CAction c) (fvs free_var_ZGenFilt z)
free_var_comnd _ = []

free_var_if :: CGActions -> [ZVar]
free_var_if (CircGAction p a) = (free_var_ZPred p)++(free_var_CAction a)
free_var_if (CircThenElse ga gb) = (free_var_if ga)++(free_var_if gb)
free_var_if (CircElse (CircusAction a)) = (free_var_CAction a)
free_var_if (CircElse (ParamActionDecl x (CircusAction a))) = setminus (free_var_CAction a) (fvs free_var_ZGenFilt x)
