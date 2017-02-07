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

omega_CommCAction :: (CAction -> CAction) -> (CAction -> CAction) -> Comm -> CAction -> CAction
omega_CommCAction f s (ChanComm c []) a = (CSPCommAction (ChanComm c []) (f a))
omega_CommCAction f s (ChanComm c ((ChanDotExp e):xs)) a 
  = make_get_com lxs (rename_vars_CAction (CSPCommAction (ChanComm c ((ChanDotExp e):xs)) (s a))) 
    where lxs = concat (map get_ZVar_st (free_var_ZExpr e))
omega_CommCAction f s (ChanComm c ((ChanOutExp e):xs)) a = f (CSPCommAction (ChanComm c ((ChanDotExp e):xs)) a)
omega_CommCAction f s (ChanComm c [ChanInpPred x p]) a 
  = case not (member x (getWrtV(a))) of 
      True -> make_get_com lsx (rename_vars_CAction (CSPCommAction (ChanComm c [ChanInpPred x p]) (f a))) 
      _  -> (CSPCommAction (ChanComm c [ChanInpPred x p]) a) 
      where lsx = concat (map get_ZVar_st (free_var_ZPred p))

omega_CCommandCAction :: (CAction -> CAction) -> (CAction -> CAction) -> Comm -> CAction -> CAction
omega_CCommandCAction f s (CAssign varls valls) = make_get_com (map fst varls) (rename_vars_CAction (make_set_com f varls valls CSPSkip))
omega_CCommandCAction f s (CIf (CircGAction g a))
  = make_get_com lsx (rename_vars_CAction  (CActionCommand (CIf (CircGAction g (s a))))) 
  where lsx = (map fst (remdups  (free_var_ZPred g)))
omega_CCommandCAction f s (CIf (CircThenElse gl glx)) 
  = make_get_com lsx (rename_vars_CAction (CActionCommand (CIf (mk_guard_pair s guard_pair))))
  where
   guard_pair = get_guard_pair (CircThenElse gl glx)
   lsx = map fst (remdups (concat (map free_var_ZPred (map fst guard_pair))))

omega_CCommandCAction f s (CommandBrace g) = f (CActionCommand (CPrefix g (ZTrue {reason = []})))
omega_CCommandCAction f s (CommandBracket g) = f (CActionCommand (CPrefix1 g))

omega_CAction :: CAction -> CAction
omega_CAction CSPSkip = CSPSkip
omega_CAction CSPStop = CSPStop
omega_CAction CSPChaos = CSPChaos

omega_CAction (CSPCommAction c a) = omega_CommCAction omega_CAction omega_prime_CAction c a
omega_CAction (CActionCommand x) = omega_CCommandCAction omega_CAction omega_prime_CAction x
omega_CAction (CSPGuard g a) 
  = make_get_com lxs (rename_vars_CAction (CSPGuard (rename_ZPred g) (omega_prime_CAction a))) 
  where lxs = concat (map get_ZVar_st (free_var_ZPred g))
omega_CAction (CSPSeq ca cb) = (CSPSeq (omega_CAction ca) (omega_CAction cb))
omega_CAction (CSPIntChoice ca cb) = (CSPIntChoice (omega_CAction ca) (omega_CAction cb))
omega_CAction (CSPExtChoice ca cb) 
  = make_get_com lsx (rename_vars_CAction (CSPExtChoice (omega_prime_CAction ca) (omega_prime_CAction cb))) 
  where lsx = (map fst (remdups (free_var_CAction (CSPExtChoice ca cb))))

omega_CAction (CSPNSParal ns1 cs ns2 a1 a2)
  = make_get_com lsx (rename_vars_CAction (CSPHide
   (CSPNSParal NSExpEmpty (CSExpr "MEMi") NSExpEmpty
     (CSPNSParal NSExpEmpty cs NSExpEmpty
      (CSPHide
       (CSPNSParal NSExpEmpty (CSExpr "MEMi") NSExpEmpty
        (CSPSeq a1 (CSPCommAction (ChanComm "terminate" []) CSPSkip))
        (CSPParAction "MemoryMerge"
         [ZSetDisplay [],
                ZVar ("LEFT",[])]))
       (CSExpr "MEMi"))
      (CSPHide
       (CSPNSParal NSExpEmpty (CSExpr "MEMi") NSExpEmpty
        (CSPSeq a2 (CSPCommAction (ChanComm "terminate" []) CSPSkip))
        (CSPParAction "MemoryMerge"
         [ZSetDisplay [],
                ZVar ("RIGHT",[])]))
       (CSExpr "MEMi")))
      (CActionName "Merge"))
      (CChanSet ["mleft","mright"])))
   where
    lsx = (map fst (remdups  (free_var_CAction a1))) `union` (map fst (remdups  (free_var_CAction a2)))


omega_CAction (CSPHide a cs) = (CSPHide (omega_CAction a) cs)
omega_CAction (CSPRecursion x c) = (CSPRecursion x (omega_CAction c))
omega_CAction (CSPRenAction a (CRenameAssign left right)) = (CSPRenAction a (CRename right left))

omega_CAction (CSPRepSeq [Choose (x,[]) v] act)
  = (CSPRepSeq [Choose (x,[]) v] (omega_CAction act))
omega_CAction (CSPRepExtChoice [Choose (x,[]) v] act)
  = (CSPRepExtChoice [Choose (x,[]) v] (omega_CAction act))
omega_CAction (CSPRepIntChoice [Choose (x,[]) v] act)
  = (CSPRepIntChoice [Choose (x,[]) v] (omega_CAction act))
omega_CAction (CSPRepParalNS (CSExpr cs) [Choose (x,[]) (ZSetDisplay lsx)]
          (NSExprParam ns [ZVar (x1,[])]) act)
  = (CSPRepParalNS (CSExpr cs) [Choose (x,[]) (ZSetDisplay lsx)]
          (NSExprParam ns [ZVar (x1,[])]) (omega_CAction act))
omega_CAction (CSPRepInterlNS [Choose (x,[]) (ZSetDisplay lsx)]
          (NSExprParam ns [ZVar (x1,[])]) act)
  = (CSPRepInterlNS [Choose (x,[]) (ZSetDisplay lsx)]
          (NSExprParam ns [ZVar (x1,[])]) (omega_CAction act))
-- From now on, I'll be restricting the ZSetDisplay lsx set to ZVar and ZInt - Hope it help me with Isabelle
omega_CAction (CSPRepSeq [Choose (x,[]) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1,[])]))
  = case x == x1 && (is_Var_or_Int xs) of
    True -> omega_CAction (rep_CSPRepSeq act xs)
    _  -> (CSPRepSeq [Choose (x,[]) (ZSeqDisplay xs)]
          (CSPParAction act [ZVar (x1,[])]))

omega_CAction (CSPRepExtChoice [Choose (x,[]) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1,[])]))
  = case x == x1 && (is_Var_or_Int xs) of
    True -> omega_CAction (rep_CSPRepExtChoice act xs)
    _  -> (CSPRepExtChoice [Choose (x,[]) (ZSeqDisplay xs)]
          (CSPParAction act [ZVar (x1,[])]))

omega_CAction (CSPRepIntChoice [Choose (x,[]) (ZSeqDisplay xs)]
          (CSPParAction act [ZVar (x1,[])]))
  = case x == x1 && (is_Var_or_Int xs) of
    True -> omega_CAction(rep_CSPRepIntChoice act xs)
    _  -> (CSPRepIntChoice [Choose (x,[]) (ZSeqDisplay xs)]
          (CSPParAction act [ZVar (x1,[])]))

omega_CAction (CSPRepParalNS (CSExpr cs) [Choose (x,[]) (ZSetDisplay lsx)]
          (NSExprParam ns [ZVar (x1,[])])
          (CSPParAction a [ZVar (x2,[])]))
  = case (x == x1) && (x == x2) && (is_Var_or_Int lsx) of
    True -> omega_CAction (rep_CSPRepParalNS a cs ns x lsx)
    _  -> (CSPRepParalNS (CSExpr cs) [Choose (x,[]) (ZSetDisplay lsx)]
          (NSExprParam ns [ZVar (x1,[])])
          (CSPParAction a [ZVar (x2,[])]))
omega_CAction (CSPRepInterlNS [Choose (x,[]) (ZSetDisplay lsx)]
          (NSExprParam ns [ZVar (x1,[])])
          (CSPParAction a [ZVar (x2,[])]))
  = case (x == x1) && (x == x2) && (is_Var_or_Int lsx) of
    True -> omega_CAction (rep_CSPRepInterlNS a ns x lsx)
    _  ->  (CSPRepInterlNS [Choose (x,[]) (ZSetDisplay lsx)]
          (NSExprParam ns [ZVar (x1,[])])
          (CSPParAction a [ZVar (x2,[])]))
omega_CAction x = x

-- Omega Prime
omega_prime_CAction :: CAction -> CAction

omega_prime_CAction (CSPCommAction (ChanComm c []) a) = (CSPCommAction (ChanComm c []) (omega_prime_CAction a))

omega_prime_CAction (CSPCommAction (ChanComm c [ChanDotExp e]) a) = (CSPCommAction (ChanComm c [ChanDotExp (rename_ZExpr e)]) (omega_prime_CAction a))

omega_prime_CAction (CSPSeq ca cb) = (CSPSeq (omega_prime_CAction ca) (omega_CAction cb))

omega_prime_CAction x = omega_CAction x

