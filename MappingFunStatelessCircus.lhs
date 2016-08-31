\section{Mapping Functions - Stateless Circus}

Mapping Functions - Stateless Circus
\ignore{
\begin{code}
module MappingFunStatelessCircus
where
import AST
--import CRL
import FormatterToCSP
import DefSets

showexpr = zexpr_string (pinfo_extz 80)
\end{code}
}
\subsection{Stateless Circus - Actions}

\begin{code}
omega_CActions :: CAction -> CAction
omega_CActions CSPSkip = CSPSkip
omega_CActions CSPStop = CSPStop
omega_CActions CSPChaos = CSPChaos


omega_CActions (CSPCommAction (ChanComm c [ChanDotExp e]) a)
  = make_get_com lxs (CSPCommAction (ChanComm c [ChanDotExp e]) (omega_prime_CActions a))
  where lxs = variablesMentionedExpIn(e)

omega_CActions (CSPCommAction (ChanComm c [ChanOutExp e]) a)
  = omega_CActions (CSPCommAction (ChanComm c [ChanDotExp e]) a)

omega_CActions (CSPGuard g a)
  = make_get_com lxs (CSPGuard g (omega_prime_CActions a))
  where lxs = variablesMentionedPredIn(g)

omega_CActions (CSPCommAction (ChanComm c [ChanInpPred x p]) a)
  = case notinSet x (getWrtV(a)) of
      True -> make_get_com lsx (CSPCommAction (ChanComm c [ChanInpPred x p]) (omega_prime_CActions a))
      _    -> (CSPCommAction (ChanComm c [ChanInpPred x p]) a)
  where lsx = variablesMentionedExpIn(p)

omega_CActions (CSPCommAction x c)
  = (CSPCommAction x (omega_CActions c))

omega_CActions (CSPSeq ca cb)
  = (CSPSeq (omega_CActions ca) (omega_CActions cb))

omega_CActions (CSPUnParAction [Choose (x,[]) t] (CSPParAction a [ZVar (x1,[])]) e)
  = case x == x1 of
      True -> (CSPRenAction x [CRename (e,[]) (x,[])])
      _    -> (CSPUnParAction [Choose (x,[]) t] (CSPParAction a [ZVar (x1,[])]) e)
-- omega_CActions (CSPExtChoice ca cb) = (CSPExtChoice (omega_CActions ca) (omega_CActions cb))




omega_CActions x = (CSPHide (CSPNSParal NSExpEmpty memi NSExpEmpty (CSPNSParal NSExpEmpty cs NSExpEmpty (CSPHide (CSPNSParal NSExpEmpty memi NSExpEmpty (CSPSeq a1 (CSPCommAction (ChanComm "terminate" []) CSPSkip)) (CSPParAction "MemoryMerge" [ZSetDisplay (make_maps_to lxs),ZVar ("LEFT",[])])) memi) (CSPHide (CSPNSParal NSExpEmpty memi NSExpEmpty (CSPSeq a2 (CSPCommAction (ChanComm "terminate" []) CSPSkip)) (CSPParAction "MemoryMerge" [ZSetDisplay (make_maps_to lxs),ZVar ("RIGHT",[])])) memi)) (CActionName "Merge")) (CChanSet ["mleft","mright"]))

omega_CActions (CSPIntChoice ca cb)
  = (CSPIntChoice (omega_CActions ca) (omega_CActions cb))
omega_CActions (CSPNSParal a b c ca cb)
  = (CSPNSParal a b c (omega_CActions ca) (omega_CActions cb))
omega_CActions (CSPParal x ca cb)
  = (CSPParal x (omega_CActions ca) (omega_CActions cb))
omega_CActions (CSPNSInter x y ca cb)
  = (CSPNSInter x y (omega_CActions ca) (omega_CActions cb))
omega_CActions (CSPInterleave ca cb)
  = (CSPInterleave (omega_CActions ca) (omega_CActions cb))

omega_CActions (CSPHide c y) = (CSPHide (omega_CActions c) y)

omega_CActions (CSPRecursion x c) = (CSPRecursion x (omega_CActions c))

omega_CActions (CSPRepSeq [Choose (x,[]) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1,[])]))
  = case x == x1 of
      True -> omega_CActions (rep_CSPRepSeq act xs)
      _    -> (CSPRepSeq [Choose (x,[]) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1,[])]))

omega_CActions (CSPRepExtChoice [Choose (x,[]) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1,[])]))
  = case x == x1 of
      True -> rep_CSPRepExtChoice act xs
      _    -> (CSPRepExtChoice [Choose (x,[]) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1,[])]))
omega_CActions (CSPRepIntChoice [Choose (x,[]) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1,[])]))
  = case x == x1 of
      True -> rep_CSPRepIntChoice act xs
      _    -> (CSPRepIntChoice [Choose (x,[]) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1,[])]))

omega_CActions (CSPRepParalNS (CSExpr cs) [Choose (x,[]) (ZSetDisplay lsx)] (NSExprParam ns [ZVar (x1,[])]) (CSPParAction a [ZVar (x2,[])]))
  = case (x == x1) && (x == x2) of
      True -> rep_CSPRepParalNS a cs ns x lsx
      _    -> (CSPRepParalNS (CSExpr cs) [Choose (x,[]) (ZSetDisplay lsx)] (NSExprParam ns [ZVar (x1,[])]) (CSPParAction a [ZVar (x2,[])]))

omega_CActions (CSPRepParal a b c)
  = (CSPRepParal a b (omega_CActions c))

omega_CActions (CSPRepInterlNS [Choose (x,[]) (ZSetDisplay lsx)] (NSExprParam ns [ZVar (x1,[])]) (CSPParAction a [ZVar (x2,[])]))
  = case (x == x1) && (x == x2) of
      True -> rep_CSPRepInterlNS a ns x lsx
      _    -> (CSPRepInterlNS [Choose (x,[]) (ZSetDisplay lsx)] (NSExprParam ns [ZVar (x1,[])]) (CSPParAction a [ZVar (x2,[])]))

omega_CActions (CSPRepInterl a c)
  = (CSPRepInterl a (omega_CActions c))

omega_CActions  _ = undefined
\end{code}

\begin{code}
omega_prime_CActions a = undefined
\end{code}

Function used to propagate $CSPRepSeq$ actions

\begin{code}
rep_CSPRepSeq :: ZName -> [ZExpr] -> CAction
rep_CSPRepSeq a [x] = CSPParAction a [x]
rep_CSPRepSeq a (x:xs) = CSPSeq (CSPParAction a [x]) (rep_CSPRepSeq a xs)
\end{code}

Function used to propagate $CSPRepIntChoice$ actions

\begin{code}
rep_CSPRepIntChoice :: ZName -> [ZExpr] -> CAction
rep_CSPRepIntChoice a [x] = (CSPParAction a [x])
rep_CSPRepIntChoice a (x:xs) = CSPIntChoice (CSPParAction a [x]) (rep_CSPRepIntChoice a xs)
\end{code}

Function used to propagate $CSPRepExtChoice$ actions

\begin{code}
rep_CSPRepExtChoice :: ZName -> [ZExpr] -> CAction
rep_CSPRepExtChoice a [x] = (CSPParAction a [x])
rep_CSPRepExtChoice a (x:xs) = CSPExtChoice (CSPParAction a [x]) (rep_CSPRepExtChoice a xs)
\end{code}

Function used to propagate $CSPRepInterNS$ actions

\begin{code}
rep_CSPRepParalNS :: ZName -> ZName -> ZName -> String -> [ZExpr] -> CAction
rep_CSPRepParalNS a _ _ _ [x] = (CSPParAction a [x])
rep_CSPRepParalNS a cs ns y (x:xs) = (CSPNSParal (NSExprParam ns [x]) (CSExpr cs) (NSBigUnion (ZSetComp [Choose (y,[]) (ZSetDisplay xs)] (Just (ZCall (ZVar (ns,[])) (ZVar (y,[])))) ) ) (CSPParAction a [x]) (rep_CSPRepParalNS a cs ns y xs) )
\end{code}

Function used to propagate $CSPRepInterNS$ actions

\begin{code}
rep_CSPRepInterlNS :: ZName -> ZName -> String -> [ZExpr] -> CAction
rep_CSPRepInterlNS a _ _ [x] = (CSPParAction a [x])
rep_CSPRepInterlNS a ns y (x:xs) = (CSPNSInter (NSExprParam ns [x]) (NSBigUnion (ZSetComp [Choose (y,[]) (ZSetDisplay xs)] (Just (ZCall (ZVar (ns,[])) (ZVar (y,[])))) ) ) (CSPParAction a [x]) (rep_CSPRepInterlNS a ns y xs) )
\end{code}

Auxiliary function to propagate $get$ communication through the variables and local variables of an action.

\begin{code}
make_get_com :: [ZVar] -> CAction -> CAction
make_get_com [(x,[])] c
  = (CSPCommAction (ChanComm "get" [ChanDotExp (ZVar (x,[])),ChanInp ("v"++x)]) c)
make_get_com ((x,[]):xs) c
  = (CSPCommAction (ChanComm "get" [ChanDotExp (ZVar (x,[])),ChanInp ("v"++x)]) (make_get_com xs c))
\end{code}

\begin{code}
make_v_chan :: [ZVar] -> [ZExpr]
make_v_chan [(x,[])] = [ZVar (("v"++x),[])]
make_v_chan ((x,[]):xs) = ((ZVar (("v"++x),[])):(make_v_chan xs))
\end{code}

\begin{code}
variablesMentionedExpIn :: ZExpr -> [ZVar]
variablesMentionedExpIn c = free_var_ZExpr c
\end{code}

\begin{code}
variablesMentionedPredIn :: ZPred -> [ZVar]
variablesMentionedPredIn c = free_var_ZPred c
\end{code}

\begin{code}
make_maps_to [ZVar (x,[])] = [ZCall (ZVar ("\\mapsto",[])) (ZTuple [ZVar (x,[]),ZVar ("v"++x,[])])]
make_maps_to ((ZVar (x,[])):xs) = (ZCall (ZVar ("\\mapsto",[])) (ZTuple [ZVar (x,[]),ZVar ("v"++x,[])])):(make_maps_to xs)
\end{code}


\subsection{Adding permanent bits of the new \Circus specification ($MemoryMerge$, $MRG$, etc)}

