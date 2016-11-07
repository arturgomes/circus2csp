\section{Misc functions -- File: DefSets.lhs}
Functions used for manipulating lists (Z Sets and sequences, as well as calculating the provisos from the Circus Refinement laws)

\ignore{
\begin{code}
module DefSets where
import Data.List
import AST
\end{code}
}

\subsection{Prototype of $wrtV(A)$, from D24.1.}
Prototype of $wrtV(A)$, from D24.1.
\begin{code}
-- TODO: Need to do it
getWrtV xs = []
\end{code}

\subsection{Bits for FreeVariables (FV(X))}
\subsection{Free Variables -- $FV(A)$. }
Need to know how to calculate for Actions.
\begin{code}
getFV xs = []
\end{code}


\begin{code}
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
  =  free_var_ZPred a ++ free_var_ZPred b
free_var_ZPred (ZIff a b)
  =  free_var_ZPred a ++ free_var_ZPred b
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
\end{code}

\begin{code}
fvs f [] = []
fvs f (e:es)
  = f(e) ++ (fvs f (es))
\end{code}
\subsection{Others -- No specific topic}

\begin{code}
subset xs ys = all (`elem` ys) xs
\end{code}

\begin{code}
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
\end{code}

\begin{code}
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
\end{code}
\begin{code}
free_var_ZGenFilt (Include s) = []
free_var_ZGenFilt (Choose v e) = [v]
free_var_ZGenFilt (Check p) = []
free_var_ZGenFilt (Evaluate v e1 e2) = []
\end{code}
\begin{code}
free_var_if (CircGAction p a)
  = (free_var_ZPred p)++(free_var_CAction a)
free_var_if (CircThenElse ga gb)
  = (free_var_if ga)++(free_var_if gb)
free_var_if (CircElse (CircusAction a))
  = (free_var_CAction a)
free_var_if (CircElse (ParamActionDecl x (CircusAction a)))
  = (free_var_CAction a) \\ (fvs free_var_ZGenFilt x)
\end{code}
\subsection{Expanding the main action}
\begin{code}      
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
\end{code}
\begin{code}
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
\end{code}

\begin{code}
get_if lst (CircGAction p a)
  = (CircGAction p (get_main_action lst a))
get_if lst (CircThenElse ga gb)
  = (CircThenElse (get_if lst ga) (get_if lst gb))
get_if lst (CircElse (CircusAction a))
  = (CircElse (CircusAction (get_main_action lst a)))
get_if lst (CircElse (ParamActionDecl x (CircusAction a)))
  = (CircElse (ParamActionDecl x (CircusAction (get_main_action lst a))))
\end{code}

\begin{code}
get_action _ [] = error "Action list is empty" 
get_action name [(CParAction n (CircusAction a))] 
  = case name == n of
      True -> a
      False -> error "Action not found"

get_action name ((CParAction n (CircusAction a)):xs)
  = case name == n of
      True -> a
      False -> get_action name xs
\end{code}

\begin{code}
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
\end{code}

\begin{code}
filter_state_comp :: [(ZName, ZVar, ZExpr)] -> [ZVar]
filter_state_comp [] = []
filter_state_comp [(_, v, _)] = [v]
filter_state_comp ((_, v, _):xs) = [v]++(filter_state_comp xs)
\end{code}

\begin{code}
map_mp f p1 [] = []
map_mp f p1 [x] = (f p1 x)
map_mp f p1 (x:xs) = (f p1 x)++(map_mp f p1 xs)
\end{code}