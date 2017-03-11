\section{Misc functions -- File: DefSets.lhs}
Functions used for manipulating lists (Z Sets and sequences, as well as calculating the provisos from the Circus Refinement laws)

\ignore{
\begin{code}
module OmegaDefs where
import Data.Char
-- import Data.Text hiding (map,concat,all,take)
import Subs
import AST
import Errors
\end{code}
}
\begin{code}
join_name n v = n ++ "_" ++ v
\end{code}




Auxiliary function to propagate $get$ communication through the variables and local variables of an action.
\begin{circus}
make\_get\_com\ (v_0,\ldots,v_n,l_0,\ldots,l_m)~A \defs
\\\t2 get.v_0?vv_0 \then \ldots \then get.v_n?vv_n \then
\\\t2 get.l_0?vl_0 \then \ldots \then get.l_m?vl_m \then A
\end{circus}
\begin{code}
make_get_com :: [ZName] -> CAction -> CAction
make_get_com [x] c
  = (CSPCommAction (ChanComm "mget"
    [ChanDotExp (ZVar (x,[])),ChanInp ("v_"++x)]) c)
make_get_com (x:xs) c
  = (CSPCommAction (ChanComm "mget"
    [ChanDotExp (ZVar (x,[])),ChanInp ("v_"++x)]) (make_get_com xs c))
make_get_com x c = c    
\end{code}

\begin{code}
make_set_com :: (CAction -> CAction) -> [ZVar] -> [ZExpr] -> CAction -> CAction
make_set_com f [(x,_)] [y] c
  = (CSPCommAction (ChanComm "mset"
    [ChanDotExp (ZVar (x,[])),ChanDotExp y]) (f c))
make_set_com f ((x,_):xs) (y:ys) c
  = (CSPCommAction (ChanComm "mset"
     [ChanDotExp (ZVar (x,[])),ChanDotExp y]) (make_set_com f xs ys c))
\end{code}

The function $get\_guard\_pair$ transform $CircGAction$ constructs into a list of tuples $(ZPred, CAction)$
\begin{code}
get_guard_pair :: CGActions -> [(ZPred, CAction)]
get_guard_pair (CircGAction g2 a2)
  = [(g2,a2)]
get_guard_pair (CircThenElse (CircGAction g2 a2) glx)
  = ((g2,a2):(get_guard_pair glx))
\end{code}
The function $rename\_guard\_pair$ will rename the guards to $v_$ prefix of free variables.

\begin{code}
rename_guard_pair :: [ZName] -> [(ZPred, CAction)] -> [(ZPred, CAction)]
rename_guard_pair sub [(a,b)] 
  = [((substitute (mk_sub_list sub) (free_vars a) a),b)]
rename_guard_pair sub ((a,b):xs) = [((substitute (mk_sub_list sub) (free_vars a) a),b)]++(rename_guard_pair sub xs)
\end{code}

The function $mk\_guard\_pair$ transforms a list of tuples $(ZPred, CAction)$ and produces $CircThenElse$ pieces according to the size of the list.
\begin{code}
mk_guard_pair :: (CAction -> CAction) -> [(ZPred, CAction)] -> CGActions
mk_guard_pair f [(g,a)] = (CircGAction g (f a))
mk_guard_pair f ((g,a):ls) = (CircThenElse (CircGAction g (f a)) (mk_guard_pair f ls))
\end{code}
The function $mk\_sub\_list$ will make a list of substitution variables to $v_$ prefix.
\begin{code}
mk_sub_list :: [ZName] -> [((ZName,[t0]),ZExpr)]
mk_sub_list [x] = [((x,[]),(ZVar ("v_"++x,[])))]
mk_sub_list (x:xs) = [((x,[]),(ZVar ("v_"++x,[])))]++(mk_sub_list xs)
\end{code}
\subsection{Prototype of $wrtV(A)$, from D24.1.}
Prototype of $wrtV(A)$, from D24.1.
\begin{code}
-- TODO: Need to do it
getWrtV xs = []
\end{code}



\begin{code}
rename_ZPred (ZFalse{reason=a})
 = (ZFalse{reason=a})
rename_ZPred (ZTrue{reason=a})
 = (ZTrue{reason=a})
rename_ZPred (ZAnd p1 p2)
 = (ZAnd (rename_ZPred p1) (rename_ZPred p2))
rename_ZPred (ZOr p1 p2)
 = (ZOr (rename_ZPred p1) (rename_ZPred p2))
rename_ZPred (ZImplies p1 p2)
 = (ZImplies (rename_ZPred p1) (rename_ZPred p2))
rename_ZPred (ZIff p1 p2)
 = (ZIff (rename_ZPred p1) (rename_ZPred p2))
rename_ZPred (ZNot p)
 = (ZNot (rename_ZPred p))
rename_ZPred (ZExists lst1 p)
 = (ZExists lst1 (rename_ZPred p))
rename_ZPred (ZExists_1 lst1 p)
 = (ZExists_1 lst1 (rename_ZPred p))
rename_ZPred (ZForall lst1 p)
 = (ZForall lst1 (rename_ZPred p))
rename_ZPred (ZPLet varxp p)
 = (ZPLet varxp (rename_ZPred p))
rename_ZPred (ZEqual xpr1 xpr2)
 = (ZEqual (rename_ZExpr xpr1) (rename_ZExpr xpr2))
rename_ZPred (ZMember xpr1 xpr2)
 = (ZMember (rename_ZExpr xpr1) (rename_ZExpr xpr2))
rename_ZPred (ZPre sp)
 = (ZPre sp)
rename_ZPred (ZPSchema sp)
 = (ZPSchema sp)
\end{code}


\begin{code}
rename_vars_CReplace (CRename zvarls1 zvarls)
 = (CRename zvarls1 zvarls)
rename_vars_CReplace (CRenameAssign zvarls1 zvarls)
 = (CRenameAssign zvarls1 zvarls)
\end{code}


\begin{code}
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

\end{code}


\subsection{Auxiliary functions for the definition of $\Omega_{A}$}
The use of Isabelle/HOL made me rethink of what was being produced
with the functions below. First, a $CSPParAction$, $A(x)$, does not need to call $omega\_CAction$ again, as it does not change anything, so I removed it when a list of parameters $x$ is a singleton. Then, I realised that I don't need to call $omega\_CAction$ at all in any of the $rep\_$ functions as that function is called for the result of any $rep\_$ function. Finally, I don't need to carry the triple with the state variable names/types. 

Function used to propagate $CSPRepSeq$ actions

\begin{code}
rep_CSPRepSeq :: ZName -> [ZExpr] -> CAction
rep_CSPRepSeq a [x]
  = (CSPParAction a [x])
rep_CSPRepSeq a (x:xs)
  = CSPSeq (CSPParAction a [x]) (rep_CSPRepSeq a xs)
\end{code}

Function used to propagate $CSPRepIntChoice$ actions

\begin{code}
rep_CSPRepIntChoice :: ZName -> [ZExpr] -> CAction
rep_CSPRepIntChoice a [x]
  = (CSPParAction a [x])
rep_CSPRepIntChoice a (x:xs)
  = CSPIntChoice (CSPParAction a [x]) (rep_CSPRepIntChoice a xs)
\end{code}

Function used to propagate $CSPRepExtChoice$ actions

\begin{code}
rep_CSPRepExtChoice :: ZName -> [ZExpr] -> CAction
rep_CSPRepExtChoice a [x]
  = (CSPParAction a [x])
rep_CSPRepExtChoice a (x:xs)
  = CSPExtChoice (CSPParAction a [x]) (rep_CSPRepExtChoice a xs)
\end{code}

Function used to propagate $CSPRepInterNS$ actions

\begin{code}
rep_CSPRepParalNS :: ZName -> ZName -> ZName -> String -> [ZExpr] -> CAction
rep_CSPRepParalNS a _ _ _ [x]
  = (CSPParAction a [x])
rep_CSPRepParalNS a cs ns y (x:xs)
  = (CSPNSParal (NSExprParam ns [x]) (CSExpr cs)
    (NSBigUnion (ZSetComp
           [Choose (y,[]) (ZSetDisplay xs)]
           (Just (ZCall (ZVar (ns,[])) (ZVar (y,[])))) ) )
     (CSPParAction a [x]) (rep_CSPRepParalNS a cs ns y xs) )
\end{code}

Function used to propagate $CSPRepInterNS$ actions

\begin{code}
rep_CSPRepInterlNS :: ZName -> ZName -> String -> [ZExpr] -> CAction
rep_CSPRepInterlNS a _ _ [x]
  = (CSPParAction a [x])
rep_CSPRepInterlNS a ns y (x:xs)
  = (CSPNSInter (NSExprParam ns [x])
    (NSBigUnion (ZSetComp
           [Choose (y,[]) (ZSetDisplay xs)]
           (Just (ZCall (ZVar (ns,[])) (ZVar (y,[])))) ) )
     (CSPParAction a [x]) (rep_CSPRepInterlNS a ns y xs) )
\end{code}

\begin{code}
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


isPrefixOf [] _ = True
isPrefixOf _ [] = False
isPrefixOf (x : xs) (y : ys) = (x == y && isPrefixOf xs ys)
\end{code}

get State variables from names
\begin{code}
get_ZVar_st ((('s':'v':'_':xs),x))
 = [('s':'v':'_':xs)]
get_ZVar_st x
 = []
\end{code}
\begin{code}
is_ZVar_st a = isPrefixOf "sv" a
is_ZVar_v_st a = isPrefixOf "v_sv" a
\end{code}



\begin{code}
rename_ZVar (va,x)
  = case (is_st_var va) of
     True -> ("v_"++va,x)
     False -> (va,x)
rename_ZExpr (ZVar (va,x))
 = case (is_st_var va) of
   True -> (ZVar ("v_"++va,x))
   False -> (ZVar (va,x))
rename_ZExpr (ZInt zi)
 = (ZInt zi)
rename_ZExpr (ZGiven gv)
 = (ZGiven gv)
rename_ZExpr (ZFree0 va)
 = (ZFree0 va)
rename_ZExpr (ZFree1 va xpr)
 = (ZFree1 va (rename_ZExpr xpr))
rename_ZExpr (ZTuple xprlst)
 = (ZTuple (map rename_ZExpr xprlst))
rename_ZExpr (ZBinding xs)
 = (ZBinding (bindingsVar xs))
rename_ZExpr (ZSetDisplay xprlst)
 = (ZSetDisplay (map rename_ZExpr xprlst))
rename_ZExpr (ZSeqDisplay xprlst)
 = (ZSeqDisplay (map rename_ZExpr xprlst))
rename_ZExpr (ZFSet zf)
 = (ZFSet zf)
rename_ZExpr (ZIntSet i1 i2)
 = (ZIntSet i1 i2)
rename_ZExpr (ZGenerator zrl xpr)
 = (ZGenerator zrl (rename_ZExpr xpr))
rename_ZExpr (ZCross xprlst)
 = (ZCross (map rename_ZExpr xprlst))
rename_ZExpr (ZFreeType va lst1)
 = (ZFreeType va lst1)
rename_ZExpr (ZPowerSet{baseset=xpr, is_non_empty=b1, is_finite=b2})
 = (ZPowerSet{baseset=(rename_ZExpr xpr), is_non_empty=b1, is_finite=b2})
rename_ZExpr (ZFuncSet{ domset=expr1, ranset=expr2, is_function=b1, is_total=b2, is_onto=b3, is_one2one=b4, is_sequence=b5, is_non_empty=b6, is_finite=b7})
 = (ZFuncSet{ domset=(rename_ZExpr expr1), ranset=(rename_ZExpr expr2), is_function=b1, is_total=b2, is_onto=b3, is_one2one=b4, is_sequence=b5, is_non_empty=b6, is_finite=b7})
rename_ZExpr (ZSetComp lst1 (Just xpr))
 = (ZSetComp lst1 (Just (rename_ZExpr xpr)))
rename_ZExpr (ZSetComp lst1 Nothing)
 = (ZSetComp lst1 Nothing)
rename_ZExpr (ZLambda lst1 xpr)
 = (ZLambda lst1 (rename_ZExpr xpr))
rename_ZExpr (ZESchema zxp)
 = (ZESchema zxp)
rename_ZExpr (ZGivenSet gs)
 = (ZGivenSet gs)
rename_ZExpr (ZUniverse)
 = (ZUniverse)
rename_ZExpr (ZCall xpr1 xpr2)
 = (ZCall (rename_ZExpr xpr1) (rename_ZExpr xpr2))
rename_ZExpr (ZReln rl)
 = (ZReln rl)
rename_ZExpr (ZFunc1 f1)
 = (ZFunc1 f1)
rename_ZExpr (ZFunc2 f2)
 = (ZFunc2 f2)
rename_ZExpr (ZStrange st)
 = (ZStrange st)
rename_ZExpr (ZMu lst1 (Just xpr))
 = (ZMu lst1 (Just (rename_ZExpr xpr)))
rename_ZExpr (ZELet lst1 xpr1)
 = (ZELet (bindingsVar lst1) (rename_ZExpr xpr1))
rename_ZExpr (ZIf_Then_Else zp xpr1 xpr2)
 = (ZIf_Then_Else zp (rename_ZExpr xpr1) (rename_ZExpr xpr2))
rename_ZExpr (ZSelect xpr va)
 = (ZSelect xpr va)
rename_ZExpr (ZTheta zs)
 = (ZTheta zs)
rename_ZExpr x
 = x
\end{code}

\begin{code}
bindingsVar []
 = []
bindingsVar [((va,x),b)]
 = case (is_st_var va) of
   True -> [(("v_"++va,x),(rename_ZExpr b))]
   False -> [((va,x),(rename_ZExpr b))]
bindingsVar (((va,x),b):xs)
 = case (is_st_var va) of
   True -> [(("v_"++va,x),(rename_ZExpr b))]++(bindingsVar xs)
   False -> [((va,x),(rename_ZExpr b))]++(bindingsVar xs)
\end{code}


\begin{code}
rename_vars_CParameter (ChanInp zn)
 = (ChanInp zn)
rename_vars_CParameter (ChanInpPred zn zp)
 = (ChanInpPred zn (rename_ZPred zp))
rename_vars_CParameter (ChanOutExp ze)
 = (ChanOutExp (rename_ZExpr ze))
rename_vars_CParameter (ChanDotExp ze)
 = (ChanDotExp (rename_ZExpr ze))
\end{code}


\begin{code}
rename_vars_Comm (ChanComm zn cpls)
 = (ChanComm zn (map rename_vars_CParameter  cpls))
rename_vars_Comm (ChanGenComm zn zexprls cpls)
 = (ChanGenComm zn (map rename_ZExpr zexprls) (map rename_vars_CParameter cpls))
\end{code}
\begin{code}

rename_vars_CAction (CSPSkip )
 = (CSPSkip )
rename_vars_CAction (CSPStop )
 = (CSPStop )
rename_vars_CAction (CSPChaos)
 = (CSPChaos)
rename_vars_CAction (CSPSeq a1 a2)
 = (CSPSeq (rename_vars_CAction a1) (rename_vars_CAction a2))
rename_vars_CAction (CSPExtChoice a1 a2)
 = (CSPExtChoice (rename_vars_CAction a1) (rename_vars_CAction a2))
rename_vars_CAction (CActionSchemaExpr zsexp)
 = (CActionSchemaExpr zsexp)
rename_vars_CAction (CActionCommand cmd)
 = (CActionCommand (rename_vars_CCommand cmd))
rename_vars_CAction (CActionName zn)
 = (CActionName zn)
rename_vars_CAction (CSPCommAction c a)
 = (CSPCommAction (rename_vars_Comm c) (rename_vars_CAction a))
rename_vars_CAction (CSPGuard zp a)
 = (CSPGuard (rename_ZPred zp) (rename_vars_CAction a))

rename_vars_CAction (CSPIntChoice a1 a2)
 = (CSPIntChoice (rename_vars_CAction a1) (rename_vars_CAction a2))
rename_vars_CAction (CSPNSParal ns1 cs ns2 a1 a2)
 = (CSPNSParal ns1 cs ns2 (rename_vars_CAction a1) (rename_vars_CAction a2))
rename_vars_CAction (CSPParal cs a1 a2)
 = (CSPParal cs (rename_vars_CAction a1) (rename_vars_CAction a2))
rename_vars_CAction (CSPNSInter ns1 ns2 a1 a2)
 = (CSPNSInter ns1 ns2 (rename_vars_CAction a1) (rename_vars_CAction a2))
rename_vars_CAction (CSPInterleave a1 a2)
 = (CSPInterleave (rename_vars_CAction a1) (rename_vars_CAction a2))
rename_vars_CAction (CSPHide a cs)
 = (CSPHide (rename_vars_CAction a) cs)
rename_vars_CAction (CSPParAction zn zexprls)
 = (CSPParAction zn (map rename_ZExpr zexprls))
rename_vars_CAction (CSPRenAction zn crpl)
 = (CSPRenAction zn (rename_vars_CReplace crpl))
rename_vars_CAction (CSPRecursion zn a)
 = (CSPRecursion zn (rename_vars_CAction a))
rename_vars_CAction (CSPUnParAction zgf a zn)
 = (CSPUnParAction zgf (rename_vars_CAction a) zn)
rename_vars_CAction (CSPRepSeq zgf a)
 = (CSPRepSeq zgf (rename_vars_CAction a))
rename_vars_CAction (CSPRepExtChoice zgf a)
 = (CSPRepExtChoice zgf (rename_vars_CAction a))
rename_vars_CAction (CSPRepIntChoice zgf a)
 = (CSPRepIntChoice zgf (rename_vars_CAction a))
rename_vars_CAction (CSPRepParalNS cs zgf ns a)
 = (CSPRepParalNS cs zgf ns (rename_vars_CAction a))
rename_vars_CAction (CSPRepParal cs zgf a)
 = (CSPRepParal cs zgf (rename_vars_CAction a))
rename_vars_CAction (CSPRepInterlNS zgf ns a)
 = (CSPRepInterlNS zgf ns (rename_vars_CAction a))
rename_vars_CAction (CSPRepInterl zgf a)
 = (CSPRepInterl zgf (rename_vars_CAction a))
\end{code}


\begin{code}
rename_vars_CCommand (CAssign zvarls1 zexprls)
 = (CAssign zvarls1 (map rename_ZExpr zexprls))
rename_vars_CCommand (CIf ga)
 = (CIf (rename_vars_CGActions ga))
rename_vars_CCommand (CVarDecl zgf a)
 = (CVarDecl zgf (rename_vars_CAction a))
rename_vars_CCommand (CAssumpt znls zp1 zp2)
 = (CAssumpt znls (rename_ZPred zp1) zp2)
rename_vars_CCommand (CAssumpt1 znls zp)
 = (CAssumpt1 znls zp)
rename_vars_CCommand (CPrefix zp1 zp2)
 = (CPrefix (rename_ZPred zp1) zp2)
rename_vars_CCommand (CPrefix1 zp)
 = (CPrefix1 zp)
rename_vars_CCommand (CommandBrace zp)
 = (CommandBrace zp)
rename_vars_CCommand (CommandBracket zp)
 = (CommandBracket zp)
rename_vars_CCommand (CValDecl zgf a)
 = (CValDecl zgf (rename_vars_CAction a))
rename_vars_CCommand (CResDecl zgf a)
 = (CResDecl zgf (rename_vars_CAction a))
rename_vars_CCommand (CVResDecl zgf a)
 = (CVResDecl zgf (rename_vars_CAction a))
\end{code}

\begin{code}
rename_vars_CGActions (CircGAction zp a)
 = (CircGAction (rename_ZPred zp) (rename_vars_CAction a))
rename_vars_CGActions (CircThenElse (CircGAction zp a) cga2)
 = (CircThenElse (CircGAction (rename_ZPred zp) (rename_vars_CAction a)) (rename_vars_CGActions cga2))
-- rename_vars_CGActions (CircElse pa) = (CircElse pa)
\end{code}


\begin{code}
remdups [] = []
remdups (x:xs) = (if (member x xs) then remdups xs else x : remdups xs)
\end{code}

\subsection{Bits for FreeVariables (FV(X))}
\subsection{Free Variables -- $FV(A)$. }
Need to know how to calculate for Actions.
\begin{code}
getFV xs = []
\end{code}

\subsection{Others -- No specific topic}

\begin{code}
subset xs ys = all (`elem` ys) xs
\end{code}

\subsection{Expanding the main action}
\begin{code}
expand_action_names_PPar :: [PPar] -> PPar -> PPar
expand_action_names_PPar lst (ProcZPara zp)
  = (ProcZPara zp)
expand_action_names_PPar lst (CParAction zn pa)
  = (CParAction zn (expand_action_names_ParAction lst pa))
expand_action_names_PPar lst (CNameSet zn ns)
  = (CNameSet zn ns)
\end{code}
\begin{code}
expand_action_names_ParAction :: [PPar] -> ParAction -> ParAction
expand_action_names_ParAction lst (CircusAction ca) = (CircusAction (expand_action_names_CAction lst ca))-- Action
expand_action_names_ParAction lst (ParamActionDecl ls pa) = (ParamActionDecl ls (expand_action_names_ParAction lst pa))    -- Decl \circspot ParAction
\end{code}
\begin{code}
expand_action_names_CAction :: [PPar] -> CAction -> CAction
expand_action_names_CAction lst (CActionSchemaExpr x)
 = (CActionSchemaExpr x)
expand_action_names_CAction lst (CActionCommand c)
 = (CActionCommand (expand_action_names_CAction_comnd lst c))
expand_action_names_CAction lst (CActionName nm)
 = get_action nm lst
expand_action_names_CAction lst (CSPSkip)
 = (CSPSkip)
expand_action_names_CAction lst (CSPStop)
 = (CSPStop)
expand_action_names_CAction lst (CSPChaos)
 = (CSPChaos)
expand_action_names_CAction lst (CSPCommAction com c)
 = (CSPCommAction com (expand_action_names_CAction lst c))
expand_action_names_CAction lst (CSPGuard p c)
 = (CSPGuard p (expand_action_names_CAction lst c))
expand_action_names_CAction lst (CSPSeq ca cb)
 = (CSPSeq (expand_action_names_CAction lst ca) (expand_action_names_CAction lst cb))
expand_action_names_CAction lst (CSPExtChoice ca cb)
 = (CSPExtChoice (expand_action_names_CAction lst ca) (expand_action_names_CAction lst cb))
expand_action_names_CAction lst (CSPIntChoice ca cb)
 = (CSPIntChoice (expand_action_names_CAction lst ca) (expand_action_names_CAction lst cb))
expand_action_names_CAction lst (CSPNSParal ns1 cs ns2 ca cb)
 = (CSPNSParal ns1 cs ns2 (expand_action_names_CAction lst ca) (expand_action_names_CAction lst cb))
expand_action_names_CAction lst (CSPParal cs ca cb)
 = (CSPParal cs (expand_action_names_CAction lst ca) (expand_action_names_CAction lst cb))
expand_action_names_CAction lst (CSPNSInter ns1 ns2 ca cb)
 = (CSPNSInter ns1 ns2 (expand_action_names_CAction lst ca) (expand_action_names_CAction lst cb))
expand_action_names_CAction lst (CSPInterleave ca cb)
 = (CSPInterleave (expand_action_names_CAction lst ca) (expand_action_names_CAction lst cb))
expand_action_names_CAction lst (CSPHide c cs)
 = (CSPHide (expand_action_names_CAction lst c) cs)
expand_action_names_CAction lst (CSPParAction nm xp)
 = (CSPParAction nm xp)
expand_action_names_CAction lst (CSPRenAction nm cr)
 = (CSPRenAction nm cr)
expand_action_names_CAction lst (CSPRecursion n (CSPSeq c (CActionName n1)))
 = case n == n1 of
   True -> (CSPRecursion n (CSPSeq (expand_action_names_CAction lst c) (CActionName n)))
   False -> (CSPRecursion n (CSPSeq (expand_action_names_CAction lst c) (CActionName n1)))
expand_action_names_CAction lst (CSPRecursion n c)
 = (CSPRecursion n (expand_action_names_CAction lst c))
expand_action_names_CAction lst (CSPUnParAction lsta c nm)
 = (CSPUnParAction lsta (expand_action_names_CAction lst c) nm)
expand_action_names_CAction lst (CSPRepSeq lsta c)
 = (CSPRepSeq lsta (expand_action_names_CAction lst c))
expand_action_names_CAction lst (CSPRepExtChoice lsta c)
 = (CSPRepExtChoice lsta (expand_action_names_CAction lst c))
expand_action_names_CAction lst (CSPRepIntChoice lsta c)
 = (CSPRepIntChoice lsta (expand_action_names_CAction lst c))
expand_action_names_CAction lst (CSPRepParalNS cs lsta ns c)
 = (CSPRepParalNS cs lsta ns (expand_action_names_CAction lst c))
expand_action_names_CAction lst (CSPRepParal cs lsta c)
 = (CSPRepParal cs lsta (expand_action_names_CAction lst c))
expand_action_names_CAction lst (CSPRepInterlNS lsta ns c)
 = (CSPRepInterlNS lsta ns (expand_action_names_CAction lst c))
expand_action_names_CAction lst (CSPRepInterl lsta c)
 = (CSPRepInterl lsta (expand_action_names_CAction lst c))
\end{code}
\begin{code}
expand_action_names_CAction_comnd lst (CAssign v e)
 = (CAssign v e)
expand_action_names_CAction_comnd lst (CIf ga)
 = (CIf (get_if lst ga))
expand_action_names_CAction_comnd lst (CVarDecl z a)
 = (CVarDecl z (expand_action_names_CAction lst a))
expand_action_names_CAction_comnd lst (CAssumpt n p1 p2)
 = (CAssumpt n p1 p2)
expand_action_names_CAction_comnd lst (CAssumpt1 n p)
 = (CAssumpt1 n p)
expand_action_names_CAction_comnd lst (CPrefix p1 p2)
 = (CPrefix p1 p2)
expand_action_names_CAction_comnd lst (CPrefix1 p)
 = (CPrefix1 p)
expand_action_names_CAction_comnd lst (CommandBrace p)
 = (CommandBrace p)
expand_action_names_CAction_comnd lst (CommandBracket p)
 = (CommandBracket p)
expand_action_names_CAction_comnd lst (CValDecl z a)
 = (CValDecl z (expand_action_names_CAction lst a))
expand_action_names_CAction_comnd lst (CResDecl z a)
 = (CResDecl z (expand_action_names_CAction lst a))
expand_action_names_CAction_comnd lst (CVResDecl z a)
 = (CVResDecl z (expand_action_names_CAction lst a))
\end{code}

\begin{code}
get_if lst (CircGAction p a)
 = (CircGAction p (expand_action_names_CAction lst a))
get_if lst (CircThenElse (CircGAction p a) gb)
 = (CircThenElse (CircGAction p (expand_action_names_CAction lst a)) (get_if lst gb))
-- get_if lst (CircElse (CircusAction a))
--  = (CircElse (CircusAction (expand_action_names_CAction lst a)))
-- get_if lst (CircElse (ParamActionDecl x (CircusAction a)))
--  = (CircElse (ParamActionDecl x (CircusAction (expand_action_names_CAction lst a))))
\end{code}

\begin{code}
get_action _ [] = error "Action list is empty"
get_action name [(CParAction n (CircusAction a))]
  | name == n = a
  | otherwise = error ("Action "++(name)++" not found")
get_action name ((CParAction n (CircusAction a)):xs)
  | (name == n) = a
  | otherwise = get_action name xs
get_action name (_:xs)
  = get_action name xs
\end{code}

\begin{code}
get_chan_param :: [CParameter] -> [ZExpr]
get_chan_param [] = []
get_chan_param [ChanDotExp (ZVar (x,_))]
 = [ZVar (x,[])]
get_chan_param [ChanOutExp (ZVar (x,_))]
 = [ZVar (x,[])]
get_chan_param [_]
 = []
get_chan_param ((ChanDotExp (ZVar (x,_))):xs)
 = [ZVar (x,[])]++(get_chan_param xs)
get_chan_param ((ChanOutExp (ZVar (x,_))):xs)
 = [ZVar (x,[])]++(get_chan_param xs)
get_chan_param (_:xs) = (get_chan_param xs)
\end{code}

\begin{code}
filter_state_comp :: [(ZName, ZVar, ZExpr)] -> [ZVar]
filter_state_comp [] = []
filter_state_comp [(_, v, _)] = [v]
filter_state_comp ((_, v, _):xs) = [v]++(filter_state_comp xs)
\end{code}

\begin{code}
is_st_var ('s':'v':'_':xs) = True
is_st_var _ = False
\end{code}




\begin{code}
middle (a,b,c) = b
\end{code}

\subsubsection{rename vars}

\begin{code}
rename_vars_ParAction (CircusAction ca)
  = (CircusAction (rename_vars_CAction ca))
rename_vars_ParAction (ParamActionDecl zglst pa)
  = (ParamActionDecl zglst (rename_vars_ParAction pa))
\end{code}

\subsection{$[ZName]$ to $[ZExpr]$ - mainly converting to $ZVar (x,[])$}
\begin{code}
zname_to_zexpr [] = []
zname_to_zexpr [a] = [ZVar (a,[])]
zname_to_zexpr (a:as) = [ZVar (a,[])]++(zname_to_zexpr as)
\end{code}
\subsection{$[ZVar]$ to $[ZExpr]$}
\begin{code}
zvar_to_zexpr [] = []
zvar_to_zexpr [(a,[])] = [ZVar (a,[])]
zvar_to_zexpr ((a,[]):as) = [ZVar (a,[])]++(zvar_to_zexpr as)
\end{code}
\subsection{$[ZGenFilt]$ to $[ZExpr]$}
\begin{code}

zgenfilt_to_zexpr [] = []
zgenfilt_to_zexpr [(Choose (a,[]) t)] = [ZVar (a,[])]
zgenfilt_to_zexpr ((Choose (a,[]) t):as) = [ZVar (a,[])]++(zgenfilt_to_zexpr as)
zgenfilt_to_zexpr (_:as) = []++(zgenfilt_to_zexpr as)
\end{code}
\subsubsection{rename vars}
%% You have to put here the remainder for Processes, so you can create on line 78
% of MappingFunStatelessCircus the definition of a renamed function for the
% Proc_var names of the variables before starting the mapping process.
\begin{code}
rename_vars_ZPara1 :: [(ZName, ZVar, ZExpr)] -> ZPara -> ZPara
rename_vars_ZPara1 lst (Process zp)
  = (Process (rename_vars_ProcDecl1 lst zp))
-- rename_vars_ZPara1 lst (ZSchemaDef n zs)
--   = (ZSchemaDef n (rename_vars_ZSExpr1 lst zs))
rename_vars_ZPara1 lst x = x
\end{code}

\begin{code}
rename_vars_ZSExpr1 :: [(ZName, ZVar, ZExpr)] -> ZSExpr -> ZSExpr
rename_vars_ZSExpr1 lst (ZSchema s)
  = ZSchema (map (rename_ZGenFilt1 lst) s)
\end{code}

\begin{code}
rename_vars_ProcDecl1 :: [(ZName, ZVar, ZExpr)] -> ProcDecl -> ProcDecl
rename_vars_ProcDecl1 lst (CProcess zn pd)
  = (CProcess zn (rename_vars_ProcessDef1 lst pd))
rename_vars_ProcDecl1 lst (CParamProcess zn znls pd)
  = (CParamProcess zn znls (rename_vars_ProcessDef1 lst pd))
rename_vars_ProcDecl1 lst (CGenProcess zn znls pd)
  = (CParamProcess zn znls (rename_vars_ProcessDef1 lst pd))
\end{code}

\begin{code}
rename_vars_ProcessDef1 :: [(ZName, ZVar, ZExpr)] -> ProcessDef -> ProcessDef
rename_vars_ProcessDef1 lst (ProcDefSpot zgf pd)
  = (ProcDefSpot zgf (rename_vars_ProcessDef1 lst pd))
rename_vars_ProcessDef1 lst (ProcDefIndex zgf pd)
  = (ProcDefIndex zgf (rename_vars_ProcessDef1 lst pd))
rename_vars_ProcessDef1 lst (ProcDef cp)
  = (ProcDef (rename_vars_CProc1 lst cp))
\end{code}

\begin{code}
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
  = (ProcMain (rename_vars_ZPara1 lst zp) (map (rename_vars_PPar1 lst) ppl) (rename_vars_CAction1 lst ca))
rename_vars_CProc1 lst (ProcStalessMain ppl ca)
  = (ProcStalessMain ppl (rename_vars_CAction1 lst ca))
\end{code}


\subsubsection{Circus Actions}
\begin{code}
rename_vars_PPar1 :: [(ZName, ZVar, ZExpr)] -> PPar -> PPar
rename_vars_PPar1 lst (ProcZPara zp)
  = (ProcZPara zp)
rename_vars_PPar1 lst (CParAction zn pa)
  = (CParAction zn (rename_vars_ParAction1 lst pa))
rename_vars_PPar1 lst (CNameSet zn ns)
  = (CNameSet zn ns)
\end{code}

\begin{code}
rename_vars_ParAction1 :: [(ZName, ZVar, ZExpr)] -> ParAction -> ParAction
rename_vars_ParAction1 lst (CircusAction ca)
  = (CircusAction (rename_vars_CAction1 lst ca))
rename_vars_ParAction1 lst (ParamActionDecl zgf pa)
  = (ParamActionDecl zgf (rename_vars_ParAction1 lst pa))
\end{code}


\begin{code}
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
\end{code}

\begin{code}
rename_vars_Comm1 :: [(ZName, ZVar, ZExpr)] -> Comm -> Comm
rename_vars_Comm1 lst (ChanComm zn cpls)
 = (ChanComm zn (map (rename_vars_CParameter1 lst) cpls))
rename_vars_Comm1 lst (ChanGenComm zn zexprls cpls)
 = (ChanGenComm zn (map (rename_vars_ZExpr1 lst) zexprls) (map (rename_vars_CParameter1 lst) cpls))
\end{code}

\begin{code}
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
\end{code}

\begin{code}
rename_vars_CCommand1 :: [(ZName, ZVar, ZExpr)] -> CCommand -> CCommand
rename_vars_CCommand1 lst (CAssign zv ze)
 = (CAssign (map (rename_vars_ZVar1 lst) zv) 
            (map (rename_vars_ZExpr1 lst) ze))
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
\end{code}

\begin{code}
rename_vars_CGActions1 :: [(ZName, ZVar, ZExpr)] -> CGActions -> CGActions
rename_vars_CGActions1 lst (CircGAction zp a)
 = (CircGAction (rename_vars_ZPred1 lst zp) (rename_vars_CAction1 lst a))
rename_vars_CGActions1 lst (CircThenElse (CircGAction zp a) cga2)
 = (CircThenElse (CircGAction (rename_vars_ZPred1 lst zp) (rename_vars_CAction1 lst a)) (rename_vars_CGActions1 lst cga2))
-- rename_vars_CGActions1 lst (CircElse pa)
-- = (CircElse pa)
\end{code}

\begin{code}
rename_vars_CReplace1 :: [(ZName, ZVar, ZExpr)] -> CReplace -> CReplace
rename_vars_CReplace1 lst (CRename zvarls1 zvarls)
 = (CRename zvarls1 zvarls)
rename_vars_CReplace1 lst (CRenameAssign zvarls1 zvarls)
 = (CRenameAssign zvarls1 zvarls)
\end{code}

\begin{code}
bindingsVar1 lst []
 = []
bindingsVar1 lst [((va,x),b)]
 = [(((join_name (get_proc_name va lst) va),x),(rename_vars_ZExpr1 lst b))]
bindingsVar1 lst (((va,x),b):xs)
 = [(((join_name (get_proc_name va lst) va),x),(rename_vars_ZExpr1 lst b))]++(bindingsVar1 lst xs)
\end{code}
\begin{code}
get_bindings_var []
 = []
get_bindings_var [((va,x),b)]
 = [va]
get_bindings_var (((va,x),b):xs)
 = va:(get_bindings_var xs)
\end{code}
\begin{code}
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
\end{code}

\begin{code}
get_proc_name :: ZName -> [(ZName, ZVar, ZExpr)] -> ZName
get_proc_name x [(a,(va,x1),b)]
 = case x == va of
  True -> a
  _ -> ""
get_proc_name x ((a,(va,x1),b):vst)
 = case x == va of
  True -> a
  _ -> get_proc_name x vst
\end{code}
\begin{code}
rename_ZGenFilt1 lst (Include s) = (Include s)
rename_ZGenFilt1 lst (Choose (va,x) e) = (Choose ((join_name (join_name "sv" (get_proc_name va lst)) va),x) (rename_vars_ZExpr1 lst e))
rename_ZGenFilt1 lst (Check p) = (Check (rename_vars_ZPred1 lst p))
rename_ZGenFilt1 lst (Evaluate v e1 e2) = (Evaluate v (rename_vars_ZExpr1 lst e1) (rename_vars_ZExpr1 lst e2))
\end{code}
\begin{code}
rename_vars_ZVar1 :: [(ZName, ZVar, ZExpr)] -> ZVar -> ZVar
rename_vars_ZVar1 lst (va,x)
 = case (inListVar1 va lst) of
  True -> ((join_name (join_name "sv" (get_proc_name va lst)) va),x)
  _ -> (va,x)
\end{code}
\begin{code}
rename_vars_ZExpr1 :: [(ZName, ZVar, ZExpr)] -> ZExpr -> ZExpr
rename_vars_ZExpr1 lst (ZVar (va,x))
 = case (inListVar1 va lst) of
  True -> (ZVar 
            ((join_name 
              (join_name "sv" 
                        (get_proc_name va lst)) 
              va),x))
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
 = (ZSetComp (map (rename_ZGenFilt1 lst) pname1) (Just (rename_vars_ZExpr1 lst xpr)))
rename_vars_ZExpr1 lst (ZSetComp pname1 Nothing)
 = (ZSetComp (map (rename_ZGenFilt1 lst) pname1) Nothing)
rename_vars_ZExpr1 lst (ZLambda pname1 xpr)
 = (ZLambda (map (rename_ZGenFilt1 lst) pname1) (rename_vars_ZExpr1 lst xpr))
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
 = (ZMu (map (rename_ZGenFilt1 lst) pname1) (Just (rename_vars_ZExpr1 lst xpr)))
rename_vars_ZExpr1 lst (ZELet pname1 xpr1)
 = (ZELet (bindingsVar1 lst pname1) (rename_vars_ZExpr1 lst xpr1))
rename_vars_ZExpr1 lst (ZIf_Then_Else zp xpr1 xpr2)
 = (ZIf_Then_Else zp (rename_vars_ZExpr1 lst xpr1) (rename_vars_ZExpr1 lst xpr2))
rename_vars_ZExpr1 lst (ZSelect xpr va)
 = (ZSelect xpr va)
rename_vars_ZExpr1 lst (ZTheta zs)
 = (ZTheta zs)
\end{code}


\begin{code}
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
\end{code}


\begin{code}
-- extract the delta variables in here'
get_delta_names [(ZFreeTypeDef ("NAME",[]) xs)]
  = get_delta_names_aux xs
get_delta_names ((ZFreeTypeDef ("NAME",[]) xs):xss)
  = (get_delta_names_aux xs)++(get_delta_names xss)
get_delta_names (_:xs)
  = (get_delta_names xs)
get_delta_names []
  = []
\end{code}

\begin{code}
get_delta_names_aux [(ZBranch0 (a,[]))]
  = [a]
get_delta_names_aux ((ZBranch0 (a,[])):xs)
  = [a]++(get_delta_names_aux xs)
\end{code}



\begin{code}
get_vars_ZExpr :: ZExpr -> [ZName]
get_vars_ZExpr (ZVar (('s':'t':'_':'v':'a':'r':'_':xs),x))
 = [('s':'t':'_':'v':'a':'r':'_':xs)]
get_vars_ZExpr (ZFree1 va xpr)
 = (get_vars_ZExpr xpr)
get_vars_ZExpr (ZTuple xpr)
 = concat (map get_vars_ZExpr xpr)
get_vars_ZExpr (ZBinding xs)
 = (get_bindings_var xs)
get_vars_ZExpr (ZSetDisplay xpr)
 = concat (map get_vars_ZExpr xpr)
get_vars_ZExpr (ZSeqDisplay xpr)
 = concat (map get_vars_ZExpr xpr)
get_vars_ZExpr (ZGenerator zrl xpr)
 = (get_vars_ZExpr xpr)
get_vars_ZExpr (ZCross xpr)
 = concat (map get_vars_ZExpr xpr)
get_vars_ZExpr (ZPowerSet{baseset=xpr, is_non_empty=b1, is_finite=b2})
 = (get_vars_ZExpr xpr)
get_vars_ZExpr (ZFuncSet{ domset=expr1, ranset=expr2, is_function=b1, is_total=b2, is_onto=b3, is_one2one=b4, is_sequence=b5, is_non_empty=b6, is_finite=b7})
 = (get_vars_ZExpr expr1)++(get_vars_ZExpr expr2)
get_vars_ZExpr (ZSetComp pname1 (Just xpr))
 = (get_vars_ZExpr xpr)
get_vars_ZExpr (ZLambda pname1 xpr)
 = (get_vars_ZExpr xpr)
get_vars_ZExpr (ZCall xpr1 xpr2)
 = (get_vars_ZExpr xpr1) ++(get_vars_ZExpr xpr2)
get_vars_ZExpr (ZMu pname1 (Just xpr))
 = (get_vars_ZExpr xpr)
get_vars_ZExpr (ZELet pname1 xpr1)
 = (get_bindings_var pname1)++(get_vars_ZExpr xpr1)
get_vars_ZExpr (ZIf_Then_Else zp xpr1 xpr2)
 = (get_vars_ZExpr xpr1)++(get_vars_ZExpr xpr2)
get_vars_ZExpr _ = []
\end{code}
\begin{code}
get_vars_ZPred (ZAnd p1 p2)
 = ((get_vars_ZPred p1)++(get_vars_ZPred p2))
get_vars_ZPred (ZOr p1 p2)
 = ((get_vars_ZPred p1)++(get_vars_ZPred p2))
get_vars_ZPred (ZImplies p1 p2)
 = ((get_vars_ZPred p1)++(get_vars_ZPred p2))
get_vars_ZPred (ZIff p1 p2)
 = ((get_vars_ZPred p1)++(get_vars_ZPred p2))
get_vars_ZPred (ZNot p)
 = ((get_vars_ZPred p))
get_vars_ZPred (ZEqual xpr1 xpr2)
 = ( (get_vars_ZExpr xpr1)++(get_vars_ZExpr xpr2))
get_vars_ZPred (ZMember xpr1 xpr2)
 = ((get_vars_ZExpr xpr1)++(get_vars_ZExpr xpr2))
get_vars_ZPred _
 = []
\end{code}
Construction of the Universe set in CSP
\begin{code}
def_U_NAME x = ("U_"++(map toUpper (take 3 x)))
def_U_prefix x = (map toTitle (take 3 x))

-- def_U_NAME x = ("U_"++Data.Text.unpack(Data.Text.toUpper(Data.Text.take 3 (pack x))))
-- def_U_prefix x = (Data.Text.unpack(Data.Text.toTitle(Data.Text.take 3 (Data.Text.pack x))))

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
\end{code}
\begin{code}
-- extract the delta variables and types in here'
def_universe [(ZAbbreviation ("\\delta",[]) (ZSetDisplay xs))]
  = def_universe_aux xs
def_universe ((ZAbbreviation ("\\delta",[]) (ZSetDisplay xs)):xss)
  = (def_universe_aux xs)++(def_universe xss)
def_universe (_:xs)
  = (def_universe xs)
def_universe []
  = []
\end{code}

\begin{code}
def_universe_aux :: [ZExpr] -> [(String, [Char], [Char], [Char])]
def_universe_aux [] = []
def_universe_aux [ZCall (ZVar ("\\mapsto",[])) (ZTuple [ZVar (b,[]),ZVar ("\\nat",[])])] = [(b,"U_NAT", "Nat", "NatValue")]
def_universe_aux [ZCall (ZVar ("\\mapsto",[])) (ZTuple [ZVar (b,[]),ZVar (c,[])])]= [(b,(def_U_NAME c), (def_U_prefix c), c)]
def_universe_aux ((ZCall (ZVar ("\\mapsto",[])) (ZTuple [ZVar (b,[]),ZVar ("\\nat",[])])):xs) = ((b,"U_NAT", "Nat", "NatValue"):(def_universe_aux xs))
def_universe_aux ((ZCall (ZVar ("\\mapsto",[])) (ZTuple [ZVar (b,[]),ZVar (c,[])])):xs) = ((b,(def_U_NAME c), (def_U_prefix c), c):(def_universe_aux xs))
def_universe_aux [(ZCall (ZVar ("\\mapsto",[])) (ZTuple [ZVar (b,[]), ZCall (ZVar ("\\power",[])) (ZVar (c,[]))]))]
  = [(b,(def_U_NAME ("POWER_"++c)), (def_U_prefix ("POWER_"++c)), ("Set("++c++")"))]
def_universe_aux ((ZCall (ZVar ("\\mapsto",[])) (ZTuple [ZVar (b,[]), ZCall (ZVar ("\\power",[])) (ZVar (c,[]))])):xs)
  = ((b,(def_U_NAME ("P"++c)), (def_U_prefix ("P"++c)), ("Set("++c++")")):(def_universe_aux xs))
\end{code}

\begin{code}
filter_types_universe [] = []
filter_types_universe [(a,b,c,d)] = [(b,b,c,d)]
filter_types_universe ((a,b,c,d):xs) = ((b,b,c,d):(filter_types_universe xs))
\end{code}


Pieces from MappingFunStatelessCircus file


\begin{code}

def_delta_mapping :: [(ZName, ZVar, ZExpr)] -> [ZExpr]
def_delta_mapping [(n,(v,[]),t)] 
  = [ZCall (ZVar ("\\mapsto",[])) (ZTuple [ZVar ((join_name (join_name "sv" n) v),[]),t])]
def_delta_mapping ((n,(v,[]),t):xs) 
  = [ZCall (ZVar ("\\mapsto",[])) (ZTuple [ZVar ((join_name (join_name "sv" n) v),[]),t])] 
    ++ (def_delta_mapping xs)
def_delta_mapping [] = []
\end{code}

\begin{code}
def_delta_name :: [(ZName, ZVar, ZExpr)] -> [ZBranch]
def_delta_name [(n,(v,[]),t)] 
  = [ZBranch0 ((join_name (join_name "sv" n) v),[])]
def_delta_name ((n,(v,[]),t):xs) 
  = [ZBranch0 ((join_name (join_name "sv" n) v),[])] 
    ++ (def_delta_name xs)
def_delta_name [] = []

\end{code}
\begin{code}
get_pre_Circ_proc :: [ZPara] -> [ZPara]
get_pre_Circ_proc ((Process cp):xs) 
  = (get_pre_Circ_proc xs)
get_pre_Circ_proc (x:xs) 
  = x:(get_pre_Circ_proc xs)
get_pre_Circ_proc []
  = []
\end{code}
\subsection{Creating the Memory process}
\begin{code}
def_mem_st_Circus_aux :: [ZPara] -> [ZPara] -> [(ZName, ZVar, ZExpr)]
def_mem_st_Circus_aux spec []
  = []
def_mem_st_Circus_aux spec [x]
  = def_mem_st_CircParagraphs spec x
def_mem_st_Circus_aux spec (x:xs)
  = (def_mem_st_CircParagraphs spec x)++(def_mem_st_Circus_aux spec xs)
\end{code}

\begin{code}
rename_z_schema_state spec (CProcess p (ProcDef (ProcMain (ZSchemaDef (ZSPlain n) schlst) proclst ma)))
  = (CProcess p (ProcDef (ProcMain (ZSchemaDef (ZSPlain n) (ZSchema xs)) proclst ma)))
    where
      xs = retrive_schemas spec schlst
rename_z_schema_state spec x = x
\end{code}

\begin{code}
retrive_schemas spec (ZSRef (ZSPlain nn) [] [])
  = case res of
      Just e' -> e'
      Nothing -> error "Schema definition not found!"
    where 
      res = (retrieve_z_schema_state nn spec)
retrive_schemas spec (ZS2 ZSAnd a b)
  = (retrive_schemas spec a)++(retrive_schemas spec b)
\end{code}

\begin{code}
retrieve_z_schema_state n [(ZSchemaDef (ZSPlain nn) (ZSchema lstx))]
  | n == nn = Just lstx
  | otherwise = Nothing
retrieve_z_schema_state n [_] = Nothing
retrieve_z_schema_state n ((ZSchemaDef (ZSPlain nn) (ZSchema lstx)):xs)
  | n == nn = Just lstx
  | otherwise = retrieve_z_schema_state n xs
retrieve_z_schema_state n (_:xs) = retrieve_z_schema_state n xs
\end{code}
\begin{code}
def_mem_st_CircParagraphs :: [ZPara] -> ZPara -> [(ZName, ZVar, ZExpr)]
def_mem_st_CircParagraphs spec (Process cp)
  = (def_mem_st_ProcDecl spec ncp)
    where 
      ncp = rename_z_schema_state spec cp
def_mem_st_CircParagraphs spec x
  = []
\end{code}

\begin{code}
def_mem_st_ProcDecl :: [ZPara] -> ProcDecl -> [(ZName, ZVar, ZExpr)]
def_mem_st_ProcDecl spec (CGenProcess zn (x:xs) pd)
  = (def_mem_st_ProcessDef spec zn pd)
def_mem_st_ProcDecl spec (CProcess zn pd)
  = (def_mem_st_ProcessDef spec zn pd)
\end{code}

\begin{code}
def_mem_st_ProcessDef :: [ZPara] -> ZName -> ProcessDef -> [(ZName, ZVar, ZExpr)]
def_mem_st_ProcessDef spec name (ProcDefSpot xl pd)
  = (def_mem_st_ProcessDef spec name pd)
def_mem_st_ProcessDef spec name (ProcDefIndex xl pd)
  = (def_mem_st_ProcessDef spec name pd)
def_mem_st_ProcessDef spec name (ProcDef cp)
  = (def_mem_st_CProc spec name cp)
\end{code}

\begin{code}
def_mem_st_CProc :: [ZPara] -> ZName -> CProc -> [(ZName, ZVar, ZExpr)]
def_mem_st_CProc spec name (ProcMain (ZSchemaDef n xls) (x:xs) ca)
  = (get_state_var spec name xls)
def_mem_st_CProc spec name x
  = []
\end{code}


\begin{code}  
get_state_var :: [ZPara] -> ZName -> ZSExpr -> [(ZName, ZVar, ZExpr)]
get_state_var spec name (ZSRef (ZSPlain nn) [] [])
  = case statev of
      Just s -> concat (map (get_state_var_aux name) s)
      Nothing -> []
    where
      statev = retrieve_z_schema_state nn spec

get_state_var spec name (ZSchema s)
  = concat (map (get_state_var_aux name) s)
get_state_var _ _ _ = []

\end{code}
\begin{code}
get_state_var_aux name (Choose x y) = [(name, x, y)]
get_state_var_aux _ _ = []
\end{code}

Here I'm making the bindings for the main action. 
\begin{code}
mk_main_action_bind :: [(ZName, ZVar, ZExpr)] -> CAction -> CAction
mk_main_action_bind lst ca
  | null lst = (CActionCommand (CValDecl [Choose ("b",[]) (ZSetComp [Choose ("x",[]) (ZVar ("BINDING",[])) ] Nothing)] ca))
  | otherwise = (CActionCommand (CValDecl [Choose ("b",[]) (ZSetComp [Choose ("x",[]) (ZVar ("BINDING",[])),Check (mk_inv lst) ] Nothing)] ca))
\end{code}
\begin{code}
mk_inv :: [(ZName, ZVar, ZExpr)] -> ZPred
mk_inv [(a,b,ZVar c)] 
  = (ZMember (ZVar b) (ZVar c))
mk_inv ((a,b,ZVar c):xs) 
  = (ZAnd (mk_inv xs) (ZMember (ZVar b) (ZVar c)) ) 
mk_inv (_:xs) 
  = mk_inv xs

\end{code}

Given $\{v_0,\ldots,v_n\}$, the function $make\_maps\_to$ returns $\{v_0 \mapsto vv_o, \ldots, v_n \mapsto vv_n\}$.
\begin{code}
make_maps_to :: [ZVar] -> [ZExpr]
make_maps_to [(x,[])]
  = [ZCall (ZVar ("\\mapsto",[]))
    (ZTuple [ZVar (x,[]),ZVar ("val"++x,[])])]
make_maps_to ((x,[]):xs)
  = [ZCall (ZVar ("\\mapsto",[]))
    (ZTuple [ZVar (x,[]),ZVar ("val"++x,[])])]++(make_maps_to xs)
\end{code}


% \subsection{Adding permanent bits of the new \Circus specification ($MemoryMerge$, $MRG$, etc)}

TODO: this function here should somehow propagate any parameter from a replicated operator

EX: [] i: {a,b,c} @ x.i -> SKIP
   = x.a -> SKIP [] x.b -> SKIP [] x.c -> SKIP
EX: [] i: {a,b,c} @ A(x)
   = A(a) [] A(b) [] A(c)
\begin{code}
propagate_CSPRep (CActionSchemaExpr e) = (CActionSchemaExpr e)
propagate_CSPRep (CActionCommand c) = (CActionCommand c) 
propagate_CSPRep (CActionName n) = (CActionName n) 
propagate_CSPRep (CSPSkip) = (CSPSkip) 
propagate_CSPRep (CSPStop ) = (CSPStop ) 
propagate_CSPRep (CSPChaos) = (CSPChaos) 
propagate_CSPRep (CSPCommAction c a) = (CSPCommAction c (propagate_CSPRep a)) 
propagate_CSPRep (CSPGuard p a) = (CSPGuard p (propagate_CSPRep a)) 
propagate_CSPRep (CSPSeq a1 a2) = (CSPSeq (propagate_CSPRep a1) (propagate_CSPRep a2)) 
propagate_CSPRep (CSPExtChoice a1 a2) = (CSPExtChoice (propagate_CSPRep a1) (propagate_CSPRep a2)) 
propagate_CSPRep (CSPIntChoice a1 a2) = (CSPIntChoice (propagate_CSPRep a1) (propagate_CSPRep a2)) 
propagate_CSPRep (CSPNSParal n1 c n2 a1 a2) = (CSPNSParal n1 c n2 (propagate_CSPRep a1) (propagate_CSPRep a2)) 
propagate_CSPRep (CSPParal c a1 a2) = (CSPParal c (propagate_CSPRep a1) (propagate_CSPRep a2)) 
propagate_CSPRep (CSPNSInter n1 n2 a1 a2) = (CSPNSInter n1 n2 (propagate_CSPRep a1) (propagate_CSPRep a2)) 
propagate_CSPRep (CSPInterleave a1 a2) = (CSPInterleave (propagate_CSPRep a1) (propagate_CSPRep a2)) 
propagate_CSPRep (CSPHide a c) = (CSPHide (propagate_CSPRep a) c) 
propagate_CSPRep (CSPParAction n ls) = (CSPParAction n ls) 
propagate_CSPRep (CSPRenAction n r) = (CSPRenAction n r) 
propagate_CSPRep (CSPRecursion n a) = (CSPRecursion n (propagate_CSPRep a)) 
propagate_CSPRep (CSPUnParAction ls a n) = (CSPUnParAction ls (propagate_CSPRep a) n) 
propagate_CSPRep (CSPRepExtChoice ls a) = (CSPRepExtChoice ls (propagate_CSPRep a)) 
propagate_CSPRep (CSPRepIntChoice ls a) = (CSPRepIntChoice ls (propagate_CSPRep a)) 
propagate_CSPRep (CSPRepParalNS c ls n a) = (CSPRepParalNS c ls n (propagate_CSPRep a)) 
propagate_CSPRep (CSPRepParal c ls a) = (CSPRepParal c ls (propagate_CSPRep a)) 
propagate_CSPRep (CSPRepInterlNS ls n a) = (CSPRepInterlNS ls n (propagate_CSPRep a)) 
propagate_CSPRep (CSPRepInterl ls a) = (CSPRepInterl ls (propagate_CSPRep a)) 
\end{code}


\begin{code}
make_memory_proc =
  CParAction "Memory" (CircusAction (CActionCommand (CVResDecl [Choose ("b",[]) (ZVar ("BINDING",[]))] (CSPExtChoice (CSPExtChoice (CSPRepExtChoice [Choose ("n",[]) (ZCall (ZVar ("\\dom",[])) (ZVar ("b",[])))] (CSPCommAction (ChanComm "mget" [ChanDotExp (ZVar ("n",[])),ChanOutExp (ZCall (ZVar ("b",[])) (ZVar ("n",[])))]) (CSPParAction "Memory" [ZVar ("b",[])]))) (CSPRepExtChoice [Choose ("n",[]) (ZCall (ZVar ("\\dom",[])) (ZVar ("b",[])))] (CSPCommAction (ChanComm "mset" [ChanDotExp (ZVar ("n",[])),ChanInpPred "nv" (ZMember (ZVar ("nv",[])) (ZCall (ZVar ("\\delta",[])) (ZVar ("n",[]))))]) (CSPParAction "Memory" [ZCall (ZVar ("\\oplus",[])) (ZTuple [ZVar ("b",[]),ZSetDisplay [ZCall (ZVar ("\\mapsto",[])) (ZTuple [ZVar ("n",[]),ZVar ("nv",[])])]])])))) (CSPCommAction (ChanComm "terminate" []) CSPSkip)))))
\end{code}
