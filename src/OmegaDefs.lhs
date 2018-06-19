\chapter{Misc functions -- File: OmegaDefs.lhs}
Functions used for manipulating lists (Z Sets and sequences, as well as calculating the provisos from the Circus Refinement laws)

\ignore{
\begin{code}
module OmegaDefs where
-- import Data.Text hiding (map,concat,all,take)
import Subs
import AST
import Errors
import RepParamAction
import Data.List hiding (union, intersect, isPrefixOf, deleteBy)

\end{code}
}

\subsection{$make\_get\_com$}
This function will take the list of state variables $[ZName]$ that are free in an expression $e$, with no duplicates, and then make a $mget$ for each one, with a copy of such value with the prefix $v\_$. It will recurse until the point where a single element $x$ is left and then the prefixed action continues behaving like $c$.
\begin{circus}
make\_get\_com\ (v_0,\ldots,v_n,l_0,\ldots,l_m)~A \defs
\\\t2 mget.v_0?vv_0 \then \ldots \then mget.v_n?vv_n \then
\\\t2 mget.l_0?vl_0 \then \ldots \then mget.l_m?vl_m \then A
\end{circus}
\begin{code}
make_get_com :: [ZVar] -> CAction -> CAction
make_get_com [] c = c
make_get_com ((x,y,z):xs) c
  = (CSPCommAction (ChanComm ("mget_"++x)
    [ChanInp ("v_"++x)]) (make_get_com xs c))
\end{code}
\subsection{$make\_set\_com$}
This function updates the values of the $Memory$ process by generating a sequence of $mset$ communications and then it behaves like $f~c$, where $f$ may be the $omega\_CAction$ or $omega\_prime\_CAction$.
\begin{code}
make_set_com :: (CAction -> CAction) -> [ZVar] -> [ZExpr] -> CAction -> CAction
make_set_com f [] [] c = (f c)
make_set_com f ((x,_,t):xs) (y:ys) c
  = (CSPCommAction (ChanComm ("mset_"++x)
     [ChanDotExp y]) (make_set_com f xs ys c))
\end{code}

\section{Local $MemoryMerge$ functions}
\subsection{$make\_lget\_com$}
This function will take the list of state variables $[ZName]$ that are free in an expression $e$, with no duplicates, and then make a $lget$ for each one, with a copy of such value with the prefix $v\_$. It will recurse until the point where a single element $x$ is left and then the prefixed action continues behaving like $c$.
\begin{circus}
make\_lget\_com\ (v_0,\ldots,v_n,l_0,\ldots,l_m)~A \defs
\\\t2 lget.v_0?vv_0 \then \ldots \then lget.v_n?vv_n \then
\\\t2 lget.l_0?vl_0 \then \ldots \then lget.l_m?vl_m \then A
\end{circus}
\begin{code}
make_lget_com :: [ZVar] -> CAction -> CAction
make_lget_com [(x,y,z)] c
  = (CSPCommAction (ChanComm ("lget"++x)
    [ChanInp ("v_"++x)]) c)
make_lget_com ((x,y,z):xs) c
  = (CSPCommAction (ChanComm ("lget"++x)
    [ChanInp ("v_"++x)]) (make_lget_com xs c))
make_lget_com x c = c
\end{code}
\subsection{$make\_lset\_com$}
This function updates the values of the $Memory$ process by generating a sequence of $lset$ communications and then it behaves like $f~c$, where $f$ may be the $omega\_CAction$ or $omega\_prime\_CAction$.
\begin{code}
make_lset_com :: (CAction -> CAction) -> [ZVar] -> [ZExpr] -> CAction -> CAction
make_lset_com f [(x,_,t)] [y] c
  = (CSPCommAction (ChanComm ("lset"++x)
    [ChanDotExp y]) (f c))
make_lset_com f ((x,_,t):xs) (y:ys) c
  = (CSPCommAction (ChanComm ("lset"++x)
     [ChanDotExp y]) (make_lset_com f xs ys c))
\end{code}

\subsection{$get\_guard\_pair$}

The function $get\_guard\_pair$ transform $CircGAction$ constructs into a list of tuples $(ZPred, CAction)$
\begin{code}
get_guard_pair :: CGActions -> [(ZPred, CAction)]
get_guard_pair (CircGAction g2 a2)
  = [(g2,a2)]
get_guard_pair (CircThenElse (CircGAction g2 a2) glx)
  = ((g2,a2):(get_guard_pair glx))
\end{code}
\subsection{$rename\_guard\_pair$}

The function $rename\_guard\_pair$ will rename the guards to $v\_$ prefix of free variables.

\begin{code}
rename_guard_pair :: [ZVar] -> [(ZPred, CAction)] -> [(ZPred, CAction)]
rename_guard_pair sub [(a,b)]
  = [((substitute (mk_sub_list sub) (free_vars a) a),b)]
rename_guard_pair sub ((a,b):xs) = [((substitute (mk_sub_list sub) (free_vars a) a),b)]++(rename_guard_pair sub xs)
\end{code}
\subsection{$mk\_guard\_pair$}

The function $mk\_guard\_pair$ transforms a list of tuples $(ZPred, CAction)$ and produces $CircThenElse$ pieces according to the size of the list.
\begin{code}
mk_guard_pair :: (CAction -> CAction) -> [(ZPred, CAction)] -> CGActions
mk_guard_pair f [(g,a)] = (CircGAction g (f a))
mk_guard_pair f ((g,a):ls) = (CircThenElse (CircGAction g (f a)) (mk_guard_pair f ls))
\end{code}
\subsection{$mk\_sub\_list$}

The function $mk\_sub\_list$ will make a list of substitution variables to $v\_$ prefix.
\begin{code}
mk_sub_list :: [ZVar] -> [(ZVar,ZExpr)]
mk_sub_list [] = []
mk_sub_list ((a,b,c):xs) = [((a,b,c),(ZVar ("v_"++a,b,c)))]++(mk_sub_list xs)
\end{code}
\subsection{Prototype of $wrtV(A)$, from D24.1.}
Prototype of $wrtV(A)$, from D24.1.
\begin{code}
-- TODO: Need to do it
wrtV :: CAction -> [ZName]
wrtV xs = []
\end{code}


\subsection{$mk\_sub\_list$}

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
rep_CSPRepParalNS a _ _ _ [x]
  = (CSPParAction a [x])
rep_CSPRepParalNS a cs ns y (x:xs)
  = (CSPNSParal [x] (CSExpr cs)
      [(ZSetComp
             [Choose y (ZSetDisplay xs)]
             (Just (ZCall (ZVar ns) (ZVar y))) )]
     (CSPParAction a [x]) (rep_CSPRepParalNS a cs ns y xs) )
\end{code}

Function used to propagate $CSPRepInterNS$ actions

\begin{code}
rep_CSPRepInterlNS :: ZName -> ZVar -> ZVar -> [ZExpr] -> CAction
rep_CSPRepInterlNS a _ _ [x]
  = (CSPParAction a [x])
rep_CSPRepInterlNS a ns y (x:xs)
  = (CSPNSInter [x]
    [(ZSetComp
           [Choose (ntrd y,[],[]) (ZSetDisplay xs)]
           (Just (ZCall (ZVar ns) (ZVar y))) )]
     (CSPParAction a [x]) (rep_CSPRepInterlNS a ns y xs) )
\end{code}
\subsection{Functions imported from $Data.List$}
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

-- Function that takes the last n elements of a string
-- used in order to get U_TYP from sv_StateName_VarName_U_TYP
lastN :: Int -> [a] -> [a]
lastN n xs = drop (length xs - n) xs
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


splitOn :: Eq a => a -> [a] -> [[a]]
splitOn d [] = []
splitOn d s = x : splitOn d (drop 1 y) where (x,y) = span (/= d) s

\end{code}
\section{Functions for manipulating the State}
\subsection{$get\_ZVar\_st$}
This function extracts those variables $ZVar$ that are a state variable member.
\begin{code}
get_ZVar_st x
  | is_ZVar_st (nfst x) = [x]
  | otherwise = []
\end{code}
\subsection{$is\_ZVar\_st$}

\begin{code}
is_ZVar_st a = isPrefixOf "sv" a || isPrefixOf "lv" a
is_Binding_var a = isPrefixOf "b_" a

is_ZVar_st' a "" = False
is_ZVar_st' a procn = isPrefixOf (join_name "sv" procn) a
\end{code}

\subsection{$is\_ZVar\_v\_st$}

\begin{code}
is_ZVar_v_st a = isPrefixOf "v_sv" a
is_ZVar_v_st' a procn = isPrefixOf (join_name "v_sv" procn)  a
\end{code}

\section{Functions for variable renaming -- $v\_$}

\subsection{$rename\_ZVar$}
Renames a $ZVar$ that is a state variable.

\begin{code}
rename_ZVar :: ([Char], t,t2) -> ([Char], t,t2)
rename_ZVar (va,x,y)
  = case (is_ZVar_st va) of
     True -> ("v_"++va,x,y)
     False -> (va,x,y)
\end{code}

\subsection{$rename\_ZExpr$}
Renames a $ZExpr$ where any $ZVar$ belonging to the state variable set will then be renamed with the $v\_$ prefix.

\begin{code}
rename_ZExpr :: ZExpr -> ZExpr
rename_ZExpr (ZVar (va,x,t))
 = (ZVar (rename_ZVar (va,x,t)))
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
\subsection{$bindingsVar$}
Auxiliary function for renaming, where any binding is renamed as well as its related $ZExpr$.
\begin{code}
bindingsVar :: [(ZVar, ZExpr)] -> [(ZVar, ZExpr)]

bindingsVar [] = []
bindingsVar (((va,x,t),b):xs)
 = case (is_ZVar_st va) of
   True -> [(("v_"++va,x,t),(rename_ZExpr b))]++(bindingsVar xs)
   False -> [((va,x,t),(rename_ZExpr b))]++(bindingsVar xs)
\end{code}

\subsection{$rename\_vars\_CParameter$}
Renaming any variable in a channel parameter.

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


\subsection{$CParameter$}
Renaming any variable in a channel parameter.
\begin{code}
rename_vars_Comm (ChanComm zn []) = (ChanComm zn [])
rename_vars_Comm (ChanComm zn (x:xs))
  | zn == "mget" = (ChanComm zn (x:(map rename_vars_CParameter xs)))
  | zn == "mset" = (ChanComm zn (x:(map rename_vars_CParameter xs)))
  | zn == "lget" = (ChanComm zn (x:(map rename_vars_CParameter xs)))
  | zn == "lset" = (ChanComm zn (x:(map rename_vars_CParameter xs)))
  | otherwise = (ChanComm zn (map rename_vars_CParameter (x:xs)))
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
% \subsection{Free Variables -- $FV(A)$. }
% Need to know how to calculate for Actions.
% \begin{code}
% getFV xs = []
% \end{code}

\subsection{Others -- No specific topic}

\begin{code}
subset xs ys = all (`elem` ys) xs
\end{code}
\subsection{Rewritting recursive \Circus\ Actions}
We are translating any recursive call into $CSPRecursion$ so we
can rewrite the main action without an infinite loop of rewritting
rules.

Firstly we define a function $isRecursive$ which looks for
any recursive call of a given \Circus\ Action.
\begin{code}
isRecursive_CAction :: ZName -> CAction -> Bool

isRecursive_CAction name (CActionCommand c)
 = isRecursive_CAction_comnd name c
isRecursive_CAction name (CActionName nm)
  | name == nm = True
  | otherwise = False
isRecursive_CAction name (CSPCommAction com c)
 = isRecursive_CAction name c
isRecursive_CAction name (CSPGuard p c)
 =isRecursive_CAction name c
isRecursive_CAction name (CSPSeq ca cb)
 = (isRecursive_CAction name ca) || (isRecursive_CAction name cb)
isRecursive_CAction name (CSPExtChoice ca cb)
 = (isRecursive_CAction name ca) || (isRecursive_CAction name cb)
isRecursive_CAction name (CSPIntChoice ca cb)
 = (isRecursive_CAction name ca) || (isRecursive_CAction name cb)
isRecursive_CAction name (CSPNSParal ns1 cs ns2 ca cb)
 = (isRecursive_CAction name ca) || (isRecursive_CAction name cb)
isRecursive_CAction name (CSPParal cs ca cb)
 = (isRecursive_CAction name ca) || (isRecursive_CAction name cb)
isRecursive_CAction name (CSPNSInter ns1 ns2 ca cb)
 = (isRecursive_CAction name ca) || (isRecursive_CAction name cb)
isRecursive_CAction name (CSPInterleave ca cb)
 = (isRecursive_CAction name ca) || (isRecursive_CAction name cb)
isRecursive_CAction name (CSPHide c cs)
 = isRecursive_CAction name c
isRecursive_CAction name (CSPRecursion n c)
 = isRecursive_CAction name c
isRecursive_CAction name (CSPUnfAction n c)
  | name == n = True
  | otherwise = False
isRecursive_CAction name (CSPUnParAction lsta c nm)
 = isRecursive_CAction name c
isRecursive_CAction name (CSPRepSeq lsta c)
 = isRecursive_CAction name c
isRecursive_CAction name (CSPRepExtChoice lsta c)
 = isRecursive_CAction name c
isRecursive_CAction name (CSPRepIntChoice lsta c)
 = isRecursive_CAction name c
isRecursive_CAction name (CSPRepParalNS cs lsta ns c)
 = isRecursive_CAction name c
isRecursive_CAction name (CSPRepParal cs lsta c)
 = isRecursive_CAction name c
isRecursive_CAction name (CSPRepInterlNS lsta ns c)
 = isRecursive_CAction name c
isRecursive_CAction name (CSPRepInterl lsta c)
 = isRecursive_CAction name c
isRecursive_CAction name (CActionSchemaExpr x)
 = False
isRecursive_CAction name (CSPSkip)
 = False
isRecursive_CAction name (CSPStop)
 = False
isRecursive_CAction name (CSPChaos)
 = False
isRecursive_CAction name (CSPParAction nm xp)
  | name == nm = True
  | otherwise = False
isRecursive_CAction name (CSPRenAction nm cr)
 = False
\end{code}
\begin{code}
isRecursive_CAction_comnd name (CAssign v e)
 = False
isRecursive_CAction_comnd name (CIf ga)
 = (isRecursive_if name ga)
isRecursive_CAction_comnd name (CVarDecl z a)
 = isRecursive_CAction name a
isRecursive_CAction_comnd name (CAssumpt n p1 p2)
 = False
isRecursive_CAction_comnd name (CAssumpt1 n p)
 = False
isRecursive_CAction_comnd name (CPrefix p1 p2)
 = False
isRecursive_CAction_comnd name (CPrefix1 p)
 = False
isRecursive_CAction_comnd name (CommandBrace p)
 = False
isRecursive_CAction_comnd name (CommandBracket p)
 = False
isRecursive_CAction_comnd name (CValDecl z a)
 = isRecursive_CAction name a
isRecursive_CAction_comnd name (CResDecl z a)
 = isRecursive_CAction name a
isRecursive_CAction_comnd name (CVResDecl z a)
 = isRecursive_CAction name a
\end{code}

\begin{code}
isRecursive_if name (CircGAction p a)
 = isRecursive_CAction name a
isRecursive_if name (CircThenElse ga gb)
 = (isRecursive_if name ga) || (isRecursive_if name gb)
\end{code}

\subsubsection{Renaming the recursive call and translating it into $CSPRecursion$}
We then rename the recursive call in order to make $\mu X \spot Action \seq X$.
\begin{code}
recursive_PPar (CParAction zn ca)
  | isRecursive_CAction zn (get_CircusAction ca)
        = (CParAction zn (makeRecursive_ParAction zn ca))
  | otherwise = (CParAction zn ca)
recursive_PPar (ProcZPara a)
  = (ProcZPara a)
recursive_PPar (CNameSet n ns)
  = (CNameSet n ns)

get_CircusAction (CircusAction ca) = ca
get_CircusAction (ParamActionDecl ls pa) = get_CircusAction pa
\end{code}

\begin{code}
makeRecursive_PPar (CParAction zn pa)
  = (CParAction zn (makeRecursive_ParAction zn pa))
makeRecursive_PPar (ProcZPara a)
  = (ProcZPara a)
makeRecursive_PPar (CNameSet n ns)
  = (CNameSet n ns)
\end{code}
\begin{code}
makeRecursive_ParAction name (CircusAction ca)
  = (CircusAction (makeRecursive_CAction name ca))
makeRecursive_ParAction name (ParamActionDecl ls pa)
  = (ParamActionDecl ls (makeRecursive_ParAction name pa))
\end{code}
\begin{code}
makeRecursive_CAction name c =  CSPRecursion ("mu"++name) (renameRecursive_CAction name c)
\end{code}
\begin{code}
renameRecursive_CAction :: ZName -> CAction -> CAction
renameRecursive_CAction name (CActionCommand c)
 = (CActionCommand (renameRecursive_CAction_comnd name c))
renameRecursive_CAction name (CActionName nm)
  | nm == name = (CActionName ("mu"++name))
  | otherwise = (CActionName nm)
renameRecursive_CAction name (CSPCommAction com c)
 = (CSPCommAction com (renameRecursive_CAction name c))
renameRecursive_CAction name (CSPGuard p c)
 = (CSPGuard p (renameRecursive_CAction name c))
renameRecursive_CAction name (CSPSeq ca cb)
 = (CSPSeq (renameRecursive_CAction name ca) (renameRecursive_CAction name cb))
renameRecursive_CAction name (CSPExtChoice ca cb)
 = (CSPExtChoice (renameRecursive_CAction name ca) (renameRecursive_CAction name cb))
renameRecursive_CAction name (CSPIntChoice ca cb)
 = (CSPIntChoice (renameRecursive_CAction name ca) (renameRecursive_CAction name cb))
renameRecursive_CAction name (CSPNSParal ns1 cs ns2 ca cb)
 = (CSPNSParal ns1 cs ns2 (renameRecursive_CAction name ca) (renameRecursive_CAction name cb))
renameRecursive_CAction name (CSPParal cs ca cb)
 = (CSPParal cs (renameRecursive_CAction name ca) (renameRecursive_CAction name cb))
renameRecursive_CAction name (CSPNSInter ns1 ns2 ca cb)
 = (CSPNSInter ns1 ns2 (renameRecursive_CAction name ca) (renameRecursive_CAction name cb))
renameRecursive_CAction name (CSPInterleave ca cb)
 = (CSPInterleave (renameRecursive_CAction name ca) (renameRecursive_CAction name cb))
renameRecursive_CAction name (CSPHide c cs)
 = (CSPHide (renameRecursive_CAction name c) cs)
renameRecursive_CAction name (CSPParAction nm xp)
  | nm == name = (CSPParAction ("mu"++nm) xp)
  | otherwise = (CSPParAction nm xp)
renameRecursive_CAction name (CSPRenAction nm cr)
 = (CSPRenAction nm cr)
renameRecursive_CAction name (CSPRecursion n c)
 = (CSPRecursion n (renameRecursive_CAction name c))
renameRecursive_CAction name (CSPUnParAction namea c nm)
 = (CSPUnParAction namea (renameRecursive_CAction name c) nm)
renameRecursive_CAction name (CSPRepSeq namea c)
 = (CSPRepSeq namea (renameRecursive_CAction name c))
renameRecursive_CAction name (CSPRepExtChoice namea c)
 = (CSPRepExtChoice namea (renameRecursive_CAction name c))
renameRecursive_CAction name (CSPRepIntChoice namea c)
 = (CSPRepIntChoice namea (renameRecursive_CAction name c))
renameRecursive_CAction name (CSPRepParalNS cs namea ns c)
 = (CSPRepParalNS cs namea ns (renameRecursive_CAction name c))
renameRecursive_CAction name (CSPRepParal cs namea c)
 = (CSPRepParal cs namea (renameRecursive_CAction name c))
renameRecursive_CAction name (CSPRepInterlNS namea ns c)
 = (CSPRepInterlNS namea ns (renameRecursive_CAction name c))
renameRecursive_CAction name (CSPRepInterl namea c)
 = (CSPRepInterl namea (renameRecursive_CAction name c))
renameRecursive_CAction _ x = x
\end{code}
\begin{code}
renameRecursive_CAction_comnd name (CAssign v e)
 = (CAssign v e)
renameRecursive_CAction_comnd name (CIf ga)
 = (CIf (renameRecursive_if name ga))
renameRecursive_CAction_comnd name (CVarDecl z a)
 = (CVarDecl z (renameRecursive_CAction name a))
renameRecursive_CAction_comnd name (CAssumpt n p1 p2)
 = (CAssumpt n p1 p2)
renameRecursive_CAction_comnd name (CAssumpt1 n p)
 = (CAssumpt1 n p)
renameRecursive_CAction_comnd name (CPrefix p1 p2)
 = (CPrefix p1 p2)
renameRecursive_CAction_comnd name (CPrefix1 p)
 = (CPrefix1 p)
renameRecursive_CAction_comnd name (CommandBrace p)
 = (CommandBrace p)
renameRecursive_CAction_comnd name (CommandBracket p)
 = (CommandBracket p)
renameRecursive_CAction_comnd name (CValDecl z a)
 = (CValDecl z (renameRecursive_CAction name a))
renameRecursive_CAction_comnd name (CResDecl z a)
 = (CResDecl z (renameRecursive_CAction name a))
renameRecursive_CAction_comnd name (CVResDecl z a)
 = (CVResDecl z (renameRecursive_CAction name a))
\end{code}

\begin{code}
renameRecursive_if name (CircGAction p a)
 = (CircGAction p (renameRecursive_CAction name a))
renameRecursive_if name (CircThenElse ga gb)
 = (CircThenElse (renameRecursive_if name ga) (renameRecursive_if name gb))
-- get_if name (CircElse (CircusAction a))
--  = (CircElse (CircusAction (renameRecursive_CAction name a)))
-- get_if name (CircElse (ParamActionDecl x (CircusAction a)))
--  = (CircElse (ParamActionDecl x (CircusAction (renameRecursive_CAction name a))))
\end{code}
\subsection{Expanding the main action}
\begin{code}
expand_action_names_PPar :: [PPar] -> [ZGenFilt] -> PPar -> PPar
expand_action_names_PPar lst param (ProcZPara zp)
  = (ProcZPara zp)
expand_action_names_PPar lst param (CParAction zn pa)
  = (CParAction zn (expand_action_names_ParAction lst param pa))
expand_action_names_PPar lst param (CNameSet zn ns)
  = (CNameSet zn ns)
\end{code}
\begin{code}
expand_action_names_ParAction :: [PPar] -> [ZGenFilt] -> ParAction -> ParAction
expand_action_names_ParAction lst param (CircusAction ca) = (CircusAction (expand_action_names_CAction lst param ca))-- Action
expand_action_names_ParAction lst param (ParamActionDecl ls pa) = (ParamActionDecl ls (expand_action_names_ParAction lst param pa))    -- Decl \circspot ParAction
\end{code}
\begin{code}
expand_action_names_CAction :: [PPar] -> [ZGenFilt] -> CAction -> CAction
expand_action_names_CAction lst param (CActionSchemaExpr x)
 = (CActionSchemaExpr x)
expand_action_names_CAction lst param (CActionCommand c)
 = (CActionCommand (expand_action_names_CAction_comnd lst param c))
expand_action_names_CAction lst param (CActionName nm)
  | (take 2 nm) == "mu" = (CActionName nm)
  | otherwise = get_action nm lst param lst
expand_action_names_CAction lst param (CSPSkip)
 = (CSPSkip)
expand_action_names_CAction lst param (CSPStop)
 = (CSPStop)
expand_action_names_CAction lst param (CSPChaos)
 = (CSPChaos)
expand_action_names_CAction lst param (CSPCommAction com c)
 = (CSPCommAction com (expand_action_names_CAction lst param c))
expand_action_names_CAction lst param (CSPGuard p c)
 = (CSPGuard p (expand_action_names_CAction lst param c))
expand_action_names_CAction lst param (CSPSeq ca cb)
 = (CSPSeq (expand_action_names_CAction lst param ca) (expand_action_names_CAction lst param cb))
expand_action_names_CAction lst param (CSPExtChoice ca cb)
 = (CSPExtChoice (expand_action_names_CAction lst param ca) (expand_action_names_CAction lst param cb))
expand_action_names_CAction lst param (CSPIntChoice ca cb)
 = (CSPIntChoice (expand_action_names_CAction lst param ca) (expand_action_names_CAction lst param cb))
expand_action_names_CAction lst param (CSPNSParal ns1 cs ns2 ca cb)
 = (CSPNSParal ns1 cs ns2 (expand_action_names_CAction lst param ca) (expand_action_names_CAction lst param cb))
expand_action_names_CAction lst param (CSPParal cs ca cb)
 = (CSPParal cs (expand_action_names_CAction lst param ca) (expand_action_names_CAction lst param cb))
expand_action_names_CAction lst param (CSPNSInter ns1 ns2 ca cb)
 = (CSPNSInter ns1 ns2 (expand_action_names_CAction lst param ca) (expand_action_names_CAction lst param cb))
expand_action_names_CAction lst param (CSPInterleave ca cb)
 = (CSPInterleave (expand_action_names_CAction lst param ca) (expand_action_names_CAction lst param cb))
expand_action_names_CAction lst param (CSPHide c cs)
 = (CSPHide (expand_action_names_CAction lst param c) cs)
expand_action_names_CAction lst param (CSPParAction nm xp)
 -- = (CSPParAction nm xp)
 | (take 2 nm) == "mu" = (CSPParAction nm xp)
 | otherwise = rename_action (get_action nm lst param lst) xp
expand_action_names_CAction lst param (CSPRenAction nm cr)
 = (CSPRenAction nm cr)
expand_action_names_CAction lst param (CSPRecursion n (CSPSeq c (CActionName n1)))
 = case n == n1 of
   True -> (CSPRecursion n (CSPSeq (expand_action_names_CAction lst param c) (CActionName n)))
   False -> (CSPRecursion n (CSPSeq (expand_action_names_CAction lst param c) (CActionName n1)))
expand_action_names_CAction lst param (CSPRecursion n c)
 = (CSPRecursion n (expand_action_names_CAction lst param c))
expand_action_names_CAction lst param (CSPUnParAction lsta c nm)
 = (CSPUnParAction lsta (expand_action_names_CAction lst param c) nm)
expand_action_names_CAction lst param (CSPRepSeq lsta c)
 = (CSPRepSeq lsta (expand_action_names_CAction lst param c))
expand_action_names_CAction lst param (CSPRepExtChoice lsta c)
 = (CSPRepExtChoice lsta (expand_action_names_CAction lst param c))
expand_action_names_CAction lst param (CSPRepIntChoice lsta c)
 = (CSPRepIntChoice lsta (expand_action_names_CAction lst param c))
expand_action_names_CAction lst param (CSPRepParalNS cs lsta ns c)
 = (CSPRepParalNS cs lsta ns (expand_action_names_CAction lst param c))
expand_action_names_CAction lst param (CSPRepParal cs lsta c)
 = (CSPRepParal cs lsta (expand_action_names_CAction lst param c))
expand_action_names_CAction lst param (CSPRepInterlNS lsta ns c)
 = (CSPRepInterlNS lsta ns (expand_action_names_CAction lst param c))
expand_action_names_CAction lst param (CSPRepInterl lsta c)
 = (CSPRepInterl lsta (expand_action_names_CAction lst param c))
expand_action_names_CAction lst param x = x
\end{code}
\begin{code}
expand_action_names_CAction_comnd lst param (CAssign v e)
 = (CAssign v e)
expand_action_names_CAction_comnd lst param (CIf ga)
 = (CIf (get_if lst param ga))
expand_action_names_CAction_comnd lst param (CVarDecl z a)
 = (CVarDecl z (expand_action_names_CAction lst param a))
expand_action_names_CAction_comnd lst param (CAssumpt n p1 p2)
 = (CAssumpt n p1 p2)
expand_action_names_CAction_comnd lst param (CAssumpt1 n p)
 = (CAssumpt1 n p)
expand_action_names_CAction_comnd lst param (CPrefix p1 p2)
 = (CPrefix p1 p2)
expand_action_names_CAction_comnd lst param (CPrefix1 p)
 = (CPrefix1 p)
expand_action_names_CAction_comnd lst param (CommandBrace p)
 = (CommandBrace p)
expand_action_names_CAction_comnd lst param (CommandBracket p)
 = (CommandBracket p)
expand_action_names_CAction_comnd lst param (CValDecl z a)
 = (CValDecl z (expand_action_names_CAction lst param a))
expand_action_names_CAction_comnd lst param (CResDecl z a)
 = (CResDecl z (expand_action_names_CAction lst param a))
expand_action_names_CAction_comnd lst param (CVResDecl z a)
 = (CVResDecl z (expand_action_names_CAction lst param a))
\end{code}

\begin{code}
get_if lst param (CircGAction p a)
 = (CircGAction p (expand_action_names_CAction lst param a))
get_if lst param (CircThenElse (CircGAction p a) gb)
 = (CircThenElse (CircGAction p (expand_action_names_CAction lst param a)) (get_if lst param gb))
-- get_if lst param (CircElse (CircusAction a))
--  = (CircElse (CircusAction (expand_action_names_CAction lst param a)))
-- get_if lst param (CircElse (ParamActionDecl x (CircusAction a)))
--  = (CircElse (ParamActionDecl x (CircusAction (expand_action_names_CAction lst param a))))
\end{code}
% 15/05/2018 - Artur
Here we replace the variable names of a CValDecl with the parameters of the action.
% let's see how it goes...
\begin{code}
-- get_action' :: ZName -> [PPar] -> [ZGenFilt] -> [PPar] -> [ZGenFilt] -> CAction
-- get_action _ _ _ [] = error "Action list is empty"
rename_action (CActionCommand (CValDecl zfs ma)) xfs
  = (replace_ParamAction_CAction1 ma (concat $ get_var_Choose zfs) xfs)
rename_action x xfs = x

get_var_Choose [] = []
get_var_Choose ((Choose a b):xs) = [a]:(get_var_Choose xs)
get_var_Choose (_:xs) = (get_var_Choose xs)

replace_ParamAction_CAction1 x [a] [b]
  = (repParamActionCAction a b x)
replace_ParamAction_CAction1 x (a:as) (b:bs)
  = replace_ParamAction_CAction1 (repParamActionCAction a b x) as bs
\end{code}
\begin{code}
get_action :: ZName -> [PPar] -> [ZGenFilt] -> [PPar] -> CAction
-- get_action _ _ _ [] = error "Action list is empty"
get_action name lst param [(CParAction n (CircusAction a))]
  | name == n = expand_action_names_CAction lst param a
  | otherwise = error ("Action "++(name)++" not found")
get_action name lst param ((CParAction n (CircusAction a)):xs)
  | (name == n) = expand_action_names_CAction lst param a
  | otherwise = get_action name lst param xs
get_action name lst param [(CParAction n (ParamActionDecl p (CircusAction a)))]
  | name == n = expand_action_names_CAction lst p a
  | otherwise = error ("Action "++(name)++" not found")
get_action name lst param ((CParAction n (ParamActionDecl p (CircusAction a))):xs)
  | (name == n) = expand_action_names_CAction lst p a
  | otherwise = get_action name lst param xs
get_action name lst param (_:xs)
  = get_action name lst param xs
get_action n _ _ [] = error ("Action list is empty"++n)
\end{code}

\begin{code}
getChanDotExpVar :: [CParameter] -> [ZExpr]
getChanDotExpVar [] = []
getChanDotExpVar ((ChanDotExp e):xs) = [e]++(get_chan_param xs)
getChanDotExpVar ((ChanOutExp e):xs) = [e]++(get_chan_param xs)
getChanDotExpVar (_:xs) = (get_chan_param xs)
\end{code}

\begin{code}
get_chan_param :: [CParameter] -> [ZExpr]
get_chan_param [] = []
get_chan_param [ChanDotExp (ZVar (x,_,t))]
 = [ZVar (x,[],t)]
get_chan_param [ChanOutExp (ZVar (x,_,t))]
 = [ZVar (x,[],t)]
get_chan_param [_]
 = []
get_chan_param ((ChanDotExp (ZVar (x,_,t))):xs)
 = [ZVar (x,[],t)]++(get_chan_param xs)
get_chan_param ((ChanOutExp (ZVar (x,_,t))):xs)
 = [ZVar (x,[],t)]++(get_chan_param xs)
get_chan_param (_:xs) = (get_chan_param xs)
\end{code}

\begin{code}
filter_state_comp :: [(ZName, ZVar, ZExpr)] -> [ZVar]
filter_state_comp [] = []
filter_state_comp [(_, v, _)] = [v]
filter_state_comp ((_, v, _):xs) = [v]++(filter_state_comp xs)
\end{code}

\subsubsection{rename vars}

\begin{code}
rename_vars_ParAction (CircusAction ca)
  = (CircusAction (rename_vars_CAction ca))
rename_vars_ParAction (ParamActionDecl zglst pa)
  = (ParamActionDecl zglst (rename_vars_ParAction pa))
\end{code}

\subsection{$[ZName]$ to $[ZExpr]$ - mainly converting to $ZVar (x,[],[])$}
\begin{code}
zname_to_zexpr [] = []
zname_to_zexpr [a] = [ZVar (a,[],[])]
zname_to_zexpr (a:as) = [ZVar (a,[],[])]++(zname_to_zexpr as)
\end{code}
\subsection{$[ZVar]$ to $[ZExpr]$}
\begin{code}
zvar_to_zexpr [] = []
zvar_to_zexpr [(a,[],t)] = [ZVar (a,[],t)]
zvar_to_zexpr ((a,[],t):as) = [ZVar (a,[],t)]++(zvar_to_zexpr as)
\end{code}
\subsection{$[ZGenFilt]$ to $[ZExpr]$}
\begin{code}

zgenfilt_to_zexpr [] = []
zgenfilt_to_zexpr [(Choose (a,[],tx) t)]
  = [ZVar (a,[],tx)]
zgenfilt_to_zexpr ((Choose (a,[],tx) t):as)
  = [ZVar (a,[],tx)]++(zgenfilt_to_zexpr as)
zgenfilt_to_zexpr (_:as) = []++(zgenfilt_to_zexpr as)
\end{code}
\subsubsection{rename vars}
%% You have to put here the remainder for Processes, so you can create on line 78
% of MappingFunStatelessCircus the definition of a renamed function for the
% Proc_var names of the variables before starting the mapping process.
\begin{code}
rename_vars_ZPara' :: [(ZName, ZVar, ZExpr)] -> ZPara -> ZPara
rename_vars_ZPara' lst (Process (CProcess zn pd))
  = (Process (CProcess zn (rename_vars_ProcessDef1 zn lst pd)))
rename_vars_ZPara' lst (Process (CParamProcess zn znls pd))
  = (Process (CParamProcess zn znls (rename_vars_ProcessDef1 zn lst pd)))
rename_vars_ZPara' lst (Process (CGenProcess zn znls pd))
  = (Process (CParamProcess zn znls (rename_vars_ProcessDef1 zn lst pd)))
rename_vars_ZPara' lst x = x

rename_vars_ZPara1 :: String ->  [(ZName, ZVar, ZExpr)] -> ZPara -> ZPara
rename_vars_ZPara1 pn lst (ZSchemaDef zn xp)
  = (ZSchemaDef zn (rename_vars_ZSExpr1 pn lst xp))
rename_vars_ZPara1 pn lst x = x
\end{code}

\begin{code}
rename_vars_ZSExpr1 :: String ->  [(ZName, ZVar, ZExpr)] -> ZSExpr -> ZSExpr
rename_vars_ZSExpr1 pn lst (ZSchema s)
  = ZSchema (map (rename_ZGenFilt1 pn  lst) s)
rename_vars_ZSExpr1 pn lst x = x
\end{code}

\begin{code}
rename_vars_ProcDecl1 :: String ->  [(ZName, ZVar, ZExpr)] -> ProcDecl -> ProcDecl
rename_vars_ProcDecl1 pn lst (CProcess zn pd)
  = (CProcess zn (rename_vars_ProcessDef1 pn lst pd))
rename_vars_ProcDecl1 pn lst (CParamProcess zn znls pd)
  = (CParamProcess zn znls (rename_vars_ProcessDef1 pn lst pd))
rename_vars_ProcDecl1 pn lst (CGenProcess zn znls pd)
  = (CParamProcess zn znls (rename_vars_ProcessDef1 pn lst pd))
\end{code}

\begin{code}
rename_vars_ProcessDef1 :: String ->  [(ZName, ZVar, ZExpr)] -> ProcessDef -> ProcessDef
rename_vars_ProcessDef1 pn lst (ProcDefSpot zgf pd)
  = (ProcDefSpot zgf (rename_vars_ProcessDef1 pn lst pd))
rename_vars_ProcessDef1 pn lst (ProcDefIndex zgf pd)
  = (ProcDefIndex zgf (rename_vars_ProcessDef1 pn lst pd))
rename_vars_ProcessDef1 pn lst (ProcDef cp)
  = (ProcDef (rename_vars_CProc1 pn lst cp))
\end{code}

\begin{code}
rename_vars_CProc1 :: String ->  [(ZName, ZVar, ZExpr)] -> CProc -> CProc
rename_vars_CProc1 pn lst (CRepSeqProc zgf cp)
  = (CRepSeqProc zgf (rename_vars_CProc1 pn lst cp))
rename_vars_CProc1 pn lst (CRepExtChProc zgf cp)
  = (CRepExtChProc zgf (rename_vars_CProc1 pn lst cp))
rename_vars_CProc1 pn lst (CRepIntChProc zgf cp)
  = (CRepIntChProc zgf (rename_vars_CProc1 pn lst cp))
rename_vars_CProc1 pn lst (CRepParalProc cs zgf cp)
  = (CRepParalProc cs zgf (rename_vars_CProc1 pn lst cp))
rename_vars_CProc1 pn lst (CRepInterlProc zgf cp)
  = (CRepInterlProc zgf (rename_vars_CProc1 pn lst cp))
rename_vars_CProc1 pn lst (CHide cp cxp)
  = (CHide (rename_vars_CProc1 pn lst cp) cxp)
rename_vars_CProc1 pn lst (CExtChoice cp1 cp2)
  = (CExtChoice (rename_vars_CProc1 pn lst cp1) (rename_vars_CProc1 pn lst cp2))
rename_vars_CProc1 pn lst (CIntChoice cp1 cp2)
  = (CIntChoice (rename_vars_CProc1 pn lst cp1) (rename_vars_CProc1 pn lst cp2))
rename_vars_CProc1 pn lst (CParParal cs cp1 cp2)
  = (CParParal cs (rename_vars_CProc1 pn lst cp1) (rename_vars_CProc1 pn lst cp2))
rename_vars_CProc1 pn lst (CInterleave cp1 cp2)
  = (CInterleave (rename_vars_CProc1 pn lst cp1) (rename_vars_CProc1 pn lst cp2))
rename_vars_CProc1 pn lst (CGenProc zn zxp)
  = (CGenProc zn zxp)
rename_vars_CProc1 pn lst (CParamProc zn zxp)
  = (CParamProc zn zxp)
rename_vars_CProc1 pn lst (CProcRename zn c1 c2)
  = (CProcRename zn c1 c2)
rename_vars_CProc1 pn lst (CSeq cp1 cp2)
  = (CSeq (rename_vars_CProc1 pn lst cp1) (rename_vars_CProc1 pn lst cp2))
rename_vars_CProc1 pn lst (CSimpIndexProc zn zxp)
  = (CSimpIndexProc zn zxp)
rename_vars_CProc1 pn lst (CircusProc zn)
  = (CircusProc zn)
rename_vars_CProc1 pn lst (ProcMain zp ppl ca)
  = (ProcMain (rename_vars_ZPara1 pn lst zp) (map (rename_vars_PPar1 pn lst) ppl) (rename_vars_CAction1 pn lst ca))
rename_vars_CProc1 pn lst (ProcStalessMain ppl ca)
  = (ProcStalessMain ppl (rename_vars_CAction1 pn lst ca))
\end{code}


\subsubsection{Circus Actions}
\begin{code}
rename_vars_PPar1 :: String ->  [(ZName, ZVar, ZExpr)] -> PPar -> PPar
rename_vars_PPar1 pn lst (ProcZPara zp)
  = (ProcZPara zp)
rename_vars_PPar1 pn lst (CParAction zn pa)
  = (CParAction zn (rename_vars_ParAction1 pn lst pa))
rename_vars_PPar1 pn lst (CNameSet zn ns)
  = (CNameSet zn ns)
\end{code}

\begin{code}
rename_vars_ParAction1 :: String ->  [(ZName, ZVar, ZExpr)] -> ParAction -> ParAction
rename_vars_ParAction1 pn lst (CircusAction ca)
  = (CircusAction (rename_vars_CAction1 pn lst ca))
rename_vars_ParAction1 pn lst (ParamActionDecl zgf pa)
  = (ParamActionDecl zgf (rename_vars_ParAction1 pn lst pa))
\end{code}

\begin{code}
rename_vars_CAction1 :: String ->  [(ZName, ZVar, ZExpr)] -> CAction -> CAction
rename_vars_CAction1 pn lst (CActionSchemaExpr zsexp)
 = (CActionSchemaExpr zsexp)
rename_vars_CAction1 pn lst (CActionCommand cmd)
 = (CActionCommand (rename_vars_CCommand1 pn lst cmd))
rename_vars_CAction1 pn lst (CActionName zn)
 = (CActionName zn)
rename_vars_CAction1 pn lst (CSPSkip )
 = (CSPSkip )
rename_vars_CAction1 pn lst (CSPStop )
 = (CSPStop )
rename_vars_CAction1 pn lst (CSPChaos)
 = (CSPChaos)
rename_vars_CAction1 pn lst (CSPCommAction c a)
 = (CSPCommAction (rename_vars_Comm1 pn lst c) (rename_vars_CAction1 pn lst a))
rename_vars_CAction1 pn lst (CSPGuard zp a)
 = (CSPGuard (rename_vars_ZPred1 pn lst zp) (rename_vars_CAction1 pn lst a))
rename_vars_CAction1 pn lst (CSPSeq a1 a2)
 = (CSPSeq (rename_vars_CAction1 pn lst a1) (rename_vars_CAction1 pn lst a2))
rename_vars_CAction1 pn lst (CSPExtChoice a1 a2)
 = (CSPExtChoice (rename_vars_CAction1 pn lst a1) (rename_vars_CAction1 pn lst a2))
rename_vars_CAction1 pn lst (CSPIntChoice a1 a2)
 = (CSPIntChoice (rename_vars_CAction1 pn lst a1) (rename_vars_CAction1 pn lst a2))
rename_vars_CAction1 pn lst (CSPNSParal ns1 cs ns2 a1 a2)
 = (CSPNSParal (map (rename_vars_ZExpr1 pn lst) ns1) cs (map (rename_vars_ZExpr1 pn lst) ns2) (rename_vars_CAction1 pn lst a1) (rename_vars_CAction1 pn lst a2))
rename_vars_CAction1 pn lst (CSPParal cs a1 a2)
 = (CSPParal cs (rename_vars_CAction1 pn lst a1) (rename_vars_CAction1 pn lst a2))
rename_vars_CAction1 pn lst (CSPNSInter ns1 ns2 a1 a2)
 = (CSPNSInter (map (rename_vars_ZExpr1 pn lst) ns1) (map (rename_vars_ZExpr1 pn lst) ns2) (rename_vars_CAction1 pn lst a1) (rename_vars_CAction1 pn lst a2))
rename_vars_CAction1 pn lst (CSPInterleave a1 a2)
 = (CSPInterleave (rename_vars_CAction1 pn lst a1) (rename_vars_CAction1 pn lst a2))
rename_vars_CAction1 pn lst (CSPHide a cs)
 = (CSPHide (rename_vars_CAction1 pn lst a) cs)
rename_vars_CAction1 pn lst (CSPParAction zn zexprls)
 = (CSPParAction zn (map (rename_vars_ZExpr1 pn lst) zexprls))
rename_vars_CAction1 pn lst (CSPRenAction zn crpl)
 = (CSPRenAction zn (rename_vars_CReplace1 pn lst crpl))
rename_vars_CAction1 pn lst (CSPRecursion zn a)
 = (CSPRecursion zn (rename_vars_CAction1 pn lst a))
rename_vars_CAction1 pn lst (CSPUnParAction zgf a zn)
 = (CSPUnParAction (map (rename_vars_ZGenFilt1 pn lst) zgf) (rename_vars_CAction1 pn lst a) zn)
rename_vars_CAction1 pn lst (CSPRepSeq zgf a)
 = (CSPRepSeq zgf (rename_vars_CAction1 pn lst a))
rename_vars_CAction1 pn lst (CSPRepExtChoice zgf a)
 = (CSPRepExtChoice (map (rename_vars_ZGenFilt1 pn lst) zgf) (rename_vars_CAction1 pn lst a))
rename_vars_CAction1 pn lst (CSPRepIntChoice zgf a)
 = (CSPRepIntChoice (map (rename_vars_ZGenFilt1 pn lst) zgf) (rename_vars_CAction1 pn lst a))
rename_vars_CAction1 pn lst (CSPRepParalNS cs zgf ns a)
 = (CSPRepParalNS cs (map (rename_vars_ZGenFilt1 pn lst) zgf) ns (rename_vars_CAction1 pn lst a))
rename_vars_CAction1 pn lst (CSPRepParal cs zgf a)
 = (CSPRepParal cs (map (rename_vars_ZGenFilt1 pn lst) zgf) (rename_vars_CAction1 pn lst a))
rename_vars_CAction1 pn lst (CSPRepInterlNS zgf ns a)
 = (CSPRepInterlNS (map (rename_vars_ZGenFilt1 pn lst) zgf) ns (rename_vars_CAction1 pn lst a))
rename_vars_CAction1 pn lst (CSPRepInterl zgf a)
 = (CSPRepInterl (map (rename_vars_ZGenFilt1 pn lst) zgf) (rename_vars_CAction1 pn lst a))
rename_vars_CAction1 pn lst x = x



rename_vars_ZGenFilt1 pn  lst (Include s) = (Include s)
rename_vars_ZGenFilt1 pn  lst (Choose va e)
  = (Choose va (rename_vars_ZExpr1 pn lst e))
    where newt = (def_U_prefix $ get_vars_ZExpr e)
rename_vars_ZGenFilt1 pn  lst (Check p) = (Check (rename_vars_ZPred1 pn lst p))
rename_vars_ZGenFilt1 pn  lst (Evaluate v e1 e2) = (Evaluate v (rename_vars_ZExpr1 pn lst e1) (rename_vars_ZExpr1 pn lst e2))
\end{code}

\begin{code}
rename_vars_Comm1 :: String ->  [(ZName, ZVar, ZExpr)] -> Comm -> Comm
rename_vars_Comm1 pn lst (ChanComm zn cpls)
 = (ChanComm zn (map (rename_vars_CParameter1 pn lst) cpls))
rename_vars_Comm1 pn lst (ChanGenComm zn zexprls cpls)
 = (ChanGenComm zn (map (rename_vars_ZExpr1 pn lst) zexprls) (map (rename_vars_CParameter1 pn lst) cpls))
\end{code}

\begin{code}
rename_vars_CParameter1 :: String ->  [(ZName, ZVar, ZExpr)] -> CParameter -> CParameter
rename_vars_CParameter1 pn lst (ChanInp zn)
 = case (inListVar1 zn lst) of
  True -> (ChanInp $ nfst (rename_vars_ZVar1 pn lst (zn,[],"")))
  _ -> (ChanInp zn)
rename_vars_CParameter1 pn lst (ChanInpPred zn zp)
 = case (inListVar1 zn lst) of
  True -> (ChanInpPred (join_name (get_proc_name zn lst) zn) (rename_vars_ZPred1 pn lst zp))
  _ -> (ChanInpPred zn zp)
rename_vars_CParameter1 pn lst (ChanOutExp ze)
 = (ChanOutExp (rename_vars_ZExpr1 pn lst ze))
rename_vars_CParameter1 pn lst (ChanDotExp ze)
 = (ChanDotExp (rename_vars_ZExpr1 pn lst ze))
\end{code}

\begin{code}
rename_vars_CCommand1 :: String ->  [(ZName, ZVar, ZExpr)] -> CCommand -> CCommand
rename_vars_CCommand1 pn lst (CAssign zv ze)
 = (CAssign (map (rename_vars_ZVar1 pn lst) zv)
            (map (rename_vars_ZExpr1 pn lst) ze))
rename_vars_CCommand1 pn lst (CIf ga)
 = (CIf (rename_vars_CGActions1 pn lst ga))
rename_vars_CCommand1 pn lst (CVarDecl zgf a)
 = (CVarDecl zgf (rename_vars_CAction1 pn lst a))
rename_vars_CCommand1 pn lst (CAssumpt znls zp1 zp2)
 = (CAssumpt znls (rename_vars_ZPred1 pn lst zp1) zp2)
rename_vars_CCommand1 pn lst (CAssumpt1 znls zp)
 = (CAssumpt1 znls zp)
rename_vars_CCommand1 pn lst (CPrefix zp1 zp2)
 = (CPrefix (rename_vars_ZPred1 pn lst zp1) zp2)
rename_vars_CCommand1 pn lst (CPrefix1 zp)
 = (CPrefix1 zp)
rename_vars_CCommand1 pn lst (CommandBrace zp)
 = (CommandBrace zp)
rename_vars_CCommand1 pn lst (CommandBracket zp)
 = (CommandBracket zp)
rename_vars_CCommand1 pn lst (CValDecl zgf a)
 = (CValDecl zgf (rename_vars_CAction1 pn lst a))
rename_vars_CCommand1 pn lst (CResDecl zgf a)
 = (CResDecl zgf (rename_vars_CAction1 pn lst a))
rename_vars_CCommand1 pn lst (CVResDecl zgf a)
 = (CVResDecl zgf (rename_vars_CAction1 pn lst a))
\end{code}

\begin{code}
rename_vars_CGActions1 :: String ->  [(ZName, ZVar, ZExpr)] -> CGActions -> CGActions
rename_vars_CGActions1 pn lst (CircGAction zp a)
 = (CircGAction (rename_vars_ZPred1 pn lst zp) (rename_vars_CAction1 pn lst a))
rename_vars_CGActions1 pn lst (CircThenElse (CircGAction zp a) cga2)
 = (CircThenElse (CircGAction (rename_vars_ZPred1 pn lst zp) (rename_vars_CAction1 pn lst a)) (rename_vars_CGActions1 pn lst cga2))
-- rename_vars_CGActions1 pn lst (CircElse pa)
-- = (CircElse pa)
\end{code}

\begin{code}
rename_vars_CReplace1 :: String ->  [(ZName, ZVar, ZExpr)] -> CReplace -> CReplace
rename_vars_CReplace1 pn lst (CRename zvarls1 zvarls)
 = (CRename zvarls1 zvarls)
rename_vars_CReplace1 pn lst (CRenameAssign zvarls1 zvarls)
 = (CRenameAssign zvarls1 zvarls)
\end{code}

\begin{code}
bindingsVar1 pn lst []
 = []
bindingsVar1 pn lst (((va,x,t),b):xs)
 = [(((join_name pn va),x,t),(rename_vars_ZExpr1 pn lst b))]++(bindingsVar1 pn lst xs)
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
inListVar1 x [(a,(va,x1,_),b)]
 = case x == va of
  True -> True
  _ -> False
inListVar1 x ((a,(va,x1,_),b):vst)
 = case x == va of
  True -> True
  _ -> inListVar1 x vst
\end{code}

\begin{code}
get_proc_name :: ZName -> [(ZName, ZVar, ZExpr)] -> ZName
get_proc_name x [(a,(va,x1,_),b)]
 = case x == va of
  True -> a
  _ -> ""
get_proc_name x ((a,(va,x1,_),b):vst)
 = case x == va of
  True -> a
  _ -> get_proc_name x vst

get_var_type :: ZName -> [(ZName, ZVar, ZExpr)] -> ZExpr
get_var_type x [(a,(va,x1,_),b)]
 = case x == va of
  True -> b
  _ -> error "type not found whilst get_var_type"
get_var_type x ((a,(va,x1,_),b):vst)
 = case x == va of
  True -> b
  _ -> get_var_type x vst
\end{code}

\begin{code}
rename_ZGenFilt1 pn  lst (Include s) = (Include s)
rename_ZGenFilt1 pn  lst (Choose (va,x,t) e)
  = (Choose ((join_name "sv" va),x,newt) (rename_vars_ZExpr1 pn lst e))
    where newt = (def_U_prefix $ get_vars_ZExpr e)
rename_ZGenFilt1 pn  lst (Check p) = (Check (rename_vars_ZPred1 pn lst p))
rename_ZGenFilt1 pn  lst (Evaluate v e1 e2) = (Evaluate v (rename_vars_ZExpr1 pn lst e1) (rename_vars_ZExpr1 pn lst e2))
\end{code}
\begin{code}
rename_vars_ZVar1 :: String ->  [(ZName, ZVar, ZExpr)] -> ZVar -> ZVar
rename_vars_ZVar1 pn lst (va,x,t)
 = case (inListVar1 va lst) of
    True -> ((join_name "sv" va),x,newt)
    _ -> (va,x,t)
    where newt = (def_U_prefix $ get_vars_ZExpr $ get_var_type va lst)
\end{code}
\begin{code}
rename_vars_ZExpr1 :: String ->  [(ZName, ZVar, ZExpr)] -> ZExpr -> ZExpr
rename_vars_ZExpr1 pn lst (ZVar v)
 = ZVar (rename_vars_ZVar1 pn lst v)
rename_vars_ZExpr1 pn lst (ZInt zi)
 = (ZInt zi)
rename_vars_ZExpr1 pn lst (ZGiven gv)
 = (ZGiven gv)
rename_vars_ZExpr1 pn lst (ZFree0 va)
 = (ZFree0 va)
rename_vars_ZExpr1 pn lst (ZFree1 va xpr)
 = (ZFree1 va (rename_vars_ZExpr1 pn lst xpr))
rename_vars_ZExpr1 pn lst (ZTuple xpr)
 = (ZTuple (map (rename_vars_ZExpr1 pn lst) xpr))
rename_vars_ZExpr1 pn lst (ZBinding xs)
 = (ZBinding (bindingsVar1 pn lst xs))
rename_vars_ZExpr1 pn lst (ZSetDisplay xpr)
 = (ZSetDisplay (map (rename_vars_ZExpr1 pn lst) xpr))
rename_vars_ZExpr1 pn lst (ZSeqDisplay xpr)
 = (ZSeqDisplay (map (rename_vars_ZExpr1 pn lst) xpr))
rename_vars_ZExpr1 pn lst (ZFSet zf)
 = (ZFSet zf)
rename_vars_ZExpr1 pn lst (ZIntSet i1 i2)
 = (ZIntSet i1 i2)
rename_vars_ZExpr1 pn lst (ZGenerator zrl xpr)
 = (ZGenerator zrl (rename_vars_ZExpr1 pn lst xpr))
rename_vars_ZExpr1 pn lst (ZCross xpr)
 = (ZCross (map (rename_vars_ZExpr1 pn lst) xpr))
rename_vars_ZExpr1 pn lst (ZFreeType va pname1)
 = (ZFreeType va pname1)
rename_vars_ZExpr1 pn lst (ZPowerSet{baseset=xpr, is_non_empty=b1, is_finite=b2})
 = (ZPowerSet{baseset=(rename_vars_ZExpr1 pn lst xpr), is_non_empty=b1, is_finite=b2})
rename_vars_ZExpr1 pn lst (ZFuncSet{ domset=expr1, ranset=expr2, is_function=b1, is_total=b2, is_onto=b3, is_one2one=b4, is_sequence=b5, is_non_empty=b6, is_finite=b7})
 = (ZFuncSet{ domset=(rename_vars_ZExpr1 pn lst expr1), ranset=(rename_vars_ZExpr1 pn lst expr2), is_function=b1, is_total=b2, is_onto=b3, is_one2one=b4, is_sequence=b5, is_non_empty=b6, is_finite=b7})
rename_vars_ZExpr1 pn lst (ZSetComp pname1 (Just xpr))
 = (ZSetComp (map (rename_ZGenFilt1 pn  lst) pname1) (Just (rename_vars_ZExpr1 pn lst xpr)))
rename_vars_ZExpr1 pn lst (ZSetComp pname1 Nothing)
 = (ZSetComp (map (rename_ZGenFilt1 pn  lst) pname1) Nothing)
rename_vars_ZExpr1 pn lst (ZLambda pname1 xpr)
 = (ZLambda (map (rename_ZGenFilt1 pn  lst) pname1) (rename_vars_ZExpr1 pn lst xpr))
rename_vars_ZExpr1 pn lst (ZESchema zxp)
 = (ZESchema zxp)
rename_vars_ZExpr1 pn lst (ZGivenSet gs)
 = (ZGivenSet gs)
rename_vars_ZExpr1 pn lst (ZUniverse)
 = (ZUniverse)
rename_vars_ZExpr1 pn lst (ZCall xpr1 xpr2)
 = (ZCall (rename_vars_ZExpr1 pn lst xpr1) (rename_vars_ZExpr1 pn lst xpr2))
rename_vars_ZExpr1 pn lst (ZReln rl)
 = (ZReln rl)
rename_vars_ZExpr1 pn lst (ZFunc1 f1)
 = (ZFunc1 f1)
rename_vars_ZExpr1 pn lst (ZFunc2 f2)
 = (ZFunc2 f2)
rename_vars_ZExpr1 pn lst (ZStrange st)
 = (ZStrange st)
rename_vars_ZExpr1 pn lst (ZMu pname1 (Just xpr))
 = (ZMu (map (rename_ZGenFilt1 pn  lst) pname1) (Just (rename_vars_ZExpr1 pn lst xpr)))
rename_vars_ZExpr1 pn lst (ZELet pname1 xpr1)
 = (ZELet (bindingsVar1 pn lst pname1) (rename_vars_ZExpr1 pn lst xpr1))
rename_vars_ZExpr1 pn lst (ZIf_Then_Else zp xpr1 xpr2)
 = (ZIf_Then_Else zp (rename_vars_ZExpr1 pn lst xpr1) (rename_vars_ZExpr1 pn lst xpr2))
rename_vars_ZExpr1 pn lst (ZSelect xpr va)
 = (ZSelect xpr va)
rename_vars_ZExpr1 pn lst (ZTheta zs)
 = (ZTheta zs)
\end{code}


\begin{code}
rename_vars_ZPred1 :: String ->  [(ZName, ZVar, ZExpr)] -> ZPred -> ZPred
rename_vars_ZPred1 pn lst (ZFalse{reason=a})
 = (ZFalse{reason=a})
rename_vars_ZPred1 pn lst (ZTrue{reason=a})
 = (ZTrue{reason=a})
rename_vars_ZPred1 pn lst (ZAnd p1 p2)
 = (ZAnd (rename_vars_ZPred1 pn lst p1) (rename_vars_ZPred1 pn lst p2))
rename_vars_ZPred1 pn lst (ZOr p1 p2)
 = (ZOr (rename_vars_ZPred1 pn lst p1) (rename_vars_ZPred1 pn lst p2))
rename_vars_ZPred1 pn lst (ZImplies p1 p2)
 = (ZImplies (rename_vars_ZPred1 pn lst p1) (rename_vars_ZPred1 pn lst p2))
rename_vars_ZPred1 pn lst (ZIff p1 p2)
 = (ZIff (rename_vars_ZPred1 pn lst p1) (rename_vars_ZPred1 pn lst p2))
rename_vars_ZPred1 pn lst (ZNot p)
 = (ZNot (rename_vars_ZPred1 pn lst p))
rename_vars_ZPred1 pn lst (ZExists pname1 p)
 = (ZExists pname1 (rename_vars_ZPred1 pn lst p))
rename_vars_ZPred1 pn lst (ZExists_1 lst1 p)
 = (ZExists_1 lst1 (rename_vars_ZPred1 pn lst p))
rename_vars_ZPred1 pn lst (ZForall pname1 p)
 = (ZForall pname1 (rename_vars_ZPred1 pn lst p))
rename_vars_ZPred1 pn lst (ZPLet varxp p)
 = (ZPLet varxp (rename_vars_ZPred1 pn lst p))
rename_vars_ZPred1 pn lst (ZEqual xpr1 xpr2)
 = (ZEqual (rename_vars_ZExpr1 pn lst xpr1) (rename_vars_ZExpr1 pn lst xpr2))
rename_vars_ZPred1 pn lst (ZMember xpr1 xpr2)
 = (ZMember (rename_vars_ZExpr1 pn lst xpr1) (rename_vars_ZExpr1 pn lst xpr2))
rename_vars_ZPred1 pn lst (ZPre sp)
 = (ZPre sp)
rename_vars_ZPred1 pn lst (ZPSchema sp)
 = (ZPSchema sp)
\end{code}


\begin{code}
-- extract the delta variables in here'
get_delta_names1 :: [ZPara] -> [String]
get_delta_names1 [(ZFreeTypeDef ("NAME",[],_) xs)]
  = get_delta_names_aux1 xs
get_delta_names1 ((ZFreeTypeDef ("NAME",[],_) xs):xss)
  = (get_delta_names_aux1 xs)++(get_delta_names1 xss)
get_delta_names1 (_:xs)
  = (get_delta_names1 xs)
get_delta_names1 []
  = []
\end{code}

\begin{code}
get_delta_names_aux1 :: [ZBranch] -> [String]
get_delta_names_aux1 [] = []
get_delta_names_aux1 [(ZBranch0 (a,[],_))] = [a]
get_delta_names_aux1 [_] = []
get_delta_names_aux1 ((ZBranch0 (a,[],_)):xs) = [a]++(get_delta_names_aux1 xs)
get_delta_names_aux1 (_:xs) = (get_delta_names_aux1 xs)
\end{code}
\begin{code}
-- extract the delta variables in here' from the same state
get_delta_names zn [(ZFreeTypeDef ("NAME",[],_) xs)]
  = get_delta_names_aux zn xs
get_delta_names zn ((ZFreeTypeDef ("NAME",[],_) xs):xss)
  = (get_delta_names_aux zn xs)++(get_delta_names zn xss)
get_delta_names zn (_:xs)
  = (get_delta_names zn xs)
get_delta_names _ []
  = []
\end{code}

\begin{code}
get_delta_names_aux procn [(ZBranch0 (a,[],_))]
  | is_ZVar_st' a procn = [a]
  | otherwise = []
get_delta_names_aux procn ((ZBranch0 (a,[],_)):xs)
  | is_ZVar_st' a procn = [a]++(get_delta_names_aux procn xs)
  | otherwise = (get_delta_names_aux procn xs)
\end{code}

Construction of the Universe set in CSP
\begin{code}

-- Make UNIVERSE datatype in CSP
get_u_tag_ZBranch [] = []
get_u_tag_ZBranch ((ZBranch1 (tag,_,_) x):xs)
  = tag : (get_u_tag_ZBranch xs)
get_u_tag_ZBranch (_:xs) = get_u_tag_ZBranch xs


mk_universe [] = ""
mk_universe [(a,b,c,d)] = c++"."++d
mk_universe ((a,b,c,d):xs)
  = c++"."++d++" | "++(mk_universe xs)

-- Make subtype U_TYP = TYP.TYPE
mk_subtype []
  = ""
mk_subtype [(a,b,c,d)]
  = "subtype "++b++" = "++c++"."++d++"\n"
mk_subtype ((a,b,c,d):xs)
  = "subtype "++b++" = "++c++"."++d++"\n"++(mk_subtype xs)

-- Make value(XXX.v) function call
-- This won't be used anymore in the next commit - 21.03.17
mk_value []
  = ""
mk_value (a:xs)
  = "value"++a++"("++a++".v) = v\n"++(mk_value xs)

-- Make type(x) function call
-- This won't be used anymore in the next commit - 21.03.17

mk_type []
  = ""
mk_type (a:xs)
  = "type"++a++"(x) = U_"++a++"\n"++(mk_type xs)

-- Make tag(x) function call
mk_tag []
  = ""
mk_tag (a:xs)
  = "tag"++a++"(x) = "++a++"\n"++(mk_tag xs)

-- make Memory(b_type1,b_type2,b_type3) parameters
mk_mem_param :: [String] -> String
mk_mem_param [] = ""
mk_mem_param [b] = "b_"++(lastN 3 b)
mk_mem_param (b:xs)
  = (mk_mem_param [b]) ++", "++ (mk_mem_param xs)

-- list of b_type parameters
mk_mem_param_lst :: [String] -> [String]
mk_mem_param_lst [] = []
mk_mem_param_lst [b] = ["b_"++(lastN 3 b)]
mk_mem_param_lst (b:xs)
  = (mk_mem_param_lst [b]) ++ (mk_mem_param_lst xs)

-- replace b_type by over(b_type,n,x) in case x == a
repl_mem_param_over :: [Char] -> [[Char]] -> [[Char]]
repl_mem_param_over _ [] = []
repl_mem_param_over a [x]
  | (lastN 3 x) == a  = ["over("++x++",n,x)"]
  | otherwise = [x]
repl_mem_param_over a (x:xs)
  = (repl_mem_param_over a [x]) ++ (repl_mem_param_over a xs)

-- list of b_type parameters into string of b_type1,b_type2,...
mk_charll_to_charl :: [Char] -> [[Char]] -> [Char]
mk_charll_to_charl _ [] = ""
mk_charll_to_charl sp [x] = x
mk_charll_to_charl sp (x:xs) = x++sp++(mk_charll_to_charl sp xs)

-- make mget external choices of Memory proc
mk_mget_mem_bndg :: [String] -> String
mk_mget_mem_bndg fs = mk_mget_mem_bndg' fs fs

mk_mget_mem_bndg' :: [String] -> [String] -> String
mk_mget_mem_bndg' fs []
  = ""
mk_mget_mem_bndg' fs [b]
  = "([] n:dom(b_"++(lastN 3 b)++") @ mget.n!(apply(b_"++(lastN 3 b)++",n)) -> Memory("++(mk_mem_param fs)++"))"
mk_mget_mem_bndg' fs (b:xs)
  = mk_mget_mem_bndg' fs [b]
  ++"\n\t\t    [] "++mk_mget_mem_bndg' fs xs


-- make mset external choices of Memory proc
mk_mset_mem_bndg fs = mk_mset_mem_bndg' fs fs
mk_mset_mem_bndg' fs [] = ""
mk_mset_mem_bndg' fs [b]
  = "\n\t\t    [] ([] n:dom(b_"
      ++(lastN 3 b)
      ++") @ mset.n?x:type"
      ++ (lastN 3 b)
      ++"(n) -> Memory("
      ++  ( mk_charll_to_charl "," (repl_mem_param_over (lastN 3 b) (mk_mem_param_lst fs) ))
      ++"))"
mk_mset_mem_bndg' fs (b:xs)
  = mk_mset_mem_bndg' fs [b]
  ++mk_mset_mem_bndg' fs xs


-- make subtype NAME_TYPE1, subtype...

-- this function returns the entire set of NAME
get_znames_from_NAME [] = []
get_znames_from_NAME ((ZFreeTypeDef ("NAME",[],_) xs):axs) = xs
get_znames_from_NAME (_:axs) = get_znames_from_NAME axs

-- first we get the names from NAME datatype
select_f_zbr [] = []
select_f_zbr ((ZBranch0 v):xs) = v : (select_f_zbr xs)
select_f_zbr (_:xs) = (select_f_zbr xs)

-- now we filter a list of names nms of a selected type tp
filter_znames_f_type [] tp = []
filter_znames_f_type (n:nms) tp
  | (ntrd n) == tp = [n] ++ (filter_znames_f_type nms tp)
  | otherwise = (filter_znames_f_type nms tp)

-- with all that, we create a subtype NAME_TYPEX
lst_subtype t [] = []
lst_subtype t ((z,s,f):zs)
      | f == t = z : (lst_subtype t zs)
      | otherwise = (lst_subtype t zs)

make_subtype_NAME :: [ZBranch] -> [Char]
make_subtype_NAME zb
  = nametypels
  where
    make_subtype znls zt =
      "subtype NAME_"++zt++" = "
        ++(mk_charll_to_charl " | " ((lst_subtype zt znls)))
    znames = remdups $ select_f_zbr zb
    ztypes = remdups $ map ntrd (select_f_zbr zb)
    nametypels = mk_charll_to_charl "\n" $
            map (make_subtype znames) ztypes

-- make NAME_VALUES_TYPE
mk_NAME_VALUES_TYPE n
  = "NAMES_VALUES_"++n++" = seq({seq({(n,v) | v <- type"++n++"(n)}) | n <- NAME_"++n++"})"
-- make BINDINGS_TYPE
mk_BINDINGS_TYPE n
  = "BINDINGS_"++n++" = {set(b) | b <- set(distCartProd(NAMES_VALUES_"++n++"))}"
-- make restrict functions within main action
mk_binding_list n
  = "b_"++n++" : BINDINGS_" ++ n

get_binding_types :: [ZGenFilt] -> [String]
get_binding_types [] = []
get_binding_types ((Choose (v,a,b) t):ts) = (lastN 3 v):get_binding_types ts


get_bindings_v :: [ZGenFilt] -> [String]
get_bindings_v [] = []
get_bindings_v ((Choose (v,a,b) t):ts) = (lastN 3 v):get_bindings_v ts


mk_restrict vlst n
    = " restrict"++n++"(bs) = dres(bs,{"++(mk_charll_to_charl ", " $ (lst_subtype n vlst))++"})"
mk_Memory_param (ZVar (n,x,y)) = "restrict"++(lastN 3 n)++"(b_"++(lastN 3 n)++")"
mk_Memory_param _ = ""
mk_restrict_name n
  = "restrict"++n++"("++"b_"++n++")"

\end{code}


\begin{code}
-- filter the Delta for the variables of a particular process procn
-- (var name, U_TYP, TYP, Type)

filter_universe_st :: String -> [(String, [Char], [Char], [Char])] -> [String]
filter_universe_st procn [(a, b, c, d)]
  | is_ZVar_st' a procn = [b]
  | otherwise = []

filter_universe_st procn ((a, b, c, d):xs)
  | is_ZVar_st' a procn= [b]++(filter_universe_st procn xs)
  | otherwise = (filter_universe_st procn xs)

\end{code}
\begin{code}
-- extract the delta variables and types in here'
def_universe [(ZAbbreviation ("\\delta",[],_) (ZSetDisplay xs))]
  = def_universe_aux xs
def_universe ((ZAbbreviation ("\\delta",[],_) (ZSetDisplay xs)):xss)
  = (def_universe_aux xs)++(def_universe xss)
def_universe (_:xs)
  = (def_universe xs)
def_universe []
  = []
\end{code}

\begin{code}
-- (var name, U_TYP, TYP, Type)
def_universe_aux :: [ZExpr] -> [(String, [Char], [Char], [Char])]
def_universe_aux [] = []
def_universe_aux [ZCall (ZVar ("\\mapsto",[],_)) (ZTuple [ZVar (b,[],_),ZVar ("\\nat",[],_)])] = [(b,"U_NAT", "NAT", "NatValue")]
def_universe_aux [ZCall (ZVar ("\\mapsto",[],_)) (ZTuple [ZVar (b,[],_),ZVar (c,[],_)])]= [(b,(def_U_NAME c), (def_U_prefix c), c)]
def_universe_aux ((ZCall (ZVar ("\\mapsto",[],_)) (ZTuple [ZVar (b,[],_),ZVar ("\\nat",[],_)])):xs) = ((b,"U_NAT", "NAT", "NatValue"):(def_universe_aux xs))
def_universe_aux ((ZCall (ZVar ("\\mapsto",[],_)) (ZTuple [ZVar (b,[],_),ZVar (c,[],_)])):xs) = ((b,(def_U_NAME c), (def_U_prefix c), c):(def_universe_aux xs))
def_universe_aux [(ZCall (ZVar ("\\mapsto",[],_)) (ZTuple [ZVar (b,[],_), ZCall (ZVar ("\\power",[],_)) (ZVar (c,[],_))]))]
  = [(b,(def_U_NAME ("_"++c)), (def_U_prefix ("_"++c)), ("Set("++c++")"))]
def_universe_aux ((ZCall (ZVar ("\\mapsto",[],_)) (ZTuple [ZVar (b,[],_), ZCall (ZVar ("\\power",[],_)) (ZVar (c,[],_))])):xs)
  = ((b,(def_U_NAME ("_"++c)), (def_U_prefix ("_"++c)), ("Set("++c++")")):(def_universe_aux xs))
\end{code}

\begin{code}
-- (var name, U_TYP, TYP, Type)
filter_types_universe [] = []
filter_types_universe [(_,b,_,_)] = [b]
filter_types_universe ((_,b,_,_):xs) = (b:(filter_types_universe xs))

filter_types_universe' [] = []
filter_types_universe' [(a,b,c,d)] = [(b,b,c,d)]
filter_types_universe' ((a,b,c,d):xs) = ((b,b,c,d):(filter_types_universe' xs))
\end{code}


Pieces from MappingFunStatelessCircus file


\begin{code}
def_delta_mapping :: [ZGenFilt] -> [ZExpr]
def_delta_mapping [] = []
def_delta_mapping ((Choose (v,[],tx) t):xs)
  = [ZCall (ZVar ("\\mapsto",[],[])) (ZTuple [ZVar (v,[],tx),t])]
    ++ (def_delta_mapping xs)
def_delta_mapping (_:xs) = (def_delta_mapping xs)


def_delta_mapping_t :: [ZGenFilt] -> [ZPara]
def_delta_mapping_t xs
    = map (subname xs) tlist
      where
        tlist = map (\(Choose v (ZVar (t,_,_))) -> t) $ filter_ZGenFilt_Choose xs
        subname xs tl =
          (ZAbbreviation
                (join_name "\\delta" tl,[],"")
                (ZSetDisplay (sub_name xs tl)))
          -- (ZFreeTypeDef (join_name "NAME" tl,[],[]) (sub_name xs tl))
        sub_name [] _= []
        sub_name ((Choose v (ZVar (t,_,_))):xs) t1
          | t1 == t =
              [ZCall (ZVar ("\\mapsto",[],[])) (ZTuple [ZVar v,(ZVar (t,[],""))])]
                ++ (sub_name xs t1)
          | otherwise = (sub_name xs t1)
        sub_name (_:xs) t1 = (sub_name xs t1)

\end{code}

\begin{code}
def_delta_name :: [ZGenFilt] -> [ZBranch]
def_delta_name [] = []
def_delta_name ((Choose v t):xs) = [ZBranch0 v] ++ (def_delta_name xs)
def_delta_name (_:xs) = (def_delta_name xs)

-- Updated on 19 jun 2018 - removing tags from universe
def_new_universe [] = []
def_new_universe ((Choose (_,_,tx) (ZVar (tt,_,_))):xs)
  = (ZBranch0 (tt,[],"")):(def_new_universe xs)
  -- = (ZBranch1 ((def_U_prefix tt),[],"") (ZVar (tt,[],""))):(def_new_universe xs)
def_new_universe ((Choose (_,_,_) (ZCall (ZVar ("\\power",_,_)) (ZVar (c,_,_)))):xs)
  = (ZBranch0 ((def_U_prefix ("P"++c)),[],"")):(def_new_universe xs)
  -- = (ZBranch1 ((def_U_prefix tt),[],"") (ZVar (tt,[],""))):(def_new_universe xs)
def_new_universe (_:xs) = (def_new_universe xs)

def_sub_univ [] = []
def_sub_univ ((Choose (_,_,tx) (ZVar (tt,_,_))):xs)
  = (ZFreeTypeDef (join_name "U" (def_U_prefix tt),[],"")
      [ZBranch0  (tt,[],"")]):(def_sub_univ xs)
      -- [ZBranch1 ((def_U_prefix tt),[],"") (ZVar (tt,[],""))]):(def_sub_univ xs)
def_sub_univ ((Choose (_,_,tx) (ZCall (ZVar ("\\power",_,_)) (ZVar (c,_,_)))):xs)
  = (ZFreeTypeDef (join_name "U" (def_U_prefix ("P"++c)),[],"")
      [ZBranch0 ((def_U_prefix ("P"++c)),[],"")]):(def_sub_univ xs)
      -- [ZBranch1 ((def_U_prefix ("P"++c)),[],"") (ZCall (ZVar ("\\power",[],"")) (ZVar (c,[],"")))]):(def_sub_univ xs)
def_sub_univ (_:xs) = (def_sub_univ xs)

def_sub_univ_set :: [ZGenFilt] -> [ZExpr]
def_sub_univ_set [] = []
def_sub_univ_set ((Choose (_,_,tx) (ZVar (tt,_,_))):xs)
  = (ZVar (join_name "U" (def_U_prefix tt),[],"")):(def_sub_univ_set xs)
def_sub_univ_set (_:xs) = (def_sub_univ_set xs)

def_sub_bind [] = []
def_sub_bind ((Choose (_,_,tx) (ZVar (tt,_,_))):xs)
  = (ZAbbreviation (join_name "BINDINGS" (def_U_prefix tt),[],"") (ZCall (ZVar ("\\fun",[],"")) (ZTuple [ZVar (join_name "NAME" (def_U_prefix tt),[],""),ZVar (join_name "U" (def_U_prefix tt) ,[],"")]))):(def_sub_bind xs)
def_sub_bind ((Choose (_,_,tx) (ZCall (ZVar ("\\power",_,_)) (ZVar (c,_,_)))):xs)
  = (ZAbbreviation (join_name "BINDINGS" (def_U_prefix ("P"++c)),[],"") (ZCall (ZVar ("\\fun",[],"")) (ZTuple [ZVar (join_name "NAME" (def_U_prefix ("P"++c)),[],""),ZVar (join_name "U" (def_U_prefix ("P"++c)) ,[],"")]))):(def_sub_bind xs)


def_sub_bind (_:xs) = (def_sub_bind xs)

def_sub_bindn [] = []
def_sub_bindn ((Choose (_,_,tx) (ZVar (tt,_,_))):xs)
  = (ZVar (join_name "BINDINGS" (def_U_prefix tt),[],"")):(def_sub_bindn xs)
def_sub_bindn ((Choose (_,_,tx) (ZCall (ZVar ("\\power",_,_)) (ZVar (c,_,_)))):xs)
    = (ZVar (join_name "BINDINGS" (def_U_prefix ("P"++c)),[],"")):(def_sub_bindn xs)

def_sub_bindn (_:xs) = (def_sub_bindn xs)

def_sub_name :: [ZGenFilt] -> [ZPara]
def_sub_name xs
    = map (subname xs) tlist
      where
        tlist = map (\(Choose v (ZVar (tt,_,_))) -> (def_U_prefix tt)) $ filter_ZGenFilt_Choose xs
        subname xs tl =
          (ZFreeTypeDef (join_name "NAME" tl,[],[]) (sub_name xs tl))
        sub_name [] _= []
        sub_name ((Choose v (ZVar (tt,_,_))):xs) t1
          | t1 == (def_U_prefix tt) = [ZBranch0 v] ++ (sub_name xs t1)
          | otherwise = (sub_name xs t1)
        sub_name (_:xs) t1 = (sub_name xs t1)



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
def_mem_st_Circus_aux spec [] = []
def_mem_st_Circus_aux spec [x] = def_mem_st_CircParagraphs spec x
def_mem_st_Circus_aux spec (x:xs)
  = (def_mem_st_CircParagraphs spec x)++(def_mem_st_Circus_aux spec xs)
\end{code}

\begin{code}

rename_z_schema_state spec (CProcess p (ProcDefSpot aa (ProcDef (ProcMain (ZSchemaDef (ZSPlain n _) schlst) proclst ma))))
  = (CProcess p (ProcDefSpot aa (ProcDef (ProcMain (ZSchemaDef (ZSPlain n []) (ZSchema xs)) proclst ma))))
    where
      xs = retrive_schemas spec schlst
rename_z_schema_state spec (CProcess p (ProcDef (ProcMain (ZSchemaDef (ZSPlain n _) schlst) proclst ma)))
  = (CProcess p (ProcDef (ProcMain (ZSchemaDef (ZSPlain n []) (ZSchema xs)) proclst ma)))
    where
      xs = retrive_schemas spec schlst
rename_z_schema_state spec x = x
\end{code}

\begin{code}
retrive_schemas spec (ZSchema lstx) = lstx
retrive_schemas spec (ZSRef (ZSPlain nn _) [] [])
  = case res of
      Just e' -> e'
      Nothing -> error "Schema definition not found!"
    where
      res = (retrieve_z_schema_state nn spec)
retrive_schemas spec (ZS1 x a)
  = (retrive_schemas spec a)
retrive_schemas spec (ZS2 ZSAnd a b)
  = (retrive_schemas spec a)++(retrive_schemas spec b)
retrive_schemas spec (ZSHide a b) = retrive_schemas spec a
retrive_schemas spec (ZSExists a b) = retrive_schemas spec b
retrive_schemas spec (ZSExists_1 a b) = retrive_schemas spec b
retrive_schemas spec (ZSForall a b) = retrive_schemas spec b
retrive_schemas spec _ = error "Schema def not implemented yet"
\end{code}

\begin{code}
retrieve_z_schema_state n [(ZSchemaDef (ZSPlain nn _) (ZSchema lstx))]
  | n == nn = Just lstx
  | otherwise = Nothing
retrieve_z_schema_state n [_] = Nothing
retrieve_z_schema_state n ((ZSchemaDef (ZSPlain nn _) (ZSchema lstx)):xs)
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
get_state_var spec name (ZSRef (ZSPlain nn _) [] [])
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
filter_main_action_bind
  :: ZName -> [(ZName, ZVar, ZExpr)] ->[(ZName, ZVar, ZExpr)]
filter_main_action_bind zn [(a,b,c)]
  | zn == a = [(a,b,c)]
  | otherwise = []
filter_main_action_bind zn ((a,b,c):ls)
  | zn == a = [(a,b,c)] ++ filter_main_action_bind zn ls
  | otherwise = filter_main_action_bind zn ls

mk_main_action_bind :: [(ZName, ZVar, ZExpr)] -> CAction -> CAction
mk_main_action_bind lst ca
  | null lst = (CActionCommand (CValDecl [Choose ("b",[],[]) (ZSetComp [Choose ("x",[],[]) (ZVar ("BINDING",[],[])) ] Nothing)] ca))
  | otherwise = (CActionCommand (CValDecl [Choose ("b",[],[]) (ZSetComp [Choose ("x",[],[]) (ZVar ("BINDING",[],[])),Check (mk_inv lst lst) ] Nothing)] ca))
\end{code}
\begin{code}
mk_inv :: [(ZName, ZVar, ZExpr)] -> [(ZName, ZVar, ZExpr)] -> ZPred
mk_inv lst [(a,(va,x,t),c)]
  = (ZMember (ZVar ((join_name (join_name "sv" a) va) ,x,newt)) (rename_vars_ZExpr1 a lst c))
    where newt = (def_U_prefix $ get_vars_ZExpr c)
mk_inv lst ((a,b,c):xs)
  = (ZAnd (mk_inv lst xs) (mk_inv lst [(a,b,c)]))
-- mk_inv x (_:xs) = mk_inv x xs

\end{code}

Given $\{v_0,\ldots,v_n\}$, the function $make\_maps\_to$ returns $\{v_0 \mapsto vv_o, \ldots, v_n \mapsto vv_n\}$.
\begin{code}
make_maps_to :: [ZVar] -> [ZExpr]
make_maps_to [(x,[],t)]
  = [ZCall (ZVar ("\\mapsto",[],[]))
    (ZTuple [ZVar (x,[],t),ZVar ("val"++x,[],t)])]
make_maps_to ((x,[],t):xs)
  = [ZCall (ZVar ("\\mapsto",[],[]))
    (ZTuple [ZVar (x,[],t),ZVar ("val"++x,[],t)])]++(make_maps_to xs)
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
  CParAction "Memory" (CircusAction (CActionCommand (CVResDecl [Choose ("b",[],[]) (ZVar ("BINDING",[],[]))] (CSPExtChoice (CSPExtChoice (CSPRepExtChoice [Choose ("n",[],[]) (ZCall (ZVar ("\\dom",[],[])) (ZVar ("b",[],[])))] (CSPCommAction (ChanComm "mget" [ChanDotExp (ZVar ("n",[],[])),ChanOutExp (ZCall (ZVar ("b",[],[])) (ZVar ("n",[],[])))]) (CSPParAction "Memory" [ZVar ("b",[],[])]))) (CSPRepExtChoice [Choose ("n",[],[]) (ZCall (ZVar ("\\dom",[],[])) (ZVar ("b",[],[])))] (CSPCommAction (ChanComm "mset" [ChanDotExp (ZVar ("n",[],[])),ChanInpPred "nv" (ZMember (ZVar ("nv",[],[])) (ZCall (ZVar ("\\delta",[],[])) (ZVar ("n",[],[]))))]) (CSPParAction "Memory" [ZCall (ZVar ("\\oplus",[],[])) (ZTuple [ZVar ("b",[],[]),ZSetDisplay [ZCall (ZVar ("\\mapsto",[],[])) (ZTuple [ZVar ("n",[],[]),ZVar ("nv",[],[])])]])])))) (CSPCommAction (ChanComm "terminate" []) CSPSkip)))))
\end{code}
Checking if the Delta is empty. That means that there's no state in any process in the specification.
\begin{code}
check_empty_delta [ZAbbreviation ("\\delta",_,_) (ZSetDisplay [])] = True
check_empty_delta [ZAbbreviation ("\\delta",_,_) (ZSetDisplay _)] = False
check_empty_delta [_] = False
check_empty_delta ((ZAbbreviation ("\\delta",_,_) (ZSetDisplay [])):xs) = True
check_empty_delta ((ZAbbreviation ("\\delta",_,_) (ZSetDisplay _)):xs) = False
check_empty_delta (_:xs) = check_empty_delta xs

\end{code}

this makes a list of local variables to be renamed
\begin{code}
\end{code}
\begin{code}
vars_to_name :: ZVar -> ZName
vars_to_name (v,x,t) = v
\end{code}
\begin{code}
rename_list_lv
  :: [Char]
     -> [(String, [t2], t)]
     -> [ZGenFilt]
     -> [((String, [t1], t), ZExpr)]
rename_list_lv p ys vs
  = ren p ys vs
    where
      ren' pn (v,[],t1) [Choose (v1,[],t2) t] =
        case v == v1 of
            True -> [((v,[],t1),ZVar ((join_name "lv" v) ,[],newt))]
            False -> []
        where newt = (def_U_prefix $ get_vars_ZExpr t)
      ren' pn (v,[],t1) ((Choose (v1,[],t2) t):xs) =
        case v == v1 of
            True -> [((v,[],t1),ZVar ((join_name "lv" v) ,[],newt))]
            False -> ren' pn (v,[],t1) xs
        where newt = (def_U_prefix $ get_vars_ZExpr t)
      ren pn [x] as = ren' pn x as
      ren pn (x:xs) as = (ren' pn x as)++(ren pn xs as)

rename_genfilt_lv :: [Char] -> [ZGenFilt] -> [ZGenFilt]
rename_genfilt_lv pn xs
  = map (rename_genfilt_lv' pn) xs

rename_genfilt_lv' pn (Choose (va,x,t) e)
  = (Choose ((join_name "lv" va),[],newt) e)
    where newt = (def_U_prefix $ get_vars_ZExpr e)
rename_genfilt_lv' pn x = x
\end{code}


Entire rewriting of the types within a ZVar
\begin{code}


upd_type_ZPara lst (Process _ProcDecl)
  = (Process (upd_type_ProcDecl lst _ProcDecl))
upd_type_ZPara lst x
  = x

--ProcDecl
upd_type_ProcDecl lst (CProcess _ZName _ProcessDef)
  = (CProcess _ZName  (upd_type_ProcessDef lst _ProcessDef))
upd_type_ProcDecl lst (CParamProcess _ZName _ZName_lst _ProcessDef)
  = (CParamProcess _ZName _ZName_lst  (upd_type_ProcessDef lst _ProcessDef))
upd_type_ProcDecl lst (CGenProcess _ZName _ZName_lst _ProcessDef)
  = (CGenProcess _ZName _ZName_lst  (upd_type_ProcessDef lst _ProcessDef))

--ProcessDef
upd_type_ProcessDef lst (ProcDefSpot _ZGenFilt_lst _ProcessDef)
  = (ProcDefSpot (map (upd_type_ZGenFilt lst) _ZGenFilt_lst)  (upd_type_ProcessDef lst _ProcessDef))
upd_type_ProcessDef lst (ProcDefIndex _ZGenFilt_lst _ProcessDef)
  = (ProcDefIndex (map (upd_type_ZGenFilt lst) _ZGenFilt_lst)  (upd_type_ProcessDef lst _ProcessDef))
upd_type_ProcessDef lst (ProcDef _CProc)
  = (ProcDef (upd_type_CProc lst _CProc))

-- CProc
upd_type_CProc lst (CRepSeqProc _ZGenFilt_lst _CProc)
  = (CRepSeqProc (map (upd_type_ZGenFilt lst) _ZGenFilt_lst) (upd_type_CProc lst _CProc))
upd_type_CProc lst (CRepExtChProc _ZGenFilt_lst _CProc)
  = (CRepExtChProc (map (upd_type_ZGenFilt lst) _ZGenFilt_lst) (upd_type_CProc lst _CProc))
upd_type_CProc lst (CRepIntChProc _ZGenFilt_lst _CProc)
  = (CRepIntChProc (map (upd_type_ZGenFilt lst) _ZGenFilt_lst) (upd_type_CProc lst _CProc))
upd_type_CProc lst (CRepParalProc _CSExp _ZGenFilt_lst _CProc)
  = (CRepParalProc _CSExp (map (upd_type_ZGenFilt lst) _ZGenFilt_lst) (upd_type_CProc lst _CProc))
upd_type_CProc lst (CRepInterlProc _ZGenFilt_lst _CProc)
  = (CRepInterlProc (map (upd_type_ZGenFilt lst) _ZGenFilt_lst) (upd_type_CProc lst _CProc))
upd_type_CProc lst (CHide _CProc _CSExp)
  = (CHide (upd_type_CProc lst _CProc) _CSExp)
upd_type_CProc lst (CExtChoice _CProc1 _CProc2)
  = (CExtChoice (upd_type_CProc lst _CProc1) (upd_type_CProc lst _CProc2))
upd_type_CProc lst (CIntChoice _CProc1 _CProc2)
  = (CIntChoice (upd_type_CProc lst _CProc1) (upd_type_CProc lst _CProc2))
upd_type_CProc lst (CParParal _CSExp _CProc1 _CProc2)
  = (CParParal _CSExp (upd_type_CProc lst _CProc1) (upd_type_CProc lst _CProc2))
upd_type_CProc lst (CInterleave _CProc1 _CProc2)
  = (CInterleave (upd_type_CProc lst _CProc1) (upd_type_CProc lst _CProc2))
upd_type_CProc lst (CGenProc _ZName  _ZExpr_lst)
  = (CGenProc _ZName  _ZExpr_lst)
upd_type_CProc lst (CParamProc _ZName  _ZExpr_lst)
  = (CParamProc _ZName  _ZExpr_lst)
upd_type_CProc lst (CProcRename _ZName  _Comm_lst1  _Comm_lst2)
  = (CProcRename _ZName  _Comm_lst1  _Comm_lst2)
upd_type_CProc lst (CSeq _CProc1 _CProc2)
  = (CSeq (upd_type_CProc lst _CProc1) (upd_type_CProc lst _CProc2))
upd_type_CProc lst (CSimpIndexProc _ZName  _ZExpr_lst)
  = (CSimpIndexProc _ZName  _ZExpr_lst)
upd_type_CProc lst (CircusProc _ZName)
  = (CircusProc _ZName)
upd_type_CProc lst (ProcMain _ZPara _PPar_lst _CAction)
  = (ProcMain _ZPara _PPar_lst (upd_type_CAction lst _CAction))
upd_type_CProc lst (ProcStalessMain _PPar_lst _CAction)
  = (ProcStalessMain _PPar_lst (upd_type_CAction lst _CAction))


upd_type_PPar lst (CParAction _ZName p)
  = (CParAction _ZName (upd_type_ParAction lst p))
upd_type_PPar lst x
  = x

upd_type_ParAction lst (CircusAction _CAction)
  = (CircusAction (upd_type_CAction lst _CAction))
upd_type_ParAction lst (ParamActionDecl _ZGenFilt_lst _ParAction)
  = (ParamActionDecl (map (upd_type_ZGenFilt lst) _ZGenFilt_lst) (upd_type_ParAction lst _ParAction))



upd_type_CAction lst (CActionCommand _CCommand)
  = (CActionCommand (upd_type_CCommand lst _CCommand))
upd_type_CAction lst (CSPCommAction _Comm _CAction)
  = (CSPCommAction (upd_type_Comm lst _Comm) (upd_type_CAction lst _CAction))
upd_type_CAction lst (CSPGuard _ZPred _CAction)
  = (CSPGuard _ZPred (upd_type_CAction lst _CAction))
upd_type_CAction lst (CSPSeq _CAction1 _CAction2)
  = (CSPSeq (upd_type_CAction lst _CAction1) (upd_type_CAction lst _CAction2))
upd_type_CAction lst (CSPExtChoice _CAction1 _CAction2)
  = (CSPExtChoice (upd_type_CAction lst _CAction1) (upd_type_CAction lst _CAction2))
upd_type_CAction lst (CSPIntChoice _CAction1 _CAction2)
  = (CSPIntChoice (upd_type_CAction lst _CAction1) (upd_type_CAction lst _CAction2))
upd_type_CAction lst (CSPNSParal _NSExp1 _CSExp _NSExp2 _CAction1 _CAction2)
  = (CSPNSParal _NSExp1 _CSExp _NSExp2 (upd_type_CAction lst _CAction1) (upd_type_CAction lst _CAction2))
upd_type_CAction lst (CSPParal _CSExp _CAction1 _CAction2)
  = (CSPParal _CSExp (upd_type_CAction lst _CAction1) (upd_type_CAction lst _CAction2))
upd_type_CAction lst (CSPNSInter _NSExp1 _NSExp2 _CAction1 _CAction2)
  = (CSPNSInter _NSExp1 _NSExp2 (upd_type_CAction lst _CAction1) (upd_type_CAction lst _CAction2))
upd_type_CAction lst (CSPInterleave _CAction1 _CAction2)
  = (CSPInterleave (upd_type_CAction lst _CAction1) (upd_type_CAction lst _CAction2))
upd_type_CAction lst (CSPHide _CAction _CSExp)
  = (CSPHide (upd_type_CAction lst _CAction) _CSExp)
upd_type_CAction lst (CSPParAction _ZName  _ZExpr_lst)
  = (CSPParAction _ZName  (map (upd_type_ZExpr lst) _ZExpr_lst))
upd_type_CAction lst (CSPRenAction _ZName _CReplace)
  = (CSPRenAction _ZName (upd_type_CReplace lst _CReplace))
upd_type_CAction lst (CSPRecursion _ZName _CAction)
  = (CSPRecursion _ZName (upd_type_CAction lst _CAction))
upd_type_CAction lst (CSPUnfAction _ZName _CAction)
  = (CSPUnfAction _ZName (upd_type_CAction lst _CAction))
upd_type_CAction lst (CSPUnParAction _ZGenFilt_lst _CAction _ZName)
  = (CSPUnParAction (map (upd_type_ZGenFilt lst) _ZGenFilt_lst) (upd_type_CAction lst _CAction) _ZName)
upd_type_CAction lst (CSPRepSeq _ZGenFilt_lst _CAction)
  = (CSPRepSeq (map (upd_type_ZGenFilt lst) _ZGenFilt_lst) (upd_type_CAction lst _CAction))
upd_type_CAction lst (CSPRepExtChoice _ZGenFilt_lst _CAction)
  = (CSPRepExtChoice (map (upd_type_ZGenFilt lst) _ZGenFilt_lst) (upd_type_CAction lst _CAction))
upd_type_CAction lst (CSPRepIntChoice _ZGenFilt_lst _CAction)
  = (CSPRepIntChoice (map (upd_type_ZGenFilt lst) _ZGenFilt_lst) (upd_type_CAction lst _CAction))
upd_type_CAction lst (CSPRepParalNS _CSExp _ZGenFilt_lst _NSExp _CAction)
  = (CSPRepParalNS _CSExp (map (upd_type_ZGenFilt lst) _ZGenFilt_lst) _NSExp (upd_type_CAction lst _CAction))
upd_type_CAction lst (CSPRepParal _CSExp _ZGenFilt_lst _CAction)
  = (CSPRepParal _CSExp (map (upd_type_ZGenFilt lst) _ZGenFilt_lst) (upd_type_CAction lst _CAction))
upd_type_CAction lst (CSPRepInterlNS _ZGenFilt_lst _NSExp _CAction)
  = (CSPRepInterlNS (map (upd_type_ZGenFilt lst) _ZGenFilt_lst) _NSExp (upd_type_CAction lst _CAction))
upd_type_CAction lst (CSPRepInterl _ZGenFilt_lst _CAction)
  = (CSPRepInterl (map (upd_type_ZGenFilt lst) _ZGenFilt_lst) (upd_type_CAction lst _CAction))
upd_type_CAction lst x = x

upd_type_Comm lst (ChanComm _ZName  _CParameter_lst)
  = (ChanComm _ZName  (map (upd_type_CParameter lst) _CParameter_lst))
upd_type_Comm lst (ChanGenComm _ZName  _ZExpr_lst  _CParameter_lst)
  = (ChanGenComm _ZName  (map (upd_type_ZExpr lst) _ZExpr_lst)  (map (upd_type_CParameter lst) _CParameter_lst))


upd_type_CParameter lst (ChanInpPred _ZName p1)
  = (ChanInpPred _ZName (upd_type_ZPred lst p1))
upd_type_CParameter lst (ChanOutExp e)
  = (ChanOutExp (upd_type_ZExpr lst e))
upd_type_CParameter lst (ChanDotExp e)
  = (ChanDotExp (upd_type_ZExpr lst e))
upd_type_CParameter lst x
  = x


upd_type_CCommand lst (CAssign _ZVar_lst  _ZExpr_lst)
  = (CAssign (map (upd_type_ZVar lst) _ZVar_lst)  (map (upd_type_ZExpr lst) _ZExpr_lst))
upd_type_CCommand lst (CIf _CGActions)
  = (CIf (upd_type_CGActions lst _CGActions))
upd_type_CCommand lst (CVarDecl _ZGenFilt_lst _CAction)
  = (CVarDecl (map (upd_type_ZGenFilt lst) _ZGenFilt_lst) (upd_type_CAction lst _CAction))
upd_type_CCommand lst (CValDecl _ZGenFilt_lst _CAction)
  = (CValDecl (map (upd_type_ZGenFilt lst) _ZGenFilt_lst) (upd_type_CAction lst _CAction))
upd_type_CCommand lst (CResDecl _ZGenFilt_lst _CAction)
  = (CResDecl (map (upd_type_ZGenFilt lst) _ZGenFilt_lst) (upd_type_CAction lst _CAction))
upd_type_CCommand lst (CVResDecl _ZGenFilt_lst _CAction)
  = (CVResDecl (map (upd_type_ZGenFilt lst) _ZGenFilt_lst) (upd_type_CAction lst _CAction))
upd_type_CCommand lst (CAssumpt _ZName_lst _ZPred1 _ZPred2)
  = (CAssumpt _ZName_lst (upd_type_ZPred lst _ZPred1) (upd_type_ZPred lst _ZPred2))
upd_type_CCommand lst (CAssumpt1 _ZName_lst _ZPred)
  = (CAssumpt1 _ZName_lst _ZPred)
upd_type_CCommand lst (CPrefix _ZPred1 _ZPred2)
  = (CPrefix (upd_type_ZPred lst _ZPred1) (upd_type_ZPred lst _ZPred2))
upd_type_CCommand lst (CPrefix1 _ZPred)
  = (CPrefix1 (upd_type_ZPred lst _ZPred))
upd_type_CCommand lst (CommandBrace _ZPred)
  = (CommandBrace (upd_type_ZPred lst _ZPred))
upd_type_CCommand lst (CommandBracket _ZPred)
  = (CommandBracket (upd_type_ZPred lst _ZPred))


upd_type_CGActions lst (CircGAction _ZPred _CAction)
  = (CircGAction (upd_type_ZPred lst _ZPred) (upd_type_CAction lst _CAction))
upd_type_CGActions lst (CircThenElse _CGActions1 _CGActions2)
  = (CircThenElse (upd_type_CGActions lst _CGActions1) (upd_type_CGActions lst _CGActions2))

upd_type_CReplace lst (CRename _ZVar_lst1 _ZVar_lst2)
  = (CRename (map ( upd_type_ZVar lst) _ZVar_lst1) (map ( upd_type_ZVar lst) _ZVar_lst2))
upd_type_CReplace lst (CRenameAssign _ZVar_lst1 _ZVar_lst2)
  = (CRenameAssign (map ( upd_type_ZVar lst) _ZVar_lst1) (map ( upd_type_ZVar lst) _ZVar_lst2))

upd_type_ZPred lst (ZFalse{reason=a})
 = (ZFalse{reason=a})
upd_type_ZPred lst (ZTrue{reason=a})
 = (ZTrue{reason=a})
upd_type_ZPred lst (ZAnd p1 p2)
 = (ZAnd (upd_type_ZPred lst p1) (upd_type_ZPred lst p2))
upd_type_ZPred lst (ZOr p1 p2)
 = (ZOr (upd_type_ZPred lst p1) (upd_type_ZPred lst p2))
upd_type_ZPred lst (ZImplies p1 p2)
 = (ZImplies (upd_type_ZPred lst p1) (upd_type_ZPred lst p2))
upd_type_ZPred lst (ZIff p1 p2)
 = (ZIff (upd_type_ZPred lst p1) (upd_type_ZPred lst p2))
upd_type_ZPred lst (ZNot p)
 = (ZNot (upd_type_ZPred lst p))
upd_type_ZPred lst (ZExists pname1 p)
 = (ZExists pname1 (upd_type_ZPred lst p))
upd_type_ZPred lst (ZExists_1 lst1 p)
 = (ZExists_1 lst1 (upd_type_ZPred lst p))
upd_type_ZPred lst (ZForall pname1 p)
 = (ZForall pname1 (upd_type_ZPred lst p))
upd_type_ZPred lst (ZPLet varxp p)
 = (ZPLet varxp (upd_type_ZPred lst p))
upd_type_ZPred lst (ZEqual xpr1 xpr2)
 = (ZEqual (upd_type_ZExpr lst xpr1) (upd_type_ZExpr lst xpr2))
upd_type_ZPred lst (ZMember xpr1 xpr2)
 = (ZMember (upd_type_ZExpr lst xpr1) (upd_type_ZExpr lst xpr2))
upd_type_ZPred lst (ZPre sp)
 = (ZPre sp)
upd_type_ZPred lst (ZPSchema sp)
 = (ZPSchema sp)

upd_type_ZVar [] (x,y,z) = (x,y,z)
upd_type_ZVar ((a,b,c):xs) (x,y,z)
  | a == x = (a,b,c)
  | (join_name "v" a) == x = ((join_name "v" a),b,c)
  | otherwise = upd_type_ZVar xs (x,y,z)


upd_type_ZExpr lst (ZVar v)
 = ZVar (upd_type_ZVar lst v)
upd_type_ZExpr lst (ZInt zi)
 = (ZInt zi)
upd_type_ZExpr lst (ZGiven gv)
 = (ZGiven gv)
upd_type_ZExpr lst (ZFree0 va)
 = (ZFree0 va)
upd_type_ZExpr lst (ZFree1 va xpr)
 = (ZFree1 va (upd_type_ZExpr lst xpr))
upd_type_ZExpr lst (ZTuple xpr)
 = (ZTuple (map (upd_type_ZExpr lst) xpr))
upd_type_ZExpr lst (ZBinding xs)
 = (ZBinding (map ((\l (a,b) -> ((upd_type_ZVar l a),(upd_type_ZExpr l b))) lst) xs))
upd_type_ZExpr lst (ZSetDisplay xpr)
 = (ZSetDisplay (map (upd_type_ZExpr lst) xpr))
upd_type_ZExpr lst (ZSeqDisplay xpr)
 = (ZSeqDisplay (map (upd_type_ZExpr lst) xpr))
upd_type_ZExpr lst (ZFSet zf)
 = (ZFSet zf)
upd_type_ZExpr lst (ZIntSet i1 i2)
 = (ZIntSet i1 i2)
upd_type_ZExpr lst (ZGenerator zrl xpr)
 = (ZGenerator zrl (upd_type_ZExpr lst xpr))
upd_type_ZExpr lst (ZCross xpr)
 = (ZCross (map (upd_type_ZExpr lst) xpr))
upd_type_ZExpr lst (ZFreeType va pname1)
 = (ZFreeType va pname1)
upd_type_ZExpr lst (ZPowerSet{baseset=xpr, is_non_empty=b1, is_finite=b2})
 = (ZPowerSet{baseset=(upd_type_ZExpr lst xpr), is_non_empty=b1, is_finite=b2})
upd_type_ZExpr lst (ZFuncSet{ domset=expr1, ranset=expr2, is_function=b1, is_total=b2, is_onto=b3, is_one2one=b4, is_sequence=b5, is_non_empty=b6, is_finite=b7})
 = (ZFuncSet{ domset=(upd_type_ZExpr lst expr1), ranset=(upd_type_ZExpr lst expr2), is_function=b1, is_total=b2, is_onto=b3, is_one2one=b4, is_sequence=b5, is_non_empty=b6, is_finite=b7})
upd_type_ZExpr lst (ZSetComp pname1 (Just xpr))
 = (ZSetComp (map (upd_type_ZGenFilt  lst) pname1) (Just (upd_type_ZExpr lst xpr)))
upd_type_ZExpr lst (ZSetComp pname1 Nothing)
 = (ZSetComp (map (upd_type_ZGenFilt  lst) pname1) Nothing)
upd_type_ZExpr lst (ZLambda pname1 xpr)
 = (ZLambda (map (upd_type_ZGenFilt  lst) pname1) (upd_type_ZExpr lst xpr))
upd_type_ZExpr lst (ZESchema zxp)
 = (ZESchema zxp)
upd_type_ZExpr lst (ZGivenSet gs)
 = (ZGivenSet gs)
upd_type_ZExpr lst (ZUniverse)
 = (ZUniverse)
upd_type_ZExpr lst (ZCall xpr1 xpr2)
 = (ZCall (upd_type_ZExpr lst xpr1) (upd_type_ZExpr lst xpr2))
upd_type_ZExpr lst (ZReln rl)
 = (ZReln rl)
upd_type_ZExpr lst (ZFunc1 f1)
 = (ZFunc1 f1)
upd_type_ZExpr lst (ZFunc2 f2)
 = (ZFunc2 f2)
upd_type_ZExpr lst (ZStrange st)
 = (ZStrange st)
upd_type_ZExpr lst (ZMu pname1 (Just xpr))
 = (ZMu (map (upd_type_ZGenFilt  lst) pname1) (Just (upd_type_ZExpr lst xpr)))
upd_type_ZExpr lst (ZELet pname1 xpr1)
 = (ZELet (map ((\l (a,b) -> ((upd_type_ZVar l a),(upd_type_ZExpr l b))) lst)  pname1) (upd_type_ZExpr lst xpr1))
upd_type_ZExpr lst (ZIf_Then_Else zp xpr1 xpr2)
 = (ZIf_Then_Else zp (upd_type_ZExpr lst xpr1) (upd_type_ZExpr lst xpr2))
upd_type_ZExpr lst (ZSelect xpr va)
 = (ZSelect xpr va)
upd_type_ZExpr lst (ZTheta zs)
 = (ZTheta zs)

upd_type_ZGenFilt lst (Include s) = (Include s)
upd_type_ZGenFilt lst (Choose v e) = (Choose (upd_type_ZVar lst v) e)
upd_type_ZGenFilt lst (Check p) = (Check (upd_type_ZPred lst p))
upd_type_ZGenFilt lst (Evaluate v e1 e2)
 = (Evaluate (upd_type_ZVar lst v) (upd_type_ZExpr lst e1) (upd_type_ZExpr lst e2))


\end{code}

Hoping to intercalate strings with something
\begin{code}
joinBy sep cont = drop (length sep) $ concat $ map (\w -> sep ++ w) cont
\end{code}
\begin{code}
mk_var_v_var_bnds :: [ZExpr] -> [ZExpr]
mk_var_v_var_bnds [] = []
mk_var_v_var_bnds ((ZVar (x,b,c)):xs)
  | c == [] = []++(mk_var_v_var_bnds xs)
  | otherwise = [(ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar (x,b,c),ZVar (join_name "v" x,b,c)]))]++(mk_var_v_var_bnds xs)

map_var_bnds :: [ZExpr] -> [[ZExpr]]
map_var_bnds xs
  = map mk_var_v_var_bnds (map (filter_mergeV_by_type xs) (get_type_v xs))

filter_mergeV_by_type :: [ZExpr] -> String -> [ZExpr]
filter_mergeV_by_type [] _ = []
filter_mergeV_by_type ((ZVar (x,b,c)):xs) v
  | c == [] = (filter_mergeV_by_type xs v)
  | v == c = [ZVar (x,b,c)]++(filter_mergeV_by_type xs v)
  | otherwise = (filter_mergeV_by_type xs v)

get_type_v :: [ZExpr] -> [String]
get_type_v xs = remdups $ map (\(ZVar (x,b,c)) -> c) xs

mkZSetDisplay :: [[ZExpr]] -> [ZExpr]
mkZSetDisplay [] = []
mkZSetDisplay ([]:xs) = (mkZSetDisplay xs)
mkZSetDisplay (x:xs) = [ZSetDisplay x]++(mkZSetDisplay xs)

get_ns :: [ZExpr] -> [ZExpr]
get_ns [ZVar ("\\emptyset",[],"")] = [ZSeqDisplay []]
get_ns [ZSetDisplay xs] = [ZSeqDisplay xs]
get_ns _ = []
\end{code}

\section{Auxiliary for Ref3}
\begin{code}
def_bndg_lhs [] = []
def_bndg_lhs ((Choose (_,_,tx) (ZVar (tt,_,_))):xs)
  = (Choose (join_name "b" tx,[],[]) (ZVar (join_name "BINDING" tx,[],[]))):(def_bndg_lhs xs)
def_bndg_lhs (Choose (_,_,tx) (ZCall (ZVar ("\\power",_,_)) (ZVar (c,_,_))):xs)
  = (Choose (join_name "b" (def_U_prefix ("P"++c)),[],"")
      (ZVar (join_name "BINDING" (def_U_prefix ("P"++c)),[],""))):
      (def_bndg_lhs xs)
def_bndg_lhs (_:xs) = (def_bndg_lhs xs)

def_bndg_rhs :: [ZGenFilt] -> ZPred
def_bndg_rhs xs
  = sub_name xs
    where
      sub_name [(Choose (v,_,t1) t)]
        = (ZMember (ZCall
                    (ZVar (join_name "b" t1,[],[]))
                    (ZVar (v,[],t1)))
                (ZVar (join_name "U" t1,[],"")))
      sub_name ((Choose (v,_,t1) t):xs)
        = (ZAnd (ZMember (ZCall
                    (ZVar (join_name "b" t1,[],[]))
                    (ZVar (v,[],t1)))
              (ZVar (join_name "U" t1,[],""))) (sub_name xs))
      sub_name (_:xs) = (sub_name xs)

data_refinement stv
  = (remdups $ def_bndg_lhs stv)++[Check (def_bndg_rhs stv)]
\end{code}
\section{Auxiliary for Ref4}
\begin{code}
-- filtering ZGenFilt so only Choose are returned
zexp_to_zvar (ZVar x) = x
filter_ZGenFilt_Choose :: [ZGenFilt] -> [ZGenFilt]
filter_ZGenFilt_Choose [] = []
filter_ZGenFilt_Choose ((Choose b t):xs) = (Choose b t):(filter_ZGenFilt_Choose xs)
filter_ZGenFilt_Choose (_:xs) = (filter_ZGenFilt_Choose xs)

filter_ZGenFilt_Check :: [ZGenFilt] -> [ZPred]
filter_ZGenFilt_Check [] = []
filter_ZGenFilt_Check ((Check e):xs) = e:(filter_ZGenFilt_Check xs)
filter_ZGenFilt_Check (_:xs) = (filter_ZGenFilt_Check xs)
-- extracting ZVar from  ZGenFilt list
filter_bnd_var :: [ZGenFilt] -> [ZExpr]
filter_bnd_var [] = []
filter_bnd_var ((Choose b t):xs) = (ZVar b):(filter_bnd_var xs)

-- Memory parameters
mk_mem_param_circ :: ZExpr -> [ZExpr] -> [ZExpr]
mk_mem_param_circ (ZVar t) [ZVar t1]
  | t == t1 = [ZCall (ZVar ("\\oplus",[],""))
            (ZTuple [ZVar t,
              ZSetDisplay [ZCall (ZVar ("\\mapsto",[],""))
                                      (ZTuple [ZVar ("n",[],""),
                                  ZVar ("nv",[],"")])]])]
  | otherwise = [ZVar t1]
mk_mem_param_circ (ZVar t) (ZVar t1:tx)
  | t == t1
    = (ZCall (ZVar ("\\oplus",[],""))
            (ZTuple [ZVar t,
              ZSetDisplay [ZCall (ZVar ("\\mapsto",[],""))
                      (ZTuple [ZVar ("n",[],""),
                  ZVar ("nv",[],"")])]])): (mk_mem_param_circ (ZVar t) tx)
  | otherwise = (ZVar t1: (mk_mem_param_circ (ZVar t) tx))

-- gets and sets replicated ext choice for Memory
mk_mget_mem_CSPRepExtChoice :: [ZExpr] -> [ZExpr] -> CAction
mk_mget_mem_CSPRepExtChoice [ZVar t] tls
  = (CSPRepExtChoice [Choose ("n",[],(lastN 3 (nfst t)))
        (ZCall (ZVar ("\\dom",[],"")) (ZVar t))]
        (CSPCommAction (ChanComm "mget"
            [ChanDotExp (ZVar ("n",[],(lastN 3 (nfst t)))),
            ChanOutExp (ZCall (ZVar t) (ZVar ("n",[],(lastN 3 (nfst t)))))])
        (CSPParAction "Memory" tls)))
mk_mget_mem_CSPRepExtChoice (ZVar t:tx) tls
  = (CSPExtChoice (CSPRepExtChoice
        [Choose ("n",[],(lastN 3 (nfst t))) (ZCall (ZVar ("\\dom",[],"")) (ZVar t))]
        (CSPCommAction (ChanComm "mget"
            [ChanDotExp (ZVar ("n",[],(lastN 3 (nfst t)))),
             ChanOutExp (ZCall (ZVar t) (ZVar ("n",[],(lastN 3 (nfst t)))))])
             (CSPParAction "Memory" tls)))
             (mk_mget_mem_CSPRepExtChoice tx tls))

mk_mset_mem_CSPRepExtChoice :: [ZExpr] -> [ZExpr] -> CAction
mk_mset_mem_CSPRepExtChoice [ZVar t] tls
  = (CSPRepExtChoice
      [Choose ("n",[],(lastN 3 (nfst t))) (ZCall (ZVar ("\\dom",[],"")) (ZVar t))]
      (CSPCommAction (ChanComm "mset"
        [ChanDotExp (ZVar ("n",[],(nfst t))),
        ChanInpPred "nv" (ZMember (ZVar ("nv",[],(lastN 3 (nfst t))))
        (ZCall (ZVar ("\\delta",[],"")) (ZVar ("n",[],(lastN 3 (nfst t))))))])
  (CSPParAction "Memory" (mk_mem_param_circ (ZVar t) tls))))
mk_mset_mem_CSPRepExtChoice (ZVar t:tx) tls
  = (CSPExtChoice (CSPRepExtChoice
    [Choose ("n",[],(lastN 3 (nfst t))) (ZCall (ZVar ("\\dom",[],"")) (ZVar t))]
    (CSPCommAction (ChanComm "mset"
      [ChanDotExp (ZVar ("n",[],(lastN 3 (nfst t)))),
       ChanInpPred "nv" (ZMember (ZVar ("nv",[],(lastN 3 (nfst t))))
       (ZCall (ZVar ("\\delta",[],"")) (ZVar ("n",[],(lastN 3 (nfst t))))))])
  (CSPParAction "Memory" (mk_mem_param_circ (ZVar t) tls))))
  (mk_mset_mem_CSPRepExtChoice tx tls))

-- gets and sets replicated ext choice for MemoryMerge
mk_lget_mem_merg_CSPRepExtChoice :: [ZExpr] -> [ZExpr] -> CAction
mk_lget_mem_merg_CSPRepExtChoice [ZVar t] tls
  = (CSPRepExtChoice
    [Choose ("n",[],(lastN 3 (nfst t))) (ZCall (ZVar ("\\dom",[],"")) (ZVar t))]
    (CSPCommAction (ChanComm "lget"
      [ChanDotExp (ZVar ("n",[],(lastN 3 (nfst t)))),
       ChanOutExp (ZCall (ZVar t) (ZVar ("n",[],(lastN 3 (nfst t)))))])
       (CSPParAction "MemoryMerge"
        (tls++[ZVar ("ns",[],"")]))))
mk_lget_mem_merg_CSPRepExtChoice (ZVar t:tx) tls
  = (CSPExtChoice (CSPRepExtChoice
    [Choose ("n",[],(lastN 3 (nfst t))) (ZCall (ZVar ("\\dom",[],"")) (ZVar t))]
    (CSPCommAction (ChanComm "lget"
      [ChanDotExp (ZVar ("n",[],(lastN 3 (nfst t)))),
       ChanOutExp (ZCall (ZVar t) (ZVar ("n",[],(lastN 3 (nfst t)))))])
       (CSPParAction "MemoryMerge"
       (tls++[ZVar ("ns",[],"")]))))
        (mk_lget_mem_merg_CSPRepExtChoice tx tls))

mk_lset_mem_merg_CSPRepExtChoice :: [ZExpr] -> [ZExpr] -> CAction
mk_lset_mem_merg_CSPRepExtChoice [(ZVar t)] tls
  = (CSPRepExtChoice
      [Choose ("n",[],(lastN 3 (nfst t))) (ZCall (ZVar ("\\dom",[],"")) (ZVar t))]
      (CSPCommAction (ChanComm "lset"
        [ChanDotExp (ZVar ("n",[],(lastN 3 (nfst t)))),
         ChanInpPred "nv" (ZMember (ZVar ("nv",[],
            (lastN 3 (nfst t)))) (ZCall (ZVar ("\\delta",[],""))
            (ZVar ("n",[],(lastN 3 (nfst t))))))])
  (CSPParAction "MemoryMerge"
    (mk_mem_param_circ (ZVar t) (tls++[ZVar ("ns",[],"")])))))
mk_lset_mem_merg_CSPRepExtChoice ((ZVar t):tx) tls
  = (CSPExtChoice (CSPRepExtChoice
    [Choose ("n",[],(lastN 3 (nfst t))) (ZCall (ZVar ("\\dom",[],"")) (ZVar t))]
    (CSPCommAction (ChanComm "lset"
      [ChanDotExp (ZVar ("n",[],(lastN 3 (nfst t)))),
       ChanInpPred "nv" (ZMember (ZVar ("nv",[],(lastN 3 (nfst t))))
       (ZCall (ZVar ("\\delta",[],"")) (ZVar ("n",[],(lastN 3 (nfst t))))))])
       (CSPParAction "MemoryMerge"
       (mk_mem_param_circ (ZVar t) (tls++[ZVar ("ns",[],"")])))))
  (mk_lset_mem_merg_CSPRepExtChoice tx tls))

-- making renaming list for bindings
mk_subinfo_bndg [] = []
mk_subinfo_bndg ((ZVar (t,_,_)):tx) = ((t,[],""), ZVar (join_name "n" (lastN 3 t),[],"")):(mk_subinfo_bndg tx)
union_ml_mr [ZVar t] = ZVar t
union_ml_mr (x:xs) = ((ZCall (ZVar ("\\cup",[],"")) (ZTuple (x:xs))))
\end{code}
\section{Preprocessing any Z Schema used as a state}
\begin{code}
-- ZSchemaDef (ZSPlain nn) zs
-- Process (CProcess "SysClock" (ProcDef (ProcMain (ZSchemaDef (ZSPlain "SysClockSt") (ZSRef (ZSPlain "SysC
get_state_from_spec [] n = error "no schema found in the current spec"
get_state_from_spec ((ZSchemaDef (ZSPlain nn _) zs):xs) n
  | n == nn = zs
  | otherwise = (get_state_from_spec xs n)
get_state_from_spec (_:xs) n = (get_state_from_spec xs n)

normal_state_proc spec [] = []
normal_state_proc spec ((Process (CProcess n (ProcDefSpot ff (ProcDef (ProcMain (ZSchemaDef (ZSPlain st _) std) ls ma))))):xs)
  = ((Process (CProcess n (ProcDefSpot ff (ProcDef (ProcMain (ZSchemaDef (ZSPlain st []) (ZSchema nstn))  ls ma ))))):(normal_state_proc spec xs))
  where
    nstn = restruct_state_proc spec std

normal_state_proc spec ((Process (CProcess n (ProcDef (ProcMain (ZSchemaDef (ZSPlain st _) std) ls ma)))):xs)
  = ((Process (CProcess n (ProcDef (ProcMain (ZSchemaDef (ZSPlain st []) (ZSchema nstn))  ls ma )))):(normal_state_proc spec xs))
  where
    nstn = restruct_state_proc spec std
normal_state_proc spec (_:xs) = (normal_state_proc spec xs)

restruct_state_proc spec (ZSchema s) = s
restruct_state_proc spec (ZS2 ZSAnd s1 s2)
  = restruct_state_proc spec s1 ++ restruct_state_proc spec s2
restruct_state_proc spec (ZSRef (ZSPlain s _) [] [])
  = restruct_state_proc spec $ get_state_from_spec spec s

\end{code}
\begin{code}
getChanName (ChanDotExp (ZVar (e,f,g))) = e
getChanName (ChanOutExp (ZVar (e,f,g))) = e
getChanName (ChanInp e) = e
getChanName (ChanInpPred e f) = e
\end{code}

\section{Prefixed Actions}
\begin{code}
prefixAction (CActionCommand c) = prefixActionCCommand c
prefixAction (CSPSeq ca1 ca2) = prefixAction ca1 && prefixAction ca2
prefixAction CSPSkip = True
prefixAction CSPStop = True
prefixAction CSPChaos = True
prefixAction (CSPCommAction _ ca) = prefixAction ca
prefixAction (CSPExtChoice ca1 ca2) = prefixAction ca1 && prefixAction ca2
prefixAction (CSPIntChoice ca1 ca2) = prefixAction ca1 && prefixAction ca2
prefixAction (CSPNSParal _ _ _ ca1 ca2) = prefixAction ca1 && prefixAction ca2
prefixAction (CSPNSInter _ _ ca1 ca2) = prefixAction ca1 && prefixAction ca2
prefixAction (CSPHide ca cs) = prefixAction ca
prefixAction (CSPRecursion _ ca) = prefixAction ca
prefixAction (CSPRepSeq _ ca) = prefixAction ca
prefixAction (CSPRepExtChoice _ ca) = prefixAction ca
prefixAction (CSPRepIntChoice _ ca) = prefixAction ca
prefixAction (CSPRepParalNS _ _ _ ca) = prefixAction ca
prefixAction (CSPRepInterlNS _ _ ca) = prefixAction ca
-- prefixAction (CActionName zn)
-- prefixAction (CSPParal cs ca1 ca2) prefixAction ca1 && prefixAction ca2
-- prefixAction (CSPInterleave ca1 ca2) = prefixAction ca1 && prefixAction ca2
prefixAction (CSPParAction zn ze) = True
-- prefixAction (CSPRenAction zn r)
-- prefixAction (CSPUnfAction zn ca) = prefixAction ca
-- prefixAction (CSPUnParAction zgf ca zn) = prefixAction ca
-- prefixAction (CSPRepParal cs zgf ca) = prefixAction ca
-- prefixAction (CSPRepInterl zgf ca ) = prefixAction ca
-- prefixAction (CSPGuard p ca)  = prefixAction ca
-- prefixAction (CActionCommand (CVarDecl zgf ca)) = prefixAction ca
prefixAction _ = False

prefixActionCCommand (CIf g) = prefixActionCGActions g
prefixActionCCommand (CVarDecl _ ca) = prefixAction ca
prefixActionCCommand _ = False

prefixActionCGActions (CircGAction p ca) = prefixAction ca
prefixActionCGActions (CircThenElse g1 g2) = prefixActionCGActions g1 && prefixActionCGActions g2
\end{code}
\subsection{New Memory model - distributed for state/local variables}

Here I'll put all the infrastructure whilst desigining the new distributed Memory Model,
but I'll keep any previous code above this section.

\begin{code}
-- 1. get_binding_types takes a ZGenFilt as input and gets the type of a Choose x T in a binding b_TYP.
{-
Memory - for the main memory (with parallel between type actions)
MemoryTYP - for replicated paralelism synchronising on "terminate"
MemoryTYPVar - for each variable in the bindings of TYP

-}
nmem_mkMemoryInternal :: [String] -> CAction
nmem_mkMemoryInternal [x] = (CSPParAction ("Memory"++x) [ZVar ((join_name "b" x),[],x)])
nmem_mkMemoryInternal (x:xs)
  = (CSPNSParal
      [ZVar ("\\emptyset",[],"")]
      (CChanSet ["terminate"])
      [ZVar ("\\emptyset",[],"")]
      (nmem_mkMemoryInternal xs)
      (nmem_mkMemoryInternal [x]))

nmem_mkMemory :: [ZGenFilt] -> [PPar]
nmem_mkMemory bst =
  [CParAction "Memory" (CircusAction (CActionCommand (CVResDecl (remdups $ filter_ZGenFilt_Choose bst) (nmem_mkMemoryInternal bstTypes))))]
  where
    nbst = (remdups $ filter_ZGenFilt_Choose bst)
    bstTypes = ( get_binding_types nbst)

nmem_mkMemoryTYPInternal :: [String] -> [PPar]
nmem_mkMemoryTYPInternal [] = []
nmem_mkMemoryTYPInternal [x] =
  [CParAction ("Memory"++x) (CircusAction (CActionCommand (CVResDecl [Choose ((join_name "b" x),[],"") (ZVar ("BINDING_"++x,[],""))] (CSPRepParal (CChanSet ["terminate"]) [Choose ("n",[],"") (ZCall (ZVar ("\\dom",[],"")) (ZVar ((join_name "b" x),[],"")))] (CSPParAction ("Memory"++x++"Var") [ZVar ("n",[],""),ZVar ((join_name "b" x),[],"")])))))]
nmem_mkMemoryTYPInternal (x:xs) =
  (nmem_mkMemoryTYPInternal [x])++(nmem_mkMemoryTYPInternal xs)



nmem_mkMemoryTYP :: [ZGenFilt] -> [PPar]
nmem_mkMemoryTYP bst
  =  (nmem_mkMemoryTYPInternal bstTypes)
  where
    nbst = (remdups $ filter_ZGenFilt_Choose bst)
    bstTypes = ( get_binding_types nbst)


nmem_mkMemoryTYPVarInternal :: [String] -> [PPar]
nmem_mkMemoryTYPVarInternal [] = []
nmem_mkMemoryTYPVarInternal [x]
  = [CParAction ("Memory"++x++"Var") (CircusAction (CActionCommand (CVResDecl [Choose ("n",[],"") (ZVar ((join_name "NAME" x),[],"")),Choose ((join_name "b" x),[],"") (ZVar ("BINDING_"++x,[],""))] (CSPExtChoice (CSPExtChoice (CSPCommAction (ChanComm "mget" [ChanDotExp (ZVar ("n",[],"")),ChanOutExp (ZCall (ZVar ((join_name "b" x),[],"")) (ZVar ("n",[],"")))]) (CSPParAction ("Memory"++x++"Var") [ZVar ("n",[],""),ZVar ((join_name "b" x),[],"")])) (CSPCommAction (ChanComm "mset" [ChanDotExp (ZVar ("n",[],"")),ChanInpPred "nv" (ZMember (ZVar ("nv",[],"")) (ZCall (ZVar ("\\delta",[],x)) (ZVar ("n",[],""))))]) (CSPParAction ("Memory"++x++"Var") [ZVar ("n",[],""),ZCall (ZVar ("\\oplus",[],"")) (ZTuple [ZVar ((join_name "b" x),[],""),ZSetDisplay [ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar ("n",[],""),ZVar ("nv",[],"")])]])]))) (CSPCommAction (ChanComm "terminate" []) CSPSkip)))))]
nmem_mkMemoryTYPVarInternal (x:xs) =
  (nmem_mkMemoryTYPVarInternal [x])++(nmem_mkMemoryTYPVarInternal xs)

nmem_mkMemoryTYPVar :: [ZGenFilt] -> [PPar]
nmem_mkMemoryTYPVar bst
  = (nmem_mkMemoryTYPVarInternal bstTypes)
  where
    nbst = (remdups $ filter_ZGenFilt_Choose bst)
    bstTypes = ( get_binding_types nbst)

\end{code}


\begin{code}
-- I'll produce one mget, mset, lget, and lset for each state variable

nmem_mkMemoryMergeInternal :: [String] -> CAction
nmem_mkMemoryMergeInternal [x] = (CSPParAction ("MemoryMerge"++x) [ZVar ((join_name "b" x),[],x)])
nmem_mkMemoryMergeInternal (x:xs)
  = (CSPNSParal
      [ZVar ("\\emptyset",[],"")]
      (CChanSet ["terminate"])
      [ZVar ("\\emptyset",[],"")]
      (nmem_mkMemoryMergeInternal xs)
      (nmem_mkMemoryMergeInternal [x]))

nmem_mkMemoryMerge :: [ZGenFilt] -> [PPar]
nmem_mkMemoryMerge bst =
  [CParAction "MemoryMerge" (CircusAction (CActionCommand (CVResDecl (remdups $ filter_ZGenFilt_Choose bst) (nmem_mkMemoryMergeInternal bstTypes))))]
  where
    nbst = (remdups $ filter_ZGenFilt_Choose bst)
    bstTypes = ( get_binding_types nbst)

nmem_mkMemoryMergeTYPInternal :: [String] -> [PPar]
nmem_mkMemoryMergeTYPInternal [] = []
nmem_mkMemoryMergeTYPInternal [x] =
  [CParAction ("MemoryMerge"++x) (CircusAction (CActionCommand (CVResDecl [Choose ((join_name "b" x),[],"") (ZVar ("BINDING_"++x,[],""))] (CSPRepParal (CChanSet ["terminate"]) [Choose ("n",[],"") (ZCall (ZVar ("\\dom",[],"")) (ZVar ((join_name "b" x),[],"")))] (CSPParAction ("MemoryMerge"++x++"Var") [ZVar ("n",[],""),ZVar ((join_name "b" x),[],"")])))))]
nmem_mkMemoryMergeTYPInternal (x:xs) =
  (nmem_mkMemoryMergeTYPInternal [x])++(nmem_mkMemoryMergeTYPInternal xs)



nmem_mkMemoryMergeTYP :: [ZGenFilt] -> [PPar]
nmem_mkMemoryMergeTYP bst
  =  (nmem_mkMemoryMergeTYPInternal bstTypes)
  where
    nbst = (remdups $ filter_ZGenFilt_Choose bst)
    bstTypes = ( get_binding_types nbst)


nmem_mkMemoryMergeTYPVarInternal :: [String] -> [PPar]
nmem_mkMemoryMergeTYPVarInternal [] = []
nmem_mkMemoryMergeTYPVarInternal [x]
  = [CParAction ("MemoryMerge"++x++"Var") (CircusAction (CActionCommand (CVResDecl [Choose ("n",[],"") (ZVar ((join_name "NAME" x),[],"")),Choose ((join_name "b" x),[],"") (ZVar ("BINDING_"++x,[],""))] (CSPExtChoice (CSPExtChoice (CSPCommAction (ChanComm "lget" [ChanDotExp (ZVar ("n",[],"")),ChanOutExp (ZCall (ZVar ((join_name "b" x),[],"")) (ZVar ("n",[],"")))]) (CSPParAction ("MemoryMerge"++x++"Var") [ZVar ("n",[],""),ZVar ((join_name "b" x),[],"")])) (CSPCommAction (ChanComm "lset" [ChanDotExp (ZVar ("n",[],"")),ChanInpPred "nv" (ZMember (ZVar ("nv",[],"")) (ZCall (ZVar ("\\delta",[],x)) (ZVar ("n",[],""))))]) (CSPParAction ("MemoryMerge"++x++"Var") [ZVar ("n",[],""),ZCall (ZVar ("\\oplus",[],"")) (ZTuple [ZVar ((join_name "b" x),[],""),ZSetDisplay [ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar ("n",[],""),ZVar ("nv",[],"")])]])]))) (CSPCommAction (ChanComm "terminate" []) CSPSkip)))))]
nmem_mkMemoryMergeTYPVarInternal (x:xs) =
  (nmem_mkMemoryMergeTYPVarInternal [x])++(nmem_mkMemoryMergeTYPVarInternal xs)

nmem_mkMemoryMergeTYPVar :: [ZGenFilt] -> [PPar]
nmem_mkMemoryMergeTYPVar bst
  = (nmem_mkMemoryMergeTYPVarInternal bstTypes)
  where
    nbst = (remdups $ filter_ZGenFilt_Choose bst)
    bstTypes = ( get_binding_types nbst)

\end{code}


\subsection{New Memory model - distributed for state/local variables}

Here I'll put all the infrastructure whilst desigining the new distributed Memory Model,
but I'll keep any previous code above this section.

\begin{code}
nmem_mkMemory1 :: [ZGenFilt] -> [PPar]
nmem_mkMemory1 bst =
  [CParAction "Memory" (CircusAction (CActionCommand (CVResDecl (remdups $ filter_ZGenFilt_Choose (data_refinement bst)) (nmem_mkMemoryInternal1 bstTypes))))]
  where
    nbst = (remdups $ filter_ZGenFilt_Choose bst)
    bstTypes = ( mk_st_zvar nbst)

nmem_mkMemoryInternal1 :: [ZVar] -> CAction
nmem_mkMemoryInternal1 [(x,_,y)] = (CSPParAction ("Memory_"++x) [ZVar ((join_name "b" (lastN 3 y)),[],x)])
nmem_mkMemoryInternal1 ((x,_,y):xs)
  = (CSPNSParal
      [ZVar ("\\emptyset",[],"")]
      (CChanSet ["terminate"])
      [ZVar ("\\emptyset",[],"")]
      (CSPParAction ("Memory_"++x) [ZVar ((join_name "b" (lastN 3 y)),[],x)])
      (nmem_mkMemoryInternal1 xs))

nmem_mkMemoryTYP1 :: [ZGenFilt] -> [PPar]
nmem_mkMemoryTYP1 bst
  =  (nmem_mkMemoryTYPInternal1 bstTypes)
  where
    nbst = (remdups $ filter_ZGenFilt_Choose bst)
    bstTypes = ( mk_st_zvar nbst)

nmem_mkMemoryTYPInternal1 :: [ZVar] -> [PPar]
nmem_mkMemoryTYPInternal1 [] = []
nmem_mkMemoryTYPInternal1 [(x,_,y)] =
  [CParAction ("Memory"++x) (CircusAction (CActionCommand (CVResDecl [Choose ((join_name "b" x),[],"") (ZVar ("BINDING_"++y,[],""))] (CSPRepParal (CChanSet ["terminate"]) [Choose ("n",[],"") (ZCall (ZVar ("\\dom",[],"")) (ZVar ((join_name "b" x),[],"")))] (CSPParAction ("Memory"++x++"Var") [ZVar ("n",[],""),ZVar ((join_name "b" x),[],"")])))))]
nmem_mkMemoryTYPInternal1 (x:xs) =
  (nmem_mkMemoryTYPInternal1 [x])++(nmem_mkMemoryTYPInternal1 xs)

nmem_mkMemoryTYPVar1 :: [ZGenFilt] -> [PPar]
nmem_mkMemoryTYPVar1 bst
  = (nmem_mkMemoryTYPVarInternal1 bstTypes)
  where
    nbst = (remdups $ filter_ZGenFilt_Choose bst)
    bstTypes = ( mk_st_zvar nbst)

nmem_mkMemoryTYPVarInternal1 :: [ZVar] -> [PPar]
nmem_mkMemoryTYPVarInternal1 [] = []
nmem_mkMemoryTYPVarInternal1 [(x,_,y)]
  = [CParAction ("Memory_"++x) (CircusAction (CSPRecursion "M" (CActionCommand (CVarDecl [Choose (("b_"++(lastN 3 y)),[],"") (ZVar (("BINDINGS_"++(lastN 3 y)),[],""))] (CSPExtChoice (CSPExtChoice (CSPCommAction (ChanComm ("mget_"++x) [ChanDotExp (ZCall (ZVar (("b_"++(lastN 3 y)),[],"")) (ZVar (x,[],"")))]) (CSPParAction "M" [ZVar (("b_"++(lastN 3 y)),[],"")])) (CSPCommAction (ChanComm ("mset_"++x) [ChanInp "nv"]) (CSPParAction "M" [ZCall (ZVar ("\\oplus",[],"")) (ZTuple [ZVar (("b_"++(lastN 3 y)),[],""),ZSetDisplay [ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar (x,[],y),ZVar ("nv",[],y)])]])]))) (CSPCommAction (ChanComm "terminate" []) CSPSkip))))))]
nmem_mkMemoryTYPVarInternal1 (x:xs) =
  (nmem_mkMemoryTYPVarInternal1 [x])++(nmem_mkMemoryTYPVarInternal1 xs)


\end{code}


\begin{code}
nmem_mkMemoryMerge1 :: [ZGenFilt] -> [PPar]
nmem_mkMemoryMerge1 bst =
  [CParAction "MemoryMerge" (CircusAction (CActionCommand (CVResDecl (remdups $ filter_ZGenFilt_Choose (data_refinement bst)) (nmem_mkMemoryMergeInternal1 bstTypes))))]
  where
    nbst = (remdups $ filter_ZGenFilt_Choose bst)
    bstTypes = ( mk_st_zvar nbst)

nmem_mkMemoryMergeInternal1 :: [ZVar] -> CAction
nmem_mkMemoryMergeInternal1 [(x,_,y)] = (CSPParAction ("MemoryMerge_"++x) [ZVar ((join_name "b" (lastN 3 y)),[],x)])
nmem_mkMemoryMergeInternal1 ((x,_,y):xs)
  = (CSPNSParal
      [ZVar ("\\emptyset",[],"")]
      (CChanSet ["terminate"])
      [ZVar ("\\emptyset",[],"")]
      (CSPParAction ("MemoryMerge_"++x) [ZVar ((join_name "b" (lastN 3 y)),[],x)])
      (nmem_mkMemoryMergeInternal1 xs))

nmem_mkMemoryMergeTYP1 :: [ZGenFilt] -> [PPar]
nmem_mkMemoryMergeTYP1 bst
  =  (nmem_mkMemoryMergeTYPInternal1 bstTypes)
  where
    nbst = (remdups $ filter_ZGenFilt_Choose bst)
    bstTypes = ( mk_st_zvar nbst)

nmem_mkMemoryMergeTYPInternal1 :: [ZVar] -> [PPar]
nmem_mkMemoryMergeTYPInternal1 [] = []
nmem_mkMemoryMergeTYPInternal1 [(x,_,y)] =
  [CParAction ("MemoryMerge"++x) (CircusAction (CActionCommand (CVResDecl [Choose ((join_name "b" x),[],"") (ZVar ("BINDING_"++y,[],""))] (CSPRepParal (CChanSet ["terminate"]) [Choose ("n",[],"") (ZCall (ZVar ("\\dom",[],"")) (ZVar ((join_name "b" x),[],"")))] (CSPParAction ("MemoryMerge"++x++"Var") [ZVar ("n",[],""),ZVar ((join_name "b" x),[],"")])))))]
nmem_mkMemoryMergeTYPInternal1 (x:xs) =
  (nmem_mkMemoryMergeTYPInternal1 [x])++(nmem_mkMemoryMergeTYPInternal1 xs)

nmem_mkMemoryMergeTYPVar1 :: [ZGenFilt] -> [PPar]
nmem_mkMemoryMergeTYPVar1 bst
  = (nmem_mkMemoryMergeTYPVarInternal1 bstTypes)
  where
    nbst = (remdups $ filter_ZGenFilt_Choose bst)
    bstTypes = ( mk_st_zvar nbst)

nmem_mkMemoryMergeTYPVarInternal1 :: [ZVar] -> [PPar]
nmem_mkMemoryMergeTYPVarInternal1 [] = []
nmem_mkMemoryMergeTYPVarInternal1 [(x,_,y)]
  = [CParAction ("MemoryMerge_"++x) (CircusAction (CSPRecursion "M" (CActionCommand (CVarDecl [Choose (("b_"++(lastN 3 y)),[],"") (ZVar (("BINDINGS_"++(lastN 3 y)),[],""))] (CSPExtChoice (CSPExtChoice (CSPCommAction (ChanComm ("lget_"++x) [ChanDotExp (ZCall (ZVar (("b_"++(lastN 3 y)),[],"")) (ZVar (x,[],"")))]) (CSPParAction "M" [ZVar (("b_"++(lastN 3 y)),[],"")])) (CSPCommAction (ChanComm ("lset_"++x) [ChanInp "nv"]) (CSPParAction "M" [ZCall (ZVar ("\\oplus",[],"")) (ZTuple [ZVar (("b_"++(lastN 3 y)),[],""),ZSetDisplay [ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar (x,[],y),ZVar ("nv",[],y)])]])]))) (CSPCommAction (ChanComm "terminate" []) CSPSkip))))))]
nmem_mkMemoryMergeTYPVarInternal1 (x:xs) =
  (nmem_mkMemoryMergeTYPVarInternal1 [x])++(nmem_mkMemoryMergeTYPVarInternal1 xs)

\end{code}



\subsubsection{Getting Types from Circus Process}
\begin{code}
getType_ProcDecl :: ProcDecl -> [ZGenFilt]
getType_ProcDecl (CProcess vZName vProcessDef) = []
getType_ProcDecl (CParamProcess vZName vZName_lst vProcessDef) = []
getType_ProcDecl (CGenProcess vZName vZName_lst vProcessDef) = []
\end{code}
\begin{code}
getType_ProcessDef :: ProcessDef -> [ZGenFilt]
getType_ProcessDef (ProcDefSpot vZGenFilt_lst vProcessDef) = vZGenFilt_lst++[]
getType_ProcessDef (ProcDefIndex vZGenFilt_lst vProcessDef) = vZGenFilt_lst++[]
getType_ProcessDef (ProcDef vCProc) = []
\end{code}
\begin{code}
getType_CProc :: CProc -> [ZGenFilt]
getType_CProc (CRepSeqProc vZGenFilt_lst vCProc) = vZGenFilt_lst++(getType_CProc vCProc)
getType_CProc (CRepExtChProc vZGenFilt_lst vCProc) = vZGenFilt_lst++(getType_CProc vCProc)
getType_CProc (CRepIntChProc vZGenFilt_lst vCProc) = vZGenFilt_lst++(getType_CProc vCProc)
getType_CProc (CRepParalProc vCSExp vZGenFilt_lst vCProc) = vZGenFilt_lst++(getType_CProc vCProc)
getType_CProc (CRepInterlProc vZGenFilt_lst vCProc) = vZGenFilt_lst++(getType_CProc vCProc)
getType_CProc (CHide vCProc vCSExp) = []
getType_CProc (CExtChoice v1CProc v2CProc) = (getType_CProc v1CProc)++(getType_CProc v2CProc)
getType_CProc (CIntChoice v1CProc v2CProc) = (getType_CProc v1CProc)++(getType_CProc v2CProc)
getType_CProc (CParParal vCSExp v1CProc v2CProc) = (getType_CProc v1CProc)++(getType_CProc v2CProc)
getType_CProc (CInterleave v1CProc v2CProc) = (getType_CProc v1CProc)++(getType_CProc v2CProc)
getType_CProc (CGenProc vZName vZExpr_lst) = []
getType_CProc (CParamProc vZName vZExpr_lst) = []
getType_CProc (CProcRename vZName vComm_lst1 vComm_lst) = []
getType_CProc (CSeq v1CProc v2CProc) = (getType_CProc v1CProc)++(getType_CProc v2CProc)
getType_CProc (CSimpIndexProc vZName vZExpr_lst) = []
getType_CProc (CircusProc vZName) = []
getType_CProc (ProcMain _ZPara vPPar_lst vCAction) = []
getType_CProc (ProcStalessMain vPPar_lst vCAction) = []
\end{code}
\subsubsection{Getting Types from Circus Actions}
\begin{code}
getType_PPar :: PPar -> [ZGenFilt]
getType_PPar (ProcZPara vZPara) = []
getType_PPar (CParAction vZName vParAction)
  = (getType_ParAction vParAction)
getType_PPar (CNameSet vZName vNSExp) = []
\end{code}
\begin{code}
getType_ParAction :: ParAction -> [ZGenFilt]
getType_ParAction (CircusAction vCAction) = []
getType_ParAction (ParamActionDecl vZGenFilt_lst vParAction)
  = vZGenFilt_lst++(getType_ParAction vParAction)
\end{code}
\begin{code}
getType_CAction :: CAction -> [ZGenFilt]
getType_CAction (CActionSchemaExpr vZSExpr) = []
getType_CAction (CActionCommand vCCommand) = []
getType_CAction (CActionName vZName) = []
getType_CAction (CSPSkip ) = []
getType_CAction (CSPStop) = []
getType_CAction (CSPChaos) = []
getType_CAction (CSPCommAction vComm vCAction)
  = (getType_CAction vCAction)
getType_CAction (CSPGuard vZPred vCAction)
  = (getType_CAction vCAction)
getType_CAction (CSPSeq v1CAction v2CAction)
  = (getType_CAction v1CAction)++(getType_CAction v2CAction)
getType_CAction (CSPExtChoice v1CAction v2CAction)
  = (getType_CAction v1CAction)++(getType_CAction v2CAction)
getType_CAction (CSPIntChoice v1CAction v2CAction)
  = (getType_CAction v1CAction)++(getType_CAction v2CAction)
getType_CAction (CSPNSParal v1NSExp vCSExp v2NSExp v1CAction v2CAction)
  = (getType_CAction v1CAction)++(getType_CAction v2CAction)
getType_CAction (CSPParal vCSExp v1CAction v2CAction)
  = (getType_CAction v1CAction)++(getType_CAction v2CAction)
getType_CAction (CSPNSInter v1NSExp v2NSExp v1CAction v2CAction)
  = (getType_CAction v1CAction)++(getType_CAction v2CAction)
getType_CAction (CSPInterleave v1CAction v2CAction)
  = (getType_CAction v1CAction)++(getType_CAction v2CAction)
getType_CAction (CSPHide vCAction vCSExp) = (getType_CAction vCAction)
getType_CAction (CSPParAction vZName vZExpr_lst) = []
getType_CAction (CSPRenAction vZName vCReplace) = []
getType_CAction (CSPRecursion vZName vCAction)
  = (getType_CAction vCAction)
getType_CAction (CSPUnfAction vZName vCAction)
  = (getType_CAction vCAction)
getType_CAction (CSPUnParAction vZGenFilt_lst vCAction vZName)
  =(getType_CAction vCAction)
getType_CAction (CSPRepSeq vZGenFilt_lst vCAction)
  =(getType_CAction vCAction)
getType_CAction (CSPRepExtChoice vZGenFilt_lst vCAction)
  =(getType_CAction vCAction)
getType_CAction (CSPRepIntChoice vZGenFilt_lst vCAction)
  =(getType_CAction vCAction)
getType_CAction (CSPRepParalNS _CSExp vZGenFilt_lst vNSExp vCAction)
  =(getType_CAction vCAction)
getType_CAction (CSPRepParal _CSExp vZGenFilt_lst vCAction)
  =(getType_CAction vCAction)
getType_CAction (CSPRepInterlNS vZGenFilt_lst vNSExp vCAction)
  =(getType_CAction vCAction)
getType_CAction (CSPRepInterl vZGenFilt_lst vCAction)
  =(getType_CAction vCAction)
\end{code}

\subsubsection{Circus Communication}

\begin{code}
getType_Comm :: Comm -> [ZGenFilt]
getType_Comm (ChanComm vZName vCParameter_lst) = []
getType_Comm (ChanGenComm vZName vZExpr_lst vCParameter_lst) = []
\end{code}
\begin{code}

getType_CParameter :: CParameter -> [ZGenFilt]
getType_CParameter (ChanInp vZName) = []
getType_CParameter (ChanInpPred vZName _ZPred) = []
getType_CParameter (ChanOutExp _ZExpr) = []
getType_CParameter (ChanDotExp _ZExpr) = []
\end{code}

\subsubsection{Circus Commands}

\begin{code}
getType_CCommand :: CCommand -> [ZGenFilt]
getType_CCommand (CAssign vZVar_lst vZExpr_lst) = []
getType_CCommand (CIf vCGActions) = []
getType_CCommand (CVarDecl vZGenFilt_lst vCAction)
  = vZGenFilt_lst++(getType_CAction vCAction)
getType_CCommand (CAssumpt vZName_lst v1ZPred v2ZPred) = []
getType_CCommand (CAssumpt1 vZName_lst vZPred) = []
getType_CCommand (CPrefix v1ZPred v2ZPred) = []
getType_CCommand (CPrefix1 _ZPred) = []
getType_CCommand (CommandBrace _ZPred) = []
getType_CCommand (CommandBracket _ZPred) = []
getType_CCommand (CValDecl vZGenFilt_lst vCAction)
  = vZGenFilt_lst++(getType_CAction vCAction)
getType_CCommand (CResDecl vZGenFilt_lst vCAction)
  = vZGenFilt_lst++(getType_CAction vCAction)
getType_CCommand (CVResDecl vZGenFilt_lst vCAction)
  = vZGenFilt_lst++(getType_CAction vCAction)
\end{code}

\begin{code}
getType_CGActions :: CGActions  -> [ZGenFilt]
getType_CGActions (CircGAction _ZPred vCAction)
  = (getType_CAction vCAction)
getType_CGActions (CircThenElse v1CGActions v2CGActions)
  = (getType_CGActions v1CGActions)++(getType_CGActions v2CGActions)

rename_ftv nm (ZBranch0 (a,b,c)) = (ZBranch0 (a,b,nm))


\end{code}
\begin{code}
-- getting all ZVar from a ZPredicate

get_v_ZGenFilt (Include _ZSExpr) = []
get_v_ZGenFilt (Choose _ZVar _ZExpr) = get_v_ZExpr _ZExpr
get_v_ZGenFilt (Check _ZPred) = (get_v_ZPred _ZPred)
get_v_ZGenFilt (Evaluate _ZVar _ZExpr1 _ZExpr2) = (get_v_ZExpr _ZExpr1)++(get_v_ZExpr _ZExpr2)

get_v_ZExpr :: ZExpr -> [ZVar]
get_v_ZExpr (ZVar v) = get_ZVar_st v
get_v_ZExpr (ZInt _ZInt) = []
get_v_ZExpr (ZGiven _GivenValue) = []
get_v_ZExpr (ZFree0 _ZVar) = []
get_v_ZExpr (ZFree1 _ZVar _ZExpr) = get_v_ZExpr _ZExpr
get_v_ZExpr (ZTuple _ZExpr_lst) = (concat $ map get_v_ZExpr _ZExpr_lst)
get_v_ZExpr (ZBinding _ZVar_ZExpr_lst) = (concat $ map (\(a,b) -> [a]++(get_v_ZExpr b)) _ZVar_ZExpr_lst)
get_v_ZExpr (ZSetDisplay _ZExpr_lst) = (concat $ map get_v_ZExpr _ZExpr_lst)
get_v_ZExpr (ZSeqDisplay _ZExpr_lst) = (concat $ map get_v_ZExpr _ZExpr_lst)
get_v_ZExpr (ZFSet _ZFSet) = []
get_v_ZExpr (ZIntSet mze mze2) = []
get_v_ZExpr (ZGenerator _ZReln _ZExpr) = get_v_ZExpr _ZExpr
get_v_ZExpr (ZCross _ZExpr_lst) = (concat $ map get_v_ZExpr _ZExpr_lst)
get_v_ZExpr (ZFreeType _ZVar _ZBranch_lst) = []

get_v_ZExpr (ZSetComp _ZGenFilt_lst mze) = concat $ map get_v_ZGenFilt _ZGenFilt_lst
get_v_ZExpr (ZLambda _ZGenFilt_lst _ZExpr) = (get_v_ZExpr _ZExpr)
get_v_ZExpr (ZESchema _ZSExpr) = []
get_v_ZExpr (ZGivenSet _GivenSet) = []
get_v_ZExpr (ZUniverse) = undefined
get_v_ZExpr (ZCall _ZExpr1 _ZExpr2) = (get_v_ZExpr _ZExpr1)++(get_v_ZExpr _ZExpr2)
get_v_ZExpr (ZReln _ZReln) = []
get_v_ZExpr (ZFunc1 _ZFunc1) = []
get_v_ZExpr (ZFunc2 _ZFunc2) = []
get_v_ZExpr (ZStrange _ZStrange) = []
get_v_ZExpr (ZMu _ZGenFilt_lst mze) = []
get_v_ZExpr (ZELet _ZVar_ZExpr_lst _ZExpr) = (get_v_ZExpr _ZExpr) ++ (concat $ map (\(a,b) -> [a]++(get_v_ZExpr b)) _ZVar_ZExpr_lst)
get_v_ZExpr (ZIf_Then_Else _ZPred _ZExpr1 _ZExpr2) = (get_v_ZExpr _ZExpr1)++(get_v_ZExpr _ZExpr2)
get_v_ZExpr (ZSelect _ZExpr _ZVar) = get_v_ZExpr _ZExpr
get_v_ZExpr _ = []

get_v_ZPred (ZAnd _ZPred1 _ZPred2) = (get_v_ZPred _ZPred1) ++ (get_v_ZPred _ZPred2)
get_v_ZPred (ZOr _ZPred1 _ZPred2) = (get_v_ZPred _ZPred1) ++ (get_v_ZPred _ZPred2)
get_v_ZPred (ZImplies _ZPred1 _ZPred2) = (get_v_ZPred _ZPred1) ++ (get_v_ZPred _ZPred2)
get_v_ZPred (ZIff _ZPred1 _ZPred2) = (get_v_ZPred _ZPred1) ++ (get_v_ZPred _ZPred2)
get_v_ZPred (ZNot _ZPred) = (get_v_ZPred _ZPred)
get_v_ZPred (ZExists _ZGenFilt_lst _ZPred) = (get_v_ZPred _ZPred)
get_v_ZPred (ZExists_1 _ZGenFilt_lst _ZPred) = (get_v_ZPred _ZPred)
get_v_ZPred (ZForall _ZGenFilt_lst _ZPred) = (get_v_ZPred _ZPred)
get_v_ZPred (ZPLet _ZVar_ZExpr_lst _ZPred) = (get_v_ZPred _ZPred)
get_v_ZPred (ZEqual _ZExpr1 _ZExpr2) = (get_v_ZExpr _ZExpr1)++(get_v_ZExpr _ZExpr2)
get_v_ZPred (ZMember _ZExpr1 _ZExpr2) = (get_v_ZExpr _ZExpr1)++(get_v_ZExpr _ZExpr2)
get_v_ZPred _ = []
\end{code}


\section{Schemas to Circus Actions}
\begin{code}
{-

I'm trying to make a translation from Z schemas to Circus actions

Here is the Haskell representation of the scheduler from Jaza examples
I'm pattern matching variables, so it is not that readable anymore.
Just using the predicates
ZSchemaDef sname (ZSchema [Choose ("active",[],"") (ZCall (ZVar ("\\finset",[],"")) (ZVar ("PID",[],""))),Choose ("ready",[],"") (ZCall (ZVar ("\\finset",[],"")) (ZVar ("PID",[],""))),Choose ("waiting",[],"") (ZCall (ZVar ("\\finset",[],"")) (ZVar ("PID",[],""))),
	Check (ZMember (ZTuple [ZCall (ZVar ("\\#",[],"")) (ZVar ("active",[],"")),ZInt 1]) (ZVar ("\\leq",[],""))),
	Check (ZEqual (ZCall (ZVar ("\\cap",[],"")) (ZTuple [ZVar ("ready",[],""),ZVar ("waiting",[],"")])) (ZVar ("\\emptyset",[],""))),
	Check (ZEqual (ZCall (ZVar ("\\cap",[],"")) (ZTuple [ZVar ("active",[],""),ZVar ("waiting",[],"")])) (ZVar ("\\emptyset",[],""))),
	Check (ZEqual (ZCall (ZVar ("\\cap",[],"")) (ZTuple [ZVar ("active",[],""),ZVar ("ready",[],"")])) (ZVar ("\\emptyset",[],""))),
	Check (ZImplies (ZEqual (ZVar ("active",[],"")) (ZVar ("\\emptyset",[],""))) (ZEqual (ZVar ("ready",[],"")) (ZVar ("\\emptyset",[],""))))])
ZSchemaDef sname (ZSchema [
	Include (ZSRef sname [] []),
	Check (ZAnd (ZEqual (ZVar ("active",[],"")) (ZVar ("ready",[],""))) (ZAnd (ZEqual (ZVar ("ready",[],"")) (ZVar ("waiting",[],""))) (ZEqual (ZVar ("waiting",[],"")) (ZSetDisplay []))))])
ZSchemaDef sname (ZSchema [
	Include (ZSRef (ZSDelta "Scheduler") [] []),
  Choose ("pp",["?"],"") (ZVar ("PID",[],"")),
	Check (ZNot (ZMember (ZVar ("pp",["?"],"")) (ZCall (ZVar ("\\cup",[],"")) (ZTuple [ZCall (ZVar ("\\cup",[],"")) (ZTuple [ZVar ("active",[],""),ZVar ("ready",[],"")]),ZVar ("waiting",[],"")])))),
	Check (ZEqual (ZVar (v,["'"],"")) e)
	Check (ZEqual (ZVar (v,["'"],"")) e)
	Check (ZEqual (ZVar (v,["'"],"")) e)
ZSchemaDef sname (ZSchema [
	Include (ZSRef (ZSDelta "Scheduler") [] []),
  Choose ("pp",["?"],"") (ZVar ("PID",[],"")),
	Check (ZMember (ZVar ("pp",["?"],"")) (ZVar ("waiting",[],""))),
	Check (ZEqual (ZVar (v,["'"],"")) e)
	Check (ZImplies (ZEqual (ZVar (v,["'"],"")) (ZSetDisplay [ZVar (v,["'"],"")) (ZVar ("ready",[],""))))),
	Check (ZImplies (ZNot (ZEqual (ZVar (v,["'"],"")) (ZVar (v,["'"],"")) (ZCall (ZVar ("\\cup",[],"")) (ZTuple [ZVar ("ready",[],""),ZSetDisplay [ZVar ("pp",["?"],"")]])))))])
ZSchemaDef sname (ZSchema [
	Include (ZSRef (ZSDelta "Scheduler") [] []),
  Choose ("pp",["!"],"") (ZVar ("PID",[],"")),
	Check (ZNot (ZEqual (ZVar ("active",[],"")) (ZSetDisplay []))),
	Check (ZMember (ZVar ("pp",["!"],"")) (ZVar ("ready",[],""))),
	Check (ZEqual (ZVar (v,["'"],"")) e)
	Check (ZEqual (ZVar (v,["'"],"")) e)
ZSchemaDef sname (ZSchema [
	Include (ZSRef (ZSDelta "Scheduler") [] []),
	Check (ZNot (ZEqual (ZVar ("active",[],"")) (ZSetDisplay []))),
	Check (ZEqual (ZVar ("ready",[],"")) (ZSetDisplay [])),
	Check (ZEqual (ZVar (v,["'"],"")) e)
	Check (ZEqual (ZVar (v,["'"],"")) e)
ZSchemaDef sname (ZSchema [
  Choose ("state",[],"") (ZVar ("Scheduler",[],"")),
  Choose ("init",[],"") (ZVar ("Init",[],"")),
  Choose ("new",[],"") (ZVar ("New",[],"")),
  Choose ("ready",[],"") (ZVar ("Ready",[],"")),
  Choose ("swap",[],"") (ZVar ("Swap",[],""))])

-}

is_predicate :: ZPred -> Bool
is_predicate (ZFalse{reason=_}) = True
is_predicate (ZTrue{reason=_}) = True
is_predicate (ZAnd a b) = is_predicate a && is_predicate b
is_predicate (ZOr a b) = is_predicate a && is_predicate b
is_predicate (ZImplies a b) = is_predicate a && is_predicate b
is_predicate (ZIff a b) = is_predicate a && is_predicate b
is_predicate (ZNot _ZPred) = True
is_predicate (ZExists _ _) = True
is_predicate (ZExists_1 _ _) = True
is_predicate (ZForall _ _) = True
is_predicate (ZPLet _ _) = True
is_predicate (ZEqual (ZVar v) _) = not (is_primed_zvar v)
is_predicate (ZMember _ _) = True
is_predicate _ = True
\end{code}

This function will convert the structure of schemas into Circus actions.
It also will transform any precondition as a predicate for guards in Circus
\begin{code}
get_schema_guards :: [ZPara] -> ZSExpr -> CAction
get_schema_guards xls (ZSRef (ZSPlain x _) [] [])
  = (CActionName x)
get_schema_guards xls (ZS2 ZSAnd (ZSchema x1) (ZSchema x2))
  = (get_schema_guards xls (ZSchema (x1++x2)))
get_schema_guards xls (ZS2 ZSOr x1 x2)
  = (CSPExtChoice (get_schema_guards xls x1) (get_schema_guards xls x2))
get_schema_guards xls (ZS2 ZSSemi x1 x2)
  = (CSPSeq (get_schema_guards xls x1) (get_schema_guards xls x2))
get_schema_guards xls (ZSchema xs)
  = get_schema_guards' xls (concat $ map getChooseFrom_ZGenFilt xs)

get_schema_guards' :: [ZPara] -> [ZPred] -> CAction
get_schema_guards' schls xs
  | not(null(fst(find_schema_guards schls xs [] []))) = (make_schema_guards schls xs)
  | otherwise = (schema_to_cactions schls xs)
\end{code}

Filtering Choose from ZGenFilt
\begin{code}
getChooseFrom_ZGenFilt :: ZGenFilt -> [ZPred]
getChooseFrom_ZGenFilt (Include _) = []
getChooseFrom_ZGenFilt (Choose _ _) = []
getChooseFrom_ZGenFilt (Check e) = [e]
getChooseFrom_ZGenFilt (Evaluate _ _ _) = []
\end{code}

Filtering preconditions for guards: g is a list of guards, e is the remaining elements of the xs list

\begin{code}
find_schema_guards xs [] g e = (concat g, concat e)
find_schema_guards xs [x] g e
  | is_predicate x = find_schema_guards xs [] ([x]:g) e
  | otherwise = find_schema_guards xs [] g ([x]:e)
find_schema_guards xls (x:xs) g e
  | is_predicate x = find_schema_guards xls xs ([x]:g) e
  | otherwise = find_schema_guards xls xs g ([x]:e)
\end{code}

\begin{code}
make_schema_guards xls xs =
    (CSPGuard (make_guards g) (schema_to_cactions xls e))
    where
      (g,e) = (find_schema_guards xls xs [] [])
      make_guards [x] = x
      make_guards (x:xs) = (ZAnd x (make_guards xs))
\end{code}

\begin{code}
schema_to_cactions :: [ZPara] -> [ZPred] -> CAction
schema_to_cactions _ [] = CSPSkip
schema_to_cactions xs [ZEqual (ZVar (v,[ZPrime],"")) e]
  = (CActionCommand (CAssign [(v,[],"")] [e]))
schema_to_cactions xs [ZAnd e@(ZEqual (ZVar e1) e2) f@(ZEqual (ZVar e3) e4)]
  | (is_primed_zvar e1 && is_primed_zvar e3)
          = (CSPSeq (schema_to_cactions xs [e]) (schema_to_cactions xs [f]))
  | otherwise = error "Could not translate to CAction"
schema_to_cactions xs [axs@(ZAnd e f)]
  | (is_predicate e && not(is_predicate f))
          = (CSPGuard e (schema_to_cactions xs [f]))
  | (is_predicate f && not(is_predicate e))
          = (CSPGuard f (schema_to_cactions xs [e]))
  | otherwise = error ("Could not translate ZAnd to CAction" ++ show axs)
  -- | otherwise = error ("Could not translate ZAnd to CAction" ++ show axs)
schema_to_cactions xs [ZImplies e@(ZEqual (ZVar e1) e2) f@(ZEqual (ZVar e3) e4)]
  | (is_predicate e && is_primed_zvar e3)
          = (CSPGuard e (schema_to_cactions xs [f]))
  | otherwise = error "Could not translate ZImplies to CAction"
schema_to_cactions xs [ZImplies e f@(ZEqual (ZVar e3) e4)]
  | (is_predicate e && is_primed_zvar e3)
          = (CSPGuard e (schema_to_cactions xs [f]))
  | otherwise = error "Could not translate to CAction"
schema_to_cactions xls ((ZEqual (ZVar (v,[ZPrime],"")) e):xs)
  = (CSPSeq (CActionCommand (CAssign [(v,[],"")] [e]))(schema_to_cactions xls xs))
schema_to_cactions xls ((ZAnd e@(ZEqual (ZVar e1) e2) f@(ZEqual (ZVar e3) e4)):xs)
  | (is_primed_zvar e1 && is_primed_zvar e3)
          = (CSPSeq (CSPSeq (schema_to_cactions xls [e]) (schema_to_cactions xls [f]))(schema_to_cactions xls xs))
  | otherwise = error "Could not translate to CAction"
schema_to_cactions xls ((ZAnd e f):xs)
  | (is_predicate e && not(is_predicate f))
          = (CSPSeq (CSPGuard e (schema_to_cactions xls [f]))(schema_to_cactions xls xs))
  | (is_predicate f && not(is_predicate e))
          = (CSPSeq (CSPGuard f (schema_to_cactions xls [e]))(schema_to_cactions xls xs))
  | otherwise = error "Could not translate to CAction"
schema_to_cactions xls ((ZImplies e f@(ZEqual (ZVar e3) e4)):xs)
  | (is_predicate e && is_primed_zvar e3)
          = (CSPSeq (CSPGuard e (schema_to_cactions xls [f]))(schema_to_cactions xls xs))
  | otherwise = error "Could not translate to CAction"
-- schema_to_cactions xls ((ZImplies e f@(ZEqual (ZVar e3) e4)):xs)
--   | (is_predicate e && is_primed_zvar e3)
--           = (CSPSeq (CSPGuard e (schema_to_cactions xls [f]))(schema_to_cactions xls xs))
--   | otherwise = error "Could not translate to CAction"
schema_to_cactions xls (_:xs) = (schema_to_cactions xls xs)
\end{code}

\begin{code}
procZParaToCParAction xs (ProcZPara (ZSchemaDef (ZSPlain sname _) s))
  = (CParAction sname (CircusAction (get_schema_guards xs s)))
procZParaToCParAction xs (CParAction n p)
  = (CParAction n (pZPtoCA_ParAction xs p))
pZPtoCA_PPar x = x
\end{code}
\subsection{Parametrised Actions}
\begin{code}
pZPtoCA_ParAction xs (CircusAction ca)
  = (CircusAction (pZPtoCAca xs ca))
pZPtoCA_ParAction xs (ParamActionDecl _zgf_lst _ParAction)
  = (ParamActionDecl _zgf_lst (pZPtoCA_ParAction xs _ParAction))
\end{code}
\subsection{\Circus\ Actions}
\begin{code}
pZPtoCAca xs (CActionSchemaExpr nm)
  = (get_schema_guards xs nm)
pZPtoCAca xs (CActionCommand c)
  = (CActionCommand (pZPtoCA_CCommand xs c))
pZPtoCAca xs (CSPCommAction _Comm ca)
  = (CSPCommAction _Comm (pZPtoCAca xs ca))
pZPtoCAca xs (CSPGuard _ZPred ca)
  = (CSPGuard _ZPred (pZPtoCAca xs ca))
pZPtoCAca xs (CSPSeq ca1 ca2)
  = (CSPSeq (pZPtoCAca xs ca1) (pZPtoCAca xs ca2))
pZPtoCAca xs (CSPExtChoice ca1 ca2)
  = (CSPExtChoice (pZPtoCAca xs ca1) (pZPtoCAca xs ca2))
pZPtoCAca xs (CSPIntChoice ca1 ca2)
  = (CSPIntChoice (pZPtoCAca xs ca1) (pZPtoCAca xs ca2))
pZPtoCAca xs (CSPNSParal _zx_lst c _zx_lst1 ca1 ca2)
  = (CSPNSParal _zx_lst c _zx_lst1 (pZPtoCAca xs ca1) (pZPtoCAca xs ca2))
pZPtoCAca xs (CSPParal _CSExp ca1 ca2)
  = (CSPParal _CSExp (pZPtoCAca xs ca1) (pZPtoCAca xs ca2))
pZPtoCAca xs (CSPNSInter _zx_lst _zx_lst1 ca1 ca2)
  = (CSPNSInter _zx_lst _zx_lst1 (pZPtoCAca xs ca1) (pZPtoCAca xs ca2))
pZPtoCAca xs (CSPInterleave ca1 ca2)
  = (CSPInterleave (pZPtoCAca xs ca1) (pZPtoCAca xs ca2))
pZPtoCAca xs (CSPHide ca _CSExp)
  = (CSPHide (pZPtoCAca xs ca) _CSExp)
pZPtoCAca xs (CSPParAction _ZName _zx_lst)
  = (CSPParAction _ZName _zx_lst)
pZPtoCAca xs (CSPRenAction _ZName _CReplace)
  = (CSPRenAction _ZName _CReplace)
pZPtoCAca xs (CSPRecursion _ZName ca)
  = (CSPRecursion _ZName (pZPtoCAca xs ca))
pZPtoCAca xs (CSPUnfAction _ZName ca)
  = (CSPUnfAction _ZName (pZPtoCAca xs ca))
pZPtoCAca xs (CSPUnParAction _zgf_lst ca n)
  = (CSPUnParAction _zgf_lst (pZPtoCAca xs ca) n)
pZPtoCAca xs (CSPRepSeq _zgf_lst ca)
  = (CSPRepSeq _zgf_lst (pZPtoCAca xs ca))
pZPtoCAca xs (CSPRepExtChoice _zgf_lst ca)
  = (CSPRepExtChoice _zgf_lst (pZPtoCAca xs ca))
pZPtoCAca xs (CSPRepIntChoice _zgf_lst ca)
  = (CSPRepIntChoice _zgf_lst (pZPtoCAca xs ca))
pZPtoCAca xs (CSPRepParalNS _CSExp _zgf_lst _zx_lst ca)
  = (CSPRepParalNS _CSExp _zgf_lst _zx_lst (pZPtoCAca xs ca))
pZPtoCAca xs (CSPRepParal _CSExp _zgf_lst ca)
  = (CSPRepParal _CSExp _zgf_lst (pZPtoCAca xs ca))
pZPtoCAca xs (CSPRepInterlNS _zgf_lst _zx_lst ca)
  = (CSPRepInterlNS _zgf_lst _zx_lst (pZPtoCAca xs ca))
pZPtoCAca xs (CSPRepInterl _zgf_lst ca)
  = (CSPRepInterl _zgf_lst (pZPtoCAca xs ca))
pZPtoCAca xs x = x
\end{code}
\subsection{\Circus\ Commands}
\begin{code}
pZPtoCA_CCommand xs (CIf g)
  = (CIf (pZPtoCA_CGActions xs g))
pZPtoCA_CCommand xs (CVarDecl _zgf_lst ca)
  = (CVarDecl _zgf_lst (pZPtoCAca xs ca))
pZPtoCA_CCommand xs (CValDecl _zgf_lst ca)
  = (CValDecl _zgf_lst (pZPtoCAca xs ca))
pZPtoCA_CCommand xs (CResDecl _zgf_lst ca)
  = (CResDecl _zgf_lst (pZPtoCAca xs ca))
pZPtoCA_CCommand xs (CVResDecl _zgf_lst ca)
  = (CVResDecl _zgf_lst (pZPtoCAca xs ca))
pZPtoCA_CCommand xs x = x
\end{code}
\subsection{\Circus\ Guards}
\begin{code}
pZPtoCA_CGActions xs (CircGAction _ZPred ca)
  = (CircGAction _ZPred (pZPtoCAca xs ca))
pZPtoCA_CGActions xs (CircThenElse g g1)
  = (CircThenElse (pZPtoCA_CGActions xs g) (pZPtoCA_CGActions xs g1))
\end{code}
\begin{code}
convert_schema_to_action schls [] = []
convert_schema_to_action schls ((Process (CProcess n (ProcDefSpot ff (ProcDef (ProcMain s ls ca))))):xs)
  = ((Process (CProcess n (ProcDefSpot ff (ProcDef (ProcMain s nls (pZPtoCAca schls ca) ))))):(convert_schema_to_action schls xs))
  where
    nls = map (procZParaToCParAction schls) ls
convert_schema_to_action schls ((Process (CProcess n (ProcDef (ProcMain s ls ca)))):xs)
  = ((Process (CProcess n (ProcDef (ProcMain s nls (pZPtoCAca schls ca) )))):(convert_schema_to_action schls xs))
  where
    nls = map (procZParaToCParAction schls) ls
convert_schema_to_action schls (_:xs) = (convert_schema_to_action schls xs)
\end{code}


\section{Retrieve Z Schemas into a list}

\section{Z Paragraphs}
\begin{code}
retr_sch_ZPara :: ZPara -> [ZPara]
retr_sch_ZPara (ZSchemaDef _ZSName _ZSExpr)
  = [(ZSchemaDef _ZSName _ZSExpr)]
retr_sch_ZPara (Process p) = (retr_sch_ProcDecl p)
retr_sch_ZPara x = []
\end{code}
\subsection{\Circus\ Process}
\begin{code}
retr_sch_ProcDecl :: ProcDecl -> [ZPara]
retr_sch_ProcDecl (CProcess _ p)
  = retr_sch_ProcessDef p
retr_sch_ProcDecl (CParamProcess _ _ p)
  = retr_sch_ProcessDef p
retr_sch_ProcDecl (CGenProcess _ _ p)
  = retr_sch_ProcessDef p
\end{code}
\subsection{\Circus\ Process}
\begin{code}
retr_sch_ProcessDef :: ProcessDef -> [ZPara]
retr_sch_ProcessDef (ProcDefSpot _ p)
  = retr_sch_ProcessDef p
retr_sch_ProcessDef (ProcDefIndex _ p)
  = retr_sch_ProcessDef p
retr_sch_ProcessDef (ProcDef cp)
  = (retr_sch_CProc cp)
\end{code}
\subsection{\Circus\ Process}
\begin{code}
retr_sch_CProc :: CProc -> [ZPara]
retr_sch_CProc (CRepSeqProc _ cp)
  = (retr_sch_CProc cp)
retr_sch_CProc (CRepExtChProc _ cp)
  = (retr_sch_CProc cp)
retr_sch_CProc (CRepIntChProc _ cp)
  = (retr_sch_CProc cp)
retr_sch_CProc (CRepParalProc _ _ cp)
  = (retr_sch_CProc cp)
retr_sch_CProc (CRepInterlProc _ cp)
  = (retr_sch_CProc cp)
retr_sch_CProc (CHide cp _)
  = (retr_sch_CProc cp)
retr_sch_CProc (CExtChoice cp cp2)
  = (retr_sch_CProc cp)++(retr_sch_CProc cp2)
retr_sch_CProc (CIntChoice cp cp2)
  = (retr_sch_CProc cp)++(retr_sch_CProc cp2)
retr_sch_CProc (CParParal _CSExp cp cp2)
  = (retr_sch_CProc cp)++(retr_sch_CProc cp2)
retr_sch_CProc (CInterleave cp cp2)
  = (retr_sch_CProc cp)++(retr_sch_CProc cp2)
retr_sch_CProc (CSeq cp cp2)
  = (retr_sch_CProc cp)++(retr_sch_CProc cp2)
retr_sch_CProc (ProcMain e pl ca)
  = (concat $ map retr_sch_PPar pl)++(retr_sch_ZPara e)
retr_sch_CProc (ProcStalessMain pl _CAction)
  = (concat $ map retr_sch_PPar pl)
retr_sch_CProc x = []
\end{code}
\subsection{Process paragraphs}
\begin{code}
retr_sch_PPar :: PPar -> [ZPara]
retr_sch_PPar (ProcZPara e)
  = (retr_sch_ZPara e)
retr_sch_PPar x = []
\end{code}


\section{Replace schema names to its definitions}

\subsection{Z Schemas}
\begin{code}
get_schema_def :: ZSName -> [ZPara] -> ZSExpr
get_schema_def n [] = error "schema was not found (generated by get_schema_def) empty"
get_schema_def n [(ZSchemaDef sn sex)]
  | n == sn = sex
  | otherwise = error "schema was not found (generated by get_schema_def) single1"
get_schema_def n [_] = error "schema was not found (generated by get_schema_def) single2"
get_schema_def n ((ZSchemaDef sn sex):xs)
  | n == sn = sex
  | otherwise = get_schema_def n xs

repl_sch_ZSExpr :: [ZPara] -> ZSExpr -> ZSExpr
repl_sch_ZSExpr schls (ZSchema _zgfs)
  = (ZSchema _zgfs)
repl_sch_ZSExpr schls (ZSRef sn _ _)
  = get_schema_def sn schls
repl_sch_ZSExpr schls (ZSRefP sn _ _ _)
  = get_schema_def sn schls
repl_sch_ZSExpr schls (ZS1 _ZS1 _ZSExpr)
  = (ZS1 _ZS1 (repl_sch_ZSExpr schls _ZSExpr))
repl_sch_ZSExpr schls (ZS2 _ZS2 _ZSExpr _ZSExpr2)
  = (ZS2 _ZS2 (repl_sch_ZSExpr schls _ZSExpr) (repl_sch_ZSExpr schls _ZSExpr2))
repl_sch_ZSExpr schls (ZSHide _ZSExpr _ZVar_lst)
  = (ZSHide (repl_sch_ZSExpr schls _ZSExpr) _ZVar_lst)
repl_sch_ZSExpr schls (ZSExists _zgfs _ZSExpr)
  = (ZSExists _zgfs (repl_sch_ZSExpr schls _ZSExpr))
repl_sch_ZSExpr schls (ZSExists_1 _zgfs _ZSExpr)
  = (ZSExists_1 _zgfs (repl_sch_ZSExpr schls _ZSExpr))
repl_sch_ZSExpr schls (ZSForall _zgfs _ZSExpr)
  = (ZSForall _zgfs (repl_sch_ZSExpr schls _ZSExpr))
\end{code}
\section{Z Paragraphs}
\begin{code}
repl_sch_ZPara :: [ZPara] -> ZPara -> ZPara
repl_sch_ZPara schls (ZSchemaDef _ZSName _ZSExpr)
  = (ZSchemaDef _ZSName (repl_sch_ZSExpr schls _ZSExpr))
repl_sch_ZPara schls (Process p)
  = (Process (repl_sch_ProcDecl schls p))
repl_sch_ZPara schls x = x
\end{code}
\subsection{\Circus\ Process}
\begin{code}
repl_sch_ProcDecl :: [ZPara] -> ProcDecl -> ProcDecl
repl_sch_ProcDecl schls (CProcess _zn p)
  = (CProcess _zn (repl_sch_ProcessDef schls p))
repl_sch_ProcDecl schls (CParamProcess _zn _zn2_lst p)
  = (CParamProcess _zn _zn2_lst (repl_sch_ProcessDef schls p))
repl_sch_ProcDecl schls (CGenProcess _zn _zn2_lst p)
  = (CGenProcess _zn _zn2_lst (repl_sch_ProcessDef schls p))
\end{code}
\subsection{\Circus\ Process}
\begin{code}
repl_sch_ProcessDef :: [ZPara] -> ProcessDef -> ProcessDef
repl_sch_ProcessDef schls (ProcDefSpot _zgfs p)
  = (ProcDefSpot _zgfs (repl_sch_ProcessDef schls p))
repl_sch_ProcessDef schls (ProcDefIndex _zgfs p)
  = (ProcDefIndex _zgfs (repl_sch_ProcessDef schls p))
repl_sch_ProcessDef schls (ProcDef _cp)
  = (ProcDef (repl_sch_CProc schls _cp))
\end{code}
\subsection{\Circus\ Process}
\begin{code}
repl_sch_CProc :: [ZPara] -> CProc -> CProc
repl_sch_CProc schls (CRepSeqProc _zgfs _cp)
  = (CRepSeqProc _zgfs (repl_sch_CProc schls _cp))
repl_sch_CProc schls (CRepExtChProc _zgfs _cp)
  = (CRepExtChProc _zgfs (repl_sch_CProc schls _cp))
repl_sch_CProc schls (CRepIntChProc _zgfs _cp)
  = (CRepIntChProc _zgfs (repl_sch_CProc schls _cp))
repl_sch_CProc schls (CRepParalProc _csx _zgfs _cp)
  = (CRepParalProc _csx _zgfs (repl_sch_CProc schls _cp))
repl_sch_CProc schls (CRepInterlProc _zgfs _cp)
  = (CRepInterlProc _zgfs (repl_sch_CProc schls _cp))
repl_sch_CProc schls (CHide _cp _csx)
  = (CHide (repl_sch_CProc schls _cp) _csx)
repl_sch_CProc schls (CExtChoice _cp _cp2)
  = (CExtChoice (repl_sch_CProc schls _cp) (repl_sch_CProc schls _cp2))
repl_sch_CProc schls (CIntChoice _cp _cp2)
  = (CIntChoice (repl_sch_CProc schls _cp) (repl_sch_CProc schls _cp2))
repl_sch_CProc schls (CParParal _csx _cp _cp2)
  = (CParParal _csx (repl_sch_CProc schls _cp) (repl_sch_CProc schls _cp2))
repl_sch_CProc schls (CInterleave _cp _cp2)
  = (CInterleave (repl_sch_CProc schls _cp) (repl_sch_CProc schls _cp2))
repl_sch_CProc schls (CGenProc _zn _zexls)
  = (CGenProc _zn _zexls)
repl_sch_CProc schls (CParamProc _zn _zexls)
  = (CParamProc _zn _zexls)
repl_sch_CProc schls (CProcRename _cp _Comm_lst _Comm_lst1)
  = (CProcRename (repl_sch_CProc schls _cp) _Comm_lst _Comm_lst1)
repl_sch_CProc schls (CSeq _cp _cp2)
  = (CSeq (repl_sch_CProc schls _cp) (repl_sch_CProc schls _cp2))
repl_sch_CProc schls (CSimpIndexProc _zn _zexls)
  = (CSimpIndexProc _zn _zexls)
repl_sch_CProc schls (CircusProc _zn)
  = (CircusProc _zn)
repl_sch_CProc schls (ProcMain _ZPara _PPar_lst _cact)
  = (ProcMain (repl_sch_ZPara schls _ZPara) (map (repl_sch_PPar schls) _PPar_lst) (repl_sch_CAction schls _cact))
repl_sch_CProc schls (ProcStalessMain _PPar_lst _cact)
  = (ProcStalessMain (map (repl_sch_PPar schls) _PPar_lst) (repl_sch_CAction schls _cact))
\end{code}
\subsection{Process paragraphs}
\begin{code}
repl_sch_PPar :: [ZPara] -> PPar -> PPar
repl_sch_PPar schls (ProcZPara _ZPara)
  = (ProcZPara (repl_sch_ZPara schls _ZPara))
repl_sch_PPar schls (CParAction _zn _ParAction)
  = (CParAction _zn (repl_sch_ParAction schls _ParAction))
repl_sch_PPar schls x = x
\end{code}
\subsection{Parametrised Actions}
\begin{code}
repl_sch_ParAction schls (CircusAction _cact) = (CircusAction (repl_sch_CAction schls _cact))
repl_sch_ParAction schls (ParamActionDecl _zgfs _ParAction) = (ParamActionDecl _zgfs (repl_sch_ParAction schls _ParAction))
\end{code}
\subsection{\Circus\ Actions}
\begin{code}
repl_sch_CAction schls (CActionSchemaExpr _ZSExpr)
  = (CActionSchemaExpr (repl_sch_ZSExpr schls _ZSExpr))
repl_sch_CAction schls (CActionCommand _CCommand)
  = (CActionCommand _CCommand)
repl_sch_CAction schls (CActionName _zn)
  = (CActionName _zn)
repl_sch_CAction schls (CSPSkip ) = (CSPSkip )
repl_sch_CAction schls (CSPStop ) = (CSPStop )
repl_sch_CAction schls (CSPChaos) = (CSPChaos)
repl_sch_CAction schls (CSPCommAction _Comm _cact)
  = (CSPCommAction _Comm (repl_sch_CAction schls _cact))
repl_sch_CAction schls (CSPGuard _zpr _cact)
  = (CSPGuard _zpr (repl_sch_CAction schls _cact))
repl_sch_CAction schls (CSPSeq _cact1 _cact2)
  = (CSPSeq (repl_sch_CAction schls _cact1) (repl_sch_CAction schls _cact2))
repl_sch_CAction schls (CSPExtChoice _cact1 _cact2)
  = (CSPExtChoice (repl_sch_CAction schls _cact1) (repl_sch_CAction schls _cact2))
repl_sch_CAction schls (CSPIntChoice _cact1 _cact2)
  = (CSPIntChoice (repl_sch_CAction schls _cact1) (repl_sch_CAction schls _cact2))
repl_sch_CAction schls (CSPNSParal _zexls _csx _zexls1 _cact1 _cact2)
  = (CSPNSParal _zexls _csx _zexls1 (repl_sch_CAction schls _cact1) (repl_sch_CAction schls _cact2))
repl_sch_CAction schls (CSPParal _csx _cact1 _cact2)
  = (CSPParal _csx (repl_sch_CAction schls _cact1) (repl_sch_CAction schls _cact2))
repl_sch_CAction schls (CSPNSInter _zexls _zexls1 _cact1 _cact2)
  = (CSPNSInter _zexls _zexls1 (repl_sch_CAction schls _cact1) (repl_sch_CAction schls _cact2))
repl_sch_CAction schls (CSPInterleave _cact1 _cact2)
  = (CSPInterleave (repl_sch_CAction schls _cact1) (repl_sch_CAction schls _cact2))
repl_sch_CAction schls (CSPHide _cact _csx)
  = (CSPHide (repl_sch_CAction schls _cact) _csx)
repl_sch_CAction schls (CSPParAction _zn _zexls)
  = (CSPParAction _zn _zexls)
repl_sch_CAction schls (CSPRenAction _zn _CReplace)
  = (CSPRenAction _zn _CReplace)
repl_sch_CAction schls (CSPRecursion _zn _cact)
  = (CSPRecursion _zn (repl_sch_CAction schls _cact))
repl_sch_CAction schls (CSPUnfAction _zn _cact)
  = (CSPUnfAction _zn (repl_sch_CAction schls _cact))
repl_sch_CAction schls (CSPUnParAction _zgfs _cact _zn)
  = (CSPUnParAction _zgfs (repl_sch_CAction schls _cact) _zn)
repl_sch_CAction schls (CSPRepSeq _zgfs _cact)
  = (CSPRepSeq _zgfs (repl_sch_CAction schls _cact))
repl_sch_CAction schls (CSPRepExtChoice _zgfs _cact)
  = (CSPRepExtChoice _zgfs (repl_sch_CAction schls _cact))
repl_sch_CAction schls (CSPRepIntChoice _zgfs _cact)
  = (CSPRepIntChoice _zgfs (repl_sch_CAction schls _cact))
repl_sch_CAction schls (CSPRepParalNS _csx _zgfs _zexls _cact)
  = (CSPRepParalNS _csx _zgfs _zexls (repl_sch_CAction schls _cact))
repl_sch_CAction schls (CSPRepParal _csx _zgfs _cact)
  = (CSPRepParal _csx _zgfs (repl_sch_CAction schls _cact))
repl_sch_CAction schls (CSPRepInterlNS _zgfs _zexls _cact)
  = (CSPRepInterlNS _zgfs _zexls (repl_sch_CAction schls _cact))
repl_sch_CAction schls (CSPRepInterl _zgfs _cact)
  = (CSPRepInterl _zgfs (repl_sch_CAction schls _cact))
\end{code}
\subsection{\Circus\ Commands}
\begin{code}
repl_sch_CCommand schls (CIf _CGActions) = (CIf _CGActions)
repl_sch_CCommand schls (CVarDecl _zgfs _cact) = (CVarDecl _zgfs (repl_sch_CAction schls _cact))
repl_sch_CCommand schls (CValDecl _zgfs _cact) = (CValDecl _zgfs (repl_sch_CAction schls _cact))
repl_sch_CCommand schls (CResDecl _zgfs _cact) = (CResDecl _zgfs (repl_sch_CAction schls _cact))
repl_sch_CCommand schls (CVResDecl _zgfs _cact) = (CVResDecl _zgfs (repl_sch_CAction schls _cact))
repl_sch_CCommand schls x = x
\end{code}
\subsection{\Circus\ Guards}
\begin{code}
repl_sch_CGActions schls (CircGAction _zpr _cact)
  = (CircGAction _zpr (repl_sch_CAction schls _cact))
repl_sch_CGActions schls (CircThenElse _CGActions _CGActions1)
  = (CircThenElse _CGActions _CGActions1)
\end{code}


\section{Making mgets and msets to variables}

\begin{code}

mk_mget_mset_vars [] = []
mk_mget_mset_vars [Choose (x,_,_) t]
  = [CircChannel [CChanDecl ("mget_"++x) t, CChanDecl ("mset_"++x) t]]
mk_mget_mset_vars ((Choose (x,_,_) t):xs)
  = [CircChannel [CChanDecl ("mget_"++x) t, CChanDecl ("mset_"++x) t]]++(mk_mget_mset_vars xs)
mk_mget_mset_vars (_:xs) = (mk_mget_mset_vars xs)

mk_mget_mset_chanset :: [ZGenFilt] -> [ZName]
mk_mget_mset_chanset [] = []
mk_mget_mset_chanset [Choose (x,_,y) t] = ["mget_"++x,"mset_"++x]
mk_mget_mset_chanset ((Choose (x,_,y) t):xs) = ["mget_"++x,"mset_"++x]++(mk_mget_mset_chanset xs)
mk_mget_mset_chanset (_:xs) = (mk_mget_mset_chanset xs)
\end{code}

\begin{code}
mk_lget_lset_vars :: [ZGenFilt] -> [ZPara]
mk_lget_lset_vars [] = []
mk_lget_lset_vars [Choose (x,_,y) t]
  = [CircChannel [CChanDecl ("lget_"++x) t, CChanDecl ("lset_"++x) t]]
mk_lget_lset_vars ((Choose (x,_,y) t):xs)
  = [CircChannel [CChanDecl ("lget_"++x) t, CChanDecl ("lset_"++x) t]]++(mk_lget_lset_vars xs)
mk_lget_lset_vars (_:xs) = (mk_lget_lset_vars xs)

mk_lget_lset_chanset :: [ZGenFilt] -> [ZName]

mk_lget_lset_chanset [] = []
mk_lget_lset_chanset [Choose (x,_,y) t]
  = ["lget_"++x,"lset_"++x]
mk_lget_lset_chanset ((Choose (x,_,y) t):xs)
  = ["lget_"++x,"lset_"++x]++(mk_lget_lset_chanset xs)
mk_lget_lset_chanset (_:xs) = (mk_lget_lset_chanset xs)

mk_st_zvar :: [ZGenFilt] -> [ZVar]
mk_st_zvar [Choose x y] = [x]
mk_st_zvar ((Choose x y):xs) = [x]++(mk_st_zvar xs)
mk_st_zvar (_:xs) = (mk_st_zvar xs)
\end{code}


\subsection{Making bindings for the spec}
\begin{code}
get_type_universe
  :: String -> ZPara -> [ZVar]
get_type_universe n (ZAbbreviation (de,[],"") (ZSetDisplay [ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar a, ZVar b])]))
  | ((lastN 3 de) == n) = [b]
  | otherwise = []
get_type_universe n _
  = []

getZBranch (ZBranch0 x) = ZVar x
getZBranch (ZBranch1 x (ZCall tts (ZTuple xls))) = ZTuple [ZCall (ZVar x) (Data.List.head xls)]

get_min_val :: ZVar -> ZPara -> [ZExpr]

get_min_val n (ZAbbreviation y (ZCall (ZVar ("\\upto",[],"")) (ZTuple xs)))
  | (nfst n) == (nfst y) = [Data.List.head xs]
  | otherwise = []
get_min_val n (ZAbbreviation y (ZCall (ZVar ("\\seq",[],"")) v))
  | (nfst n) == (nfst y) = [ZSeqDisplay []]
  | otherwise = []
get_min_val n (ZFreeTypeDef y xs)
  | (nfst n) == (nfst y) = [Data.List.head (map getZBranch xs)]
  | otherwise = []
get_min_val n _ = []

make_binding_pair :: ZExpr -> (ZVar,ZVar)
make_binding_pair (ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar v,ZVar t]))
  = (v,t)


make_binding :: [ZPara] -> (ZVar,ZVar) -> String
make_binding spec ((a,b,c),t)
  | Subs.isPrefixOf "_" c
      = "("++a++", {"++(if (Data.List.null getMinVal) then "DO_IT_MANUALLY"
                            else (mapping_ZExpr (get_delta_names1 spec) (Data.List.head $ getMinVal)))++"})"
  | "NAT" == c
      = "("++a++", 0)"
  | otherwise = "("++a++", "++(if (Data.List.null getMinVal) then "DO_IT_MANUALLY"
                            else (mapping_ZExpr (get_delta_names1 spec) (Data.List.head $ getMinVal)))++")"
  where
    getMinVal = (concat $ map (get_min_val t) spec)
\end{code}

\begin{code}
mapping_ZTuple [ZVar ("\\nat",_,[])] = "NatValue"
mapping_ZTuple [ZCall (ZVar (a,[],"")) c] = a++"."++(mapping_ZExpr [] c)
mapping_ZTuple [ZVar ("\\nat_1",_,[])] = "NatValue"
-- mapping_ZTuple [ZVar (v,_)] = "value("++v++")"
mapping_ZTuple [ZVar (v,_,t)]
  | (is_ZVar_v_st v) = v
  -- | (is_ZVar_v_st v) = "value"++(def_U_prefix t)++"("++v++")"
  | otherwise = v
mapping_ZTuple [ZInt x] = show (fromIntegral x)
mapping_ZTuple ((ZVar (v,_,t)):xs)
  | (is_ZVar_v_st v) = v++ "," ++ (mapping_ZTuple xs)
  -- | (is_ZVar_v_st v) = "value"++(def_U_prefix t)++"("++v++")"++ "," ++ (mapping_ZTuple xs)
  | otherwise = v ++ "," ++ (mapping_ZTuple xs)
mapping_ZTuple ((ZInt x):xs) = (show (fromIntegral x)) ++ "," ++ (mapping_ZTuple xs)
mapping_ZTuple ((ZCall (ZVar (a,[],"")) c):xs) = a++"."++(mapping_ZExpr [] c) ++ "," ++ (mapping_ZTuple xs)
mapping_ZTuple _ = ""
\end{code}

\begin{code}
mapping_ZCross [ZVar ("\\int",_,[])] = "Int"
mapping_ZCross [ZVar ("\\nat",_,[])] = "NatValue"
mapping_ZCross [ZVar (v,_,_)] = v
mapping_ZCross ((ZVar x):xs) = (mapping_ZCross [ZVar x]) ++ "." ++ (mapping_ZCross xs)
mapping_ZCross _ = ""
\end{code}

\begin{code}
-- aux functions
mapping_ZExpr_def :: [ZName] -> String
mapping_ZExpr_def [x] = x
mapping_ZExpr_def (x:xs) = x++","++(mapping_ZExpr_def xs)

mapping_ZExpr_set [] = ""
mapping_ZExpr_set [ZVar (a,b,x)] = a
mapping_ZExpr_set ((ZVar (a,b,x)):xs) = a++","++(mapping_ZExpr_set xs)
mapping_ZExpr_set (_:xs) = (mapping_ZExpr_set xs)
\end{code}
\begin{code}
mapping_ZExpr_def_f f [] = ""
mapping_ZExpr_def_f f [x] = (f x)
mapping_ZExpr_def_f f (x:xs) = (f x)++","++(mapping_ZExpr_def_f f xs)

mapping_ZExpr1 (ZInt m) = show(fromIntegral m)
mapping_ZExpr1 (ZVar (a,_,t)) = a
mapping_ZExpr1 (ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [a,b])) = "("++(mapping_ZExpr1  a)++","++(mapping_ZExpr1  b)++")"
mapping_ZExpr1 (ZCall (ZVar (x,_,_)) b) = "("++x++"."++(mapping_ZExpr1 b)++")"
mapping_ZExpr1 x = mapping_ZExpr [] x
\end{code}

\subsection{Mapping Function for Expressions}
\begin{code}
mapping_ZExpr :: [ZName] ->  ZExpr -> String

mapping_ZExpr lst (ZVar ("\\emptyset",[],[])) = "{}"
mapping_ZExpr lst (ZVar ("\\int",[],[])) = "Int"
mapping_ZExpr lst (ZVar ("\\nat",_,_)) = "NatValue"
-- mapping_ZExpr lst (ZVar (a,_)) = a
mapping_ZExpr lst (ZInt m) = show(fromIntegral m)
mapping_ZExpr lst (ZVar (a,_,t))
  -- | (inListVar a lst) = "value"++(def_U_prefix t)++"(v_"++a++")"
  -- | (inListVar a lst) = "v_"++a
  -- | (is_ZVar_v_st a) = a
  -- | (is_ZVar_v_st a) = "value"++(def_U_prefix t)++"("++a++")"
  -- | otherwise = a
  = a
mapping_ZExpr lst (ZBinding _) = ""
mapping_ZExpr lst (ZCall (ZVar ("*",[],[])) (ZTuple [n,m])) = "("++mapping_ZExpr lst (n) ++ " * " ++ mapping_ZExpr lst (m)++")"
mapping_ZExpr lst (ZCall (ZVar ("+",[],[])) (ZTuple [n,m])) = "("++mapping_ZExpr lst (n) ++ " + " ++ mapping_ZExpr lst (m)++")"
mapping_ZExpr lst (ZCall (ZVar ("-",[],[])) (ZTuple [n,m])) = "("++mapping_ZExpr lst (n) ++ " - " ++ mapping_ZExpr lst (m)++")"
mapping_ZExpr lst (ZCall (ZVar ("\\035",[],[])) a) = "\035(" ++ mapping_ZExpr lst (a)++")"
mapping_ZExpr lst (ZCall (ZVar ("\\\035",[],[])) a) = "card("++(mapping_ZExpr lst a)++")"
mapping_ZExpr lst (ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [a,b])) = "("++(mapping_ZExpr lst a)++","++(mapping_ZExpr lst b)++")"
mapping_ZExpr lst (ZCall (ZVar ("\\bigcap",[],[])) (ZTuple [a,b])) = "Inter("++(mapping_ZExpr lst a)++","++(mapping_ZExpr lst b)++")"
mapping_ZExpr lst (ZCall (ZVar ("\\bigcup",[],[])) (ZTuple [a,b])) = "Union("++(mapping_ZExpr lst a)++","++(mapping_ZExpr lst b)++")"
mapping_ZExpr lst (ZCall (ZVar ("\\cap",[],[])) (ZTuple [a,b])) = "inter("++(mapping_ZExpr lst a)++","++(mapping_ZExpr lst b)++")"
mapping_ZExpr lst (ZCall (ZVar ("\\cat",[],[])) (ZTuple [a,b])) = mapping_ZExpr lst (a)++"^"++mapping_ZExpr lst (b)
mapping_ZExpr lst (ZCall (ZVar ("\\cup",[],[])) (ZTuple [a,b]))
  = "union("++(mapping_ZExpr lst a)++","++(mapping_ZExpr lst b)++")"
mapping_ZExpr lst (ZCall (ZVar ("\\dcat",[],[])) s)
  = "concat("++mapping_ZExpr lst (s)++")"
mapping_ZExpr lst (ZCall (ZVar ("\\div",[],[])) (ZTuple [n,m])) = "("++mapping_ZExpr lst (n) ++ " / " ++ mapping_ZExpr lst (m)++")"
mapping_ZExpr lst (ZCall (ZVar ("\\dom",[],[])) a)
  = "dom("++(mapping_ZExpr lst a)++")"
mapping_ZExpr lst (ZCall (ZVar ("\\mod",[],[])) (ZTuple [n,m])) = mapping_ZExpr lst (n) ++ " % " ++ mapping_ZExpr lst (m)
mapping_ZExpr lst (ZCall (ZVar ("\\dres",[],[])) (ZTuple [n,m])) = "dres("++mapping_ZExpr lst (n) ++ ", " ++ mapping_ZExpr lst (m)++")"
mapping_ZExpr lst (ZCall (ZVar ("\\comp",[],[])) (ZTuple [n,m])) = "comp("++mapping_ZExpr lst (n) ++ ", " ++ mapping_ZExpr lst (m)++")"
mapping_ZExpr lst (ZCall (ZVar ("\\rres",[],[])) (ZTuple [n,m])) = "rres("++mapping_ZExpr lst (n) ++ ", " ++ mapping_ZExpr lst (m)++")"
mapping_ZExpr lst (ZCall (ZVar ("\\pfun",[],[])) (ZTuple [n,m])) = "pfun("++mapping_ZExpr lst (n) ++ ", " ++ mapping_ZExpr lst (m)++")"
mapping_ZExpr lst (ZCall (ZVar ("\\negate",[],[])) n) = " -" ++ (mapping_ZExpr lst (n))
mapping_ZExpr lst (ZCall (ZVar ("\\oplus",[],[])) (ZTuple [ZVar a,ZSetDisplay [ZCall (ZVar ("\\mapsto",[],[])) (ZTuple [ZVar b,c])]]))
  = "over("++(mapping_ZExpr lst (ZVar a))++","++(mapping_ZExpr lst (ZVar b))++","++(mapping_ZExpr lst c)++")"
mapping_ZExpr lst (ZCall (ZVar ("\\sym",_,_)) (ZTuple [ZVar a,ZVar b])) = "("++(mapping_ZExpr lst (ZVar a))++"."++(mapping_ZExpr lst (ZVar b))++")"
mapping_ZExpr lst (ZCall (ZVar ("\\oplus",_,_)) (ZTuple [ZVar a,ZVar b])) = "oplus("++(mapping_ZExpr lst (ZVar a))++","++(mapping_ZExpr lst (ZVar b))++")"
mapping_ZExpr lst (ZCall (ZVar ("\\power",[],[])) a) ="Set("++(mapping_ZExpr lst a)++")"
mapping_ZExpr lst (ZCall (ZVar ("\\ran",[],[])) a) = "ran("++(mapping_ZExpr lst a)++")"
mapping_ZExpr lst (ZCall (ZVar ("\\seq",[],[])) a) = "Seq("++(mapping_ZExpr lst a)++")"
mapping_ZExpr lst (ZCall (ZVar ("\\setminus",[],[])) (ZTuple [a,b])) = "diff("++(mapping_ZExpr lst a)++","++(mapping_ZExpr lst b)++")"
mapping_ZExpr lst (ZCall (ZVar ("head",[],[])) s) = "head("++mapping_ZExpr lst (s)++")"
mapping_ZExpr lst (ZCall (ZVar ("tail",[],[])) s) = "tail("++mapping_ZExpr lst (s)++")"
-- mapping_ZExpr lst (ZCall (ZVar a) (ZVar b)) = "apply("++(mapping_ZExpr lst (ZVar a))++","++(mapping_ZExpr lst (ZVar b))++")"
mapping_ZExpr lst (ZCall (ZVar ("\\upto",[],[])) (ZTuple [a,b]))
  = "{"++(mapping_ZExpr lst a)++".."++(mapping_ZExpr lst b)++"}"
mapping_ZExpr lst (ZSetDisplay [ZCall (ZVar ("\\upto",[],[])) (ZTuple [a,b])]) = "{"++(mapping_ZExpr1 a)++".."++(mapping_ZExpr1 b)++"}"
mapping_ZExpr lst (ZSetDisplay []) = ""
mapping_ZExpr lst (ZSetDisplay x) = "{"++(mapping_ZExpr_def_f mapping_ZExpr1 x)++"}"
mapping_ZExpr lst (ZTuple ls) = "("++mapping_ZTuple ls ++ ")"
mapping_ZExpr lst (ZSeqDisplay []) = "<>"
mapping_ZExpr lst (ZSeqDisplay [ZVar (a,b,c)])
  | Subs.isPrefixOf "b_" a ="<"++a++">"
  | Subs.isPrefixOf "sv_" a ="<"++a++">"
  | "ns" == a ="<y | y <- ns,member(y,dom(bd))>"
  | otherwise = "<y | y <- "++a++">"
mapping_ZExpr lst (ZSeqDisplay [(ZCall (ZVar ("\\cup",[],[])) (ZTuple xs)) ]) = joinBy "^" $ map (\x -> "< "++(mapping_ZExpr lst x)++">") xs
mapping_ZExpr lst (ZSeqDisplay x) = "<"++(mapping_ZExpr_def_f mapping_ZExpr1 x)++">"
-- mapping_ZExpr lst (ZSeqDisplay x) = "<y | y <- "++(concat $map (mapping_ZExpr lst) x)++">"
mapping_ZExpr lst (ZCross ls) = mapping_ZCross ls
mapping_ZExpr lst (ZSetComp a (Just (ZTuple ls))) = "("++(joinBy "," $ map (mapping_ZExpr lst) $ map (\(Choose v t) -> t) $ filter_ZGenFilt_Choose a)++")"
-- mapping_ZExpr lst (ZCall c d) = "apply("++(mapping_ZExpr lst c)++","++(mapping_ZExpr lst d)++")"
mapping_ZExpr lst (ZCall (ZVar (a,[],x)) b)
  | isPrefixOf "b_" a = "apply("++a++","++(mapping_ZExpr lst b)++")"
  | otherwise = (mapping_ZExpr lst (ZVar (a,[],x)))++"("++(mapping_ZExpr lst b)++")"
mapping_ZExpr lst (ZCall a b) = (mapping_ZExpr lst a)++"("++(mapping_ZExpr lst b)++")"
mapping_ZExpr lst x = ""
-- mapping_ZExpr lst x = fail ("not implemented by mapping_ZExpr: " ++ show x)

\end{code}
\begin{code}
-- removing recursion from Memory processes
rem_recursion m (CSPExtChoice a b) = (CSPExtChoice (rem_recursion m a) (rem_recursion m b))
rem_recursion m (CSPCommAction b a) = (CSPCommAction b (rem_recursion m a))
rem_recursion m (CSPParAction "M" xs) = (CSPParAction m xs)
rem_recursion m x = x
\end{code}
\begin{code}
-- find types for deltas
find_type n (ZFreeTypeDef (v,_,_) xs)
  | n == v = xs
  | otherwise = []
find_type n _ = []
\end{code}
