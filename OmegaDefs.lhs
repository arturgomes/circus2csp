\chapter{Misc functions -- File: OmegaDefs.lhs}
Functions used for manipulating lists (Z Sets and sequences, as well as calculating the provisos from the Circus Refinement laws)

\ignore{
\begin{code}
module OmegaDefs where
-- import Data.Text hiding (map,concat,all,take)
import Subs
import AST
import Errors

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
make_get_com [(x,y,z)] c
  = (CSPCommAction (ChanComm "mget"
    [ChanDotExp (ZVar (x,[],z)),ChanInp ("v_"++x)]) c)
make_get_com ((x,y,z):xs) c
  = (CSPCommAction (ChanComm "mget"
    [ChanDotExp (ZVar (x,[],z)),ChanInp ("v_"++x)]) (make_get_com xs c))
make_get_com x c = c
\end{code}
\subsection{$make\_set\_com$}
This function updates the values of the $Memory$ process by generating a sequence of $mset$ communications and then it behaves like $f~c$, where $f$ may be the $omega\_CAction$ or $omega\_prime\_CAction$.
\begin{code}
make_set_com :: (CAction -> CAction) -> [ZVar] -> [ZExpr] -> CAction -> CAction
make_set_com f [(x,_,t)] [y] c
  = (CSPCommAction (ChanComm "mset"
    [ChanDotExp (ZVar (x,[],t)),ChanDotExp y]) (f c))
make_set_com f ((x,_,t):xs) (y:ys) c
  = (CSPCommAction (ChanComm "mset"
     [ChanDotExp (ZVar (x,[],t)),ChanDotExp y]) (make_set_com f xs ys c))
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
  = (CSPCommAction (ChanComm "lget"
    [ChanDotExp (ZVar (x,[],z)),ChanInp ("v_"++x)]) c)
make_lget_com ((x,y,z):xs) c
  = (CSPCommAction (ChanComm "lget"
    [ChanDotExp (ZVar (x,[],z)),ChanInp ("v_"++x)]) (make_lget_com xs c))
make_lget_com x c = c
\end{code}
\subsection{$make\_lset\_com$}
This function updates the values of the $Memory$ process by generating a sequence of $lset$ communications and then it behaves like $f~c$, where $f$ may be the $omega\_CAction$ or $omega\_prime\_CAction$.
\begin{code}
make_lset_com :: (CAction -> CAction) -> [ZVar] -> [ZExpr] -> CAction -> CAction
make_lset_com f [(x,_,t)] [y] c
  = (CSPCommAction (ChanComm "lset"
    [ChanDotExp (ZVar (x,[],t)),ChanDotExp y]) (f c))
make_lset_com f ((x,_,t):xs) (y:ys) c
  = (CSPCommAction (ChanComm "lset"
     [ChanDotExp (ZVar (x,[],t)),ChanDotExp y]) (make_lset_com f xs ys c))
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
getWrtV xs = []
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
is_ZVar_st a = isPrefixOf "sv" a
is_ZVar_st a = isPrefixOf "lv" a
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
 = False
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
  | (take 2 nm) == "mu" = (CActionName nm)
  | otherwise = get_action nm lst lst
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
expand_action_names_CAction lst x = x
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
get_action _ lst [] = error "Action list is empty"
get_action name lst [(CParAction n (CircusAction a))]
  | name == n = expand_action_names_CAction lst a
  | otherwise = error ("Action "++(name)++" not found")
get_action name lst ((CParAction n (CircusAction a)):xs)
  | (name == n) = expand_action_names_CAction lst a
  | otherwise = get_action name lst xs
get_action name lst (_:xs)
  = get_action name lst xs
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
 = (CSPUnParAction zgf (rename_vars_CAction1 pn lst a) zn)
rename_vars_CAction1 pn lst (CSPRepSeq zgf a)
 = (CSPRepSeq zgf (rename_vars_CAction1 pn lst a))
rename_vars_CAction1 pn lst (CSPRepExtChoice zgf a)
 = (CSPRepExtChoice zgf (rename_vars_CAction1 pn lst a))
rename_vars_CAction1 pn lst (CSPRepIntChoice zgf a)
 = (CSPRepIntChoice zgf (rename_vars_CAction1 pn lst a))
rename_vars_CAction1 pn lst (CSPRepParalNS cs zgf ns a)
 = (CSPRepParalNS cs zgf ns (rename_vars_CAction1 pn lst a))
rename_vars_CAction1 pn lst (CSPRepParal cs zgf a)
 = (CSPRepParal cs zgf (rename_vars_CAction1 pn lst a))
rename_vars_CAction1 pn lst (CSPRepInterlNS zgf ns a)
 = (CSPRepInterlNS zgf ns (rename_vars_CAction1 pn lst a))
rename_vars_CAction1 pn lst (CSPRepInterl zgf a)
 = (CSPRepInterl zgf (rename_vars_CAction1 pn lst a))
rename_vars_CAction1 pn lst x = x

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
  True -> (ChanInp (join_name (get_proc_name zn lst) zn))
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
get_u_tag_ZBranch ((ZBranch1 (tag,_,_) (ZVar (typ,_,_))):xs)
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
  = [(b,(def_U_NAME ("P"++c)), (def_U_prefix ("P"++c)), ("Set("++c++")"))]
def_universe_aux ((ZCall (ZVar ("\\mapsto",[],_)) (ZTuple [ZVar (b,[],_), ZCall (ZVar ("\\power",[],_)) (ZVar (c,[],_))])):xs)
  = ((b,(def_U_NAME ("P"++c)), (def_U_prefix ("P"++c)), ("Set("++c++")")):(def_universe_aux xs))
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
        tlist = map (\(Choose v t) -> (ntrd v)) xs
        subname xs tl =
          (ZAbbreviation
                (join_name "\\delta" tl,[],"")
                (ZSetDisplay (sub_name xs tl)))
          -- (ZFreeTypeDef (join_name "NAME" tl,[],[]) (sub_name xs tl))
        sub_name [] _= []
        sub_name ((Choose v t):xs) t1
          | t1 == (ntrd v) =
              [ZCall (ZVar ("\\mapsto",[],[])) (ZTuple [ZVar v,t])]
                ++ (sub_name xs t1)
          | otherwise = (sub_name xs t1)
        sub_name (_:xs) t1 = (sub_name xs t1)

\end{code}

\begin{code}
def_delta_name :: [ZGenFilt] -> [ZBranch]
def_delta_name [] = []
def_delta_name ((Choose v t):xs) = [ZBranch0 v] ++ (def_delta_name xs)
def_delta_name (_:xs) = (def_delta_name xs)

def_new_universe [] = []
def_new_universe ((Choose (_,_,tx) (ZVar (tt,_,_))):xs)
  = (ZBranch1 (tx,[],"") (ZVar (tt,[],""))):(def_new_universe xs)
def_new_universe (_:xs) = (def_new_universe xs)

def_sub_univ [] = []
def_sub_univ ((Choose (_,_,tx) (ZVar (tt,_,_))):xs)
  = (ZFreeTypeDef (join_name "U" tx,[],"")
      [ZBranch1 (tx,[],"") (ZVar (tt,[],""))]):(def_sub_univ xs)
def_sub_univ (_:xs) = (def_sub_univ xs)

def_sub_univ_set :: [ZGenFilt] -> [ZExpr]
def_sub_univ_set [] = []
def_sub_univ_set ((Choose (_,_,tx) (ZVar (tt,_,_))):xs)
  = (ZVar (join_name "U" tx,[],"")):(def_sub_univ_set xs)
def_sub_univ_set (_:xs) = (def_sub_univ_set xs)

def_sub_bind [] = []
def_sub_bind ((Choose (_,_,tx) (ZVar (tt,_,_))):xs)
  = (ZAbbreviation (join_name "BINDINGS" tx,[],"") (ZCall (ZVar ("\\fun",[],"")) (ZTuple [ZVar (join_name "NAME" tx,[],""),ZVar (join_name "U" tx ,[],"")]))):(def_sub_bind xs)
def_sub_bind (_:xs) = (def_sub_bind xs)

def_sub_bindn [] = []
def_sub_bindn ((Choose (_,_,tx) (ZVar (tt,_,_))):xs)
  = (ZVar (join_name "BINDINGS" tx,[],"")):(def_sub_bindn xs)
def_sub_bindn (_:xs) = (def_sub_bindn xs)

def_sub_name :: [ZGenFilt] -> [ZPara]
def_sub_name xs
    = map (subname xs) tlist
      where
        tlist = map (\(Choose v t) -> (ntrd v)) xs
        subname xs tl =
          (ZFreeTypeDef (join_name "NAME" tl,[],[]) (sub_name xs tl))
        sub_name [] _= []
        sub_name ((Choose v t):xs) t1
          | t1 == (ntrd v) = [ZBranch0 v] ++ (sub_name xs t1)
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
rename_z_schema_state spec (CProcess p (ProcDef (ProcMain (ZSchemaDef (ZSPlain n) schlst) proclst ma)))
  = (CProcess p (ProcDef (ProcMain (ZSchemaDef (ZSPlain n) (ZSchema xs)) proclst ma)))
    where
      xs = retrive_schemas spec schlst
rename_z_schema_state spec x = x
\end{code}

\begin{code}
retrive_schemas spec (ZSchema lstx) = lstx
retrive_schemas spec (ZSRef (ZSPlain nn) [] [])
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
	= (ProcDefSpot _ZGenFilt_lst  (upd_type_ProcessDef lst _ProcessDef))
upd_type_ProcessDef lst (ProcDefIndex _ZGenFilt_lst _ProcessDef)
	= (ProcDefIndex _ZGenFilt_lst  (upd_type_ProcessDef lst _ProcessDef))
upd_type_ProcessDef lst (ProcDef _CProc)
	= (ProcDef (upd_type_CProc lst _CProc))

-- CProc
upd_type_CProc lst (CRepSeqProc _ZGenFilt_lst _CProc)
	= (CRepSeqProc _ZGenFilt_lst (upd_type_CProc lst _CProc))
upd_type_CProc lst (CRepExtChProc _ZGenFilt_lst _CProc)
	= (CRepExtChProc _ZGenFilt_lst (upd_type_CProc lst _CProc))
upd_type_CProc lst (CRepIntChProc _ZGenFilt_lst _CProc)
	= (CRepIntChProc _ZGenFilt_lst (upd_type_CProc lst _CProc))
upd_type_CProc lst (CRepParalProc _CSExp _ZGenFilt_lst _CProc)
	= (CRepParalProc _CSExp _ZGenFilt_lst (upd_type_CProc lst _CProc))
upd_type_CProc lst (CRepInterlProc _ZGenFilt_lst _CProc)
	= (CRepInterlProc _ZGenFilt_lst (upd_type_CProc lst _CProc))
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
upd_type_ZVar (_:xs) (x,y,z)
    = upd_type_ZVar xs (x,y,z)

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
mk_var_v_var_bnds [] = []
mk_var_v_var_bnds ((ZVar (x,b,c)):xs) =
  [(ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar (x,b,c),ZVar (join_name "v" x,b,c)]))]++(mk_var_v_var_bnds xs)
mk_var_v_var_bnds (_:xs) = mk_var_v_var_bnds xs
\end{code}
