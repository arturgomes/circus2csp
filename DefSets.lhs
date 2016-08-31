\section{Introduction}

\ignore{
\begin{code}
module DefSets
where
import Data.List
import AST
\end{code}
}
\begin{code}
inSet c acls = [ x | x <- acls, x == c]
\end{code}
\begin{code}
invertBool x
  = case x of
      False -> True
      True  -> False
\end{code}
\begin{code}
subsetEq as bs = isPrefixOf as bs
\end{code}
\begin{code}
notinSet c acls = isEmpty [ x | x <- acls, x == c]
\end{code}
\begin{code}
intersectionSet as bs
  = let ns = [ a | a <- as, elem a bs] in [ b | b <- bs, elem b ns]
\end{code}

\begin{code}
unionSet as bs
  = let ns = [ a | a <- as++bs]
  	in [x | (x,y) <- zip ns [0..], x `notElem` (take y as)]
\end{code}
\begin{code}
isEmpty xs
  = case xs of
      [] -> True
      _  -> False
\end{code}
\begin{code}
isNotEmpty xs
  = case xs of
      [] -> True
      _  -> False
\end{code}
\begin{code}
-- TODO: Need to do it
getFV xs = free_var_ZExpr xs
\end{code}
\begin{code}
-- TODO: Need to do it
getWrtV xs = []
\end{code}
\begin{code}
maybeToBool x
 = case x
 of
 	Just _  -> True
 	Nothing -> False
\end{code}
Bits for FreeVariables (FV(X))
\begin{code}

free_var_ZExpr :: ZExpr -> [ZVar]

free_var_ZExpr(ZVar v) = [v]
free_var_ZExpr(ZInt c ) = []
free_var_ZExpr(ZGiven a) = error "Don't know what free vars of ZGiven are right now. Check back later"

free_var_ZExpr(ZFree0 a) = error "Don't know what free vars of ZFree0 are right now. Check back later"

free_var_ZExpr(ZFree1 v ex) = error "Don't know what free vars of ZFree1 are right now. Check back later"
free_var_ZExpr(ZTuple exls ) = fvs exls
free_var_ZExpr(ZBinding a) = error "Don't know what free vars of ZBinding are right now. Check back later"
free_var_ZExpr(ZSetDisplay exls ) = fvs exls
free_var_ZExpr(ZSeqDisplay exls ) = fvs exls
free_var_ZExpr(ZFSet fs ) = error "Don't know what free vars of ZFSet are right now. Check back later"
free_var_ZExpr(ZIntSet zi1 zi2) = error "Don't know what free vars of ZIntSet are right now. Check back later"
free_var_ZExpr(ZGenerator rl ex) = error "Don't know what free vars of ZGenerator are right now. Check back later"
free_var_ZExpr(ZCross exls ) = fvs exls
free_var_ZExpr(ZFreeType zv zbls) = error "Don't know what free vars of ZFreeType are right now. Check back later"
free_var_ZExpr(ZPowerSet{baseset=b, is_non_empty=e, is_finite=fs}) = error "Don't know what free vars of ZPowerSet are right now. Check back later"
free_var_ZExpr(ZFuncSet{domset=d, ranset=r, is_function=f, is_total=t, is_onto=o, is_one2one=oo, is_sequence=s, is_non_empty=ne, is_finite=ff}) = error "Don't know what free vars of ZFree0 are right now. Check back later"
free_var_ZExpr(ZSetComp gfls ma) = error "Don't know what free vars of ZSetComp are right now. Check back later"
free_var_ZExpr(ZLambda zgls ex) = error "Don't know what free vars of ZLambda are right now. Check back later"
free_var_ZExpr(ZESchema a) = error "Don't know what free vars of ZESchema are right now. Check back later"
free_var_ZExpr(ZGivenSet a) = error "Don't know what free vars of ZGivenSet are right now. Check back later"
free_var_ZExpr(ZUniverse) = error "Don't know what free vars of ZUniverse are right now. Check back later"
free_var_ZExpr(ZCall ex ex2) = free_var_ZExpr ex2 -- is this right??
free_var_ZExpr(ZReln rl ) = error "Don't know what free vars of ZReln are right now. Check back later"
free_var_ZExpr(ZFunc1 a) = error "Don't know what free vars of ZFunc1 are right now. Check back later"
free_var_ZExpr(ZFunc2 a) = error "Don't know what free vars of ZFunc2 are right now. Check back later"
free_var_ZExpr(ZStrange zs ) = error "Don't know what free vars of ZStrange are right now. Check back later"
free_var_ZExpr(ZMu zgls mex) = error "Don't know what free vars of ZMu are right now. Check back later"
free_var_ZExpr(ZELet ves pr)
	= (setDif (free_var_ZExpr(pr)) (map fst ves)) ++ fvs(map snd ves)
free_var_ZExpr(ZIf_Then_Else zp ex ex1) = error "Don't know what free vars of ZIf_Then_Else are right now. Check back later"
--free_var_ZExpr(ZIf_Then_Else zp ex ex1) = free_var_ZPred zp ++ free_var_ZExpr ex ++ free_var_ZExpr ex1
free_var_ZExpr(ZSelect ex zv) = error "Don't know what free vars of ZSelect are right now. Check back later"
free_var_ZExpr(ZTheta zsx) = error "Don't know what free vars of ZTheta are right now. Check back later"

free_var_ZPred :: ZPred -> [ZVar]

free_var_ZPred (ZFalse{reason=p}) = error "Don't know what free vars of ZFalse are right now. Check back later"
free_var_ZPred (ZTrue{reason=p}) = error "Don't know what free vars of ZTrue are right now. Check back later"
free_var_ZPred (ZAnd a b) = free_var_ZPred a ++ free_var_ZPred b
free_var_ZPred (ZOr a b) = free_var_ZPred a ++ free_var_ZPred b
free_var_ZPred (ZImplies a b) =  free_var_ZPred a ++ free_var_ZPred b
free_var_ZPred (ZIff a b) =  free_var_ZPred a ++ free_var_ZPred b
free_var_ZPred (ZNot a) = free_var_ZPred a
free_var_ZPred (ZExists [Choose v e] a) = setDif (free_var_ZPred a) [v]
free_var_ZPred (ZExists ls a) = error "Don't know what free vars of ZExists are right now. Check back later"
free_var_ZPred (ZExists_1 [Choose v e] a) = setDif (free_var_ZPred a) [v]
free_var_ZPred (ZExists_1 ls a) = error "Don't know what free vars of ZExists_1 are right now. Check back later"
free_var_ZPred (ZForall [Choose v e] a) = setDif (free_var_ZPred a) [v]
free_var_ZPred (ZForall ls a) = error "Don't know what free vars of ZForall are right now. Check back later"
free_var_ZPred (ZPLet ls a ) = error "Don't know what free vars of ZPLet are right now. Check back later"
--free_var_ZPred (ZEqual expa expb) = free_var_ZExpr expa ++ free_var_ZExpr expb
free_var_ZPred (ZEqual expa expb) = error "Don't know what free vars of ZEqual are right now. Check back later"
free_var_ZPred (ZMember expa expb) = error "Don't know what free vars of ZMember are right now. Check back later"
free_var_ZPred (ZPre zsexpr) = error "Don't know what free vars of ZPre are right now. Check back later"
free_var_ZPred (ZPSchema zsexpr) = error "Don't know what free vars of ZPSchema are right now. Check back later"

fvs [] = []
fvs (e:es) = free_var_ZExpr(e) ++ fvs(es)

removeItem x list  = [y | y <- list, y/=x]
setDif z [] = z
setDif xs (y:ys) = setDif (removeItem y xs) ys

\end{code}