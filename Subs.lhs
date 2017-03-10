\section{Substitution}


\ignore{
\begin{code}
module Subs
-- $Id: Subs.hs,v 1.25 2005-02-25 14:04:11 marku Exp $

\end{code}
}

Defines substitution-related functions over Z terms. These functions should be
applied only to unfolded terms (so ZESchema, ZTheta expressions etc. are not
handled here).

Exports ZExpr and ZPred as instances of SubsTerm, which is a type class
containing functions for performing substitution, determining free variables,
etc.

Note that 'substitute sub vs term' takes a set of variables, vs, as well as
the substitution, sub.  This varset must include all free variables of the
entire term that the substituted term will be placed inside (including free
vars of 'term' itself), plus any bound variables that 'term' is within the
scope of.  This allows the substitute function to preserve the 'no-repeated-
bound-vars' invariant.

\begin{code}
(
  avoid_variables,
  choose_fresh_var,
  diff_varset,
  empty_varset,
  free_vars,    -- Hugs does not export this automatically
  free_var_ZExpr,
  free_var_ZPred,
  free_var_CAction,
  fvars_expr,
  fvars_genfilt,
  fvars_pred,
  in_varset,
  inter_varset,
  make_subinfo,
  rename_bndvars,
  rename_lhsvars,  -- only for use by Unfold really.
  show_varset,
  sub_expr,
  sub_genfilt,
  sub_genfilt2,
  sub_pred,
  subs_add,
  subs_avoid,
  subs_domain,
  subs_range,
  subs_remove,
  subs_sub,
  subseteq_varset,
  SubsTerm,
  substitute,   -- Hugs does not export this automatically
  Substitution,
  union_varset,
  union_varsets,
  uniquify,     -- Restores the no-repeated-bound-vars invariant
  VarSet,
  varset,
  varset_from_zvars,
  varset_to_zvars
)
where

import AST
import FiniteSets

type Substitution = [(ZVar,ZExpr)]

-- Optional Precondition checking
-- Define pre f msg val = val to turn this off.
pre f msg val = val
pre False msg val = error ("Precondition Error: " ++ msg)
pre True  msg val = val

class SubsTerm t where
  substitute :: Substitution -> VarSet -> t -> t
  free_vars  :: t -> VarSet   -- result is all ZVar's
  uniquify   :: VarSet -> t -> t
  uniquify   = substitute []

instance SubsTerm ZExpr where
  substitute = presubstitute sub_expr
  free_vars  = fvars_expr

instance SubsTerm ZPred where
  substitute = presubstitute sub_pred
  free_vars  = fvars_pred

presubstitute f sub vs term =
    pre ((termvars `diff_varset` domvars) `subseteq_varset` vs)
	("subs does not include all free vars: " ++ argmsg)
	(f (make_subinfo sub (union_varsets (vs:ranvars))) term)
    where
    ranvars = map (free_vars . snd) sub
    domvars = varset_from_zvars (map fst sub)
    termvars = free_vars term
    argmsg = "\n\t" ++ show term ++
	     "\n\t" ++ show sub ++
	     "\n\t{" ++ show_varset vs ++ "}"

\end{code}
\subsection{$VarSet$ ADT}

To get more typechecking, here we create a copy of the $FinSet$ ADT, restricted to handling just $(ZVar _)$ terms.
\begin{code}

newtype VarSet = VarSet FinSet   -- but containing only (ZVar _) terms.
		 deriving (Eq,Show)

-- Now we promote all the relevant FinSet operations to VarSet.
varset  :: [ZExpr] -> VarSet
varset vs
  = if bad == [] then VarSet (set vs) else error "non-vars in varset"
  where
  bad = filter (not . isZVar) vs
  isZVar (ZVar _) = True
  isZVar _        = False

varset_from_zvars  :: [ZVar] -> VarSet
varset_from_zvars = VarSet . set . map ZVar

zvars_from_zexpr (ZVar x) = [x]
zvars_from_zexpr _ = []

varset_to_zvars  :: VarSet -> [ZVar]
varset_to_zvars (VarSet (x:xs)) = zvars_from_zexpr x ++ (varset_to_zvars (VarSet xs))
varset_to_zvars empty_varset = []

empty_varset = VarSet emptyset

union_varsets :: [VarSet] -> VarSet
union_varsets vs = VarSet (gen_union [s | VarSet s <- vs])

-- binary operations
union_varset    (VarSet a) (VarSet b) = VarSet (union a b)
inter_varset    (VarSet a) (VarSet b) = VarSet (inter a b)
diff_varset     (VarSet a) (VarSet b) = VarSet (diff a b)
subseteq_varset (VarSet a) (VarSet b) = subset a b

in_varset        v         (VarSet b) = v `mem` b
show_varset     (VarSet vs) = show_zvars [v | ZVar v <- vs]

\end{code}

\subsection{$SubstitutionInfo$ ADT}

It is convenient to pass around more information than just the
substitution, so we pass around this SubstitutionInfo type,
which contains the substitution, plus the set of variables
which must be avoided when choosing new local variables.
This 'avoid' set must contain:

 \begin{itemize}   

\item  all free variables of the entire term that surrounds the term that
substitute is being applied to (usually none, because most complete terms have
no free vars). Note: This is slightly stronger than necessary -- it could be
just the free vars minus the domain of the substitution.

\item  all outer bound variables of the entire term (so that the substitution
preserves the uniquify invariant -- no repeated bound variable names on any
path into the term)

\item  all free variables in the range of the substitution (because we must
avoid capturing these) 

\end{itemize} 
\subsection{Substitution -- Manipulating sets}

\begin{code}

type SubstitutionInfo = (Substitution, VarSet)
\end{code}

\begin{code}

make_subinfo :: Substitution -> VarSet -> SubstitutionInfo
make_subinfo sub vs = (sub, vs)
\end{code}

\begin{code}

subs_sub :: SubstitutionInfo -> Substitution
subs_sub (sub,_) = sub
\end{code}

\begin{code}

subs_domain :: SubstitutionInfo -> [ZVar]
subs_domain (sub,_) = map fst sub
\end{code}

\begin{code}

subs_range :: SubstitutionInfo -> [ZExpr]
subs_range (sub,_) = map snd sub
\end{code}

\begin{code}

subs_avoid :: SubstitutionInfo -> VarSet
subs_avoid (_,vs) = vs
\end{code}

\begin{code}

subs_add :: SubstitutionInfo -> (ZVar,ZExpr) -> SubstitutionInfo
subs_add (sub,vs) (x,e) =
    ((x,e):sub, vs `union_varset` extras)
    where
    extras  = varset_from_zvars [x] `union_varset` free_vars e
\end{code}

\begin{code}

subs_remove :: SubstitutionInfo -> ZVar -> SubstitutionInfo
subs_remove (sub,vs) x = (filter (\ (v,_) -> v /= x) sub, vs)


\end{code}
\subsection{Substitution for Expressions}

\begin{code}


sub_expr :: SubstitutionInfo -> ZExpr -> ZExpr
sub_expr subs e@(ZUniverse)   = e
sub_expr subs e@(ZVar v)      = maybe e id (lookup v (fst subs))
sub_expr subs e@(ZGiven _)    = e
sub_expr subs e@(ZGivenSet _) = e
sub_expr subs e@(ZInt _)      = e
sub_expr subs (ZGenerator r e) = ZGenerator r (sub_expr subs e)
sub_expr subs e@(ZPowerSet{}) = e{baseset=sub_expr subs (baseset e)}
sub_expr subs e@(ZFuncSet{})  = e{domset=sub_expr subs (domset e),
				  ranset=sub_expr subs (ranset e)}
sub_expr subs (ZCross es)     = ZCross (map (sub_expr subs) es)
sub_expr subs (ZTuple es)     = ZTuple (map (sub_expr subs) es)
sub_expr subs (ZCall e1 e2)   = ZCall (sub_expr subs e1) (sub_expr subs e2)
sub_expr subs (ZSetDisplay es) = ZSetDisplay (map (sub_expr subs) es)
sub_expr subs (ZSeqDisplay es) = ZSeqDisplay (map (sub_expr subs) es)
sub_expr subs (ZSetComp gfs (Just e)) = ZSetComp gfs2 (Just e2)
  where
  (gfs2,e2) = sub_genfilt sub_expr subs gfs e
sub_expr subs (ZLambda gfs e) = ZLambda gfs2 e2
  where
  (gfs2,e2) = sub_genfilt sub_expr subs gfs e
sub_expr subs (ZMu gfs (Just e)) = ZMu gfs2 (Just e2)
  where
  (gfs2,e2) = sub_genfilt sub_expr subs gfs e
--sub_expr subs (ZELet defs e)  = ZELet defs2 e2
--  where
--  (defs2, e2) = sub_letdef sub_expr subs defs e
sub_expr subs (ZIf_Then_Else p e1 e2) = ZIf_Then_Else p' e1' e2'
  where
  p'  = sub_pred subs p
  e1' = sub_expr subs e1
  e2' = sub_expr subs e2
sub_expr subs (ZSelect e v) = ZSelect (sub_expr subs e) v
  -- Note that e.v = (\lambda [u:U;v:V] @ v) e      (when e:[u:U;v:V])
  --               = \{ u:U; v:V @ (\lblot u==u,v==v \rblot, v) \}
  --    Field names:                       ^    ^
  --    Variable names: ^    ^                ^    ^         ^
  -- This makes it clear that v is local to this set comprehension,
  -- so is not free within 'e.v' and should not be renamed!
sub_expr subs e@(ZReln _)     = e
sub_expr subs e@(ZFunc1 _)    = e
sub_expr subs e@(ZFunc2 _)    = e
sub_expr subs e@(ZStrange _)  = e
sub_expr subs e@(ZFSet _)     = e  -- contains no vars at all
sub_expr subs e@(ZIntSet _ _) = e
sub_expr subs (ZBinding bs)   = ZBinding [(v,sub_expr subs e)|(v,e) <- bs]
sub_expr subs e@(ZFree0 _)    = e
sub_expr subs (ZFree1 n e)    = ZFree1 n (sub_expr subs e)
sub_expr subs e@(ZFreeType _ _) = e   -- has no free variables
sub_expr subs e = error ("substitute should not see: " ++ show e)
\end{code}
\subsection{Substitution for Predicates}

\begin{code}

sub_pred :: SubstitutionInfo -> ZPred -> ZPred
sub_pred subs p@(ZFalse{})     = p
sub_pred subs p@(ZTrue{})      = p
sub_pred subs (ZAnd p1 p2)     = ZAnd (sub_pred subs p1) (sub_pred subs p2)
sub_pred subs (ZOr p1 p2)      = ZOr  (sub_pred subs p1) (sub_pred subs p2)
sub_pred subs (ZImplies p1 p2) = ZImplies (sub_pred subs p1) (sub_pred subs p2)
sub_pred subs (ZIff p1 p2)     = ZIff (sub_pred subs p1) (sub_pred subs p2)
sub_pred subs (ZNot p)         = ZNot (sub_pred subs p)
sub_pred subs (ZExists gfs p)  = ZExists gfs2 p2
  where
  (gfs2,p2) = sub_genfilt sub_pred subs gfs p
sub_pred subs (ZExists_1 gfs p)= ZExists_1 gfs2 p2
  where
  (gfs2,p2) = sub_genfilt sub_pred subs gfs p
sub_pred subs (ZForall gfs p)  = ZForall gfs2 p2
  where
  (gfs2,p2) = sub_genfilt sub_pred subs gfs p
--sub_pred subs (ZPLet defs p)   = ZPLet defs2 p2
--  where
--  (defs2, p2) = sub_letdef sub_pred subs defs p
sub_pred subs (ZEqual e1 e2)  = ZEqual (sub_expr subs e1) (sub_expr subs e2)
sub_pred subs (ZMember e1 e2) = ZMember (sub_expr subs e1) (sub_expr subs e2)
sub_pred subs p = error ("substitute should not see: " ++ show p)

\end{code}
\subsubsection{Substitution for Circus Actions}
\begin{code}
sub_ParAction :: SubstitutionInfo -> ParAction -> ParAction
sub_ParAction subs (CircusAction vCAction) = (CircusAction (sub_CAction subs vCAction))
sub_ParAction subs (ParamActionDecl vZGenFilt_lst vParAction) 
  = (ParamActionDecl vZGenFilt_lst2 vParAction2)
  where
    (vZGenFilt_lst2,vParAction2) = sub_genfilt sub_ParAction subs vZGenFilt_lst vParAction

\end{code}
\begin{code}

sub_CAction :: SubstitutionInfo -> CAction -> CAction
sub_CAction subs (CActionSchemaExpr x) = (CActionSchemaExpr x)
sub_CAction subs (CActionCommand c) = (CActionCommand (sub_CCommand subs c))
sub_CAction subs (CActionName nm) = (CActionName nm)
sub_CAction subs (CSPCommAction cc c) = (CSPCommAction (sub_Comm subs cc) (sub_CAction subs c))
sub_CAction subs (CSPGuard p c) = (CSPGuard (sub_pred subs p) (sub_CAction subs c))
sub_CAction subs (CSPSeq ca cb) = (CSPSeq (sub_CAction subs ca) (sub_CAction subs cb))
sub_CAction subs (CSPExtChoice ca cb) = (CSPExtChoice (sub_CAction subs ca) (sub_CAction subs cb))
sub_CAction subs (CSPIntChoice ca cb) = (CSPIntChoice (sub_CAction subs ca) (sub_CAction subs cb))
sub_CAction subs (CSPNSParal ns1 cs ns2 ca cb) = (CSPNSParal ns1 cs ns2 (sub_CAction subs ca) (sub_CAction subs cb))
sub_CAction subs (CSPParal cs ca cb) = (CSPParal cs (sub_CAction subs ca) (sub_CAction subs cb))
sub_CAction subs (CSPNSInter ns1 ns2 ca cb) = (CSPNSInter ns1 ns2 (sub_CAction subs ca) (sub_CAction subs cb))
sub_CAction subs (CSPInterleave ca cb) = (CSPInterleave (sub_CAction subs ca) (sub_CAction subs cb))
sub_CAction subs (CSPHide c cs) = (CSPHide (sub_CAction subs c) cs)
sub_CAction subs (CSPParAction nm xp) = (CSPParAction nm xp)
sub_CAction subs (CSPRenAction nm cr) = (CSPRenAction nm cr)
sub_CAction subs (CSPRecursion nm c) = (CSPRecursion nm (sub_CAction subs c))
sub_CAction subs (CSPUnParAction lst c nm) = (CSPUnParAction lst (sub_CAction subs c) nm)
sub_CAction subs (CSPRepSeq lst c) = (CSPRepSeq lst (sub_CAction subs c))
sub_CAction subs (CSPRepExtChoice lst c) = (CSPRepExtChoice lst (sub_CAction subs c))
sub_CAction subs (CSPRepIntChoice lst c) = (CSPRepIntChoice lst (sub_CAction subs c))
sub_CAction subs (CSPRepParalNS cs lst ns c) = (CSPRepParalNS cs lst ns (sub_CAction subs c))
sub_CAction subs (CSPRepParal cs lst c) = (CSPRepParal cs lst (sub_CAction subs c))
sub_CAction subs (CSPRepInterlNS lst ns c) = (CSPRepInterlNS lst ns (sub_CAction subs c))
sub_CAction subs (CSPRepInterl lst c) = (CSPRepInterl lst (sub_CAction subs c))
sub_CAction subs x = x

\end{code}

\subsubsection{Substitution for Circus Communication}

\begin{code}
-- I still need to work on the substitution starting from the function sub_Comm
-- so we can have substitution over Circus Actions and CircusPar.
-- This is not yet compiled, as I'm still working on it.

sub_Comm :: SubstitutionInfo -> Comm -> Comm
sub_Comm subs (ChanComm vZName vCParameter_lst) = (ChanComm vZName (map (sub_CParameter subs) vCParameter_lst))
sub_Comm subs (ChanGenComm vZName vZExpr_lst vCParameter_lst) = (ChanGenComm vZName (map (sub_expr subs) vZExpr_lst) (map (sub_CParameter subs) vCParameter_lst))
\end{code}
\begin{code}
sub_CParameter :: SubstitutionInfo -> CParameter -> CParameter
sub_CParameter subs (ChanInp vZName) = (ChanInp vZName)
sub_CParameter subs (ChanInpPred vZName vZPred) = (ChanInpPred vZName (sub_pred subs vZPred))
sub_CParameter subs (ChanOutExp vZExpr) = (ChanOutExp (sub_expr subs vZExpr))
sub_CParameter subs (ChanDotExp vZExpr) = (ChanDotExp (sub_expr subs vZExpr))
\end{code}

\subsubsection{Substitution for Circus Commands}

\begin{code}
-- sub_expr subs (ZSetComp gfs (Just e)) = ZSetComp gfs2 (Just e2)
-- (gfs2,e2) = sub_genfilt sub_expr subs gfs e
sub_CCommand :: SubstitutionInfo -> CCommand -> CCommand
sub_CCommand subs (CAssign vZVar_lst vZExpr_lst) = (CAssign vZVar_lst (map (sub_expr subs) vZExpr_lst))
sub_CCommand subs (CIf vCGActions) = (CIf (sub_CGActions subs vCGActions))
sub_CCommand subs (CVarDecl vZGenFilt_lst vCAction) 
  = (CVarDecl vZGenFilt_lst2 vCAction2)
  where
    (vZGenFilt_lst2,vCAction2) = sub_genfilt sub_CAction subs vZGenFilt_lst vCAction
sub_CCommand subs (CAssumpt vZName_lst v1ZPred v2ZPred) = (CAssumpt vZName_lst (sub_pred subs v1ZPred) (sub_pred subs v2ZPred))
sub_CCommand subs (CAssumpt1 vZName_lst vZPred) = (CAssumpt1 vZName_lst (sub_pred subs vZPred))
sub_CCommand subs (CPrefix v1ZPred v2ZPred) = (CPrefix (sub_pred subs v1ZPred) (sub_pred subs v2ZPred))
sub_CCommand subs (CPrefix1 vZPred) = (CPrefix1 (sub_pred subs vZPred))
sub_CCommand subs (CommandBrace vZPred) = (CommandBrace (sub_pred subs vZPred))
sub_CCommand subs (CommandBracket vZPred) = (CommandBracket (sub_pred subs vZPred))
sub_CCommand subs (CValDecl vZGenFilt_lst vCAction) 
  = (CValDecl vZGenFilt_lst2 vCAction2)
  where
    (vZGenFilt_lst2,vCAction2) = sub_genfilt sub_CAction subs vZGenFilt_lst vCAction
sub_CCommand subs (CResDecl vZGenFilt_lst vCAction) 
  = (CResDecl vZGenFilt_lst2 vCAction2)
  where
    (vZGenFilt_lst2,vCAction2) = sub_genfilt sub_CAction subs vZGenFilt_lst vCAction
sub_CCommand subs (CVResDecl vZGenFilt_lst vCAction) 
  = (CVResDecl vZGenFilt_lst2 vCAction2)
  where
    (vZGenFilt_lst2,vCAction2) = sub_genfilt sub_CAction subs vZGenFilt_lst vCAction
\end{code}
\begin{code}
sub_CGActions :: SubstitutionInfo -> CGActions  -> CGActions
sub_CGActions subs (CircGAction vZPred vCAction) 
  = (CircGAction (sub_pred subs vZPred) (sub_CAction subs vCAction))
sub_CGActions subs (CircThenElse (CircGAction vZPred vCAction) v2CGActions) 
  = (CircThenElse (CircGAction (sub_pred subs vZPred) (sub_CAction subs vCAction)) (sub_CGActions subs v2CGActions))
-- sub_CGActions subs (CircElse vParAction) = (CircElse vParAction)
\end{code}
\begin{code}
sub_CReplace :: SubstitutionInfo -> CReplace -> CReplace
sub_CReplace subs (CRename v1ZVar_lst v2ZVar_lst) = (CRename v1ZVar_lst v2ZVar_lst)
sub_CReplace subs (CRenameAssign v1ZVar_lst v2ZVar_lst) = (CRenameAssign v1ZVar_lst v2ZVar_lst)
\end{code}
\begin{code}

--sub_letdef :: (SubstitutionInfo -> term -> term)
--              -> SubstitutionInfo -> [(ZVar,ZExpr)] -> VarSet -> term
--              -> ([(ZVar,ZExpr)], term)
--sub_letdef subfunc subs0 defs0 t_vars t
--  = (zip lhs2 rhs2, subfunc subs2 t)
--  where
--  (lhs,rhs) = unzip defs0
--  subs1 = subs0 `subs_remove` lhs
--  dont_capture = subs_range_vars subs1
--  clash = varset_from_zvars lhs `inter_varset` dont_capture
--  inuse = t_vars `union_varset` dont_capture
--  (lhs2, extrasubs) = rename_lhsvars clash inuse lhs
--  subs2 = subs1 `subs_union` extrasubs
--  rhs2  = map (sub_expr subs0) rhs
\end{code}

\begin{code}

-- rename_lhsvars clash inuse vars
-- This chooses new names for each v in vars that is also in clash.
-- The new names are chosen to avoid inuse.
rename_lhsvars :: VarSet -> VarSet -> [ZVar] -> ([ZVar], Substitution)
rename_lhsvars (VarSet []) inuse lhs = (lhs,[]) -- optimize the common case
rename_lhsvars clash inuse [] = ([], [])
rename_lhsvars clash inuse (v:vs)
  | ZVar v `in_varset` clash = (v2:vs2, (v,ZVar v2):subs2)
  | otherwise                = (v:vs2,  subs2)
  where
  (vs2, subs2) = rename_lhsvars clash inuse2 vs
  v2 = choose_fresh_var inuse (get_zvar_name v)
  inuse2 = varset_from_zvars [v2] `union_varset` inuse

\end{code}
\subsection{Substitution}
This is the most complex part of substitution. The scope rules for $[ZGenFilt]$
lists are fairly subtle (see AST.hs) and on top of those, we have to do a
substitution, being careful (as usual!) to rename any of the bound variables
that might capture variables in the range of the substitution.  This is enough
to make life exciting...

The '$subfunc$' argument is either $sub_pred$ or $sub_expr$. It is passed as a
parameter so that this function can work on $[ZGenFilt]$ lists that are followed
by either kind of term. (An earlier version used the type class 'substitute',
and avoided having this parameter, but GHC 4.02 did not like that).

\begin{code}

sub_genfilt :: (SubstitutionInfo -> term -> term)
	       -> SubstitutionInfo -> [ZGenFilt] -> term
	       -> ([ZGenFilt], term)
sub_genfilt subfunc subs0 gfs0 t =
    (gfs, subfunc finalsubs t)
    where
    (gfs,finalsubs) = sub_genfilt2 subs0 gfs0

sub_genfilt2 :: SubstitutionInfo -> [ZGenFilt]
	     -> ([ZGenFilt], SubstitutionInfo)
sub_genfilt2 subs0 [] =
    ([], subs0)
sub_genfilt2 subs0 (Evaluate x e t:gfs0) =
    (Evaluate x2 e2 t2 : gfs, subs)
    where
    e2 = sub_expr subs0 e
    t2 = sub_expr subs0 t
    subs1 = subs0 `subs_remove` x
    (x2,subs2) =
	if ZVar x `in_varset` subs_avoid subs1
	   then (fresh, subs1 `subs_add` (x,ZVar fresh))
	   else (x,subs1)
    fresh = choose_fresh_var (subs_avoid subs1) (get_zvar_name x)
    (gfs, subs) = sub_genfilt2 subs2 gfs0
sub_genfilt2 subs0 (Choose x e:gfs0) =
    (Choose x2 (sub_expr subs0 e) : gfs, subs)
    where
    subs1 = subs0 `subs_remove` x
    (x2,subs2) =
	if ZVar x `in_varset` subs_avoid subs1
	   then (fresh, subs1 `subs_add` (x,ZVar fresh))
	   else (x,subs1)
    fresh = choose_fresh_var (subs_avoid subs1) (get_zvar_name x)
    (gfs, subs) = sub_genfilt2 subs2 gfs0
sub_genfilt2 subs0 (Check p:gfs0) =
    (Check (sub_pred subs0 p) : gfs, subs)
    where
    (gfs, subs) = sub_genfilt2 subs0 gfs0
\end{code}

This renames any bound variables that are in '$clash$', to avoid
capture problems.  (It only renames the defining occurrence of the
variables, not all the places where they are used, but it returns
a substitution which will do that when it is applied later).
To ensure that the new variable name is fresh, it is chosen to not
conflict with any of the variable in 'inuse'.

This function could almost be implemented using $map$, but we use a
recursive defn so that as each fresh variable is chosen, it can be
added to the set of '$inuse$' variables.

\begin{code}

rename_bndvars :: VarSet -> VarSet -> [ZGenFilt] -> ([ZGenFilt],Substitution)
rename_bndvars (VarSet []) _ gfs = (gfs,[]) -- optimize a common case
rename_bndvars clash inuse [] = ([],[])
rename_bndvars clash inuse (c@(Evaluate v e t):gfs0)
  | ZVar v `in_varset` clash = (Evaluate v2 e t:gfs, (v,ZVar v2):subs)
  | otherwise                = (c:gfs_easy, subs_easy)
  where
  (gfs, subs)           = rename_bndvars clash inuse2 gfs0
  (gfs_easy, subs_easy) = rename_bndvars clash inuse gfs0
  v2 = choose_fresh_var inuse (get_zvar_name v)
  inuse2 = varset_from_zvars [v2] `union_varset` inuse
rename_bndvars clash inuse (c@(Choose v e):gfs0)
  | ZVar v `in_varset` clash = (Choose v2 e:gfs, (v,ZVar v2):subs)
  | otherwise                = (c:gfs, subs)
  where
  (gfs, subs) = rename_bndvars clash inuse2 gfs0
  v2 = choose_fresh_var inuse (get_zvar_name v)
  inuse2 = varset_from_zvars [v2] `union_varset` inuse
rename_bndvars clash inuse (c@(Check _):gfs0)
  = (c:gfs, subs)
  where
  (gfs, subs) = rename_bndvars clash inuse gfs0


\end{code}
\subsection{Free Variables for $Expressions$}


\begin{code}
free_var_ZExpr :: ZExpr -> [ZVar]
free_var_ZExpr x = varset_to_zvars $ free_vars x

\end{code}
\begin{code}

-- TODO: an more efficient algorithm might be to keep track
--   of the bound vars on the way in, and only generate those
--   that are not in that set.  This is what Zeta does, and it
--   might produce less garbage.
fvars_expr :: ZExpr -> VarSet
fvars_expr ZUniverse        = empty_varset
fvars_expr e@(ZVar v)       = varset [e]
fvars_expr (ZGiven _)       = empty_varset
fvars_expr (ZGivenSet _)    = empty_varset
fvars_expr (ZInt _)         = empty_varset
fvars_expr (ZGenerator r e) = fvars_expr e
fvars_expr (ZPowerSet{baseset=e})
			    = fvars_expr e
fvars_expr (ZFuncSet{domset=e1,ranset=e2})
			    = fvars_expr e1 `union_varset` fvars_expr e2
fvars_expr (ZCross es)      = union_varsets (map fvars_expr es)
fvars_expr (ZTuple es)      = union_varsets (map fvars_expr es)
fvars_expr (ZCall e1 e2)    = fvars_expr e1 `union_varset` fvars_expr e2
fvars_expr (ZSetDisplay es) = union_varsets (map fvars_expr es)
fvars_expr (ZSeqDisplay es) = union_varsets (map fvars_expr es)
fvars_expr (ZSetComp gfs (Just e))
			    = fvars_genfilt gfs (fvars_expr e)
fvars_expr (ZLambda gfs e)  = fvars_genfilt gfs (fvars_expr e)
fvars_expr (ZMu gfs (Just e))=fvars_genfilt gfs (fvars_expr e)
fvars_expr (ZELet defs e)
  = rhsvars `union_varset` (fvars_expr e `diff_varset` bndvarset)
  where
  (bndvars, rhss) = unzip defs
  bndvarset = varset (map ZVar bndvars)
  rhsvars = union_varsets (map fvars_expr rhss)
fvars_expr (ZIf_Then_Else p e1 e2)
  = fvars_pred p `union_varset` fvars_expr e1 `union_varset` fvars_expr e2

fvars_expr (ZSelect e v)    = fvars_expr e
fvars_expr (ZReln _)        = empty_varset
fvars_expr (ZFunc1 _)       = empty_varset
fvars_expr (ZFunc2 _)       = empty_varset
fvars_expr (ZStrange _)     = empty_varset
fvars_expr (ZFSet _)        = empty_varset
fvars_expr (ZIntSet _ _)    = empty_varset
fvars_expr (ZBinding bs)    = union_varsets (map (fvars_expr . snd) bs)
fvars_expr (ZFree0 _)       = empty_varset
fvars_expr (ZFree1 n e)     = fvars_expr e
fvars_expr (ZFreeType _ _)  = empty_varset  -- has no free variables
fvars_expr e  = error ("free_vars should not see: " ++ show e)
\end{code}
\subsection{Free Variables for $Predicates$}

\begin{code}
free_var_ZPred :: ZPred -> [ZVar]
free_var_ZPred x = varset_to_zvars $ free_vars x
\end{code}

\begin{code}

fvars_pred :: ZPred -> VarSet
fvars_pred (ZFalse{})       = empty_varset
fvars_pred (ZTrue{})        = empty_varset
fvars_pred (ZAnd p1 p2)     = fvars_pred p1 `union_varset` fvars_pred p2
fvars_pred (ZOr p1 p2)      = fvars_pred p1 `union_varset` fvars_pred p2
fvars_pred (ZImplies p1 p2) = fvars_pred p1 `union_varset` fvars_pred p2
fvars_pred (ZIff p1 p2)     = fvars_pred p1 `union_varset` fvars_pred p2
fvars_pred (ZNot p)         = fvars_pred p
fvars_pred (ZExists gfs p)  = fvars_genfilt gfs (fvars_pred p)
fvars_pred (ZExists_1 gfs p)= fvars_genfilt gfs (fvars_pred p)
fvars_pred (ZForall gfs p)  = fvars_genfilt gfs (fvars_pred p)
fvars_pred (ZPLet defs p)
  = rhsvars `union_varset` (fvars_pred p `diff_varset` bndvarset)
  where
  (bndvars, rhss) = unzip defs
  bndvarset = varset (map ZVar bndvars)
  rhsvars = union_varsets (map fvars_expr rhss)
fvars_pred (ZEqual e1 e2)   = fvars_expr e1 `union_varset` fvars_expr e2
fvars_pred (ZMember e1 e2)  = fvars_expr e1 `union_varset` fvars_expr e2
fvars_pred p = error ("freevars should not see: " ++ show p)
\end{code}

\begin{code}
free_var_ZGenFilt lst f e = varset_to_zvars $ (fvars_genfilt lst (varset_from_zvars $ f e))
\end{code}

\begin{code}


fvars_genfilt :: [ZGenFilt] -> VarSet -> VarSet
fvars_genfilt gfs inner = foldr adjust inner gfs
    where
    adjust (Choose x t) inner =
	(inner `diff_varset` varset_from_zvars [x])
	 `union_varset` free_vars t
    adjust (Check p) inner =
	inner `union_varset` free_vars p
    adjust (Evaluate x e t) inner =
	(inner `diff_varset` varset_from_zvars [x])
	  `union_varset` (free_vars e `union_varset` free_vars t)
\end{code}
\subsection{Free Variables for \Circus\ actions }

\begin{code}

free_var_CAction :: CAction -> [ZVar]
free_var_CAction (CActionSchemaExpr x) = []
free_var_CAction (CActionCommand c) = (free_var_comnd c)
free_var_CAction (CActionName nm) = []
free_var_CAction (CSPSkip) = []
free_var_CAction (CSPStop) = []
free_var_CAction (CSPChaos) = []
free_var_CAction (CSPCommAction (ChanComm com xs) c) = (get_chan_var xs)++(free_var_CAction c)
free_var_CAction (CSPGuard p c) = (free_var_ZPred p)++(free_var_CAction c)
free_var_CAction (CSPSeq ca cb) = (free_var_CAction ca)++(free_var_CAction cb)
free_var_CAction (CSPExtChoice ca cb) = (free_var_CAction ca)++(free_var_CAction cb)
free_var_CAction (CSPIntChoice ca cb) = (free_var_CAction ca)++(free_var_CAction cb)
free_var_CAction (CSPNSParal ns1 cs ns2 ca cb) = (free_var_CAction ca)++(free_var_CAction cb)
free_var_CAction (CSPParal cs ca cb) = (free_var_CAction ca)++(free_var_CAction cb)
free_var_CAction (CSPNSInter ns1 ns2 ca cb) = (free_var_CAction ca)++(free_var_CAction cb)
free_var_CAction (CSPInterleave ca cb) = (free_var_CAction ca)++(free_var_CAction cb)
free_var_CAction (CSPHide c cs) = (free_var_CAction c)
free_var_CAction (CSPParAction nm xp) = []
free_var_CAction (CSPRenAction nm cr) = []
free_var_CAction (CSPRecursion nm c) = (free_var_CAction c)
free_var_CAction (CSPUnParAction lst c nm) =  free_var_ZGenFilt lst free_var_CAction c
free_var_CAction (CSPRepSeq lst c) =  free_var_ZGenFilt lst free_var_CAction c
free_var_CAction (CSPRepExtChoice lst c) =  free_var_ZGenFilt lst free_var_CAction c
free_var_CAction (CSPRepIntChoice lst c) =  free_var_ZGenFilt lst free_var_CAction c
free_var_CAction (CSPRepParalNS cs lst ns c) =  free_var_ZGenFilt lst free_var_CAction c
free_var_CAction (CSPRepParal cs lst c) =  free_var_ZGenFilt lst free_var_CAction c
free_var_CAction (CSPRepInterlNS lst ns c) =  free_var_ZGenFilt lst free_var_CAction c
free_var_CAction (CSPRepInterl lst c) =  free_var_ZGenFilt lst free_var_CAction c
\end{code}


\begin{code}
get_chan_var :: [CParameter] -> [ZVar]
get_chan_var [] = []
get_chan_var [ChanDotExp (ZVar (x,_))] = [(x,[])]
get_chan_var [ChanOutExp (ZVar (x,_))] = [(x,[])]
get_chan_var [_] = []
get_chan_var ((ChanDotExp (ZVar (x,_))):xs) = [(x,[])]++(get_chan_var xs)
get_chan_var ((ChanOutExp (ZVar (x,_))):xs) = [(x,[])]++(get_chan_var xs)
get_chan_var (_:xs) = (get_chan_var xs)
\end{code}


\subsection{Free Variables for \Circus\ commands }

\begin{code}
free_var_comnd (CAssign v e)
 = v
free_var_comnd (CIf ga)
 = free_var_if ga
free_var_comnd (CVarDecl lst c)
 =  free_var_ZGenFilt lst free_var_CAction c
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
free_var_comnd (CValDecl lst c)
 =  free_var_ZGenFilt lst free_var_CAction c
free_var_comnd (CResDecl lst c)
 =  free_var_ZGenFilt lst free_var_CAction c
free_var_comnd (CVResDecl lst c)
 =  free_var_ZGenFilt lst free_var_CAction c
\end{code}

\begin{code}
free_var_if (CircGAction p a)
 = (free_var_ZPred p)++(free_var_CAction a)
free_var_if (CircThenElse (CircGAction p a) gb)
 = (free_var_ZPred p)++(free_var_CAction a)++(free_var_if gb)
-- free_var_if (CircElse (CircusAction a))
--  = (free_var_CAction a)
-- free_var_if (CircElse (ParamActionDecl x (CircusAction a)))
--  =  free_var_ZGenFilt x free_var_CAction a
\end{code}
\subsection{Fresh Variables generator }
\begin{code}

-- returns a ZVar that does not appear in the given list of zvars.
choose_fresh_var :: VarSet -> String -> ZVar
choose_fresh_var vs s
  = head [v|d <- decors, let v = make_zvar s d, not (ZVar v `in_varset` vs)]

decors0 = [[d] | d <- ["_1","_2","_3","_4","_5","_6","_7","_8","_9"]]
decors  = [[]] ++ [d2++d | d2 <- decors, d <- decors0]


avoid_variables :: Env -> VarSet
avoid_variables = varset_from_zvars . map fst . local_values
\end{code}
