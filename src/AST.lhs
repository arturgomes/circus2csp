\chapter{Abstract Syntax Trees}
\ignore{
Both Z and Circus AST are found here.
\begin{code}
module AST where
\end{code}

\begin{verbatim}
--
-- $Id: AST.hs,v 1.58 2005-03-26 13:07:43 marku Exp $
--
-- This module defines Abstract Syntax Trees for Z terms
-- (expressions, predicates, schemas etc.).
-- These abstract syntax trees are also used for the *result* of
-- evaluating Z terms.
--
-- There are often several semantically equivalent data structures for
-- representing a given result, each with different space usage and ability
-- to perform various operations efficiently.  For example, the result of
-- evaluating a set comprehension expression (of type \power \ints) could
-- be represented by several data structures, including:
--
--       ZIntSet (Just lo) (Just hi)                       (= lo .. hi)
--       ZFSet s                       (s is defined in FiniteSets.lhs)
--       ZSetDisplay [ZInt 3, ZInt 4, complex_int_expr]
--
-- The ZIntSet one is best for contiguous ranges of integers and can even
-- handle infinite ranges (a missing endpoint); the ZFSet one is only
-- used when all elements are defined and in canonical form -- it keeps
-- elements in strictly sorted order so that common set operations can be
-- done in linear time; The ZSetDisplay structure is used for finite sets
-- that contain complex (non-canonical) elements (for example the above
-- ZSetDisplay may contain two or three elements, depending upon whether
-- the 'complex_int_expr' evaluates to 3 or 4 or something else).
--
-- Evaluation functions may use different strategies for each data
-- structure, or may coerce a given structure into their favourite.
--
-- Haskell defines == (and <, > etc.) over ZExpr structures, but this
-- is not always the same as semantic equality (=).  Eg. Is this true?
--
--              a==b   =>  a=b
--
-- According to Spivey and the Z standard, not always!  If a or b
-- is undefined, then the truth value of a=b is unknown.
-- Even more commonly, the converse is not always true, because several
-- different data structures may represent the same value.  However, when
-- both a and b are in 'canonical' (see isCanonical below) form, we have:
--
--              a==b   <=>   a=b.
--
-- Intuitively, any ZExpr that is constructed entirely from the following
-- constructors must be in a unique canonical form:
--
--    ZInt, ZGiven, ZTuple, ZFree0, ZFree1, ZFSet, ZBinding.
--
-- Free types are represented as follows.
-- Given a typical free type:   CList ::= nil | cons <<C x CList>>,
-- T is represented by the data structure:
--
--  d = ZFreeType clist
--        [ZBranch0 nil,
--         ZBranch1 cons (ZCross (...C...) (ZVar clist))]
--
-- where nil=("nil",[]), cons=("cons",[]), clist=("CList",[]).
-- Note how the first argument to ZFreeType supports recursive references.
-- After the 'unfold' stage, free types never contain any free variables.
--
-- Members of this free type are represented as:
--
--      nil       is ZFree0 nil
--
--      cons      is the function (\lambda x: c \cross d @ Free1 cons x)
--                (functions are actually represented as a ZSetComp term)
--
--      cons val  is ZFree1 cons val   (if val is in C \cross CList)
--                                     (otherwise it will be undefined)
--
-- where x is some local ZVar, c is the representation of type C
-- and d is given above.  In other words, (ZBranch0 nil) represents
-- the singleton set:   { ZFree0 nil }
--
-- Invariants
-- ==========
-- Here are the main invariants of these data structures:
--
-- * ZTuple and ZCross always have at least two members in their arg list.
-- * ZFSet only contains canonical values.
-- * If ZIntSet has both an upper and lower bound, then the lower bound
--   should be no greater than the upper.  (In fact, the empty set case
--   is normally represented as 'zemptyset', below).
-- * An empty set can be represented in many ways, but the preferred
--   representation is 'zemptyset', below).
-- * All manipulations of the argument of ZFSet should be done via
--   functions in the FiniteSets module (in case the representation
--   of those finite sets changes in the future).  Construction of a
--   new finite set should normally be done via FiniteSets.make_zfset.
--   (it will return ZSetDisplay instead if some members are not canonical).
-- * The (name,value) pairs of ZBinding terms are always sorted in
--   increasing alphabetically order, with no duplicate names.
-- * The Maybe parts of ZSetComp and ZMu are always filled in
--   after the unfold phase.  That is, they are not 'Nothing'.
-- * All schema expressions are removed during the Unfold phase.
\end{verbatim}

\section{Z Abstract Syntax}

\subsection{Z Given Sets}
\begin{code}
type GivenSet = ZVar      -- names of given sets.
type GivenValue = String  -- members of given sets are strings
type ZInt = Integer       -- If you change this, you must also change
        -- the definition of L_NUMBER in Lexer.hs
type ZFSet = [ZExpr]      -- But always manipulate via FiniteSets functions.
\end{code}

TODO: Make this a separate module, perhaps combined with \texttt{VarSet}.

\subsection{Z Names and Decorations}
\begin{code}
data ZDecor
  = ZPrime | ZInput | ZOutput |ZDelta | ZXi | ZUnI -- a decor: ''', '!', '?' or '_N'
  deriving (Eq,Ord,Show)
type ZVar = (String, [ZDecor], String) -- all kinds of Z names
type ZName = String
\end{code}

\begin{code}

make_zvar :: String -> [ZDecor] -> ZVar
make_zvar s dl = (s,dl,"")

make_ztvar :: String -> [ZDecor] -> String -> ZVar
make_ztvar s dl t = (s,dl,t)

decorate_zvar :: ZVar -> [ZDecor] -> ZVar
decorate_zvar (s,dl,t) d = (s,dl++d,t)

prime_zvar :: ZVar -> ZVar
prime_zvar v = decorate_zvar v [ZPrime]

unprime_zvar :: ZVar -> ZVar
-- Pre: is_primed_zvar v
unprime_zvar (n,[ZPrime],t) = (n,[],t)

string_to_zvar :: String -> ZVar
string_to_zvar s = make_zvar s []
nfst :: ZVar -> String
nfst (a,b,c) = a
nsnd :: ZVar -> [ZDecor]
nsnd (a,b,c) = b

ntrd :: ZVar -> String
ntrd (a,b,c) = c

get_zvar_name :: ZVar -> String
get_zvar_name = nfst

get_zvar_decor :: ZVar -> [ZDecor]
get_zvar_decor = nsnd

is_unprimed_zvar :: ZVar -> Bool
is_unprimed_zvar (_,[],_)  = True
is_unprimed_zvar _       = False

is_primed_zvar :: ZVar -> Bool
is_primed_zvar (_,[ZPrime],_) = True
is_primed_zvar _         = False

is_input_zvar :: ZVar -> Bool
is_input_zvar (_,[ZInput],_)  = True
is_input_zvar _          = False

is_output_zvar :: ZVar -> Bool
is_output_zvar (_,[ZOutput],_) = True
is_output_zvar _         = False


show_zvar :: ZVar -> String
show_zvar (s,dl,t) = s ++ (concat $ map show_zdecor dl)

show_zdecor ZPrime = "'"
show_zdecor ZInput = "?"
show_zdecor ZOutput = "!"
show_zdecor ZDelta = "Delta"
show_zdecor ZXi = "Xi"
show_zdecor ZUnI = "_i"
show_zvars :: [ZVar] -> String
show_zvars = concatMap ((' ':) . show_zvar)
\end{code}

\subsection{Z Relations and Functions}
\begin{code}
data ZReln   -- binary toolkit relations (all take one arg: a pair)
  = ZLessThan        -- 3 < 4
  | ZLessThanEq      -- 3 \leq 3
  | ZGreaterThan     -- 4 > 3
  | ZGreaterThanEq   -- 4 \geq 4
  | ZSubset          -- {1,2} \subset {1,2,4}
  | ZSubsetEq        -- {1,2} \subseteq {1,2}
  | ZPartition       -- {(1,{1,3}),(4,{2,4})} \partition 1..4
  | ZPrefix          -- <1,2> \prefix <1,2,3,4>
  | ZSuffix          -- <2,3> \suffix <0,1,2,3>
  | ZInSeq           -- <2,3> \inseq  <0,1,2,3,4,5>
  -- These next two should only be used within the Pretty Printer.
  -- E.g. The parser expands a \neq b into (ZNot (ZEqual a b))
  --      and that form is always used internally.
  | ZNeq
  | ZNotin
  deriving (Eq,Ord,Show)

data ZFunc1  -- prefix and postfix unary functions
       -- (These all take an argument that is not a pair)
  = ZDom     -- \dom
  | ZRan     -- \ran
  | ZSizeof  -- slash hash-symbol
  | ZBigCup  -- \bigcup
  | ZBigCap  -- \bigcap
  | ZId      -- \id    -- changed into ZSetComp by Unfold.hs
  | ZRev     -- rev
  | ZHead    -- head
  | ZLast    -- last
  | ZTail    -- tail
  | ZFront   -- front
  | ZSquash  -- squash
  | ZDCat    -- \dcat
  | ZSucc    -- succ   -- changed into ZSetComp by Unfold.hs
  | ZNegate  -- '-'
  | ZMax     -- max
  | ZMin     -- min
  | ZInv     -- '~'
  | ZStar    -- '*'
  | ZClosure -- '+'
  | ZSum     -- an extension for 424 module 3.
  deriving (Eq,Ord,Show)


data ZFunc2  -- binary functions that take one argument: a pair
  = ZMapsto  -- \mapsto   (unfoldexpr converts this into a pair
  -- Integer operations
  | ZUpto    -- \upto
  | ZPlus    -- +
  | ZMinus   -- '-'
  | ZTimes   -- *
  | ZDiv     -- \div
  | ZMod     -- \mod
  -- Set operations
  | ZUnion   -- \cup
  | ZInter   -- \cap
  | ZSetMinus-- '\'
  -- Relation/Function operations
  | ZComp    -- \comp     (relation composition)
  | ZCirc    -- \circ     (backward relation composition)
  | ZDRes    -- \dres
  | ZRRes    -- \rres
  | ZNDRes   -- \ndres
  | ZNRRes   -- \nrres
  | ZRelImg  -- _ \limg _ \rimg
  | ZOPlus   -- \oplus    (function/relation overriding)
  -- Sequence operations
  | ZCat     -- \cat      sequence concatenation
  | ZExtract -- \extract  = \squash (A \dres Seq)
  | ZFilter  -- \filter   = \squash (Seq \rres A)
  -- These two are not syntactically binary functions, but semantically
  -- they behave as though they are, because they take a pair as an argument.
  | ZFirst   -- first
  | ZSecond  -- second
  deriving (Eq,Ord,Show)

data ZStrange -- toolkit functions/sets that defy categorization!
  = ZIter     -- iter n R (or R^n) is curried: takes two arguments.
  | ZDisjoint -- is a set of functions of type: Index \pfun \power Elem
  deriving (Eq,Ord,Show)
\end{code}

\newpage
\subsection{Z Generators and Filters}
These 'Generator or Filter' terms are used to represent the
search space within quantifiers, set comprehensions, schemas.
All (Include ...) terms should be expanded out before being
passed to the eval... functions.

The scope of declared names is complex here.
Immediately after parsing, the usual Z scope rules apply.
That is, in $[x:T;y:U;P;Q]$ the scope of $x$ and $y$ includes any predicates
such as $P$ and $Q$, but excludes all types, $T$ and $U$.  This allows
signatures (declarations) to be reordered with impunity.

AFTER the unfold and uniquify stages (see Unfold.hs), the scope
rules are basically left to right.  A variable x is in scope
immediately AFTER its declaration.  Note that in 'Choose x t',
the t is not in the scope of the newly declared x, but following
predicates and declarations are in the scope of x.  Similarly for
'Evaluate x e t' --- e and t are outside the scope of x.
This means that one must be careful when reordering elements
of a [GenFilt] not to move terms further left than the declarations
the their free variables.

Note: to implement these scoping rules, a common trick that we use
      in several places (eg. \verb"Eval::gen_and_filter") is to pass around
      TWO environments as we recurse through a [ZGenFilt].
      One environment is the environment from outside the whole list,
      and is used to evaluate/manipulate the type expressions, while
      the other environment is the internal one (which is extended as
      we go left to right into the list) and is used on the other
      expressions and predicates.


\begin{code}
data ZGenFilt
  = Include ZSExpr     -- Schema inclusion
  | Choose ZVar ZExpr  -- (Choose x T) means x:T
  | Check ZPred
  | Evaluate ZVar ZExpr ZExpr -- This means Let x==e | e \in t
  deriving (Eq,Ord,Show)
\end{code}

\begin{code}

genfilt_names :: [ZGenFilt] -> [ZVar]
genfilt_names []                   = []
genfilt_names (Choose v _:gfs)     = v : genfilt_names gfs
genfilt_names (Check _:gfs)        = genfilt_names gfs
genfilt_names (Evaluate v _ _:gfs) = v : genfilt_names gfs
genfilt_names (Include s:gfs)
  = error ("genfilt_names called before "++show s++" expanded.")
\end{code}

\subsection{Z Expressions}
\begin{code}
data ZExpr
  = ---------- Basic Z values (non-set values) ----------
    ZVar ZVar           -- for non-schema names (may include decorations)
  | ZInt ZInt           -- an integer constant
  | ZGiven GivenValue   -- an element of a given set
  | ZFree0 ZVar         -- a member of a free type.
  | ZFree1 ZVar ZExpr   -- a member of a free type (with an argument)
  | ZTuple [ZExpr]      -- (a,b,c)
  | ZBinding [(ZVar,ZExpr)] -- always in sorted name order (no duplicates)
  ---------- Data structures for sets ----------
  -- These are roughly ordered by how 'large' a set they typically represent.
  | ZSetDisplay [ZExpr]   -- set displays, like {1,2,4}
  | ZSeqDisplay [ZExpr]   -- sequence displays, like <1,2,4>
  | ZFSet ZFSet           -- all elements must be in canonical form.
  | ZIntSet (Maybe ZInt) (Maybe ZInt) -- integer range with lo/hi bounds.
        --   ZIntSet (Just lo) (Just hi) means lo..hi.
        --   ZIntSet Nothing   (Just hi) means -infinity..hi.
        --   ZIntSet (Just lo) Nothing   means lo..+infinity.
        --   ZIntSet Nothing   Nothing   means \num
  | ZGenerator ZReln ZExpr -- sets that are useful for iterating through.
        -- ZGenerator r e = { x:ZUniverse | x rel e }
  | ZCross [ZExpr]        -- a \cross b \cross c
  | ZFreeType ZVar [ZBranch] -- an entire free type (all branches)
  | ZPowerSet{baseset::ZExpr, -- power set types
        is_non_empty::Bool,
        is_finite::Bool}
  | ZFuncSet{ domset::ZExpr, -- relation/function/sequence types
        ranset::ZExpr,
        is_function::Bool,
        is_total::Bool,        -- dom R = domset
        is_onto::Bool,         -- ran R = ranset
        is_one2one::Bool,      -- injective
        is_sequence::Bool,     -- dom is 1.. length s
        is_non_empty::Bool,
        is_finite::Bool}
  | ZSetComp [ZGenFilt] (Maybe ZExpr) -- set comprehensions
  | ZLambda [ZGenFilt] ZExpr          -- only for parsing (removed in Unfold)
  | ZESchema ZSExpr                   -- sets of bindings (removed in Unfold)
  | ZESchemaP [ZVar] ZSExpr                   -- sets of bindings (removed in Unfold)
  | ZGivenSet GivenSet                -- an entire given set
  | ZUniverse               -- the set of all Z values! (a unit for \cap)
  ---------- Z constructs that are not necessarily sets ----------
  | ZCall ZExpr ZExpr                 -- function call:  f a
  | ZReln ZReln                       -- binary toolkit relations
  | ZFunc1 ZFunc1                     -- unary toolkit functions
  | ZFunc2 ZFunc2                     -- binary toolkit functions
  | ZStrange ZStrange                 -- miscellaneous toolkit functions/sets.
  | ZMu [ZGenFilt] (Maybe ZExpr)      -- mu expression
  | ZELet [(ZVar,ZExpr)] ZExpr        -- let a=1;b=2 in... (removed in Unfold)
  | ZIf_Then_Else ZPred ZExpr ZExpr   -- if p then e1 else e2
  | ZSelect ZExpr ZVar                -- e.field
  | ZTheta ZSExpr                     -- \theta S (removed in Unfold)
  deriving (Eq,Ord,Show)
\end{code}

\texttt{ZValue} is a synonym for \texttt{ZExpr}, but is used for the result of
evaluations, where the last group of \texttt{ZExpr} alternatives above
are the most common kinds of results.

\begin{code}
type ZValue = ZExpr
\end{code}

\begin{code}
is_pair :: ZValue -> Bool
is_pair (ZTuple [_,_]) = True
is_pair _              = False

pair_fst :: ZValue -> ZValue
pair_fst (ZTuple [x,_]) = x
pair_fst _ = error "pair_fst applied to non-pair value"

pair_snd :: ZValue -> ZValue
pair_snd (ZTuple [_,y]) = y
pair_snd _ = error "pair_snd applied to non-pair value"

isZFSet :: ZExpr -> Bool
isZFSet (ZFSet _) = True
isZFSet _         = False

-- This is equivalent to (ZFSet FiniteSets.emptyset), but
-- for convenience we define it directly here.
zemptyset :: ZExpr
zemptyset = ZFSet []

-- This is the union of all Z relations:  ZUniverse <-> ZUniverse
zrelations :: ZExpr
zrelations = ZFuncSet{domset=ZUniverse,
          ranset=ZUniverse,
          is_function =False,
          is_total    =False,
          is_onto     =False,
          is_one2one  =False,
          is_sequence =False,
          is_non_empty=False,
          is_finite   =False}
\end{code}

\subsection{Z Predicates}
\begin{code}
data ZPred
  = ZFalse{reason::[ZPred]}
  | ZTrue{reason::[ZPred]}
  | ZAnd ZPred ZPred
  | ZOr ZPred ZPred
  | ZImplies ZPred ZPred
  | ZIff ZPred ZPred
  | ZNot ZPred
  | ZExists [ZGenFilt] ZPred
  | ZExists_1 [ZGenFilt] ZPred
  | ZForall [ZGenFilt] ZPred
  | ZPLet [(ZVar,ZExpr)] ZPred  -- removed in Unfold
  | ZEqual ZExpr ZExpr
  | ZMember ZExpr ZExpr
  | ZPre ZSExpr                 -- removed in Unfold
  | ZPSchema ZSExpr             -- removed in Unfold
  deriving (Eq,Ord,Show)

ztrue = ZTrue{reason=[]}
zfalse = ZFalse{reason=[]}
\end{code}

\subsection{Z Schemas}
\begin{code}
data ZSExpr
  = ZSchema [ZGenFilt]
  | ZSRef ZSName [ZDecor] [ZReplace]
  | ZSRefP ZSName [ZDecor] [ZVar] [ZReplace]
  | ZS1 ZS1 ZSExpr              -- unary schema operators
  | ZS2 ZS2 ZSExpr ZSExpr       -- binary schema operators
  | ZSHide ZSExpr [ZVar]
  | ZSExists [ZGenFilt] ZSExpr
  | ZSExists_1 [ZGenFilt] ZSExpr
  | ZSForall [ZGenFilt] ZSExpr
  deriving (Eq,Ord,Show)

-- Note that any legal list of ZReplace's must not contain any repeated
-- first-argument ZVars.  Eg [a/b,a/c] is legal, but [b/a,c/a] is not.
-- When renaming causes names to be merged, the merged names must have
-- the same type.
data ZReplace
  = ZRename ZVar ZVar           -- S [yi / xi] = ZRename (ZVar xi []) (ZVar yi [])
  | ZAssign ZVar ZExpr          -- S [xi := 3] = ZAssign (ZVar xi []) (Int 3)
  deriving (Eq,Ord,Show)

data ZSName                     -- schema names including prefix.
  = ZSPlain String [ZVar] | ZSDelta String [ZVar] | ZSXi String [ZVar]
  deriving (Eq,Ord,Show)

data ZS1
  = ZSPre | ZSNot
  deriving (Eq,Ord,Show)

data ZS2
  = ZSAnd | ZSOr | ZSImplies | ZSIff
  | ZSProject | ZSSemi | ZSPipe
  deriving (Eq,Ord,Show)
\end{code}
}
\ignore{
\begin{code}
data ZBranch                    -- E.g. given T ::= A | C <<N x T>>
  = ZBranch0 ZVar               -- the A branch is: ZBranch0 ("A",[])
  | ZBranch1 ZVar ZExpr         -- and C branch is: ZBranch1 ("C",[]) (ZCross [...])
  deriving (Eq,Ord,Show)

isBranch0 :: ZBranch -> Bool
isBranch0 (ZBranch0 _) = True
isBranch0 _            = False

type ZSpec = [ZPara]
\end{code}


Any \texttt{ZExpr}/\texttt{ZValue} that satisfies 'isCanonical'
is fully evaluated into a unique form.
For such terms, \verb"==" is equivalent to semantic equality.
\begin{code}
isCanonical :: ZExpr -> Bool
isCanonical (ZInt _)      = True
isCanonical (ZFSet _)     = True  -- an invariant of the system
isCanonical (ZTuple v)    = all isCanonical v
isCanonical (ZGiven _)    = True
isCanonical (ZFree0 _)    = True
isCanonical (ZFree1 _ v)  = isCanonical v
isCanonical (ZBinding bs) = all (isCanonical . snd) bs
isCanonical _             = False
\end{code}

\texttt{isDefined e} is true when e is obviously well defined
(though it may be too big to compute).
Any canonical value is defined,
but so are some infinite sets like $\nat$:  \texttt{(ZIntSet (Just 0) Nothing)}
When \texttt{isDefined} is false, the term may still be defined.
NOTE: \texttt{isDefined} ignores type correctness.
      E.g. \{1, \{1\}\} is treated as being defined.
\begin{code}
isDefined :: ZExpr -> Bool
isDefined (ZInt _)        = True
isDefined (ZIntSet _ _)   = True
isDefined (ZFSet _)       = True  -- an invariant of the system
isDefined (ZTuple v)      = all isDefined v
isDefined (ZReln _)       = True
isDefined (ZGiven _)      = True
isDefined (ZGivenSet _)   = True
-- could add some toolkit functions here (at least the non-generic ones).
isDefined (ZSetDisplay vs)= all isDefined vs
isDefined (ZSeqDisplay vs)= all isDefined vs
isDefined (ZFree0 _)      = True
isDefined (ZFree1 _ _)    = True   -- Note (1)
isDefined (ZBinding bs)   = all (isDefined . snd) bs
isDefined v               = False


\end{code}
Note 1:
\texttt{ZFree1} terms initially only appear as the body of lambda terms.
The reduction of those lambda terms checks domain membership,
which includes proving definedness.
So any standalone \texttt{ZFree1} term must be defined.

}
\ignore{
\section{Environments}

Used during traversal/evaluation of terms

Environments contain stacks (lists),
with new bound variables being pushed onto the front of the list.

The environment also stores information
about how large the search space is,
and how hard we want to search:
\begin{itemize}
  \item
     \verb"search_space" starts at 1, and is multiplied by the size of
      the type sets as we search inside [ZGenFilt] lists.
  \item
     If \verb"search_space" gets larger than \verb"max_search_space",
      we stop searching (and return a search space error).
  \item
     If we try to generate a finite set larger than \verb"max_set_size", we
      return a setsize error.
\end{itemize}

\begin{code}
type SearchSpace = [(ZVar,Int)]  -- the max number of choices for each var.
type GlobalDefs  = [(ZVar,ZExpr)]

data Env =
    Env{search_space::Integer,
  search_vars::SearchSpace, -- search_space = product of these nums
  max_search_space::Integer,
  max_set_size::Integer,
  global_values::GlobalDefs,
  local_values::[(ZVar,ZExpr)]
  --avoid_variables::VarSet   TODO: add later?
       }
    deriving Show

empty_env :: GlobalDefs -> Env
empty_env gdefs =
    Env{search_space=1,
  search_vars=[],
  max_search_space=100000,
  max_set_size=1000,
  global_values=gdefs,
  local_values=[]
  --avoid_variables=vs
       }

-- an environment for temporary evaluations.
-- Smaller search space, no names defined.
dummy_eval_env = (empty_env []){max_search_space=10000}


set_max_search_space :: Integer -> Env -> Env
set_max_search_space i env = env{max_search_space=i}

set_max_set_size :: Integer -> Env -> Env
set_max_set_size i env = env{max_set_size=i}

envPushLocal :: ZVar -> ZExpr -> Env -> Env
envPushLocal v val env = env{local_values = (v,val) : local_values env}

envPushLocals :: [(ZVar,ZExpr)] -> Env -> Env
envPushLocals vs env = env{local_values = vs ++ local_values env}

envIsLocal  :: Env -> ZVar -> Bool
envIsLocal env v = v `elem` (map fst (local_values env))

-- schema names are undecorated global names whose value is a schema?
-- TODO: check out what the Z standard says.
envIsSchema :: Env -> String -> Bool
envIsSchema env v =
    not (null [0 | (n,ZESchema _) <- global_values env, n==string_to_zvar v])

envLookupLocal :: (Monad m) => ZVar -> Env -> m ZValue
envLookupLocal v env =
    case lookup v (local_values env) of
   Just e  -> return e
   Nothing -> fail ("unknown local variable: " ++ show_zvar v)

envLookupGlobal :: (Monad m) => ZVar -> Env -> m ZValue
envLookupGlobal v env =
    case lookup v (global_values env) of
   Just e  -> return e
   Nothing -> fail ("unknown global variable: " ++ show_zvar v)

envLookupVar :: (Monad m) => ZVar -> Env -> m ZValue
envLookupVar v env =
    case lookup v (local_values env) of
   Just e  -> return e
   Nothing -> case lookup v (global_values env) of
       Just e  -> return e
       Nothing -> fail ("unknown variable: " ++ show_zvar v)

\end{code}

\section{Visitor Classes for Z Terms}

\begin{code}
data ZTerm
    = ZExpr ZExpr
    | ZPred ZPred
    | ZSExpr ZSExpr
    | ZNull
    deriving (Eq,Ord,Show)


-- This class extends monad to have the standard features
-- we expect while evaluating/manipulating Z terms.
-- It supports a standard notion of `environment',
-- which maintains a mapping from names to ZExpr, plus
-- other flags etc.  The environment is extended by the
-- local names as the traversal goes inside binders (like forall).
--
-- TODO: can we build in the notion of uniquify-variables?
--       eg.
-- uniquify_expr env (ZSetComp gf (Just e)) = ZSetComp gf2 (Just e2)
--    where
--    (gf2, env2, sub) = uniquify_gfs env gf
--    e2 = substitute sub env2 (uniquify_expr env2 e)

class (Monad m) => Visitor m where
    -- these methods define what the visitor does!
    visitExpr      :: ZExpr -> m ZExpr
    visitPred      :: ZPred -> m ZPred
    visitSExpr     :: ZSExpr -> m ZSExpr
    visitBranch    :: ZBranch -> m ZBranch
    visitBinder    :: [ZGenFilt] -> ZTerm -> m ([ZGenFilt],ZTerm,Env)
    visitGenFilt   :: ZGenFilt -> m ZGenFilt
    visitTerm      :: ZTerm -> m ZTerm
    -- visitPara ??

    -- Methods for manipulating the environment,
    -- which includes a mapping from names to expressions.
    lookupLocal  :: ZVar -> m ZExpr  -- lookup locals only
    lookupGlobal :: ZVar -> m ZExpr  -- lookup globals only
    lookupVar    :: ZVar -> m ZExpr  -- lookup locals, then globals
    -- methods for pushing local variables.
    pushLocal   :: ZVar -> ZExpr -> m ()
    pushLocals  :: [(ZVar,ZExpr)] -> m ()
    pushGenFilt :: ZGenFilt -> m ()
    pushBinder  :: [ZGenFilt] -> m ()
    currEnv     :: m Env         -- returns the current environment
    setEnv      :: Env -> m ()   -- changes to use the given environment
         -- (It is generally better to use withEnv)
    withEnv     :: Env -> m a -> m a  -- uses the given environment
    localEnv    :: m a -> m a    -- uses the current env then discards it

    ----------------- Default Implementations --------------------
    -- The default visitors just recurse through the term
    -- Instances will override some cases of these, like this:
    --    myvisitExpr (ZVar v) = ...             (special processing)
    --    myvisitExpr e        = traverseExpr e  (handle all other cases)
    visitExpr = traverseExpr
    visitPred = traversePred
    visitSExpr = traverseSExpr
    visitBranch = traverseBranch
    visitBinder = traverseBinder
    visitGenFilt = traverseGenFilt
    visitTerm = traverseTerm

    -- Default environment implementations.
    -- Minimum defs required are: currEnv and setEnv.
    lookupLocal v  = currEnv >>= envLookupLocal v
    lookupGlobal v = currEnv >>= envLookupGlobal v
    lookupVar v    = currEnv >>= envLookupVar v
    pushLocal v t  = currEnv >>= (setEnv . envPushLocal v t)
    pushLocals vs  = currEnv >>= (setEnv . envPushLocals vs)
    pushGenFilt    = pushGFType
    pushBinder     = mapM_ pushGenFilt
    withEnv e m =
      do  origenv <- currEnv
          setEnv e
          res <- m
          setEnv origenv
          return res
    localEnv m = do {env <- currEnv; withEnv env m}


-- auxiliary functions for visitors
pushGFType :: Visitor m => ZGenFilt -> m ()
pushGFType (Evaluate v e t) = pushLocal v t
pushGFType (Choose v t) = pushLocal v t
pushGFType _ = return ()
\end{code}

\subsection{Default Traversal Functions}

The following \verb"traverse*" functions are useful defaults
for visitor methods.  They recurse through Z terms, invoking
the VISITOR methods at each level (NOT the \verb"traverse*" functions!).

This gives an inheritance-like effect, which allows instances of
the Visitor class to define a method M which overrides just the few
cases it is interested in, then call one of these \verb"traverse*" functions
to handle the remaining cases (subterms within those cases will invoke
M, not just \verb"traverse*").  Thus the effective visitor method will be
the fixed-point of traverse overridden by M etc.

The goal of this design is that when the data structures change
(adding/removing/changing cases), then updating the traversal*
functions here should update ALL traversals within Jaza.
(The code that does something specific with the changed cases will
still need updating manually within each traversal, but this is
usually a small fraction of the possible cases).

These default traversal methods extend the environment by
pushing the TYPE expression of each local variable.

WARNING: \texttt{traverseSExpr} currently does nothing.
  This implies that: all schema inclusions are ignored as ZGenFilt lists
  are being processed, which means that inner terms will not
  have the right environment.  This is not a problem once
  all schema expressions have been unfolded.
  This problem will be fixable (if necessary) after typechecking
  is implemented.

\begin{code}
traverseExpr e@(ZVar _) = return e
traverseExpr e@(ZInt _) = return e
traverseExpr e@(ZGiven _) = return e
traverseExpr e@(ZFree0 _) = return e
traverseExpr (ZFree1 n e) =
    do  e2 <- visitExpr e
        return (ZFree1 n e2)
traverseExpr (ZTuple es) =
    do  es2 <- mapM visitExpr es
        return (ZTuple es2)
traverseExpr (ZBinding ves) =
    do  ves2 <- mapM traverseZVarExpr ves
        return (ZBinding ves2)
traverseExpr (ZSetDisplay es) =
    do  es2 <- mapM visitExpr es
        return (ZSetDisplay es2)
traverseExpr (ZSeqDisplay es) =
    do  es2 <- mapM visitExpr es
        return (ZSeqDisplay es2)
traverseExpr e@(ZFSet vals) = return e
traverseExpr e@(ZIntSet lo hi) = return e
traverseExpr (ZGenerator r e) =
    do  e2 <- visitExpr e
        return (ZGenerator r e2)
traverseExpr (ZCross es) =
    do  es2 <- mapM visitExpr es
        return (ZCross es2)
traverseExpr e@(ZFreeType name bs) =
    do  bs2 <- localEnv (pushLocal name e >> mapM visitBranch bs)
        return (ZFreeType name bs2)
traverseExpr e@ZPowerSet{} =
    do  base2 <- visitExpr (baseset e)
        return e{baseset=base2}
traverseExpr e@ZFuncSet{} =
    do  dom2 <- visitExpr (domset e)
        ran2 <- visitExpr (ranset e)
        return e{domset=dom2, ranset=ran2}
traverseExpr (ZSetComp gfs (Just e)) =
    do  (gfs2,ZExpr e2,_) <- visitBinder gfs (ZExpr e)
        return (ZSetComp gfs2 (Just e2))
traverseExpr (ZLambda gfs e) =
    do  (gfs2,ZExpr e2,_) <- visitBinder gfs (ZExpr e)
        return (ZLambda gfs2 e2)
traverseExpr (ZESchema se) =
    do  se2 <- visitSExpr se
        return (ZESchema se2)
traverseExpr e@(ZGivenSet _) = return e
traverseExpr e@ZUniverse = return e
traverseExpr (ZCall f e) =
    do  f2 <- visitExpr f
        e2 <- visitExpr e
        return (ZCall f2 e2)
traverseExpr e@(ZReln rel) = return e
traverseExpr e@(ZFunc1 f)  = return e
traverseExpr e@(ZFunc2 f)  = return e
traverseExpr e@(ZStrange _) = return e
traverseExpr (ZMu gfs (Just e)) =
    do  (gfs2,ZExpr e2,_) <- visitBinder gfs (ZExpr e)
        return (ZMu gfs2 (Just e2))
traverseExpr (ZELet defs e) =
    do  defs2 <- mapM traverseZVarExpr defs
        e2 <- visitExpr e
        return (ZELet defs2 e2)
traverseExpr (ZIf_Then_Else p thn els) =
    do  p2 <- visitPred p
        thn2 <- visitExpr thn
        els2 <- visitExpr els
        return (ZIf_Then_Else p2 thn2 els2)
traverseExpr (ZSelect e v) =
    do  e2 <- visitExpr e
        return (ZSelect e2 v)
traverseExpr (ZTheta se) =
    do  se2 <- visitSExpr se
        return (ZTheta se2)


-- helper functions
traverseZVarExpr (v,e) =
    do  e2 <- visitExpr e
        return (v,e2)


traverseMaybeExpr Nothing =
    return Nothing
traverseMaybeExpr (Just e) =
    do  e2 <- visitExpr e
        return (Just e2)


traversePred e@ZFalse{} = return e
traversePred e@ZTrue{} = return e
traversePred (ZAnd p q) =
  do  p2 <- visitPred p
      q2 <- visitPred q
      return (ZAnd p2 q2)
traversePred (ZOr p q) =
  do  p2 <- visitPred p
      q2 <- visitPred q
      return (ZOr p2 q2)
traversePred (ZImplies p q) =
  do  p2 <- visitPred p
      q2 <- visitPred q
      return (ZImplies p2 q2)
traversePred (ZIff p q) =
  do  p2 <- visitPred p
      q2 <- visitPred q
      return (ZIff p2 q2)
traversePred (ZNot p) =
  do  p2 <- visitPred p
      return (ZNot p2)
traversePred (ZExists gfs p) =
  do  (gfs2,ZPred p2,_) <- visitBinder gfs (ZPred p)
      return (ZExists gfs2 p2)
traversePred (ZExists_1 gfs p) =
  do  (gfs2,ZPred p2,_) <- visitBinder gfs (ZPred p)
      return (ZExists_1 gfs2 p2)
traversePred (ZForall gfs p) =
  do  (gfs2,ZPred p2,_) <- visitBinder gfs (ZPred p)
      return (ZForall gfs2 p2)
traversePred (ZPLet defs p) =
  do  defs2 <- mapM traverseZVarExpr defs
      p2 <- visitPred p
      return (ZPLet defs2 p2)
traversePred (ZEqual p q) =
  do  p2 <- visitExpr p
      q2 <- visitExpr q
      return (ZEqual p2 q2)
traversePred (ZMember p q) =
  do  p2 <- visitExpr p
      q2 <- visitExpr q
      return (ZMember p2 q2)
traversePred (ZPre se) =
  do  se2 <- visitSExpr se
      return (ZPre se2)
traversePred (ZPSchema se) =
  do  se2 <- visitSExpr se
      return (ZPSchema se2)


-- instances should override this.
-- (not necessary if the terms they are visiting have already
--  had all schema expressions unfolded).
traverseSExpr se = fail "traverseSExpr is not implemented"


traverseBranch e@(ZBranch0 _) =
    return e
traverseBranch (ZBranch1 name e) =
  do  e2 <- visitExpr e
      return (ZBranch1 name e2)


-- The default traversal for binders obeys the Jaza (post-unfold)
-- scope rules: the scope of a declared variable starts immediately
-- after the declaration (so includes following declaration types).
traverseGenFilt (Choose v t) =
  do  t2 <- visitExpr t
      pushLocal v t2
      return (Choose v t2)
traverseGenFilt (Check p) =
  do  p2 <- visitPred p
      return (Check p2)
traverseGenFilt (Evaluate v e t) =
  do  e2 <- visitExpr e
      t2 <- visitExpr t
      pushLocal v t2
      return (Evaluate v e2 t2)
traverseGenFilt (Include p) =
    fail "traverseGenFilt should not see schema inclusions"


traverseBinder gfs term =
    localEnv trav2
    where
    trav2 = do gfs2 <- mapM visitGenFilt gfs
               term2 <- visitTerm term
               env <- currEnv
               return (gfs2,term2,env)


traverseTerm (ZExpr e)  = visitExpr e >>= (return . ZExpr)
traverseTerm (ZPred p)  = visitPred p >>= (return . ZPred)
traverseTerm (ZSExpr e) = visitSExpr e >>= (return . ZSExpr)
traverseTerm (ZNull)    = return ZNull
\end{code}


}

\section{Z Paragraphs}
\begin{code}
data ZPara
  = ZGivenSetDecl GivenSet       -- [XXX]
  | ZSchemaDef ZSName ZSExpr     -- \begin{schema}{XXX}...\end{schema}
  -- or XXX \defs [...|...]
  | ZSchemaDefP ZSName [ZVar] ZSExpr     -- XXX[Y] \defs [...|...]
  | ZAbbreviation ZVar ZExpr     -- XXX == expression
  | ZFreeTypeDef ZVar [ZBranch]  -- XXX ::= A | B | ...
  | ZPredicate ZPred
  | ZAxDef [ZGenFilt]            -- \begin{axdef}...\end{axdef}
  | ZGenDef [ZGenFilt]           -- \begin{gendef}...\end{gendef}
  | ZMachineDef{machName::String,   -- a state machine.
    machState::String,
    machInit::String,
    machOps::[String]}
\end{code}

\section{Circus Abstract Syntax}
A \Circus\ specification is a list of paragraphs, $ZPara$. They can be either a channel declaration, a channel set declaration or a process declaration.
\begin{code}
--------------------------------------
-------------   Circus   -------------
--    Artur Oliveira - May 2016     --
--------------------------------------
-- ... from ZPara
  | CircChannel [CDecl]         -- \circchannel CDecl
  | CircChanSet ZName CSExp     -- \circchanset N == CSExp
  | Process ProcDecl            -- ProcDecl
  | Assert String            -- CSP Assertion text
  -- | AssertFDR Assertion            -- CSP Assertion text
  deriving (Eq,Ord,Show)

-- From and based on https://github.com/tomgr/libcspm/blob/master/src/CSPM/Syntax/AST.hs
  -- data Assertion =
  --     -- | A refinement assertion, e.g. @assert P [F= Q@.
  --     Refinement {
  --         refinementSpecification :: CAction,
  --         refinementModel :: Model,
  --         refinementImplementation :: CAction,
  --     }
  --     -- | A check of property, like deadlock freedom, e.g.
  --     -- @assert P :[deadlock free [F]]@.
  --     | PropertyCheck {
  --         propertyCheckProcess :: CAction,
  --         propertyCheckProperty :: SemanticProperty ,
  --         propertyCheckModel :: Maybe Model,
  --     }
  --     deriving (Eq, Ord, Show)
  --
  -- data Model =
  --     Traces
  --     | Failures
  --     | FailuresDivergences
  --     | Refusals
  --     | RefusalsDivergences
  --     | Revivals
  --     | RevivalsDivergences
  --     deriving (Eq, Ord, Show)
  --
  -- data SemanticProperty =
  --   DeadlockFreedom
  --   | Deterministic
  --   | LivelockFreedom
  --   deriving (Eq, Ord, Show)

type CProgram = [ZPara]
\end{code}

\subsection{\Circus\ Channel Declaration -- $CDecl$}
\begin{code}

data CDecl
  = CChan ZName                             --  no type is defined
  | CChanDecl ZName ZExpr                   -- channel_name : type
  | CGenChanDecl ZName ZName ZExpr          -- generic chan decl
  deriving (Eq,Ord,Show)
\end{code}

Channel Schema, $SchemaExp$, declaration is left out for now, but
one could declare it as:

\begin{schema}{SchExpr}
\circchannel c1:\nat \\
\circchannel c2:\nat \\
\end{schema}

and therefore, would need to define it in terms of the Z parser.


\subsection{\Circus\ Channel Expression -- $CSExp$}
\begin{code}
data CSExp
  = CSExpr ZName                           -- a chanset decl from another chanset
  | CSEmpty                                -- Empty chanset
  | CChanSet [ZName]                       -- named chanset
  | ChanSetUnion CSExp CSExp               -- chanset union
  | ChanSetInter CSExp CSExp               -- chanset intersection
  | ChanSetDiff CSExp CSExp                -- chanset hidding chanset
  deriving (Eq,Ord,Show)

\end{code}

\subsection{\Circus\ Process -- $ProcDecl$}
\begin{code}
data ProcDecl
  = CProcess ZName ProcessDef              -- \circprocess N \circdef ProcDef
  | CParamProcess ZName [ZName] ProcessDef  -- \circprocess N[N^{+}] \circdef ProcDef
  | CGenProcess ZName [ZName] ProcessDef   -- \circprocess N[N^{+}] \circdef ProcDef
  deriving (Eq,Ord,Show)

\end{code}

\subsection{\Circus\ Process -- $ProcessDef$}
\begin{code}
data ProcessDef
  = ProcDefSpot [ZGenFilt] ProcessDef      -- Decl \circspot ProcDef
  | ProcDefIndex [ZGenFilt] ProcessDef     -- Decl \circindex ProcDef
  | ProcDef CProc                          -- Proc
  deriving (Eq,Ord,Show)

\end{code}

\subsection{\Circus\ Process -- $CProc$}
\begin{code}
data CProc
  = CRepSeqProc [ZGenFilt] CProc           -- \Semi Decl \circspot Proc
  | CRepExtChProc [ZGenFilt] CProc         -- \Extchoice Decl \circspot Proc
  | CRepIntChProc [ZGenFilt] CProc         -- \IntChoice Decl \circspot Proc
  | CRepParalProc CSExp [ZGenFilt] CProc   -- \lpar CSExp \rpar Decl \circspot Proc
  | CRepInterlProc [ZGenFilt] CProc        -- \Interleave Decl \circspot Proc
  | CHide CProc CSExp                      -- Proc \circhide CSExp
  | CExtChoice CProc CProc                 -- Proc \extchoice Proc
  | CIntChoice CProc CProc                 -- Proc \intchoice Proc
  | CParParal CSExp CProc CProc            -- Proc \lpar CSExp \rpar Proc
  | CInterleave CProc CProc                -- Proc \interleave Proc
  -- | ChanProcDecl CDecl ProcessDef [ZExpr]  -- (Decl \circspot ProcDef)(Exp^{+})
  | CGenProc ZName [ZExpr]                 -- N[Exp^{+}]
  | CParamProc ZName [ZExpr]              -- N(Exp^{+})
  -- | CIndexProc [ZGenFilt] ProcessDef    -- \(Decl \circindex ProcDef) \lcircindex Exp^{+} \rcircindex  -- TODO
  | CProcRename CProc [Comm] [Comm]        -- Proc[N^{+}:=N^{+}] -- TODO
  | CSeq CProc CProc                       -- Proc \cirCSeq Proc
  | CSimpIndexProc ZName [ZExpr]           -- N\lcircindex Exp^{+} \rcircindex
  | CircusProc ZName                       -- N
  | ProcMain ZPara [PPar] CAction          -- \circbegin PPar*
                                           --   \circstate SchemaExp PPar*
                                           --   \circspot Action
                                           --   \circend
  | ProcStalessMain [PPar] CAction         -- \circbegin PPar*
                                           --   \circspot Action
                                           --   \circend
 deriving (Eq,Ord,Show)
\end{code}

\subsection{\Circus\ Name-Sets}

\begin{code}
data NSExp
  = NSExpEmpty                             -- \{\}
  | NSExprMult [ZVar]                     -- \{N^{+}\}
  | NSExprSngl ZName                       -- N
  | NSExprParam ZName [ZExpr]              -- N(Exp)
  | NSUnion NSExp NSExp                    -- NSExp \union NSExp
  | NSIntersect NSExp NSExp                -- NSExp \intersect NSExp
  | NSHide NSExp NSExp                     -- NSExp \circhide \NSExp
  | NSBigUnion ZExpr
  deriving (Eq,Ord,Show)
\end{code}

\subsection{Process paragraphs -- $PPar$}
\begin{code}
data PPar
 = ProcZPara ZPara                         -- Par
 | CParAction ZName ParAction              -- N \circdef ParAction
 | CNameSet ZName [ZExpr]                    -- \circnameset N == NSExp
 deriving (Eq,Ord,Show)
\end{code}
\subsection{Parametrised Actions -- $ParAction$}
\begin{code}

data ParAction
 = CircusAction CAction                                 -- Action
 | ParamActionDecl [ZGenFilt] ParAction    -- Decl \circspot ParAction
 deriving (Eq,Ord,Show)
\end{code}
\subsection{\Circus\ Actions -- $CAction$}
\begin{code}
data CAction
 = CActionSchemaExpr ZSExpr               -- \lschexpract S \rschexpract
 | CActionCommand CCommand
 | CActionName ZName
 | CSPSkip | CSPStop | CSPChaos
 | CSPCommAction Comm CAction             -- Comm \then Action
 | CSPGuard ZPred CAction                 -- Pred \circguard Action
 | CSPSeq CAction CAction                 -- Action \circseq Action
 | CSPExtChoice CAction CAction           -- Action \extchoice Action
 | CSPIntChoice CAction CAction           -- Action \intchoice Action
 | CSPNSParal [ZExpr] CSExp [ZExpr] CAction CAction -- Action \lpar NSExp | CSExp | NSExp \rpar Action
 | CSPParal CSExp CAction CAction         -- Action \lpar CSExp \rpar Action
 | CSPNSInter [ZExpr] [ZExpr] CAction CAction -- Action \linter NSExp | NSExp \rinter Action
 | CSPInterleave CAction CAction          -- Action \interleave Action
 | CSPHide CAction CSExp                  -- Action \circhide CSExp
 | CSPParAction ZName [ZExpr]             -- Action(Exp^{+})
 | CSPRenAction ZName CReplace            -- Action[x/y,z/n]
 | CSPRecursion ZName CAction             -- \circmu N \circspot Action
 | CSPUnfAction ZName CAction             -- N (Action)
 | CSPUnParAction [ZGenFilt] CAction [ZExpr]     -- (Decl \circspot Action) (ZName)
 | CSPRepSeq [ZGenFilt] CAction           -- \Semi Decl \circspot Action
 | CSPRepExtChoice [ZGenFilt] CAction     -- \Extchoice Decl \circspot Action
 | CSPRepIntChoice [ZGenFilt] CAction     -- \IntChoice Decl \circspot Action
 | CSPRepParalNS CSExp [ZGenFilt] [ZExpr] CAction -- \lpar CSExp \rpar Decl \circspot \lpar NSExp \rpar Action
 | CSPRepParal CSExp [ZGenFilt] CAction   -- \lpar CSExp \rpar Decl \circspot Action
 | CSPRepInterlNS [ZGenFilt] [ZExpr] CAction  -- \Interleave Decl \circspot \linter NSExp \rinter Action
 | CSPRepInterl [ZGenFilt] CAction        -- \Interleave Decl \circspot  Action
  deriving (Eq,Ord,Show)
\end{code}

\subsection{\Circus\ Communication}

\begin{code}
data Comm
  = ChanComm ZName [CParameter]           -- N CParameter*
  | ChanGenComm ZName [ZExpr] [CParameter]-- N [Exp^{+}] CParameter *
  deriving (Eq,Ord,Show)
\end{code}

\subsection{\Circus\ Communication -- $CParameter$ }
\begin{code}
data CParameter
   = ChanInp ZName                        -- ?N
   | ChanInpPred ZName ZPred              -- ?N : Pred
   | ChanOutExp ZExpr                     -- !Exp
   | ChanDotExp ZExpr                     -- .Exp
   deriving (Eq,Ord,Show)
\end{code}

\subsection{\Circus\ Commands -- $CCommand$}

\begin{code}
data CCommand
  = CAssign [ZVar] [ZExpr]                -- N^{+} := Exp^{+}
  | CIf CGActions                         -- \circif GActions \cirfi
  | CVarDecl [ZGenFilt] CAction           -- \circvar Decl \circspot Action
  | CValDecl [ZGenFilt] CAction           -- \circval Decl \circspot Action
  | CResDecl [ZGenFilt] CAction           -- \circres Decl \circspot Action
  | CVResDecl [ZGenFilt] CAction          -- \circvres Decl \circspot Action
  | CAssumpt [ZName] ZPred ZPred          -- N^{+} \prefixcolon [Pred,Pred]
  | CAssumpt1 [ZName] ZPred               -- N^{+} \prefixcolon [Pred]
  | CPrefix ZPred ZPred                   -- \prefixcolon [Pred,Pred]
  | CPrefix1 ZPred                        -- \prefixcolon [Pred]
  | CommandBrace ZPred                    -- \{Pred\}
  | CommandBracket ZPred                  -- [Pred]
  deriving (Eq,Ord,Show)
\end{code}

\subsection{\Circus\ Guards -- $CGActions$}

\begin{code}

data CGActions
 = CircGAction ZPred CAction                 -- Pred \circthen Action
 | CircThenElse CGActions CGActions    -- CGActions \circelse GActions
 -- | CircElse ParAction    -- \circelse CAction
 deriving (Eq,Ord,Show)
\end{code}

\subsection{Circus Renaming -- $CReplace$}

\begin{code}

data CReplace
  = CRename [ZVar] [ZVar]        -- A[yi / xi] = CRename (ZVar xi []) (ZVar yi [])
  | CRenameAssign [ZVar] [ZVar]  -- A[yi := xi] = CRenameAssign (ZVar xi []) (ZVar yi [])
  deriving (Eq,Ord,Show)
\end{code}
