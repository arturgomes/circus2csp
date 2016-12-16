module CRL
where
import AST
-- import DefSets
-- import Data.List
-- import Data.Maybe
getFV :: t -> [t1]
getFV xs = []

getWrtV :: t -> [t1]
getWrtV xs = []

crl_var_exp_par2 :: CAction -> CAction
crl_var_exp_par2 (CSPNSParal ns1 cs ns2
                  (CActionCommand (CVarDecl d1 a1))
                  (CActionCommand (CVarDecl d2 a2)))
  = case (d1 == d2) of
      True  -> (CActionCommand (CVarDecl d1
                      (CSPNSParal ns1 cs ns2 a1 a2)))
      False -> (CSPNSParal ns1 cs ns2
                      (CActionCommand (CVarDecl d1 a1))
                      (CActionCommand (CVarDecl d2 a2)))

crl_variableBlockIntroduction :: CAction -> ZVar -> ZExpr -> CAction
crl_variableBlockIntroduction a x t
  = case p1 of
      True -> CActionCommand (CVarDecl [(Choose x t)] a)
      False -> a
    where
      p1 = not (elem x (getFV a))

crl_seqSkipUnit_a :: CAction -> CAction
crl_seqSkipUnit_a (CSPSeq CSPSkip a) = a

crl_seqSkipUnit_b :: CAction -> CAction
crl_seqSkipUnit_b a = (CSPSeq a CSPSkip)

crl_parallelismExternalChoiceExpansion :: CAction -> Comm -> CAction -> CAction
crl_parallelismExternalChoiceExpansion
  (CSPNSParal ns1 cs ns2
      (CSPRepExtChoice i (CSPCommAction ai aAi))
      (CSPRepExtChoice j (CSPCommAction bj aBj))) c aC
  = (CSPNSParal ns1 cs ns2
      (CSPRepExtChoice i (CSPCommAction ai aAi))
      (CSPExtChoice (CSPRepExtChoice j
          (CSPCommAction bj aBj))
      (CSPCommAction c aC)))


crl_parallelismIntroduction1b :: CAction -> NSExp -> [ZName] -> NSExp -> CActioncrl_parExtChoiceExchange
crl_parallelismIntroduction1b
  (CSPCommAction (ChanComm c
      [ChanDotExp e]) a)
      (NSExprMult ns1) cs (NSExprMult ns2)
  = case p1 && p2 of
      True -> (CSPNSParal (NSExprMult ns1) (CChanSet cs) (NSExprMult ns2)
                (CSPCommAction (ChanComm c [ChanDotExp e]) a)
                (CSPCommAction (ChanComm c [ChanDotExp e]) CSPSkip))
      False -> (CSPCommAction (ChanComm c [ChanDotExp e]) a)
    where
      p1 = not (elem c (usedC a))
      p2 = (subset (getWrtV a) ns1)


crl_parallelismIntroduction1a :: CAction -> NSExp -> [ZName] -> NSExp -> CAction
crl_parallelismIntroduction1a
    (CSPCommAction (ChanComm c e) a)
        (NSExprMult ns1) cs (NSExprMult ns2)
  = case p1 && p2 of
      True -> (CSPNSParal (NSExprMult ns1) (CChanSet cs) (NSExprMult ns2)
                  (CSPCommAction (ChanComm c e) a)
                  (CSPCommAction (ChanComm c e) CSPSkip))
      False -> (CSPCommAction (ChanComm c e) a)
    where
      p1 = elem c (usedC a)
      p2 = (subset (getWrtV a) ns1)


crl_chanExt1 :: CAction -> ZName -> CAction
crl_chanExt1 (CSPNSParal ns1 (CChanSet cs) ns2 a1 a2) c
  = case p1 of
      True -> (CSPNSParal ns1 (ChanSetUnion
                    (CChanSet cs) (CChanSet [c])) ns2 a1 a2)
      False -> (CSPNSParal ns1 (CChanSet cs) ns2 a1 a2)
    where
      p1 = not (elem c ((usedC a1) `union` (usedC a2)))

crl_hidingExpansion2 :: CAction -> ZName -> CAction
crl_hidingExpansion2 (CSPHide a (CChanSet cs)) c
  = case p1 of
      True -> (CSPHide a (ChanSetUnion (CChanSet cs) (CChanSet [c])))
      False -> (CSPHide a (CChanSet cs))
    where
      p1 = not (c `elem` cs)

crl_prefixHiding :: CAction -> CAction
crl_prefixHiding
  (CSPHide (CSPCommAction (ChanComm c []) CSPSkip) (CChanSet [c1]))
  = case (c == c1) of
      True        -> CSPSkip
      otherwise   -> (CSPHide (CSPCommAction (ChanComm c []) CSPSkip)
                        (CChanSet [c1]))
crl_prefixHiding (CSPHide (CSPCommAction
                    (ChanComm c [ChanDotExp e]) CSPSkip)
                    (CChanSet [c1]))
  = case (c == c1) of
      True        -> CSPSkip
      otherwise   -> (CSPHide (CSPCommAction
                        (ChanComm c [ChanDotExp e]) CSPSkip)
                          (CChanSet [c1]))


crl_hidingIdentity :: CAction -> CAction
crl_hidingIdentity (CSPHide a (CChanSet cs))
  = case p1 of
      True -> a
      False -> (CSPHide a (CChanSet cs))
    where
      p1 = null (cs `intersect` (usedC a))


crl_parExtChoiceExchange :: CAction -> CAction
crl_parExtChoiceExchange
    (CSPExtChoice
      (CSPNSParal ns1 cs ns2 a1 a2)
      (CSPNSParal ns11 cs1 ns21 b1 b2))
  = case (ns1 == ns11 && cs1 == cs && ns2 == ns21) of
      True ->  (CSPNSParal ns1 cs ns2
                  (CSPExtChoice a1 b1)
                  (CSPExtChoice a2 b2))
      False -> (CSPExtChoice
                  (CSPNSParal ns1 cs ns2 a1 a2)
                  (CSPNSParal ns11 cs1 ns21 b1 b2))




crl_parallelismExternalChoiceDistribution :: CAction -> CAction
crl_parallelismExternalChoiceDistribution
    (CSPRepExtChoice i (CSPNSParal ns1 (CChanSet cs) ns2 ai a))
  = case p1 && p2 of
      True  -> (CSPNSParal ns1
                  (CChanSet cs) ns2 (CSPRepExtChoice i ai) a)
      False -> (CSPRepExtChoice i (CSPNSParal ns1 (CChanSet cs) ns2 ai a))
    where
      p1 = (subset (initials a) cs)
      p2 = isJust (deterministic a)


crl_extChoiceStopUnit :: CAction -> CAction
crl_extChoiceStopUnit (CSPExtChoice CSPStop a) = a

crl_extChoiceSeqDist :: CAction -> CAction

crl_extChoiceSeqDist (CSPSeq (CSPRepExtChoice i
                        (CSPGuard gi (CSPCommAction ci ai))) b)
  = (CSPRepExtChoice i (CSPSeq
          (CSPGuard gi (CSPCommAction ci ai)) b))


crl_hidingExternalChoiceDistribution :: CAction -> CAction
crl_hidingExternalChoiceDistribution
    (CSPHide (CSPExtChoice a1 a2) (CChanSet cs))
  = case p1 of
      True  -> (CSPExtChoice
                  (CSPHide a1 (CChanSet cs))
                  (CSPHide a2 (CChanSet cs)))
      False -> (CSPHide (CSPExtChoice a1 a2) (CChanSet cs))
    where
      p1 = null ((initials a1 `union` initials a2) `intersect` cs)



crl_parallelismDeadlocked1 :: CAction -> CAction
crl_parallelismDeadlocked1
    (CSPNSParal ns1 (CChanSet cs) ns2
          (CSPCommAction (ChanComm c1 x) a1)
          (CSPCommAction (ChanComm c2 y) a2))
  = case p1 && p2 of
    True -> (CSPNSParal ns1 (CChanSet cs) ns2
              CSPStop
              (CSPCommAction (ChanComm c2 y) a2))
    False -> (CSPNSParal ns1 (CChanSet cs) ns2
              (CSPCommAction (ChanComm c1 x) a1)
              (CSPCommAction (ChanComm c2 y) a2))
    where
      p1 = (c1 == c2)
      p2 = (subset [c1,c2] cs)
crl_parallelismDeadlocked1 (CSPNSParal ns1 (CChanSet cs) ns2
                              CSPStop (CSPCommAction c2 a2))
  = CSPStop


crl_seqStopZero :: CAction -> CAction
crl_seqStopZero (CSPSeq CSPStop a)
  = CSPStop

crl_communicationParallelismDistribution :: CAction -> CAction
crl_communicationParallelismDistribution
    (CSPNSParal ns1 cs ns2
        (CSPCommAction (ChanComm c [ChanOutExp e]) (CActionName a1))
        (CSPCommAction (ChanComm c1 [ChanInp x1])
          (CSPParAction a2 [ZVar (x,[])])))
  = case (c == c1 && x == x1) of
      True  ->  (CSPCommAction (ChanComm c [ChanDotExp e])
                    (CSPNSParal ns1 cs ns2
                          (CActionName a1)
                          (CSPParAction a2 [e])))
      False -> (CSPNSParal ns1 cs ns2
                    (CSPCommAction (ChanComm c [ChanOutExp e])
                      (CActionName a1))
                    (CSPCommAction (ChanComm c1 [ChanInp x1])
                      (CSPParAction a2 [ZVar (x,[])])))


crl_channelExtension3 :: CAction -> ZName -> ZName -> CAction
crl_channelExtension3
      (CSPHide (CSPNSParal ns1 cs1 ns2 a1
                (CSPParAction a2 [e])) cs2) c x
  = (CSPHide (CSPNSParal ns1 cs1 ns2
        (CSPCommAction (ChanComm c [ChanOutExp (e)]) a1)
        (CSPCommAction (ChanComm c [ChanInp x])
          (CSPParAction a2 [ZVar (x,[])]))) cs2)

crl_channelExtension4 :: CAction -> CAction
crl_channelExtension4 (CSPHide (CSPNSParal ns1 (CChanSet cs1) ns2 a1 a2) (CChanSet cs2)) (ChanComm c [ChanOutExp (e)])
  = case p1 && p2
    of
      True -> (CSPHide (CSPNSParal ns1 (CChanSet cs1) ns2 (CSPCommAction (ChanComm c [ChanOutExp (e)]) a1) (CSPCommAction (ChanComm c [ChanOutExp (e)]) a2)) (CChanSet cs2))
      False -> (CSPHide (CSPNSParal ns1 (CChanSet cs1) ns2 a1 a2) (CChanSet cs2))
    where
      p1 = c `elem` cs1
      p2 = c `elem` cs2


crl_promVarState
  (ProcMain
      (ZSchemaDef st (ZSchema exsc))
        [CParAction lact (ParamActionDecl (xt:zvar1) act)]
        (CActionCommand (CValDecl [xt1] mact)))
  = case (xt == xt1) of
      True -> (ProcMain
                (ZSchemaDef st (ZS2 ZSAnd (ZSchema exsc) (ZSchema [xt])))
                [CParAction lact act] mact)
      False -> (ProcMain
                (ZSchemaDef st (ZSchema exsc))
                [CParAction lact
                    (ParamActionDecl (xt:zvar1) act)]
                    (CActionCommand (CValDecl [xt1] mact)))

crl_promVarState2
    (ProcStalessMain
      [CParAction lact (ParamActionDecl (xt1:zvar1) act)]
      (CActionCommand (CValDecl [xt] mact))) st
  = case (xt == xt1) of
      True -> (ProcMain (ZSchemaDef st (ZSchema [xt]))
                [CParAction lact act] mact)
      False -> (ProcStalessMain
                  [CParAction lact (ParamActionDecl (xt1:zvar1) act)]
                  (CActionCommand (CValDecl [xt] mact)))


crl_parallelismUnit1 (CSPNSParal _ _ _ CSPSkip CSPSkip) = CSPSkip


crl_parallInterlEquiv (CSPNSInter ns1 ns2 a1 a2)
  = (CSPNSParal ns1 CSEmpty ns2 a1 a2)
crl_parallInterlEquiv_backwards (CSPNSParal ns1 CSEmpty ns2 a1 a2)
  = (CSPNSInter ns1 ns2 a1 a2)


crl_parSeqStep (CSPNSParal ns1 cs ns2 (CSPSeq a1 a2) a3)
    = (CSPSeq a1 (CSPNSParal ns1 cs ns2 a2 a3))


crl_hidingSequenceDistribution (CSPHide (CSPSeq a1 a2) cs)
    = (CSPSeq (CSPHide a1 cs) (CSPHide a2 cs))


crl_guardSeqAssoc (CSPSeq (CSPGuard g a1) a2) = (CSPGuard g (CSPSeq a1 a2))



crl_inputPrefixParallelismDistribution2
      (CSPCommAction (ChanComm c [ChanInp x])
          (CSPNSParal ns1 cs ns2 a1 a2))
  = (CSPNSParal ns1 cs ns2
      (CSPCommAction (ChanComm c [ChanInp x]) a1)
      a2)


crl_prefixSkip (CSPCommAction (ChanComm c [ChanDotExp x]) a)
  = (CSPSeq (CSPCommAction
              (ChanComm c [ChanDotExp x]) CSPSkip) a)
crl_prefixSkip (CSPCommAction c a)
  = (CSPSeq (CSPCommAction c CSPSkip) a)


crl_prefixParDist (CSPCommAction (ChanComm cc [])
                    (CSPNSParal ns1 cs ns2 a1 a2))
  = (CSPNSParal
      ns1 (ChanSetUnion cs (CChanSet [cc])) ns2
      (CSPCommAction (ChanComm cc []) a1)
      (CSPCommAction (ChanComm cc []) a2))

crl_prefixParDist (CSPCommAction (ChanComm c [ChanDotExp e])
                    (CSPNSParal ns1 cs ns2 a1 a2))
  = (CSPNSParal
      ns1 (ChanSetUnion cs (CChanSet [c])) ns2
      (CSPCommAction (ChanComm c [ChanDotExp e]) a1)
      (CSPCommAction (ChanComm c [ChanDotExp e]) a2))


crl_externalChoiceSequenceDistribution2
      (CSPSeq (CSPExtChoice (CSPGuard g1 a1) (CSPGuard g2 a2)) b)
  = (CSPExtChoice (CSPSeq (CSPGuard g1 a1) b)
                  (CSPSeq (CSPGuard g2 a2) b))




crl_trueGuard (CSPGuard ZTrue{reason=[]} a)
  = a


crl_falseGuard (CSPGuard ZFalse{reason=[]} _)
  = CSPStop


crl_hidingChaos (CSPHide CSPChaos _)
  = CSPChaos


crl_seqChaosZero (CSPSeq CSPChaos _)
  = CSPChaos


crl_parallelismZero (CSPNSParal _ _ _ CSPChaos _)
  = CSPChaos


crl_internalChoiceParallelismDistribution (CSPNSParal ns1 cs ns2 (CSPIntChoice a1 a2) a3)
  = (CSPIntChoice
      (CSPNSParal ns1 cs ns2 a1 a3)
      (CSPNSParal ns1 cs ns2 a2 a3))


--Law 43 (Sequence/Internal choice—distribution)
crl43 (CSPSeq a1 (CSPIntChoice a2 a3))
  = (CSPIntChoice
      (CSPSeq a1 a2)
      (CSPSeq a1 a3))


crl_sequenceInternalChoiceDistribution
    (CSPHide (CSPNSParal ns1 cs1 ns2 a1 a2) cs2)
  = (CSPNSParal ns1 cs1 ns2
      (CSPHide a1 cs2)
      (CSPHide a2 cs2))


crl_hidingCombination (CSPHide (CSPHide a cs1) cs2)
  = (CSPHide a (ChanSetUnion cs1 cs2))


crl_parallelismDeadlocked3
  (CSPNSParal ns1 cs ns2
      (CSPRepExtChoice i (CSPCommAction ci ai))
      (CSPRepExtChoice j (CSPCommAction cj aj)))
  = (CSPNSParal ns1 cs ns2 CSPStop
      (CSPRepExtChoice j (CSPCommAction cj aj)))


crl_assignmentRemoval (CSPSeq (CActionCommand (CAssign _ e)) (CSPParAction a _))
  = (CSPParAction a e)




crl_innocuousAssignment (CActionCommand (CAssign [(x1,[])] [ZVar (x2,[])]))
  = case (x1 == x2) of
      True -> CSPSkip
      False -> (CActionCommand (CAssign [(x1,[])] [ZVar (x2,[])]))


crl_variableSubstitution2
    (CValDecl [Include (ZSRef (ZSPlain x) [] [])]
        (CSPParAction a [ZVar (x1,[])])) y
  = (CValDecl [Include (ZSRef (ZSPlain y) [] [])]
        (CSPParAction a [ZVar (y,[])]))



crl_inputPrefixSequenceDistribution
    (CSPSeq (CSPCommAction (ChanComm c [ChanInp x]) a1) a2 )
  = (CSPCommAction (ChanComm c [ChanInp x]) (CSPSeq a1 a2))


crl_inputPrefixHidIdentity
    (CSPSeq (CSPCommAction (ChanComm c [ChanInp x]) a1) a2)
  = (CSPCommAction (ChanComm c [ChanInp x]) (CSPSeq a1 a2))


crl_guardParDist
    (CSPNSParal ns1 cs ns2 (CSPGuard g a1) a2)
  = (CSPGuard g (CSPNSParal ns1 cs ns2 a1 a2))



crl_internalChoiceHidingDistribution
    (CSPHide (CSPIntChoice a1 a2) cs)
  = (CSPIntChoice (CSPHide a1 cs) (CSPHide a2 cs))


crl_assignmentSkip
    (CActionCommand (CValDecl
        [Include (ZSRef (ZSPlain x) [] [])]
        (CActionCommand (CAssign [(x1,[])] [ZVar (e,[])]))))
  = (CActionCommand (CValDecl
        [Include (ZSRef (ZSPlain x) [] [])] CSPSkip))

----Extra from CRL.lhs

usedC :: CAction -> [ZName]y
usedC (CSPCommAction x c) = [getCommName x] ++ usedC c
usedC (CSPGuard _ c) = usedC c
usedC (CSPSeq ca cb) = (usedC ca) ++ (usedC cb)
usedC (CSPExtChoice ca cb) = (usedC ca) ++ (usedC cb)
usedC (CSPIntChoice ca cb) = (usedC ca) ++ (usedC cb)
usedC (CSPNSParal _ _ _ ca cb) = (usedC ca) ++ (usedC cb)
usedC (CSPParal _ ca cb) = (usedC ca) ++ (usedC cb)
usedC (CSPNSInter _ _ ca cb) = (usedC ca) ++ (usedC cb)
usedC (CSPInterleave ca cb) = (usedC ca) ++ (usedC cb)
usedC (CSPHide c _) = usedC c
usedC (CSPRecursion _ c) = usedC c
usedC (CSPRepSeq _ c) = usedC c
usedC (CSPRepExtChoice _ c) = usedC c
usedC (CSPRepIntChoice _ c) = usedC c
usedC (CSPRepParalNS _ _ _ c) = usedC c
usedC (CSPRepParal _ _ c) = usedC c
usedC (CSPRepInterlNS _ _ c) = usedC c
usedC (CSPRepInterl _ c) = usedC c
usedC _ = []

getCommName :: Comm -> ZName
getCommName (ChanComm n _) = n
getCommName (ChanGenComm n _ _) = n

initials :: CAction -> [ZName]
initials (CSPCommAction x c) = [getCommName x]
initials (CSPGuard _ c) = initials c
initials (CSPSeq ca cb) = (initials ca)
initials (CSPExtChoice ca cb) = (initials ca) ++ (initials cb)
initials (CSPIntChoice ca cb) = (initials ca) ++ (initials cb)
initials (CSPNSParal _ _ _ ca cb) = (initials ca) ++ (initials cb)
initials (CSPParal _ ca cb) = (initials ca) ++ (initials cb)
initials (CSPNSInter _ _ ca cb) = (initials ca) ++ (initials cb)
initials (CSPInterleave ca cb) = (initials ca) ++ (initials cb)
initials (CSPHide c _) = initials c
initials (CSPRecursion _ c) = initials c
initials (CSPRepSeq _ c) = initials c
initials (CSPRepExtChoice _ c) = initials c
initials (CSPRepIntChoice _ c) = initials c
initials (CSPRepParalNS _ _ _ c) = initials c
initials (CSPRepParal _ _ c) = initials c
initials (CSPRepInterlNS _ _ c) = initials c
initials (CSPRepInterl _ c) = initials c
initials CSPSkip = ["tick"]
initials _ = [[]]

deterministic :: CAction -> Maybe [Char]
deterministic (CSPCommAction x c) = deterministic c
deterministic (CSPGuard _ c) = deterministic c
deterministic (CSPSeq ca cb) =
  case (da == Nothing)
    && (da == db) of
        false -> Just "Deterministic"
  where
    da = (deterministic ca)
    db = (deterministic cb)

deterministic (CSPExtChoice ca cb) =
  case (da == Nothing)
    && (da == db) of
        false -> Just "Deterministic"
  where
    da = (deterministic ca)
    db = (deterministic cb)

deterministic (CSPIntChoice ca cb) = Nothing
deterministic (CSPNSParal _ _ _ ca cb) = Nothing
deterministic (CSPParal _ ca cb) =  Nothing
deterministic (CSPNSInter _ _ ca cb) =
  case (da == Nothing)
    && (da == db) of
        false -> Just "Deterministic"
  where
    da = (deterministic ca)
    db = (deterministic cb)

deterministic (CSPInterleave ca cb) =
  case (da == Nothing)
    && (da == db) of
        false -> Just "Deterministic"
  where
    da = (deterministic ca)
    db = (deterministic cb)
deterministic (CSPHide c _) = Nothing
deterministic (CSPRecursion _ c) = deterministic c
deterministic (CSPRepSeq _ c) = deterministic c
deterministic (CSPRepExtChoice _ c) = deterministic c
deterministic (CSPRepIntChoice _ c) = Nothing
deterministic (CSPRepParalNS _ _ _ c) = Nothing
deterministic (CSPRepParal _ _ c) = Nothing
deterministic (CSPRepInterlNS _ _ c) = deterministic c
deterministic (CSPRepInterl _ c) = deterministic c
deterministic CSPSkip = Just "Deterministic"
deterministic _ = Just "Undefined"

isDeterministic :: CAction -> [Char]
isDeterministic a
  = case x of
      Just "Deterministic" -> "Deterministic"
      Just x               -> "undefined"
      Nothing              -> "Non-deterministic"
    where x = (deterministic a)

subset xs ys = all (`elem` ys) xs



-- Artur - 15/12/2016
-- What we find below this line was taken from the Data.List module
-- It is hard to import such package with Haskabelle, so I had
-- to put it directly into my code.

-- From Data.List
-- | The '\\' function is list difference ((non-associative).
-- In the result of @xs@ '\\' @ys@, the first occurrence of each element of
-- @ys@ in turn (if any) has been removed from @xs@.  Thus
--
-- > (xs ++ ys) \\ xs == ys.
--
-- It is a special case of 'deleteFirstsBy', which allows the programmer
-- to supply their own equality test.

(\\)                    :: (Eq a) => [a] -> [a] -> [a]
(\\)                    =  foldl (flip delete)


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


flip         :: (a -> b -> c) -> b -> a -> c
flip f x y   =  f y x


-- | The 'union' function returns the list union of the two lists.
-- For example,
--
-- > "dog" `union` "cow" == "dogcw"
--
-- Duplicates, and elements of the first list, are removed from the
-- the second list, but if the first list contains duplicates, so will
-- the result.
-- It is a special case of 'unionBy', which allows the programmer to supply
-- their own equality test.

union                   :: (Eq a) => [a] -> [a] -> [a]
union                   = unionBy (==)

-- | The 'unionBy' function is the non-overloaded version of 'union'.
unionBy                 :: (a -> a -> Bool) -> [a] -> [a] -> [a]
unionBy eq xs ys        =  xs ++ foldl (flip (deleteBy eq)) (nubBy eq ys) xs

-- | The 'intersect' function takes the list intersection of two lists.
-- For example,
--
-- > [1,2,3,4] `intersect` [2,4,6,8] == [2,4]
--
-- If the first list contains duplicates, so will the result.
--
-- > [1,2,2,3,4] `intersect` [6,4,4,2] == [2,2,4]
--
-- It is a special case of 'intersectBy', which allows the programmer to
-- supply their own equality test.

intersect               :: (Eq a) => [a] -> [a] -> [a]
intersect               =  intersectBy (==)

-- | The 'intersectBy' function is the non-overloaded version of 'intersect'.
intersectBy             :: (a -> a -> Bool) -> [a] -> [a] -> [a]
intersectBy eq xs ys    =  [x | x <- xs, any (eq x) ys]

-- | /O(n^2)/. The 'nub' function removes duplicate elements from a list.
-- In particular, it keeps only the first occurrence of each element.
-- (The name 'nub' means \`essence\'.)
-- It is a special case of 'nubBy', which allows the programmer to supply
-- their own equality test.
nub                     :: (Eq a) => [a] -> [a]
-- stolen from HBC
nub l                   = nub' l []             -- '
  where
    nub' [] _           = []                    -- '
    nub' (x:xs) ls                              -- '
        | x `elem` ls   = nub' xs ls            -- '
        | otherwise     = x : nub' xs (x:ls)    -- '


-- | The 'nubBy' function behaves just like 'nub', except it uses a
-- user-supplied equality predicate instead of the overloaded '=='
-- function.
nubBy                   :: (a -> a -> Bool) -> [a] -> [a]
nubBy eq []             =  []
nubBy eq (x:xs)         =  x : nubBy eq (filter (\ y -> not (eq x y)) xs)
-- nubBy eq l              = nubBy' l []
--   where
--     nubBy' [] _         = []
--     nubBy' (y:ys) xs
--        | elem_by eq y xs = nubBy' ys xs
--        | otherwise       = y : nubBy' ys (y:xs)

-- Not exported:
-- Note that we keep the call to `eq` with arguments in the
-- same order as in the reference implementation
-- 'xs' is the list of things we've seen so far, 
-- 'y' is the potential new element
elem_by :: (a -> a -> Bool) -> a -> [a] -> Bool
elem_by _  _ []         =  False
elem_by eq y (x:xs)     =  y `eq` x || elem_by eq y xs


-- | The 'isJust' function returns 'True' iff its argument is of the
-- form @Just _@.
--
-- ==== __Examples__
--
-- Basic usage:
--
-- >>> isJust (Just 3)
-- True
--
-- >>> isJust (Just ())
-- True
--
-- >>> isJust Nothing
-- False
--
-- Only the outer constructor is taken into consideration:
--
-- >>> isJust (Just Nothing)
-- True
--
isJust         :: Maybe a -> Bool
isJust Nothing = False
isJust _       = True