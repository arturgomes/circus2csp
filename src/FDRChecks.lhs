\begin{code}
module FDRChecks where


import System.IO
import Control.Applicative
-- import System.Process
-- import System.Directory
import Data.List
import Data.Word
import System.CPUTime

-- import System.IO (readFile)
import Control.Applicative ((<$>))
import Data.Maybe (isJust, fromJust)
-- import Data.List (sortBy)
import Data.Function (on)

data RefModel = FailDiv
              | Fail
              | Traces
              deriving Show

getRefModel :: RefModel -> [Char]
getRefModel FailDiv = " [FD= "
getRefModel Fail = " [F= "
getRefModel Traces = " [T= "

getSemanticModel :: RefModel -> [Char]
getSemanticModel FailDiv = "[FD]"
getSemanticModel Fail = "[F]"
getSemanticModel Traces = "[T]"

mkSemanticModel :: [Char] -> RefModel
mkSemanticModel "FD" = FailDiv
mkSemanticModel "F" = Fail
mkSemanticModel "T" = Traces

data Assertion = CSPRefinement RefModel String String
               | CSPLivelock String (Maybe RefModel)
               | CSPDeadlock String (Maybe RefModel)
               | CSPDivergence String (Maybe RefModel)
               | CSPDeterministic String (Maybe RefModel)
               deriving Show

-- We first generate all possible assertion checks

-- for each possible assertion, we can have:
getAssertion :: Assertion -> [Char]
getAssertion (CSPRefinement rm m1 m2)
  = m1 ++ (getRefModel rm) ++ m2
getAssertion (CSPLivelock m1 (Just r))
  = m1 ++ " :[livelock free "++(getSemanticModel r)++"]"
getAssertion (CSPLivelock m1 Nothing)
  = m1 ++ " :[livelock free]"
getAssertion (CSPDeadlock m1 (Just r))
  = m1 ++ " :[deadlock free "++(getSemanticModel r)++"]"
getAssertion (CSPDeadlock m1 (Nothing))
  = m1 ++ " :[deadlock free]"
getAssertion (CSPDivergence m1 (Just r))
  = m1 ++ " :[divergence free "++(getSemanticModel r)++"]"
getAssertion (CSPDivergence m1 (Nothing))
  = m1 ++ " :[divergence free]"
getAssertion (CSPDeterministic m1 (Just r))
  = m1 ++ " :[deterministic "++(getSemanticModel r)++"]"
getAssertion (CSPDeterministic m1 (Nothing))
  = m1 ++ " :[deterministic]"

-- then we can make a batch for all assertions combining models

-- CSPRefinement check
batchRef :: [String] -> RefModel -> [Assertion]
batchRef xs ms = (makeCSPRefinements xs xs ms)

makeCSPRefinements :: [String] -> [String] -> RefModel -> [Assertion]
makeCSPRefinements [] _ _ = []
makeCSPRefinements (x:xs) ys a = (makeRefs x ys a)++(makeCSPRefinements xs ys a)

makeRefs :: String -> [String] -> RefModel -> [Assertion]
makeRefs x [] _ = []
makeRefs x (y:ys) ms = [CSPRefinement ms x y]++(makeRefs x ys ms)

-- CSPDeadlock freedom check
batchDL :: [String] -> RefModel -> [Assertion]
batchDL xs ms = (makeCSPDeadlocks xs [ms])

makeCSPDeadlocks :: [String] -> [RefModel] -> [Assertion]
makeCSPDeadlocks [] _= []
makeCSPDeadlocks (x:xs) y = (makeDead x y)++(makeCSPDeadlocks xs y)

makeDead :: String -> [RefModel] -> [Assertion]
makeDead x [] = [CSPDeadlock x Nothing]
  -- = [CSPDeadlock x Nothing, CSPDeadlock x (Just FailDiv), CSPDeadlock x (Just Fail), CSPDeadlock x (Just Traces)]
makeDead x [y] = [CSPDeadlock x (Just y)]
  -- = [CSPDeadlock x Nothing, CSPDeadlock x (Just FailDiv), CSPDeadlock x (Just Fail), CSPDeadlock x (Just Traces)]

-- CSPDivergences check
batchDiv :: [String] -> RefModel -> [Assertion]
batchDiv xs ms = (makeCSPDivergences xs [ms])

makeCSPDivergences :: [String] -> [RefModel] -> [Assertion]
makeCSPDivergences [] y = []
makeCSPDivergences (x:xs) y
  = (makeDiv x y)++(makeCSPDivergences xs y)

makeDiv :: String -> [RefModel] -> [Assertion]
makeDiv x [] = [CSPDivergence x Nothing]
makeDiv x [y] = [CSPDivergence x (Just y)]
  -- = [CSPDivergence x Nothing, CSPDivergence x (Just FailDiv), CSPDivergence x (Just Fail), CSPDivergence x (Just Traces)]

-- CSPDeterministic check
batchDet :: [String] -> RefModel -> [Assertion]
batchDet xs ms = (makeCSPDeterministic xs [ms])

makeCSPDeterministic :: [String] -> [RefModel] -> [Assertion]
makeCSPDeterministic [] _ = []
makeCSPDeterministic (x:xs) y
  = (makeDeterm x y)++(makeCSPDeterministic xs y)

makeDeterm :: String -> [RefModel] -> [Assertion]
makeDeterm x [] = [CSPDeterministic x Nothing]
makeDeterm x [y] = [CSPDeterministic x (Just y)]
  -- = [CSPDeterministic x Nothing, CSPDeterministic x (Just FailDiv), CSPDeterministic x (Just Fail), CSPDeterministic x (Just Traces)]

-- batch create the assertions
makeRefAssert :: [Assertion] -> [[Char]]
makeRefAssert xs = map makeRefAssert' xs

makeRefAssert' :: Assertion -> [Char]
makeRefAssert' x = "assert "++(getAssertion x)

{-
Parsing results from assertions
-}

parseAssert2 :: Monad m => Assertion -> String -> m [String]
parseAssert2 a f = makeRAssert1 a $ map words $ drop 2 $ lines f

parseAssert :: Monad m => Assertion -> String -> FilePath -> IO (m [RAssert])
parseAssert a t f =  makeRAssert a t <$> map words . drop 2 . lines  <$>  readFile f

parseAssert1 :: Monad m => Assertion -> FilePath -> IO (m [String])
parseAssert1 a f =  makeRAssert1 a <$> map words . drop 2 . lines  <$>  readFile f

makeRAssert :: Monad m => Assertion -> String -> [[[Char]]] -> m [RAssert]
makeRAssert a t [_, _, c, d, e, f, g]
        = return [ResAssertion{assertion=a,
                              result=(concat $ drop 1 c),
                              sv=(concat $ drop 2 d),
                              tv=(concat $ drop 2 e),
                              pv=(concat $ drop 2 f),
                              timeEx=t}]
makeRAssert a t [_, _, c, d, e, f, g,_,_,_,_,_,_,_,_]
        = return [ResAssertion{assertion=a,
                              result=(concat $ drop 1 c),
                              sv=(concat $ drop 2 d),
                              tv=(concat $ drop 2 e),
                              pv=(concat $ drop 2 f),
                              timeEx=t}]
makeRAssert _ _ _= return []

makeRAssert1 :: Monad m => Assertion -> [[String]] -> m [String]
makeRAssert1 (CSPRefinement FailDiv a b) (_:_:c:xs) = return [a, b,head(drop 1 c)]
makeRAssert1 _ _= return []

data Res = Failed | Passed  deriving Show

getRes :: [Char] -> Res
getRes "Passed" = Passed
getRes "Failed" = Failed

data RAssert = ResAssertion{assertion::Assertion,
                            result::String,
                            sv::String,
                            tv::String,
                            pv::String,
                            timeEx::String
                          } deriving Show
-- data BatchAssert a = BA a [Assertion] deriving Show

makeRefMatrix1 :: Monad m => String -> m [[Char]]
makeRefMatrix1 f = (makeRefMatrix (map makeTuple (wl f)))
makeRefMatrix12 :: String -> [[(String, String, String)]]
makeRefMatrix12 f = map makeTuple $ wl f

makeTuple :: [String] -> [(String, String, String)]
makeTuple (a:b:c:_) = [(a,b,c)]

wl :: String -> [[String]]
wl f = map words $ lines f
uwl :: [[String]] -> String
uwl f = unlines $ map unwords f

getA :: (String,String,String) -> String
getA (a,b,c) = a
getB :: (String,String,String) -> String
getB (a,b,c) = b
getC :: (String,String,String) -> String
getC (a,b,c) = c

makeRefMatrix (x:xs)
  = return (concat ((headM++(concat(map makeRefMatrixB (x:xs))))))
    where
      headM = makeRefMatrixHead x

makeRefMatrixHead' xs = concat (makeRefMatrixHead xs)
makeRefMatrixHead [] =  []
makeRefMatrixHead xs =  [" ,"]:(makeRefMatrixHead1 xs)
makeRefMatrixHead1 [] =  []
makeRefMatrixHead1 (x:xs) =  [(getB x)++","]:(makeRefMatrixHead1 xs)

makeRefMatrixB' xs =  concat(makeRefMatrixB xs)
makeRefMatrixB (x:xs) =  [((getA x)++", ")]:(makeRefMatrixB1 (x:xs))
makeRefMatrixB1 [] = []
makeRefMatrixB1 (x:xs) = [((getC x)++", ")]:(makeRefMatrixB1 xs)

makeRefTabLatex (x:xs)
  = return (("\\begin{tabular}{")
              ++(makeRefTabLatexSetting (length x) "l" "r")
              ++("}\\toprule\n")
              ++( (makeRefTabLatexHead x))
              ++("\\\\ \\midrule\n")
              ++(concat (map makeRefTabLatexB (x:xs)))
              ++("\\bottomrule\\end{tabular}\n"))

makeRefTabLatexSetting 0 _ _= ""
makeRefTabLatexSetting x b c= b++"|"++c++(makeRefTabLatexSetting1 (x-1) c)
makeRefTabLatexSetting1 0 _ = ""
makeRefTabLatexSetting1 x c = "|"++c++(makeRefTabLatexSetting1 (x-1) c)

makeRefTabLatexHead [] =  ""
makeRefTabLatexHead xs =  ("\n &"++(sepBy " & " (map getB xs)))

makeRefTabLatexB [] =  ""
makeRefTabLatexB xs =  ("\\\\\n"++(getA (head xs))++" & "++(sepBy " & " $ map getC xs))



sepBy _ [] = []
sepBy _ [x] = x
sepBy s (x:xs) = x++s++(sepBy s xs)

-- Old, remove later - 06 Jul 2018
{-
Here's the main content with the
assertions from the Memory models
of the Chronometer and Alarm models
(from my thesis and Oliveira's thesis)
-}
assertions = ["m2CF","m3CF","m4CF",
              "m2aHC","m3aHC","m4aHC" --,
              -- "m2aHWU","m3aHWU","m4aHWU",
              -- "m2aHWUok","m3aHWUok","m4aHWUok"
              -- ,
              -- "m2aM","m3aM","m4aM",
              -- "m2aS","m3aS","m4aS"
              ]

-- assertions = ["m2CF","m3CF","m4CF",
--               "m2HAC","m3HAC","m4HAC",
--               "m2HC","m3HC","m4HC",
--               -- "m2HWU","m3HWU","m4HWU",
--               -- "m2HWUok","m3HWUok","m4HWUok",
--               -- "m2M","m3M","m4M",
--               -- "m2S","m3S","m4S",
--               "m2aCF","m3aCF","m4aCF",
--               "m2aHAC","m3aHAC","m4aHAC",
--               "m2aHC","m3aHC","m4aHC" --,
--               -- "m2aHWU","m3aHWU","m4aHWU",
--               -- "m2aHWUok","m3aHWUok","m4aHWUok"
--               -- ,
--               -- "m2aM","m3aM","m4aM",
--               -- "m2aS","m3aS","m4aS"
--               ]
\end{code}
