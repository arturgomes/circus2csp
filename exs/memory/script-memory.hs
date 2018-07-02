import System.IO
import Control.Applicative
import System.Process
import System.Directory
import Data.List
import Data.Word
import System.CPUTime

-- import System.IO (readFile)
import Control.Applicative ((<$>))
import Data.Maybe (isJust, fromJust)
-- import Data.List (sortBy)
import Data.Function (on)

main = do writeFile "result.txt" ""
          batchFDR4 "mem_alarm.csp" assertions





data RefModel = FailDiv
              | Fail
              | Traces
              deriving Show

getRefModel FailDiv = " [FD= "
getRefModel Fail = " [F= "
getRefModel Traces = " [T= "

getSemanticModel FailDiv = "[FD]"
getSemanticModel Fail = "[F]"
getSemanticModel Traces = "[T]"

data Assertion = Refinement RefModel String String
               | Livelock String (Maybe RefModel)
               | Deadlock String (Maybe RefModel)
               | Divergence String (Maybe RefModel)
               | Deterministic String (Maybe RefModel)
               deriving Show

-- We first generate all possible assertion checks

-- for each possible assertion, we can have:
getAssertion (Refinement rm m1 m2)
  = m1 ++ (getRefModel rm) ++ m2
getAssertion (Livelock m1 (Just r))
  = m1 ++ " :[livelock free "++(getSemanticModel r)++"]"
getAssertion (Livelock m1 Nothing)
  = m1 ++ " :[livelock free]"
getAssertion (Deadlock m1 (Just r))
  = m1 ++ " :[deadlock free "++(getSemanticModel r)++"]"
getAssertion (Deadlock m1 (Nothing))
  = m1 ++ " :[deadlock free]"
getAssertion (Divergence m1 (Just r))
  = m1 ++ " :[divergence free "++(getSemanticModel r)++"]"
getAssertion (Divergence m1 (Nothing))
  = m1 ++ " :[divergence free]"
getAssertion (Deterministic m1 (Just r))
  = m1 ++ " :[deterministic "++(getSemanticModel r)++"]"
getAssertion (Deterministic m1 (Nothing))
  = m1 ++ " :[deterministic]"

-- then we can make a batch for all assertions combining models

batchAssertions xs
  = (makeRefinements xs xs)

batchAssertions1 xs
  = (makeLivelocks xs)
  ++(makeDeadlocks xs)
  ++(makeDivergences xs)
  ++(makeDeterministic xs)

makeRefinements [] _ = []
makeRefinements (x:xs) ys
  = (makeRefs x ys)++(makeRefinements xs ys)
makeRefs x [] = []
makeRefs x (y:ys) = [Refinement FailDiv x y]++(makeRefs x ys)
makeLivelocks [] = []
makeLivelocks (x:xs)
  = (makeLiv x)++(makeLivelocks xs)
makeLiv x
  -- = [Livelock x Nothing, Livelock x (Just FailDiv), Livelock x (Just Fail), Livelock x (Just Traces)]
  = [Livelock x Nothing]
makeDeadlocks [] = []
makeDeadlocks (x:xs)
  = (makeDead x)++(makeDeadlocks xs)
makeDead x
  -- = [Deadlock x Nothing, Deadlock x (Just FailDiv), Deadlock x (Just Fail), Deadlock x (Just Traces)]
  = [Deadlock x Nothing]
makeDivergences [] = []
makeDivergences (x:xs)
  = (makeDiv x)++(makeDivergences xs)
makeDiv x
  -- = [Divergence x Nothing, Divergence x (Just FailDiv), Divergence x (Just Fail), Divergence x (Just Traces)]
  = [Divergence x Nothing]
makeDeterministic [] = []
makeDeterministic (x:xs)
  = (makeDeterm x)++(makeDeterministic xs)
makeDeterm x
  -- = [Deterministic x Nothing, Deterministic x (Just FailDiv), Deterministic x (Just Fail), Deterministic x (Just Traces)]
  = [Deterministic x Nothing]

-- batch create the assertions
makeRefAssert xs = map makeRefAssert' xs
makeRefAssert' x = "assert "++(getAssertion x)

-- (batchAssertions xs)

{-
Parsing results from assertions
-}

-- parseAssert f = map words . drop 2 . lines  <$>  readFile f
parseAssert a t f =  makeRAssert a t <$> map words . drop 2 . lines  <$>  readFile f
parseAssert1 a t f =  makeRAssert1 a t <$> map words . drop 2 . lines  <$>  readFile f
-- parseAssert file = map words . drop 2 . lines  <$> readFile file
-- [a, b, c, d, e, f, g]
-- [["CF2",":[divergence","free]:"],
--   ["Log:"],
--   ["Result:","Passed"],
--   ["Visited","States:","2,428"],
--   ["Visited","Transitions:","3,967"],
--   ["Visited","Plys:","69"],
--   ["Estimated","Total","Storage:","268MB"]]
makeRAssert a t [_, _, c, d, e, f, g]
        = Just $ ResAssertion{assertion=a,
                              result=(concat $ drop 1 c),
                              sv=(concat $ drop 2 d),
                              tv=(concat $ drop 2 e),
                              pv=(concat $ drop 2 f),
                              timeEx=t}
makeRAssert a t [_, _, c, d, e, f, g,_,_,_,_,_,_,_,_]
        = Just $ ResAssertion{assertion=a,
                              result=(concat $ drop 1 c),
                              sv=(concat $ drop 2 d),
                              tv=(concat $ drop 2 e),
                              pv=(concat $ drop 2 f),
                              timeEx=t}
makeRAssert _ _ _= Nothing

makeRAssert1 (Refinement FailDiv a b) t (_:_:c:xs) = [a, b, (concat $ drop 1 c), t]
makeRAssert1 (Refinement FailDiv a b) t (_:_:c:xs) = [a, b,(concat $ drop 1 c), t]
makeRAssert1 _ _ _= []
--

data Res = Failed | Passed  deriving Show
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

updateFile fileName update = do
    handle <- openFile fileName ReadMode;
    contents <- hGetContents handle;
    hClose handle;
    writeFile fileName $ update contents;

-- Print the current directory structure with files
fdr4 spec ass =
  do copyFile spec "temp.txt"
     appendFile "temp.txt" (makeRefAssert' ass)
     start1 <- getCPUTime
     (_, Just hout, _, ph) <- createProcess (proc "bash" ["-c", "refines temp.txt -q -f plain"]){ std_out = CreatePipe }
     end1 <- (waitForProcess ph >> getCPUTime)
     grepBytes <- hGetContents hout;
     writeFile "tmp.txt" grepBytes;
     copyFile "tmp.txt" "tmp1.txt"
     let diff = (fromIntegral (end1 - start1)) / (10^12)
     -- aa <- parseAssert ass (show diff) "tmp1.txt";
     aa <- parseAssert1 ass (show diff) "tmp1.txt";
     appendFile "result.txt" ((show aa)++"\n");

factorParseAssert (Just x) = (show x)++"\n"
factorParseAssert Nothing = ""
--
batchFDR4 spec xs
  = mapM (fdr4 spec) (batchAssertions xs)

{-
Here's the main content with the
assertions from the Memory models
of the Chronometer and Alarm models
(from my thesis and Oliveira's thesis)
-}

assertions = ["CF2","CF3","CF4",
              "HAC2","HAC3","HAC4",
              "HC2","HC3","HC4",
              "HWU2","HWU3","HWU4",
              "HWUok2","HWUok3","HWUok4",
              "M2","M3","M4",
              "S2","S3","S4",
              "CF2a","CF3a","CF4a",
              "HAC2a","HAC3a","HAC4a",
              "HC2a","HC3a","HC4a",
              "HWU2a","HWU3a","HWU4a",
              "HWUok2a","HWUok3a","HWUok4a",
              "M2a","M3a","M4a",
              "S2a","S3a","S4a"]
