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
          bf <- batchFDR4 "mem_alarm.csp" assertions
          writeFile "ref_raw1.txt" (uwl $ makeRefMatrix1 bf)
          -- writeFile "ref_matrix.txt" (makeRefMatrix bf)
          -- writeFile "ref_latex.txt" (makeRefTabLatex bf)
          print bf
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

parseAssert2 a f = makeRAssert1 a $ map words $ drop 2 $ lines f
parseAssert a t f =  makeRAssert a t <$> map words . drop 2 . lines  <$>  readFile f
parseAssert1 a f =  makeRAssert1 a <$> map words . drop 2 . lines  <$>  readFile f
-- parseAssert file = map words . drop 2 . lines  <$> readFile file
-- [a, b, c, d, e, f, g]
-- [["CF2",":[divergence","free]:"],
--   ["Log:"],
--   ["Result:","Passed"],
--   ["Visited","States:","2,m4m28"],
--   ["Visited","Transitions:","3,967"],
--   ["Visited","Plys:","69"],
--   ["Estimated","Total","Storage:","m268MB"]]
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

makeRAssert1 (Refinement FailDiv a b) (_:_:c:xs) = return [a, b,head(drop 1 c)]
makeRAssert1 _ _= return []
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

-- Print the current directory structure with files
fdr4 spec ass =
  do copyFile spec "temp.txt";
     appendFile "temp.txt" (makeRefAssert' ass);
     start1 <- getCPUTime;
     (_, Just hout, _, ph) <- createProcess (proc "bash" ["-c", "refines temp.txt -q -f plain"]){ std_out = CreatePipe };
     end1 <- (waitForProcess ph >> getCPUTime);
     grepBytes <- hGetContents hout;
     -- writeFile "tmp.txt" grepBytes;
     -- copyFile "tmp.txt" "tmp1.txt";
     let diff = (fromIntegral (end1 - start1)) / (10^12);
     -- aa <- parseAssert ass (show diff) "tmp1.txt";
     let aa = (unlines $ map unwords (parseAssert2 ass grepBytes));
     -- let bb = words aa;
     -- aa <- parseAssert "tmp1.txt";
     -- appendFile "ref_raw.txt" aa
     cc <- (parseAssert2 ass grepBytes)
     return cc;

batchFDR4 spec xs
  = do
     dd <- (mapM (fdr4 spec) (batchAssertions xs))
     -- let cc = ((map putToTuple $ concat dd));
     appendFile "ref_raw.txt" (uwl dd)
     return (unlines $ map unwords dd)

-- makeRefMatrix1 f :: IO String -> IO [[String]]
makeRefMatrix1 f = (makeRefMatrix (map makeTuple (wl f)))
makeRefMatrix12 f = map makeTuple $ wl f

-- makeTuple :: [[String]] -> [([String],[String],[String])]
makeTuple :: [String] -> [(String, String, String)]
makeTuple (a:b:c:_) = [(a,b,c)]

wl f = map words $ lines f
uwl f = unlines $ map unwords f
-- getA :: (String,String,String) -> String
getA (a,b,c) = a
-- getB :: (String,String,String) -> String
getB (a,b,c) = b
-- getC :: (String,String,String) -> String
getC (a,b,c) = c
--
-- memRef :: [[(String, String, String, String)]]
-- makeRefMatrix :: [[(String,String,String)]] -> String
-- uwlmf f = uwl $ makeRefMatrix1 f
makeRefMatrix (x:xs)
  = return (concat ((headM++(concat(map makeRefMatrixB (x:xs))))))
    where
      headM = makeRefMatrixHead x

-- makeRefMatrixHead :: [(String,String,String)] -> String
makeRefMatrixHead' xs = concat (makeRefMatrixHead xs)
makeRefMatrixHead [] =  []
makeRefMatrixHead xs =  [" ,"]:(makeRefMatrixHead1 xs)
makeRefMatrixHead1 [] =  []
makeRefMatrixHead1 (x:xs) =  [(getB x)++","]:(makeRefMatrixHead1 xs)

-- makeRefMatrixB :: [(String,String,String)] -> String
-- makeRefMatrixB [] =  [""]
makeRefMatrixB' xs =  concat(makeRefMatrixB xs)
makeRefMatrixB (x:xs) =  [((getA x)++", ")]:(makeRefMatrixB1 (x:xs))
makeRefMatrixB1 [] = []
makeRefMatrixB1 (x:xs) = [((getC x)++", ")]:(makeRefMatrixB1 xs)

-- makeRefTabLatex :: [[(String,String,String)]] -> String
makeRefTabLatex (x:xs)
  = return (("\\begin{tabular}{")
              ++(makeRefTabLatexSetting (length x) "l" "r")
              ++("}\\toprule\n")
              ++( (makeRefTabLatexHead x))
              ++("\\\\ \\midrule\n")
              ++(concat (map makeRefTabLatexB (x:xs)))
              ++("\\bottomrule\\end{tabular}\n"))

-- makeRefTabLatexSetting :: Int -> String -> String -> String
makeRefTabLatexSetting 0 _ _= ""
makeRefTabLatexSetting x b c= b++"|"++c++(makeRefTabLatexSetting1 (x-1) c)
makeRefTabLatexSetting1 0 _ = ""
makeRefTabLatexSetting1 x c = "|"++c++(makeRefTabLatexSetting1 (x-1) c)

-- makeRefTabLatexHead :: [(String,String,String)] -> String
makeRefTabLatexHead [] =  ""
makeRefTabLatexHead xs =  ("\n &"++(sepBy " & " (map getB xs)))

-- makeRefTabLatexB :: [(String,String,String)] -> String
makeRefTabLatexB [] =  ""
makeRefTabLatexB xs =  ("\\\\\n"++(getA (head xs))++" & "++(sepBy " & " $ map getC xs))



sepBy _ [] = []
sepBy _ [x] = x
sepBy s (x:xs) = x++s++(sepBy s xs)
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
