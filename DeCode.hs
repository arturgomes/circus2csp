module Main where
import System.IO
import Data.Char

{-

Compile:
   ghc -o decode DeCode.hs

To use

./decode < AST.lhs > AST.hs

-}
main = do 
  lhs <- hGetContents stdin
  let hs = unlines $ stripNonCode $ lines lhs
  hPutStrLn stdout hs

stripNonCode [] = []
stripNonCode (ln:lns)
  | trim ln == "\\begin{code}"  =  spacer : copyCode lns
  | otherwise                   =  stripNonCode lns

copyCode [] = []
copyCode (ln:lns)
  | trim ln == "\\end{code}"  =  stripNonCode lns
  | otherwise                 =  ln : copyCode lns

trim = reverse . ltrim . reverse . ltrim
ltrim = dropWhile isSpace

spacer = "\n--\n"

