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
  let hs = unlines $ stripNonCode $ ([open]++(lines lhs)++[close])
  hPutStrLn stdout hs

stripNonCode [] = []
stripNonCode (ln:lns)
  | trim ln == "\\begin{code}"  =  close : copyCode lns
  | otherwise                   =  ln : stripNonCode lns

copyCode [] = []
copyCode (ln:lns)
  | trim ln == "\\end{code}"  =  open : stripNonCode lns
  | otherwise                 =  ln : copyCode lns

trim = reverse . ltrim . reverse . ltrim
ltrim = dropWhile isSpace

spacer = "\n--\n"
open = "{-\n"

close = "-}\n"
