\section{Circus Parser UI}

Circus Parser Interface build on based on Jaza UI (TextUI.lhs)

\begin{code}
module Main
-- This module defines a simple textual user interface
-- for the animator.  Call 'main' to start it up, then type 'help'.
where

import AST
import Errors
import Animate
import Data.List
import Data.Char
import Data.Char
import Formatter
import System.IO          -- Standard IO library, so we can catch IO errors etc.
import System.Process
import Control.Exception
import Control.Monad
import System.Directory
import PreVarMappingFunStatelessCircus
import DistMemMappingFunStatelessCircus
import System.Environment
--import System.Console.Readline  -- was Readline

prompt1 = "Circus2CSP> " -- prompt for each command
prompt2 = "      " -- a visible, but cut/pastable, prompt for multiline input

specname = ""
-- These determine how most large output terms are displayed.
pinfo = pinfo_extz 75
output_zexpr = zexpr_stdout pinfo
output_zpred = zpred_stdout pinfo
output_zpara = zpara_stdout pinfo

version = "0.8.2.0"
vdate = "July 2018"

main :: IO ()
main
  = do  putStr "Welcome to Circus2CSP translator, version "
        putStr version
        putStr " "
        putStrLn vdate
        putStrLn "Author: Artur Oliveira Gomes (gomesa at tcd.ie)"
        putStrLn "This is based on JAZA (Just Another Z Animator), see below."
        putStrLn "Copyright(C) 1999-2005 Mark Utting (marku@cs.waikato.ac.nz)."
        putStrLn "Jaza comes with ABSOLUTELY NO WARRANTY (see file COPYING)."
        putStrLn "This is free software, and you are welcome to redistribute"
        putStrLn "it under certain conditions (see file COPYING)."
        putStrLn ""
        putStrLn "Type `help' to see the available commands."
        putStrLn ""
        animGo <- get_config animator0
        putStrLn ("Src. path: "++getSrcDir animGo)
        putStrLn ("Dst. path: "++getDstDir animGo)
        get_cmd animGo ""

get_config anim  = catch (read_config anim)
                         ((\e -> return anim)::(IOException -> IO Animator))

read_config anim
  = do txt <- readFile ".c2c"
       let anim' = parse_configs anim $ lines txt
       return anim'


-- Print the current directory structure with files
printM = do
  txt <- readFile ".c2c"
  mapM_ tl [getSrcDir $ parse_configs animator0 $ lines txt ]

tl p = vs (if "/" `isPrefixOf` p then "" else ".") "" "" "" p

vs p l t a n = do
  putStrLn (l ++ a ++ t ++ n)
  vsc (p ++ "/" ++ n) (l ++ exs)
  where
    exs = case a of ""  -> ""; "`" -> "    "; _   -> "|   "

vsc p l =
  wm (doesDirectoryExist p) $ do
      cn <- getDirectoryContents p
      let vi = sort . filter (`notElem` [".", ".."]) $ cn
          as = replicate (length vi - 1) "|" ++ ["`"]
      zipWithM_ (vs p l "-- ") as vi

wm mtest ma = mtest >>= flip when ma


parse_configs anim [] = anim
parse_configs anim (ln:lns)
  = parse_configs anim' lns
  where
    anim' = case trim ln of
             ('s':'r':'c':':':rest)  ->  setSrcDir anim rest
             ('d':'s':'t':':':rest)  ->  setDstDir anim rest
             _                       ->  anim

trim = reverse . ltrim . reverse . ltrim
ltrim "" = ""
ltrim str@(c:cs)
 | isSpace c  =  ltrim cs
 | otherwise  =  str

get_cmd :: Animator -> String -> IO ()
get_cmd anim fn
  = do  -- TODO: this catch does not work with Hugs.  Find out why.
  s <- catch (getLineEdit prompt1) ((\err -> return "quit")::(IOException -> IO String))
  get_cmd2 (dropWhile isSpace s) anim fn


-- This handles reading any extra lines of input, until a complete
-- command has been read.  It counts opening and closing brackets
-- '([{ ... }])' and keeps reading lines until enough closing
-- brackets have been found.
-- Also, if cmd == a '\begin{...}' construct then reading continues
-- until a similar '\end{...}' is found.
-- It handles empty lines, comments and 'echo' lines itself, but
-- passes other commands to do_cmd.
get_cmd2 :: String -> Animator -> String -> IO ()
get_cmd2 ""       anim fn = get_cmd anim fn -- empty command line
get_cmd2 ('%':_)  anim fn = get_cmd anim fn  -- a comment line
get_cmd2 cmd anim fn
 = get_cmd3 word
    [reverse (dropWhile isSpace (reverse rest))] -- take spaces off end.
    (length(filter openbracket rest) - length(filter closebracket rest))
    anim fn
    where
    (word,rest) = span isAlpha cmd
    endcmd = "\\end{" ++ takeWhile isAlpha (drop (length "\\begin{") cmd)
          ++ "}"

get_cmd3 :: String -> [String] -> Int -> Animator -> String -> IO ()
-- 'sofar' is a list of the input lines for this command (in reverse order).
-- The Int argument is the number of unclosed brackets in 'sofar'.
get_cmd3 cmd sofar opened anim fn
    | opened <= 0
      = do_cmd cmd (dropWhile isSpace (concatMap ('\n':) (reverse sofar))) anim fn
    | otherwise
      = do s <- getLineEdit prompt2
           let opened2 = opened + length (filter openbracket s)
                                - length (filter closebracket s)
           get_cmd3 cmd (s:sofar) opened2 anim fn

openbracket :: Char -> Bool
openbracket '(' = True
openbracket '[' = True
openbracket '{' = True
openbracket  _  = False

closebracket :: Char -> Bool
closebracket ')' = True
closebracket ']' = True
closebracket '}' = True
closebracket  _  = False


help =
  ["Available commands for Circus2CSP:",
   fmtcmd "conv filename"             "'load filename; omega; tocsp'.",
   fmtcmd "convp filename"            "perform conv but with mget_var instead of mget.var",
   fmtcmd "reconv"                    "repeat 'conv' on previous file",
   fmtcmd "reconvp"                   "repeat 'convp' on previous file",
   -- fmtcmd "show"                   "Display a summary of whole spec.",
   -- fmtcmd "orig"                   "Display the whole spec originally loaded.",
   fmtcmd "quit"                      "Exit the animator",
   fmtcmd "load filename"             "Load a Z specification from a file",
   fmtcmd "omega"                     "Apply the Omega function to Circus spec",
   fmtcmd "tocsp"                     "Map the whole spec into CSP.",
   fmtcmd "reload"                    "Re-load Z specification from current file",
   -- fmtcmd "latex"                  "Pretty print into LaTeX.",
   fmtcmd "list"                      "List the files in the current directory.",
   fmtcmd "reset"                     "Reset the whole specification",
   fmtcmd "help"                      "Display this message",
   fmtcmd "refinesT"                  "Run FDR4 in command line mode",
   fmtcmd "% comment"                 "(Ignored)",
   "Available commands for FDR4:",
   "The parameter 'model' where m can be [T,F,FD]",
   fmtcmd "assert ref spec impl"         "assert spec [FD= impl",
   fmtcmd "assert ref spec impl model"   "assert spec [m= impl",
   fmtcmd "assert refall"                 "perform batch refinement for all processes available",
   fmtcmd "assert refall model"           "perform refall using a given model",
   fmtcmd "assert dl spec"             "checks spec for dls",
   fmtcmd "assert dl spec model"       "checks spec for dls using a given model",
   fmtcmd "assert dlall"               "perform batch dl check for all processe available",
   fmtcmd "assert dlall model"         "perform 'dlall' using a given mode",
   fmtcmd "assert div spec"           "checks spec for div",
   fmtcmd "assert div spec model"     "checks spec for div using a given mode",
   fmtcmd "assert divsall"            "perform batch div check for all processe available",
   fmtcmd "assert divsall model"      "perform 'divsall'  using a given model",
   fmtcmd "assert det spec"        "checks if spec is det",
   fmtcmd "assert det spec model " "checks if spec is det using a given model",
   fmtcmd "assert detall"          "perform batch det check for all processe available",
   fmtcmd "assert detall model "   "perform 'detall'  using a given model",
   fmtcmd "assert jumbo"                     "perform all batches available (may take some time)"
  ]


-- This processes each command.
--    Pre: The 'cmd' and 'args' strings must have no whitespace
--         at the start or end of the string.
-- For convenience, the Hugs ":load" command is similar to "quit".
--  (I often forget to get out of the animator before doing a
--   ":load" command while developing the animator in Emacs).

do_cmd :: [Char] -> String -> Animator -> String -> IO ()
do_cmd cmd args anim fn
  | cmd == "quit" =
      return ()
  | cmd == ":q" =
      return ()
  | cmd == ":load" =
      do {putStrLn ("ERROR \"" ++ args
      ++ "\" (Line 1): You did not quit JAZA."
      ++ "\nDo the load again...");
    return ()}
  | cmd == "help" && args =="" =
      do {putStr (unlines help); get_cmd anim fn}
  | cmd == "load"
     = catch
        ( do let fname = getSrcDir anim++args
             putStrLn ("Loading '"++fname++"' ...")
             spec <- readFile (fname++".tex");
             let (anim',_,_) = resetanimator anim
             done_cmd (pushfile args spec $ setFName args anim') )
        (\err ->
            do {putStrLn (show (err :: IOException)); get_cmd anim fn})
  | cmd == "reload"
     = do_cmd "load" (getFName anim) anim fn
  | cmd == "omega" =
      done_cmd (omegaCircus anim fn)
  | cmd == "tocsp" =
      done_cmd (anim, upslonCircus anim fn, fn)
  | cmd == "list" =
      do{printM; get_cmd anim fn}
  | cmd == "conv"
     = catch
        (do let fname = getSrcDir anim++args
            putStrLn ("Loading '"++fname++"' ...")
            spec <- readFile (fname++".tex")
            let (anim',_,_) = resetanimator anim
            let (anim1,answ1,fn1) = pushfile args spec $ setFName args anim'
            let (anim2,answ2,fn2) = omegaCircus anim1 fn1
            done_cmd (anim2, upslonCircus anim2 fn2, fn2))
        (\err ->
            do {putStrLn (show (err :: IOException)); get_cmd anim fn})
  | cmd == "convp"
   = catch
      (do let fname = getSrcDir anim++args
          putStrLn ("Loading '"++fname++"' ...")
          spec <- readFile (fname++".tex")
          let (anim',_,_) = resetanimator anim
          let (anim1,answ1,fn1) = pushfile args spec $ setFName args anim'
          let (anim2,answ2,fn2) = preVarOmegaCircus anim1 fn1
          done_cmd (anim2, prevarupslonCircus anim2 fn2, fn2))
      (\err ->
          do {putStrLn (show (err :: IOException)); get_cmd anim fn})
  | cmd == "refinesT"
       = do  putStrLn     "--------------------------------------------------------------------------------------------------"
             putStrLn ("---------- Running FDR4 using the file '"++"\x1b[32m" ++ (getDstDir anim++args)++(getFName anim)++".csp"++ "\x1b[0m"++"' ...")
             putStrLn "--------------------------------------------------------------------------------------------------"

-- "Welcome to FDR Version 4.2.3 copyright 2016 Oxford University Innovation Ltd. All Rights Reserved."
-- "--------------------------------------------------------------------------------------------------"
             fdr4 ((getDstDir anim++args)++(getFName anim)++".csp")
             putStrLn ("\x1b[32m" ++ "End of the execution of FDR4 ..."++ "\x1b[0m")
             get_cmd anim fn
  | cmd == "reconv"
     = do_cmd "conv" (getFName anim) anim fn
  | cmd == "reconvp"
     = do_cmd "convp" (getFName anim) anim fn
  | cmd == "reset" && args == "" =
      done_cmd (resetanimator anim)
  | cmd == "show" =
      done_cmd (anim, showC,fn)
  | cmd == "original" =
      done_cmd (anim, showO,fn)
  | cmd == "latex" =
      done_cmd (anim, latexCircus anim fn, fn)
  | otherwise =
      do putStrLn "Unknown/illegal command."
         get_cmd anim fn
  where
  -- rd is used to read input values from user
  rd p = getLineEdit ("    Input " ++ p ++ " = ")
  showC = showCircus anim
  showO = showOrigSpec anim


done_cmd :: (Animator, Answer,String) -> IO ()
done_cmd (anim, DoneUpsilon s f,args)
  = cmd_output (anim,s,args,".csp",".csp")
done_cmd (anim, DoneLatex s f,args)
  = cmd_output (anim,s,args,".pretty.tex",".pretty.tex")
done_cmd (anim, DoneOmega s f,args)
  = cmd_output (anim,s,args,".csp",".hc")
done_cmd (anim, Done s,args)
  = cmd_output (anim,s,args,".spec.txt",".spec.txt")
done_cmd (anim, ErrorMsg m,args)   = do {putErrorMsg m; get_cmd anim args}
done_cmd (anim, ErrorLocns es,args)= do {putStrLn (unlines (map fmtperr es));
           get_cmd anim args}

cmd_output :: (Animator, String, String, String, String) -> IO ()
cmd_output (anim,s,args,extt,extw)
  = do putStrLn s
       touch (root++extt)
       writeStr (root++extw) s
       get_cmd anim args
  where
    root = getDstDir anim++args

-- done_cmd :: (Animator, Answer) -> IO ()
-- done_cmd (anim, DoneUpsilon s f)
--   = do {putStrLn s; touch (f++".csp"); writeStr (f++".csp") s; get_cmd anim}
-- done_cmd (anim, DoneOmega s f)
--   = do {putStrLn s; touch (f++".csp"); writeStr (f++".hc") s; get_cmd anim}
-- done_cmd (anim, Done s)
--   = do {putStrLn s; writeFile "spec.txt" s; get_cmd anim}
-- -- done_cmd (anim, Spec s)       = do {putStrLn s; writeFile "spec.txt" s; get_cmd anim}
-- done_cmd (anim, ErrorMsg m)   = do {putErrorMsg m; get_cmd anim}
-- done_cmd (anim, ErrorLocns es)= do {putStrLn (unlines (map fmtperr es));
-- 				    get_cmd anim}


-- Artur
touch :: FilePath -> IO ()
touch name = do
  exists <- doesFileExist name
  unless exists $ appendFile name ""
writeStr :: FilePath -> String -> IO ()
writeStr fp c =
    bracket
      (openFile fp WriteMode)
      hClose
      (\h -> hPutStr h c)



fmtgfs :: (Int,ZGenFilt) -> String
fmtgfs (n,Check ZFalse{reason=(r:rs)}) =
   show n ++ "  " ++ "false  \\because{"
  ++ concat[zpred_string pinfo p ++ "; " | p<- r:rs]
  ++ "}"
fmtgfs (n,gf) =
   show n ++ "  " ++ zgenfilt_string pinfo gf



putErrorMsg :: ErrorMsg -> IO ()
putErrorMsg m =
    do sequence_ (map putMsgPart m)
       putStrLn ""

putMsgPart :: MsgPart -> IO ()
putMsgPart (MStr s)   = putStr s
putMsgPart (MNewLine) = putStrLn ""
putMsgPart (MExpr e)  = output_zexpr e
putMsgPart (MPred p)  = output_zpred p
putMsgPart (MVars vs) = putStr (show_zvars vs)



-- Left justifies a string
ljustify :: Int -> String -> String
ljustify n s = s ++ take (max 0 (n - length s)) (repeat ' ')

-- Formats a parse error.
fmtperr :: SyntaxError -> String
fmtperr (l,c,m)
  = "Error on line " ++ show l ++ ", column " ++ show c ++ ": " ++ m

-- Formats a command help message
fmtcmd :: String -> String -> String
fmtcmd cmd msg = "    " ++ ljustify 24 cmd ++ msg


getLineEdit :: String -> IO String
getLineEdit prompt
  = do putStr prompt
       hFlush stdout   -- needed with GHC.
       getLine
--    do  Just s <- readline prompt
--	if null s
--	   then return ()
--	   else addHistory s
--	return s


\end{code}
%Artur 06 Jul 2018
\subsection{FDR specific code}
$fdr4$ - executes FDR with the assertions already predefined in the file.
\begin{code}
fdr4 spec =
  do (_, Just hout, _, _) <- createProcess (proc "bash" ["-c", "refines "++spec]){ std_out = CreatePipe }
  -- do (_, Just hout, _, _) <- createProcess (proc "bash" ["-c", "refines -qb "++spec]){ std_out = CreatePipe }
     grepBytes <- hGetContents hout
     putStrLn grepBytes
\end{code}
$fdr4check$ perform any specific check provided by the user within Circus2CSP.
\begin{code}

{-

fmtcmd "assert ref spec impl"         "assert spec [FD= impl",
fmtcmd "assert ref spec impl model"   "assert spec [m= impl",
fmtcmd "assert refall"                 "perform batch refinement for all processes available",
fmtcmd "assert refall model"           "perform refall using a given model",
fmtcmd "assert dl spec"             "checks spec for dls",
fmtcmd "assert dl spec model"       "checks spec for dls using a given model",
fmtcmd "assert dlall"               "perform batch dl check for all processe available",
fmtcmd "assert dlall model"         "perform 'dlall' using a given mode",
fmtcmd "assert div spec"           "checks spec for div",
fmtcmd "assert div spec model"     "checks spec for div using a given mode",
fmtcmd "assert divsall"            "perform batch div check for all processe available",
fmtcmd "assert divsall model"      "perform 'divsall'  using a given model",
fmtcmd "assert det spec"        "checks if spec is det",
fmtcmd "assert det spec model " "checks if spec is det using a given model",
fmtcmd "assert detall"          "perform batch det check for all processe available",
fmtcmd "assert detall model "   "perform 'detall'  using a given model",
fmtcmd "assert jumbo"                     "perform all batches available (may take some time)"

-}
assert param xs =
  do_assert (unwords param) xs

do_assert (p:ps) xs
| (p == "ref") && (length ps >= 3) = do_refines ps
| (p == "refall") = do_refinesall xs ps
| (p == "dl") && (length ps > 1) = do_deadlock ps
| (p == "dlall") = do_deadlockall xs ps
| (p == "div") && (length ps >= 1) = do_divergence ps
| (p == "divsall") = do_divergenceall xs ps
| (p == "det") && (length ps >= 1) = do_refines ps
| (p == "detall") = do_deterministicall xs ps
| (p == "ref") && (length ps >= 1) = do_deterministic ps

do_refinesall xs [] = undefined -- refineall
do_refinesall xs [model] = undefined -- refineall model

do_refines [spec,impl] = undefined -- spec [FD= impl
do_refines [spec,impl,model] = undefined -- spec [m= impl

do_deadlockall xs [] = undefined -- deadlockall
do_deadlockall xs [model] = undefined -- deadlockall model

do_deadlock [spec] = undefined -- spec :[deadlock free]
do_deadlock [spec,model] = undefined -- spec :[deadlock free [m]]

do_divergenceall xs [] = undefined -- divergenceall
do_divergenceall xs [model] = undefined -- divergenceall model

do_divergence [spec] = undefined -- spec :[divergence free]
do_divergence [spec,model] = undefined -- spec :[divergence free [m]]

do_deterministicall xs [] = undefined -- divergenceall
do_deterministicall xs [model] = undefined -- divergenceall model

do_deterministic [spec] = undefined -- spec :[divergence free]
do_deterministic [spec,model] = undefined -- spec :[divergence free [m]]

do_jumbo xs = undefined


-- Print the current directory structure with files
fdr4check :: FilePath -> Assertion -> IO [String]
fdr4check spec ass =
  do copyFile spec "temp.txt";
     appendFile "temp.txt" (makeRefAssert' ass);
     -- start1 <- getCPUTime;
     (_, Just hout, _, ph) <- createProcess (proc "bash" ["-c", "refines temp.txt -q -f plain"]){ std_out = CreatePipe };
     -- end1 <- (waitForProcess ph >> getCPUTime);
     grepBytes <- hGetContents hout;
     -- let diff = (fromIntegral (end1 - start1)) / (10^12);
     let aa = (unlines $ map unwords (parseAssert2 ass grepBytes));
     cc <- (parseAssert2 ass grepBytes)
     return cc;

-- batchFDR4 spec xs
--   = do
--      dd <- (mapM (fdr4 spec) (batchRef xs))
--      -- let cc = ((map putToTuple $ concat dd));
--      appendFile "ref_raw.txt" (uwl dd)
--      return (unlines $ map unwords dd)

\end{code}
