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
import Formatter
import System.IO          -- Standard IO library, so we can catch IO errors etc.
import Control.Exception
import Control.Monad
import System.Directory
import MappingFunStatelessCircus
--import System.Console.Readline  -- was Readline

prompt1 = "Circus2CSP> " -- prompt for each command
prompt2 = "      " -- a visible, but cut/pastable, prompt for multiline input

specname = ""
-- These determine how most large output terms are displayed.
pinfo = pinfo_extz 75
output_zexpr = zexpr_stdout pinfo
output_zpred = zpred_stdout pinfo
output_zpara = zpara_stdout pinfo


main :: IO ()
main
  = do  putStrLn "Welcome to Circus2CSP translator, version 0.7b.  September 2017"
        putStrLn "Author: Artur Oliveira Gomes (gomesa at tcd.ie)"
        putStrLn "This is based on JAZA (Just Another Z Animator), see below."
        putStrLn "Copyright(C) 1999-2005 Mark Utting (marku@cs.waikato.ac.nz)."
        putStrLn "Jaza comes with ABSOLUTELY NO WARRANTY (see file COPYING)."
        putStrLn "This is free software, and you are welcome to redistribute"
        putStrLn "it under certain conditions (see file COPYING)."
        putStrLn ""
        putStrLn "Type `help' to see the available commands."
        putStrLn ""
      	get_cmd animator0 ""


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
      = do  s <- getLineEdit prompt2
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
  ["Available commands:",
   fmtcmd "quit"                   "Exit the animator",
   fmtcmd "load filename"          "Load a Z specification from a file",
   fmtcmd "show"                   "Display a summary of whole spec.",
   fmtcmd "tocsp"                   "Map the whole spec into CSP.",
   fmtcmd "latex"                   "Pretty print into LaTeX.",
   fmtcmd "omega"                  "Apply the Omega function to Circus spec",
   fmtcmd "reset"                  "Reset the whole specification",
   fmtcmd "help"                   "Display this message",
   fmtcmd "% comment"              "(Ignored)"
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
  | cmd == ":load" =
      do {putStrLn ("ERROR \"" ++ args
		    ++ "\" (Line 1): You did not quit JAZA."
		    ++ "\nDo the load again...");
	  return ()}
  | cmd == "help" && args =="" =
      do {putStr (unlines help); get_cmd anim fn}
  | cmd == "load" =
      catch
	  (do {putStrLn ("Loading '"++args++"' ...");
	       spec <- readFile (args++".tex");
	       done_cmd (pushfile args spec anim)})
	  (\err ->
	      do {putStrLn (show (err :: IOException));
		  get_cmd anim fn})
  | cmd == "reset" && args == "" =
      done_cmd (resetanimator anim)
  | cmd == "show" =
      done_cmd (anim, showC,fn)
  | cmd == "tocsp" =
      done_cmd (anim, upslonCircus anim fn, fn)
  | cmd == "latex" =
      done_cmd (anim, latexCircus anim fn, fn)
  | cmd == "omega" =
      done_cmd (omegaCircus anim fn)
  | otherwise =
      do  putStrLn "Unknown/illegal command."
	  get_cmd anim fn
  where
  -- rd is used to read input values from user
  rd p = getLineEdit ("    Input " ++ p ++ " = ")
  showC = showCircus anim


done_cmd :: (Animator, Answer,String) -> IO ()
done_cmd (anim, DoneUpsilon s f,args)
  = do {putStrLn s; touch (args++".csp"); writeStr (args++".csp") s; get_cmd anim args}
done_cmd (anim, DoneLatex s f,args)
  = do {putStrLn s; writeStr (args++".tex") s; get_cmd anim args}
done_cmd (anim, DoneOmega s f,args)
  = do {putStrLn s; touch (args++".csp"); writeStr (args++".hc") s; get_cmd anim args}
done_cmd (anim, Done s,args)
  = do {putStrLn s; writeFile "spec.txt" s; get_cmd anim args}
done_cmd (anim, ErrorMsg m,args)   = do {putErrorMsg m; get_cmd anim args}
done_cmd (anim, ErrorLocns es,args)= do {putStrLn (unlines (map fmtperr es));
           get_cmd anim args}

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
    do  sequence_ (map putMsgPart m)
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
getLineEdit prompt =
    do  putStr prompt
	hFlush stdout   -- needed with GHC.
	getLine
--    do  Just s <- readline prompt
--	if null s
--	   then return ()
--	   else addHistory s
--	return s
\end{code}
