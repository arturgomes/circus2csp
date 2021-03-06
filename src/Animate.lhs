\section{Animate functions}

Here you find the animator functions and also where we include the
Omega mappings and Circus to CSP mappings.

\begin{code}
module Animate
-- This module defines the Animator data structure, and
-- various operations on it.  Text and Graphical User Interfaces
-- should be built on top of this module.
( Animator,
  animator0,        -- initial animator state
  getSrcDir, getDstDir, -- get source and destination directories
  setSrcDir, setDstDir, -- set source and destination directories
  setFName, getFName,       -- name of currently loaded file
  Answer(..),       -- most Animator results are returned using this
  errstr,           -- convenience function for creating a string ErrorMsg.
  isUndefMsg,       -- recognises the 'undefined result' message
  isDone,           -- tests an animator result to see if it succeeded
  pushfile, resetanimator, -- extending/deleting the spec.
  showCircus,       -- display the spec after omega -- Andrew (May 2018)
  showOrigSpec,       -- similar to showspec but with DoneCirc -- Artur Gomes
  SyntaxError,       -- from Errors module
  omegaCircus,       -- Omega function for the Circus translator
  preVarOmegaCircus,       -- Omega function for the Circus translator
  upslonCircus,       -- Upslon function for the Circus translator
  prevarupslonCircus,       -- Upslon function for the Circus translator
  latexCircus,        -- pretty print in Latex
  batchGetProcList -- get processes name from the Animator
)
where

import AST
import Parse
import Unfold
import Optimize
import Eval
import Errors
import Data.Char
import Data.List
import PreVarMappingFunStatelessCircus
import DistMemMappingFunStatelessCircus
import PreVarMappingFunCircusCSP
import DistMemMappingFunCircusCSP
--import PrintTex



-- This data structure contains all the internal state of the animator.
-- We use named fields so that it can easily be extended with new fields.
data Animator
  = Anim { spec::[ZParaInfo]  -- a stack of definitions, most recent at head
         , filename :: String -- working filename
         , srcSubDir :: String -- optional place to look for files
         , dstSubDir :: String -- optional place to output files
         }

getSrcDir = srcSubDir
getDstDir = dstSubDir
setSrcDir anim str = anim{srcSubDir = str}
setDstDir anim str = anim{dstSubDir = str}
getFName = filename
setFName fn anim = anim{filename = fn}

data ZParaInfo
  = ZParaDefn{origpara::ZPara, defname::ZVar, defunfolded::ZExpr}
  | ZAxDefDefn{origpara::ZPara,axdefunfolded::[ZGenFilt]}
  | ZParaPred{origpara::ZPara, predunfolded::ZPred}
  | CircusChannel{origpara::ZPara, chanunfolded::[CDecl]}
  | CircusChanSet{origpara::ZPara, defcname::ZName, chansetunfolded::CSExp}
  | CircusProcess{origpara::ZPara,procunfolded::ProcDecl}
  | CircusAssert{origpara::ZPara,assertunfolded::String}
  | ZParaMachine{origpara::ZPara,
     defname::ZVar
      -- umachState::[ZGenFilt],
      -- umachInit ::[ZGenFilt],
      -- umachOps  ::[(String,[ZGenFilt])]
     }


batchGetProcList :: Animator -> [String]
batchGetProcList (Anim{spec=x}) = batchGetProcList' x
batchGetProcList' :: [ZParaInfo] -> [String]
batchGetProcList' [] = []
batchGetProcList' [(CircusProcess{procunfolded=x})]
  = [(getProcName x)]
batchGetProcList' ((CircusProcess{procunfolded=x}):xs)
  = [(getProcName x)]++(batchGetProcList' xs)
batchGetProcList' (_:xs) = (batchGetProcList' xs)
getProcName (CProcess p (ProcDefSpot zgf pd))
  = p ++ "("++(mapping_ZGenFilt_list [] (map mkNewBindings zgf) ) ++ ")"
getProcName (CProcess p _)
  = p


uenv :: [ZParaInfo] -> Env
uenv ps =
    empty_env (defs ++ branches)
    where
    x = string_to_zvar "x"
    defs = [(defname p, defunfolded p) | p@(ZParaDefn{}) <- ps]
    branches = concat [map mkbranch bs |
           ZParaDefn{defunfolded=ZFreeType n bs} <- ps]
    mkbranch (ZBranch0 s) = (s, ZFree0 s)
    mkbranch (ZBranch1 s dom) =
  -- a function, expressed as a set comprehension
              (s, ZSetComp [Choose x dom] (Just (ZTuple[ZVar x, ZFree1 s (ZVar x)])))

spec0 = []
filename0 = ""

animator0
  = Anim{ spec       =  spec0
        , filename   =  filename0
        , srcSubDir  =  "./"
        , dstSubDir  =  "./"
        }


-- Most animator functions return one of these responses.
-- In fact, functions whose names start with 'show...' only return this.

data Answer
  = Done String
  | DoneLatex String String
  | DoneUpsilon String String
  | DoneOmega String String
  | DoneReport String String
  | ErrorMsg ErrorMsg
  | ErrorLocns [SyntaxError]   -- (Line, Column, String) triples
  | Value ZValue
  | Pred ZPred
  | BoolValue Bool
  | Defn ZPara
  | Spec [ZPara]
  | SchemaCode String ZExpr Int   -- optimized code of a schema

errstr s = ErrorMsg [MStr s]

undefmsg = MStr "Result is Undefined.  Reason: "
isUndefMsg (m:_) = m == undefmsg
isUndefMsg _     = False

isDone :: Answer -> Bool
isDone (Done _) = True
isDone (DoneUpsilon _ _) = True
isDone (DoneLatex _ _) = True
isDone (DoneOmega _ _) = True
isDone (DoneReport _ _) = True
isDone _        = False


-- This is like pushpara, but processes an entire file.
-- If there are no errors, it pushes the entire file onto the current spec.
-- If there are errors anywhere in the file, none of the definitions in
-- the file are added.  That is, a load that gives errors does nothing.
-- TODO: incorporate filename into the syntax error messages.
pushfile :: String -> String -> Animator -> (Animator,Answer,String)
pushfile filename contents anim
  | isOk result = (anim{spec=spec2}, Done msg,filename)
  -- | isOk result = (anim{spec=spec2}, Done msg)
  | otherwise   = (anim, answerErrorOr result,filename)
  where
  result = do {para <- parseZspec contents;
          spec2 <- process_paras (spec anim) para;
          return (spec2, length para)}
  (spec2, ndefs) = fromOk result
  msg  = "Added " ++ show(ndefs) ++ " definition" ++
   (if ndefs > 1 then "s." else ".")


-- Andrew:
showCircus :: Animator  -> Answer
showCircus anim
 = Done $ unlines ( [ ""
                    , "Filename = " ++ filename anim
                    , "from: " ++ srcSubDir anim
                    , "  to: " ++ dstSubDir anim
                    , "-----" ]
                    ++ map showInteresting
                         (filter isInteresting $ reverse $ spec anim) )

isInteresting (CircusProcess (Process _) _) = True
isInteresting (CircusChannel (CircChannel _) _) = True
isInteresting _ = False

showInteresting (CircusProcess (Process (CProcess nm _)) _) = "PROCESS "++nm
showInteresting (CircusChannel (CircChannel cdecls) _)
  = "channel " ++ (intercalate ", " $ map showCDeclName cdecls)
showInteresting _ = "?"

showCDeclName (CChan nm)             =  nm
showCDeclName (CChanDecl nm _)       =  nm++":T"
showCDeclName (CGenChanDecl nm _ _)  =  "["++nm++"]"

-- Artur
-- 15/05/2018
-- I'm putting back the old showCircus but renamed to showOrigSpec
-- So I can have a look at what the original spec looks like
-- I'm debugging and I might take it out later on..

showOrigSpec :: Animator  -> Answer
showOrigSpec spec@Anim{spec=sp} = Done (unlines $ map fmtpara $ reverse sp)

--

getspecHC :: String -> Animator -> Answer
getspecHC args s@(Anim{spec=x}) = DoneOmega (unlines ( map fmtpara ( reverse x))) args

getspecCSP :: String -> String -> Answer
getspecCSP args s = DoneUpsilon s args

getspecLatex :: String -> String -> Answer
getspecLatex args s = DoneLatex s args
-- reverse example:
-- Input: reverse [1..5]
-- Output: [5,4,3,2,1]
--
-- unlines example:
-- Type:  [String] -> String
-- Input: unlines ["aa","bb","cc","dd","ee"]
-- Output: "aa\nbb\ncc\ndd\nee\n"

-- This is my first attempt in trying to apply
-- the Omega function into the spec
omegaCircus :: Animator -> String -> (Animator,Answer,String)
omegaCircus anim args
  | null (spec anim) = (anim, errstr "Omega command: Specification is empty", args)
  | otherwise        = (newanim, getspecHC args newanim, args)
  where
  msg = "Omega function applied to the current spec"
  newanim = anim{spec=(applyOmega anim "")}

preVarOmegaCircus :: Animator -> String -> (Animator,Answer,String)
preVarOmegaCircus anim args
  | null (spec anim) = (anim, errstr "Omega command: Specification is empty", args)
  | otherwise        = (newanim, getspecHC args newanim, args)
  where
  msg = "Omega function applied to the current spec"
  newanim = anim{spec=(applyOmega anim "prevar")}

applyOmega :: Animator -> String -> [ZParaInfo]
applyOmega anim typ
  | typ == "prevar" = fromOk (process_paras_omega (spec anim) (prevar_omega_Circus (map origpara (spec anim))))
  | otherwise = fromOk (process_paras_omega (spec anim) (omega_Circus (map origpara (spec anim))))

-- This is my first attempt in trying to apply
-- the Upsilon function into the spec
-- upslonCircus :: Animator -> Answer
upslonCircus anim args = getspecCSP args (applyUpslon anim)
prevarupslonCircus anim args = getspecCSP args (prevarapplyUpslon anim)

applyUpslon anim
  = upslonHeader
    ++ (mapping_Circus (reverse (map origpara (spec anim)))
                       (reverse (map origpara (spec anim))) )

prevarapplyUpslon anim
 = upslonHeader
   ++ (prevar_mapping_Circus (reverse (map origpara (spec anim)))
                      (reverse (map origpara (spec anim))) )


upslonHeader = "include \"sequence_aux.csp\"\ninclude \"function_aux.csp\"\n\n"

latexCircus anim args = getspecLatex args (applyLatex anim)

applyLatex anim
  = (print_tex_Circus (reverse (map origpara (spec anim))))

print_tex_Circus _ = "print_tex_Circus NYI"

resetanimator :: Animator -> (Animator,Answer,String)
resetanimator anim
  = ( anim{spec=spec0}
    , Done "Reset command: Specification is now empty.","")

----------------------------------------------------------------------
-- The remaining functions are usually private to this module
----------------------------------------------------------------------
answerErrorOr :: ErrorOr t -> Answer
answerErrorOr (SyntaxErrors errs)
  = ErrorLocns errs
answerErrorOr (Undefined msg)
  = ErrorMsg (undefmsg : msg)
answerErrorOr (TooBig info msg)
  = ErrorMsg (MStr ("Problem: " ++ show info) : MNewLine : msg)
answerErrorOr (Impossible msg)
  = ErrorMsg (MStr "Problem: " : msg)
answerErrorOr (IllFormed msg)
  = ErrorMsg (MStr "Specification Error: " : msg)



-- This is for showing a summary of a Z paragraph
fmtpara :: ZParaInfo -> String
fmtpara p
  = s -- ++ if null rest then "" else "..."
  where
  s = (show (origpara p))
  -- (s,rest) = splitAt 2000000 (show (origpara p))

-- splitAt
-- Type: Int -> [a] -> ([a],[a])
-- Input: splitAt 5 [1,2,3,4,5,6,7,8,9,10]
-- Output: ([1,2,3,4,5],[6,7,8,9,10])

get_info :: ZVar -> Animator -> ErrorOr ZParaInfo
get_info s anim
  | null matches   = IllFormed [MStr ("no such definition: " ++ show_zvar s)]
  | otherwise      = Ok (head matches)
  where
  matches = [p | p@ZParaDefn{defname=n} <- spec anim, n==s]

-- process_paras spec newp.
--
--  This pushes new paragraphs (newp) onto the existing specification (spec).
--
process_paras :: [ZParaInfo] -> [ZPara] -> ErrorOr [ZParaInfo]
process_paras spec []
  = return spec
process_paras spec (p@(ZGivenSetDecl s) : ps)
  = do let newp = ZParaDefn{origpara=p,
           defname=s,
           defunfolded=ZGivenSet s}
       newspec <- adddefn newp spec
       process_paras newspec ps
process_paras spec (p@(ZSchemaDef name se) : ps)
  = do gfs <- unfoldsexpr (uenv spec) se
       let newp = ZParaDefn{origpara=p,
           defname=make_schema_name name,
           defunfolded=(ZESchema (ZSchema gfs))}
       newspec <- adddefn newp spec
       process_paras newspec ps
process_paras spec (p@(ZSchemaDefP name px se) : ps)
  = do gfs <- unfoldsexpr (uenv spec) se
       let newp = ZParaDefn{origpara=p,
           defname=make_schema_name name,
           defunfolded=(ZESchema (ZSchema gfs))}
       newspec <- adddefn newp spec
       process_paras newspec ps
process_paras spec (p@ZMachineDef{} : ps)
  = do let e = uenv spec
       state <- unfoldsexpr e . sref . machState $ p
       init <- unfoldsexpr e . sref . machInit $ p
       ops <- mapM (unfoldsexpr e . sref) (machOps p)
       -- TODO: check typing conditions of machine
       let newp = ZParaMachine{origpara=p,
        defname=string_to_zvar (machName p)}
       let newspec = newp:spec
       process_paras newspec ps
  where
  sref name = ZSRef (ZSPlain name []) [] []
process_paras spec (p@(ZAbbreviation n e) : ps)
  = do ue <- unfoldexpr (uenv spec) e
       let newp = ZParaDefn{origpara=p,
           defname=n,
           defunfolded=ue}
       newspec <- adddefn newp spec
       process_paras newspec ps
process_paras spec (p@(ZFreeTypeDef n bs) : ps)
  = do  ue <- unfoldexpr (uenv spec) (ZFreeType n bs)
        let newp = ZParaDefn{origpara=p,
           defname=n,
           defunfolded=ue}
        newspec <- adddefn newp spec
        process_paras newspec ps
process_paras spec (p@(ZPredicate pred) : ps)
  = do  upred <- unfoldpred (uenv spec) pred
        let newp = ZParaPred{origpara=p,
           predunfolded=upred}
        process_paras (newp:spec) ps
process_paras spec (p@(CircChannel s) : ps)
  = do let newp = CircusChannel{origpara=p,
           chanunfolded=s}
       let newspec = newp:spec
       process_paras newspec ps
process_paras spec (p@(CircChanSet v s) : ps)
  = do let newp = CircusChanSet{origpara=p,
           defcname=v,
           chansetunfolded=s}
       let newspec = newp:spec
       process_paras newspec ps
process_paras spec (p@(Process s) : ps)
  = do let newp = CircusProcess{origpara=p,
           procunfolded=s}
       let newspec = newp:spec
       process_paras newspec ps
process_paras spec (p@(Assert s) : ps)
 = do let newp = CircusAssert{origpara=p,
          assertunfolded=s}
      let newspec = newp:spec
      process_paras newspec ps
process_paras spec (p@(ZAxDef v) : ps)
  = do let newp = ZAxDefDefn{origpara=p,
           axdefunfolded=v}
       let newspec = newp:spec
       process_paras newspec ps
process_paras spec (para : ps)
  = fail ("Not implemented yet: " ++ show para)


adddefn :: ZParaInfo -> [ZParaInfo] -> ErrorOr [ZParaInfo]
adddefn def spec
    | defname def `elem` [n | ZParaDefn{defname=n} <- spec]
      = return spec
      -- = fail ("redeclaration of: " ++ show_zvar(defname def)) -- ignore what's already declared
    | otherwise
      = return (def:spec)
\end{code}
The following is similar to $process_paras$ but here it works for applying the Omega functions. It will replace the existing definitions of Processes
\begin{code}
-- process_paras_omega spec newp.
--
--  This pushes new paragraphs (newp) onto the existing specification (spec).
--
process_paras_omega :: [ZParaInfo] -> [ZPara] -> ErrorOr [ZParaInfo]
process_paras_omega spec []
  = return spec
process_paras_omega spec (p@(Process s) : ps)
  = do let newp = CircusProcess{origpara=p,
           procunfolded=s}
       let newspec = newp:(remove_proc_para spec s)
       process_paras_omega newspec ps
process_paras_omega spec (p@(CircChannel s) : ps)
  = do let newp = CircusChannel{origpara=p,
           chanunfolded=s}
       let newspec = newp:(remove_chan_para spec (CircChannel s))
       process_paras_omega newspec ps
process_paras_omega spec (p@(CircChanSet v s) : ps)
  = do let newp = CircusChanSet{origpara=p,
           defcname=v,
           chansetunfolded=s}
       let newspec = newp:(remove_chan_para spec (CircChanSet v s))
       process_paras_omega newspec ps
process_paras_omega spec (p@(ZGivenSetDecl te) : ps)
  = do let newp = ZParaDefn{origpara=p,
           defname=te,
           defunfolded=ZGivenSet te}
       newspec <- adddefn newp spec
       process_paras_omega newspec ps
process_paras_omega spec (p@(ZAbbreviation ("BINDINGS",[],[]) e) : ps)
  = do ue <- unfoldexpr (uenv spec) e
       let newp = ZParaDefn{origpara=p,
           defname=("BINDING",[],[]),
           defunfolded=ue}
       newspec <- adddefn newp spec
       process_paras_omega newspec ps
process_paras_omega spec (p@(ZAbbreviation ("\\delta",[],[]) e) : ps)
  = do ue <- unfoldexpr (uenv spec) e
       let newp = ZParaDefn{origpara=p,
           defname=("\\delta",[],[]),
           defunfolded=ue}
       newspec <- adddefn newp spec
       process_paras_omega newspec ps
process_paras_omega spec (p@(ZAbbreviation nm e) : ps)
  = do ue <- unfoldexpr (uenv spec) e
       let newp = ZParaDefn{origpara=p,
           defname=nm,
           defunfolded=ue}
       newspec <- adddefn newp spec
       process_paras_omega newspec ps
process_paras_omega spec (p@(ZFreeTypeDef ("NAME",[],[]) bs) : ps)
  = do  ue <- unfoldexpr (uenv spec) (ZFreeType ("NAME",[],[]) bs)
        let newp = ZParaDefn{origpara=p,
           defname=("NAME",[],[]),
           defunfolded=ue}
        newspec <- adddefn newp spec
        process_paras_omega newspec ps
process_paras_omega spec (p@(ZFreeTypeDef ("UNIVERSE",[],[]) bs) : ps)
  = do  ue <- unfoldexpr (uenv spec) (ZFreeType ("UNIVERSE",[],[]) bs)
        let newp = ZParaDefn{origpara=p,
           defname=("UNIVERSE",[],[]),
           defunfolded=ue}
        newspec <- adddefn newp spec
        process_paras_omega newspec ps
process_paras_omega spec (p@(ZFreeTypeDef nm bs) : ps)
   = do  ue <- unfoldexpr (uenv spec) (ZFreeType nm bs)
         let newp = ZParaDefn{origpara=p,
            defname=nm,
            defunfolded=ue}
         newspec <- adddefn newp spec
         process_paras_omega newspec ps
process_paras_omega spec (para : ps)
  = process_paras_omega spec ps
\end{code}
\begin{code}
remove_proc_para [CircusProcess{origpara=x, procunfolded=pd1}] cp
  = case (compare_proc pd1 cp) of
      True -> []
      _ -> [CircusProcess{origpara=x,procunfolded=pd1}]
remove_proc_para [x] cp
  = [x]
remove_proc_para ((CircusProcess{origpara=x, procunfolded=pd1}):xs) cp
  = case (compare_proc pd1 cp) of
      True -> xs
      _ -> ((CircusProcess{origpara=x,procunfolded=pd1}):(remove_proc_para xs cp))
remove_proc_para (x:xs) cp
  = x:(remove_proc_para xs cp)

\end{code}
\begin{code}
remove_chan_para [CircusChannel{origpara=x, chanunfolded=pd1}] (CircChannel cp)
  = case pd1 == cp of
      True -> []
      _ -> [CircusChannel{origpara=x, chanunfolded=pd1}]
remove_chan_para [CircusChanSet{origpara=x, defcname=n, chansetunfolded=pd1}] (CircChanSet v s)
  = case v == n of
      True -> []
      _ -> [CircusChanSet{origpara=x, defcname=n, chansetunfolded=pd1}]
remove_chan_para [x] cp
  = [x]
remove_chan_para ((CircusChannel{origpara=x, chanunfolded=pd1}):xs) (CircChannel cp)
  = case pd1 == cp of
      True -> xs
      _ -> ((CircusChannel{origpara=x, chanunfolded=pd1}):(remove_chan_para xs (CircChannel cp)))
remove_chan_para ((CircusChanSet{origpara=x, defcname=n, chansetunfolded=pd1}):xs) (CircChanSet v cp)
  = case v == n of
      True -> xs
      _ -> ((CircusChanSet{origpara=x, defcname=n, chansetunfolded=pd1}):(remove_chan_para xs (CircChanSet v cp)))
remove_chan_para (x:xs) cp
  = x:(remove_chan_para xs cp)
\end{code}
\begin{code}
compare_proc (CProcess zn1 pd1) (CProcess zn2 pd2)
  = case (zn1 == zn2) of
      True -> True
      _ -> False
compare_proc (CParamProcess zn1 znls1 pd1) (CParamProcess zn2 znls2 pd2)
  = case (zn1 == zn2) of
      True -> True
      _ -> False
compare_proc (CGenProcess zn1 znls1 pd1) (CGenProcess zn2 znls2 pd2)
  = case (zn1 == zn2) of
      True -> True
      _ -> False
\end{code}
