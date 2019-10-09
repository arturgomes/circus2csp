%!TEX root = $HOME/Dropbox/Academico/PostGrad/Doutorado/phd/thesis/artur-gomes.tex

\chapter{Mapping Functions - Circus to CSP}

Mapping Functions - Circus to CSP
\begin{code}
module PreVarMappingFunCircusCSP
(
  prevar_mapping_Circus
)
where
import AST
import Subs
import PreVarCRL
import Formatter
import Data.List
-- import Data.Text hiding (map,concat)
import Data.Char hiding (toUpper, toTitle)
import PreVarMappingFunStatelessCircus
import PreVarOmegaDefs


showexpr = zexpr_string (pinfo_extz 80)
\end{code}

%In here, you have to create a preprocessing set of functions
% in order to rename the variable names and put it as a preamble
% of the specification.

\section{Mapping Circus Paragraphs}
The following functions are used to map Circus Channels into CSP. However, generic circus channels are not yet captured by the tool.
\begin{code}
prevar_mapping_Circus :: [ZPara] -> [ZPara] -> String
prevar_mapping_Circus spec []
  = ""
prevar_mapping_Circus spec [x]
  = prevar_mapping_CircParagraphs spec x
prevar_mapping_Circus spec (x:xs)
  = prevar_mapping_CircParagraphs spec x ++ (prevar_mapping_Circus spec xs)

-- prevar_filter_spec (e(CircChannel a):xs)
\end{code}
\subsection{Mapping the UNIVERSE type}
\begin{circus}
  \Upsilon_{CircParagraphs}([UNIVERSE])
  \defs\\
     \tco{datatype UNIVERSE = }MK_{Universe}(ulst)\\
  MK_{subtype}(fulst)\\
  MK_{value}(fulst)\\
  MK_{type}(fulst)\\
  MK_{tag}(fulst)\\\\
  % \tco{Memory(}MK_{mem\_param}(fulst)\tco{)=}\\
  % \qquad MK_{mget}(fulst)\\
  % \qquad MK_{mset}(fulst)\\
  % \qquad \tco{[] terminate -> SKIP}\\\\
  % \tco{Memorise(P,}MK_{mem\_param}(fulst)\tco{)=}\\
  % \qquad\tco{((P ; terminate -> SKIP)[|MEM\_I|] Memory(}MK_{mem\_param}(fulst)\tco{))\textbackslash MEM\_I}
\end{circus}
    \begin{provs}
      \item $\delta(\emptyset) \notin spec$ -- There is at least one element in the $\delta$ mapping.
        \item $spec$ is the whole specification
        \item $ulst = DEF_{Universe}(spec)$ -- list of mappings from variables to types, from $\delta$ function
        \item $fulst = GET_{Types}(spec)$ -- list of all types from $\delta$ function
    \end{provs}

\begin{code}

prevar_mapping_CircParagraphs :: [ZPara] -> ZPara -> String

prevar_mapping_CircParagraphs spec (ZAxDef [Choose _ (ZCall (ZVar ("\\fun",[],"")) tp),Check (ZEqual (ZVar (f,_,_)) (ZLambda a b))])
  = "\n"++f++"("++(joinBy "," $ map (prevar_mapping_ZExpr (get_delta_names1 spec)) $ map (\(Choose v t) -> ZVar v) $ prevar_filter_ZGenFilt_Choose a)++") = "++(prevar_mapping_ZExpr (get_delta_names1 spec) b)

prevar_mapping_CircParagraphs spec (ZAxDef [Choose _ (ZCall (ZVar ("\\pfun",[],"")) tp),Check (ZEqual (ZVar (f,_,_)) (ZLambda a b))])
  = "\n"++f++"("++(joinBy "," $ map (prevar_mapping_ZExpr (get_delta_names1 spec)) $ map (\(Choose v t) -> ZVar v) $ prevar_filter_ZGenFilt_Choose a)++") = "++(prevar_mapping_ZExpr (get_delta_names1 spec) b)

prevar_mapping_CircParagraphs spec (ZFreeTypeDef ("UNIVERSE",_,_) []) = ""
prevar_mapping_CircParagraphs spec (ZFreeTypeDef ("UNIVERSE",_,_) univ)
  = case res of
    False -> ("\n--------------------------------"++
            "\n-- The universe of values"++
            "\n datatype UNIVERSE = " ++ (prevar_mapping_ZBranch_list univ)) -- ++
            -- "\n NatValueMax = 4\nNatValue = {0..NatValueMax}"++
            -- "\n--Conversions"++
            -- "\n"++(mk_value (get_u_tag_ZBranch univ))++
            -- "\n"++(mk_type (get_u_tag_ZBranch univ))++
            -- "\n"++(mk_tag (get_u_tag_ZBranch univ)))
    True -> ""
  where
    univlst = (def_universe spec)
    funivlst = remdups (prevar_filter_types_universe' univlst)
    res = member (ZAbbreviation ("\\delta",[],[]) (ZSetDisplay [])) spec
\end{code}
\subsection{Mapping $mget$ and $mset$ for the $Memory$ approach}
\begin{circus}
  \Upsilon_{CircParagraphs}(\circchannel mget,mset : NAME \cross UNIVERSE)
  \defs\\\qquad \Upsilon_{CDecl}(\circchannel mget,mset : NAME \cross UNIVERSE)
\end{circus}
    \begin{provs}
      \item $\delta(\emptyset) \notin spec$ -- There is at least one element in the $\delta$ mapping.
    \end{provs}
\begin{code}
prevar_mapping_CircParagraphs spec (CircChannel [CChanDecl "mget" (ZCross [ZVar ("NAME",[],[]),ZVar ("UNIVERSE",[],[])]),CChanDecl "mset" (ZCross [ZVar ("NAME",[],[]),ZVar ("UNIVERSE",[],[])])])
  = case res of
    False -> "\n\n--------------------------------"
            ++ "\n -- mget, mset and terminate -- "
            ++ "\n--------------------------------\n"
            ++ prevar_mapping_CDecl spec [CChanDecl "mget" (ZCross [ZVar ("NAME",[],[]),ZVar ("UNIVERSE",[],[])]),CChanDecl "mset" (ZCross [ZVar ("NAME",[],[]),ZVar ("UNIVERSE",[],[])])]
    True -> ""
    where
      res =  member (ZAbbreviation ("\\delta",[],[]) (ZSetDisplay [])) spec
\end{code}
\subsection{Mapping $terminate$ for the $Memory$ approach}
\begin{circus}
  \Upsilon_{CircParagraphs}(\circchannel terminate)
  \defs\\\qquad \Upsilon_{CDecl}(\circchannel terminate)
\end{circus}
    \begin{provs}
      \item $\delta(\emptyset) \notin spec$ -- There is at least one element in the $\delta$ mapping.
    \end{provs}
\begin{code}
prevar_mapping_CircParagraphs spec (CircChannel [CChan "terminate"])
  = case res of
    False -> "\n" ++ prevar_mapping_CDecl spec [CChan "terminate"]
    True -> ""
    where
      res =  member (ZAbbreviation ("\\delta",[],[]) (ZSetDisplay [])) spec
\end{code}
\subsection{Mapping $MEMI$ channel set for the $Memory$ approach}

\begin{circus}
  \Upsilon_{CircParagraphs}(\circchannelset MEMI == \lchanset mget, mset, terminate \rchanset)
  \defs\\\qquad \tco{MEM\_I =}\Upsilon_{CSExp}(\lchanset mget, mset, terminate \rchanset)
\end{circus}
    \begin{provs}
      \item $\delta(\emptyset) \notin spec$ -- There is at least one element in the $\delta$ mapping.
    \end{provs}
\begin{code}
prevar_mapping_CircParagraphs spec (CircChanSet "MEMI" (CChanSet ["mset","mget","terminate"]))
  = case res of
    False -> "\n\n--------------------------------"
            ++ "\n -- MEMI -- "
            ++ "\n--------------------------------\n"
            ++ "MEMI" ++ " = " ++ (prevar_mapping_CSExp (CChanSet ["mset","mget","terminate"]))
    True -> ""
    where
      res =  member (ZAbbreviation ("\\delta",[],[]) (ZSetDisplay [])) spec

\end{code}
\subsection{Mapping $\delta$ function}

The definition of the $\delta$ is not directly translated into CSP. Instead, we define in the $UNIVERSE$ translation rules, the equivalent notation, the $typeXYZ$ function.


\subsection{Mapping $BINDING$}

\begin{circus}
  \Upsilon_{CircParagraphs}(BINDING \defs NAME \cross \mathbb{U})
  \defs\\\qquad
     \tco{BINDINGS\_}
  T_1
     \tco{ =\ \{set(b) | b <- set(distCartProd(NAMES\_VALUES\_}T_1\tco{))\}}\\
  \qquad\ldots
\\\qquad \tco{BINDINGS\_}T_n\tco{ = \{set(b) | b <- set(distCartProd(NAMES\_VALUES\_}T_n\tco{))\}}
\end{circus}
    \begin{provs}
      \item $T_1,\ldots,T_N$ are the possible types of the specification.
      \item $\delta(\emptyset) \notin spec$ -- There is at least one element in the $\delta$ mapping.
    \end{provs}
\begin{code}
prevar_mapping_CircParagraphs spec (ZAbbreviation (xn,_,_) xp)
  | Subs.isPrefixOf "\\delta_" xn
      && (Data.List.length xn > Data.List.length "\\delta_")
      -- = "\n-- Subtype definition for "++(lastN 3 nm)++
        = "\n-- Binding set for "++nm++
        "\nb_"++ (def_U_prefix nm)++ "1 = {"++
        (joinBy "," $ (map (make_binding spec) mbp))++
        "}" ++
          -- "\nsubtype "++nm ++ " = "++
          -- (prevar_mapping_ZBranch_list (remdups zbs))++
          -- "\n" ++ mk_NAME_VALUES_TYPE (lastN 3 nm) ++
          "\n"
  | Subs.isPrefixOf "BINDINGS" xn
    && (Data.List.length xn > Data.List.length "BINDINGS")
        = ("\n-- Bindings definitions for "++(lastN 3 xn)++ "\n"
            ++ xn
            ++ " = {set(b) | b <- set(distCartProd(NAMES_VALUES_"
            ++ (lastN 3 xn)
            ++ "))}\n")
  | "BINDINGS" == xn = ""
  | otherwise = "\n"++ xn ++
                " = " ++ prevar_mapping_ZExpr (get_delta_names1 spec) xp
  where
    nm = (Data.List.drop (Data.List.length "\\delta_") xn)
    mbp = map make_binding_pair ((\(ZSetDisplay xs) -> xs) xp)

\end{code}
\subsection{Mapping $NAME$}
\begin{code}
prevar_mapping_CircParagraphs spec (ZFreeTypeDef (nm,b,[]) []) = ""
prevar_mapping_CircParagraphs spec (ZFreeTypeDef (nm,b,[]) zbs)
  | nm == "NAME" = "\n-- definition of NAME for the entire spec "
      ++ "\ndatatype NAME = "++(prevar_mapping_ZBranch_list (remdups zbs))++"\n"
  | Subs.isPrefixOf "NAME" nm = "\nsubtype "++ nm
      ++ " = " ++(prevar_mapping_ZBranch_list (remdups zbs))++"\n"
  | Subs.isPrefixOf "U_" nm = "\nsubtype "++ nm
          ++ " = " ++(prevar_mapping_ZBranch_list (remdups zbs))++"\n"
  | otherwise = "\ndatatype "++ nm ++ " = " ++(prevar_mapping_ZBranch_list zbs)++"\n"


\end{code}
% \subsection{Mapping given sets}
%
% \begin{circus}
%   \Upsilon_{CircParagraphs}(N == \{a | b\})
%   \defs\\\qquad
%      \tco{N = }\Upsilon_{ZTuple}(\{a | b\})
% \end{circus}
% \begin{code}
% prevar_mapping_CircParagraphs spec (ZAbbreviation (n,[],t) (ZSetComp xl (Just (ZTuple ztp))))
%   = "\n"++ n ++ " = (" ++ prevar_mapping_ZTuple ztp ++ ")"
%
% \end{code}
\subsection{Mapping Z free types}

\begin{circus}
  \Upsilon_{CircParagraphs}(N ::= a_1 | \ldots | a_n) \defs \tco{datatype N = }\Upsilon_{ZBranch\_list}(a_1 | \ldots | a_n)
\end{circus}

\begin{code}
prevar_mapping_CircParagraphs spec (ZFreeTypeDef (a,b,c) zbs)
  = "\ndatatype " ++ a ++ " = " ++ (prevar_mapping_ZBranch_list zbs)

\end{code}
\subsection{Mapping \Circus\ process -- $ProcDecl$}

\begin{circus}
  \Upsilon_{CircParagraphs}(P) \defs\Upsilon_{ProcDecl}(P)
\end{circus}
    \begin{provs}
      \item $P$ is a \Circus\ process.
    \end{provs}
\begin{code}
prevar_mapping_CircParagraphs spec (Process cp)
  = "\n" ++ prevar_mapping_ProcDecl spec cp

\end{code}
\subsection{Mapping \Circus\ channel -- $CDecl$}

\begin{circus}
  \Upsilon_{CircParagraphs}(\circchannel c) \defs \Upsilon_{CDecl}(c)
\end{circus}
    \begin{itemize}
      \item $c$ is a \Circus\ channel.
    \end{itemize}
\begin{code}
prevar_mapping_CircParagraphs spec (CircChannel cc2)
  = "\n" ++ prevar_mapping_CDecl spec cc2
\end{code}

\subsection{Mapping \Circus\ channel set -- $CSExp$}

\begin{circus}
  \Upsilon_{CircParagraphs}(\circchannelset CN == CS) \defs
      \tco{CN = }\Upsilon_{CSExp}(CS)
\end{circus}
    \begin{provs}
      \item $CS$ is a $CSExp$.
    \end{provs}
\begin{code}
prevar_mapping_CircParagraphs spec (CircChanSet cn c2)
  = "\n" ++ cn ++ " = " ++ (prevar_mapping_CSExp c2)

\end{code}

\ignore{
\begin{code}
-- prevar_mapping_CircParagraphs spec (ZGivenSetDecl gs)
--   = undefined
-- prevar_mapping_CircParagraphs spec (ZSchemaDef zsn zse)
--   = undefined
\end{code}
}
% \subsection{Mapping Z abbreviation}
%
% \begin{circus}
%   \Upsilon_{CircParagraphs}(N == expr) \defs \tco{N = }\Upsilon_{ZExpr}
% \end{circus}
%     \begin{provs}
%       \item $expr$ is a Z expression.
%     \end{provs}
\begin{code}
-- % prevar_mapping_CircParagraphs spec (ZAbbreviation (n,[],t) (ZSetDisplay ls))
-- %   = "\n" ++ n ++ " = " ++ (prevar_mapping_ZExpr (get_delta_names1 spec) (ZSetDisplay ls))
-- % prevar_mapping_CircParagraphs spec (ZAbbreviation (n,[],t) expr)
-- %   = "\n" ++ n ++ " = " ++ (prevar_mapping_ZExpr (get_delta_names1 spec) expr)
prevar_mapping_CircParagraphs spec (Assert x) = "\n" ++ x
\end{code}
\ignore{
\begin{code}
-- prevar_mapping_CircParagraphs spec (ZPredicate zp)
--   = undefined
-- prevar_mapping_CircParagraphs spec (ZAxDef zgfs)
--   = undefined
-- prevar_mapping_CircParagraphs spec (ZGenDef zgfs)
--   = undefined
\end{code}}
In any other cases, an error is raised.
\begin{code}
prevar_mapping_CircParagraphs spec x
  = fail ("not implemented by prevar_mapping_CircParagraphs: " ++ show x)
\end{code}

\subsection{Mapping Free Types - Auxiliary functions}
The function $mapping\_ZBranch$ transforms free types and composite free types into the corresponding notation in CSP. For such, a composite type can be $A\cross B$ and therefore, it is translated using $mapping\_ZBranch\_cross$.
\begin{code}
prevar_mapping_ZBranch :: ZBranch -> String
prevar_mapping_ZBranch  (ZBranch0 (a,b,c)) = prevar_mapping_ZExpr [] (ZVar (a,b,c))
prevar_mapping_ZBranch  (ZBranch1 (a,xb,c) (ZVar (b,[],t))) = prevar_mapping_ZExpr [] (ZVar (a,xb,c)) ++ "." ++ prevar_mapping_ZExpr [] (ZVar (b,[],t))
prevar_mapping_ZBranch  (ZBranch1 (a,xb,c) (ZCross b)) = prevar_mapping_ZExpr [] (ZVar (a,xb,c)) ++ "." ++ (prevar_mapping_ZBranch_cross b)
prevar_mapping_ZBranch  (ZBranch1 (a,xb,c) tt) = prevar_mapping_ZExpr [] (ZVar (a,xb,c)) ++ "." ++ prevar_mapping_ZExpr [] tt
\end{code}

\begin{code}
prevar_mapping_ZBranch_cross :: [ZExpr] -> String
prevar_mapping_ZBranch_cross [ZVar (a,b,c)] = a
prevar_mapping_ZBranch_cross ((ZVar (a,b,c)):xs) = a ++ "." ++ (prevar_mapping_ZBranch_cross xs)
\end{code}
Then, the $mapping\_ZBranch\_list$ transforms the RHS of the equality, with the possible free types from a $ZBranch$ list.
\begin{code}
prevar_mapping_ZBranch_list :: [ZBranch] -> String
prevar_mapping_ZBranch_list [] = ""
prevar_mapping_ZBranch_list [x] = (prevar_mapping_ZBranch x)
prevar_mapping_ZBranch_list (x:xs) = (prevar_mapping_ZBranch x) ++ " | " ++ (prevar_mapping_ZBranch_list  xs)
\end{code}
\subsection{Mapping Circus Channels}
This set of mapping functions will translate the declaration of channels from \Circus\ into \CSPM. Although, generic channels are not yet available.

\begin{circus}
  \Upsilon_{CDecl}(\circchannel a) \defs \tco{channel a}\\
  \Upsilon_{CDecl}(\circchannel a : T) \defs \tco{channel a : T}
\end{circus}
\begin{code}
prevar_mapping_CDecl :: [ZPara] -> [CDecl] -> String
prevar_mapping_CDecl spec x
  = (prevar_display_chann_CChan spec x1) ++ (prevar_display_chann_CChanDecl spec x2)
  where x1 = prevar_filter_channels_CChan x
        x2 = prevar_filter_channels_CChanDecl x
-- prevar_mapping_CDecl spec (CGenChanDecl zn3 zn4 ze)
--   = undefined
\end{code}
A channel declaration can be either of form $CChan$ or $CChanDecl$. For $CChan$, we can have $\circchannel terminate$, whereas for $CChanDecl$, $\circchannel mget : NAME \cross BINDING$. Thus, we filter both cases into $x1$ for $CChan$ and $x2$ for $CChanDecl$, and then, display them accordingly.
\begin{code}
prevar_filter_channels_CChan :: [CDecl] -> [ZName]
prevar_filter_channels_CChan [] = []
prevar_filter_channels_CChan ((CChan a):xs) = [a]++(prevar_filter_channels_CChan xs)
prevar_filter_channels_CChan (_:xs) = (prevar_filter_channels_CChan xs)
\end{code}
\begin{code}
prevar_filter_channels_CChanDecl :: [CDecl] -> [(ZName, ZExpr)]
prevar_filter_channels_CChanDecl [] = []
prevar_filter_channels_CChanDecl ((CChanDecl a b):xs)
    = [(a,b)]++(prevar_filter_channels_CChanDecl xs)
prevar_filter_channels_CChanDecl (_:xs) = (prevar_filter_channels_CChanDecl xs)
\end{code}
\begin{code}
prevar_display_chann_CChan :: [ZPara] -> [ZName] -> String
prevar_display_chann_CChan spec [] = ""
prevar_display_chann_CChan spec x = "channel " ++ prevar_display_chann_CChan' spec x
\end{code}
\begin{code}
prevar_display_chann_CChan' :: [ZPara] -> [ZName] -> String
prevar_display_chann_CChan' spec  [] = ""
prevar_display_chann_CChan' spec [x] = x
prevar_display_chann_CChan' spec (x:xs) = x ++ ", " ++ (prevar_display_chann_CChan' spec xs)
\end{code}
\begin{code}
prevar_display_chann_CChanDecl :: [ZPara] -> [(String, ZExpr)] -> String
prevar_display_chann_CChanDecl spec [] = ""
prevar_display_chann_CChanDecl spec [(a,b)]
  = "channel " ++ a
    ++ " : " ++ (prevar_mapping_ZExpr (get_delta_names1 spec) b)
prevar_display_chann_CChanDecl spec (x:xs)
  = "channel " ++ prevar_display_chann_CChan' spec (map fst (x:xs))
    ++ " : " ++ (prevar_mapping_ZExpr (get_delta_names1 spec) (snd x))
\end{code}
\subsection{Mapping Circus channel sets}

\begin{circus}
  \Upsilon_{CSExp}(\lchanset xs \rchanset) \defs \tco{\{| } \Upsilon_{CSExp\_get\_cs}(xs) \tco{ |\}}\\
  \Upsilon_{CSExp}(CS1 \setminus CS2) \defs
       \tco{diff(}\Upsilon_{CSExp}(CS1)\tco{,}\Upsilon_{CSExp}(CS2)\tco{)}\\
  \Upsilon_{CSExp}(CS1 \cup CS2) \defs
       \tco{union(}\Upsilon_{CSExp}(CS1)\tco{,}\Upsilon_{CSExp}(CS2)\tco{)}\\
  \Upsilon_{CSExp}(CS1 \cap CS2) \defs
       \tco{inter(}\Upsilon_{CSExp}(CS1)\tco{,}\Upsilon_{CSExp}(CS2)\tco{)}\\
  \Upsilon_{CSExp}(\lchanset \rchanset) \defs \tco{\{\}}\\
  \Upsilon_{CSExp}(CS) \defs \tco{CS}
\end{circus}
    \begin{provs}
      \item $CS$, $CS1$ and $CS2$ are channel sets, $CSExp$.
    \end{provs}
\begin{code}
prevar_mapping_CSExp :: CSExp -> String
prevar_mapping_CSExp (CChanSet xs) = "{| " ++ (prevar_mapping_CSExp_prevar_get_cs xs) ++ " |}"
prevar_mapping_CSExp (ChanSetDiff a b) = "diff("++(prevar_mapping_CSExp a)++","++(prevar_mapping_CSExp b)++")"
prevar_mapping_CSExp (ChanSetInter a b) = "inter("++(prevar_mapping_CSExp a)++","++(prevar_mapping_CSExp b)++")"
prevar_mapping_CSExp (ChanSetUnion a b) = "union("++(prevar_mapping_CSExp a)++","++(prevar_mapping_CSExp b)++")"
prevar_mapping_CSExp (CSEmpty) = "{ }"
prevar_mapping_CSExp (CSExpr zn) = zn
\end{code}
Transforms a $CChanSet$ channel set into a list of channels in the CSP format
\begin{code}
prevar_mapping_CSExp_prevar_get_cs :: [[Char]] -> [Char]
prevar_mapping_CSExp_prevar_get_cs [] = ""
prevar_mapping_CSExp_prevar_get_cs [x] = x
prevar_mapping_CSExp_prevar_get_cs (c:cs) = c ++ "," ++ (prevar_mapping_CSExp_prevar_get_cs cs)
\end{code}

\subsection{Mapping Circus Processes Declaration}
This is the translation rules for $ProcDecl$. Up to the date, we don't have a translation rule for generic processes.
\begin{circus}
  \Upsilon_{ProcDecl}(\circprocess P \circdef ProcDef) \defs \tco{P} \Upsilon_{ProcessDef}(PD)
\end{circus}
    \begin{provs}
      \item $P$ is the name of a \Circus\ process.
      \item$PD$ is the content within $\circbegin \ldots \circend$.
    \end{provs}
\begin{code}
prevar_mapping_ProcDecl ::  [ZPara] -> ProcDecl -> String
--prevar_mapping_ProcDecl procn spec (CGenProcess zn (x:xs) pd)
--  = (show zn) ++ " = "
-- prevar_mapping_ProcDecl spec (CProcess procn (ProcDef
--     (ProcStalessMain xs (CSPRepIntChoice bind (CSPHide a (CSExpr "MEMI"))))))
--   = "\n" ++ procn ++"("++ (prevar_mapping_ZGenFilt_list spec bind) ++ ") =" ++ ma
--   where
--     ma = (if (xs == [])
--           then ma1
--           else "\n  let" ++ (prevar_mapping_PPar_list procn spec xs) ++ "\n  within " ++ ma1)
--     ma1 = "\n     let "
--             ++ restr
--             ++"\n     within"
--             ++(prevar_mapping_CAction procn args spec (CSPHide a (CSExpr "MEMI")))++"\n"
--     zn =  get_znames_from_NAME spec
--     znames = remdups $ map nfst (select_f_zbr zn)
--     ztypes = remdups $ map ntrd (select_f_zbr zn)
--     restr = mk_charll_to_charl "\n        " $
--        map (mk_restrict (concat $ map (\(va,b,c) -> (if (Subs.isPrefixOf ("sv"++"_") va) || (Subs.isPrefixOf ("lv"++"_") va) then [(va,b,c)] else [])) (select_f_zbr zn))) (get_binding_types bind)
--     restn = mk_charll_to_charl ", " $ map mk_restrict_name (get_binding_types bind)
prevar_mapping_ProcDecl spec (CProcess p pd)
  = "\n" ++ p ++ (prevar_mapping_ProcessDef p [] spec pd)
prevar_mapping_ProcDecl spec _
  = ""
\end{code}

\subsection{Mapping Circus Processes Definition}
NOTE:Process definition index is not yet defined.
\begin{circus}
  \Upsilon_{ProcessDef}(Proc) \defs \tco{= } \Upsilon_{CProc}(Proc)\\
  \Upsilon_{ProcessDef}(Decl \circspot Proc) \defs \tco{(}\Upsilon_{ZGenFilt\_list}\tco{)= }\Upsilon_{CProc}(Proc)
\end{circus}
    \begin{provs}
      \item $Proc$ is the process content.
      \item $Decl$ are the local variables for the process $Proc$ environment.
    \end{provs}
\begin{code}
prevar_mapping_ProcessDef :: ZName -> String -> [ZPara] -> ProcessDef -> String
prevar_mapping_ProcessDef procn args spec (ProcDef cp)
  = " = " ++ (prevar_mapping_CProc procn args spec cp)
prevar_mapping_ProcessDef procn args spec (ProcDefSpot xl pd)
  = "("++(prevar_mapping_ZGenFilt_list spec xl ) ++ ")" ++ (prevar_mapping_ProcessDef procn (prevar_mapping_ZGenFilt_list spec xl ) spec pd)
prevar_mapping_ProcessDef procn args spec (ProcDefIndex xl pd)
  = "("++(prevar_mapping_ZGenFilt_list spec xl ) ++ ")" ++ (prevar_mapping_ProcessDef procn (prevar_mapping_ZGenFilt_list spec xl ) spec pd)
-- prevar_mapping_ProcessDef procn args spec (ProcDefIndex (x:xs) pd)
--  = "("++(getZGenFilt (x:xs)) ++ ") = " ++ (prevar_mapping_CProc procn args spec cp)
\end{code}
The two functions below will make the list of parameters of the \CSPM\ process, those from the $Decl$ part of the \Circus\ process.
\begin{code}
prevar_mapping_ZGenFilt_list :: [ZPara] -> [ZGenFilt] -> String
prevar_mapping_ZGenFilt_list spec [x]
  = (prevar_mapping_ZGenFilt spec x)
prevar_mapping_ZGenFilt_list spec (x:xs)
  = (prevar_mapping_ZGenFilt spec x) ++ "," ++ (prevar_mapping_ZGenFilt_list  spec xs)
\end{code}
\begin{code}
prevar_mapping_ZGenFilt :: [ZPara] -> ZGenFilt -> String
prevar_mapping_ZGenFilt  spec (Choose v _) = nfst v
\end{code}

\subsection{Mapping Circus Processes}
In this section, we list all the mapping functions for the possible behaviours of a \Circus\ process. Note that $CGenProc$ ($N[Exp^{+}]$), $CSimpIndexProc$, and $CParamProc$ ($N(Exp^{+})$) are not yet implemented.

\begin{circus}
  \Upsilon_{CProc}(P1 \extchoice P2) \defs \Upsilon_{CProc}(P1)\tco{ [] }\Upsilon_{CProc}(P2) \\
  \Upsilon_{CProc}(P1 \circhide CS) \defs \Upsilon_{CProc}(P1)~\tco{\textbackslash}~\Upsilon_{Pred_{CS}}(CS) \\
  \Upsilon_{CProc}(P1 \intchoice P2) \defs \Upsilon_{CProc}(P1)~\tco{|\textasciitilde|}~\Upsilon_{CProc}(P2) \\
  \Upsilon_{CProc}(P1 \interleave P2) \defs \Upsilon_{CProc}(P1)~\tco{|||}~\Upsilon_{CProc}(P2) \\
  \Upsilon_{CProc}(P) \defs \tco{P} \\
  \Upsilon_{CProc}(P1 \lpar CS \rpar P2) \defs \Upsilon_{CProc}(P1)~\tco{[|}~\Upsilon_{Pred_{CS}}(CS)~\tco{|]}~\Upsilon_{CProc}(P2) \\
  \Upsilon_{CProc}(P1 \circseq P2) \defs \Upsilon_{CProc}(P1)~\tco{;}~\Upsilon_{CProc}(P2) \\
  \Upsilon_{CProc}(\Extchoice x:S \circspot P1) \defs \tco{[] x :}~\Upsilon_{ZExpr}(S)~\tco{@}~\Upsilon_{CProc}(P2) \\
  \Upsilon_{CProc}(\Intchoice x:S \circspot P1) \defs \tco{|\textasciitilde| x :}~\Upsilon_{ZExpr}(S)~\tco{@}~\Upsilon_{CProc}(P2) \\
  \Upsilon_{CProc}(\Interleave x:S \circspot P1) \defs \tco{|\textasciitilde| x :}~\Upsilon_{ZExpr}(S)~\tco{@}~\Upsilon_{CProc}(P2) \\
  \Upsilon_{CProc}(\lpar CS \rpar x:S \circspot P1) \defs ~\tco{[|}~\Upsilon_{Pred_{CS}}(CS)~\tco{|] x :}~\Upsilon_{ZExpr}(S)~\tco{@}~\Upsilon_{CProc}(P2) \\
  \Upsilon_{CProc}(\Semi x:S \circspot P1) \defs \tco{; x :}~\Upsilon_{ZExpr}(S)~\tco{@}~\Upsilon_{CProc}(P2) \\
  \Upsilon_{CProc}(\circbegin AL \circspot MA \circend) \defs\\
  \qquad \tco{let} \Upsilon_{PPar\_list}(AL)\\
  \qquad \tco{within}~\Upsilon_{CAction}(MA) \\
  \Upsilon_{CProc}(\circbegin \circspot MA \circend) \defs \Upsilon_{CAction}(MA)\\
  \Upsilon_{CProc}(Proc[NL:=EL]) \defs \tco{P[[}~\Upsilon_{Rename}(NL,EL)~\tco{]]}


\end{circus}
    \begin{provs}
      \item $P$ is a process name.
      \item $P1$ and $P2$ is a process $CProc$
      \item $cs$ is a channel set $CSExp$
      \item $MA$ is the main action of the \Circus\ process.
      \item $AL$ is the list of actions.
    \end{provs}
\begin{code}
prevar_mapping_CProc :: ZName -> String -> [ZPara] -> CProc -> String
prevar_mapping_CProc procn args spec (CExtChoice a b)
  = "( " ++ (prevar_mapping_CProc procn args spec a)
    ++ " [] "
    ++ (prevar_mapping_CProc procn args spec b) ++ " )"
prevar_mapping_CProc procn args spec (CHide a cs)
  = "( " ++ (prevar_mapping_CProc procn args spec a)
    ++  " \\ "
    ++ prevar_mapping_predicate_cs (cs) ++ " )"
prevar_mapping_CProc procn args spec (CIntChoice a b)
  = "( " ++ (prevar_mapping_CProc procn args spec a)
    ++ " |~| "
    ++ (prevar_mapping_CProc procn args spec b) ++ " )"
prevar_mapping_CProc procn args spec (CInterleave a b)
  = "( " ++ (prevar_mapping_CProc procn args spec a)
    ++ " ||| "
    ++ (prevar_mapping_CProc procn args spec b) ++ " )"
prevar_mapping_CProc procn args spec (CircusProc zn)
  = zn
prevar_mapping_CProc procn args spec (CParParal cs a b)
  = "( " ++ (prevar_mapping_CProc procn args spec a)
    ++ " [| "
    ++ prevar_mapping_predicate_cs (cs)
    ++ " |] "
    ++ (prevar_mapping_CProc procn args spec b) ++ " )"
prevar_mapping_CProc procn args spec (CSeq a b)
  = "( " ++ (prevar_mapping_CProc procn args spec a)
    ++ " ; "
    ++ (prevar_mapping_CProc procn args spec b) ++ " )"
prevar_mapping_CProc procn args spec (CRepExtChProc [(Choose (x,[],tx) s)] a)
  = "[] "
    ++  x
    ++ " : "
    ++ (prevar_mapping_ZExpr (get_delta_names1 spec) s)
    ++ " @ "
    ++ (prevar_mapping_CProc procn args spec a)
prevar_mapping_CProc procn args spec (CRepIntChProc [(Choose (x,[],tx) s)] a)
  = "|~| "
    ++  x
    ++ " : "
    ++ (prevar_mapping_ZExpr (get_delta_names1 spec) s)
    ++ " @ "
    ++ (prevar_mapping_CProc procn args spec a)
prevar_mapping_CProc procn args spec (CRepInterlProc [(Choose (x,[],tx) s)] a)
  = "|||"
    ++  x
    ++ " : "
    ++ (prevar_mapping_ZExpr (get_delta_names1 spec) s)
    ++ " @ "
    ++ (prevar_mapping_CProc procn args spec a)
prevar_mapping_CProc procn args spec (CRepParalProc cse [(Choose (x,[],tx) s)] a)
  = " [| "
    ++ prevar_mapping_predicate_cs (cse)
    ++ " |] "
    ++  x
    ++ " : "
    ++ (prevar_mapping_ZExpr (get_delta_names1 spec) s)
    ++ " @ "
    ++ (prevar_mapping_CProc procn args spec a)
prevar_mapping_CProc procn args spec (CRepSeqProc [(Choose (x,[],tx) s)] a)
  = "; "
    ++  x
    ++ " : "
    ++ (prevar_mapping_ZExpr (get_delta_names1 spec) s)
    ++ " @ "
    ++ (prevar_mapping_CProc procn args spec a)
prevar_mapping_CProc procn args spec (ProcStalessMain al ma)
  | al == [] = "" ++ (prevar_mapping_CAction procn args spec ma)
  | otherwise = "\n  let" ++ (prevar_mapping_PPar_list procn spec al)
    ++ "\n  within " ++ (prevar_mapping_CAction procn args spec ma)
prevar_mapping_CProc procn args spec (CParamProc zn xl)
   = zn ++ "(" ++ concat (map (prevar_mapping_ZExpr (get_delta_names1 spec)) xl) ++ ")"
prevar_mapping_CProc procn args spec (CProcRename n (zv:zvs) (xp:xps))
  = (prevar_mapping_CProc procn args spec n) ++"[["++ (prevar_mapping_rename procn spec (zv:zvs) (xp:xps)) ++"]]"
prevar_mapping_CProc procn args spec x
  = fail ("not implemented by prevar_mapping_CProc: " ++ show x)
\end{code}

This function maps any renaming, to its equivalent syntax in \CSPM.
\begin{circus}
  \Upsilon_{Rename}(x\#xs,y\#xs) \defs \Upsilon_{Comm}(x)~\tco{<- }\Upsilon_{Comm}(y)\tco{ , }\Upsilon_{Rename}(xs,xs) \\
  \Upsilon_{Rename}([x],[y]=) \defs \Upsilon_{Comm}(x)~\tco{<- }\Upsilon_{Comm}(y)
  \end{circus}

\begin{code}
prevar_mapping_rename :: ZName -> [ZPara] -> [Comm] -> [Comm] -> [Char]
prevar_mapping_rename procn spec [y] [x]
  = (prevar_mapping_Comm procn spec y)++ " <- "++ (prevar_mapping_Comm procn spec x)
prevar_mapping_rename procn spec (y:zvs) (x:xps)
  = (prevar_mapping_Comm procn spec y)++ " <- "++ (prevar_mapping_Comm procn spec x)++", "++(prevar_mapping_rename procn spec zvs xps)
prevar_mapping_rename _ _ [] _ = ""
prevar_mapping_rename _ _ _ [] = ""
\end{code}
\subsection{Mapping Circus Processes Paragraphs}
NOTE: $CNameSet$ and $ProcZPara$ is not yet implemented
\begin{circus}
  \Upsilon_{PPar}(P \circdef Decl \circspot A) \defs~\tco{P(}\Upsilon_{ZGenFilt\_list}(Decl)\tco{) = }\Upsilon_{CAction}(A) \\
  \Upsilon_{PPar}(P \circdef A) \defs~\tco{P = }\Upsilon_{CAction}(A)
  \end{circus}
\begin{code}
prevar_mapping_PPar :: ZName -> String -> [ZPara] -> PPar -> String
prevar_mapping_PPar procn args spec (CParAction m (CircusAction (CSPRecursion "M" (CActionCommand (CVarDecl xs a)))))
  = prevar_mapping_PPar procn args spec (CParAction m (CircusAction (CActionCommand (CVarDecl xs (rem_recursion m a)))))

prevar_mapping_PPar procn args spec (CParAction p (CircusAction (CActionCommand (CVResDecl decl a ))))
  = p
    ++"("
    ++ (prevar_mapping_ZGenFilt_list spec decl)
    ++ ") =\n        "
    ++ (prevar_mapping_CAction procn args spec a)
prevar_mapping_PPar procn args spec (CParAction p (CircusAction (CActionCommand (CVarDecl decl a ))))
  = p
    ++"("
    ++ (prevar_mapping_ZGenFilt_list spec decl)
    ++ ") =\n        "
    ++ (prevar_mapping_CAction procn args spec a)
prevar_mapping_PPar procn args spec (CParAction p pa)
  = p ++ (prevar_mapping_ParAction procn spec pa)
prevar_mapping_PPar procn args spec x
  = fail ("Not implemented by prevar_mapping_PPar: " ++ show x)
--prevar_mapping_PPar procn spec (ProcZPara zp)
--  = undefined
\end{code}
This function just process a list of $PPar$ from within a \Circus\ process printing it one line each.
\begin{code}
prevar_mapping_PPar_list :: ZName -> [ZPara] -> [PPar] -> String
prevar_mapping_PPar_list procn spec []
  = "\n     "
prevar_mapping_PPar_list procn spec (x:xs)
  = "\n     " ++ (prevar_mapping_PPar procn [] spec x) ++ (prevar_mapping_PPar_list procn spec xs)
\end{code}

\subsection{Mapping Parameterised Circus Actions}
\begin{code}
prevar_mapping_ParAction :: ZName -> [ZPara] -> ParAction -> String
prevar_mapping_ParAction procn spec (CircusAction ca)
  = " = " ++ (prevar_mapping_CAction procn [] spec ca)
prevar_mapping_ParAction procn spec (ParamActionDecl xl pa)
  = "("++(prevar_mapping_ZGenFilt_list  spec xl ) ++ ")" ++ (prevar_mapping_ParAction [] spec pa)
\end{code}

\subsection{Mapping Circus Actions}
NOTE: $CActionSchemaExpr$ is not yet implemented.

\begin{code}
prevar_mapping_CAction :: ZName -> String -> [ZPara] -> CAction -> ZName
prevar_mapping_CAction procn args spec (CActionCommand cc)
  = "("++prevar_mapping_CCommand procn spec cc++")"
prevar_mapping_CAction procn args spec (CActionName zn)
  = zn ++ "\n"
prevar_mapping_CAction procn args spec (CSPUnfAction x (CActionName v))
  = x ++"("++v++")\n"
--prevar_mapping_CAction procn args spec (CActionSchemaExpr zse)
--  = undefined
\end{code}
\begin{circus}
\Upsilon_A(c?x : P \then A)
\defs~\tco{c?x :\{x | x <- $\delta(c)$,$\Upsilon_{\mathbb{B}}(P(x))$\} -> $\Upsilon_A(A)$}
\end{circus}

\begin{code}
prevar_mapping_CAction procn args spec (CSPCommAction (ChanComm c [ChanInpPred x p]) a)
  = case np of
    "true" -> c ++ "?"++ x ++ " : { x | x <- "++ (prevar_get_c_chan_type spec c (prevar_get_chan_list spec)) ++ "} ->\n      ("++ (prevar_mapping_CAction procn args spec a)++")"
    _ -> c ++ "?"++ x ++ " : { x | x <- "++ (prevar_get_c_chan_type spec c (prevar_get_chan_list spec)) ++ ", "++ (prevar_mapping_predicate (get_delta_names1 spec) p) ++ "} ->\n      ("++ (prevar_mapping_CAction procn args spec a)++")"
    where
      np = (prevar_mapping_predicate (get_delta_names1 spec) p)
\end{code}
\begin{circus}
\Upsilon_A(c?x\then A)\circdef~\tco{c?x -> } \Upsilon_A(A)
\end{circus}
\begin{code}
prevar_mapping_CAction procn args spec (CSPCommAction (ChanComm c [ChanInp x]) CSPSkip)
  = (prevar_get_channel_name spec (ChanComm c [ChanInp x]))
    ++ " -> SKIP"
prevar_mapping_CAction procn args spec (CSPCommAction (ChanComm c [ChanInp x]) a)
  = (prevar_get_channel_name spec (ChanComm c [ChanInp x]))
    ++ " ->\n      "
    ++ prevar_mapping_CAction procn args spec (a)
\end{code}

\begin{circus}
\Upsilon_A(c!v \then\ A)\circdef~\tco{c!v -> }\Upsilon_A(A)
\end{circus}
\begin{code}
prevar_mapping_CAction procn args spec (CSPCommAction (ChanComm c [ChanOutExp (ZVar (x,[],tx))]) CSPSkip)
  = (prevar_get_channel_name spec (ChanComm c [ChanOutExp (ZVar (x,[],tx))]))
    ++ " -> SKIP"
prevar_mapping_CAction procn args spec (CSPCommAction (ChanComm c [ChanOutExp (ZVar (x,[],tx))]) a)
  = (prevar_get_channel_name spec (ChanComm c [ChanOutExp (ZVar (x,[],tx))]))
    ++ " ->\n      "
    ++ prevar_mapping_CAction procn args spec (a) ++ ""

prevar_mapping_CAction procn args spec (CSPCommAction (ChanComm c lst) CSPSkip)
  = (prevar_get_channel_name spec (ChanComm c lst))
    ++ " -> SKIP"
prevar_mapping_CAction procn args spec (CSPCommAction (ChanComm c lst) a)
  = (prevar_get_channel_name spec (ChanComm c lst))
    ++ " ->\n      "
    ++ prevar_mapping_CAction procn args spec (a)
\end{code}


\begin{circus}
\Upsilon_A(c\then\ A)\circdef~\tco{c -> }\Upsilon_A(A)
\end{circus}
\begin{code}
prevar_mapping_CAction procn args spec (CSPCommAction c a)
  = (prevar_get_channel_name spec c)
    ++ " ->\n      "
    ++ prevar_mapping_CAction procn args spec (a) ++ ""
\end{code}

\begin{circus}
\Upsilon_A(A \extchoice B) \circdef~\Upsilon_A(A) ~\tco{[]} \Upsilon_A(B)
\end{circus}
\begin{code}
prevar_mapping_CAction procn args spec (CSPExtChoice a b)
  = "( " ++ prevar_mapping_CAction procn args spec (a)
    ++ "\n      [] "
    ++ prevar_mapping_CAction procn args spec (b) ++ ")"
\end{code}

\begin{circus}
\Upsilon_A(g \& A)\circdef~\Upsilon_{\mathbb{B}}(g)~\tco{\&}~\Upsilon_A(A)
\end{circus}
\begin{code}
prevar_mapping_CAction procn args spec (CSPGuard g ca)
 -- I'm using the True Guard
  -- and False Guard laws directly
  -- into the translation.
  = case guard of
    "true" -> (prevar_mapping_CAction procn args spec ca) -- True Law (true & A = A)
    "false" -> "STOP"                   -- False Law (false & A = Stop)
    _ -> "( " ++ guard ++ "   & " ++ (prevar_mapping_CAction procn args spec ca) ++ " )"
  where guard = (prevar_mapping_predicate (get_delta_names1 spec) g)
\end{code}

\begin{circus}
\Upsilon_A(A \circhide cs) \circdef~\Upsilon_A(A)~\tco{\textbackslash} \Upsilon_{\mathbb{P}^{cs}} (cs)
\end{circus}
\begin{code}
prevar_mapping_CAction procn args spec (CSPHide a cs)
  = "( " ++ prevar_mapping_CAction procn args spec (a)
    ++  "\\"
    ++ prevar_mapping_predicate_cs (cs) ++ " )"
\end{code}

\begin{circus}
\Upsilon_A(A \intchoice B) \circdef~\Upsilon_A(A)~\tco{|\textasciitilde|} \Upsilon_A(B)
\end{circus}
\begin{code}
prevar_mapping_CAction procn args spec (CSPIntChoice a b)
  = "( " ++ prevar_mapping_CAction procn args spec (a)
    ++ "\n      |~| "
    ++ prevar_mapping_CAction procn args spec (b) ++ " )"
\end{code}
\begin{code}
prevar_mapping_CAction procn args spec (CSPInterleave ca cb)
   = "( " ++ prevar_mapping_CAction procn args spec (ca)
     ++ "\n      ||| "
     ++ prevar_mapping_CAction procn args spec (cb) ++ " )"
\end{code}

\begin{circus}
\Upsilon_A(A \linter ns1 | ns2 \rinter B) \circdef~\Upsilon_A(A)~\tco{|||}~\Upsilon_A(B)
\end{circus}
\begin{code}
prevar_mapping_CAction procn args spec (CSPNSInter ns1 ns2 a b)
  = "( " ++ prevar_mapping_CAction procn args spec (a)
    ++ "\n     |||"
    ++ prevar_mapping_CAction procn args spec (b) ++ " )"
\end{code}

\begin{circus}
\Upsilon_A(A\lpar ns1|cs|ns2\rpar B)\circdef~\Upsilon_A(A)~\tco{[|}~\Upsilon_{\mathbb{P}^{cs}}(cs)\tco{|]}\Upsilon_A(B)
\end{circus}
\begin{code}

prevar_mapping_CAction procn args spec (CSPNSParal _ (CSExpr "MEMI") _ ca (CSPParAction "Memory" zb))
  = "( " ++ prevar_mapping_CAction procn args spec ca
   ++ "\n      [| MEMI |] Memory("++args++"))"
prevar_mapping_CAction procn args spec (CSPNSParal ns1 cs ns2 a b)
 = "( " ++ prevar_mapping_CAction procn args spec (a)
   ++ "\n      [| "
   ++ prevar_mapping_predicate_cs (cs)
   ++ " |] \n      "
   ++ prevar_mapping_CAction procn args spec (b) ++ " )"
\end{code}
\begin{code}


prevar_mapping_CAction procn args spec (CSPParAction zn xl)
  = zn ++ "(" ++ joinBy "," (map (prevar_mapping_ZExpr (get_delta_names1 spec)) xl) ++ ")"
\end{code}
% \begin{code}
% prevar_mapping_CAction procn args spec (CSPParal cs a b)
%   = prevar_mapping_CAction procn args spec (a)
%     ++ "\n      [| "
%     ++ prevar_mapping_predicate_cs (cs)
%     ++ " |]\n      "
%     ++ prevar_mapping_CAction procn args spec (b)
% \end{code}

\begin{circus}
\Upsilon (\circmu X \circspot\ A(X )) \circdef~\tco{let Arec =}~\Upsilon_A(A(A_{rec}))~\tco{within Arec}
\end{circus}
\begin{code}
prevar_mapping_CAction procn args spec (CSPRecursion x (CActionCommand (CVarDecl [Choose (b,[],"") (ZVar (c,[],""))] cs)))
  = "( " ++ "let "
    ++ x ++ "("++b++")"
    ++ " = "
    ++ prevar_mapping_CAction procn args spec (cs)
    ++ " within "
    ++ x ++ "("++b++")" ++ " )"
prevar_mapping_CAction procn args spec (CSPRecursion x a)
  = "( " ++ "let "
    ++ x
    ++ " = "
    ++ prevar_mapping_CAction procn args spec (a)
    ++ " within "
    ++ x ++ " )"

\end{code}

\begin{circus}
\Upsilon_A(\Extchoice x : S \circspot A)\circdef~\tco{[] x :}~\Upsilon_{\mathbb{P}}(S)~\tco{@}~\Upsilon_A(A)
\end{circus}
\begin{code}
prevar_mapping_CAction procn args spec (CSPRepExtChoice [(Choose (x,[],tx) s)] a)
  = "( " ++ "[] "
    ++  x
    ++ " : "
    ++ (prevar_mapping_ZExpr (get_delta_names1 spec) s)
    ++ " @ "
    ++ prevar_mapping_CAction procn args spec (a) ++ " )"
\end{code}

\begin{circus}
\Upsilon_A(\Intchoice x : S \circspot A)\circdef~\tco{|\textasciitilde| x :}~\Upsilon_{\mathbb{P}}(S)~\tco{@}~\Upsilon_A(A)
\end{circus}
\begin{code}


-- first case is for the BINDING
prevar_mapping_CAction procn args spec (CSPRepIntChoice bdls (CSPHide (CSPNSParal [] (CSExpr "MEMI") bs1 (CSPSeq ca (CSPCommAction (ChanComm "terminate" []) CSPSkip)) (CSPParAction "Memory" zb)) (CSExpr "MEMI")))
    = "\n     let "++ restr
       ++"\n     within"
       ++"\n        |~| "++ bnd ++" @ "++(prevar_mapping_CAction procn args spec (CSPHide (CSPNSParal [] (CSExpr "MEMI") bs1 (CSPSeq ca (CSPCommAction (ChanComm "terminate" []) CSPSkip)) (CSPParAction "Memory" zb)) (CSExpr "MEMI")))++"\n"
       where
         zn =  get_znames_from_NAME spec
         znames = remdups $ map nfst (select_f_zbr zn)
         ztypes = remdups $ map ntrd (select_f_zbr zn)
         restr = mk_charll_to_charl "\n        " $
            map (mk_restrict (concat $ map (\(va,b,c) -> (if (Subs.isPrefixOf ("sv"++"_") va) || (Subs.isPrefixOf ("lv"++"_") va) then [(va,b,c)] else [])) (select_f_zbr zn))) (get_binding_types bdls)
         bnd = mk_charll_to_charl ", " $ map mk_binding_list (get_binding_types bdls)
         restn = mk_charll_to_charl ", " $ map mk_restrict_name (get_binding_types bdls)

-- otherwise...
prevar_mapping_CAction procn args spec (CSPRepIntChoice [(Choose (x,[],tx) (ZVar (t,_,tx1)))] a)
  = "( " ++ "|~| "
    ++  x
    ++ " : "
    ++ t
    ++ " @\n         "
    ++ prevar_mapping_CAction procn args spec (a) ++ " )"
prevar_mapping_CAction procn args spec (CSPRepIntChoice [(Choose (x,[],tx) s)] a)
      = "( " ++ "|~| "
        ++  x
        ++ " : "
        ++ (prevar_mapping_ZExpr (get_delta_names1 spec) s)
        ++ " @\n         "
        ++ prevar_mapping_CAction procn args spec (a) ++ " )"
\end{code}

\begin{code}
prevar_mapping_CAction procn args spec (CSPRepInterl [(Choose (x,[],tx) s)] a)
  = "( " ++ "||| "
    ++  x
    ++ " : "
    ++ (prevar_mapping_ZExpr (get_delta_names1 spec) s)
    ++ " @ "
    ++ prevar_mapping_CAction procn args spec (a) ++ " )"
\end{code}

\begin{circus}
\Upsilon_A(\Interleave x : S \circspot \lpar \emptyset \rpar A) \circdef~\tco{||| x:}\Upsilon_{\mathbb{P}}(S)~\tco{@}~\Upsilon_A(A)
\end{circus}
\begin{code}
prevar_mapping_CAction procn args spec (CSPRepInterlNS [(Choose (x,[],tx) s)] [] a)
  = "( " ++ "||| "
    ++  x
    ++ " : "
    ++ (prevar_mapping_ZExpr (get_delta_names1 spec) s)
    ++ " @ "
    ++ prevar_mapping_CAction procn args spec (a) ++ " )"
\end{code}

\begin{circus}
\Upsilon_A(\lpar cs \rpar x : S \circspot  A)\circdef~\tco{[|}\Upsilon_{\mathbb{P}^{cs}}(cs)\tco{|] x :}\Upsilon_{\mathbb{P}}(S)~\tco{@}~\Upsilon_A(A)
\end{circus}
\begin{code}
prevar_mapping_CAction procn args spec (CSPRepParal cs [(Choose (x,[],tx) s)] a)
  = "( " ++ "[| "
    ++ prevar_mapping_predicate_cs (cs)
    ++ " |] "
    ++  x
    ++ " : "
    ++ (prevar_mapping_ZExpr (get_delta_names1 spec) s)
    ++ " @ "
    ++ prevar_mapping_CAction procn args spec (a) ++ " )"
\end{code}

\begin{circus}
\Upsilon_A(\lpar cs \rpar x : S \circspot \lpar \emptyset \rpar A)\circdef~\tco{[|}\Upsilon_{\mathbb{P}^{cs}}(cs)\tco{|] x :}\Upsilon_{\mathbb{P}}(S)~\tco{@}~\Upsilon_A(A)
\end{circus}
\begin{code}
prevar_mapping_CAction procn args spec (CSPRepParalNS cs [(Choose (x,[],tx) s)] [] a)
  = "( " ++ "[| "
    ++ prevar_mapping_predicate_cs (cs)
    ++ " |] "
    ++  x
    ++ " : "
    ++ (prevar_mapping_ZExpr (get_delta_names1 spec) s)
    ++ " @ "
    ++ prevar_mapping_CAction procn args spec (a) ++ " )"
\end{code}

\begin{circus}
\Upsilon_A(\Semi x : S \circspot A)\circdef~\tco{; x :}\Upsilon_{seq}(S)~\tco{@}~\Upsilon_A(A)
\end{circus}
\begin{code}
prevar_mapping_CAction procn args spec (CSPRepSeq xs a)
  = "( " ++  c_to_csp_CSPRepSeq spec xs
    ++ prevar_mapping_CAction procn args spec (a) ++ " )"
\end{code}

\begin{circus}
\Upsilon_A(A \circseq B) \circdef~\Upsilon_A(A)~\tco{;}~\Upsilon_A(B)
\end{circus}
\begin{code}
prevar_mapping_CAction procn args spec (CSPSeq a b)
  = "( " ++ prevar_mapping_CAction procn args spec (a)
    ++ ";\n      "
    ++ prevar_mapping_CAction procn args spec (b) ++ " )"
\end{code}

\begin{circus}
\Upsilon_A(\Skip) \defs~\tco{SKIP}
\end{circus}
\begin{code}
prevar_mapping_CAction procn args spec (CSPSkip)
  = "SKIP"
\end{code}

\begin{circus}
\Upsilon_A(\Stop) \defs~\tco{STOP}
\end{circus}
\begin{code}
prevar_mapping_CAction procn args spec (CSPStop)
  = "STOP"
\end{code}

\begin{circus}
\Upsilon_A(\Chaos) \defs~\tco{CHAOS}
\end{circus}
\begin{code}
prevar_mapping_CAction procn args spec (CSPChaos)
  = "CHAOS"
\end{code}
\begin{code}
prevar_mapping_CAction procn args spec x
  = fail ("not implemented by prevar_mapping_CAction: " ++ show x)
\end{code}

\subsection{Mapping Circus Commands}
NOTE: $CAssumpt$, $CommandBrace$, $CommandBracket$ not implemented yet
\begin{code}
prevar_mapping_CCommand :: ZName -> [ZPara] -> CCommand -> ZName
prevar_mapping_CCommand procn spec (CAssign (x:xs) (y:ys))
  = error ("Assignments are not available in CSP")
prevar_mapping_CCommand procn spec (CAssumpt (x:xs) zpa zpb)
  = error ("Assumptions are not available in CSP")
prevar_mapping_CCommand procn spec (CIf cga)
  = prevar_mapping_CGActions procn spec cga
-- prevar_mapping_CCommand procn spec (CommandBrace zp)
--   = undefined
-- prevar_mapping_CCommand procn spec (CommandBracket zp)
--   = undefined
-- prevar_mapping_CCommand procn spec (CResDecl (x:xs) ca)
--   = undefined
{-
prevar_mapping_CCommand procn spec (CVarDecl bds ca)
 = "let "++ restr
    ++"\n        within"
    ++"\n        |~| "++ bnd ++" @ Memorise("++(prevar_mapping_CAction procn args spec ca)++",\n         "++restn++")\n"
    where
      zn =  get_znames_from_NAME spec
      znames = remdups $ map nfst (select_f_zbr zn)
      ztypes = remdups $ map ntrd (select_f_zbr zn)
      restr = mk_charll_to_charl "\n        " $
         map (mk_restrict (concat (map (\(va,b,c) -> if (Subs.isPrefixOf ("sv"++"_") va) || (Subs.isPrefixOf ("lv"++"_") va) then [(va,b,c)] else []) (select_f_zbr zn)))) ztypes
      bnd = mk_charll_to_charl ", " $ map mk_binding_list ztypes
      restn = mk_charll_to_charl ", " $ map mk_restrict_name ztypes
-}
prevar_mapping_CCommand procn spec (CValDecl (x:xs) ca)
   = ""
-- prevar_mapping_CCommand procn spec (CVResDecl (x:xs) ca)
--   = undefined
prevar_mapping_CCommand procn spec x
  = fail ("not implemented by prevar_mapping_CCommand: " ++ show x)
\end{code}

\subsection{Mapping Circus Guarded Actions}
\begin{code}
prevar_mapping_CGActions :: ZName -> [ZPara] -> CGActions -> ZName
prevar_mapping_CGActions procn spec (CircThenElse cga1 cga2)
  = (prevar_mapping_CGActions procn spec cga1) ++ " [] " ++ (prevar_mapping_CGActions procn spec cga2)
prevar_mapping_CGActions procn spec (CircGAction zp ca)
  = (prevar_mapping_predicate (get_delta_names1 spec) zp) ++ " &\n         " ++ (prevar_mapping_CAction procn [] spec ca)
\end{code}

\subsection{Mapping Channel Communication}
\begin{code}
prevar_mapping_Comm :: ZName -> [ZPara] -> Comm -> String
prevar_mapping_Comm procn spec (ChanComm zn xs)
  = zn ++ (prevar_mapString (prevar_mapping_CParameter procn) spec xs)
prevar_mapping_Comm procn spec (ChanGenComm zn xs ys)
  = error ("ChanGenComm not yet implemented")
\end{code}

\begin{code}
prevar_mapString :: (t1 -> t -> String) -> t1 -> [t] -> String
prevar_mapString f s [] = ""
prevar_mapString f s (x:xs) = (f s x) ++ (prevar_mapString f s xs)
\end{code}
\begin{code}
prevar_mapping_CParameter :: ZName -> [ZPara] -> CParameter -> ZName
prevar_mapping_CParameter procn spec (ChanInp zn)
  = "?"++zn

prevar_mapping_CParameter procn spec (ChanInpPred zn (ZPSchema (ZSRef (ZSPlain p _) [] [])))
  = "?"++zn ++":"++ p
prevar_mapping_CParameter procn spec (ChanInpPred zn zp)
  = "?"++zn ++":"++ (prevar_mapping_predicate (get_delta_names1 spec) zp)
prevar_mapping_CParameter procn spec (ChanOutExp ze)
  = prevar_mapping_CParameter procn spec (ChanDotExp ze)
prevar_mapping_CParameter procn spec (ChanDotExp ze)
  = "."++(prevar_mapping_ZExpr (get_delta_names1 spec) ze)
\end{code}

\subsection{Mapping Circus Namesets}
\begin{code}

-- prevar_mapping_NSExp procn spec ([])
--   = undefined
-- prevar_mapping_NSExp procn spec (NSExprMult (x:xs))
--   = undefined
-- prevar_mapping_NSExp procn spec (NSExprSngl zn)
--   = undefined
-- prevar_mapping_NSExp procn spec (NSHide nse1 nse2)
--   = undefined
-- prevar_mapping_NSExp procn spec (NSIntersect nse1 nse2)
--   = undefined
-- prevar_mapping_NSExp procn spec (NSUnion nse1 nse2)
--   = undefined
prevar_mapping_NSExp procn spec x
  = fail ("not implemented by prevar_mapping_NSExp: " ++ show x)
\end{code}

\section{Mapping Functions from Circus to CSP - Based on D24.1 - COMPASS}


\subsection{Mapping Functions for Predicates}

\begin{code}
prevar_mapping_predicate :: [ZName] -> ZPred -> String
-- NOt sure what "if then  else" is about
-- prevar_mapping_predicate lst (ZIf_Then_Else b x1 x2)
--   = "if " ++ (prevar_mapping_predicate lst b) ++
--     " then  " ++ (prevar_mapping_predicate lst x1) ++
--     " else " ++ (prevar_mapping_predicate lst x2)
prevar_mapping_predicate lst ( (ZMember (ZTuple [a,b]) (ZVar ("\\geq",[],[]))))
  = "(" ++ (prevar_mapping_ZExpr lst a) ++ " >= " ++ (prevar_mapping_ZExpr lst b)++")"
prevar_mapping_predicate lst ( (ZMember (ZTuple [a,b]) (ZVar (">",[],[]))))
  = "(" ++ (prevar_mapping_ZExpr lst a) ++ " > " ++ (prevar_mapping_ZExpr lst b)++")"
prevar_mapping_predicate lst ( (ZMember (ZTuple [a,b]) (ZVar ("\\leq",[],[]))))
  = "(" ++ (prevar_mapping_ZExpr lst a) ++ " <= " ++ (prevar_mapping_ZExpr lst b)++")"
prevar_mapping_predicate lst ( (ZMember (ZTuple [a,b]) (ZVar ("<",[],[]))))
  = "(" ++ (prevar_mapping_ZExpr lst a) ++ " < " ++ (prevar_mapping_ZExpr lst b)++")"
prevar_mapping_predicate lst ( (ZNot (ZEqual a b)))
  = "(" ++ (prevar_mapping_ZExpr lst a) ++ " != " ++ (prevar_mapping_ZExpr lst b)++")"
prevar_mapping_predicate lst ( (ZEqual a b))
  = "(" ++ (prevar_mapping_ZExpr lst a) ++ " == " ++ (prevar_mapping_ZExpr lst b)++")"
prevar_mapping_predicate lst (ZOr a b)
  = "(" ++ (prevar_mapping_predicate lst a) ++ " or " ++ (prevar_mapping_predicate lst b)++")"
prevar_mapping_predicate lst (ZAnd a b)
  = "(" ++ (prevar_mapping_predicate lst a) ++ " and " ++ (prevar_mapping_predicate lst b)++")"
prevar_mapping_predicate lst ( (ZNot b))
  = "not (" ++ (prevar_mapping_predicate lst b)++")"
prevar_mapping_predicate lst (ZPSchema (ZSRef (ZSPlain "\\true" _) [] []))
  = "true"
prevar_mapping_predicate lst (ZPSchema (ZSRef (ZSPlain "\\false" _) [] []))
  = "false"
prevar_mapping_predicate lst (ZTrue{reason=[]})
  = "true"
prevar_mapping_predicate lst (ZFalse{reason=[]})
  = "false"
prevar_mapping_predicate lst (ZMember (ZVar (x,[],tx)) (ZCall (ZVar ("\\delta",[],dtyp)) (ZVar (n,[],_))))
  = "("++x++":type"++dtyp++"("++n++"))"
prevar_mapping_predicate lst (ZMember a b)
  = "member("++(prevar_mapping_ZExpr lst a)++","++(prevar_mapping_ZExpr lst b)++")"
prevar_mapping_predicate lst x
  = fail ("not implemented by prevar_mapping_predicate: " ++ show x)
\end{code}


\subsection{Mapping Function for Channel Set Expressions}
\begin{code}
prevar_mapping_predicate_cs :: CSExp -> String
prevar_mapping_predicate_cs (CSEmpty) = "{}"
prevar_mapping_predicate_cs (CChanSet x) = "{| "++(prevar_mapping_ZExpr_def x)++" |}"
prevar_mapping_predicate_cs (CSExpr x) = x
prevar_mapping_predicate_cs (ChanSetUnion a b)
  = "union("++ (prevar_mapping_predicate_cs a)++","++ (prevar_mapping_predicate_cs b) ++")"
prevar_mapping_predicate_cs (ChanSetInter a b)
  = "inter("++ (prevar_mapping_predicate_cs a)++","++ (prevar_mapping_predicate_cs b) ++")"
prevar_mapping_predicate_cs (ChanSetDiff a b)
  = "diff("++ (prevar_mapping_predicate_cs a)++","++ (prevar_mapping_predicate_cs b) ++")"
-- prevar_mapping_predicate_cs x
--   = fail ("not implemented by prevar_mapping_predicate_cs: " ++ show x)

\end{code}

\subsection{Mapping Function for Sequence Expressions}

The mapping function for sequence expressions is defined as follows:


%

% # (ChanComm "mget" [ChanDotExp (ZVar v),ChanInp t])
% # (ChanComm "mset" [ChanDotExp (ZVar v),ChanDotExp (ZCall (ZVar v) (ZTuple [ZCall (ZVar v) (ZTuple [ZVar v,ZInt 1]),ZInt 3]))])
% # (ChanComm "mset" [ChanDotExp (ZVar v),ChanDotExp (ZInt 0)])
% # (ChanComm "mset" [ChanDotExp (ZVar v),ChanDotExp (ZVar v)])
\begin{code}
prevar_get_channel_name :: [ZPara] -> Comm -> ZName
prevar_get_channel_name spec (ChanComm "mset" [ChanDotExp (ZVar (n,[],x)),ChanInpPred nv1 (ZMember (ZVar (nv2,[],_)) (ZCall (ZVar ("\\delta",[],xtp)) (ZVar (nv3,[],_))))]) = "mset."++n++"?"++nv1++":type"++xtp++"("++n++")"
prevar_get_channel_name spec  (ChanComm "mget" [ChanDotExp (ZVar (n,[],x)),ChanOutExp (ZCall (ZVar (b,[],_)) (ZVar (n1,[],_)))]) = "mget."++n++".apply("++b++","++n1++")"
prevar_get_channel_name spec (ChanComm "mset" [ChanDotExp (ZVar (n,[],x)),ChanOutExp (ZCall (ZVar (b,[],_)) (ZVar (n1,[],_)))]) = "mset."++n++".apply("++b++","++n1++")"
prevar_get_channel_name spec (ChanComm "mget" [ChanDotExp (ZVar (x,[],t)),ChanInp v1]) = "mget."++x++"?"++v1++":(type"++(def_U_prefix t)++"("++x++"))"
prevar_get_channel_name spec (ChanComm "mset" ((ChanDotExp (ZVar (x,[],t))):xs)) = "mset."++x++".("++(def_U_prefix t)++(prevar_get_channel_name_cont spec xs)++")"
prevar_get_channel_name spec (ChanComm "lset" [ChanDotExp (ZVar (n,[],x)),ChanInpPred nv1 (ZMember (ZVar (nv2,[],_)) (ZCall (ZVar ("\\delta",[],xtp)) (ZVar (nv3,[],_))))]) = "lset."++n++"?"++nv1++":type"++xtp++"("++n++")"
prevar_get_channel_name spec  (ChanComm "lget" [ChanDotExp (ZVar (n,[],x)),ChanOutExp (ZCall (ZVar (b,[],_)) (ZVar (n1,[],_)))]) = "lget."++n++".apply("++b++","++n1++")"
prevar_get_channel_name spec (ChanComm "lset" [ChanDotExp (ZVar (n,[],x)),ChanOutExp (ZCall (ZVar (b,[],_)) (ZVar (n1,[],_)))]) = "lset."++n++".apply("++b++","++n1++")"
prevar_get_channel_name spec (ChanComm "lget" [ChanDotExp (ZVar (x,[],t)),ChanInp v1]) = "lget."++x++"?"++v1++":(type"++(def_U_prefix t)++"("++x++"))"
prevar_get_channel_name spec (ChanComm "lset" ((ChanDotExp (ZVar (x,[],t))):xs)) = "lset."++x++".("++(def_U_prefix t)++(prevar_get_channel_name_cont spec xs)++")"
prevar_get_channel_name spec (ChanComm x y)
  = x++(prevar_get_channel_name_cont spec y)
prevar_get_channel_name spec (ChanGenComm _ _ _)
  = ""
\end{code}

\begin{code}
prevar_get_channel_name_cont spec [] = ""

prevar_get_channel_name_cont spec ((ChanOutExp v) : xs)
  = prevar_get_channel_name_cont spec ((ChanDotExp v) : xs)
prevar_get_channel_name_cont spec ((ChanDotExp v) : xs)
  = "."++(prevar_mapping_ZExpr (get_delta_names1 spec) v)++(prevar_get_channel_name_cont spec xs)
prevar_get_channel_name_cont spec ((ChanInp v) : xs)
  = "?"++v++(prevar_get_channel_name_cont spec xs)
prevar_get_channel_name_cont spec ((ChanInpPred v (ZPSchema (ZSRef (ZSPlain p _) [] []))) : xs)
  = "?"++v++":"++p++(prevar_get_channel_name_cont spec xs)
prevar_get_channel_name_cont spec ((ChanInpPred v x) : xs)
  = "?"++v++":"++(prevar_mapping_predicate (get_delta_names1 spec) x)++(prevar_get_channel_name_cont spec xs)
\end{code}
\begin{code}
prevar_get_c_chan_type :: [ZPara] -> ZName -> [CDecl] -> String
prevar_get_c_chan_type spec c [(CChanDecl a b)]
  = case a == c of
      True -> prevar_mapping_ZExpr (get_delta_names1 spec) b
      False -> error "Channel not found"
prevar_get_c_chan_type spec c ((CChanDecl a b):xs)
  = case a == c of
      True -> prevar_mapping_ZExpr (get_delta_names1 spec) b
      False -> prevar_get_c_chan_type spec c xs
prevar_get_c_chan_type spec c (_:xs)
  = prevar_get_c_chan_type spec c xs
prevar_get_c_chan_type spec c []
  = error "No channel was found"
\end{code}

\begin{code}
prevar_get_chan_list [CircChannel x] = x
prevar_get_chan_list ((CircChannel x):xs) = x ++ (prevar_get_chan_list xs)
prevar_get_chan_list (_:xs) = (prevar_get_chan_list xs)
prevar_get_chan_list _ = []
\end{code}


\begin{code}
c_to_csp_CSPRepSeq _ [] = ""
c_to_csp_CSPRepSeq spec [Choose (a,b,c) s]
  = " ; " ++a ++ " : " ++ (prevar_mapping_ZExpr (get_delta_names1 spec) s)++ " @  "
c_to_csp_CSPRepSeq spec ((Choose (a,b,c) s):xs)
  = " ; " ++a ++ " : " ++ (prevar_mapping_ZExpr (get_delta_names1 spec) s) ++ " @  "
  ++ c_to_csp_CSPRepSeq spec xs
\end{code}
