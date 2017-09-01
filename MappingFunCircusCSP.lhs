%!TEX root = MAIN.tex

\chapter{Mapping Functions - Circus to CSP}

Mapping Functions - Circus to CSP
\begin{code}
module MappingFunCircusCSP
(
  mapping_Circus
)
where
import AST
import Subs
import CRL
import FormatterToCSP
import Data.List
import Data.Text hiding (map,concat)
import Data.Char hiding (toUpper, toTitle)
import MappingFunStatelessCircus
import OmegaDefs


showexpr = zexpr_string (pinfo_extz 80)
\end{code}

%In here, you have to create a preprocessing set of functions
% in order to rename the variable names and put it as a preamble
% of the specification.

\section{Mapping Circus Paragraphs}
The following functions are used to map Circus Channels into CSP. However, generic circus channels are not yet captured by the tool.
\begin{code}
mapping_Circus :: [ZPara] -> [ZPara] -> String
mapping_Circus spec []
  = ""
mapping_Circus spec [x]
  = mapping_CircParagraphs spec x
mapping_Circus spec (x:xs)
  = mapping_CircParagraphs spec x ++ (mapping_Circus spec xs)

-- filter_spec (e(CircChannel a):xs)
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

mapping_CircParagraphs :: [ZPara] -> ZPara -> String
mapping_CircParagraphs spec (ZFreeTypeDef ("UNIVERSE",_,_) univ)
  = case res of
    False -> ("\n--------------------------------"++
            "\n-- The universe of values"++
            "\n datatype UNIVERSE = " ++ (mapping_ZBranch_list univ)++
            -- "\n NatValueMax = 4\nNatValue = {0..NatValueMax}"++
            "\n--Conversions"++
            "\n"++(mk_value (get_u_tag_ZBranch univ))++
            "\n"++(mk_type (get_u_tag_ZBranch univ))++
            "\n"++(mk_tag (get_u_tag_ZBranch univ)))
    True -> ""
  where
    univlst = (def_universe spec)
    funivlst = remdups (filter_types_universe' univlst)
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
mapping_CircParagraphs spec (CircChannel [CChanDecl "mget" (ZCross [ZVar ("NAME",[],[]),ZVar ("UNIVERSE",[],[])]),CChanDecl "mset" (ZCross [ZVar ("NAME",[],[]),ZVar ("UNIVERSE",[],[])])])
  = case res of
    False -> "\n\n--------------------------------"
            ++ "\n -- mget, mset and terminate -- "
            ++ "\n--------------------------------\n"
            ++ mapping_CDecl spec [CChanDecl "mget" (ZCross [ZVar ("NAME",[],[]),ZVar ("UNIVERSE",[],[])]),CChanDecl "mset" (ZCross [ZVar ("NAME",[],[]),ZVar ("UNIVERSE",[],[])])]
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
mapping_CircParagraphs spec (CircChannel [CChan "terminate"])
  = case res of
    False -> "\n" ++ mapping_CDecl spec [CChan "terminate"]
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
mapping_CircParagraphs spec (CircChanSet "MEMI" (CChanSet ["mset","mget","terminate"]))
  = case res of
    False -> "\n\n--------------------------------"
            ++ "\n -- MEMI -- "
            ++ "\n--------------------------------\n"
            ++ "MEMI" ++ " = " ++ (mapping_CSExp (CChanSet ["mset","mget","terminate"]))
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
mapping_CircParagraphs spec (ZAbbreviation (xn,_,_) xp)
  | Subs.isPrefixOf "\\delta" xn = ""
  | Subs.isPrefixOf "BINDINGS" xn
    && (Data.List.length xn > Data.List.length "BINDINGS")
        = ("\n-- Bindings definitions for "++(lastN 3 xn)++ "\n"
            ++ xn
            ++ " = {set(b) | b <- set(distCartProd(NAMES_VALUES_"
            ++ (lastN 3 xn)
            ++ "))}\n")
  | otherwise = "\n"++ xn ++
                " = " ++ mapping_ZExpr (get_delta_names1 spec) xp
\end{code}
\subsection{Mapping $NAME$}
\begin{code}
mapping_CircParagraphs spec (ZFreeTypeDef (nm,b,[]) zbs)
  | nm == "NAME" = "\n-- definition of NAME for the entire spec "
      ++ "\ndatatype NAME = "++(mapping_ZBranch_list zbs)++"\n"
  | Subs.isPrefixOf "NAME" nm
      && (Data.List.length nm > Data.List.length "NAME")
        = "\n-- Subtype definition for "++(lastN 3 nm)
          ++ "\n subtype "++nm ++ " = " ++(mapping_ZBranch_list zbs)++
          "\n" ++ mk_NAME_VALUES_TYPE (lastN 3 nm) ++ "\n"
  | Subs.isPrefixOf "U_" nm
      && (Data.List.length nm > Data.List.length "U_")
        = "\n-- subtypes of UNIVERSE for "++(lastN 3 nm)
            ++ "\nsubtype "++nm ++ " = " ++(mapping_ZBranch_list zbs)++"\n"
  | otherwise = "\ndatatype "++ nm ++ " = " ++(mapping_ZBranch_list zbs)++"\n"


\end{code}
% \subsection{Mapping given sets}
%
% \begin{circus}
%   \Upsilon_{CircParagraphs}(N == \{a | b\})
%   \defs\\\qquad
%   \tco{N = }\Upsilon_{ZTuple}(\{a | b\})
% \end{circus}
% \begin{code}
% mapping_CircParagraphs spec (ZAbbreviation (n,[],t) (ZSetComp xl (Just (ZTuple ztp))))
%   = "\n"++ n ++ " = (" ++ mapping_ZTuple ztp ++ ")"
%
% \end{code}
\subsection{Mapping Z free types}

\begin{circus}
  \Upsilon_{CircParagraphs}(N ::= a_1 | \ldots | a_n) \defs \tco{datatype N = }\Upsilon_{ZBranch\_list}(a_1 | \ldots | a_n)
\end{circus}
\begin{code}
mapping_CircParagraphs spec (ZFreeTypeDef (a,b,c) zbs)
  = "\ndatatype " ++ a ++ " = " ++ (mapping_ZBranch_list zbs)

\end{code}
\subsection{Mapping \Circus\ process -- $ProcDecl$}

\begin{circus}
  \Upsilon_{CircParagraphs}(P) \defs\Upsilon_{ProcDecl}(P)
\end{circus}
    \begin{provs}
      \item $P$ is a \Circus\ process.
    \end{provs}
\begin{code}
mapping_CircParagraphs spec (Process cp)
  = "\n" ++ mapping_ProcDecl spec cp

\end{code}
\subsection{Mapping \Circus\ channel -- $CDecl$}

\begin{circus}
  \Upsilon_{CircParagraphs}(\circchannel c) \defs \Upsilon_{CDecl}(c)
\end{circus}
    \begin{itemize}
      \item $c$ is a \Circus\ channel.
    \end{itemize}
\begin{code}
mapping_CircParagraphs spec (CircChannel cc2)
  = "\n" ++ mapping_CDecl spec cc2
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
mapping_CircParagraphs spec (CircChanSet cn c2)
  = "\n" ++ cn ++ " = " ++ (mapping_CSExp c2)

\end{code}

\ignore{
\begin{code}
-- mapping_CircParagraphs spec (ZGivenSetDecl gs)
--   = undefined
-- mapping_CircParagraphs spec (ZSchemaDef zsn zse)
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
-- % mapping_CircParagraphs spec (ZAbbreviation (n,[],t) (ZSetDisplay ls))
-- %   = "\n" ++ n ++ " = " ++ (mapping_ZExpr (get_delta_names1 spec) (ZSetDisplay ls))
-- % mapping_CircParagraphs spec (ZAbbreviation (n,[],t) expr)
-- %   = "\n" ++ n ++ " = " ++ (mapping_ZExpr (get_delta_names1 spec) expr)
mapping_CircParagraphs spec (Assert x) = "\n" ++ x
\end{code}
\ignore{
\begin{code}
-- mapping_CircParagraphs spec (ZPredicate zp)
--   = undefined
-- mapping_CircParagraphs spec (ZAxDef zgfs)
--   = undefined
-- mapping_CircParagraphs spec (ZGenDef zgfs)
--   = undefined
\end{code}}
In any other cases, an error is raised.
\begin{code}
mapping_CircParagraphs spec x
  = fail ("not implemented by mapping_CircParagraphs: " ++ show x)
\end{code}

\subsection{Mapping Free Types - Auxiliary functions}
The function $mapping\_ZBranch$ transforms free types and composite free types into the corresponding notation in CSP. For such, a composite type can be $A\cross B$ and therefore, it is translated using $mapping\_ZBranch\_cross$.
\begin{code}
mapping_ZBranch :: ZBranch -> String
mapping_ZBranch  (ZBranch0 (a,b,c)) = a
mapping_ZBranch  (ZBranch1 (a,xb,c) (ZVar (b,[],t))) = a ++ "." ++ b
mapping_ZBranch  (ZBranch1 (a,xb,c) (ZCross b)) = a ++ "." ++ (mapping_ZBranch_cross  b)
\end{code}

\begin{code}
mapping_ZBranch_cross :: [ZExpr] -> String
mapping_ZBranch_cross [ZVar (a,b,c)] = a
mapping_ZBranch_cross ((ZVar (a,b,c)):xs) = a ++ "." ++ (mapping_ZBranch_cross xs)
\end{code}
Then, the $mapping\_ZBranch\_list$ transforms the RHS of the equality, with the possible free types from a $ZBranch$ list.
\begin{code}
mapping_ZBranch_list :: [ZBranch] -> String
mapping_ZBranch_list [] = ""
mapping_ZBranch_list [x] = (mapping_ZBranch x)
mapping_ZBranch_list (x:xs) = (mapping_ZBranch x) ++ " | " ++ (mapping_ZBranch_list  xs)
\end{code}
\subsection{Mapping Circus Channels}
This set of mapping functions will translate the declaration of channels from \Circus\ into \CSPM. Although, generic channels are not yet available.

\begin{circus}
  \Upsilon_{CDecl}(\circchannel a) \defs \tco{channel a}\\
  \Upsilon_{CDecl}(\circchannel a : T) \defs \tco{channel a : T}
\end{circus}
\begin{code}
mapping_CDecl :: [ZPara] -> [CDecl] -> String
mapping_CDecl spec x
  = (display_chann_CChan x1) ++ (display_chann_CChanDecl x2)
  where x1 = filter_channels_CChan x
        x2 = filter_channels_CChanDecl x
-- mapping_CDecl spec (CGenChanDecl zn3 zn4 ze)
--   = undefined
\end{code}
A channel declaration can be either of form $CChan$ or $CChanDecl$. For $CChan$, we can have $\circchannel terminate$, whereas for $CChanDecl$, $\circchannel mget : NAME \cross BINDING$. Thus, we filter both cases into $x1$ for $CChan$ and $x2$ for $CChanDecl$, and then, display them accordingly.
\begin{code}
filter_channels_CChan :: [CDecl] -> [ZName]
filter_channels_CChan [(CChan a)] = [a]
filter_channels_CChan [_] = []
filter_channels_CChan ((CChan a):xs) = [a]++(filter_channels_CChan xs)
filter_channels_CChan (_:xs) = (filter_channels_CChan xs)
\end{code}
\begin{code}
filter_channels_CChanDecl :: [CDecl] -> [(ZName, ZExpr)]
filter_channels_CChanDecl [(CChanDecl a b)] = [(a,b)]
filter_channels_CChanDecl [_] = []
filter_channels_CChanDecl ((CChanDecl a b):xs) = [(a,b)]++(filter_channels_CChanDecl xs)
filter_channels_CChanDecl (_:xs) = (filter_channels_CChanDecl xs)
\end{code}
\begin{code}
display_chann_CChan :: [ZName] -> String
display_chann_CChan [] = ""
display_chann_CChan x = "channel " ++ display_chann_CChan' x
\end{code}
\begin{code}
display_chann_CChan' :: [ZName] -> String
display_chann_CChan' [] = ""
display_chann_CChan' [x] = x
display_chann_CChan' (x:xs) = x ++ ", " ++ (display_chann_CChan' xs)
\end{code}
\begin{code}
display_chann_CChanDecl :: [(String, ZExpr)] -> String
display_chann_CChanDecl [] = ""
display_chann_CChanDecl [(a,b)]
  = "channel " ++ a
    ++ " : " ++ (get_channel_type b)
display_chann_CChanDecl (x:xs)
  = "channel " ++ display_chann_CChan' (map fst (x:xs))
    ++ " : " ++ (get_channel_type (snd x))
\end{code}
Function $get_channel_type$ translates the AST syntax for type expressions into \CSPM.
\begin{code}
get_channel_type :: ZExpr -> String
get_channel_type (ZVar ("\\nat",b,[])) = "NatValue"
get_channel_type (ZVar ("\\nat_1",b,[])) = "NatValue"
get_channel_type (ZVar (a,b,c)) = a
get_channel_type (ZCall (ZVar ("\\power",[],[])) (ZVar (v,[],_))) = "Set("++v++")"
get_channel_type (ZCross xs) = (get_channel_type_list xs)
get_channel_type (ZTuple xls) = "(" ++ get_channel_type_tuple xls ++ ")"
get_channel_type (ZSetComp [Choose (a,[],ta) (ZVar (at,[],tat)),
              Choose (b,[],tb) (ZVar (bt,[],tbt))]
                (Just (ZTuple [ZVar (a1,[],ta1),ZVar (b1,[],tb1)])))
  = "(" ++ get_channel_type_tuple [(ZVar (at,[],tat)),(ZVar (bt,[],tbt))] ++ ")"
get_channel_type _ = ""

get_channel_type_tuple :: [ZExpr] -> String
get_channel_type_tuple [ZVar (a,[],_)] = a
get_channel_type_tuple ((ZVar (a,[],_)):xs) = a ++ "," ++ (get_channel_type_tuple xs)

get_channel_type_list :: [ZExpr] -> String
get_channel_type_list [x] = (get_channel_type x)
get_channel_type_list (x:xs) = (get_channel_type x) ++ "." ++ (get_channel_type_list xs)
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
mapping_CSExp :: CSExp -> String
mapping_CSExp (CChanSet xs) = "{| " ++ (mapping_CSExp_get_cs xs) ++ " |}"
mapping_CSExp (ChanSetDiff a b) = "diff("++(mapping_CSExp a)++","++(mapping_CSExp b)++")"
mapping_CSExp (ChanSetInter a b) = "inter("++(mapping_CSExp a)++","++(mapping_CSExp b)++")"
mapping_CSExp (ChanSetUnion a b) = "union("++(mapping_CSExp a)++","++(mapping_CSExp b)++")"
mapping_CSExp (CSEmpty) = "{ }"
mapping_CSExp (CSExpr zn) = zn
\end{code}
Transforms a $CChanSet$ channel set into a list of channels in the CSP format
\begin{code}
mapping_CSExp_get_cs :: [[Char]] -> [Char]
mapping_CSExp_get_cs [] = ""
mapping_CSExp_get_cs [x] = x
mapping_CSExp_get_cs (c:cs) = c ++ "," ++ (mapping_CSExp_get_cs cs)
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
mapping_ProcDecl ::  [ZPara] -> ProcDecl -> String
--mapping_ProcDecl procn spec (CGenProcess zn (x:xs) pd)
--  = (show zn) ++ " = "
mapping_ProcDecl spec (CProcess p pd)
  = "\n" ++ p ++ (mapping_ProcessDef p spec pd)
mapping_ProcDecl spec _
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
mapping_ProcessDef :: ZName -> [ZPara] -> ProcessDef -> String
mapping_ProcessDef procn spec (ProcDef cp)
  = " = " ++ (mapping_CProc procn spec cp)
mapping_ProcessDef procn spec (ProcDefSpot xl pd)
  = "("++(mapping_ZGenFilt_list  spec xl ) ++ ")" ++ (mapping_ProcessDef procn spec pd)
-- mapping_ProcessDef procn spec (ProcDefIndex (x:xs) pd)
--  = "("++(getZGenFilt (x:xs)) ++ ") = " ++ (mapping_CProc procn spec cp)
\end{code}
The two functions below will make the list of parameters of the \CSPM\ process, those from the $Decl$ part of the \Circus\ process.
\begin{code}
mapping_ZGenFilt_list :: [ZPara] -> [ZGenFilt] -> String
mapping_ZGenFilt_list spec [x]
  = (mapping_ZGenFilt spec x)
mapping_ZGenFilt_list spec (x:xs)
  = (mapping_ZGenFilt spec x) ++ "," ++ (mapping_ZGenFilt_list  spec xs)
\end{code}
\begin{code}
mapping_ZGenFilt :: [ZPara] -> ZGenFilt -> String
mapping_ZGenFilt  spec (Choose v _) = nfst v
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
mapping_CProc :: ZName -> [ZPara] -> CProc -> String
mapping_CProc procn spec (CExtChoice a b)
  = "( " ++ (mapping_CProc procn spec a)
    ++ " [] "
    ++ (mapping_CProc procn spec b) ++ " )"
mapping_CProc procn spec (CHide a cs)
  = "( " ++ (mapping_CProc procn spec a)
    ++  " \\ "
    ++ mapping_predicate_cs (cs) ++ " )"
mapping_CProc procn spec (CIntChoice a b)
  = "( " ++ (mapping_CProc procn spec a)
    ++ " |~| "
    ++ (mapping_CProc procn spec b) ++ " )"
mapping_CProc procn spec (CInterleave a b)
  = "( " ++ (mapping_CProc procn spec a)
    ++ " ||| "
    ++ (mapping_CProc procn spec b) ++ " )"
mapping_CProc procn spec (CircusProc zn)
  = zn
mapping_CProc procn spec (CParParal cs a b)
  = "( " ++ (mapping_CProc procn spec a)
    ++ " [| "
    ++ mapping_predicate_cs (cs)
    ++ " |] "
    ++ (mapping_CProc procn spec b) ++ " )"
mapping_CProc procn spec (CSeq a b)
  = "( " ++ (mapping_CProc procn spec a)
    ++ " ; "
    ++ (mapping_CProc procn spec b) ++ " )"
mapping_CProc procn spec (CRepExtChProc [(Choose (x,[],tx) s)] a)
  = "[] "
    ++  x
    ++ " : "
    ++ (mapping_ZExpr (get_delta_names1 spec) s)
    ++ " @ "
    ++ (mapping_CProc procn spec a)
mapping_CProc procn spec (CRepIntChProc [(Choose (x,[],tx) s)] a)
  = "|~| "
    ++  x
    ++ " : "
    ++ (mapping_ZExpr (get_delta_names1 spec) s)
    ++ " @ "
    ++ (mapping_CProc procn spec a)
mapping_CProc procn spec (CRepInterlProc [(Choose (x,[],tx) s)] a)
  = "|||"
    ++  x
    ++ " : "
    ++ (mapping_ZExpr (get_delta_names1 spec) s)
    ++ " @ "
    ++ (mapping_CProc procn spec a)
mapping_CProc procn spec (CRepParalProc cse [(Choose (x,[],tx) s)] a)
  = " [| "
    ++ mapping_predicate_cs (cse)
    ++ " |] "
    ++  x
    ++ " : "
    ++ (mapping_ZExpr (get_delta_names1 spec) s)
    ++ " @ "
    ++ (mapping_CProc procn spec a)
mapping_CProc procn spec (CRepSeqProc [(Choose (x,[],tx) s)] a)
  = "; "
    ++  x
    ++ " : "
    ++ (mapping_ZExpr (get_delta_names1 spec) s)
    ++ " @ "
    ++ (mapping_CProc procn spec a)
mapping_CProc procn spec (ProcStalessMain al ma)
  | al == [] = "\n\t" ++ (mapping_CAction procn spec ma)
  | otherwise = "\n\tlet " ++ (mapping_PPar_list procn spec al)
    ++ "within " ++ (mapping_CAction procn spec ma)
-- (mapping_CProc procn spec CGenProc zn (x:xs))
--   = undefined
mapping_CProc procn spec (CParamProc zn xl)
   = zn ++ "(" ++ concat (map (mapping_ZExpr (get_delta_names1 spec)) xl) ++ ")"
-- (mapping_CProc procn spec CSimpIndexProc zn (x:xs))
--   = undefined
-- (mapping_CProc procn spec ProcMain zp (x:xs) ca)
--   = undefined
mapping_CProc procn spec (CProcRename n (zv:zvs) (xp:xps))
  = n ++"[["++ (mapping_rename procn spec (zv:zvs) (xp:xps)) ++"]]"
mapping_CProc procn spec x
  = fail ("not implemented by mapping_CProc: " ++ show x)
\end{code}

This function maps any renaming, to its equivalent syntax in \CSPM.
\begin{circus}
  \Upsilon_{Rename}(x\#xs,y\#xs) \defs \Upsilon_{Comm}(x)~\tco{<- }\Upsilon_{Comm}(y)\tco{ , }\Upsilon_{Rename}(xs,xs) \\
  \Upsilon_{Rename}([x],[y]=) \defs \Upsilon_{Comm}(x)~\tco{<- }\Upsilon_{Comm}(y)
  \end{circus}

\begin{code}
mapping_rename :: ZName -> [ZPara] -> [Comm] -> [Comm] -> [Char]
mapping_rename procn spec [y] [x]
  = (mapping_Comm procn spec y)++ " <- "++ (mapping_Comm procn spec x)
mapping_rename procn spec (y:zvs) (x:xps)
  = (mapping_Comm procn spec y)++ " <- "++ (mapping_Comm procn spec x)++", "++(mapping_rename procn spec zvs xps)
mapping_rename _ _ [] _ = ""
mapping_rename _ _ _ [] = ""
\end{code}
\subsection{Mapping Circus Processes Paragraphs}
NOTE: $CNameSet$ and $ProcZPara$ is not yet implemented
\begin{circus}
  \Upsilon_{PPar}(P \circdef Decl \circspot A) \defs~\tco{P(}\Upsilon_{ZGenFilt\_list}(Decl)\tco{) = }\Upsilon_{CAction}(A) \\
  \Upsilon_{PPar}(P \circdef A) \defs~\tco{P = }\Upsilon_{CAction}(A)
  \end{circus}
\begin{code}
mapping_PPar :: ZName -> [ZPara] -> PPar -> String
--mapping_PPar procn spec (CNameSet zn nse) --  = undefined
-- mapping_PPar procn spec (CParAction "Memory" (CircusAction (CActionCommand (CVResDecl decl a ))))
-- mapping_PPar procn spec (CParAction "Memory" x) = ""
mapping_PPar procn spec (CParAction p (CircusAction (CActionCommand (CVResDecl decl a ))))
  = p ++"("++ (mapping_ZGenFilt_list spec decl) ++ ") =\n\t\t\t" ++ (mapping_CAction procn spec a)
mapping_PPar procn spec (CParAction p pa)
  = p ++ (mapping_ParAction procn spec pa)
mapping_PPar procn spec x
  = fail ("Not implemented by mapping_PPar: " ++ show x)
--mapping_PPar procn spec (ProcZPara zp)
--  = undefined
\end{code}
This function just process a list of $PPar$ from within a \Circus\ process printing it one line each.
\begin{code}
mapping_PPar_list :: ZName -> [ZPara] -> [PPar] -> String
mapping_PPar_list procn spec []
  = "\n\t\t"
mapping_PPar_list procn spec (x:xs)
  = "\n\t\t" ++ (mapping_PPar procn spec x) ++ (mapping_PPar_list procn spec xs)
\end{code}

\subsection{Mapping Parameterised Circus Actions}
\begin{code}
mapping_ParAction :: ZName -> [ZPara] -> ParAction -> String
mapping_ParAction procn spec (CircusAction ca)
  = " = " ++ (mapping_CAction procn spec ca)
mapping_ParAction procn spec (ParamActionDecl xl pa)
  = "("++(mapping_ZGenFilt_list  spec xl ) ++ ") = " ++ (mapping_ParAction procn spec pa)
\end{code}

\subsection{Mapping Circus Actions}
NOTE: $CActionSchemaExpr$ is not yet implemented.

\begin{code}
mapping_CAction :: ZName -> [ZPara] -> CAction -> ZName
mapping_CAction procn spec (CActionCommand cc)
  = "("++mapping_CCommand procn spec cc++")"
mapping_CAction procn spec (CActionName zn)
  = zn
mapping_CAction procn spec (CSPUnfAction x (CActionName v))
  = x ++"("++v++")"
--mapping_CAction procn spec (CActionSchemaExpr zse)
--  = undefined
\end{code}
\begin{circus}
\Upsilon_A(c?x : P \then A)
\defs~\tco{c?x :\{x | x <- $\delta(c)$,$\Upsilon_{\mathbb{B}}(P(x))$\} -> $\Upsilon_A(A)$}
\end{circus}

\begin{code}
mapping_CAction procn spec (CSPCommAction (ChanComm c [ChanInpPred x p]) a)
  = case np of
    "true" -> c ++ "?"++ x ++ " : { x | x <- "++ (get_c_chan_type spec c (get_chan_list spec)) ++ "} ->\n\t\t ("++ (mapping_CAction procn spec a)++")"
    _ -> c ++ "?"++ x ++ " : { x | x <- "++ (get_c_chan_type spec c (get_chan_list spec)) ++ ", "++ (mapping_predicate (get_delta_names1 spec) p) ++ "} ->\n\t\t ("++ (mapping_CAction procn spec a)++")"
    where
      np = (mapping_predicate (get_delta_names1 spec) p)
\end{code}
\begin{circus}
\Upsilon_A(c?x\then A)\circdef~\tco{c?x -> } \Upsilon_A(A)
\end{circus}
\begin{code}
mapping_CAction procn spec (CSPCommAction (ChanComm c [ChanInp x]) a)
  = (get_channel_name spec (ChanComm c [ChanInp x]))
    ++ " ->\n\t\t "
    ++ mapping_CAction procn spec (a)
\end{code}

\begin{circus}
\Upsilon_A(c!v \then\ A)\circdef~\tco{c!v -> }\Upsilon_A(A)
\end{circus}
\begin{code}
mapping_CAction procn spec (CSPCommAction (ChanComm c [ChanOutExp (ZVar (x,[],tx))]) a)
  = (get_channel_name spec (ChanComm c [ChanOutExp (ZVar (x,[],tx))]))
    ++ " ->  "
    ++ mapping_CAction procn spec (a) ++ ""

mapping_CAction procn spec (CSPCommAction (ChanComm c lst) a)
  = (get_channel_name spec (ChanComm c lst))
    ++ " -> "
    ++ mapping_CAction procn spec (a) ++ ""
\end{code}


\begin{circus}
\Upsilon_A(c\then\ A)\circdef~\tco{c -> }\Upsilon_A(A)
\end{circus}
\begin{code}
mapping_CAction procn spec (CSPCommAction c a)
  = (get_channel_name spec c)
    ++ " ->\n\t\t "
    ++ mapping_CAction procn spec (a) ++ ""
\end{code}

\begin{circus}
\Upsilon_A(A \extchoice B) \circdef~\Upsilon_A(A) ~\tco{[]} \Upsilon_A(B)
\end{circus}
\begin{code}
mapping_CAction procn spec (CSPExtChoice a b)
  = "( " ++ mapping_CAction procn spec (a)
    ++ "\n\t\t [] "
    ++ mapping_CAction procn spec (b) ++ ")"
\end{code}

\begin{circus}
\Upsilon_A(g \& A)\circdef~\Upsilon_{\mathbb{B}}(g)~\tco{\&}~\Upsilon_A(A)
\end{circus}
\begin{code}
mapping_CAction procn spec (CSPGuard g ca)
 -- I'm using the True Guard
  -- and False Guard laws directly
  -- into the translation.
  = case guard of
    "true" -> (mapping_CAction procn spec ca) -- True Law (true & A = A)
    "false" -> "STOP"                   -- False Law (false & A = Stop)
    _ -> "( " ++ guard ++ " & " ++ (mapping_CAction procn spec ca) ++ " )"
  where guard = (mapping_predicate (get_delta_names1 spec) g)
\end{code}

\begin{circus}
\Upsilon_A(A \circhide cs) \circdef~\Upsilon_A(A)~\tco{\textbackslash} \Upsilon_{\mathbb{P}^{cs}} (cs)
\end{circus}
\begin{code}
mapping_CAction procn spec (CSPHide a cs)
  = "( " ++ mapping_CAction procn spec (a)
    ++  "\\"
    ++ mapping_predicate_cs (cs) ++ " )"
\end{code}

\begin{circus}
\Upsilon_A(A \intchoice B) \circdef~\Upsilon_A(A)~\tco{|\textasciitilde|} \Upsilon_A(B)
\end{circus}
\begin{code}
mapping_CAction procn spec (CSPIntChoice a b)
  = "( " ++ mapping_CAction procn spec (a)
    ++ " |~| "
    ++ mapping_CAction procn spec (b) ++ " )"
\end{code}
\begin{code}
mapping_CAction procn spec (CSPInterleave ca cb)
   = "( " ++ mapping_CAction procn spec (ca)
     ++ "\n\t\t ||| "
     ++ mapping_CAction procn spec (cb) ++ " )"
\end{code}

\begin{circus}
\Upsilon_A(A \linter ns1 | ns2 \rinter B) \circdef~\Upsilon_A(A)~\tco{|||}~\Upsilon_A(B)
\end{circus}
\begin{code}
mapping_CAction procn spec (CSPNSInter ns1 ns2 a b)
  = "( " ++ mapping_CAction procn spec (a)
    ++ "\n\t\t|||"
    ++ mapping_CAction procn spec (b) ++ " )"
\end{code}

\begin{circus}
\Upsilon_A(A\lpar ns1|cs|ns2\rpar B)\circdef~\Upsilon_A(A)~\tco{[|}~\Upsilon_{\mathbb{P}^{cs}}(cs)\tco{|]}\Upsilon_A(B)
\end{circus}
\begin{code}
mapping_CAction procn spec (CSPNSParal ns1 cs ns2 a b)
  = "( " ++ mapping_CAction procn spec (a)
    ++ "\n\t\t [| "
    ++ mapping_predicate_cs (cs)
    ++ " |] \n\t\t"
    ++ mapping_CAction procn spec (b) ++ " )"
\end{code}
\begin{code}
mapping_CAction procn spec (CSPParAction zn xl)
  = zn ++ "(" ++ joinBy "," (map (mapping_ZExpr (get_delta_names1 spec)) xl) ++ ")"
\end{code}
% \begin{code}
% mapping_CAction procn spec (CSPParal cs a b)
%   = mapping_CAction procn spec (a)
%     ++ " [| "
%     ++ mapping_predicate_cs (cs)
%     ++ " |] "
%     ++ mapping_CAction procn spec (b)
% \end{code}

\begin{circus}
\Upsilon (\circmu X \circspot\ A(X )) \circdef~\tco{let Arec =}~\Upsilon_A(A(A_{rec}))~\tco{within Arec}
\end{circus}
\begin{code}
mapping_CAction procn spec (CSPRecursion x a)
  = "( " ++ "let "
    ++ x
    ++ " = "
    ++ mapping_CAction procn spec (a)
    ++ " within "
    ++ x ++ " )"
\end{code}

\begin{circus}
\Upsilon_A(\Extchoice x : S \circspot A)\circdef~\tco{[] x :}~\Upsilon_{\mathbb{P}}(S)~\tco{@}~\Upsilon_A(A)
\end{circus}
\begin{code}
mapping_CAction procn spec (CSPRepExtChoice [(Choose (x,[],tx) s)] a)
  = "( " ++ "[] "
    ++  x
    ++ " : "
    ++ (mapping_ZExpr (get_delta_names1 spec) s)
    ++ " @ "
    ++ mapping_CAction procn spec (a) ++ " )"
\end{code}

\begin{circus}
\Upsilon_A(\Intchoice x : S \circspot A)\circdef~\tco{|\textasciitilde| x :}~\Upsilon_{\mathbb{P}}(S)~\tco{@}~\Upsilon_A(A)
\end{circus}
\begin{code}


-- first case is for the BINDING
mapping_CAction procn spec (CSPRepIntChoice bdls (CSPHide (CSPNSParal [] (CSExpr "MEMI") bs1 (CSPSeq ca (CSPCommAction (ChanComm "terminate" []) CSPSkip)) (CSPParAction "Memory" zb)) (CSExpr "MEMI")))
    = "\n\t\tlet "++ restr
       ++"\n\t\twithin"
       ++"\n\t\t\t|~| "++ bnd ++" @ "++(mapping_CAction procn spec (CSPHide (CSPNSParal [] (CSExpr "MEMI") bs1 (CSPSeq ca (CSPCommAction (ChanComm "terminate" []) CSPSkip)) (CSPParAction "Memory" zb)) (CSExpr "MEMI")))++"\n"
       where
         zn =  get_znames_from_NAME spec
         znames = remdups $ map nfst (select_f_zbr zn)
         ztypes = remdups $ map ntrd (select_f_zbr zn)
         restr = mk_charll_to_charl "\n\t\t\t" $
            map (mk_restrict (concat $ map (\(va,b,c) -> (if (Subs.isPrefixOf ((join_name "sv" procn)++"_") va) then [(va,b,c)] else [])) (select_f_zbr zn))) (get_binding_types bdls)
         bnd = mk_charll_to_charl ", " $ map mk_binding_list (get_binding_types bdls)
         restn = mk_charll_to_charl ", " $ map mk_restrict_name (get_binding_types bdls)

-- otherwise...
mapping_CAction procn spec (CSPRepIntChoice [(Choose (x,[],tx) (ZVar (t,_,tx1)))] a)
  = "( " ++ "|~| "
    ++  x
    ++ " : "
    ++ t
    ++ " @\n\t\t\t "
    ++ mapping_CAction procn spec (a) ++ " )"
mapping_CAction procn spec (CSPRepIntChoice [(Choose (x,[],tx) s)] a)
      = "( " ++ "|~| "
        ++  x
        ++ " : "
        ++ (mapping_ZExpr (get_delta_names1 spec) s)
        ++ " @\n\t\t\t "
        ++ mapping_CAction procn spec (a) ++ " )"
\end{code}

% \begin{code}
% mapping_CAction procn spec (CSPRepInterl [(Choose (x,[]) s)] a)
%   = "||| "
%     ++  show x
%     ++ " : "
%     ++ (mapping_ZExpr (get_delta_names1 spec) s)
%     ++ " @ "
%     ++ mapping_CAction procn spec (a)
% \end{code}

\begin{circus}
\Upsilon_A(\Interleave x : S \circspot \lpar \emptyset \rpar A) \circdef~\tco{||| x:}\Upsilon_{\mathbb{P}}(S)~\tco{@}~\Upsilon_A(A)
\end{circus}
\begin{code}
mapping_CAction procn spec (CSPRepInterlNS [(Choose (x,[],tx) s)] [] a)
  = "( " ++ "||| "
    ++  x
    ++ " : "
    ++ (mapping_ZExpr (get_delta_names1 spec) s)
    ++ " @ "
    ++ mapping_CAction procn spec (a) ++ " )"
\end{code}

\begin{circus}
\Upsilon_A(\lpar cs \rpar x : S \circspot \lpar \emptyset \rpar A)\circdef~\tco{[|}\Upsilon_{\mathbb{P}^{cs}}(cs)\tco{|] x :}\Upsilon_{\mathbb{P}}(S)~\tco{@}~\Upsilon_A(A)
\end{circus}
\begin{code}
mapping_CAction procn spec (CSPRepParalNS cs [(Choose (x,[],tx) s)] [] a)
  = "( " ++ "[| "
    ++ mapping_predicate_cs (cs)
    ++ " |] "
    ++  x
    ++ " : "
    ++ (mapping_ZExpr (get_delta_names1 spec) s)
    ++ " @ "
    ++ mapping_CAction procn spec (a) ++ " )"
\end{code}

\begin{circus}
\Upsilon_A(\Semi x : S \circspot A)\circdef~\tco{; x :}\Upsilon_{seq}(S)~\tco{@}~\Upsilon_A(A)
\end{circus}
\begin{code}
mapping_CAction procn spec (CSPRepSeq [(Choose (x,[],tx) s)] a)
  = "( " ++ "; "
    ++  x
    ++ " : "
    ++ (mapping_ZExpr (get_delta_names1 spec) s)
    ++ " @ "
    ++ mapping_CAction procn spec (a) ++ " )"
\end{code}

\begin{circus}
\Upsilon_A(A \circseq B) \circdef~\Upsilon_A(A)~\tco{;}~\Upsilon_A(B)
\end{circus}
\begin{code}
mapping_CAction procn spec (CSPSeq a b)
  = "( " ++ mapping_CAction procn spec (a)
    ++ " ; "
    ++ mapping_CAction procn spec (b) ++ " )"
\end{code}

\begin{circus}
\Upsilon_A(\Skip) \defs~\tco{SKIP}
\end{circus}
\begin{code}
mapping_CAction procn spec (CSPSkip)
  = "SKIP"
\end{code}

\begin{circus}
\Upsilon_A(\Stop) \defs~\tco{STOP}
\end{circus}
\begin{code}
mapping_CAction procn spec (CSPStop)
  = "STOP"
\end{code}

\begin{circus}
\Upsilon_A(\Chaos) \defs~\tco{CHAOS}
\end{circus}
\begin{code}
mapping_CAction procn spec (CSPChaos)
  = "CHAOS"
\end{code}
\begin{code}
mapping_CAction procn spec x
  = fail ("not implemented by mapping_CAction: " ++ show x)
\end{code}

\subsection{Mapping Circus Commands}
NOTE: $CAssumpt$, $CommandBrace$, $CommandBracket$ not implemented yet
\begin{code}
mapping_CCommand :: ZName -> [ZPara] -> CCommand -> ZName
mapping_CCommand procn spec (CAssign (x:xs) (y:ys))
  = error ("Assignments are not available in CSP")
mapping_CCommand procn spec (CAssumpt (x:xs) zpa zpb)
  = error ("Assumptions are not available in CSP")
mapping_CCommand procn spec (CIf cga)
  = mapping_CGActions procn spec cga
-- mapping_CCommand procn spec (CommandBrace zp)
--   = undefined
-- mapping_CCommand procn spec (CommandBracket zp)
--   = undefined
-- mapping_CCommand procn spec (CResDecl (x:xs) ca)
--   = undefined
{-
mapping_CCommand procn spec (CVarDecl bds ca)
 = "let "++ restr
    ++"\n\t\t\twithin"
    ++"\n\t\t\t|~| "++ bnd ++" @ Memorise("++(mapping_CAction procn spec ca)++",\n\t\t\t "++restn++")\n"
    where
      zn =  get_znames_from_NAME spec
      znames = remdups $ map nfst (select_f_zbr zn)
      ztypes = remdups $ map ntrd (select_f_zbr zn)
      restr = mk_charll_to_charl "\n\t\t\t" $
         map (mk_restrict (concat (map (\(va,b,c) -> if (Subs.isPrefixOf ((join_name "sv" procn)++"_") va) then [(va,b,c)] else []) (select_f_zbr zn)))) ztypes
      bnd = mk_charll_to_charl ", " $ map mk_binding_list ztypes
      restn = mk_charll_to_charl ", " $ map mk_restrict_name ztypes
-}
mapping_CCommand procn spec (CValDecl (x:xs) ca)
   = ""
-- mapping_CCommand procn spec (CVResDecl (x:xs) ca)
--   = undefined
mapping_CCommand procn spec x
  = fail ("not implemented by mapping_CCommand: " ++ show x)
\end{code}

\subsection{Mapping Circus Guarded Actions}
\begin{code}
mapping_CGActions :: ZName -> [ZPara] -> CGActions -> ZName
mapping_CGActions procn spec (CircThenElse cga1 cga2)
  = (mapping_CGActions procn spec cga1) ++ " [] " ++ (mapping_CGActions procn spec cga2)
mapping_CGActions procn spec (CircGAction zp ca)
  = (mapping_predicate (get_delta_names1 spec) zp) ++ " &\n\t\t\t " ++ (mapping_CAction procn spec ca)
\end{code}

\subsection{Mapping Channel Communication}
\begin{code}
mapping_Comm :: ZName -> [ZPara] -> Comm -> String
mapping_Comm procn spec (ChanComm zn xs)
  = zn ++ (mapString (mapping_CParameter procn) spec xs)
mapping_Comm procn spec (ChanGenComm zn xs ys)
  = error ("ChanGenComm not yet implemented")
\end{code}

\begin{code}
mapString :: (t1 -> t -> String) -> t1 -> [t] -> String
mapString f s [] = ""
mapString f s (x:xs) = (f s x) ++ (mapString f s xs)
\end{code}
\begin{code}
mapping_CParameter :: ZName -> [ZPara] -> CParameter -> ZName
mapping_CParameter procn spec (ChanInp zn)
  = "?"++zn
mapping_CParameter procn spec (ChanInpPred zn zp)
 = "?"++zn ++":"++ (mapping_predicate (get_delta_names1 spec) zp)
mapping_CParameter procn spec (ChanOutExp ze)
  = mapping_CParameter procn spec (ChanDotExp ze)
mapping_CParameter procn spec (ChanDotExp ze)
  = "."++(mapping_ZExpr (get_delta_names1 spec) ze)
\end{code}

\subsection{Mapping Circus Namesets}
\begin{code}

-- mapping_NSExp procn spec ([])
--   = undefined
-- mapping_NSExp procn spec (NSExprMult (x:xs))
--   = undefined
-- mapping_NSExp procn spec (NSExprSngl zn)
--   = undefined
-- mapping_NSExp procn spec (NSHide nse1 nse2)
--   = undefined
-- mapping_NSExp procn spec (NSIntersect nse1 nse2)
--   = undefined
-- mapping_NSExp procn spec (NSUnion nse1 nse2)
--   = undefined
mapping_NSExp procn spec x
  = fail ("not implemented by mapping_NSExp: " ++ show x)
\end{code}

\section{Mapping Functions from Circus to CSP - Based on D24.1 - COMPASS}


\subsection{Mapping Functions for Predicates}

\begin{code}
mapping_predicate :: [ZName] -> ZPred -> String
-- NOt sure what "if then  else" is about
-- mapping_predicate lst (ZIf_Then_Else b x1 x2)
--   = "if " ++ (mapping_predicate lst b) ++
--     " then  " ++ (mapping_predicate lst x1) ++
--     " else " ++ (mapping_predicate lst x2)
mapping_predicate lst ( (ZMember (ZTuple [a,b]) (ZVar ("\\geq",[],[]))))
  = (mapping_ZExpr lst a) ++ " >= " ++ (mapping_ZExpr lst b)
mapping_predicate lst ( (ZMember (ZTuple [a,b]) (ZVar (">",[],[]))))
  = (mapping_ZExpr lst a) ++ " > " ++ (mapping_ZExpr lst b)
mapping_predicate lst ( (ZMember (ZTuple [a,b]) (ZVar ("\\leq",[],[]))))
  = (mapping_ZExpr lst a) ++ " <= " ++ (mapping_ZExpr lst b)
mapping_predicate lst ( (ZMember (ZTuple [a,b]) (ZVar ("<",[],[]))))
  = (mapping_ZExpr lst a) ++ " < " ++ (mapping_ZExpr lst b)
mapping_predicate lst ( (ZNot (ZEqual a b)))
  = (mapping_ZExpr lst a) ++ " != " ++ (mapping_ZExpr lst b)
mapping_predicate lst ( (ZEqual a b))
  = (mapping_ZExpr lst a) ++ " == " ++ (mapping_ZExpr lst b)
mapping_predicate lst (ZOr a b)
  = (mapping_predicate lst a) ++ " or " ++ (mapping_predicate lst b)
mapping_predicate lst (ZAnd a b)
  = (mapping_predicate lst a) ++ " and " ++ (mapping_predicate lst b)
mapping_predicate lst ( (ZNot b))
  = "not " ++ (mapping_predicate lst b)
mapping_predicate lst (ZPSchema (ZSRef (ZSPlain "\\true") [] []))
  = "true"
mapping_predicate lst (ZPSchema (ZSRef (ZSPlain "\\false") [] []))
  = "false"
mapping_predicate lst (ZTrue{reason=[]})
  = "true"
mapping_predicate lst (ZFalse{reason=[]})
  = "false"
mapping_predicate lst (ZMember (ZVar (x,[],tx)) (ZCall (ZVar ("\\delta",[],[])) (ZVar (n,[],_))))
  = "type"++(def_U_prefix tx)++"("++n++")"
mapping_predicate lst (ZMember a b)
  = "member("++(mapping_ZExpr lst a)++","++(mapping_ZExpr lst b)++")"
mapping_predicate lst x
  = fail ("not implemented by mapping_predicate: " ++ show x)
\end{code}


\subsection{Mapping Function for Channel Set Expressions}
\begin{code}
mapping_predicate_cs :: CSExp -> String
{-
The following one is not very well accepted by FDR as it may introduce differente type channels and therefore, it is incompatible.
For instance,

Couldn't match expected type Event with actual type Int=>Event
    In the expression: getCurrentTime
    In the expression: {tick, getCurrentTime}
    In the statement of a comprehension: c <- {tick, getCurrentTime}
    Relevant variable types:
        getCurrentTime :: Int=>Event
        tick :: Event
        HDMachine :: Proc
        SysClock :: Proc

I think it would be rather correct if we define it as {| x,y,z|}

-}
-- mapping_predicate_cs cs = (mapping_set_cs_exp cs)

mapping_predicate_cs (CSEmpty) = "{}"
mapping_predicate_cs (CChanSet x) = "{| "++(mapping_ZExpr_def x)++" |}"
mapping_predicate_cs (CSExpr x) = x
mapping_predicate_cs (ChanSetUnion a b)
  = "union("++ (mapping_predicate_cs a)++","++ (mapping_predicate_cs b) ++")"
mapping_predicate_cs (ChanSetInter a b)
  = "inter("++ (mapping_predicate_cs a)++","++ (mapping_predicate_cs b) ++")"
mapping_predicate_cs (ChanSetDiff a b)
  = "diff("++ (mapping_predicate_cs a)++","++ (mapping_predicate_cs b) ++")"
-- mapping_predicate_cs x
--   = fail ("not implemented by mapping_predicate_cs: " ++ show x)

\end{code}

\subsection{Mapping Function for Sequence Expressions}

The mapping function for sequence expressions is defined as follows:


%

% # (ChanComm "mget" [ChanDotExp (ZVar v),ChanInp t])
% # (ChanComm "mset" [ChanDotExp (ZVar v),ChanDotExp (ZCall (ZVar v) (ZTuple [ZCall (ZVar v) (ZTuple [ZVar v,ZInt 1]),ZInt 3]))])
% # (ChanComm "mset" [ChanDotExp (ZVar v),ChanDotExp (ZInt 0)])
% # (ChanComm "mset" [ChanDotExp (ZVar v),ChanDotExp (ZVar v)])
\begin{code}
get_channel_name :: [ZPara] -> Comm -> ZName
get_channel_name spec (ChanComm "mset" [ChanDotExp (ZVar (n,[],x)),ChanInpPred nv1 (ZMember (ZVar (nv2,[],_)) (ZCall (ZVar ("\\delta",[],_)) (ZVar (nv3,[],_))))])
  = "mset."++n++"?"++nv1++":type"++(lastN 3 x)++"("++n++")"
get_channel_name spec  (ChanComm "mget" [ChanDotExp (ZVar (n,[],x)),ChanOutExp (ZCall (ZVar (b,[],_)) (ZVar (n1,[],_)))])
    = "mget."++n++".apply("++b++","++n1++")"
get_channel_name spec  (ChanComm "mset" [ChanDotExp (ZVar (n,[],x)),ChanOutExp (ZCall (ZVar (b,[],_)) (ZVar (n1,[],_)))])
  = "mset."++n++".apply("++b++","++n1++")"
get_channel_name spec (ChanComm "mget" [ChanDotExp (ZVar (x,[],t)),ChanInp v1])
  = "mget."++x++"?"++v1++":(type"++(def_U_prefix t)++"("++x++"))"
get_channel_name spec (ChanComm "mset" ((ChanDotExp (ZVar (x,[],t))):xs))
  = "mset."++x++".("++(def_U_prefix t)++(get_channel_name_cont spec xs)++")"
get_channel_name spec (ChanComm x y)
  = x++(get_channel_name_cont spec y)
get_channel_name spec (ChanGenComm _ _ _)
  = ""
\end{code}

\begin{code}
get_channel_name_cont spec [] = ""

get_channel_name_cont spec ((ChanOutExp v) : xs)
  = get_channel_name_cont spec ((ChanDotExp v) : xs)
get_channel_name_cont spec ((ChanDotExp v) : xs)
  = "."++(mapping_ZExpr (get_delta_names1 spec) v)++(get_channel_name_cont spec xs)
get_channel_name_cont spec ((ChanInp v) : xs)
  = "?"++v++(get_channel_name_cont spec xs)
get_channel_name_cont spec ((ChanInpPred v x) : xs)
  = "?"++v++":"++(mapping_predicate (get_delta_names1 spec) x)++(get_channel_name_cont spec xs)
\end{code}
\begin{code}
get_c_chan_type :: [ZPara] -> ZName -> [CDecl] -> String
get_c_chan_type spec c [(CChanDecl a b)]
  = case a == c of
      True -> mapping_ZExpr (get_delta_names1 spec) b
      False -> error "Channel not found"
get_c_chan_type spec c ((CChanDecl a b):xs)
  = case a == c of
      True -> mapping_ZExpr (get_delta_names1 spec) b
      False -> get_c_chan_type spec c xs
get_c_chan_type spec c (_:xs)
  = get_c_chan_type spec c xs
get_c_chan_type spec c []
  = error "No channel was found"
\end{code}

\begin{code}
get_chan_list [CircChannel x] = x
get_chan_list ((CircChannel x):xs) = x ++ (get_chan_list xs)
get_chan_list (_:xs) = (get_chan_list xs)
get_chan_list _ = []
\end{code}

\begin{code}
mapping_ZTuple [ZVar ("\\nat",_,[])] = "NatValue"
mapping_ZTuple [ZVar ("\\nat_1",_,[])] = "NatValue"
-- mapping_ZTuple [ZVar (v,_)] = "value("++v++")"
mapping_ZTuple [ZVar (v,_,t)]
  | (is_ZVar_v_st v) = "value"++(def_U_prefix t)++"("++v++")"
  | otherwise = v
mapping_ZTuple [ZInt x] = show (fromIntegral x)
mapping_ZTuple ((ZVar (v,_,t)):xs)
  | (is_ZVar_v_st v) = "value"++(def_U_prefix t)++"("++v++")"++ "," ++ (mapping_ZTuple xs)
  | otherwise = v ++ "," ++ (mapping_ZTuple xs)
mapping_ZTuple ((ZInt x):xs) = (show (fromIntegral x)) ++ "," ++ (mapping_ZTuple xs)
mapping_ZTuple _ = ""
\end{code}

\begin{code}
mapping_ZCross [ZVar ("\\int",_,[])] = "Int"
mapping_ZCross [ZVar (v,_,_)] = v
mapping_ZCross ((ZVar (v,_,_)):xs) = (v) ++ "." ++ (mapping_ZCross xs)
mapping_ZCross _ = ""
\end{code}

\begin{code}
-- aux functions
mapping_ZExpr_def :: [ZName] -> String
mapping_ZExpr_def [x] = x
mapping_ZExpr_def (x:xs) = x++","++(mapping_ZExpr_def xs)

mapping_ZExpr_set [] = ""
mapping_ZExpr_set [ZVar (a,b,x)] = a
mapping_ZExpr_set ((ZVar (a,b,x)):xs) = a++","++(mapping_ZExpr_set xs)
mapping_ZExpr_set (_:xs) = (mapping_ZExpr_set xs)
\end{code}
\begin{code}
mapping_ZExpr_def_f f [x] = (f x)
mapping_ZExpr_def_f f (x:xs) = (f x)++","++(mapping_ZExpr_def_f f xs)

mapping_ZExpr1 (ZVar (a,_,t)) = a
mapping_ZExpr1 (ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [a,b])) = "("++(mapping_ZExpr1  a)++","++(mapping_ZExpr1  b)++")"
\end{code}

\subsection{Mapping Function for Expressions}
\begin{code}
mapping_ZExpr :: [ZName] ->  ZExpr -> String

mapping_ZExpr lst (ZVar ("\\emptyset",[],[])) = "{}"
mapping_ZExpr lst (ZVar ("\\int",[],[])) = "Int"
-- mapping_ZExpr lst (ZVar (a,_)) = a
mapping_ZExpr lst (ZInt m) = show(fromIntegral m)
mapping_ZExpr lst (ZVar (a,_,t))
  | (inListVar a lst) = "value"++(def_U_prefix t)++"(v_"++a++")"
  | (is_ZVar_v_st a) = "value"++(def_U_prefix t)++"("++a++")"
  | otherwise = a
mapping_ZExpr lst (ZBinding _) = ""
--mapping_ZExpr lst (ZCall (ZSeqDisplay x) _) = "<"++(mapping_ZExpr_def_f x)++">"
mapping_ZExpr lst (ZCall (ZVar ("*",[],[])) (ZTuple [n,m])) = "("++mapping_ZExpr lst (n) ++ " * " ++ mapping_ZExpr lst (m)++")"
mapping_ZExpr lst (ZCall (ZVar ("+",[],[])) (ZTuple [n,m])) = "("++mapping_ZExpr lst (n) ++ " + " ++ mapping_ZExpr lst (m)++")"
mapping_ZExpr lst (ZCall (ZVar ("-",[],[])) (ZTuple [n,m])) = "("++mapping_ZExpr lst (n) ++ " - " ++ mapping_ZExpr lst (m)++")"
mapping_ZExpr lst (ZCall (ZVar ("\\035",[],[])) a) = "\035(" ++ mapping_ZExpr lst (a)++")"
mapping_ZExpr lst (ZCall (ZVar ("\\\035",[],[])) a) = "card("++(mapping_ZExpr lst a)++")"
mapping_ZExpr lst (ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [a,b])) = "("++(mapping_ZExpr lst a)++","++(mapping_ZExpr lst b)++")"
mapping_ZExpr lst (ZCall (ZVar ("\\bigcap",[],[])) (ZTuple [a,b])) = "Inter("++(mapping_ZExpr lst a)++","++(mapping_ZExpr lst b)++")"
mapping_ZExpr lst (ZCall (ZVar ("\\bigcup",[],[])) (ZTuple [a,b])) = "Union("++(mapping_ZExpr lst a)++","++(mapping_ZExpr lst b)++")"
mapping_ZExpr lst (ZCall (ZVar ("\\cap",[],[])) (ZTuple [a,b])) = "inter("++(mapping_ZExpr lst a)++","++(mapping_ZExpr lst b)++")"
mapping_ZExpr lst (ZCall (ZVar ("\\cat",[],[])) (ZTuple [a,b])) = mapping_ZExpr lst (a)++"^"++mapping_ZExpr lst (b)
mapping_ZExpr lst (ZCall (ZVar ("\\cup",[],[])) (ZTuple [a,b])) = "union("++(mapping_ZExpr lst a)++","++(mapping_ZExpr lst b)++")"
mapping_ZExpr lst (ZCall (ZVar ("\\dcat",[],[])) s) = "concat("++mapping_ZExpr lst (s)++")"
mapping_ZExpr lst (ZCall (ZVar ("\\div",[],[])) (ZTuple [n,m])) = "("++mapping_ZExpr lst (n) ++ " / " ++ mapping_ZExpr lst (m)++")"
mapping_ZExpr lst (ZCall (ZVar ("\\dom",[],[])) a) = "dom("++(mapping_ZExpr lst a)++")"
mapping_ZExpr lst (ZCall (ZVar ("\\mod",[],[])) (ZTuple [n,m])) = mapping_ZExpr lst (n) ++ " % " ++ mapping_ZExpr lst (m)
mapping_ZExpr lst (ZCall (ZVar ("\\negate",[],[])) n) = "- " ++ mapping_ZExpr lst (n)
mapping_ZExpr lst (ZCall (ZVar ("\\oplus",[],[])) (ZTuple [ZVar (b,[],_),ZSetDisplay [ZCall (ZVar ("\\mapsto",[],[])) (ZTuple [ZVar (n,[],_),ZVar (x,[],_)])]])) = "over("++b++","++n++","++x++")"
mapping_ZExpr lst (ZCall (ZVar ("\\power",[],[])) a) ="Set("++(mapping_ZExpr lst a)++")"
mapping_ZExpr lst (ZCall (ZVar ("\\ran",[],[])) a) = "set("++(mapping_ZExpr lst a)++")"
mapping_ZExpr lst (ZCall (ZVar ("\\seq",[],[])) a) = "Seq("++(mapping_ZExpr lst a)++")"
mapping_ZExpr lst (ZCall (ZVar ("\\setminus",[],[])) (ZTuple [a,b])) = "diff("++(mapping_ZExpr lst a)++","++(mapping_ZExpr lst b)++")"
mapping_ZExpr lst (ZCall (ZVar ("head",[],[])) s) = "head("++mapping_ZExpr lst (s)++")"
mapping_ZExpr lst (ZCall (ZVar ("tail",[],[])) s) = "tail("++mapping_ZExpr lst (s)++")"
mapping_ZExpr lst (ZCall (ZVar (b,[],_)) (ZVar (n,[],_))) = "apply("++b++","++n++")"
mapping_ZExpr lst (ZCall (ZVar ("\\upto",[],[])) (ZTuple [a,b]))
  = "{"++(mapping_ZExpr lst a)++".."++(mapping_ZExpr lst b)++"}"
mapping_ZExpr lst (ZSetDisplay [ZCall (ZVar ("\\upto",[],[])) (ZTuple [a,b])]) = "{"++(show a)++".."++(show b)++"}"
mapping_ZExpr lst (ZSetDisplay x) = "{"++(mapping_ZExpr_def_f mapping_ZExpr1 x)++"}"
mapping_ZExpr lst (ZTuple ls) = "("++mapping_ZTuple ls ++ ")"
mapping_ZExpr lst (ZSeqDisplay []) = "<>"
mapping_ZExpr lst (ZSeqDisplay x) = "<"++(mapping_ZExpr_set x)++">"
mapping_ZExpr lst (ZCross ls) = mapping_ZCross ls
mapping_ZExpr lst (ZELet _ _) = ""
mapping_ZExpr lst (ZESchema _) = ""
mapping_ZExpr lst (ZFree0 _) = ""
mapping_ZExpr lst (ZFree1 _ _) = ""
mapping_ZExpr lst (ZFreeType _ _) = ""
mapping_ZExpr lst (ZFSet _) = ""
mapping_ZExpr lst (ZFunc1 _) = ""
mapping_ZExpr lst (ZFunc2 _) = ""
mapping_ZExpr lst (ZFuncSet _ _ _ _ _ _ _ _ _) = ""
mapping_ZExpr lst (ZGenerator _ _) = ""
mapping_ZExpr lst (ZGiven _) = ""
mapping_ZExpr lst (ZGivenSet _) = ""
mapping_ZExpr lst (ZIf_Then_Else _ _ _) = ""
mapping_ZExpr lst (ZIntSet _ _) = ""
mapping_ZExpr lst (ZLambda _ _) = ""
mapping_ZExpr lst (ZMu _ _) = ""
mapping_ZExpr lst (ZPowerSet _ _ _) = ""
mapping_ZExpr lst (ZReln _) = ""
mapping_ZExpr lst (ZSelect _ _) = ""
mapping_ZExpr lst (ZSetComp _ _ ) = ""

mapping_ZExpr lst (ZStrange _) = ""
mapping_ZExpr lst (ZTheta _) = ""
mapping_ZExpr lst (ZUniverse) = ""
mapping_ZExpr lst x = fail ("not implemented by mapping_ZExpr: " ++ show x)

\end{code}
