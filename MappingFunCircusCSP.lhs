\section{Mapping Functions - Circus to CSP}

Mapping Functions - Circus to CSP
\begin{code}
module MappingFunCircusCSP
(
  mapping_Circus
)
where
import AST
import CRL
import FormatterToCSP
import Data.Char
import MappingFunStatelessCircus
import DefSets


showexpr = zexpr_string (pinfo_extz 80)
\end{code}
\ignore{

%In here, you have to create a preprocessing set of functions
% in order to rename the variable names and put it as a preamble
% of the specification.

\subsection{Mapping Circus Paragraphs}
The following functions are used to map Circus Channels into CSP. However, generic circus channels are not yet captured by the tool.
\begin{code}
mapping_Circus :: [ZPara] -> [ZPara] -> String
mapping_Circus spec []
  = ""
mapping_Circus spec [x]
  = mapping_CircParagraphs spec x
mapping_Circus spec (x:xs)
  = mapping_CircParagraphs spec x ++ (mapping_Circus spec xs)

\end{code}
\begin{code}

mapping_CircParagraphs :: [ZPara] -> ZPara -> String
mapping_CircParagraphs spec (ZFreeTypeDef (a,b) zbs)
  = "\ndatatype " ++ a ++ " = " ++ (mapping_ZBranch_list spec zbs) 
mapping_CircParagraphs spec (Process cp)
  = "\n" ++ mapping_ProcDecl spec cp
mapping_CircParagraphs spec (CircChanSet cn c2)
  = "\n" ++ cn ++ " = " ++ (mapping_CSExp spec c2)
mapping_CircParagraphs spec (CircChannel cc2)
  = "\n" ++ mapping_CDecl spec cc2
-- mapping_CircParagraphs spec (ZGivenSetDecl gs)
--   = undefined
-- mapping_CircParagraphs spec (ZSchemaDef zsn zse)
--   = undefined
mapping_CircParagraphs spec (ZAbbreviation ("\\delta",[]) (ZSetDisplay ls)) 
  = ""
mapping_CircParagraphs spec (ZAbbreviation (n,[]) (ZSetDisplay ls)) 
  = "\n" ++ n ++ " = " ++ (mapping_ZExpr (get_delta_names spec) (ZSetDisplay ls))
mapping_CircParagraphs spec (ZAbbreviation (n,[]) expr) 
  = "\n" ++ n ++ " = " ++ (mapping_ZExpr (get_delta_names spec) expr)
-- mapping_CircParagraphs spec (ZPredicate zp)
--   = undefined
-- mapping_CircParagraphs spec (ZAxDef zgfs)
--   = undefined
-- mapping_CircParagraphs spec (ZGenDef zgfs)
--   = undefined
mapping_CircParagraphs spec x
  = fail ("not implemented by mapping_CircParagraphs: " ++ show x)
\end{code}

Definition of Free Types
\begin{code}
-- ZFreeTypeDef ("MYTYPE",[]) [ZBranch0 ("A",[]),ZBranch1 ("B",[]) (ZCross [ZVar ("\\nat",[]),ZVar ("\\nat",[])])]
mapping_ZBranch_list :: [ZPara] -> [ZBranch] -> String
mapping_ZBranch_list spec [x]
  = (mapping_ZBranch spec x)
mapping_ZBranch_list spec (x:xs)
  = (mapping_ZBranch spec x) ++ " | " ++ (mapping_ZBranch_list spec xs)
mapping_ZBranch spec (ZBranch0 (a,b))
  = a
mapping_ZBranch spec (ZBranch1 (a,xb) (ZCross b))
  = a ++ "." ++ (mapping_ZBranch_cross spec b)

mapping_ZBranch_cross :: [ZPara] -> [ZExpr] -> String
mapping_ZBranch_cross spec [ZVar (a,b)]
  = a
mapping_ZBranch_cross spec ((ZVar (a,b)):xs)
  = a ++ "." ++ (mapping_ZBranch_cross spec xs)
\end{code}
\subsection{Mapping Circus Channels}
\begin{code}
mapping_CDecl :: [ZPara] -> [CDecl] -> String
mapping_CDecl spec x
  = (show_chann_CChan x1)
    ++ (display_chann_CChanDecl x2)
  where x1 = filter_channels_CChan x
        x2 = filter_channels_CChanDecl x
-- mapping_CDecl spec (CGenChanDecl zn3 zn4 ze)
--   = undefined
\end{code}
\begin{code}
filter_channels_CChan :: [CDecl] -> [ZName]

filter_channels_CChan [(CChan a)]
  = [a]
filter_channels_CChan [_]
  = []
filter_channels_CChan ((CChan a):xs)
  = [a]++(filter_channels_CChan xs)
filter_channels_CChan (_:xs)
  = (filter_channels_CChan xs)
\end{code}
\begin{code}
show_chann_CChan :: [String] -> String
show_chann_CChan []
  = ""
show_chann_CChan x
  = "channel " ++ display_chann_CChan x
\end{code}
\begin{code}
display_chann_CChan :: [String] -> String
display_chann_CChan []
  = ""
display_chann_CChan [x]
  = x
display_chann_CChan (x:xs)
  = x ++ ", " ++ (display_chann_CChan xs)
\end{code}
\begin{code}
filter_channels_CChanDecl :: [CDecl] -> [(ZName, ZExpr)]
filter_channels_CChanDecl [(CChanDecl a b)]
  = [(a,b)]
filter_channels_CChanDecl [_]
  = []
filter_channels_CChanDecl ((CChanDecl a b):xs)
  = [(a,b)]++(filter_channels_CChanDecl xs)
filter_channels_CChanDecl (_:xs)
  = (filter_channels_CChanDecl xs)
\end{code}
\begin{code}
display_chann_CChanDecl :: [(String, ZExpr)] -> String
display_chann_CChanDecl []
  = ""
display_chann_CChanDecl [(a,b)]
  = "channel " ++ a
    ++ " : " ++ (get_channel_type b) 
display_chann_CChanDecl (x:xs)
  = "channel " ++ display_chann_CChan (map fst (x:xs)) ++ " : " ++ (get_channel_type (snd x))
   
\end{code}
\begin{code}
get_channel_type :: ZExpr -> String
get_channel_type (ZVar (a,b))
  = a
get_channel_type (ZCross xs)
  = (get_channel_type_list xs)
get_channel_type_list [x]
  = (get_channel_type x)
get_channel_type_list (x:xs)
  = (get_channel_type x) ++ "." ++ (get_channel_type_list xs)
\end{code}

\subsection{Mapping Circus channel sets}
\begin{code}
mapping_CSExp :: [ZPara] -> CSExp -> String

mapping_CSExp spec (CChanSet xs)
  = "{| " ++ (mapping_CSExp_get_cs spec xs) ++ " |}"
mapping_CSExp spec (ChanSetDiff a b)
  = "diff("++(mapping_CSExp spec a)++","
    ++(mapping_CSExp spec b)++")"
mapping_CSExp spec (ChanSetInter a b)
  = "inter("++(mapping_CSExp spec a)++","
    ++(mapping_CSExp spec b)++")"
mapping_CSExp spec (ChanSetUnion a b)
  = "union("++(mapping_CSExp spec a)++","
    ++(mapping_CSExp spec b)++")"
mapping_CSExp spec (CSEmpty)
  = "{| |}"
mapping_CSExp spec (CSExpr zn)
  = zn
\end{code}
Transforms a channel set into a list of channels in the CSP format
\begin{code}
mapping_CSExp_get_cs spec []
  = ""
mapping_CSExp_get_cs spec [x]
  = x
mapping_CSExp_get_cs spec (c:cs)
  = c ++ "," ++ (mapping_CSExp_get_cs spec cs)
\end{code}

\subsection{Mapping Circus Processes Declaration}

\begin{code}
mapping_ProcDecl :: [ZPara] -> ProcDecl -> String
--mapping_ProcDecl spec (CGenProcess zn (x:xs) pd)
--  = (show zn) ++ " = "
mapping_ProcDecl spec (CProcess zn pd)
  = "\n" ++ zn ++ (mapping_ProcessDef spec pd)
mapping_ProcDecl spec _
  = ""
\end{code}

\subsection{Mapping Circus Processes Definition}
NOTE:Process definition index is not yet defined.
\begin{code}
mapping_ProcessDef :: [ZPara] -> ProcessDef -> String
mapping_ProcessDef spec (ProcDef cp)
  = " = " ++ (mapping_CProc spec cp)
mapping_ProcessDef spec (ProcDefSpot xl pd)
  = "("++(mapping_ZGenFilt_list spec xl ) ++ ")" ++ (mapping_ProcessDef spec pd)
-- mapping_ProcessDef spec (ProcDefIndex (x:xs) pd)
--  = "("++(getZGenFilt (x:xs)) ++ ") = " ++ (mapping_CProc spec cp)
\end{code}
\begin{code}
mapping_ZGenFilt :: [ZPara] -> ZGenFilt -> String
mapping_ZGenFilt spec (Choose v _) = fst v

mapping_ZGenFilt_list :: [ZPara] -> [ZGenFilt] -> String
mapping_ZGenFilt_list spec [x]
  = (mapping_ZGenFilt spec x)
mapping_ZGenFilt_list spec (x:xs)
  = (mapping_ZGenFilt spec x) ++ "," ++ (mapping_ZGenFilt_list spec xs)
\end{code}


\subsection{Mapping Circus Processes}
Note: $CGenProc$ ($N[Exp^{+}]$), $CSimpIndexProc$, and $CParamProc$ ($N(Exp^{+})$) are not yet implemented.
\begin{code}
mapping_CProc :: [ZPara] -> CProc -> String

mapping_CProc spec (CExtChoice a b)
  = "( " ++ (mapping_CProc spec a)
    ++ " [] "
    ++ (mapping_CProc spec b) ++ " )"
mapping_CProc spec (CHide a cs)
  = "( " ++ (mapping_CProc spec a)
    ++  " \\ "
    ++ mapping_predicate_cs (cs) ++ " )"
mapping_CProc spec (CIntChoice a b)
  = "( " ++ (mapping_CProc spec a)
    ++ " |~| "
    ++ (mapping_CProc spec b) ++ " )"
mapping_CProc spec (CInterleave a b)
  = "( " ++ (mapping_CProc spec a)
    ++ " ||| "
    ++ (mapping_CProc spec b) ++ " )"
mapping_CProc spec (CircusProc zn)
  = zn
mapping_CProc spec (CParParal cs a b)
  = "( " ++ (mapping_CProc spec a)
    ++ " [| "
    ++ mapping_predicate_cs (cs)
    ++ " |] "
    ++ (mapping_CProc spec b) ++ " )"
mapping_CProc spec (CSeq a b)
  = "( " ++ (mapping_CProc spec a)
    ++ " ; "
    ++ (mapping_CProc spec b) ++ " )"
mapping_CProc spec (CRepExtChProc [(Choose (x,[]) s)] a)
  = "[] "
    ++  x
    ++ " : "
    ++ (mapping_ZExpr (get_delta_names spec) s)
    ++ " @ "
    ++ (mapping_CProc spec a)
mapping_CProc spec (CRepIntChProc [(Choose (x,[]) s)] a)
  = "|~| "
    ++  x
    ++ " : "
    ++ (mapping_ZExpr (get_delta_names spec) s)
    ++ " @ "
    ++ (mapping_CProc spec a)
mapping_CProc spec (CRepInterlProc [(Choose (x,[]) s)] a)
  = "|||"
    ++  x
    ++ " : "
    ++ (mapping_ZExpr (get_delta_names spec) s)
    ++ " @ "
    ++ (mapping_CProc spec a)
mapping_CProc spec (CRepParalProc cse [(Choose (x,[]) s)] a)
  = " [| "
    ++ mapping_predicate_cs (cse)
    ++ " |] "
    ++  x
    ++ " : "
    ++ (mapping_ZExpr (get_delta_names spec) s)
    ++ " @ "
    ++ (mapping_CProc spec a)
mapping_CProc spec (CRepSeqProc [(Choose (x,[]) s)] a)
  = "; "
    ++  x
    ++ " : "
    ++ (mapping_ZExpr (get_delta_names spec) s)
    ++ " @ "
    ++ (mapping_CProc spec a)
mapping_CProc spec (ProcStalessMain pps ca)
  = "\n\tlet " ++ (mapping_PPar_list spec pps)
    ++ "within " ++ (mapping_CAction spec ca)
-- (mapping_CProc spec CGenProc zn (x:xs))
--   = undefined
mapping_CProc spec (CParamProc zn (x:xs))
   = zn ++ "(" ++ (mapping_ZTuple (x:xs)) ++ ")"
-- (mapping_CProc spec CSimpIndexProc zn (x:xs))
--   = undefined
-- (mapping_CProc spec ProcMain zp (x:xs) ca)
--   = undefined
mapping_CProc spec (CProcRename n (zv:zvs) (xp:xps))
  = n ++"[["++ (map_rename spec (zv:zvs) (xp:xps)) ++"]]"
mapping_CProc spec x
  = fail ("not implemented by mapping_CProc: " ++ show x)
\end{code}
\begin{code}
map_rename spec [y] [x]
  = (mapping_Comm spec y)++ " <- "++ (mapping_Comm spec x)
map_rename spec (y:zvs) (x:xps)
  = (mapping_Comm spec y)++ " <- "++ (mapping_Comm spec x)++", "++(map_rename spec zvs xps)
map_rename _ [] _ = ""
map_rename _ _ [] = ""
\end{code}
\subsection{Mapping Circus Processes Paragraphs}
NOTE: $CNameSet$ and $ProcZPara$ is not yet implmented
\begin{code}
mapping_PPar :: [ZPara] -> PPar -> String
--mapping_PPar spec (CNameSet zn nse)
--  = undefined
mapping_PPar spec (CParAction zn (CircusAction (CActionCommand (CVResDecl ls a ))))
  = zn ++"("++ (mapping_ZGenFilt_list spec ls) ++ ") =" ++ (mapping_CAction spec a)
mapping_PPar spec (CParAction zn pa)
  = zn ++ (mapping_ParAction spec pa)
mapping_PPar spec x
  = fail ("Not implemented by mapping_PPar: " ++ show x)
--mapping_PPar spec (ProcZPara zp)
--  = undefined
\end{code}
\begin{code}
mapping_PPar_list :: [ZPara] -> [PPar] -> String
mapping_PPar_list spec []
  = ""
mapping_PPar_list spec [x]
  = mapping_PPar spec x ++ "\n\t"
mapping_PPar_list spec (x:xs)
  = (mapping_PPar spec x) ++ "\n\t\t" ++ (mapping_PPar_list spec xs)
\end{code}

\subsection{Mapping Parameterised Circus Actions}
\begin{code}
mapping_ParAction :: [ZPara] -> ParAction -> String
mapping_ParAction spec (CircusAction ca)
  = " = " ++ (mapping_CAction spec ca)
mapping_ParAction spec (ParamActionDecl xl pa)
  = "("++(mapping_ZGenFilt_list spec xl ) ++ ") = " ++ (mapping_ParAction spec pa)
\end{code}
}
\subsection{Mapping Circus Actions}
NOTE: $CActionSchemaExpr$, $CSPNSInter$, $CSPParAction$ is not yet implemented.

\begin{code}
mapping_CAction :: [ZPara] -> CAction -> ZName
mapping_CAction spec (CActionCommand cc)
  = mapping_CCommand spec cc
mapping_CAction spec (CActionName zn)
  = zn
--mapping_CAction spec (CActionSchemaExpr zse)
--  = undefined
\end{code}
\begin{circus}
\Upsilon_A(c?x : P \then A)
\defs~\tco{c?x :\{x | x <- $\delta(c)$,$\Upsilon_{\mathbb{B}}(P(x))$\} -> $\Upsilon_A(A)$}
\end{circus}

\begin{code}
mapping_CAction spec (CSPCommAction (ChanComm c [ChanInpPred x p]) a)
  = case np of
    "true" -> c ++ "?"++ x ++ " : { x | x <- "++ (get_c_chan_type spec c (get_chan_list spec)) ++ "} -> ("++ (mapping_CAction spec a)++")"
    _ -> c ++ "?"++ x ++ " : { x | x <- "++ (get_c_chan_type spec c (get_chan_list spec)) ++ ", "++ (mapping_predicate (get_delta_names spec) p) ++ "} -> ("++ (mapping_CAction spec a)++")"
    where
      np = (mapping_predicate (get_delta_names spec) p)
\end{code}
\begin{circus}
\Upsilon_A(c?x\then A)\circdef~\tco{c?x -> } \Upsilon_A(A)
\end{circus}

% \begin{circus}
% \Upsilon_A(c.v\then\ A)\circdef~\tco{c.v -> }\Upsilon_A(A)
% \end{circus}
% \begin{code}
% mapping_CAction spec (CSPCommAction (ChanComm c [ChanDotExp (ZVar (x,y))]) a)
%   = (get_channel_name spec (ChanComm c [ChanDotExp (ZVar (x,y))]))
%     ++ " -> "
%     ++ show x
%     ++ mapping_CAction spec (a)
% \end{code}

\begin{circus}
\Upsilon_A(c!v \then\ A)\circdef~\tco{c!v -> }\Upsilon_A(A)
\end{circus}
\begin{code}
mapping_CAction spec (CSPCommAction (ChanComm c [ChanOutExp (ZVar (x,[]))]) a)
  = (get_channel_name spec (ChanComm c [ChanOutExp (ZVar (x,[]))]))
    ++ " -> "
    ++ mapping_CAction spec (a) ++ ""

mapping_CAction spec (CSPCommAction (ChanComm c lst) a)
  = (get_channel_name spec (ChanComm c lst))
    ++ " -> "
    ++ mapping_CAction spec (a) ++ ""
\end{code}


\begin{circus}
\Upsilon_A(c\then\ A)\circdef~\tco{c -> }\Upsilon_A(A)
\end{circus}
\begin{code}
mapping_CAction spec (CSPCommAction c a)
  = (get_channel_name spec c)
    ++ " -> "
    ++ mapping_CAction spec (a) ++ ""
\end{code}

\begin{circus}
\Upsilon_A(A \extchoice B) \circdef~\Upsilon_A(A) ~\tco{[]} \Upsilon_A(B)
\end{circus}
\begin{code}
mapping_CAction spec (CSPExtChoice a b)
  = "( " ++ mapping_CAction spec (a)
    ++ " [] "
    ++ mapping_CAction spec (b) ++ ")"
\end{code}

\begin{circus}
\Upsilon_A(g \& A)\circdef~\Upsilon_{\mathbb{B}}(g)~\tco{\&}~\Upsilon_A(A)
\end{circus}
\begin{code}
mapping_CAction spec (CSPGuard g ca)
 -- I'm using the True Guard
  -- and False Guard laws directly
  -- into the translation.
  = case guard of
    "true" -> (mapping_CAction spec ca) -- True Law (true & A = A)
    "false" -> "STOP"                   -- False Law (false & A = Stop)
    _ -> "( " ++ guard ++ " & " ++ (mapping_CAction spec ca) ++ " )"
  where guard = (mapping_predicate (get_delta_names spec) g)
\end{code}

\begin{circus}
\Upsilon_A(A \circhide cs) \circdef~\Upsilon_A(A)~\tco{\textbackslash} \Upsilon_{\mathbb{P}^{cs}} (cs)
\end{circus}
\begin{code}
mapping_CAction spec (CSPHide a cs)
  = "( " ++ mapping_CAction spec (a)
    ++  "\\"
    ++ mapping_predicate_cs (cs) ++ " )"
\end{code}

\begin{circus}
\Upsilon_A(A \intchoice B) \circdef~\Upsilon_A(A)~\tco{|\textasciitilde|} \Upsilon_A(B)
\end{circus}
\begin{code}
mapping_CAction spec (CSPIntChoice a b)
  = "( " ++ mapping_CAction spec (a)
    ++ " |~| "
    ++ mapping_CAction spec (b) ++ " )"
\end{code}
% \begin{code}
% mapping_CAction spec (CSPInterleave ca cb)
%   = mapping_CAction spec (ca)
%     ++ " ||| "
%     ++ mapping_CAction spec (cb)
% \end{code}

\begin{circus}
\Upsilon_A(A |[ns1 | ns2]| B) \circdef~\Upsilon_A(A)~\tco{|||}~\Upsilon_A(B)
\end{circus}
\begin{code}
mapping_CAction spec (CSPNSInter ns1 ns2 a b)
  = "( " ++ mapping_CAction spec (a)
    ++ "|||"
    ++ mapping_CAction spec (b) ++ " )"
\end{code}

\begin{circus}
\Upsilon_A(A\lpar ns1|cs|ns2\rpar B)\circdef~\Upsilon_A(A)~\tco{[|}~\Upsilon_{\mathbb{P}^{cs}}(cs)\tco{|]}\Upsilon_A(B)
\end{circus}
\begin{code}
mapping_CAction spec (CSPNSParal ns1 cs ns2 a b)
  = "( " ++ mapping_CAction spec (a)
    ++ " [| "
    ++ mapping_predicate_cs (cs)
    ++ " |] "
    ++ mapping_CAction spec (b) ++ " )"
\end{code}
\begin{code}
mapping_CAction spec (CSPParAction zn xl)
  = zn ++ "(" ++ concat (map_mp1 mapping_ZExpr (get_delta_names spec) xl) ++ ")"
\end{code}
% \begin{code}
% mapping_CAction spec (CSPParal cs a b)
%   = mapping_CAction spec (a)
%     ++ " [| "
%     ++ mapping_predicate_cs (cs)
%     ++ " |] "
%     ++ mapping_CAction spec (b)
% \end{code}

\begin{circus}
\Upsilon (\circmu X \circspot\ A(X )) \circdef~\tco{let Arec =}~\Upsilon_A(A(A_{rec}))~\tco{within Arec}
\end{circus}
\begin{code}
mapping_CAction spec (CSPRecursion x a)
  = "( " ++ "let "
    ++ x
    ++ " = "
    ++ mapping_CAction spec (a)
    ++ " within "
    ++ x ++ " )"
\end{code}

\begin{circus}
\Upsilon_A(\Extchoice x : S \circspot A)\circdef~\tco{[] x :}~\Upsilon_{\mathbb{P}}(S)~\tco{@}~\Upsilon_A(A)
\end{circus}
\begin{code}
mapping_CAction spec (CSPRepExtChoice [(Choose (x,[]) s)] a)
  = "( " ++ "[] "
    ++  x
    ++ " : "
    ++ (mapping_ZExpr (get_delta_names spec) s)
    ++ " @ "
    ++ mapping_CAction spec (a) ++ " )"
\end{code}

\begin{circus}
\Upsilon_A(\Intchoice x : S \circspot A)\circdef~\tco{|\textasciitilde| x :}~\Upsilon_{\mathbb{P}}(S)~\tco{@}~\Upsilon_A(A)
\end{circus}
\begin{code}
mapping_CAction spec (CSPRepIntChoice [(Choose (x,[]) s)] a)
  = "( " ++ "|~| "
    ++  x
    ++ " : "
    ++ (mapping_ZExpr (get_delta_names spec) s)
    ++ " @ "
    ++ mapping_CAction spec (a) ++ " )"
\end{code}

% \begin{code}
% mapping_CAction spec (CSPRepInterl [(Choose (x,[]) s)] a)
%   = "||| "
%     ++  show x
%     ++ " : "
%     ++ (mapping_ZExpr (get_delta_names spec) s)
%     ++ " @ "
%     ++ mapping_CAction spec (a)
% \end{code}

\begin{circus}
\Upsilon_A(\Interleave x : S \circspot \lpar \emptyset \rpar A) \circdef~\tco{||| x:}\Upsilon_{\mathbb{P}}(S)~\tco{@}~\Upsilon_A(A)
\end{circus}
\begin{code}
mapping_CAction spec (CSPRepInterlNS [(Choose (x,[]) s)] NSExpEmpty a)
  = "( " ++ "||| "
    ++  x
    ++ " : "
    ++ (mapping_ZExpr (get_delta_names spec) s)
    ++ " @ "
    ++ mapping_CAction spec (a) ++ " )"
\end{code}

\begin{circus}
\Upsilon_A(\lpar cs \rpar x : S \circspot \lpar \emptyset \rpar A)\circdef~\tco{[|}\Upsilon_{\mathbb{P}^{cs}}(cs)\tco{|] x :}\Upsilon_{\mathbb{P}}(S)~\tco{@}~\Upsilon_A(A)
\end{circus}
\begin{code}
mapping_CAction spec (CSPRepParalNS cs [(Choose (x,[]) s)] NSExpEmpty a)
  = "( " ++ "[| "
    ++ mapping_predicate_cs (cs)
    ++ " |] "
    ++  x
    ++ " : "
    ++ (mapping_ZExpr (get_delta_names spec) s)
    ++ " @ "
    ++ mapping_CAction spec (a) ++ " )"
\end{code}

\begin{circus}
\Upsilon_A(\Semi x : S \circspot A)\circdef~\tco{; x :}\Upsilon_{seq}(S)~\tco{@}~\Upsilon_A(A)
\end{circus}
\begin{code}
mapping_CAction spec (CSPRepSeq [(Choose (x,[]) s)] a)
  = "( " ++ "; "
    ++  show x
    ++ " : "
    ++ (mapping_ZExpr (get_delta_names spec) s)
    ++ " @ "
    ++ mapping_CAction spec (a) ++ " )"
\end{code}

\begin{circus}
\Upsilon_A(A \circseq B) \circdef~\Upsilon_A(A)~\tco{;}~\Upsilon_A(B)
\end{circus}
\begin{code}
mapping_CAction spec (CSPSeq a b)
  = "( " ++ mapping_CAction spec (a)
    ++ " ; "
    ++ mapping_CAction spec (b) ++ " )"
\end{code}

\begin{circus}
\Upsilon_A(\Skip) \defs~\tco{SKIP}
\end{circus}
\begin{code}
mapping_CAction spec (CSPSkip)
  = "SKIP"
\end{code}

\begin{circus}
\Upsilon_A(\Stop) \defs~\tco{STOP}
\end{circus}
\begin{code}
mapping_CAction spec (CSPStop)
  = "STOP"
\end{code}

\begin{circus}
\Upsilon_A(\Chaos) \defs~\tco{CHAOS}
\end{circus}
\begin{code}
mapping_CAction spec (CSPChaos)
  = "CHAOS"
\end{code}
\begin{code}
mapping_CAction spec x
  = fail ("not implemented by mapping_CAction: " ++ show x)
\end{code}

\subsection{Mapping Circus Commands}
NOTE: $CAssumpt$, $CommandBrace$, $CommandBracket$ not implemented yet
\begin{code}
mapping_CCommand :: [ZPara] -> CCommand -> ZName
mapping_CCommand spec (CAssign (x:xs) (y:ys))
  = error ("Assignments are not available in CSP")
mapping_CCommand spec (CAssumpt (x:xs) zpa zpb)
  = error ("Assumptions are not available in CSP")
mapping_CCommand spec (CIf cga)
  = mapping_CGActions spec cga
-- mapping_CCommand spec (CommandBrace zp)
--   = undefined
-- mapping_CCommand spec (CommandBracket zp)
--   = undefined
-- mapping_CCommand spec (CResDecl (x:xs) ca)
--   = undefined
-- mapping_CCommand spec (CVarDecl (x:xs) ca)
--   = undefined
-- mapping_CCommand spec (CVResDecl (x:xs) ca)
--   = undefined
mapping_CCommand spec x
  = fail ("not implemented by mapping_CCommand: " ++ show x)
\end{code}

\subsection{Mapping Circus Guarded Actions}
\begin{code}
mapping_CGActions :: [ZPara] -> CGActions -> ZName
mapping_CGActions spec (CircThenElse cga1 cga2)
  = (mapping_CGActions spec cga1) ++ " [] " ++ (mapping_CGActions spec cga2)
mapping_CGActions spec (CircGAction zp ca)
  = (mapping_predicate (get_delta_names spec) zp) ++ " & " ++ (mapping_CAction spec ca)
\end{code}

\subsection{Mapping Channel Communication}
\begin{code}
mapping_Comm :: [ZPara] -> Comm -> String
mapping_Comm spec (ChanComm zn xs)
  = zn ++ (mapString mapping_CParameter spec xs)
mapping_Comm spec (ChanGenComm zn xs ys)
  = error ("Assumptions are not yet implemented")
\end{code}

\begin{code}
mapString :: (t1 -> t -> String) -> t1 -> [t] -> String
mapString f s [] = ""
mapString f s [x] = (f s x)
mapString f s (x:xs) = (f s x) ++ (mapString f s xs)
\end{code}
\begin{code}
mapping_CParameter :: [ZPara] -> CParameter -> ZName
mapping_CParameter spec (ChanInp zn)
  = zn
mapping_CParameter spec (ChanInpPred zn zp)
 = zn ++ (mapping_predicate (get_delta_names spec) zp)
mapping_CParameter spec (ChanOutExp ze)
  = mapping_ZExpr (get_delta_names spec) ze
mapping_CParameter spec (ChanDotExp ze)
  = mapping_ZExpr (get_delta_names spec) ze
\end{code}

\subsection{Mapping Circus Namesets}
\begin{code}

-- mapping_NSExp spec (NSExpEmpty)
--   = undefined
-- mapping_NSExp spec (NSExprMult (x:xs))
--   = undefined
-- mapping_NSExp spec (NSExprSngl zn)
--   = undefined
-- mapping_NSExp spec (NSHide nse1 nse2)
--   = undefined
-- mapping_NSExp spec (NSIntersect nse1 nse2)
--   = undefined
-- mapping_NSExp spec (NSUnion nse1 nse2)
--   = undefined
mapping_NSExp spec x
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
mapping_predicate lst ( (ZMember (ZTuple [a,b]) (ZVar ("\\geq",[]))))
  = (mapping_ZExpr lst a) ++ " >= " ++ (mapping_ZExpr lst b)
mapping_predicate lst ( (ZMember (ZTuple [a,b]) (ZVar (">",[]))))
  = (mapping_ZExpr lst a) ++ " > " ++ (mapping_ZExpr lst b)
mapping_predicate lst ( (ZMember (ZTuple [a,b]) (ZVar ("\\leq",[]))))
  = (mapping_ZExpr lst a) ++ " <= " ++ (mapping_ZExpr lst b)
mapping_predicate lst ( (ZMember (ZTuple [a,b]) (ZVar ("<",[]))))
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
mapping_predicate lst (ZMember (ZVar (x,[])) (ZCall (ZVar ("\\delta",[])) (ZVar (n,[]))))
  = "type("++n++")"  
mapping_predicate lst (ZMember a b)
  = "member("++(mapping_ZExpr lst a)++","++(mapping_ZExpr lst b)++")"
mapping_predicate lst x
  = fail ("not implemented by mapping_predicate: " ++ show x)
\end{code}


\subsection{Mapping Function for Channel Set Expressions}
\begin{code}
mapping_predicate_cs :: CSExp -> String
mapping_predicate_cs (cs)
  = "Union({{| c |} | c <- "++ (mapping_set_cs_exp cs) ++" })"
mapping_set_cs_exp (CChanSet x)
  = "{ "++(mapping_ZExpr_def x)++" }"
mapping_set_cs_exp (CSExpr x) 
  = x
mapping_set_cs_exp (ChanSetUnion a b)
  = "union("++ (mapping_set_cs_exp a)++","++ (mapping_set_cs_exp b) ++")"
mapping_set_cs_exp (ChanSetInter a b)
  = "inter("++ (mapping_set_cs_exp a)++","++ (mapping_set_cs_exp b) ++")"
mapping_set_cs_exp (ChanSetDiff a b)
  = "diff("++ (mapping_set_cs_exp a)++","++ (mapping_set_cs_exp b) ++")"
mapping_set_cs_exp x
  = fail ("not implemented by mapping_set_cs_exp: " ++ show x)

\end{code}

\subsection{Mapping Function for Sequence Expressions}

The mapping function for sequence expressions is defined as follows:


\begin{code}
get_channel_name :: [ZPara] -> Comm -> ZName
get_channel_name spec (ChanComm "mget" ((ChanDotExp (ZVar (x,[]))):xs))
  = "mget."++x++"?v"++x++":(type("++x++"))"
get_channel_name spec (ChanComm "mset" ((ChanDotExp (ZVar (x,[]))):xs))
  = "mset."++x++".((tag("++x++"))"++(get_channel_name_cont spec xs)++")"
get_channel_name spec (ChanComm x y)
  = x++(get_channel_name_cont spec y)
get_channel_name spec (ChanGenComm _ _ _)
  = ""
\end{code}
\begin{code}
get_channel_name_cont spec [] = ""
get_channel_name_cont spec [(ChanOutExp (ZVar v))] 
  = "."++(mapping_ZExpr (get_delta_names spec) (ZVar v))++""
get_channel_name_cont spec [(ChanOutExp v)] 
  = "."++(mapping_ZExpr (get_delta_names spec) v)++""
get_channel_name_cont spec [(ChanDotExp (ZVar v))] 
  = "."++(mapping_ZExpr (get_delta_names spec) (ZVar v))++""
get_channel_name_cont spec [(ChanDotExp v)] 
  = ".("++(mapping_ZExpr (get_delta_names spec) v)++")"
  -- = "."++(showexpr v)
get_channel_name_cont spec [(ChanInp v)] 
  = "?"++v
get_channel_name_cont spec [(ChanInpPred v x)] 
  = "?"++v++":"++(mapping_predicate (get_delta_names spec) x)
get_channel_name_cont spec ((ChanOutExp (ZVar v)) : xs) 
  = "."++(mapping_ZExpr (get_delta_names spec) (ZVar v))++""++(get_channel_name_cont spec xs)
get_channel_name_cont spec ((ChanOutExp v) : xs) 
  = "."++(mapping_ZExpr (get_delta_names spec) v)++(get_channel_name_cont spec xs)
get_channel_name_cont spec ((ChanDotExp (ZVar v)) : xs) 
  = "."++(mapping_ZExpr (get_delta_names spec) (ZVar v))++""++(get_channel_name_cont spec xs)
get_channel_name_cont spec ((ChanDotExp v) : xs) 
  = "."++(mapping_ZExpr (get_delta_names spec) v)++(get_channel_name_cont spec xs)
get_channel_name_cont spec ((ChanInp v) : xs) 
  = "?"++v++(get_channel_name_cont spec xs)
get_channel_name_cont spec ((ChanInpPred v x) : xs) 
  = "?"++v++":"++(mapping_predicate (get_delta_names spec) x)++(get_channel_name_cont spec xs)
\end{code}
\begin{code}
get_c_chan_type :: [ZPara] -> ZName -> [CDecl] -> String
get_c_chan_type spec c [(CChanDecl a b)]
  = case a == c of
      True -> mapping_ZExpr (get_delta_names spec) b
      False -> error "Channel not found"
get_c_chan_type spec c ((CChanDecl a b):xs)
  = case a == c of
      True -> mapping_ZExpr (get_delta_names spec) b
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
mapping_ZTuple [ZVar (v,_)] = v
mapping_ZTuple [ZInt x] = show (fromIntegral x)
mapping_ZTuple ((ZVar (v,_)):xs) = (v) ++ "," ++ (mapping_ZTuple xs)
mapping_ZTuple ((ZInt x):xs) = (show (fromIntegral x)) ++ "," ++ (mapping_ZTuple xs)
mapping_ZTuple _ = ""
\end{code}

\begin{code}
mapping_ZCross [ZVar ("\\int",_)] = "Int"
mapping_ZCross [ZVar (v,_)] = v
mapping_ZCross ((ZVar (v,_)):xs) = (v) ++ "." ++ (mapping_ZCross xs)
mapping_ZCross _ = ""
\end{code}

\begin{code}
-- aux functions
mapping_ZExpr_def :: [ZName] -> String
mapping_ZExpr_def [x] = (show x)
mapping_ZExpr_def (x:xs) = (show x)++","++(mapping_ZExpr_def xs)
\end{code}
\begin{code}
mapping_ZExpr_def_f f [x] = (f x)
mapping_ZExpr_def_f f (x:xs) = (f x)++","++(mapping_ZExpr_def_f f xs)
\end{code}
\begin{code}
mapping_ZExpr_def_f1 f a [x] = (f a x)
mapping_ZExpr_def_f1 f a (x:xs) = (f a x)++","++(mapping_ZExpr_def_f1 f a xs)
\end{code}

\subsection{Mapping Function for Expressions}
\begin{code}
mapping_ZExpr :: [ZName] ->  ZExpr -> String
-- (mapping_ZExpr lst {x1 : a1; . . . ; xn : an | b • E(x1, ..., xn)}) = b
-- {mapping_CAction(E(x1, ..., xn))|mapping_CAction(xi) mapping_CAction(ai),mapping_CAction spec (b)}
mapping_ZExpr lst (ZBinding _) = ""
mapping_ZExpr lst (ZCall (ZSeqDisplay x) _) = "<"++(mapping_ZExpr_def_f showexpr x)++">"
mapping_ZExpr lst (ZCall (ZVar ("*",[])) (ZTuple [ZInt m,ZInt n])) = show ((fromIntegral m)*(fromIntegral n))
mapping_ZExpr lst (ZCall (ZVar ("*",[])) (ZTuple [m,n])) = "("++mapping_ZExpr lst (n) ++ " * " ++ mapping_ZExpr lst (m)++")"
mapping_ZExpr lst (ZCall (ZVar ("+",[])) (ZTuple [ZInt m,ZInt n])) = show ((fromIntegral m)+(fromIntegral n))
mapping_ZExpr lst (ZCall (ZVar ("+",[])) (ZTuple [m,n])) = "("++mapping_ZExpr lst (n) ++ " + " ++ mapping_ZExpr lst (m)++")"
mapping_ZExpr lst (ZCall (ZVar ("-",[])) (ZTuple [ZInt m,ZInt n])) = show ((fromIntegral m)-(fromIntegral n))
mapping_ZExpr lst (ZCall (ZVar ("-",[])) (ZTuple [m,n])) = "("++mapping_ZExpr lst (n) ++ " - " ++ mapping_ZExpr lst (m)++")"
mapping_ZExpr lst (ZCall (ZVar ("\\035",[])) a) = "\035(" ++ mapping_ZExpr lst (a)++")"
mapping_ZExpr lst (ZCall (ZVar ("\\\035",[])) a) = "card("++(mapping_ZExpr lst a)++")"
mapping_ZExpr lst (ZCall (ZVar ("\\bigcap",[])) (ZTuple [a,b])) = "Inter("++(mapping_ZExpr lst a)++","++(mapping_ZExpr lst b)++")"
mapping_ZExpr lst (ZCall (ZVar ("\\bigcup",[])) (ZTuple [a,b])) = "Union("++(mapping_ZExpr lst a)++","++(mapping_ZExpr lst b)++")"
mapping_ZExpr lst (ZCall (ZVar ("\\cap",[])) (ZTuple [a,b])) = "inter("++(mapping_ZExpr lst a)++","++(mapping_ZExpr lst b)++")"
mapping_ZExpr lst (ZCall (ZVar ("\\cat",[])) (ZTuple [a,b])) = mapping_ZExpr lst (a)++"^"++mapping_ZExpr lst (b)
mapping_ZExpr lst (ZCall (ZVar ("\\cup",[])) (ZTuple [a,b])) = "union("++(mapping_ZExpr lst a)++","++(mapping_ZExpr lst b)++")"
mapping_ZExpr lst (ZCall (ZVar ("\\dcat",[])) s) = "concat("++mapping_ZExpr lst (s)++")"
mapping_ZExpr lst (ZCall (ZVar ("\\div",[])) (ZTuple [ZInt m,ZInt n])) = show ((fromIntegral m)/(fromIntegral n))
mapping_ZExpr lst (ZCall (ZVar ("\\div",[])) (ZTuple [m,n])) = "("++mapping_ZExpr lst (n) ++ " / " ++ mapping_ZExpr lst (m)++")"
mapping_ZExpr lst (ZCall (ZVar ("\\dom",[])) a) = "dom("++(mapping_ZExpr lst a)++")"
mapping_ZExpr lst (ZCall (ZVar ("\\mod",[])) (ZTuple [ZInt m,ZInt n])) = show ((fromIntegral m) `mod` (fromIntegral n))
mapping_ZExpr lst (ZCall (ZVar ("\\mod",[])) (ZTuple [m,n])) = mapping_ZExpr lst (n) ++ " % " ++ mapping_ZExpr lst (m)
mapping_ZExpr lst (ZCall (ZVar ("\\negate",[])) n) = "- " ++ mapping_ZExpr lst (n)
mapping_ZExpr lst (ZCall (ZVar ("\\oplus",[])) (ZTuple [ZVar (b,[]),ZSetDisplay [ZCall (ZVar ("\\mapsto",[])) (ZTuple [ZVar (n,[]),ZVar (x,[])])]])) = "over("++b++","++n++","++x++")"
mapping_ZExpr lst (ZCall (ZVar ("\\power",[])) a) ="Set("++(mapping_ZExpr lst a)++")"
mapping_ZExpr lst (ZCall (ZVar ("\\ran",[])) a) = "set("++(mapping_ZExpr lst a)++")"
mapping_ZExpr lst (ZCall (ZVar ("\\seq",[])) a) = "Seq("++(mapping_ZExpr lst a)++")"
mapping_ZExpr lst (ZCall (ZVar ("\\setminus",[])) (ZTuple [a,b])) = "diff("++(mapping_ZExpr lst a)++","++(mapping_ZExpr lst b)++")"
mapping_ZExpr lst (ZCall (ZVar ("head",[])) s) = "head("++mapping_ZExpr lst (s)++")"
mapping_ZExpr lst (ZCall (ZVar ("tail",[])) s) = "tail("++mapping_ZExpr lst (s)++")"
mapping_ZExpr lst (ZCall (ZVar (b,[])) (ZVar (n,[]))) = "apply("++b++","++n++")"
mapping_ZExpr lst (ZCall (ZVar ("\\upto",[])) (ZTuple [ZInt m,ZInt n])) = "{"++show(fromIntegral m)++".."++show(fromIntegral n)++"}"
mapping_ZExpr lst (ZCall (ZVar ("\\upto",[])) (ZTuple [a,b])) = "{"++(show a)++".."++(show b)++"}"
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
mapping_ZExpr lst (ZInt n) = show n
mapping_ZExpr lst (ZIntSet _ _) = ""
mapping_ZExpr lst (ZLambda _ _) = ""
mapping_ZExpr lst (ZMu _ _) = ""
mapping_ZExpr lst (ZPowerSet _ _ _) = ""
mapping_ZExpr lst (ZReln _) = ""
mapping_ZExpr lst (ZSelect _ _) = ""
mapping_ZExpr lst (ZSeqDisplay []) = "<>"
mapping_ZExpr lst (ZSeqDisplay _) = ""
mapping_ZExpr lst (ZSetComp _ _ ) = ""
mapping_ZExpr lst (ZSetDisplay [ZCall (ZVar ("\\upto",[])) (ZTuple [a,b])]) = "{"++(show a)++".."++(show b)++"}"
mapping_ZExpr lst (ZSetDisplay x) = "{"++(mapping_ZExpr_def_f1 mapping_ZExpr lst x)++"}"
mapping_ZExpr lst (ZStrange _) = ""
mapping_ZExpr lst (ZTheta _) = ""
mapping_ZExpr lst (ZTuple ls) = "("++mapping_ZTuple ls ++ ")"
mapping_ZExpr lst (ZUniverse) = ""
mapping_ZExpr lst (ZVar ("\\emptyset",[])) = "{}"
mapping_ZExpr lst (ZVar ("\\int",[])) = "Int"
-- mapping_ZExpr lst (ZVar (a,_)) = a
mapping_ZExpr lst (ZVar (a,_)) 
  = case (inListVar a lst) of
      True -> "value(v"++a++")"
      _ -> a
mapping_ZExpr lst x = fail ("not implemented by mapping_ZExpr: " ++ show x)

\end{code}
