\section{Mapping Functions - Circus to CSP}

Mapping Functions - Circus to CSP
\ignore{
\begin{code}
module MappingFunCircusCSP
where
import AST
import CRL
import FormatterToCSP


showexpr = zexpr_string (pinfo_extz 80)
\end{code}
}
\ignore{
\subsection{Mapping Circus Paragraphs}
The following functions are used to map Circus Channels into CSP. However, generic circus channels are not yet captured by the tool.
\begin{code}
mapping_Circus :: [ZPara] -> [Char]
mapping_Circus []
  = ""
mapping_Circus [x]
  = mapping_CircParagraphs x
mapping_Circus (x:xs)
  = mapping_CircParagraphs x ++ (mapping_Circus xs)
\end{code}
\begin{code}
mapping_CircParagraphs :: ZPara -> [Char]

mapping_CircParagraphs (ZFreeTypeDef (a,b) zbs)
  = "datatype " ++ a ++ " = " ++ (mapping_ZBranch_list zbs)
mapping_CircParagraphs (Process cp)
  = mapping_ProcDecl cp
mapping_CircParagraphs (CircChanSet cn c2)
  = cn ++ " = " ++ (mapping_CSExp c2) ++ "\n"
mapping_CircParagraphs (CircChannel cc2)
  = mapping_CDecl cc2
-- mapping_CircParagraphs (ZGivenSetDecl gs)
--   = undefined
-- mapping_CircParagraphs (ZSchemaDef zsn zse)
--   = undefined
-- mapping_CircParagraphs (ZAbbreviation (name,[]) (ZSetComp [Choose ("x",[]) (ZVar ("\\nat",[])),Check (ZMember (ZTuple [ZVar ("x",[]),ZInt 10]) (ZVar ("\\leq",[])))] (Just (ZCall (ZVar ("*",[])) (ZTuple [ZVar ("x",[]),ZVar ("x",[])])))) ) = undefined
-- mapping_CircParagraphs (ZPredicate zp)
--   = undefined
-- mapping_CircParagraphs (ZAxDef zgfs)
--   = undefined
-- mapping_CircParagraphs (ZGenDef zgfs)
--   = undefined
mapping_CircParagraphs x
  = fail ("not implemented by mapping_CircParagraphs: " ++ show x)
\end{code}

Definition of Free Types
\begin{code}
-- ZFreeTypeDef ("MYTYPE",[]) [ZBranch0 ("A",[]),ZBranch1 ("B",[]) (ZCross [ZVar ("\\nat",[]),ZVar ("\\nat",[])])]

mapping_ZBranch_list [x]
  = (mapping_ZBranch x)
mapping_ZBranch_list (x:xs)
  = (mapping_ZBranch x) ++ " | " ++ (mapping_ZBranch_list xs)
mapping_ZBranch (ZBranch0 (a,b))
  = a
mapping_ZBranch (ZBranch1 (a,xb) (ZCross b))
  = a ++ "." ++ (mapping_ZBranch_cross b)
mapping_ZBranch_cross [ZVar (a,b)]
  = a
mapping_ZBranch_cross ((ZVar (a,b)):xs)
  = a ++ "." ++ (mapping_ZBranch_cross xs)
\end{code}
\subsection{Mapping Circus Channels}
\begin{code}
mapping_CDecl :: [CDecl] -> [Char]
mapping_CDecl x
  = (show_chann_CChan x1)
    ++ (display_chann_CChanDecl x2)
  where x1 = filter_channels_CChan x
        x2 = filter_channels_CChanDecl x
-- mapping_CDecl (CGenChanDecl zn3 zn4 ze)
--   = undefined
\end{code}
\begin{code}
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
show_chann_CChan []
  = ""
show_chann_CChan x
  = "channel " ++ display_chann_CChan x

display_chann_CChan []
  = ""
display_chann_CChan [x]
  = x ++ "\n"
display_chann_CChan (x:xs)
  = x ++ ", " ++ (display_chann_CChan xs)
\end{code}
\begin{code}
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
display_chann_CChanDecl []
  = ""
display_chann_CChanDecl [(a,b)]
  = "channel " ++ a
    ++ " : " ++ (get_channel_type b) ++"\n"
display_chann_CChanDecl ((a,b):xs)
  = "channel " ++ a
    ++ " : " ++ (get_channel_type b)
    ++"\n" ++ (display_chann_CChanDecl xs)
\end{code}
\begin{code}
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
mapping_CSExp :: CSExp -> [Char]
mapping_CSExp (CChanSet xs)
  = "{| " ++ (mapping_CSExp_get_cs xs) ++ " |}"
mapping_CSExp (ChanSetDiff a b)
  = "diff("++(mapping_CSExp a)++","
    ++(mapping_CSExp b)++")"
mapping_CSExp (ChanSetInter a b)
  = "inter("++(mapping_CSExp a)++","
    ++(mapping_CSExp b)++")"
mapping_CSExp (ChanSetUnion a b)
  = "union("++(mapping_CSExp a)++","
    ++(mapping_CSExp b)++")"
mapping_CSExp (CSEmpty)
  = "{| |}"
mapping_CSExp (CSExpr zn)
  = show zn
\end{code}
Transforms a channel set into a list of channels in the CSP format
\begin{code}
mapping_CSExp_get_cs :: Show a => [a] -> [Char]
mapping_CSExp_get_cs []
  = ""
mapping_CSExp_get_cs [x]
  = show x
mapping_CSExp_get_cs (c:cs)
  = show c ++ "," ++ (mapping_CSExp_get_cs cs)
\end{code}

\subsection{Mapping Circus Processes Declaration}

\begin{code}
mapping_ProcDecl :: ProcDecl -> [Char]
--mapping_ProcDecl (CGenProcess zn (x:xs) pd)
--  = (show zn) ++ " = "
mapping_ProcDecl (CProcess zn pd)
  = zn ++ (mapping_ProcessDef pd)
\end{code}

\subsection{Mapping Circus Processes Definition}
NOTE:Process definition index is not yet defined.
\begin{code}
mapping_ProcessDef :: ProcessDef -> [Char]
mapping_ProcessDef (ProcDef cp)
  = " = " ++ (mapping_CProc cp)
mapping_ProcessDef (ProcDefSpot xl pd)
  = "("++(mapping_ZGenFilt_list xl ) ++ ") = " ++ (mapping_ProcessDef pd)
-- mapping_ProcessDef (ProcDefIndex (x:xs) pd)
--  = "("++(getZGenFilt (x:xs)) ++ ") = " ++ (mapping_CProc cp)
\end{code}
\begin{code}
mapping_ZGenFilt (Choose v _) = fst v
mapping_ZGenFilt_list [x]
  = (mapping_ZGenFilt x)
mapping_ZGenFilt_list (x:xs)
  = (mapping_ZGenFilt x) ++ "," ++ (mapping_ZGenFilt_list xs)
\end{code}


\subsection{Mapping Circus Processes}
Note: $CGenProc$ ($N[Exp^{+}]$), $CSimpIndexProc$, and $CParamProc$ ($N(Exp^{+})$) are not yet implemented.
\begin{code}
mapping_CProc :: CProc -> [Char]
mapping_CProc (CExtChoice a b)
  = mapping_CProc(a)
    ++ " [] "
    ++ mapping_CProc(b)
mapping_CProc (CHide a cs)
  = mapping_CProc(a)
    ++  "\\"
    ++ mapping_predicate_cs (cs)
mapping_CProc (CIntChoice a b)
  = mapping_CProc(a)
    ++ " |~| "
    ++ mapping_CProc(b)
mapping_CProc (CInterleave a b)
  = mapping_CProc(a)
    ++ "|||"
    ++ mapping_CProc(b)
mapping_CProc (CircusProc zn)
  = show zn
mapping_CProc (CParParal cs a b)
  = mapping_CProc(a)
    ++ " [| "
    ++ mapping_predicate_cs(cs)
    ++ " |] "
    ++ mapping_CProc(b)
mapping_CProc (CRepExtChProc [(Choose x s)] a)
  = "[] "
    ++  show x
    ++ " : "
    ++ mapping_set_exp(s)
    ++ " @ "
    ++ mapping_CProc(a)
mapping_CProc (CRepIntChProc [(Choose x s)] a)
  = "|~| "
    ++  show x
    ++ " : "
    ++ mapping_set_exp(s)
    ++ " @ "
    ++ mapping_CProc(a)
mapping_CProc (CRepInterlProc [(Choose x s)] a)
  = "|||"
    ++  show x
    ++ " : "
    ++ mapping_set_exp(s)
    ++ " @ "
    ++ mapping_CProc(a)
mapping_CProc (CRepParalProc cse [(Choose x s)] a)
  = " [| "
    ++ mapping_predicate_cs(cse)
    ++ " |] "
    ++  show x
    ++ " : "
    ++ mapping_set_exp(s)
    ++ " @ "
    ++ mapping_CProc(a)
mapping_CProc (CRepSeqProc [(Choose x s)] a)
  = "; "
    ++  show x
    ++ " : "
    ++ mapping_seq(s)
    ++ " @ "
    ++ mapping_CProc(a)
mapping_CProc (CSeq a b)
  = mapping_CProc(a)
    ++ " ; "
    ++ mapping_CProc(b)
mapping_CProc (ProcStalessMain pps ca)
  = "\n\tlet \n\t\t" ++ (mapping_PPar_list pps)
    ++ "within " ++ (mapping_CAction ca) ++ "\n"
-- mapping_CProc (CGenProc zn (x:xs))
--   = undefined
-- mapping_CProc (CParamProc zn (x:xs))
--   = undefined
-- mapping_CProc (CSimpIndexProc zn (x:xs))
--   = undefined
-- mapping_CProc (ProcMain zp (x:xs) ca)
--   = undefined
mapping_CProc x
  = fail ("not implemented by mapping_CProc: " ++ show x)
\end{code}

\subsection{Mapping Circus Processes Paragraphs}
NOTE: $CNameSet$ and $ProcZPara$ is not yet implmented
\begin{code}
mapping_PPar :: PPar -> [Char]
--mapping_PPar (CNameSet zn nse)
--  = undefined
mapping_PPar (CParAction zn pa)
  = zn ++ (mapping_ParAction pa)

mapping_PPar x
  = fail ("Not implemented by mapping_PPar: " ++ show x)
--mapping_PPar (ProcZPara zp)
--  = undefined
\end{code}
\begin{code}
mapping_PPar_list []
  = ""
mapping_PPar_list [x]
  = mapping_PPar x ++ "\n\t"
mapping_PPar_list (x:xs)
  = (mapping_PPar x) ++ "\n\t\t" ++ (mapping_PPar_list xs)
\end{code}

\subsection{Mapping Parameterised Circus Actions}
\begin{code}
mapping_ParAction :: ParAction -> [Char]
mapping_ParAction (CircusAction ca)
  = " = " ++ (mapping_CAction ca)
mapping_ParAction (ParamActionDecl xl pa)
  = "("++(mapping_ZGenFilt_list xl ) ++ ") = " ++ (mapping_ParAction pa)
\end{code}
}
\subsection{Mapping Circus Actions}
NOTE: $CActionSchemaExpr$, $CSPNSInter$, $CSPParAction$ is not yet implemented.

\begin{code}
mapping_CAction :: CAction -> [Char]
mapping_CAction (CActionCommand cc)
  = mapping_CCommand cc
mapping_CAction (CActionName zn)
  = zn
--mapping_CAction (CActionSchemaExpr zse)
--  = undefined
\end{code}
\begin{circus}
\Upsilon(c?x : P \then A)
\defs~\tco{c?x : \{x | x <- } \delta(c)\tco{,} \Upsilon_{\mathbb{B}} (P(x))~\tco{\}->} \Upsilon(A)
\end{circus}

% \begin{code}
% mapping_CAction (CSPCommAction (ChanComm c [ChanInpPred x (ZVar (p,[]))]) a)
%   = (get_channel_name (ChanComm c [ChanInpPred x (ZVar (p,[]))]))
%     ++ "?"
%     ++ show x
%     ++ " : \{ x | x <- "
%     ++ mapping_CAction(a)
% \end{code}
\begin{circus}
\Upsilon(c?x\then A)\circdef~\tco{c?x -> } \Upsilon(A)
\end{circus}

% \begin{circus}
% \Upsilon(c.v\then\ A)\circdef~\tco{c.v -> }\Upsilon(A)
% \end{circus}
% \begin{code}
% mapping_CAction (CSPCommAction (ChanComm c [ChanDotExp (ZVar (x,y))]) a)
%   = (get_channel_name (ChanComm c [ChanDotExp (ZVar (x,y))]))
%     ++ " -> "
%     ++ show x
%     ++ mapping_CAction(a)
% \end{code}

\begin{circus}
\Upsilon(c!v \then\ A)\circdef~\tco{c!v -> }\Upsilon(A)
\end{circus}
\begin{code}
mapping_CAction (CSPCommAction (ChanComm c [ChanOutExp (ZVar (x,[]))]) a)
  = (get_channel_name (ChanComm c [ChanOutExp (ZVar (x,[]))]))
    ++ " -> "
    ++ mapping_CAction(a)
\end{code}


\begin{circus}
\Upsilon(c\then\ A)\circdef~\tco{c -> }\Upsilon(A)
\end{circus}
\begin{code}
mapping_CAction (CSPCommAction c a)
  = (get_channel_name c)
    ++ " -> "
    ++ mapping_CAction(a)
\end{code}

\begin{circus}
\Upsilon(A \extchoice B) \circdef~\Upsilon(A) ~\tco{[]} \Upsilon(B)
\end{circus}
\begin{code}
mapping_CAction (CSPExtChoice a b)
  = mapping_CAction(a)
    ++ " [] "
    ++ mapping_CAction(b)
\end{code}

\begin{circus}
\Upsilon(g \& A)\circdef~\Upsilon_{\mathbb{B}}(g)~\tco{\&}~\Upsilon(A)
\end{circus}
\begin{code}
mapping_CAction (CSPGuard g ac)
  = mapping_predicate(g)
    ++ " & "
    ++ mapping_CAction(ac)
\end{code}

\begin{circus}
\Upsilon (A \circhide cs) \circdef~\Upsilon(A)~\tco{\textbackslash} \Upsilon_{\mathbb{P}^{cs}} (cs)
\end{circus}
\begin{code}
mapping_CAction (CSPHide a cs)
  = mapping_CAction(a)
    ++  "\\"
    ++ mapping_predicate_cs (cs)
\end{code}

\begin{circus}
\Upsilon(A \intchoice B) \circdef~\Upsilon(A)~\tco{|\textasciitilde|} \Upsilon(B)
\end{circus}
\begin{code}
mapping_CAction (CSPIntChoice a b)
  = mapping_CAction(a)
    ++ " |~| "
    ++ mapping_CAction(b)
\end{code}
\begin{code}
mapping_CAction (CSPInterleave ca cb)
  = mapping_CAction(ca)
    ++ " ||| "
    ++ mapping_CAction(cb)
\end{code}

\begin{circus}
\Upsilon(A |[ns1 | ns2]| B) \circdef~\Upsilon(A)~\tco{|||}~\Upsilon(B)
\end{circus}
\begin{code}
mapping_CAction (CSPNSInter ns1 ns2 a b)
  = mapping_CAction(a)
    ++ "|||"
    ++ mapping_CAction(b)
\end{code}

\begin{circus}
\Upsilon(A\lpar ns1|cs|ns2\rpar B)\circdef~\Upsilon(A)~\tco{[|}~\Upsilon_{\mathbb{P}^{cs}}(cs)\tco{|]}\Upsilon(B)
\end{circus}
\begin{code}
mapping_CAction (CSPNSParal ns1 cs ns2 a b)
  = mapping_CAction(a)
    ++ " [| "
    ++ mapping_predicate_cs(cs)
    ++ " |] "
    ++ mapping_CAction(b)
\end{code}
% \begin{code}
% --mapping_CAction (CSPParAction zn xl)
% --  = (show zn)
% --    ++ "(" ++ (mapping_ZGenFilt_list xl) ++ ")"
% \end{code}
% \begin{code}
% mapping_CAction (CSPParal cs a b)
%   = mapping_CAction(a)
%     ++ " [| "
%     ++ mapping_predicate_cs(cs)
%     ++ " |] "
%     ++ mapping_CAction(b)
% \end{code}

\begin{circus}
\Upsilon (\circmu X \circspot\ A(X )) \circdef~\tco{let Arec =}~\Upsilon(A(A_{rec}))~\tco{within Arec}
\end{circus}
\begin{code}
mapping_CAction (CSPRecursion x a)
  = "let "
    ++ x
    ++ " = "
    ++ mapping_CAction(a)
    ++ " within "
    ++ x
\end{code}

\begin{circus}
\Upsilon(\Extchoice x : S \circspot A)\circdef~\tco{[] x :}~\Upsilon_{\mathbb{P}}(S)~\tco{@}~\Upsilon(A)
\end{circus}
\begin{code}
mapping_CAction (CSPRepExtChoice [(Choose x s)] a)
  = "[] "
    ++  show x
    ++ " : "
    ++ mapping_set_exp(s)
    ++ " @ "
    ++ mapping_CAction(a)
\end{code}

\begin{circus}
\Upsilon(\Intchoice x : S \circspot A)\circdef~\tco{|\textasciitilde| x :}~\Upsilon_{\mathbb{P}}(S)~\tco{@}~\Upsilon(A)
\end{circus}
\begin{code}
mapping_CAction (CSPRepIntChoice [(Choose x s)] a)
  = "|~| "
    ++  show x
    ++ " : "
    ++ mapping_set_exp(s)
    ++ " @ "
    ++ mapping_CAction(a)
\end{code}

% \begin{code}
% mapping_CAction (CSPRepInterl [(Choose x s)] a)
%   = "||| "
%     ++  show x
%     ++ " : "
%     ++ mapping_set_exp(s)
%     ++ " @ "
%     ++ mapping_CAction(a)
% \end{code}

\begin{circus}
\Upsilon(\Interleave x : S \circspot \lpar \emptyset \rpar A) \circdef~\tco{||| x:}\Upsilon_{\mathbb{P}}(S)~\tco{@}~\Upsilon(A)
\end{circus}
\begin{code}
mapping_CAction (CSPRepInterlNS [(Choose x s)] NSExpEmpty a)
  = "||| "
    ++  show x
    ++ " : "
    ++ mapping_set_exp(s)
    ++ " @ "
    ++ mapping_CAction(a)
\end{code}

\begin{circus}
\Upsilon(\lpar cs \rpar x : S \circspot \lpar \emptyset \rpar A)\circdef~\tco{[|}\Upsilon_{\mathbb{P}^{cs}}(cs)\tco{|] x :}\Upsilon_{\mathbb{P}}(S)~\tco{@}~\Upsilon(A)
\end{circus}
\begin{code}
mapping_CAction (CSPRepParalNS cs [(Choose x s)] NSExpEmpty a)
  = "[| "
    ++ mapping_predicate_cs (cs)
    ++ " |] "
    ++  show x
    ++ " : "
    ++ mapping_set_exp(s)
    ++ " @ "
    ++ mapping_CAction(a)
\end{code}

\begin{circus}
\Upsilon(\Semi x : S \circspot A)\circdef~\tco{; x :}\Upsilon_{seq}(S)~\tco{@}~\Upsilon(A)
\end{circus}
\begin{code}
mapping_CAction (CSPRepSeq [(Choose x s)] a)
  = "; "
    ++  show x
    ++ " : "
    ++ mapping_seq(s)
    ++ " @ "
    ++ mapping_CAction(a)
\end{code}

\begin{circus}
\Upsilon(A \circseq B) \circdef~\Upsilon(A)~\tco{;}~\Upsilon(B)
\end{circus}
\begin{code}
mapping_CAction (CSPSeq a b)
  = mapping_CAction(a)
    ++ " ; "
    ++ mapping_CAction(b)
\end{code}

\begin{circus}
\Upsilon(\Skip) \defs~\tco{SKIP}
\end{circus}
\begin{code}
mapping_CAction (CSPSkip)
  = "SKIP"
\end{code}

\begin{circus}
\Upsilon(\Stop) \defs~\tco{STOP}
\end{circus}
\begin{code}
mapping_CAction (CSPStop)
  = "STOP"
\end{code}

\begin{circus}
\Upsilon(\Chaos) \defs~\tco{CHAOS}
\end{circus}
\begin{code}
mapping_CAction (CSPChaos)
  = "CHAOS"
\end{code}
\begin{code}
mapping_CAction x
  = fail ("not implemented by mapping_CAction: " ++ show x)
\end{code}

\subsection{Mapping Circus Commands}
NOTE: $CAssumpt$, $CommandBrace$, $CommandBracket$ not implemented yet
\begin{code}
mapping_CCommand :: CCommand -> [Char]
mapping_CCommand (CAssign (x:xs) (y:ys))
  = error ("Assignments are not available in CSP")
mapping_CCommand (CAssumpt (x:xs) zpa zpb)
  = undefined
mapping_CCommand (CIf cga)
  = mapping_CGActions cga
-- mapping_CCommand (CommandBrace zp)
--   = undefined
-- mapping_CCommand (CommandBracket zp)
--   = undefined
-- mapping_CCommand (CResDecl (x:xs) ca)
--   = undefined
-- mapping_CCommand (CVarDecl (x:xs) ca)
--   = undefined
-- mapping_CCommand (CVResDecl (x:xs) ca)
--   = undefined
mapping_CCommand x
  = fail ("not implemented by mapping_CCommand: " ++ show x)
\end{code}

\subsection{Mapping Circus Guarded Actions}
\begin{code}
mapping_CGActions :: CGActions -> [Char]
mapping_CGActions (CircThenElse cga1 cga2)
  = (mapping_CGActions cga1) ++ " [] " ++ (mapping_CGActions cga2)
mapping_CGActions (CircGAction zp ca)
  = (mapping_predicate zp) ++ " & " ++ (mapping_CAction ca)
\end{code}

\subsection{Mapping Channel Communication}
\begin{code}
mapping_Comm :: Comm -> [Char]
mapping_Comm (ChanComm zn xs)
  = zn ++ (mapString mapping_CParameter xs)
mapping_Comm (ChanGenComm zn xs ys)
  = undefined
\end{code}
\begin{code}
mapString f [] = ""
mapString f [x] = (f x)
mapString f (x:xs) = (f x) ++ (mapString f xs)
\end{code}
\begin{code}
mapping_CParameter :: CParameter -> [Char]
mapping_CParameter (ChanInp zn)
  = zn
--mapping_CParameter (ChanInpPred zn zp)
--  = zn ++ (mapping_predicate zp)
-- mapping_CParameter (ChanOutExp ze)
--   = undefined
-- mapping_CParameter (ChanDotExp ze)
--   = undefined
mapping_CParameter x
  = fail ("not implemented by mapping_CParameter: " ++ show x)
\end{code}

\subsection{Mapping Circus Namesets}
\begin{code}
mapping_NSExp :: NSExp -> [Char]
-- mapping_NSExp (NSExpEmpty)
--   = undefined
-- mapping_NSExp (NSExprMult (x:xs))
--   = undefined
-- mapping_NSExp (NSExprSngl zn)
--   = undefined
-- mapping_NSExp (NSHide nse1 nse2)
--   = undefined
-- mapping_NSExp (NSIntersect nse1 nse2)
--   = undefined
-- mapping_NSExp (NSUnion nse1 nse2)
--   = undefined
mapping_NSExp x
  = fail ("not implemented by mapping_NSExp: " ++ show x)
\end{code}

\section{Mapping Functions from Circus to CSP - Based on D24.1 - COMPASS}

\subsection{Mapping Functions for Numbers}

 The mapping function for set expressions is defined as follows:

\begin{code}

mapping_numbers :: ZExpr -> [Char]
mapping_numbers (ZCall (ZVar ("+",[])) (ZTuple [m,n]))
  = mapping_numbers (n) ++ "+" ++ mapping_numbers (m)
mapping_numbers (ZCall (ZVar ("-",[])) (ZTuple [m,n]))
  = mapping_numbers (n) ++ "-" ++ mapping_numbers (m)
mapping_numbers (ZCall (ZVar ("\\negate",[])) n)
  = "-" ++ mapping_numbers (n)
mapping_numbers (ZCall (ZVar ("*",[])) (ZTuple [m,n]))
  = mapping_numbers (n) ++ "*" ++ mapping_numbers (m)
mapping_numbers (ZCall (ZVar ("\\div",[])) (ZTuple [m,n]))
  = mapping_numbers (n) ++ "/" ++ mapping_numbers (m)
mapping_numbers (ZCall (ZVar ("\\mod",[])) (ZTuple [m,n]))
  = mapping_numbers (n) ++ "%" ++ mapping_numbers (m)
mapping_numbers (ZInt n)
  = show n
mapping_numbers (ZVar (n,[]))
  = n
mapping_numbers x
  = fail ("not implemented by mapping_numbers: " ++ show x)

\end{code}
\subsection{Mapping Functions for Predicates}

\begin{code}
mapping_predicate :: ZPred -> [Char]
-- NOt sure what "if then  else" is about
-- mapping_predicate (ZIf_Then_Else b x1 x2)
--   = "if " ++ (mapping_predicate b) ++
--     " then  " ++ (mapping_predicate x1) ++
--     " else " ++ (mapping_predicate x2)
mapping_predicate ( (ZMember (ZTuple [a,b]) (ZVar ("\\geq",[]))))
  = (mapping_numbers a) ++ " >= " ++ (mapping_numbers b)
mapping_predicate ( (ZMember (ZTuple [a,b]) (ZVar (">",[]))))
  = (mapping_numbers a) ++ " > " ++ (mapping_numbers b)
mapping_predicate ( (ZMember (ZTuple [a,b]) (ZVar ("\\leq",[]))))
  = (mapping_numbers a) ++ " <= " ++ (mapping_numbers b)
mapping_predicate ( (ZMember (ZTuple [a,b]) (ZVar ("<",[]))))
  = (mapping_numbers a) ++ " < " ++ (mapping_numbers b)
mapping_predicate ( (ZNot (ZEqual a b)))
  = (mapping_numbers a) ++ " != " ++ (mapping_numbers b)
mapping_predicate ( (ZEqual a b))
  = (mapping_numbers a) ++ " = " ++ (mapping_numbers b)
mapping_predicate ( (ZNot b))
  = "not " ++ (mapping_predicate b)
mapping_predicate (ZOr a b)
  = (mapping_predicate a) ++ " or " ++ (mapping_predicate b)
mapping_predicate (ZAnd a b)
  = (mapping_predicate a) ++ " and " ++ (mapping_predicate b)
mapping_predicate (ZTrue{reason=[]})
  = "true"
mapping_predicate (ZFalse{reason=[]})
  = "false"
mapping_predicate (ZMember a b)
  = "member("++(mapping_set_exp a)++","++(mapping_set_exp b)++")"
mapping_predicate x
  = fail ("not implemented by mapping_predicate: " ++ show x)
\end{code}

\subsection{Mapping Function for Set Expressions}
\begin{code}
mapping_set_exp :: ZExpr -> [Char]
mapping_set_exp (ZVar ("\\emptyset",[]))
  = "{}"
mapping_set_exp (ZSetDisplay [ZCall (ZVar ("\\upto",[])) (ZTuple [a,b])])
  = "{"++(show a)++".."++(show b)++"}"
mapping_set_exp (ZSetDisplay x)
  = "{"++(mapping_seq_def show x)++"}"
mapping_set_exp ((ZCall (ZVar ("\\cup",[])) (ZTuple [a,b])))
  = "union("++mapping_set_exp(a)++","++mapping_set_exp(b)++")"
mapping_set_exp ((ZCall (ZVar ("\\cap",[])) (ZTuple [a,b])))
  = "inter("++mapping_set_exp(a)++","++mapping_set_exp(b)++")"
mapping_set_exp ((ZCall (ZVar ("\\setminus",[])) (ZTuple [a,b])))
  = "diff("++mapping_set_exp(a)++","++mapping_set_exp(b)++")"
mapping_set_exp ((ZCall (ZVar ("\\bigcup",[])) (ZTuple [a,b])))
  = "Union("++mapping_set_exp(a)++","++mapping_set_exp(b)++")"
mapping_set_exp ((ZCall (ZVar ("\\bigcap",[])) (ZTuple [a,b])))
  = "Inter("++mapping_set_exp(a)++","++mapping_set_exp(b)++")"
mapping_set_exp (ZCall (ZVar ("\\\035",[])) a)
  = "card("++mapping_set_exp(a)++")"
mapping_set_exp (ZCall (ZVar ("\\ran",[])) a)
  = "set("++mapping_set_exp(a)++")"
mapping_set_exp (ZCall (ZVar ("\\power",[])) a)
  ="Set("++mapping_set_exp(a)++")"
mapping_set_exp (ZCall (ZVar ("\\seq",[])) a)
  = "Seq("++mapping_set_exp(a)++")"
mapping_set_exp (ZVar (x,_))
  = show x
mapping_set_exp x
  = fail ("not implemented by mapping_set_exp: " ++ show x)

-- mapping_set_exp ({x1 : a1; . . . ; xn : an | b • E(x1, ..., xn)}) = b
-- {mapping_CAction(E(x1, ..., xn))|mapping_CAction(xi) mapping_CAction(ai),mapping_CAction(b)}
\end{code}
\subsection{Mapping Function for Channel Set Expressions}
\begin{code}
mapping_predicate_cs :: CSExp -> [Char]
mapping_predicate_cs (cs)
  = "Union({{| c |} | c <- "++mapping_set_cs_exp(cs)++"})"

mapping_set_cs_exp :: CSExp -> [Char]
mapping_set_cs_exp (CChanSet x)
  = "{"++(mapping_seq_def show x)++"}"
mapping_set_cs_exp (ChanSetUnion a b)
  = "union("++mapping_set_cs_exp(a)++","++mapping_set_cs_exp(b)++")"
mapping_set_cs_exp (ChanSetInter a b)
  = "inter("++mapping_set_cs_exp(a)++","++mapping_set_cs_exp(b)++")"
mapping_set_cs_exp (ChanSetDiff a b)
  = "diff("++mapping_set_cs_exp(a)++","++mapping_set_cs_exp(b)++")"
mapping_set_cs_exp x
  = fail ("not implemented by mapping_set_cs_exp: " ++ show x)

\end{code}

\subsection{Mapping Function for Sequence Expressions}

The mapping function for sequence expressions is defined as follows:

\begin{code}
mapping_seq :: ZExpr -> [Char]
mapping_seq (ZCall (ZVar ("\\dcat",[])) s)
  = "concat("++mapping_seq(s)++")"
mapping_seq (ZCall (ZVar ("tail",[])) s)
  = "tail("++mapping_seq(s)++")"
mapping_seq (ZCall (ZVar ("head",[])) s)
  = "head("++mapping_seq(s)++")"
mapping_seq (ZCall (ZVar ("\\035",[])) a)
  = "\035(" ++ mapping_seq(a)++")"
mapping_seq (ZCall (ZVar ("\\cat",[])) (ZTuple [a,b]))
  = mapping_seq(a)++"^"++mapping_seq(b)
mapping_seq (ZCall (ZSeqDisplay x) _)
  = "<"++(mapping_seq_def showexpr x)++">"
mapping_seq (ZSeqDisplay [])
  = "<>"
mapping_seq x
  = fail ("not implemented by mapping_seq: " ++ show x)
\end{code}
\begin{code}
-- aux functions
mapping_seq_def :: (t -> [Char]) -> [t] -> [Char]
mapping_seq_def f [x]
  = (f x)
mapping_seq_def f (x:xs)
  = (f x)++","++(mapping_seq_def f xs)
\end{code}
\begin{code}
get_channel_name :: Comm -> ZName
get_channel_name (ChanComm x [])
  = x
get_channel_name (ChanComm c [ChanOutExp v])
  = c++"!"++(showexpr v)
get_channel_name (ChanComm c [ChanDotExp v])
  = c++"."++(showexpr v)
get_channel_name (ChanComm c [ChanInp v])
  = c++"?"++v
-- get_channel_name (ChanComm c [ChanInpPred v x]) = c++"?"++v++":"++x
\end{code}
