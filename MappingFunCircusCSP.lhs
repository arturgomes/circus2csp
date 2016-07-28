\section{MappingFunCircusCSP}

MappingFunCircusCSP MappingFunCircusCSP MappingFunCircusCSP MappingFunCircusCSP
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

mapping_CircParagraphs (ZGivenSetDecl gs)
  = (fst gs) ++ " = {}"
mapping_CircParagraphs (ZSchemaDef zsn zse)
  = undefined
mapping_CircParagraphs (ZAbbreviation zv ze)
  = undefined
mapping_CircParagraphs (ZFreeTypeDef zv zbs)
  = "datatype " ++ zv ++ " = " ++ (mapping_ZBranch zbs)
mapping_CircParagraphs (ZPredicate zp)
  = undefined
mapping_CircParagraphs (ZAxDef zgfs)
  = undefined
mapping_CircParagraphs (ZGenDef zgfs)
  = undefined
mapping_CircParagraphs (Process cp)
  = mapping_ProcDecl cp
mapping_CircParagraphs (CircChanSet cn c2)
  = cn ++ " = " ++ (mapping_CSExp c2) ++ "\n"
mapping_CircParagraphs (CircChannel cc2)
  = mapping_CDecl cc2
\end{code}
\begin{code}
mapping_ZBranch = get_channel_type_list
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
mapping_CProc (CGenProc zn (x:xs))
  = undefined
mapping_CProc (CParamProc zn (x:xs))
  = undefined
mapping_CProc (CSimpIndexProc zn (x:xs))
  = undefined
mapping_CProc (ProcMain zp (x:xs) ca)
  = undefined
mapping_CProc (ProcStalessMain pps ca)
  = "\n\tlet \n\t\t" ++ (mapping_PPar_list pps)
    ++ "within " ++ (mapping_CAction ca) ++ "\n"

\end{code}

\subsection{Mapping Circus Processes Paragraphs}
NOTE: $CNameSet$ and $ProcZPara$ is not yet implmented
\begin{code}
mapping_PPar :: PPar -> [Char]
--mapping_PPar (CNameSet zn nse)
--  = undefined
mapping_PPar (CParAction zn pa)
  = zn ++ (mapping_ParAction pa)
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
mapping_CAction (CSPCommAction co CSPSkip)
  = (get_channel_name co)
    ++ " -> "
    ++ mapping_CAction(CSPSkip)
mapping_CAction (CSPCommAction c a)
  = (get_channel_name c)
    ++ " -> "
    ++ mapping_CAction(a)
mapping_CAction (CSPExtChoice a b)
  = mapping_CAction(a)
    ++ " [] "
    ++ mapping_CAction(b)
mapping_CAction (CSPGuard g ac)
  = mapping_predicate(g)
    ++ " & "
    ++ mapping_CAction(ac)
mapping_CAction (CSPHide a cs)
  = mapping_CAction(a)
    ++  "\\"
    ++ mapping_predicate_cs (cs)
mapping_CAction (CSPIntChoice a b)
  = mapping_CAction(a)
    ++ " |~| "
    ++ mapping_CAction(b)
mapping_CAction (CSPInterleave ca cb)
  = mapping_CAction(ca)
    ++ " ||| "
    ++ mapping_CAction(cb)
--mapping_CAction (CSPNSInter ns1 ns2 a b)
--  = mapping_CAction(a)
--    ++ "|||"
--    ++ mapping_CAction(b)
mapping_CAction (CSPNSParal ns1 cs ns2 a b)
  = mapping_CAction(a)
    ++ " [| "
    ++ mapping_predicate_cs(cs)
    ++ " |] "
    ++ mapping_CAction(b)
--mapping_CAction (CSPParAction zn xl)
--  = (show zn)
--    ++ "(" ++ (mapping_ZGenFilt_list xl) ++ ")"
mapping_CAction (CSPParal cs a b)
  = mapping_CAction(a)
    ++ " [| "
    ++ mapping_predicate_cs(cs)
    ++ " |] "
    ++ mapping_CAction(b)
mapping_CAction (CSPRecursion x a)
  = "let "
    ++ x
    ++ " = "
    ++ mapping_CAction(a)
    ++ " within "
    ++ x
mapping_CAction (CSPRepExtChoice [(Choose x s)] a)
  = "[] "
    ++  show x
    ++ " : "
    ++ mapping_set_exp(s)
    ++ " @ "
    ++ mapping_CAction(a)
mapping_CAction (CSPRepIntChoice [(Choose x s)] a)
  = "|~| "
    ++  show x
    ++ " : "
    ++ mapping_set_exp(s)
    ++ " @ "
    ++ mapping_CAction(a)
mapping_CAction (CSPRepInterl [(Choose x s)] a)
  = "||| "
    ++  show x
    ++ " : "
    ++ mapping_set_exp(s)
    ++ " @ "
    ++ mapping_CAction(a)
mapping_CAction (CSPRepInterlNS [(Choose x s)] NSExpEmpty a)
  = "||| "
    ++  show x
    ++ " : "
    ++ mapping_set_exp(s)
    ++ " @ "
    ++ mapping_CAction(a)
mapping_CAction (CSPRepParalNS cs [(Choose x s)] NSExpEmpty a)
  = "[| "
    ++ mapping_predicate_cs (cs)
    ++ " |] "
    ++  show x
    ++ " : "
    ++ mapping_set_exp(s)
    ++ " @ "
    ++ mapping_CAction(a)
mapping_CAction (CSPRepSeq [(Choose x s)] a)
  = "; "
    ++  show x
    ++ " : "
    ++ mapping_seq(s)
    ++ " @ "
    ++ mapping_CAction(a)
mapping_CAction (CSPSeq a b)
  = mapping_CAction(a)
    ++ " ; "
    ++ mapping_CAction(b)
mapping_CAction (CSPSkip)
  = "SKIP"
mapping_CAction (CSPStop)
  = "STOP"
mapping_CAction (CSPChaos)
  = "CHAOS"
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
mapping_CCommand (CommandBrace zp)
  = undefined
mapping_CCommand (CommandBracket zp)
  = undefined
mapping_CCommand (CResDecl (x:xs) ca)
  = undefined
mapping_CCommand (CVarDecl (x:xs) ca)
  = undefined
mapping_CCommand (CVResDecl (x:xs) ca)
  = undefined
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
mapping_CParameter (ChanDotExp ze)
  = undefined
mapping_CParameter (ChanInp zn)
  = zn
mapping_CParameter (ChanInpPred zn zp)
  = zn ++ (mapping_predicate zp)
mapping_CParameter (ChanOutExp ze)
  = undefined
\end{code}

\subsection{Mapping Circus Namesets}
\begin{code}
mapping_NSExp :: NSExp -> [Char]
mapping_NSExp (NSExpEmpty)
  = undefined
mapping_NSExp (NSExprMult (x:xs))
  = undefined
mapping_NSExp (NSExprSngl zn)
  = undefined
mapping_NSExp (NSHide nse1 nse2)
  = undefined
mapping_NSExp (NSIntersect nse1 nse2)
  = undefined
mapping_NSExp (NSUnion nse1 nse2)
  = undefined
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
-- NOt sure what "if then else" is about
-- mapping_predicate (ZIf_Then_Else b x1 x2)
--   = "if " ++ (mapping_predicate b) ++
--     " then " ++ (mapping_predicate x1) ++
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
mapping_set_exp (ZCall (ZVar ("\\#",[])) a)
  = "card("++mapping_set_exp(a)++")"
mapping_set_exp (ZCall (ZVar ("\\ran",[])) a)
  = "set("++mapping_set_exp(a)++")"
mapping_set_exp (ZCall (ZVar ("\\power",[])) a)
  ="Set("++mapping_set_exp(a)++")"
mapping_set_exp (ZCall (ZVar ("\\seq",[])) a)
  = "Seq("++mapping_set_exp(a)++")"
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
mapping_seq (ZCall (ZVar ("\\#",[])) a)
  = "#(" ++ mapping_seq(a)++")"
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
