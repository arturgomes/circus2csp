module MappingFunCircusCSP
where
import AST
import CRL
import FormatterToCSP


showexpr = zexpr_string (pinfo_extz 80)

mapping_CAction (CActionCommand cc) = undefined
mapping_CAction (CActionName zn) = undefined
mapping_CAction (CActionSchemaExpr zse) = undefined
mapping_CAction (CSPChaos) = "CHAOS"
mapping_CAction (CSPCommAction co CSPSkip) = (get_channel_name co) ++ " -> " ++ mapping_CAction(CSPSkip)
mapping_CAction (CSPCommAction c a) = (get_channel_name c) ++ " -> " ++ mapping_CAction(a)
mapping_CAction (CSPExtChoice a b) = mapping_CAction(a) ++ " [] "  ++ mapping_CAction(b)
mapping_CAction (CSPGuard g ac) = mapping_predicate(g) ++ " & " ++ mapping_CAction(ac)
mapping_CAction (CSPHide a cs) = mapping_CAction(a) ++  "\\" ++ mapping_predicate_cs (cs)
mapping_CAction (CSPIntChoice a b) = mapping_CAction(a) ++ " |~| "  ++ mapping_CAction(b)
mapping_CAction (CSPInterleave ca cb) = undefined
mapping_CAction (CSPNSInter ns1 ns2 a b) = mapping_CAction(a) ++ "|||" ++ mapping_CAction(b)
mapping_CAction (CSPNSParal ns1 cs ns2 a b) = mapping_CAction(a) ++ " [| " ++ mapping_predicate_cs(cs) ++ " |] "++ mapping_CAction(b)
mapping_CAction (CSPParAction zn (x:xs)) = undefined
mapping_CAction (CSPParal cs a b) = mapping_CAction(a) ++ " [| " ++ mapping_predicate_cs(cs) ++ " |] "++ mapping_CAction(b)
mapping_CAction (CSPRecursion x a) = "let Mu" ++ show x ++ " = " ++ mapping_CAction(a) ++ ";  Mu" ++ show x ++ "within Mu" ++ show x
mapping_CAction (CSPRepExtChoice [(Choose x s)] a) = "[] " ++  show x  ++ " : "++ mapping_set_exp(s) ++ " @ " ++ mapping_CAction(a)
mapping_CAction (CSPRepIntChoice [(Choose x s)] a) = "|~| " ++  show x  ++ " : "++ mapping_set_exp(s) ++ " @ " ++ mapping_CAction(a)
mapping_CAction (CSPRepInterl (x:xs) ca) = undefined
mapping_CAction (CSPRepInterlNS [(Choose x s)] NSExpEmpty a) = "||| " ++  show x  ++ " : " ++ mapping_set_exp(s) ++ " @ " ++ mapping_CAction(a)
mapping_CAction (CSPRepParalNS cs [(Choose x s)] NSExpEmpty a) = "[| " ++ mapping_predicate_cs (cs) ++ " |] "++  show x ++ " : "++ mapping_set_exp(s) ++ " @ " ++ mapping_CAction(a)
mapping_CAction (CSPRepSeq [(Choose x s)] a) = "; " ++  show x  ++ " : "++ mapping_seq(s) ++ " @ " ++ mapping_CAction(a)
mapping_CAction (CSPSeq a b) = mapping_CAction(a) ++ " ; " ++ mapping_CAction(b)
mapping_CAction (CSPSkip) = "SKIP"
mapping_CAction (CSPStop) = "STOP"


mapping_CProc (CExtChoice a b) = mapping_CProc(a) ++ " [] "  ++ mapping_CProc(b)
mapping_CProc (CGenProc zn (x:xs)) = undefined
mapping_CProc (CHide a cs) = mapping_CProc(a) ++  "\\" ++ mapping_predicate_cs (cs)
mapping_CProc (CIntChoice a b) = mapping_CProc(a) ++ " |~| "  ++ mapping_CProc(b)
mapping_CProc (CInterleave a b) = mapping_CProc(a) ++ "|||" ++ mapping_CProc(b)
mapping_CProc (CircusProc zn) = undefined
mapping_CProc (CParamProc zn (x:xs)) = undefined
mapping_CProc (CParParal cs a b) = mapping_CProc(a) ++ " [| " ++ mapping_predicate_cs(cs) ++ " |] "++ mapping_CProc(b)
mapping_CProc (CRepExtChProc [(Choose x s)] a) = "[] " ++  show x  ++ " : "++ mapping_set_exp(s) ++ " @ " ++ mapping_CProc(a)
mapping_CProc (CRepIntChProc [(Choose x s)] a) = "|~| " ++  show x  ++ " : "++ mapping_set_exp(s) ++ " @ " ++ mapping_CProc(a)
mapping_CProc (CRepInterlProc (x:xs) cp) = undefined
mapping_CProc (CRepParalProc cse (x:xs) cp) = undefined
mapping_CProc (CRepSeqProc [(Choose x s)] a) = "; " ++  show x  ++ " : "++ mapping_seq(s) ++ " @ " ++ mapping_CProc(a)
mapping_CProc (CSeq a b) = mapping_CProc(a) ++ " ; " ++ mapping_CProc(b)
mapping_CProc (CSimpIndexProc zn (x:xs)) = undefined
mapping_CProc (ProcMain zp (x:xs) ca) = undefined
mapping_CProc (ProcStalessMain (x:xs) ca) = undefined

mapping_CCommand (CAssign (x:xs) (y:ys)) = undefined
mapping_CCommand (CAssumpt (x:xs) zpa zpb) = undefined
mapping_CCommand (CIf cga) = undefined
mapping_CCommand (CommandBrace zp) = undefined
mapping_CCommand (CommandBracket zp) = undefined
mapping_CCommand (CResDecl (x:xs) ca) = undefined
mapping_CCommand (CVarDecl (x:xs) ca) = undefined
mapping_CCommand (CVResDecl (x:xs) ca) = undefined


mapping_CDecl (CChan zn1) = undefined
mapping_CDecl (CChanDecl zn2 ze) = undefined
mapping_CDecl (CGenChanDecl zn3 zn4 ze) = undefined

mapping_CGActions (CircGAction zp ca) = undefined
mapping_CGActions (CircThenElse cga1 cga2) = undefined

mapping_Comm (ChanComm zn (x:xs)) = undefined
mapping_Comm (ChanGenComm zn (x:xs) (y:ys)) = undefined

mapping_CParameter (ChanDotExp ze) = undefined
mapping_CParameter (ChanInp zn) = undefined
mapping_CParameter (ChanInpPred zn zp) = undefined
mapping_CParameter (ChanOutExp ze) = undefined

mapping_CSExp (CChanSet xs) = "{| " ++ (mapping_CSExp_get_cs xs) ++ " |}"
mapping_CSExp (ChanSetDiff a b) = "diff("++mapping_CSExp(a)++","++mapping_CSExp(b)++")"
mapping_CSExp (ChanSetInter a b) = "inter("++mapping_CSExp(a)++","++mapping_CSExp(b)++")"
mapping_CSExp (ChanSetUnion a b) = "union("++mapping_CSExp(a)++","++mapping_CSExp(b)++")"
mapping_CSExp (CSEmpty) = "{| |}"
mapping_CSExp (CSExpr zn) = show zn

-- aux fun for mapping_CSExp
mapping_CSExp_get_cs [] = ""
mapping_CSExp_get_cs [x] = show x
mapping_CSExp_get_cs (c:cs) = show c ++ "," ++ (mapping_CSExp_get_cs cs)

mapping_NSExp (NSExpEmpty) = undefined
mapping_NSExp (NSExprMult (x:xs)) = undefined
mapping_NSExp (NSExprSngl zn) = undefined
mapping_NSExp (NSHide nse1 nse2) = undefined
mapping_NSExp (NSIntersect nse1 nse2) = undefined
mapping_NSExp (NSUnion nse1 nse2) = undefined

mapping_ParAction (CircusAction ca) = undefined
mapping_ParAction (ParamActionDecl (x:xs) pa) = undefined

mapping_PPar (CNameSet zn nse) = undefined
mapping_PPar (CParAction zn pa) = undefined
mapping_PPar (ProcZPara zp) = undefined

mapping_ProcDecl (CGenProcess zn (x:xs) pd) = undefined
mapping_ProcDecl (CProcess zn pd) = undefined

mapping_ProcessDef (ProcDef cp) = undefined
mapping_ProcessDef (ProcDefIndex (x:xs) pd) = undefined
mapping_ProcessDef (ProcDefSpot (x:xs) pd) = undefined

-- Mapping Function for Actions



-- Mapping Functions for Numbers
-- The mapping function for set expressions is defined as follows:


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
mapping_numbers (ZInt n) = show n
mapping_numbers _ = "Not implemented by mapping_numbers"

-- Mapping Functions for Predicates
-- NOt sure what "if then else" is about
-- mapping_expression (ZIf_Then_Else b x1 x2)
-- 	= "if " ++ (mapping_predicate b) ++
-- 		" then " ++ (mapping_CAction x1) ++
-- 		" else " ++ (mapping_CAction x2)

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
mapping_predicate ( (ZOr a b))
	= (mapping_predicate a) ++ " or " ++ (mapping_predicate b)
mapping_predicate ( (ZAnd a b))
	= (mapping_predicate a) ++ " and " ++ (mapping_predicate b)
mapping_predicate ( ZTrue{reason=[]}) = "true"
mapping_predicate ( ZFalse{reason=[]}) = "false"
mapping_predicate _
	= "not implemented by mapping_predicate"

-- Mapping Function for Set Expressions
mapping_set_exp (ZSetDisplay x)
	= "{"++(mapping_seq_def show x)++"}"
mapping_set_exp (ZSetDisplay [ZCall (ZVar ("\\upto",[])) (ZTuple [a,b])])
	= "{"++show (a)++".."+show (b)++"}"
mapping_set_exp ((ZCall (ZVar ("\\cup",[])) (ZTuple [a,b])))
	= "union("++mapping_set_exp(a)++","++mapping_set_exp(b)++")"
mapping_set_exp ((ZCall (ZVar ("\\cap",[])) (ZTuple [a,b])))
	= "inter("++mapping_set_exp(a)++","++mapping_set_exp(b)++")"
mapping_set_exp ((ZCall (ZVar ("\\setminus",[])) (ZTuple [a,b])))
	= "diff("++mapping_set_exp(a)++","++mapping_set_exp(b)++")"
-- mapping_set_exp (S A) = Union(mapping_set_exp(A))
-- mapping_set_exp (T A) = Inter(mapping_set_exp(A))
mapping_set_exp (Choose x a)
	= "member("++(show x)++","++mapping_set_exp(a)++")"
mapping_set_exp (ZCall (ZVar ("\\#",[])) a)
	= "card("++mapping_set_exp(a)++")"
mapping_set_exp (ZCall (ZVar ("\\ran",[])) a)
	= "set("++mapping_set_exp(a)++")"
mapping_set_exp (ZCall (ZVar ("\\power",[])) a)
	="Set("++mapping_set_exp(a)++")"
mapping_set_exp (ZCall (ZVar ("\\seq",[])) a)
	= "Seq("++mapping_set_exp(a)++")"
mapping_set_exp _
	= "not implemented by mapping_set_exp"
-- mapping_set_exp ({}) = {}
-- mapping_set_exp ({x1 : a1; . . . ; xn : an | b • E(x1, ..., xn)}) = b
-- {mapping_CAction(E(x1, ..., xn))|mapping_CAction(xi) mapping_CAction(ai),mapping_CAction(b)}

-- Mapping Function for Channel Set Expressions
mapping_predicate_cs (cs) = "Union({{| c |} | c <- "++mapping_set_exp(cs)++"})"

-- Mapping Function for Sequence Expressions
-- The mapping function for sequence expressions is defined as follows:
-- mapping_seq (ZCall (ZVar ("dcat",[])) s)
-- 	= "concat("++mapping_seq(s)++")"
-- mapping_seq (ZCall (ZVar ("tail",[])) s)
-- 	= "tail("mapping_seq(s)++")"
-- mapping_seq (ZCall (ZVar ("head",[])) s)
-- 	= "head("mapping_seq(s)++")"
mapping_seq (ZCall (ZVar ("\\#",[])) a)
	= "#(" ++ mapping_seq(a)++")"
mapping_seq (ZCall (ZVar ("\\cat",[])) (ZTuple [a,b]))
	= mapping_seq(a)++"^"++mapping_seq(b)
mapping_seq (ZCall (ZSeqDisplay x) _)
	= "<"++(mapping_seq_def showexpr x)++">"
mapping_seq (ZSeqDisplay [])
	= "<>"
mapping_seq _
	= "not implemented by mapping_seq"
-- aux functions
mapping_seq_def f [x] = (f x)
mapping_seq_def f (x:xs) = (f x)++","++(mapping_seq_def f xs)

get_channel_name (ChanComm x []) = x
get_channel_name (ChanComm c [ChanOutExp v]) = c++"!"++(showexpr v)
get_channel_name (ChanComm c [ChanDotExp v]) = c++"."++(showexpr v)
get_channel_name (ChanComm c [ChanInp v]) = c++"?"++v
-- get_channel_name (ChanComm c [ChanInpPred v x]) = c++"?"++v++":"++x
