module Parse
  (-- For convenience, we export some error handling functions
   -- (from module Errors) that are needed to interpret parser results.
   ErrorOr(..),
   isOk,  notOk, fromOk, error_message,
   -- These are the top-level parsers, of type String -> ErrorOr ast
   parseZspec,   -- a whole spec
   parseZpara,   -- one paragraph only
   parseZsexpr,  -- a single schema expression (no \begin..\end needed)
   parseZexpr,   -- a single expression (no \begin..\end needed)
   parseZpred,   -- a single predicate (no \begin..\end needed)
   parseZident,  -- a single identifier (perhaps decorated)
   -- This lower-level paragraph-parsing function is for testing only
   pzp
  )
-- This Z parser is based closely upon the LL(infinity) Z grammar
-- in the paper: "A Concrete Z Grammar", PRG-TR-22-95,
-- by Peter T. Breuer and Jonathan P. Bowen, and the (more informal)
-- grammar in the appendix of "The Z Reference Manual" (Edition 2),
-- by J. M. Spivey, 1992 Prentice Hall.
--
-- It is reasonably complete, except that generics are not handled
-- and global definitions and let definitions cannot (yet) define
-- operators.
--
-- Note: paragraphs are flattened as much as possible.
--       In other words, a given set declaration, [A,B,C] is expanded
--       out into three separate given set declarations.  Similarly,
--       abbreviations (a==...), free type definitions etc. are all
--       expanded out into separate paragraphs.  This makes the
--       abstract syntax trees simpler (each paragraph generally
--       defines just one name).
--       However, axdef and gendef paragraphs are not expanded,
--       even when they define multiple names, because we assume that
--       the names and associated predicates are grouped together for
--       some semantic reason.  E.g. It is good style for all the
--       constraints on a declared constant to be given in the axdef
--       paragraph where the constant is declared.
where

import EParseLib
import Lexer
import AST
import Control.Monad
import Errors


-- This shows you the whole result (all parses and all errors)
-- It is for debugging and testing only.
pzp :: String -> ParseResult ZToken ZSpec
pzp = epapply zparagraph . zlex lexstate0


check_parse :: ParseResult ZToken ast -> ErrorOr ast
check_parse ParseResult{parses=[], besterror=err}
  = SyntaxErrors [mkParseError err]
check_parse ParseResult{parses=[(t,[],[])]}
  = Ok t
check_parse ParseResult{parses=[(t,errs,[])]}
  = SyntaxErrors errs
check_parse ParseResult{parses=[(t,[],toks)], besterror=err}
  = SyntaxErrors [mkParseError (toks,"valid syntax upto here"),
		  mkParseError err]
check_parse ParseResult{}
  = SyntaxErrors [(0,0,"ambiguous parse!")]


parseZspec :: String -> ErrorOr ZSpec
parseZspec = check_parse . epapply zspec . zlex lexstate0

parseZpara :: String -> ErrorOr ZSpec
parseZpara = check_parse . epapply zparagraph . zlex lexstate0

parseZsexpr :: String -> ErrorOr ZSExpr
parseZsexpr = check_parse . epapply zschema_exp . zlexz 0 lexstate0

parseZexpr :: String -> ErrorOr ZExpr
parseZexpr = check_parse . epapply zexpression . zlexz 0 lexstate0

parseZpred :: String -> ErrorOr ZPred
parseZpred = check_parse . epapply zpredicate . zlexz 0 lexstate0

parseZident :: String -> ErrorOr ZVar
parseZident = check_parse . epapply zident . zlexz 0 lexstate0


--------------------------------------
------------- Z - Spivey -------------
--------------------------------------

-- Specification ::= Paragraph NL ... NL Paragraph

zspec :: EParser ZToken ZSpec
zspec
  = do {ps <- many zparagraph; return (concat ps)}

-- Paragraph ::= [Ident,...,Ident]
--		|Axiomatic-Box
--		|Schema-Box
--		|Generic-Box
--		|Schema-Name[Gen-Formals]* \defs Schema-Exp
--		|Def-Lhs	== Expression
--		|Ident ::= Branch | ... | Branch
--		|Predicate
zparagraph :: EParser ZToken [ZPara]
zparagraph
  = zunboxed_para +++
    zaxiomatic_box +++ -- \begin{axdef}...\end{axdef}
    zschema_box +++
    circus_paragraphs +++
    zmachine_box   -- an extension for defining state machines.

-- Axiomatic-Box ::= [
--		| Decl-Part
--		|-------------
--		| Axiom-Part
--	  	]*

zaxiomatic_box :: EParser ZToken [ZPara]
zaxiomatic_box
  = do  tok L_BEGIN_AXDEF
	cut
	decls <- zdecl_part
	ax <- opt [] (do {optnls; tok L_WHERE; cut; optnls; zaxiom_part })
	optnls
	tok L_END_AXDEF
	return [ZAxDef (concat decls ++ ax)]

-- Schema-Box ::= [
--		|--Schema-Name[Gen-Formals]*---
--		| Decl-Part
--		|-------
--		| Axiom-Part
--		|------------------
--		]*
zschema_box :: EParser ZToken [ZPara]
zschema_box
  = do  tok L_BEGIN_SCHEMA
	cut
	tok L_OPENBRACE
	name <- zschema_name
	tok L_CLOSEBRACE
	-- TODO: add generic formals
	decls <- zdecl_part
	ax <- opt [] (do {optnls; tok L_WHERE; cut; optnls; zaxiom_part })
	optnls
	tok L_END_SCHEMA
	return [ZSchemaDef name (ZSchema (concat decls ++ ax))]

-- Artur Gomes
zschema_box_single :: EParser ZToken ZPara
zschema_box_single
  = do  tok L_BEGIN_SCHEMA
	cut
	tok L_OPENBRACE
	name <- zschema_name
	tok L_CLOSEBRACE
	-- TODO: add generic formals
	decls <- zdecl_part
	ax <- opt [] (do {optnls; tok L_WHERE; cut; optnls; zaxiom_part })
	optnls
	tok L_END_SCHEMA
	return (ZSchemaDef name (ZSchema (concat decls ++ ax)))

--Generic-Box ::= [
--		==[Gen-Formals]*========
--		| Decl-Part
--		-----------
--		| Axiom-Part
--		------------------------
--		]*
zgeneric_box :: EParser ZToken [ZPara]
zgeneric_box
  = do  tok L_BEGIN_GENDEF
	cut
	decls <- zdecl_part
	ax <- opt [] (do {optnls; tok L_WHERE; cut; optnls; zaxiom_part })
	optnls
	tok L_END_GENDEF
	return [ZGenDef (concat decls ++ ax)]
-- TODO Gen_Actuals

--Decl-Par ::= Basic-Decl Sep ... Sep Basic-Decl
zdecl_part :: EParser ZToken [[ZGenFilt]]
zdecl_part = zbasic_decl `sepby1` many1 zsep

--Axiom-Part ::= Predicate Sep ... Sep Predicate
zaxiom_part :: EParser ZToken [ZGenFilt]
zaxiom_part
  = do  ps <- zpredicate `sepby1` many1 zsep
	return (map Check ps)

--Sep ::= ; | NL
zsep :: EParser ZToken ZToken
zsep
  = tok L_BACKSLASH_BACKSLASH +++
    tok L_SEMICOLON +++
    tok L_ALSO

--Def-Lhs ::= Var-Name [Gen-Formals]*
--		|Pre-Gen Decoration Indent
--		|Ident In-Gen Decoration Indent
zdef_lhs :: EParser ZToken ZVar
zdef_lhs
  = do  var_name <- zword
	dec <- zdecoration
	return (make_zvar var_name dec)
-- TODO Pre_Gen_Decor Ident, Ident In_Gen_decor Ident and generic formals

--Branch ::= Ident
-- |	Var-Name << Expression >>
zbranch :: EParser ZToken ZBranch
zbranch
  = do  {vn <- zvar_name;
	 tok L_LDATA;
	 e <- zexpression;
	 tok L_RDATA;
	 return (ZBranch1 vn e)} +++
    do  {i <- zident;
	 return (ZBranch0 i)}

--Schema-Exp ::= \forall Schema-Text @ Schema-Exp
--	| \exists Schema-Text @ Schema-Exp
--	| \exists_1 Schema-Text @ Schema-Exp
--	| Schema-Exp-1
zschema_exp :: EParser ZToken ZSExpr
zschema_exp
  = do  {tok L_FORALL;
	 st <- zschema_text;
	 optnls;
	 tok L_AT;
	 optnls;
	 se <- zschema_exp;
	 return (ZSForall st se)} +++
    do  {tok L_EXISTS;
	 st <- zschema_text;
	 optnls;
	 tok L_AT;
	 optnls;
	 se <- zschema_exp;
	 return (ZSExists st se)} +++
    do  {tok L_EXISTS_1;
	 st <- zschema_text;
	 optnls;
	 tok L_AT;
	 optnls;
	 se <- zschema_exp;
	 return (ZSExists_1 st se)} +++
     zschema_exp_1

--Schema-Exp-1	::= [Schema-Text]
--		|Schema-Ref
--		|\lnot Schema-Exp-1
--		|\pre Schema-Exp-1
--		|Schema-Exp-1 \land Schema-Exp-1
--		|Schema-Exp-1 \lor Schema-Exp-1
--		|Schema-Exp-1 \implies Schema-Exp-1
--		|Schema-Exp-1 \iff Schema-Exp-1
--		|Schema-Exp-1 \project Schema-Exp-1
--		|Schema-Exp-1 \hide (Decl-Name,...,Decl-Name)
--		|Schema-Exp-1 \semi Schema-Exp-1
--		|Schema-Exp-1 \pipe Schema-Exp-1
--	|   (Schema-Exp)
-- Note this differs from the Breuer/Bowen grammar because
--  \implies binds tighter than \iff and the precedence of
--  schema operators is respected as in zrm.
zschema_exp_1f :: EParser ZToken ZSExpr
zschema_exp_1f
  = chainl1 zschema_exp_3 (do {optnls; tok L_LAND; optnls; return (ZS2 ZSAnd)})

zschema_exp_1e :: EParser ZToken ZSExpr
zschema_exp_1e
  = chainl1 zschema_exp_1f (do {optnls; tok L_LOR; optnls; return (ZS2 ZSOr)})

zschema_exp_1d :: EParser ZToken ZSExpr
zschema_exp_1d
  = chainr1 zschema_exp_1e (do {optnls; tok L_IMPLIES; optnls; return (ZS2 ZSImplies)})

zschema_exp_1c :: EParser ZToken ZSExpr
zschema_exp_1c
  = chainl1 zschema_exp_1d (do {optnls; tok L_IFF; optnls; return (ZS2 ZSIff)})

zschema_exp_1b :: EParser ZToken ZSExpr
zschema_exp_1b
  = chainl1 zschema_exp_1c (do {optnls; tok L_PROJECT; optnls; return (ZS2 ZSProject)})

zschema_exp_3 :: EParser ZToken ZSExpr
zschema_exp_3
  = do { se <- zschema_exp_u;
	 se2 <- opt se (do {hidel <- zit_hiding;
   return (ZSHide se hidel)});
	 return se2 }

zschema_exp_1a :: EParser ZToken ZSExpr
zschema_exp_1a
  = chainl1 zschema_exp_1b (do {optnls; tok L_SEMI; optnls; return (ZS2 ZSSemi)})

zschema_exp_1 :: EParser ZToken ZSExpr
zschema_exp_1
  = chainl1 zschema_exp_1a (do {optnls; tok L_PIPE; optnls; return (ZS2 ZSPipe)})

zschema_exp_u :: EParser ZToken ZSExpr
zschema_exp_u
  = do  {tok L_OPENBRACKET;
	 st <- zschema_text;
	 tok L_CLOSEBRACKET;
	 return (ZSchema st)} +++
    do  {tok L_LNOT;
	 se <- zschema_exp_u;
	 return (ZS1 ZSNot se)} +++
    do  {tok L_PRE;
	 se <- zschema_exp_u;
	 return (ZS1 ZSPre se)} +++
    do  {tok L_OPENPAREN;
	 se <- zschema_exp;
	 tok L_CLOSEPAREN;
	 return se} +++
    zschema_ref

--Schema-Text ::= Declaration [|Predicate]*
zschema_text :: EParser ZToken [ZGenFilt]
zschema_text
  = do  d <- zdeclaration
	p <- opt [] (do {optnls;
 tok L_VERT;
 optnls;
 p <- zpredicate;
 return [Check p]})
	return (concat d ++ p)

--Schema-Ref ::= Schema-Name Decoration [Gen-Actuals]* [Renaming]*
zschema_ref :: EParser ZToken ZSExpr
zschema_ref
  = do  {zn <- zschema_name;
	 dec <- zdecoration;
	 reps <- opt [] zreplace;
	 return (ZSRef zn dec reps)}
-- TODO Gen_Actuals
--Renaming	::= [Decl-Name/Decl-Name,...,Decl-Name/Decl-Name]

zreplace :: EParser ZToken [ZReplace]
zreplace
  = do  {tok L_OPENBRACKET;
	 reps <- zrename_or_repl `sepby1` comma;
	 tok L_CLOSEBRACKET;
	 return reps}

zrename_or_repl :: EParser ZToken ZReplace
zrename_or_repl
  = do  {dn1 <- zdecl_name;
	 tok L_SLASH;
	 dn2 <- zdecl_name;
	 return (ZRename dn2 dn1)} +++
    do  {dn1 <- zdecl_name;
	 tok L_ASSIGN;
	 dn2 <- zexpression;
	 return (ZAssign dn1 dn2)}


-- Declaration	::= Basic-Decl; ... ; Basic-Decl
zdeclaration :: EParser ZToken [[ZGenFilt]]
zdeclaration = zbasic_decl `sepby1` do {optnls; tok L_SEMICOLON; optnls}

--Basic-Decl    ::= Decl-Name, ..., Decl-Name : Expression
--	| Schema-Ref
zbasic_decl :: EParser ZToken [ZGenFilt]
zbasic_decl
  = do  {ws <- zdecl_name `sepby1` comma;
	 optnls;
	 tok L_COLON;
	 optnls;
	 e <- zexpression;
	 return [Choose (make_zvar w d) e | (w,d) <- ws]} +++
    do  {sr <- zschema_ref;
	 return [Include sr]}

--Predicate ::= \forall Schema-Text @ Predicate
--	| \exists Schema-Text @ Predicate
--	| \exists_1 Schema-Text @ Predicate
--	| \LET Let-Def ; ... ; Let-Def @ Predicate
--	| Predicate-1

zpredicate :: EParser ZToken ZPred
zpredicate
  = do  {tok L_FORALL;
	 st <- zschema_text;
	 optnls;
	 tok L_AT;
	 optnls;
	 p <- zpredicate;
	 return (ZForall st p)} +++
    do  {tok L_EXISTS;
	 st <- zschema_text;
	 optnls;
	 tok L_AT;
	 optnls;
	 p <- zpredicate;
	 return (ZExists st p)} +++
    do  {tok L_EXISTS_1;
	 st <- zschema_text;
	 optnls;
	 tok L_AT;
	 optnls;
	 p <- zpredicate;
	 return (ZExists_1 st p)} +++
    do  {tok L_LET;
	 ldl <- zlet_def `sepby1` do {optnls; tok L_SEMICOLON; optnls};
	 optnls;
	 tok L_AT;
	 optnls;
	 p <- zpredicate;
	 return (ZPLet ldl p)} +++
    zpredicate_1

--Predicate-1 	::= Expression Rel Expression Rel ... Rel Expression
--	| Pre-Rel Decoration Expression
--	| Schema-Ref
--	| \pre Schema-Ref
--	| \true
--	| \false
--	| \lnot Predicate-1
--	| Predicate-1 \land Predicate-1
--	| Predicate-1 \lor Predicate-1
--	| Predicate-1 \implies Predicate-1
--	| Predicate-1 \iff Predicate-1
--	| (Predicate-1)

zpredicate_1 :: EParser ZToken ZPred
zpredicate_1
  = chainl1 zpredicate_1a (do {optnls; tok L_IFF; optnls; return ZIff})

-- Note this differs from the Breuer/Bowen grammar because
--  \implies binds tighter than \iff and the precedence of
--  predicate operators is respected as in zrm.

zpredicate_1a :: EParser ZToken ZPred
zpredicate_1a
  = chainr1 zpredicate_1b (do {optnls; tok L_IMPLIES; optnls; return ZImplies})

zpredicate_1b :: EParser ZToken ZPred
zpredicate_1b
  = chainl1 zpredicate_1c (do {optnls; tok L_LOR; optnls; return ZOr})

zpredicate_1c :: EParser ZToken ZPred
zpredicate_1c
  = chainl1 zpredicate_u (do {optnls; tok L_LAND; optnls; return ZAnd})

zpredicate_u :: EParser ZToken ZPred
zpredicate_u
    = do  {e1 <- zexpression;
	   es <- many1 (do {optnls;
    r <- zrel;
    optnls;
    e2 <- zexpression;
    return (r,e2)});
	   return (it_pred e1 es)} +++
--  Handles iterations, e.g. a=b=c or a \in b = c, by taking the conjunct
--   of each  iteration e.g. a=b \land b=c or a \in b \land b=c respectively.
--  Note: Single zexpressions are not allowed here by Spivey but are in
--   the Breuer/Bowen grammar (a mistake?).  We follow Spivey.
      do  {op <- zpre_rel_decor;
	   e <- zexpression;
	   return (ZMember e (ZVar op))} +++
      do  {tok L_PRE; sr <- zschema_ref; return (ZPre sr)} +++
      do  {tok L_TRUE; return ztrue} +++
      do  {tok L_FALSE; return zfalse} +++
      do  {tok L_LNOT;
	   p <- zpredicate;
	   return (ZNot p)} +++
      do  {tok L_OPENPAREN;
	   p <- zpredicate;
	   tok L_CLOSEPAREN;
	   return p;} +++
      do  {sr <- zschema_ref;
	   return (ZPSchema sr)}

it_pred :: ZExpr -> [(ZExpr -> ZExpr -> ZPred, ZExpr)] -> ZPred
it_pred e1 [(f,e2)]    = f e1 e2
it_pred e1 ((f,e2):fs) = f e1 e2 `ZAnd` it_pred e2 fs

--Rel ::= = | \in | In-Rel Decoration
zrel :: EParser ZToken (ZExpr -> ZExpr -> ZPred)
zrel
  = do  {tok L_EQUALS; return ZEqual} +++
    do  {tok L_IN; return ZMember} +++
    do  {tok L_NEQ; return (\e1 e2 -> (ZNot (ZEqual e1 e2)))} +++
    do  {tok L_NOTIN; return (\e1 e2 -> (ZNot (ZMember e1 e2)))} +++
    do  {ir <- zin_rel_decor; return (member_of_in_rel (ZVar ir))} +++
    do  {tok L_INREL; tok L_OPENBRACE; i <- zident;
	 tok L_CLOSEBRACE; return (member_of_in_rel (ZVar i))}
  where
  -- Translate (x R y) into (x,y) \in R.
  member_of_in_rel r e1 e2 = ZMember (ZTuple [e1,e2]) r

--Let-Def ::= Var-Name == Expression
zlet_def :: EParser ZToken (ZVar,ZExpr)
zlet_def
  = do  {vn <- zvar_name;
	 optnls;
	 tok L_EQUALS_EQUALS;
	 optnls;
	 e <- zexpression;
	 return (vn,e)}


-- Comments from Artur
-- [Expression, ..., Expression]
zexpressions :: EParser ZToken [ZExpr]
zexpressions
  = do  {e <- zexpression;
	 el <- many (do {comma;
 e1 <- zexpression;
 return e1});
	 return (e : el)}

--Expression-0	::= \lambda Schema-Text @ Expression
--	| \mu Schema-Text [@ Expression]*
--	| \let Let-Def; ... ; Let-Def @ Expression
--	| Expression
-- Comment from Mark Utting
-- This differs slightly from the Breuer/Bowen grammar.
-- To avoid reparsing parenthesized expressions, we define
-- zexpression_0 so it only parses the special weakly binding
-- expressions, and does not call zexpression.
zexpression_0 :: EParser ZToken ZExpr
zexpression_0
  = do  {tok L_LAMBDA;
	 st <- zschema_text;
	 optnls;
	 tok L_AT;
	 optnls;
	 e <- zexpression;
	 return (ZLambda st e)} +++
    do  {tok L_MU;
	 st <- zschema_text;
	 e <- opt Nothing (do {tok L_AT; exp <- zexpression; return (Just exp)});
	 return (ZMu st e)} +++
    do  {tok L_LET;
	 ldl <- zlet_def `sepby1` do {optnls; tok L_SEMICOLON; optnls};
	 optnls;
	 tok L_AT;
	 optnls;
	 e <- zexpression;
	 return (ZELet ldl e)}
--Expression 	::= \IF Predicate \THEN Expression \ELSE Expression
--	| Expression-1
zexpression :: EParser ZToken ZExpr
zexpression
  = do  {tok L_IF;
	 p <- zpredicate;
	 optnls;
	 tok L_THEN;
	 optnls;
	 e1 <- zexpression;
	 optnls;
	 tok L_ELSE;
	 optnls;
	 e2 <- zexpression;
	 return (ZIf_Then_Else p e1 e2)} +++
    zexpression_1

--Expression-1 	::= Expression-1 In-Gen Decoration Expression-1
--	| Expression-2 \cross Expression-2 \cross ... \cross Expression-2
--	| Expression-2
zexpression_1 :: EParser ZToken ZExpr
zexpression_1
  = chainr1 zexpression_1a (do {op <- zin_gen_decor;
	return (infixop((ZVar op)))})

zexpression_1a :: EParser ZToken ZExpr
zexpression_1a
  = do  {e <- (zexpression_2 1);
	 ce <- opt e (do {cel <- many1 (do {optnls;
		    tok L_CROSS;
		    optnls;
		    e2 <- zexpression_2 1;
		    return e2});
  return (ZCross (e:cel))});
	 return (ce)}

--Expression-2	::= Expression-2 In-Fun Decoration Expression-2
--	| \power Expression-4
--	| Pre-Gen Decoration Expression-4
--	| − Decoration Expression-4
--	| Expression-4 \limg Expression-0 \rimg Decoration
--	| Expression-3
zexpression_2 :: Int -> EParser ZToken ZExpr
zexpression_2 7 = zexpression_2a
zexpression_2 p
  = chainl1 (zexpression_2 (p+1)) (do {optnls;
	       op <- (zin_fun_decor p);
	       optnls;
	       return (infixop (ZVar op))})

infixop :: ZExpr -> ZExpr -> ZExpr -> ZExpr
infixop op a b = ZCall op (ZTuple [a,b])

zexpression_2a :: EParser ZToken ZExpr
zexpression_2a
  = do  {tok L_POWER;
	 e <- zexpression_4;
	 return (ZCall (ZVar (make_zvar "\\power" [])) e)} +++
    do  {op <- zpre_gen_decor;
	 e <- zexpression_4;
	 return (ZCall (ZVar op) e)} +++
    do  {tok L_HYPHEN;
	 dec <- zdecoration;
	 e <- zexpression_4;
	 return (ZCall (ZVar (make_zvar "\\negate" dec)) e)} +++
    do  {e4 <- zexpression_4;
	 -- We factor e4 out of the following 2 cases, to avoid reparsing it.
	 -- As Breuer/Bowen note, this is a source of inefficiency
	 -- in their parser.  e4 is often big, so reparsing it is bad.
	 do { tok L_LIMG;
	      e0 <- zexpression_0 +++ zexpression;
	      tok L_RIMG;
	      dec <- zdecoration;
	      let {op = make_zvar "\\relimg" dec};
	      return (ZCall (ZVar op) (ZTuple [e4,e0])) }
	    +++
	 do { -- this is zexpression_3 (function calls), done inline
	      es <- many zexpression_4;
	      return (foldl1 ZCall (e4:es)) }}

--Expression-3	::= Expression-3 Expression-4
--	| Expression-4
-- Defined above in zexpression_2a

--Expression-4	::=Var-Name [ Gen-Actuals] | Number
--	| Schema-Ref
--	| Set-Exp
--	| ⟨ [ Expression, ... , Expression] ⟩
--	| [ Expression, ... , Expression]
--	| (Expression, Expression, ... , Expression)
--	| \theta Schema-Name Decoration [ Renaming]
--	| Expression-4 . Var-Name
--	| Expression-4 Post-Fun Decoration
--	| Expression-4^(Expression)
--	| (Expression-0)
zexpression_4 :: EParser ZToken ZExpr
zexpression_4
 = do  {e <- zexpression_4a;
	e2 <- opt e (do {tok L_POINT;
 v <- zvar_name;
 return (ZSelect e v)} +++
		     do {op <- zpost_fun_decor;
 return (ZCall (ZVar op) e)} +++
		     do {tok L_BSUP;
 e2 <- zexpression;
 tok L_ESUP;
 let {op = make_zvar "iter" []};
 -- iter is curried: 'R\bsup k \esep' means 'iter R k'
 return (ZCall (ZCall (ZVar op) e2) e)});
	return e2 }

zexpression_4a :: EParser ZToken ZExpr
zexpression_4a
  = do  {vn <- zvar_name; return (ZVar vn)} +++
-- TODO Gen_Actuals
    do  {i <- znumber; return (ZInt i)} +++
    do  {s <- zgivenval; return (ZGiven s)} +++
    do  {zset_exp} +++
    do  {tok L_LANGLE;
	 el <- opt [] zexpressions;
	 tok L_RANGLE;
	 return (ZSeqDisplay el)} +++
    zexpression_4b

zexpression_4b :: EParser ZToken ZExpr
zexpression_4b
  = do  {tok L_OPENPAREN;
	 -- Note: this *only* parses \lambda, \let and \mu
	 e <- zexpression_0;
	 tok L_CLOSEPAREN;
	 return e} +++
    do  { -- here we combine parsing of parenthesized expressions
	  -- and parsing of tuples, to avoid reparsing the first
	  -- expression in a tuple.  The Breuer/Bowen grammar does
	  -- does do this, so behaves exponentially on nested expressions
	 tok L_OPENPAREN;
	 es <- zexpressions;
	 tok L_CLOSEPAREN;
	 return (if length es == 1 then head es else ZTuple es)} +++
    do  {tok L_LBLOT;
	 bl <- opt [] (zlet_def `sepby1` do {optnls; tok L_COMMA; optnls});
	 tok L_RBLOT;
	 return (ZBinding bl)} +++
    do  {tok L_THETA;
	 sn <- zschema_name;
	 dec <- zdecoration;
	 reps <- opt [] zreplace;
	 return (ZTheta (ZSRef sn dec reps))} +++
    do  {sr <- zschema_ref;
	 return (ZESchema sr)}

--Set-Exp		::= { [ Expression, ... , Expression]* }
--	| { Schema-Text [ @ Expression]* }
zset_exp ::  EParser ZToken ZExpr
zset_exp
  = do  {tok L_OPENSET;
	 el <- opt [] zexpressions;
	 tok L_CLOSESET;
	 -- Note: Z is ambiguous here.
	 --   {S} can be parsed as a set display or a set comprehension.
	 --   Spivey (Edition 2) p.55 says if S is a schema reference,
	 --   this should be parsed as a set comprehension.
	 --   At this stage in parsing, we do not know which names are
	 --   schemas, so we leave it as a set display.
	 --   The Unfold module translates them to set comprehensions.
	 return (ZSetDisplay el) } +++
    do  {tok L_OPENSET;
	 st <- zschema_text;
	 e <- opt Nothing (do {optnls;
       tok L_AT;
       optnls;
       exp <- zexpression;
       return (Just exp)});
	 tok L_CLOSESET;
	 return (ZSetComp st e)}

--Ident ::= Word Decoration
zident :: EParser ZToken ZVar
zident = do {w <- zword; d <- zdecoration; return (make_zvar w d)}

--Decl-Name 	::= Ident
--	| Op-Name
zdecl_name :: EParser ZToken ZVar
zdecl_name = zop_name +++ zident

--Var-Name		::= Ident
--	| (Op-Name)
zvar_name :: EParser ZToken ZVar
zvar_name
  = do  {tok L_OPENPAREN;
  		 vn <- zop_name;
  		 tok L_CLOSEPAREN;
  		 return vn} +++
    zident

--Op-Name		::= _ In-Sym Decoration _
--	| Pre-Sym Decoration _
--	| _ Post-Sym Decoration
--	| _ \limg _ \rimg Decoration
--	| _ Decoration
zop_name :: EParser ZToken ZVar
zop_name =
  do  {tok L_UNDERSCORE;
       is <- zin_sym_decor;
       tok L_UNDERSCORE;
       return is} +++
  do  {ps <- zpre_sym_decor;
       tok L_UNDERSCORE;
       return ps} +++
  do  {tok L_UNDERSCORE;
       w <- zpost_fun;
       d <- zdecoration;
       return (make_zvar w d)} +++
  do  {tok L_UNDERSCORE;
       tok L_LIMG;
       tok L_UNDERSCORE;
       tok L_RIMG;
       dec <- zdecoration;
       return (make_zvar "\\relimg" dec)} +++
  do  {tok L_HYPHEN;
       dec <- zdecoration;
       return (make_zvar "\\negate" dec)}

--In-Sym 		::= In-Fun | In-Gen | In-Rel
zin_sym_decor :: EParser ZToken ZVar
zin_sym_decor
  = do  iop <- zin_fun_decor 0 +++ zin_gen_decor +++ zin_rel_decor
	return iop

--Pre-Sym 		::= Pre-Gen | Pre-Rel
zpre_sym_decor :: EParser ZToken ZVar
zpre_sym_decor = zpre_gen_decor +++ zpre_rel_decor

--Post-Sym ::= Post-Fun
-- By Artur Gomes -- To see if this is right!
zpost_sym_decor :: EParser ZToken ZVar
zpost_sym_decor = do zpost_fun_decor

--Decoration :: = [Stroke ... Stroke]*
zdecoration :: EParser ZToken [ZDecor]
zdecoration = many zstroke

--Gen-Formals 	::= [Ident, ..., Ident]
--TODO

--Gen-Actuals 	::= [Expression,...,Expression]
--TODO

--Word ::= Undecorated name or special symbol
zword :: EParser ZToken String
zword =
  do L_WORD w <- sat isWord
     return w
  where
  isWord (L_WORD _) = True
  isWord _          = False

--Stroke ::= Single decoration: ′, ?, ! or a subscript digit
zstroke :: EParser ZToken ZDecor
zstroke
  = do  L_STROKE w <- sat isStroke
	return w
    where
    isStroke (L_STROKE _) = True
    isStroke _            = False

--Schema-Name 	::= Same as Word, but used to name a schema
zschema_name :: EParser ZToken ZSName
zschema_name
  = do  {tok L_DELTA; name <- zword; return (ZSDelta name)} +++
    do  {tok L_XI; name <- zword; return (ZSXi name)} +++
    do  {name <- zword; return (ZSPlain name)}

--In-Fun ::= Infix function symbol
zin_fun_decor :: Int -> EParser ZToken ZVar
zin_fun_decor p
  = do  {ifs <- zin_fun p;
	 dec <- zdecoration;
	 return (make_zvar ifs dec)}

zin_fun :: Int -> EParser ZToken String
zin_fun p =
  do {optnls;
      L_IN_FUN _ w <- sat (isIn_Fun p);
      optnls;
      return w} +++
  do {guard (p==3 || p==0);
      -- p==3 is when infix - appears within expressions: x - 2
      -- p==0 is when it appears in declarations:  _ - _ : Type
      optnls;
      tok L_HYPHEN;
      optnls;
      return ("-")}
  where
  isIn_Fun p2 (L_IN_FUN p _) = p == p2 || p2 == 0
  isIn_Fun p2 _              = False
-- calling this function with  an argument of zero will
-- match in_fun's with any precedence value i.e. 1-6

--In-Rel ::= Infix relation symbol (or underlined identifier)
zin_rel_decor :: EParser ZToken ZVar
zin_rel_decor
  = do  {irs <- zin_rel;
	 dec <- zdecoration;
	 return (make_zvar irs dec)}

zin_rel :: EParser ZToken String
zin_rel =
  do  optnls
      L_IN_REL w <- sat isIn_Rel
      optnls
      return w
  where
  isIn_Rel (L_IN_REL _)  = True
  isIn_Rel _             = False

--In-Gen ::= Infix generic symbol
zin_gen_decor :: EParser ZToken ZVar
zin_gen_decor
  = do  {igs <- zin_gen;
	 dec <- zdecoration;
	 return (make_zvar igs dec)}

zin_gen :: EParser ZToken String
zin_gen =
  do  optnls
      L_IN_GEN w <- sat isIn_Gen
      optnls
      return w
  where
  isIn_Gen (L_IN_GEN _)  = True
  isIn_Gen _             = False

--Pre-Rel 		::= Prefix relation symbol
zpre_rel_decor :: EParser ZToken ZVar
zpre_rel_decor
  = do  {prs <- zpre_rel;
	 dec <- zdecoration;
	 return (make_zvar prs dec)}

zpre_rel :: EParser ZToken String
zpre_rel =
  do L_PRE_REL w <- sat isPre_Rel
     return w
  where
  isPre_Rel (L_PRE_REL _)  = True
  isPre_Rel _             = False


--Pre-Gen 		::= Prefix generic symbol
zpre_gen_decor :: EParser ZToken ZVar
zpre_gen_decor
  = do  {pgs <- zpre_gen;
	 dec <- zdecoration;
	 return (make_zvar pgs dec)}

zpre_gen :: EParser ZToken String
zpre_gen =
  do L_PRE_GEN w <- sat isPre_Gen
     return w
  where
  isPre_Gen (L_PRE_GEN _) = True
  isPre_Gen _             = False

--Post-Fun 		::= Postfix function symbol
zpost_fun_decor :: EParser ZToken ZVar
zpost_fun_decor
  = do  {pfs <- zpost_fun;
	 dec <- zdecoration;
	 return (make_zvar pfs dec)}

zpost_fun :: EParser ZToken String
zpost_fun =
  do L_POST_FUN w <- sat isPost_Fun
     return w
  where
  isPost_Fun (L_POST_FUN _)  = True
  isPost_Fun _                = False

--Number ::= Unsigned decimal integer
znumber :: EParser ZToken ZInt
znumber =
  do L_NUMBER i <- sat isNumber
     return i
  where
  isNumber (L_NUMBER _) = True
  isNumber _            = False


--------------------------------------
-------------   Circus   -------------
--------------------------------------

--Program 	:: CircusPar*


--CircusPar 	::= Par
-- 				| \circchannel CDecl
-- 				| \circchanset N == CSExp
-- 				| ProcDecl


circus_paragraphs :: EParser ZToken [ZPara]
circus_paragraphs
  = do {tok L_BEGIN_CIRCUS;
  	cut;
  	s <- circus_par `sepby1` many1 zsep;
  	optnls;
  	tok L_END_CIRCUS;
  	return (concat s)}


circus_par :: EParser ZToken [ZPara]
circus_par
  = circ_chan +++ 
  circ_chanset +++
  circus_proc

circus_proc :: EParser ZToken [ZPara]
circus_proc 
  = do {cdec <- circus_proc_decl;
  	    	return [Process cdec]}

circ_chan :: EParser ZToken [ZPara]
circ_chan
  = do {optnls;
  tok L_CIRCCHANNEL;
  	    	cdec <- circusdecl;
  	    	return [CircChannel cdec]}

--CDecl 		::= SimpleCDecl
-- 			    | SimpleCDecl; CDecl
circusdecl  :: EParser ZToken [CDecl]
circusdecl
  = do { csd <- csimpledecl `sepby1` zsep;
  	return (concat csd)}

--SimpleCDecl	::= N^{+}
-- 				| N^{+} : Exp
--				| [N^{+}]N^{+} : Exp
-- 				| SchemaExp -- left out
csimpledecl :: EParser ZToken [CDecl]
csimpledecl
  = do {tok L_OPENBRACKET;
		tp <- zdecl_name;
		tok L_CLOSEBRACKET;
		optnls;
		ws <- zdecl_name `sepby1` comma;
		optnls;
		tok L_COLON;
		optnls;
		e <- zexpression;
		return [CGenChanDecl tp (make_zvar w d) e | (w,d) <- ws]}
	+++
	do {ws <- zdecl_name `sepby1` comma; 
		optnls; 
		tok L_COLON; 
		optnls; 
		e <- zexpression; 
		return [CChanDecl (make_zvar w d) e | (w,d) <- ws]}
	+++
	do {gs <- zdecl_name `sepby1` comma; 
		return (map CChan gs)}


circ_chanset :: EParser ZToken [ZPara]
circ_chanset
  = do {optnls;
  		tok L_CIRCCHANSET; 
 		optnls;
  		tp <- zdecl_name;
 		optnls;
 		tok L_EQUALS_EQUALS;
 		optnls;
 		cdec <- circuscsexpr; 
 		return [CircChanSet tp cdec]}
--CSExp		::= \lchanset \rchanset
-- | \lchanset N^{+} \rchanset
-- | N
-- | CSExp \union CSExp
-- | CSExp \intersect CSExp
-- | CSExp \circhide CSExp

circuscsexpr ::  EParser ZToken CSExp
circuscsexpr
 = circuscsexpr_union +++
   circuscsexpr_intersect  +++
   circuscsexpr_hide +++
   csexp_ecsn 

circuscsexpr_union ::  EParser ZToken CSExp
circuscsexpr_union
 = do {cs1 <- csexp_ecsn; -- CSExp \union CSExp
 		optnls; tok L_UNION; optnls;
 		cs2 <- circuscsexpr;
 		return (ChanSetUnion cs1 cs2)}
circuscsexpr_intersect ::  EParser ZToken CSExp
circuscsexpr_intersect
 = do {cs1 <- csexp_ecsn; -- CSExp \union CSExp
 		optnls; tok L_INTERSECT; optnls;
 		cs2 <- circuscsexpr;
 		return (ChanSetInter cs1 cs2)}
circuscsexpr_hide ::  EParser ZToken CSExp
circuscsexpr_hide
 = do {cs1 <- csexp_ecsn; -- CSExp \union CSExp
 		optnls; tok L_CIRCHIDE; optnls;
 		cs2 <- circuscsexpr;
 		return (ChanSetHide cs1 cs2)}

csexp_empty ::  EParser ZToken CSExp
csexp_empty
 = do {tok L_LCHANSET; tok L_RCHANSET; -- \lchanset \rchanset
		return CSEmpty}

csexp_chanset ::  EParser ZToken CSExp
csexp_chanset
 = do {tok L_LCHANSET; -- \lchanset N^{+} \rchanset
 		optnls;
  		ws <- zdecl_name `sepby1` comma; 
		optnls;
 		tok L_RCHANSET;
 		return (CChanSet [(make_zvar w d) | (w,d) <- ws])}

csexp_channame ::  EParser ZToken CSExp
csexp_channame
 = do {ws <- zdecl_name; -- N
   		return (CSExpr ws)}		

csexp_ecsn ::  EParser ZToken CSExp
csexp_ecsn
 = csexp_empty +++
    csexp_chanset +++  
    csexp_channame


-- ProcDecl	::= \circprocess N \circdef ProcDef
-- 			| \circprocess N[N^{+}] \circdef ProcDef
circus_proc_decl :: EParser ZToken ProcDecl
circus_proc_decl
  =	do {tok L_CIRCPROCESS; 
 		optnls;
  		nm <- zdecl_name;
  		optnls;
  		tok L_CIRCDEF; 
 		optnls;
  		prc <- circus_proc_def;
  		return (CProcess nm prc)} +++
  	do {tok L_CIRCPROCESS; 
 		optnls;
  		nm <- zdecl_name;
  		optnls;
  		tok L_OPENBRACKET;
		nm1 <- zdecl_name;
		tok L_CLOSEBRACKET;
		optnls;
  		prc <- circus_proc_def;
		return (CGenProcess nm nm1 prc)}


--ProcDef		::= Decl \circspot ProcDef
-- 				| Decl \circindex ProcDef
-- 				| Proc
circus_proc_def :: EParser ZToken ProcDef
circus_proc_def
  =	do {decls <- zdecl_part;
  		optnls;
  		tok L_CIRCSPOT; 
 		optnls;
  		prc <- circus_process;
  		return (ProcDefSpot (concat decls) prc)} +++
  	do {decls <- zdecl_part;
  		optnls;
  		tok L_CIRCINDEX; 
 		optnls;
  		prc <- circus_process;
  		return (ProcDefIndex (concat decls) prc)} +++
  	do {prc <- circus_process;
  		return (CoreProcess prc)}


--Proc 		::= \circbegin PPar*
			-- \circstate SchemaExp PPar*
			-- \circspot Action
			-- \circend
			-- | Proc \circsemi Proc
			-- | Proc \extchoice Proc
			-- | Proc \intchoice Proc
			-- | Proc \lpar CSExp \rpar Proc
			-- | Proc \interleave Proc
			-- | Proc \circhide CSExp
			-- | (Decl \circspot ProcDef)(Exp^{+})
			-- | N(Exp^{+})
			-- | N
			-- | (Decl \circindex ProcDef)\lcircindex Exp^{+} \rcircindex
			-- | N\lcircindex Exp^{+} \rcircindex
			-- | Proc[N^{+}:=N^{+}]
			-- | N[Exp^{+}]
			-- | \Semi Decl \circspot Proc
			-- | \Extchoice Decl \circspot Proc
			-- | \IntChoice Decl \circspot Proc
			-- | \lpar CSExp \rpar Decl \circspot Proc
			-- | \Interleave Decl \circspot Proc
circus_process :: EParser ZToken CProc
circus_process 
	=do {tok L_CIRCUSBEGIN;
		optnls;
		pp2 <- proc_par;
		optnls;
		tok L_CIRCSPOT;
		main2 <- circus_action;
		optnls;
		tok L_CIRCUSEND;
		return (ProcStalessMain pp2 main2)
		}+++
	do {tok L_CIRCUSBEGIN;
		optnls;
		stt <- zschema_box_single;
		optnls;
		pp1 <-  proc_par;
		optnls;
		tok L_CIRCSPOT;
		main <- circus_action;
		optnls;
		tok L_CIRCUSEND;
		return (ProcMain1 stt pp1 main)
		}+++
	do {tok L_CIRCUSBEGIN;
		optnls;
		pp <- proc_par;
		optnls;
		stt <- zschema_box_single;
		optnls;
		pp1 <-  proc_par;
		optnls;
		tok L_CIRCSPOT;
		main <- circus_action;
		optnls;
		tok L_CIRCUSEND;
		return (ProcMain pp stt pp1 main)
		}
	


-- NSExp	::= \{\}
		-- | \{N^{+}\}
		-- | N
		-- | NSExp \union NSExp
		-- | NSExp \intersect NSExp
		-- | NSExp \circhide \NSExp
circusnsexpr ::  EParser ZToken NSExp
circusnsexpr
 = circusnsexpr_union +++
   circusnsexpr_intersect  +++
   circusnsexpr_hide +++
   nsexp_ensn 

circusnsexpr_union ::  EParser ZToken NSExp
circusnsexpr_union
 = do {cs1 <- nsexp_ensn; -- NSExp \union NSExp
 		optnls; tok L_UNION; optnls;
 		cs2 <- circusnsexpr;
 		return (NSUnion cs1 cs2)}
circusnsexpr_intersect ::  EParser ZToken NSExp
circusnsexpr_intersect
 = do {cs1 <- nsexp_ensn; -- NSExp \union NSExp
 		optnls; tok L_INTERSECT; optnls;
 		cs2 <- circusnsexpr;
 		return (NSIntersect cs1 cs2)}
circusnsexpr_hide ::  EParser ZToken NSExp
circusnsexpr_hide
 = do {cs1 <- nsexp_ensn; -- NSExp \union NSExp
 		optnls; tok L_CIRCHIDE; optnls;
 		cs2 <- circusnsexpr;
 		return (NSHide cs1 cs2)}

nsexp_empty ::  EParser ZToken NSExp
nsexp_empty
 = do {tok L_LCHANSET; tok L_RCHANSET; -- \{\}
		return NSExpEmpty}

nsexp_nset_mult ::  EParser ZToken NSExp
nsexp_nset_mult
 = do {tok L_LCHANSET; -- \{N^{+}\}
 		optnls;
  		ws <- zdecl_name `sepby1` comma; 
		optnls;
 		tok L_RCHANSET;
 		return (NSExprMult [(make_zvar w d) | (w,d) <- ws])}
nsexp_nset_sgl ::  EParser ZToken NSExp
nsexp_nset_sgl
 = do {tok L_LCHANSET; -- \{N^{+}\}
 		optnls;
  		(w,d) <- zdecl_name;
		optnls;
 		tok L_RCHANSET;
 		return (NSExprSngl (make_zvar w d))}

nsexp_ensn ::  EParser ZToken NSExp
nsexp_ensn
 = nsexp_empty +++
    nsexp_nset_mult +++  
    nsexp_nset_sgl

--PPar 		::= Par
-- 			| N \circdef ParAction
-- 			| \circnameset N == NSExp
proc_par :: EParser ZToken [PPar]
proc_par 
	= --do { ppar <- zparagraph `sepby1` optnls; return [ProcPar (concat ppar)]} +++
	circus_action_par_lim 


circus_action_par_lim :: EParser ZToken [PPar]
circus_action_par_lim
  = do {
  	tok L_END_CIRCUS;
  	optnls;
 	cap <- circus_action_par `sepby1` optnls;
  	optnls;
  	tok L_BEGIN_CIRCUS;
  	return cap}

circus_action_par :: EParser ZToken PPar
circus_action_par
  = do {
  	tok L_BEGIN_CIRCUSACTION;
  	cut;
	nm <- zdecl_name;
	optnls;
	tok L_CIRCDEF; 
	optnls;
	prc <- par_action;
  	optnls;
  	tok L_END_CIRCUSACTION;
  	return (CParAction nm prc)}

--ParAction 	::= Action
-- 				| Decl \circspot ParAction
par_action :: EParser ZToken ParAction
par_action =
	do {cact <- circus_action; return (CircusAction cact)} +++
	do {decls <- zdecl_part;
  		optnls;
  		tok L_CIRCSPOT; 
 		optnls;
  		prc <- par_action;
  		return (ParActionDecl (concat decls) prc)}

--Action 		::= SchemaExp
-- 				| Command
-- 				| N
-- 				| CSPAction
-- 				| Action[N^{+}:=N^{+}] -- TODO: to be done
circus_action :: EParser ZToken CAction
circus_action 
	= --do {stt <- zschema_box_single; return (CActionSchema stt)} +++
	  -- do {nm <- circus_command; return (CActionCommand nm)} +++
	  do {nm <- zdecl_name; return (CircusActionName nm)} +++
	  do {csp <- csp_action; return (CCSPAction csp)}


--CSPAction	::= \Skip | \Stop | \Chaos | Comm \then Action
-- | Pred \circguard Action
-- | Action \circseq Action
-- | Action \extchoice Action
-- | Action \intchoice Action
-- | Action \lpar NSExp | CSExp | NSExp \rpar Action
-- | Action \linter NSExp | NSExp \rinter Action
-- | Action \circhide CSExp
-- | ParAction(Exp^{+)
-- | \circmu N \circspot Action
-- | \Semi Decl \circspot Action
-- | \Extchoice Decl \circspot Action
-- | \IntChoice Decl \circspot Action
-- | \lpar CSExp \rpar Decl \circspot \lpar NSExp \rpar Action
-- | \Interleave Decl \circspot \linter NSExp \rinter Action
csp_action :: EParser ZToken CSPAction
csp_action =
	do {tok L_SKIP; return CSPSkip} +++
	do {tok L_STOP; return CSPStop} +++
	do {tok L_CHAOS; return CSPChaos}

--Comm 		::= N CParameter* | N [Exp^{+}] CParameter *

--CParameter	::= ?N | ?N : Pred | !Exp | .Exp

--Command 	::= N^{+} := Exp^{+}
-- | \circif GActions \cirfi
-- | \circvar Decl \circspot Action
-- | N^{+} :[Pred,Pred]
-- | \{Pred\}
-- | [Pred]
-- | \circval Decl \circspot Action
-- | \circres Decl \circspot Action
-- | \circvres Decl \circspot Action
-- circus_command :: EParser ZToken CAction
-- circus_command =

--GActions 	::= Pred \then Action
-- | Pred \then Action \extchoice GAction

--------------------------------------
---------- Auxiliary Defs ------------
---- From the original Jaza Files ----
--------------------------------------


zunboxed_para :: EParser ZToken [ZPara]
zunboxed_para
  = do  tok L_BEGIN_ZED
	cut
	s <- zitem `sepby1` many1 zsep
	optnls
	tok L_END_ZED
	return (concat s)

zitem :: EParser ZToken [ZPara]
zitem = zitem_givensets +++
	zitem_sdef +++
	zitem_abbrev +++
	zitem_freetype +++
	zitem_pred

zitem_givensets
  = do  tok L_OPENBRACKET
	gs <- zident `sepby1` comma
	tok L_CLOSEBRACKET
	return (map ZGivenSetDecl gs)

zitem_sdef :: EParser ZToken [ZPara]
zitem_sdef
  = do  name <- zschema_name
	optnls
	tok L_DEFS
	cut
	optnls
	se <- zschema_exp
	return [ZSchemaDef name se]

zitem_abbrev :: EParser ZToken [ZPara]
zitem_abbrev
  = do  zdef <- zdef_lhs
	optnls
	tok L_EQUALS_EQUALS
	cut
	optnls
	e <- zexpression
	return [ZAbbreviation zdef e]

zitem_freetype :: EParser ZToken [ZPara]
zitem_freetype
  = do  zdef <- zdef_lhs
	optnls
	tok L_COLON_COLON_EQUALS
	cut
	optnls
	b <- zbranch `sepby1` do {optnls; tok L_VERT; optnls}
	return [ZFreeTypeDef zdef b]


zitem_pred :: EParser ZToken [ZPara]
zitem_pred = do {p <- zpredicate; return [ZPredicate p]}


zit_hiding :: EParser ZToken [ZVar]
zit_hiding
  = do  {hidel <- many1 zhide;
	 return (concat hidel)}

zhide :: EParser ZToken [ZVar]
zhide
  = do  optnls
	tok L_HIDE
	optnls
	tok L_OPENPAREN
	dn <- zdecl_name `sepby1` comma
	tok L_CLOSEPAREN
	return dn

opt ::  a -> EParser ZToken a -> EParser ZToken a
opt def p = p +++ return def

-- Takes as many backslash as needed
optnls :: EParser ZToken [ZToken]
optnls = many (tok L_BACKSLASH_BACKSLASH)

comma = do {optnls; tok L_COMMA; optnls}
semicolon = do {optnls; tok L_SEMICOLON; optnls}

zmachine_box

 :: EParser ZToken [ZPara]
zmachine_box
  -- Eg: \begin{machine}{foo} State \init Init \ops Op1; Op2 \end{machine}
  -- Note: All names must be undecorated schema names.
  = do  tok L_BEGIN_MACHINE
	cut
	tok L_OPENBRACE
	name <- zword
	tok L_CLOSEBRACE
	-- TODO: add generic formals?
	state <- zword
	tok (L_WORD "\\machineInit")
	init <- zword
	tok (L_WORD "\\machineOps")
	ops <- zword `sepby1` zsep
	tok L_END_MACHINE
	return [ZMachineDef{machName=name,
    machState=state,
    machInit=init,
    machOps=ops}]

zgivenval :: EParser ZToken String
zgivenval =
  do L_GIVENVAL s <- sat isGivenVal
     return s
  where
  isGivenVal (L_GIVENVAL _) = True
  isGivenVal _              = False