\section{Introduction}

This is a trivial program that prints the first 20 factorials.

\begin{code}
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
--      In other words, a given set declaration, [A,B,C] is expanded
--      out into three separate given set declarations.  Similarly,
--      abbreviations (a==...), free type definitions etc. are all
--      expanded out into separate paragraphs.  This makes the
--      abstract syntax trees simpler (each paragraph generally
--      defines just one name).
--      However, axdef and gendef paragraphs are not expanded,
--      even when they define multiple names, because we assume that
--      the names and associated predicates are grouped together for
--      some semantic reason.  E.g. It is good style for all the
--      constraints on a declared constant to be given in the axdef
--      paragraph where the constant is declared.
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
parseZpara = check_parse . epapply zparagraphs . zlex lexstate0

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
  = do {ps <- many zparagraphs; return (concat ps)}

-- Paragraph ::= [Ident,...,Ident]
--		|Axiomatic-Box
--		|Schema-Box
--		|Generic-Box
--		|Schema-Name[Gen-Formals]* \defs Schema-Exp
--		|Def-Lhs	== Expression
--		|Ident ::= Branch | ... | Branch
--		|Predicate

zparagraphs :: EParser ZToken ZSpec
zparagraphs
  = zparagraph
    +++ circus_paragraphs

zparagraph :: EParser ZToken [ZPara]
zparagraph
  = zunboxed_para +++
    zaxiomatic_box +++ -- \begin{axdef}...\end{axdef}
    zschema_box +++
    zmachine_box   -- an extension for defining state machines.


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
  = do  {name <- zschema_name;
  	optnls;
  	tok L_DEFS;
  	cut;
  	optnls;
  	se <- zschema_exp;
  	return [ZSchemaDef name se]}

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

zdef_lhs :: EParser ZToken ZVar
zdef_lhs
  = do  var_name <- zword
	dec <- zdecoration
	return (make_zvar var_name dec)
-- TODO Pre_Gen_Decor Ident, Ident In_Gen_decor Ident and generic formals

zbranch :: EParser ZToken ZBranch
zbranch
  = do  {vn <- zvar_name;
	 tok L_LDATA;
	 e <- zexpression;
	 tok L_RDATA;
	 return (ZBranch1 vn e)} +++
    do  {i <- zident;
	 return (ZBranch0 i)}

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


zschema_exp_1 :: EParser ZToken ZSExpr
zschema_exp_1
  = chainl1 zschema_exp_1a (do {optnls; tok L_PIPE; optnls; return (ZS2 ZSPipe)})

-- Note this differs from the Breuer/Bowen grammar because
--  \implies binds tighter than \iff and the precedence of
--  schema operators is respected as in zrm.

zschema_exp_1a :: EParser ZToken ZSExpr
zschema_exp_1a
  = chainl1 zschema_exp_1b (do {optnls; tok L_SEMI; optnls; return (ZS2 ZSSemi)})

zschema_exp_1b :: EParser ZToken ZSExpr
zschema_exp_1b
  = chainl1 zschema_exp_1c (do {optnls; tok L_PROJECT; optnls; return (ZS2 ZSProject)})

zschema_exp_1c :: EParser ZToken ZSExpr
zschema_exp_1c
  = chainl1 zschema_exp_1d (do {optnls; tok L_IFF; optnls; return (ZS2 ZSIff)})

zschema_exp_1d :: EParser ZToken ZSExpr
zschema_exp_1d
  = chainr1 zschema_exp_1e (do {optnls; tok L_IMPLIES; optnls; return (ZS2 ZSImplies)})

zschema_exp_1e :: EParser ZToken ZSExpr
zschema_exp_1e
  = chainl1 zschema_exp_1f (do {optnls; tok L_LOR; optnls; return (ZS2 ZSOr)})

zschema_exp_1f :: EParser ZToken ZSExpr
zschema_exp_1f
  = chainl1 zschema_exp_3 (do {optnls; tok L_LAND; optnls; return (ZS2 ZSAnd)})


zschema_exp_3 :: EParser ZToken ZSExpr
zschema_exp_3
  = do { se <- zschema_exp_u;
	 se2 <- opt se (do {hidel <- zit_hiding;
			   return (ZSHide se hidel)});
	 return se2 }

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

zschema_ref :: EParser ZToken ZSExpr
zschema_ref
  = do  {zn <- zschema_name;
	 dec <- zdecoration;
	 reps <- opt [] zreplace;
	 return (ZSRef zn dec reps)}
-- TODO Gen_Actuals

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

zschema_name :: EParser ZToken ZSName
zschema_name
  = do  {tok L_DELTA; name <- zword; return (ZSDelta name)} +++
    do  {tok L_XI; name <- zword; return (ZSXi name)} +++
    do  {name <- zword; return (ZSPlain name)}


zschema_text :: EParser ZToken [ZGenFilt]
zschema_text
  = do  d <- zdeclaration
	p <- opt [] (do {optnls;
			 tok L_VERT;
			 optnls;
			 p <- zpredicate;
			 return [Check p]})
	return (concat d ++ p)

zdeclaration :: EParser ZToken [[ZGenFilt]]
zdeclaration = zbasic_decl `sepby1` do {optnls; tok L_SEMICOLON; optnls}

zsep :: EParser ZToken ZToken
zsep
  = tok L_BACKSLASH_BACKSLASH +++
    tok L_SEMICOLON +++
    tok L_ALSO

opt ::  a -> EParser ZToken a -> EParser ZToken a
opt def p = p +++ return def

optnls :: EParser ZToken [ZToken]
optnls = many (tok L_BACKSLASH_BACKSLASH)

comma = do {optnls; tok L_COMMA; optnls}

zaxiomatic_box :: EParser ZToken [ZPara]
zaxiomatic_box
  = do  tok L_BEGIN_AXDEF
	cut
	decls <- zdecl_part
	ax <- opt [] (do {optnls; tok L_WHERE; cut; optnls; zaxiom_part })
	optnls
	tok L_END_AXDEF
	return [ZAxDef (concat decls ++ ax)]

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

zmachine_box :: EParser ZToken [ZPara]
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

zdecl_part :: EParser ZToken [[ZGenFilt]]
zdecl_part = zbasic_decl `sepby1` many1 zsep

zaxiom_part :: EParser ZToken [ZGenFilt]
zaxiom_part
  = do  ps <- zpredicate `sepby1` many1 zsep
	return (map Check ps)

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

zexpressions :: EParser ZToken [ZExpr]
zexpressions
  = do  {e <- zexpression;
	 el <- many (do {comma;
			 e1 <- zexpression;
			 return e1});
	 return (e : el)}
zexpressions1 :: EParser ZToken [ZExpr]
zexpressions1
  = do  {e <- zexpression `sepby1` do {optnls; tok L_COMMA; optnls};
	 		return e}
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
	 return (ZSetDisplay el) }
	+++ do {tok L_OPENSET;
				st <- zschema_text;
				e <- opt Nothing (do {optnls;
									tok L_AT;
									optnls;
									exp <- zexpression;
									return (Just exp)});
				tok L_CLOSESET;
				return (ZSetComp st e)}


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


zlet_def :: EParser ZToken (ZVar,ZExpr)
zlet_def
  = do  {vn <- zvar_name;
	 optnls;
	 tok L_EQUALS_EQUALS;
	 optnls;
	 e <- zexpression;
	 return (vn,e)}

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

zvar_name :: EParser ZToken ZVar
zvar_name
  = do  {tok L_OPENPAREN; vn <- zop_name; tok L_CLOSEPAREN; return vn} +++
    zident

zdecl_name :: EParser ZToken ZVar
zdecl_name = zop_name +++ zident

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

zin_sym_decor :: EParser ZToken ZVar
zin_sym_decor
  = do  iop <- zin_fun_decor 0 +++ zin_gen_decor +++ zin_rel_decor
	return iop

zpre_sym_decor :: EParser ZToken ZVar
zpre_sym_decor = zpre_gen_decor +++ zpre_rel_decor

zident :: EParser ZToken ZVar
zident = do {w <- zword; d <- zdecoration; return (make_zvar w d)}


zdecoration :: EParser ZToken [ZDecor]
zdecoration = many zstroke

zstroke :: EParser ZToken ZDecor
zstroke
  = do  L_STROKE w <- sat isStroke
	return w
    where
    isStroke (L_STROKE _) = True
    isStroke _            = False

zword :: EParser ZToken String
zword =
  do L_WORD w <- sat isWord
     return w
  where
  isWord (L_WORD _) = True
  isWord _          = False

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

znumber :: EParser ZToken ZInt
znumber =
  do L_NUMBER i <- sat isNumber
     return i
  where
  isNumber (L_NUMBER _) = True
  isNumber _            = False

zgivenval :: EParser ZToken String
zgivenval =
  do L_GIVENVAL s <- sat isGivenVal
     return s
  where
  isGivenVal (L_GIVENVAL _) = True
  isGivenVal _              = False

--------------------------------------
-------------  Circus   -------------
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
	-- \circchannel CDecl
	= circ_chan
	-- \circchanset N == CSExp
	+++ circ_chanset
	-- Par
	+++ circus_zitem
	-- ProcDecl
	+++ circus_proc

-- Z Paragraphs within Circus environment
circus_zitem :: EParser ZToken [ZPara]
circus_zitem =
	do {s <- zitem `sepby1` many1 zsep; return (concat s)}

-- Circus Process declaration
circus_proc :: EParser ZToken [ZPara]
circus_proc
  = do {cdec <- circus_proc_decl;
  	    	return [Process cdec]}

-- Circus Channel Declaration
circ_chan :: EParser ZToken [ZPara]
circ_chan
  = do {optnls;
  tok L_CIRCCHANNEL;
  	    	cdec <- circusdecl;
  	    	return [CircChannel cdec]}

-- Circus Chanset declaration

circ_chanset :: EParser ZToken [ZPara]
circ_chanset
  = do {tok L_CIRCCHANSET;
 		optnls;
  		tp <- zword;
 		optnls;
 		tok L_EQUALS_EQUALS;
		cut;
		optnls;
 		cdec <- circuscsexpr;
 		return [CircChanSet tp cdec]}
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
	-- [N^{+}]N^{+} : Exp
	= do {tok L_OPENBRACKET;
		tp <- zword;
		tok L_CLOSEBRACKET;
		optnls;
		ws <- zword `sepby1` comma;
		optnls;
		tok L_COLON;
		optnls;
		e <- zexpression;
		return (mapCGenChanDecl tp ws e)}
	-- N^{+} : Exp
	+++ do {ws <- zword `sepby1` comma; optnls;
		tok L_COLON;
		optnls;
		e <- zexpression;
		return (mapCChanDecl ws e)}
	-- N^{+}
	+++ do {gs <- zword `sepby1` comma;
		return (map CChan gs)}

mapCGenChanDecl :: ZName -> [ZName] -> ZExpr -> [CDecl]
mapCGenChanDecl tp [] e      = []
mapCGenChanDecl tp [x] e    = [CGenChanDecl tp x e]
mapCGenChanDecl tp (x:xs) e = (CGenChanDecl tp x e):(mapCGenChanDecl tp xs e)

mapCChanDecl :: [ZName] -> ZExpr -> [CDecl]
mapCChanDecl [] e      = []
mapCChanDecl [x] e    = [CChanDecl x e]
mapCChanDecl (x:xs) e = (CChanDecl x e):(mapCChanDecl xs e)
--CSExp		::= \lchanset \rchanset
-- | \lchanset N^{+} \rchanset
-- | N
-- | CSExp \union CSExp
-- | CSExp \intersect CSExp
-- | CSExp \circhide CSExp

circuscsexpr ::  EParser ZToken CSExp
circuscsexpr
	= circuscsexpr_union
	+++ circuscsexpr_intersect
	+++ circuscsexpr_hide
	+++ csexpr_ecsn

chansetlist :: EParser ZToken [ZName]
chansetlist
  = do  {e <- zword;
	 el <- many (do {comma; e1 <- zword; return e1});
	 return (e : el)}

circuscsexpr_union ::  EParser ZToken CSExp
circuscsexpr_union
	= chainl1 circuscsexpr_intersect (do {optnls; tok L_UNION; optnls; return ChanSetUnion})

circuscsexpr_intersect ::  EParser ZToken CSExp
circuscsexpr_intersect
	= chainl1 circuscsexpr_hide (do {optnls; tok L_INTERSECT; optnls; return ChanSetInter})

circuscsexpr_hide ::  EParser ZToken CSExp
circuscsexpr_hide
	= chainl1 csexpr_ecsn (do {optnls; tok L_CIRCHIDE; optnls; return ChanSetDiff})

csexpr_ecsn ::  EParser ZToken CSExp
csexpr_ecsn
	= do {ws <- zword; -- N
   		return (CSExpr ws)}
	+++ do {tok L_LCHANSET; -- \lchanset N^{+} \rchanset
  		ws <- opt [] (zword `sepby1` do {optnls; tok L_COMMA; optnls});
 		tok L_RCHANSET;
 		return (CChanSet ws)}
	+++ do {tok L_LCHANSET; tok L_RCHANSET; -- \lchanset \rchanset
		return CSEmpty}
	+++ do {tok L_OPENPAREN;
			optnls;
			xx <- circuscsexpr;
			optnls;
			tok L_CLOSEPAREN;
			return xx}

-- ProcDecl	::= \circprocess N \circdef ProcDef
-- 			| \circprocess N[N^{+}] \circdef ProcDef
circus_proc_decl :: EParser ZToken ProcDecl
circus_proc_decl
  =	do {tok L_CIRCPROCESS; -- \circprocess N \circdef ProcessDef
 		optnls;
  		nm <- zword;
  		optnls;
  		tok L_CIRCDEF ;
		optnls;
  		prc <- circus_proc_def;
  		return (CProcess nm prc)}
  	+++ do {tok L_CIRCPROCESS; -- \circprocess N[N^{+}] \circdef ProcessDef
 		optnls;
  		nm <- zword;
  		optnls;
  		tok L_OPENBRACKET;
		nm1 <- zword `sepby` comma;
		tok L_CLOSEBRACKET ;
  		optnls;
  		tok L_CIRCDEF ;
		optnls;
  		prc <- circus_proc_def;
		return (CGenProcess nm nm1 prc)}

--ProcessDef    ::= Decl \circspot ProcessDef
-- 				| Decl \circindex ProcessDef
-- 				| Proc
circus_proc_def :: EParser ZToken ProcessDef
circus_proc_def
  =
  	--Decl \circspot ProcessDef
  	do {decls <- zdeclaration;
		  		optnls;
		  		tok L_CIRCSPOT;
		 		optnls;
		  		prc <- circus_proc_def;
  		return (ProcDefSpot (concat decls) prc)}
  	-- Decl \circindex ProcessDef
  	+++ do {decls <- zdeclaration;
		  		optnls;
		  		tok L_CIRCINDEX ;
				cut;
				optnls;
		  		prc <- circus_proc_def;
  	return (ProcDefIndex (concat decls) prc)}
  	+++ do {prc <- circus_process; -- Proc
  		return (ProcDef prc)}
  	+++ do {tok L_OPENPAREN;
  			cp <- circus_proc_def;
  			tok L_CLOSEPAREN;
  			return cp}

--Proc 		::= \circbegin PPar*
			-- \circstate SchemaExp PPar*
			-- \circspot Action
			-- \circend
			-- | Proc \cirCSeq Proc
			-- | Proc \extchoice Proc
			-- | Proc \intchoice Proc
			-- | Proc \lpar CSExp \rpar Proc
			-- | Proc \interleave Proc
			-- | Proc \circhide CSExp
			-- | (Decl \circspot ProcessDef)(Exp^{+})
			-- | N(Exp^{+})
			-- | N
			-- | (Decl \circindex ProcessDef)\lcircindex Exp^{+} \rcircindex
			-- | N\lcircindex Exp^{+} \rcircindex
			-- | Proc[N^{+}:=N^{+}]
			-- | N[Exp^{+}]
			-- | \Semi Decl \circspot Proc
			-- | \Extchoice Decl \circspot Proc
			-- | \IntChoice Decl \circspot Proc
			-- | \lpar CSExp \rpar Decl \circspot Proc
			-- | \Interleave Decl \circspot Proc

-- Precedence order:
-- top
-- ||| (interleave >>
-- 		[| |] (parallel) >>
-- 			|~| (internal choice) >>
-- 				[] (external choice >>
-- 					; (sequence)
-- bottom

circus_process :: EParser ZToken CProc
circus_process
	-- \Interleave Decl \circspot Proc
	= do {tok L_REPINTERLEAVE;
	  		optnls;
			decls <- zdeclaration;
	  		optnls;
	  		tok L_CIRCSPOT;
	 		optnls;
	  		cp1<- circus_process;
			return (CRepInterlProc (concat decls) cp1)}
	-- \lpar CSExp \rpar Decl \circspot Proc
	+++ do {tok L_LPAR;
			optnls;
 			csex <- circuscsexpr;
			optnls;
			tok L_RPAR;;
			decls <- zdeclaration;
	  		optnls;
	  		tok L_CIRCSPOT ;
			cut;
			optnls;
	  		prc <- circus_process;
	  		return (CRepParalProc csex (concat decls) prc)}
	-- \IntChoice Decl \circspot Proc
	+++  do {tok L_REPINTCHOICE;
			decls <- zdeclaration;
	  		optnls;
	  		tok L_CIRCSPOT;
			cut;
			optnls;
	  		prc <- circus_process;
	  		return (CRepIntChProc (concat decls) prc)}
	-- \Extchoice Decl \circspot Proc
	+++ do {tok L_REPEXTCHOICE;
	  		decls <- zdeclaration;
	  		optnls;
	  		tok L_CIRCSPOT;
			cut;
			optnls;
	  		prc <- circus_process;
	  		return (CRepExtChProc (concat decls) prc)}
	-- \Semi Decl \circspot Proc
	+++ do {tok L_REPSEMI;
			decls <- zdeclaration;
	  		optnls;
	  		tok L_CIRCSPOT;
			cut;
			optnls;
	  		prc <- circus_process;
			return (CRepSeqProc (concat decls) prc)}
	+++ circus_process_interleave

-- recursive circus processe functions
-- Proc \interleave Proc
circus_process_interleave :: EParser ZToken CProc
circus_process_interleave
	 = chainl1 circus_process_paral_cs (do {optnls; tok L_INTERLEAVE; optnls; return CInterleave})
	-- = chainl1 circus_process_paral_cs (do {optnls; tok L_INTERLEAVE; optnls; return CInterleave})

-- Proc \lpar CSExp \rpar Proc
circus_process_paral_cs :: EParser ZToken CProc
circus_process_paral_cs
	= recursiveCParParal1 circus_process_int_choice (do {optnls; tok L_LPAR; optnls; csex <- circuscsexpr; optnls; tok L_RPAR; return csex })

-- Proc \intchoice Proc
circus_process_int_choice :: EParser ZToken CProc
circus_process_int_choice
	= chainl1 circus_process_ext_choice (do {optnls; tok L_INTCHOICE; optnls; return CIntChoice})

-- Proc \extchoice Proc
circus_process_ext_choice :: EParser ZToken CProc
circus_process_ext_choice
	= chainl1 circus_process_seq (do {optnls; tok L_EXTCHOICE; optnls; return CExtChoice})

-- Proc \cirCSeq Proc
circus_process_seq :: EParser ZToken CProc
circus_process_seq
	= chainl1 circus_process_u (do {optnls; tok L_CIRCSEQ; optnls; return CSeq})
circus_process_u :: EParser ZToken CProc
circus_process_u
	-- N(Exp^{+})
	= circus_process_param_proc
	-- Proc[N^{+}:=N^{+}]
	+++ circus_process_rename
	-- N[Exp^{+}]
	+++ circus_process_rep_proc
	-- N
	+++ circus_process_name
	-- (Proc)
	+++ circus_process_paren_proc
	-- \circbegin PPar*
		-- \circspot Action
		-- \circend
	+++ circus_proc_stateless_main
	-- \circbegin PPar*
		-- \circstate SchemaExp PPar*
		-- \circspot Action
		-- \circend
	+++ circus_proc_main
	-- Proc \circhide CSExp
	+++ circus_process_hide
	-- Action rename
circus_process_rename :: EParser ZToken CProc
circus_process_rename
	= do {nm <- zword; optnls;
			tok L_OPENBRACKET;
			ws <- sepbycomma1 zword;
	 		tok L_ASSIGN;
	 		zxprs <- zexpressions;
			tok L_CLOSEBRACKET;
			return (CProcRename nm ws zxprs)}
-- Proc \circhide CSExp
circus_process_hide :: EParser ZToken CProc
circus_process_hide
	= do {tok L_OPENPAREN;
			optnls;
			cp1 <- circus_process;
			optnls;
			tok L_CIRCHIDE;
			optnls;
			csex <- circuscsexpr;
			optnls;
			tok L_CLOSEPAREN;
			return (CHide cp1 csex)}
-- N
circus_process_name :: EParser ZToken CProc
circus_process_name
	= do {nm <- zword;
			return (CircusProc nm)}

-- (N)
circus_process_paren_proc :: EParser ZToken CProc
circus_process_paren_proc
	= do {tok L_OPENPAREN;
			optnls;
			xp <- circus_process;
			optnls;
			tok L_CLOSEPAREN ;
			return xp}
-- N(Exp^{+})
circus_process_param_proc :: EParser ZToken CProc
circus_process_param_proc
	= do {nm <- zword;
	  		tok L_OPENPAREN;
			xp <- opt [] (zexpression `sepby1` do {optnls; tok L_COMMA; optnls});
			tok L_CLOSEPAREN ;
			return (CParamProc nm xp)}

-- N[Exp^{+}]
circus_process_rep_proc :: EParser ZToken CProc
circus_process_rep_proc
	= do {nm <- zword;
	  		optnls;
	  		tok L_OPENBRACKET;
			xp <- zexpressions;
			tok L_CLOSEBRACKET ;
			return (CGenProc nm xp)}

-- \circbegin PPar*
	-- \circspot Action
	-- \circend
circus_proc_stateless_main :: EParser ZToken CProc
circus_proc_stateless_main
	= do {tok L_CIRCUSBEGIN;
			optnls;
			pp3 <- proc_par `sepby` many1 zsep;
			optnls;
			tok L_CIRCSPOT;
			main2 <- circus_action;
			optnls;
			tok L_CIRCUSEND;
			return (ProcStalessMain (concat pp3) main2)
			}

-- \circbegin PPar*
	-- \circstate SchemaExp PPar*
	-- \circspot Action
	-- \circend
circus_proc_main  :: EParser ZToken CProc
circus_proc_main
	= do {tok L_CIRCUSBEGIN;
			optnls;
			pp <- proc_par `sepby` many1 zsep;
			optnls;
			stt <- circ_state;
			optnls;
			pp1 <- proc_par `sepby` many1 zsep;
			optnls;
			tok L_CIRCSPOT;
			main <- circus_action;
			optnls;
			tok L_CIRCUSEND;
			return (ProcMain (remFromListSinglElem stt) ((concat pp)++(concat pp1)) main)
			}

circ_state :: EParser ZToken [ZPara]
circ_state
	= do {tok L_CIRCSTATE;
				stt <- zitem_sdef; return stt}
	+++ do {tok L_BEGIN_CIRCUS;
			  	cut;
			  	tok L_CIRCSTATE;
				stt1 <- zitem_sdef;
			  	optnls;
			  	tok L_END_CIRCUS;
			  	return stt1}

remFromListSinglElem [s] = s

-- NSExp	::= \{\}
		-- | \{N^{+}\}
		-- | N
		-- | NSExp \union NSExp
		-- | NSExp \intersect NSExp
		-- | NSExp \circhide \NSExp
circusnsexpr ::  EParser ZToken NSExp
circusnsexpr
 = nsexp_ensn
 +++ circusnsexpr_union
 +++ circusnsexpr_bigunion
 +++ circusnsexpr_intersect
 +++ circusnsexpr_hide

-- NSExp \union NSExp
circusnsexpr_union ::  EParser ZToken NSExp
circusnsexpr_union
 = do {cs1 <- nsexp_ensn; -- NSExp \union NSExp
	 		optnls; tok L_UNION; optnls;
	 		cs2 <- circusnsexpr;
	 		return (NSUnion cs1 cs2)}
-- \bigcup NSExp
circusnsexpr_bigunion ::  EParser ZToken NSExp
circusnsexpr_bigunion
 = do {tok L_BIGCUP; optnls;
	 		cs <- zset_exp;
	 		return (NSBigUnion cs)}

-- NSExp \intersect NSExp
circusnsexpr_intersect ::  EParser ZToken NSExp
circusnsexpr_intersect
 = do {cs1 <- nsexp_ensn; -- NSExp \union NSExp
	 		optnls; tok L_INTERSECT; optnls;
	 		cs2 <- circusnsexpr;
	 		return (NSIntersect cs1 cs2)}

-- NSExp \circhide \NSExp
circusnsexpr_hide ::  EParser ZToken NSExp
circusnsexpr_hide
 = do {cs1 <- nsexp_ensn; -- NSExp \union NSExp
	 		optnls; tok L_CIRCHIDE; optnls;
	 		cs2 <- circusnsexpr;
	 		return (NSHide cs1 cs2)}

--  \{\}
nsexp_empty ::  EParser ZToken NSExp
nsexp_empty
 = do {tok L_OPENBRACE;
 			tok L_CLOSEBRACE; -- \{\}
			return NSExpEmpty}

-- \{N^{+}\}
nsexp_nset_mult ::  EParser ZToken NSExp
nsexp_nset_mult
	= do {tok L_OPENBRACE; -- \{N^{+}\}
	  		ws <- zword `sepby1` comma;
	 		tok L_CLOSEBRACE;
	 		return (NSExprMult ws)}

-- N
nsexp_nset_sgl ::  EParser ZToken NSExp
nsexp_nset_sgl
	= do {wd <- zword;
			return (NSExprSngl wd)}
-- N(Exp+)
nsexp_nset_param ::  EParser ZToken NSExp
nsexp_nset_param
	= do {pa <- zword;
			optnls;
			tok L_OPENPAREN;
			ze <- zexpression `sepby1` comma;
			tok L_CLOSEPAREN;
			return (NSExprParam pa ze)}

nsexp_ensn ::  EParser ZToken NSExp
nsexp_ensn
	= nsexp_nset_param
		+++ nsexp_nset_sgl
		+++ nsexp_nset_mult
		+++ nsexp_empty



--PPar 		::= Par
-- 			| N \circdef ParAction
-- 			| \circnameset N == NSExp
proc_par :: EParser ZToken [PPar]
proc_par
	=do {tok L_END_CIRCUS;
		  	cut;
		  	pr <- many proc_within_environments;
		  	optnls;
		  	tok L_BEGIN_CIRCUS;
		  	return (concat pr)}
	+++ do {cap <- many circus_action_p;
	  		return (concat cap)}

proc_within_environments
	= do {s <- zparagraph;
			return (takeZPara s)}
	 +++
	do {tok L_BEGIN_CIRCUSACTION;
		  	cut;
		  	cap <- many (do {x <- circus_action_p `sepby1` zsep; return (concat x)});
		  	optnls;
		  	tok L_END_CIRCUSACTION;
		  	return (concat cap)}

takeZPara :: [ZPara] -> [PPar]
takeZPara []     = []
takeZPara [x]    = [ProcZPara x]
takeZPara (x:xs) = [ProcZPara x]++(takeZPara xs)

circus_action_p :: EParser ZToken [PPar]
circus_action_p
	--  N \circdef ParAction
	= do {nma <- zword;
			optnls;
			tok L_CIRCDEF;
			optnls;
			pa <- par_action;
		  	return [CParAction nma pa]}
	-- N
	+++ do {nmp <- zitem;
	  		return (takeZPara nmp)}
	-- \circnameset N == NSExp
	+++ do {tok L_CIRCNAMESET;
		  	optnls;
			nmb <- zword;
			optnls;
			tok L_EQUALS_EQUALS;
			optnls;
			nexp1 <- circusnsexpr;
		  	return [CNameSet nmb nexp1]}

--ParAction 	::= Action
-- 				| Decl \circspot ParAction
par_action :: EParser ZToken ParAction
par_action
	-- Decl \circspot ParAction
	= do {decls <- zdeclaration;
	  		optnls;
	  		tok L_CIRCSPOT;
	 		optnls;
	  		prc <- par_action;
	  		return (ParamActionDecl (concat decls) prc)}
	-- Action
	+++ do {cact <- circus_action; return (CircusAction cact)}

-- The following is defined as circus_action_u, after the CSPAction functions
--Action 		::= SchemaExp
-- 				| Command
-- 				| N
-- 				| CSPAction
-- 				| Action[N^{+}:=N^{+}] -- TODO: to be done

--CSPAction	::= \Skip | \Stop | \Chaos | Comm \then Action
-- | Pred \circguard Action
-- | Action \circseq Action
-- | Action \extchoice Action
-- | Action \intchoice Action
-- | Action \lpar NSExp | CSExp | NSExp \rpar Action
-- | Action \lpar CSExp \rpar Action
-- | Action \interleave Action
-- | Action \linter NSExp | NSExp \rinter Action
-- | Action \circhide CSExp
-- | ParAction(Exp^{+)
-- | \circmu N \circspot Action
-- | \Semi Decl \circspot Action
-- | \Extchoice Decl \circspot Action
-- | \IntChoice Decl \circspot Action
-- | \lpar CSExp \rpar Decl \circspot \lpar NSExp \rpar Action
-- | \Interleave Decl \circspot \linter NSExp \rinter Action
-- | \Interleave x: T \circspot A
-- | \Interleave x: T \linter NS \rinter \circspot A
-- | \lpar CS \rpar x: T \circspot \lpar NS \rpar A
-- | \Intchoice x : T \circspot A
-- |\lpar CS \rpar x: T \circspot A

circus_action :: EParser ZToken CAction
circus_action
	-- \Interleave Decl \circspot \linter NSExp \rinter Action
	=  do {tok L_REPINTERLEAVE;
	  		optnls;
			decls <- zdecl_part;
	  		optnls;
	  		tok L_CIRCSPOT;
			optnls;
	  		tok L_LINTER;
			ns<- circusnsexpr;
			tok L_RINTER;
	 		optnls;
	  		cp1<- circus_action;
			return (CSPRepInterlNS (concat decls) ns cp1)}
	-- \Interleave x: T \circspot A
	+++ do {tok L_REPINTERLEAVE;
	  		optnls;
			decls <- zdecl_part;
	  		optnls;
	  		tok L_CIRCSPOT;
			optnls;
	  		cp1<- circus_action;
			return (CSPRepInterl (concat decls) cp1)}
	-- \lpar CS \rpar x: T \circspot \lpar NS \rpar A
	+++ do {tok L_LPAR;
			optnls;
 			csex <- circuscsexpr;
			optnls;
			tok L_RPAR;
			optnls;
			decls <- zdecl_part;
	  		optnls;
	  		tok L_CIRCSPOT ;
			cut;
			optnls;
	  		tok L_LPAR;
			optnls;
			ns<- circusnsexpr;
			optnls;
			tok L_RPAR;
	 		optnls;
	  		prc <- circus_action;
	  		return (CSPRepParalNS csex (concat decls) ns prc)}
	-- \lpar CS \rpar x: T \circspot A
	+++ do {tok L_LPAR;
			optnls;
 			csex <- circuscsexpr;
			optnls;
			tok L_RPAR;
			optnls;
			decls <- zdecl_part;
	  		optnls;
	  		tok L_CIRCSPOT ;
			cut;
			optnls;
	  		prc <- circus_action;
	  		return (CSPRepParal csex (concat decls)  prc)}
	-- \Intchoice x : T \circspot A
	+++ do {tok L_REPINTCHOICE;
			optnls;
			decls <- zdecl_part;
	  		optnls;
	  		tok L_CIRCSPOT ;
			cut;
			optnls;
	  		prcx <- circus_action;
	  		return (CSPRepIntChoice (concat decls) prcx)}
	-- \Extchoice x : T \circspot A
	+++ do {tok L_REPEXTCHOICE;
			decls <- zdecl_part;
	  		optnls;
	  		tok L_CIRCSPOT ;
			cut;
			optnls;
	  		prc <- circus_action;
	  		return (CSPRepExtChoice (concat decls)  prc)}
	-- \Semi x : T \circspot A
	+++ do {tok L_REPSEMI;
			decls <- zdecl_part;
	  		optnls;
	  		tok L_CIRCSPOT ;
			cut;
			optnls;
	  		prc <- circus_action;
			return (CSPRepSeq (concat decls) prc)}
	+++ circus_action_ns_interleave

-- recursive circus processes functions
-- | Action \linter NSExp | NSExp \rinter Action
circus_action_ns_interleave :: EParser ZToken CAction
circus_action_ns_interleave
	= recursiveCSPParParal2 circus_action_interleave
							(do {optnls;
								tok L_LINTER;
								optnls;
								nsex1 <- circusnsexpr;
								optnls;
								tok L_VERT;
								optnls;
								nsex2 <- circusnsexpr;
								optnls;
								tok L_RINTER;
								return (nsex1,nsex2)})
-- | Action \interleave Action
circus_action_interleave :: EParser ZToken CAction
circus_action_interleave
	= chainl1 circus_action_ns_paral (do {optnls;
											tok L_INTERLEAVE;
											optnls;
											return CSPInterleave})

-- | Action \lpar NSExp | CSExp | NSExp \rpar Action
circus_action_ns_paral :: EParser ZToken CAction
circus_action_ns_paral
	= recursiveCSPParParal1 circus_action_paral (do {optnls;
															tok L_LPAR;
															optnls;
															nsex1 <- circusnsexpr;
															optnls;
															tok L_VERT;
															optnls;
															csex <- circuscsexpr;
															optnls;
															tok L_VERT;
															optnls;
															nsex2 <- circusnsexpr;
															optnls;
															tok L_RPAR;
															return (nsex1,csex,nsex2)})

-- | Action \lpar CSExp \rpar Action
circus_action_paral :: EParser ZToken CAction
circus_action_paral
	= recursiveCParParal2 circus_action_int_choice (do {optnls;
															tok L_LPAR;
															optnls;
															csex <- circuscsexpr;
															optnls;
															tok L_RPAR;
															return csex})
-- | Action \intchoice Action
circus_action_int_choice :: EParser ZToken CAction
circus_action_int_choice
	= chainl1 circus_action_ext_choice (do {optnls;
											tok L_INTCHOICE;
											optnls;
											return CSPIntChoice})

-- | Action \extchoice Action
circus_action_ext_choice :: EParser ZToken CAction
circus_action_ext_choice
	= chainl1 circus_action_guard (do {optnls;
										tok L_EXTCHOICE;
										optnls;
										return CSPExtChoice})

-- | Pred \circguard Action
circus_action_guard :: EParser ZToken CAction
circus_action_guard
	= do {tok L_LCIRCGUARD;
			optnls;
			zp <- zpredicate;
			optnls;
			tok L_RCIRCGUARD;
			optnls;
			tok L_CIRCGUARD;
			optnls;
			cag <- circus_action_guard;
			return (CSPGuard zp cag)}
			+++ circus_action_comm

-- Comm \then Action
circus_action_comm :: EParser ZToken CAction
circus_action_comm
	= do {cc <- circus_comm;
			optnls;
			tok L_CTHEN;
			optnls;
			cac <- circus_action_comm;
			return (CSPCommAction cc cac)}
			+++ circus_action_seq
-- | Action \circseq Action
circus_action_seq :: EParser ZToken CAction
circus_action_seq
	= chainl1 circus_action_u (do {optnls;
									tok L_CIRCSEQ;
									optnls;
									return CSPSeq})

--  \Skip | \Stop | \Chaos | Comm \then Action
-- | Action \circhide CSExp
-- | ParAction(Exp^{+)
-- | \circmu N \circspot Action

circus_action_u :: EParser ZToken CAction
circus_action_u
	=
	-- On-the-fly parameterised action/command call
	-- TODO: put par_action instead of just a name
	-- 		SHOULD BE:  CSPParAction ParAction [ZExpr]
	-- 		NOW IT IS:	CSPParAction ZName [ZExpr]
	-- | ParAction(Exp^{+)
	do {pa <- zword;
			optnls;
			tok L_OPENPAREN;
			optnls;
			ze <- zexpressions;
			optnls;
			tok L_CLOSEPAREN;
			return (CSPParAction pa ze)}
	-- unamed param action (x : T \circspot A(x))(e)
	+++ do {tok L_OPENPAREN;
			decls <- zbasic_decl;
	  		optnls;
	  		tok L_CIRCSPOT;
	 		optnls;
			ze <- circus_action;
			optnls;
			tok L_CLOSEPAREN;
			tok L_OPENPAREN;
			zw <- zword;
			tok L_CLOSEPAREN;
			return (CSPUnParAction decls ze zw)}
	--  CSPRenAction ZName [CReplace]
	+++ do {cc <- zword;
			cac <- creplace;
			return (CSPRenAction cc cac)}
	-- Action name
	+++ do {nm <- zword; return (CActionName nm)}
	-- \Skip
	+++ do {tok L_SKIP; return CSPSkip}
	-- \Stop
	+++ do {tok L_STOP; return CSPStop}
	-- \Chaos
	+++ do {tok L_CHAOS; return CSPChaos}
	-- Command
	+++ do {nm <- circus_command; return (CActionCommand nm)}
	-- \lschexpract S \rschexpract
	+++ do {tok L_LSCHEXPRACT;
			optnls;
			ca <- zschema_exp;
			optnls;
			tok L_RSCHEXPRACT;
			return (CActionSchemaExpr ca)}
	-- (Action)
	+++ do {tok L_OPENPAREN;
			optnls;
			ca <- circus_action;
			optnls;
			tok L_CLOSEPAREN;
			return ca}
	-- On-the-fly parameterised mu action call
	-- \circmu N \circspot Action
	+++ do {tok L_CIRCMU;
			optnls;
			cc <- zword;
			optnls;
			tok L_CIRCSPOT;
			optnls;
			cac <- circus_action;
			return (CSPRecursion cc cac)}
	-- | Action \circhide CSExp
	+++ circus_action_hide

-- | Action \circhide CSExp
circus_action_hide :: EParser ZToken CAction
circus_action_hide
	= do {tok L_OPENPAREN; optnls;
			cp1 <- circus_action;
			optnls;
			tok L_CIRCHIDE;
			csex <- circuscsexpr;
			optnls;
			tok L_CLOSEPAREN;
			return (CSPHide cp1 csex)}

--Comm 		::= N CParameter* | N [Exp^{+}] CParameter*
circus_comm :: EParser ZToken Comm
circus_comm
	--  N CParameter*
	= do {zn <- zword;
	  		optnls;
			cpx <- many circus_comm_params;
	  		return (ChanComm zn (concat cpx))}
	-- N [Exp^{+}] CParameter *
	+++ do {zn <- zword;
	  		tok L_OPENBRACKET;
	  		zxpr <- zexpressions;
	  		tok L_CLOSEBRACKET;
			cpx <- opt [] circus_comm_params;
	  		return (ChanGenComm zn zxpr cpx)}

-- CParameter* -- list of parameters
circus_comm_params :: EParser ZToken [CParameter]
circus_comm_params
  = do  {e <- circus_comm_param;
  		el <- many (do {e1 <- circus_comm_param;
  						return e1});
	 return (e : el)}

--CParameter	::= ?N | ?N : Pred | !Exp | .Exp
circus_comm_param :: EParser ZToken CParameter
circus_comm_param
	= circus_comm_param_dot_exp +++ -- .Exp
		circus_comm_param_input_pred +++ -- ?N : Pred
		circus_comm_param_input +++ -- ?N
		circus_comm_param_output_exp -- !Exp


 -- ?N
circus_comm_param_input :: EParser ZToken CParameter
circus_comm_param_input
	= do {tok L_CINPUT;
	  		zn <- zword;
			return (ChanInp zn)}

-- ?N : Pred
circus_comm_param_input_pred :: EParser ZToken CParameter
circus_comm_param_input_pred
	= do {tok L_CINPUT;
	  		zn <- zword;
			optnls;
			tok L_COLON;
			optnls;
	  		p <- zexpression;
			return (ChanInpPred zn p)}

-- !Exp
circus_comm_param_output_exp:: EParser ZToken CParameter
circus_comm_param_output_exp
	= do {tok L_COUTPUT;
	  		p <- zexpression;
			return (ChanOutExp p)}

-- .Exp
circus_comm_param_dot_exp :: EParser ZToken CParameter
circus_comm_param_dot_exp
	= do {tok L_POINT;
	  		p <- zexpression;
			return (ChanDotExp p)}

--Command 	::= N^{+} := Exp^{+}
-- | \circif GActions \cirfi
-- | \circvar Decl \circspot Action
-- | N^{+} :[Pred,Pred]
-- | \{Pred\}
-- | [Pred]
-- | \circval Decl \circspot Action
-- | \circres Decl \circspot Action
-- | \circvres Decl \circspot Action
circus_command :: EParser ZToken CCommand
circus_command
	= circus_command_vres
	+++ circus_command_res
	+++ circus_command_val
	+++ circus_command_var
	+++ circus_command_assign
	+++	circus_command_prefix
	+++	circus_command_bracket
	+++	circus_command_brace
	+++ circus_command_assumption
	+++ circus_command_if

circus_command_vres :: EParser ZToken CCommand
circus_command_vres
	= do {tok L_CIRCVRES;
			decls <- zdecl_part;
	  		optnls;
	  		tok L_CIRCSPOT ;
			cut;
			optnls;
	  		prc <- circus_action;
			return (CVResDecl (concat decls) prc)}

circus_command_res :: EParser ZToken CCommand
circus_command_res
	= do {tok L_CIRCRES;
			decls <- zdecl_part;
	  		optnls;
	  		tok L_CIRCSPOT ;
			cut;
			optnls;
	  		prc <- circus_action;
			return (CResDecl (concat decls) prc)}

circus_command_val :: EParser ZToken CCommand
circus_command_val
	= do {tok L_CIRCVAL;
			decls <- zdecl_part;
	  		optnls;
	  		tok L_CIRCSPOT ;
			cut;
			optnls;
	  		prc <- circus_action;
			return (CValDecl (concat decls) prc)}

circus_command_var :: EParser ZToken CCommand
circus_command_var
	= do {tok L_CIRCVAR;
			decls <- zdecl_part;
	  		optnls;
	  		tok L_CIRCSPOT ;
			cut;
			optnls;
	  		prc <- circus_action;
			return (CValDecl (concat decls) prc)}
circus_command_bracket :: EParser ZToken CCommand
circus_command_bracket
	= do {tok L_OPENBRACKET;
			decls <- zpredicate;
	  		tok L_CLOSEBRACKET ;
			return (CommandBracket decls)}

circus_command_brace :: EParser ZToken CCommand
circus_command_brace
	= do {tok L_OPENBRACE;
			decls <- zpredicate;
	  		tok L_CLOSEBRACE ;
			return (CommandBrace decls)}

circus_command_assumption :: EParser ZToken CCommand
circus_command_assumption
	= do {ws <- zword `sepby1` comma;
	  		optnls;
			tok L_COLON;
	  		optnls;
	  		tok L_OPENBRACKET;
	  		optnls;
			pred1 <- zpredicate;
	  		optnls;
	  		tok L_COMMA;
	  		optnls;
			pred2 <- zpredicate;
	  		optnls;
	  		tok L_CLOSEBRACKET;
			return (CAssumpt ws pred1 pred2)}
circus_command_prefix :: EParser ZToken CCommand
circus_command_prefix
	= do {tok L_COLON;
	  		optnls;
	  		tok L_OPENBRACKET;
	  		optnls;
			pred1 <- zpredicate;
	  		optnls;
	  		tok L_COMMA;
	  		optnls;
			pred2 <- zpredicate;
	  		optnls;
	  		tok L_CLOSEBRACKET;
			return (CPrefix pred1 pred2)}
--  N^{+} := Exp^{+}
circus_command_assign :: EParser ZToken CCommand
circus_command_assign
	= do {tok L_OPENPAREN; optnls;
			ws <- sepbycomma1 zword;
			optnls;
			tok L_ASSIGN;
			optnls;
			zxprs <- sepbycomma zexpression;
			optnls;
			tok L_CLOSEPAREN;
			return (CAssign ws zxprs)}

sepbycomma p
	= do {e <- p;
			el <- many (do {comma;
							e1 <- p;
							return e1});
			return (e : el)}
sepbycomma1 p
	= do {e <- p;
			el <- many (do {comma;
							e1 <- p;
							return (make_zvar e1 [])});
			return ((make_zvar e []) : el)}

circus_command_if :: EParser ZToken CCommand
circus_command_if
	= do {tok L_CIRCIF;
			optnls;
			gc <- circus_guarded_commands;
			optnls;
	  		tok L_CIRCFI;
			return (CIf gc)}

--CGActions 	::= Pred \circthen Action
-- 				| Pred \circthen Action \circelse CGActions
circus_guarded_commands :: EParser ZToken CGActions
circus_guarded_commands
	= do {tok L_CIRCELSE;
			optnls;
	  		cgc <- par_action;
	  		return (CircElse cgc)}
	  +++ do {gcs <- circus_guarded_command;
			optnls;
			tok L_CIRCELSE;
			optnls;
	  		cgc <- circus_guarded_commands;
	  		return (CircThenElse gcs cgc)}
	  +++ circus_guarded_command

circus_guarded_command :: EParser ZToken CGActions
circus_guarded_command
	= do {decls <- zpredicate; optnls;
	  		tok L_CIRCTHEN; optnls;
	  		prc <- circus_action;
	  		return (CircGAction decls prc)}

creplace :: EParser ZToken [CReplace]
creplace
  = do  {tok L_OPENBRACKET;
	 reps <- crename `sepby1` comma;
	 tok L_CLOSEBRACKET;
	 return reps}

crename :: EParser ZToken CReplace
crename
  = do  {dn1 <- zdecl_name;
	 tok L_SLASH;
	 dn2 <- zdecl_name;
	 return (CRename dn2 dn1)}
\end{code}
