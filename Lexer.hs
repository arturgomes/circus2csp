module Lexer
--
-- Lexical scanner for LaTeX Z specifications.
--
-- zlex is the main entry point.  It is normally called like this:
--
--      zlex lexstate0 "input string ..."
--
-- The scanner handles operator declarations itself, and keeps
-- a record of what operators have been declared.
--
-- To speed up processing, simplify the parser and avoid starting
-- Z paragraphs within informal commentary, the scanner handles
-- commentary separately from the contents of Z paragraphs.
--
-- TODO: provide a way of saving/returning the lexer state,
--       because it contains declared operators etc.
-- TODO: implement %%cmd commands (to record declared operators).
--
where
import EParseLib
import Data.Char

data ZToken
  -- These first few pairs of tokens cause the lexer to start/stop
  -- returning tokens.  They should all appear at the beginning of a line.
  -- LIMITATION: spaces are not allowed within these commands yet.
  = L_BEGIN_ZED            -- '\begin{zed}'  or '\begin{syntax}'
  | L_END_ZED              -- '\end{zed}'    or '\end{syntax}'
  | L_BEGIN_AXDEF          -- '\begin{axdef}'
  | L_END_AXDEF            -- '\end{axdef}'
  | L_BEGIN_SCHEMA         -- '\begin{schema}'
  | L_END_SCHEMA           -- '\end{schema}'
  | L_BEGIN_GENDEF         -- '\begin{gendef}'
  | L_END_GENDEF           -- '\end{gendef}'
  | L_BEGIN_MACHINE        -- '\begin{machine}'    (a Jaza extension)
  | L_END_MACHINE          -- '\end{machine}'
  -- Circus paragraphs - begin
  | L_BEGIN_CIRCUS         -- '\begin{circus}'
  | L_END_CIRCUS           -- '\end{circus}'
  | L_BEGIN_CIRCUSACTION   -- '\begin{circusaction}'
  | L_END_CIRCUSACTION     -- '\end{circusaction}'


  -- Begin Circus Tokens
  | L_REPEXTCHOICE
  | L_REPINTCHOICE
  | L_REPINTERLEAVE
  | L_REPSEMI
  | L_CHAOS
  | L_CIRCUSBEGIN
  | L_CIRCUSEND
  | L_CIRCASSIGNM
  | L_CIRCCHANSET
  | L_CIRCDEF
  | L_CIRCELSE
  | L_CIRCGUARD
  | L_CIRCCHANNEL
  | L_CIRCHIDE
  | L_CIRCIF
  | L_CIRCINDEX
  | L_CIRCMU
  | L_CIRCNAMESET
  | L_CIRCPROCESS
  | L_CIRCRES
  | L_CIRCSEMI
  | L_CIRCSEQ
  | L_CIRCSPOT
  | L_CIRCSTATE
  | L_CIRCTHEN
  | L_CIRCVAL
  | L_CIRCVAR
  | L_CIRCVRES
  | L_CIRCFI
  | L_LCIRCGUARD
  | L_RCIRCGUARD
  | L_EXCLMRK
  | L_EXTCHOICE
  | L_INTCHOICE
  | L_INTERLEAVE
  | L_INTERSECT
  | L_LCHANSET
  | L_LCIRCINDEX
  | L_LCURLYBR
  | L_LSCHEXPRACT
  | L_RSCHEXPRACT
  | L_LINTER
  | L_LPAR
  | L_PERIOD
  | L_QSTNMRK
  | L_RCHANSET
  | L_RCIRCINDEX
  | L_RCURLYBR
  | L_RINTER
  | L_RPAR
  | L_SKIP
  | L_STOP
  | L_CTHEN
  | L_UNION
  -- end Circus Tokens

  -- Now some common keywords and separators.
  | L_WHERE                -- '\where'
  | L_LET                  -- '\LET'
  | L_IF                   -- '\IF'
  | L_THEN                 -- '\THEN'
  | L_ELSE                 -- '\ELSE'
  | L_DELTA                -- '\Delta'
  | L_XI                   -- '\Xi'
  | L_LAMBDA               -- '\lambda'
  | L_MU                   -- '\mu'
  | L_THETA                -- '\theta'
  | L_DEFS                 -- '\defs'
  | L_CROSS                -- '\cross'
  | L_POWER                -- '\power'
  | L_COLON_COLON_EQUALS   -- '::='
  | L_ASSIGN               -- ':='
  | L_COLON                -- ':'
  | L_SEMICOLON            -- ';'
  | L_COMMA                -- ','
  | L_VERT                 -- '|'
  | L_AT                   -- '@'
  | L_POINT                -- '.'
  | L_SLASH                -- '/'  (used in renamings, and division!)
  | L_HYPHEN               -- '-'
  | L_UNDERSCORE           -- '_'   (used in decls:  _ f _ : Type)
  | L_EQUALS_EQUALS        -- '=='
  | L_BACKSLASH_BACKSLASH  -- '\\'
  | L_ALSO                 -- '\also'
  | L_LDATA                -- '\ldata'
  | L_RDATA                -- '\rdata'
  | L_OPENBRACE            -- '{'
  | L_CLOSEBRACE           -- '}'
  | L_OPENSET              -- '\{'
  | L_CLOSESET             -- '\}'
  | L_OPENPAREN            -- '('
  | L_CLOSEPAREN           -- ')'
  | L_OPENBRACKET          -- '['
  | L_CLOSEBRACKET         -- ']'
  | L_LIMG                 -- '\limg'
  | L_RIMG                 -- '\rimg'
  | L_BSUP                 -- '\bsup'  (these begin/end a superscript expr.)
  | L_ESUP                 -- '\esup'
  | L_LANGLE               -- '\langle' (these begin/end a literal sequence)
  | L_RANGLE               -- '\rangle'
  | L_LBLOT                -- '\lblot'  (these begin/end a literal binding)
  | L_RBLOT                -- '\rblot'

  -- schema operators and logical operators are overloaded.
  | L_FORALL               -- '\forall'
  | L_EXISTS               -- '\exists'
  | L_EXISTS_1             -- '\exists_1'
  | L_IMPLIES              -- '\implies'
  | L_LAND                 -- '\land'
  | L_LOR                  -- '\lor'
  | L_IFF                  -- '\iff'
  | L_PROJECT              -- '\project'
  | L_HIDE                 -- '\hide'
  | L_SEMI                 -- '\semi'
  | L_PIPE                 -- '\pipe'
  | L_LNOT                 -- '\lnot'
  | L_PRE                  -- '\pre'
  | L_TRUE                 -- 'true'
  | L_FALSE                -- 'false'

  -- relations
  | L_EQUALS               -- '='
  | L_IN                   -- '\in'
  | L_NEQ                  -- '\neq'
  | L_NOTIN                -- '\notin'
  | L_INREL                -- '\inrel'  (used in '\inrel{name}')

  --missing from the ISO Standard Z -
  | L_GENERIC
  | L_RELATION
  | L_LEFTASSOC
  | L_RIGHTASSOC
  | L_EMPTY_SET
  | L_SYMDIFF
  | L_BIG_CUP
  | L_BIG_CAP
  | L_DOM
  | L_RAN
  | L_NUM
  | L_ARITHMOS
  | L_VDASH
  | L_FUNCTION
  -- terminals that carry information with them.
  | L_WORD String          -- used for identifiers, schema names etc.
  | L_GIVENVAL String      -- strings are elements of given sets.
  | L_IN_FUN Int String    -- used for infix operators priority 1-6
  | L_IN_REL String
  | L_IN_GEN String
  | L_PRE_REL String
  | L_PRE_GEN String
  | L_POST_FUN String
  | L_NUMBER Integer
  | L_STROKE String        -- a decoration: ''', '!', '?' or '_N'
  | L_ERROR String         -- an unrecognised char/word/token
  deriving (Read,Show,Eq)



-- The scanner has this internal state which records line numbers,
-- declared operators etc.  (The current column number is handled via
-- an explicit argument to zlex, because it changes so often, and
-- experiments show that the scanner is faster that way).

data LexState = LexState{line::Int, opstrs::[String]}

incrline :: LexState -> LexState
incrline ls = ls{line = line ls + 1}

lexstate0 :: LexState
lexstate0 = LexState{line=1, opstrs=[]}


--   zlexc handles the 'commentary' part of Z specifications
--     It skips everything, looking only for constructs at the beginning
--     of a line that start a Z paragraph (like \begin{schema}).
--
--   zlexz is used within each Z paragraph, to generate the Z tokens.
--
-- zlexz takes a column number as argument (and lexer state and input string).
-- Columns are numbered from zero, whereas lines are numbered from one.
-- This numbering scheme matches Emacs conventions.

zlex :: LexState -> String -> [Token ZToken]
zlex = zlexc

zlexc :: LexState -> String -> [Token ZToken]
zlexc ls ""
  = []
zlexc ls ('%':'%':c:s)
  | isAlpha c = lexdirective ls (c:s)
  | otherwise = zskipline ls (c:s)
zlexc ls s
  | cmd == begin
    && head s4 == '}'
    = lexcmd envname
  | otherwise
    -- it must still be commentary, so skip the whole line!
    = zskipline ls s
  where
  begin = "\\begin{"
  spacetab ' '  = True
  spacetab '\t' = True
  spacetab _    = False
  (spaces,s2) = span spacetab s
  (cmd,s3) = splitAt (length begin) s2
  (envname,s4) = span isAlpha s3
  pos = length spaces
  rest = zlexz (pos + length begin + length envname + 1) ls (tail s4)
  lexcmd "zed"    = Token L_BEGIN_ZED (line ls) pos : rest
  lexcmd "syntax" = Token L_BEGIN_ZED (line ls) pos : rest
  lexcmd "axdef"  = Token L_BEGIN_AXDEF (line ls) pos : rest
  lexcmd "schema" = Token L_BEGIN_SCHEMA (line ls) pos : rest
  lexcmd "gendef" = Token L_BEGIN_GENDEF (line ls) pos : rest
  lexcmd "machine"= Token L_BEGIN_MACHINE (line ls) pos : rest
  lexcmd "circus"= Token L_BEGIN_CIRCUS (line ls) pos : rest
  lexcmd "circusaction"= Token L_BEGIN_CIRCUSACTION (line ls) pos : rest
  lexcmd _ = zskipline ls s

directivetable
  = ["inop","postop","inrel","prerel","ingen","pregen","ignore"]

lexdirective ls s
  | directive `elem` directivetable
      = error "%%...  operator declarations not implemented yet!"
  | otherwise
      -- Ignore all unknown directives (silently!)
      -- Note: this is currently ignoring the 'type', 'tame' and
      --       'unchecked' directives.
      = zskipline ls rest
  where
  (directive, rest) = span isAlpha s


zskipline ls s
  = zlexc (incrline ls) (drop 1 (dropWhile (/= '\n') s))


zlexz :: Int -> LexState -> String -> [Token ZToken]
zlexz c ls ""       = []
-- various forms of whitespace
zlexz c ls (' ':s)  = zlexz (c+1) ls s
zlexz c ls ('~':s)  = zlexz (c+1) ls s
zlexz c ls ('&':s)  = zlexz (c+1) ls s   -- ignore Latex tabs
zlexz c ls ('\r':s) = zlexz (c+1) ls s   -- so that DOS files work
zlexz c ls ('\t':s) = zlexz ((c `div` 8 + 1)*8) ls s
zlexz c ls ('\n':s) = zlexz 0 (incrline ls) s  -- newline
zlexz c ls ('\f':s) = zlexz 0 (incrline ls) s  -- formfeed
zlexz c ls ('\v':s) = zlexz 0 (incrline ls) s  -- vertical tab
zlexz c ls ('%':s)  = zlexz 0 (incrline ls) (drop 1 (dropWhile (/= '\n') s))
zlexz c ls ('\\':'!':s) = zlexz (c+2) ls s
zlexz c ls ('\\':',':s) = zlexz (c+2) ls s
zlexz c ls ('\\':':':s) = zlexz (c+2) ls s
zlexz c ls ('\\':';':s) = zlexz (c+2) ls s
zlexz c ls ('\\':' ':s) = zlexz (c+2) ls s
zlexz c ls ('\\':'t':'1':s) = zlexz (c+3) ls s -- Artur : producing \t1, \t2, \t3, \t4
zlexz c ls ('\\':'t':'2':s) = zlexz (c+3) ls s
zlexz c ls ('\\':'t':'3':s) = zlexz (c+3) ls s
zlexz c ls ('\\':'t':'4':s) = zlexz (c+3) ls s
-- LaTeX commands that start with a backslash
zlexz c ls ('\\':'\\':s)
  = Token L_BACKSLASH_BACKSLASH (line ls) c : zlexz (c+2) ls s
zlexz c ls ('\\':'_':s)
  = Token L_UNDERSCORE (line ls) c : zlexz (c+2) ls s
zlexz c ls ('\\':'{':s)
  = Token L_OPENSET (line ls) c : zlexz (c+2) ls s
zlexz c ls ('\\':'}':s)
  = Token L_CLOSESET (line ls) c : zlexz (c+2) ls s
zlexz c ls ('\\':'#':s)
  = Token (L_WORD "\\#") (line ls) c : zlexz (c+2) ls s
zlexz c ls ('\\':s)
  -- A few commands can have a "_1" after them, which changes their meaning.
  -- For these commands, we call tok_1, to discard the "_1".
  -- Occurences of "_1" that are not recognised here are treated as
  -- normal decorations.  Perhaps *all* "_1" should be treated as decorations,
  -- but that is difficult at the moment, because the ones handled below
  -- generate a variety of lexical symbols.  This might become easier after
  -- operator declarations are implemented?
  | cmd=="t" && length (takeWhile isDigit s2) == 1
      = zlexz (c+3) ls (tail s2)   -- ignore \tN tabs commands
  -- A.2.4.1 Greek Alphabet Characters
  | cmd=="Delta"  = tok L_DELTA
  | cmd=="Xi"     = tok L_XI
  | cmd=="theta"  = tok L_THETA
  | cmd=="lambda" = tok L_LAMBDA
  | cmd=="mu"     = tok L_MU
  -- A.2.4.2 Other letter characters
  | cmd=="arithmos"=tok L_ARITHMOS
  | cmd=="nat"    = tok L_CIRCNAMESET
  | cmd=="power" && underscore1
      = tok_1 (L_PRE_GEN ("\\power_1"))
  | cmd=="power"  = tok L_POWER -- must come after \power_1.
  -- A.2.4.3 Special characters
  | cmd=="ldata"  = tok L_LDATA
  | cmd=="rdata"  = tok L_RDATA
  | cmd=="lblot"  = tok L_LBLOT
  | cmd=="rblot"  = tok L_RBLOT
  -- A.2.4.4 Symbol Characters (except mathematical toolkit characters)
  | cmd=="vdash"   = tok L_VDASH
  | cmd=="land"   = tok L_LAND
  | cmd=="lor"    = tok L_LOR
  | cmd=="implies"= tok L_IMPLIES
  | cmd=="iff"    = tok L_IFF
  | cmd=="lnot"   = tok L_LNOT
  | cmd=="forall" = tok L_FORALL
  | cmd=="exists" && underscore1 = tok_1 L_EXISTS_1
  | cmd=="exists" = tok L_EXISTS       -- must come after \exists_1.
  | cmd=="cross"  = tok L_CROSS
  | cmd=="in"     = tok L_IN
  | cmd=="hide"   = tok L_HIDE
  | cmd=="project"= tok L_PROJECT
  | cmd=="semi"   = tok L_SEMI
  | cmd=="pipe"   = tok L_PIPE
-- A.2.4.5 Core Words
  | cmd=="IF"     = tok L_IF
  | cmd=="THEN"   = tok L_THEN
  | cmd=="ELSE"   = tok L_ELSE
  | cmd=="LET"    = tok L_LET
  | cmd=="pre"    = tok L_PRE
  | cmd=="function"   = tok L_FUNCTION
  | cmd=="generic"    = tok L_GENERIC
  | cmd=="relation"   = tok L_RELATION
  | cmd=="leftassoc"  = tok L_LEFTASSOC
  | cmd=="rightassoc" = tok L_RIGHTASSOC
  -- A.2.5 Mathematical toolkit characters and words
  -- A.2.5.1 Section set_toolkit
  | cmd=="rel"    = tok (L_IN_GEN ('\\':cmd))
  | cmd=="fun"    = tok (L_IN_GEN ('\\':cmd))
  | cmd=="neq"    = tok L_NEQ
  | cmd=="notin"  = tok L_NOTIN
  | cmd=="emptyset"= tok L_EMPTY_SET
  | cmd=="subset" = tok (L_IN_REL ('\\':cmd))
  | cmd=="subseteq"= tok (L_IN_REL ('\\':cmd))
  | cmd=="cap"    = tok (L_IN_FUN 4 ('\\':cmd))
  | cmd=="cup"    = tok (L_IN_FUN 3 ('\\':cmd))
  | cmd=="setminus"= tok (L_IN_FUN 3 ('\\':cmd))
  | cmd=="symdiff"= tok L_SYMDIFF
  | cmd=="bigcup"= tok L_BIG_CUP
  | cmd=="bigcap"= tok L_BIG_CAP
  | cmd=="finset" && underscore1
      = tok_1 (L_PRE_GEN ("\\finset_1"))
  | cmd=="finset" = tok (L_PRE_GEN ("\\finset"))  -- must come after \finset_1
  -- A.2.5.2 Section set_toolkit
  | cmd=="mapsto" = tok (L_IN_FUN 1 ('\\':cmd))
  | cmd=="id"     = tok (L_PRE_GEN ('\\':cmd))
  | cmd=="comp"   = tok (L_IN_FUN 4 ('\\':cmd))
  | cmd=="circ"   = tok (L_IN_FUN 4 ('\\':cmd))
  | cmd=="dres"   = tok (L_IN_FUN 6 ('\\':cmd))
  | cmd=="rres"   = tok (L_IN_FUN 6 ('\\':cmd))
  | cmd=="ndres"  = tok (L_IN_FUN 6 ('\\':cmd))
  | cmd=="nrres"  = tok (L_IN_FUN 6 ('\\':cmd))
  | cmd=="inv"    = tok (L_POST_FUN ('\\':cmd))
  | cmd=="limg"   = tok L_LIMG
  | cmd=="rimg"   = tok L_RIMG
  | cmd=="oplus"  = tok (L_IN_FUN 5 ('\\':cmd))
  | cmd=="plus"   = tok (L_POST_FUN ('\\':cmd))
  | cmd=="star"   = tok (L_POST_FUN ('\\':cmd))
  -- A.2.5.3 Section function_toolkit
  | cmd=="pfun"   = tok (L_IN_GEN ('\\':cmd))
  | cmd=="pinj"   = tok (L_IN_GEN ('\\':cmd))
  | cmd=="inj"    = tok (L_IN_GEN ('\\':cmd))
  | cmd=="psurj"  = tok (L_IN_GEN ('\\':cmd))
  | cmd=="surj"   = tok (L_IN_GEN ('\\':cmd))
  | cmd=="bij"    = tok (L_IN_GEN ('\\':cmd))
  | cmd=="ffun"   = tok (L_IN_GEN ('\\':cmd))
  | cmd=="finj"   = tok (L_IN_GEN ('\\':cmd))
  | cmd=="disjoint"= tok (L_PRE_REL ('\\':cmd))
  | cmd=="partition"= tok (L_IN_REL ('\\':cmd))
  -- A.2.5.3 Section number_toolkit
  | cmd=="geq"    = tok (L_IN_REL ('\\':cmd))
  | cmd=="leq"    = tok (L_IN_REL ('\\':cmd))
  | cmd=="mod"    = tok (L_IN_FUN 4 ('\\':cmd))
  | cmd=="div"    = tok (L_IN_FUN 4 ('\\':cmd))
  | cmd=="num"    = tok L_NUM
  -- Need the \negate -> ~, but different from '~' space
  -- A.2.5.4 Section sequence_toolkit
  | cmd=="upto"   = tok (L_IN_FUN 2 ('\\':cmd))
  | cmd=="seq" && underscore1
      = tok_1 (L_PRE_GEN ("\\seq_1")) -- must come after \seq_1.
  | cmd=="seq"    = tok (L_PRE_GEN ("\\seq"))
  | cmd=="iseq"   = tok (L_PRE_GEN ('\\':cmd))
  | cmd=="langle" = tok L_LANGLE
  | cmd=="rangle" = tok L_RANGLE
  | cmd=="cat"    = tok (L_IN_FUN 3 ('\\':cmd))
  | cmd=="extract"= tok (L_IN_FUN 4 ('\\':cmd))
  | cmd=="filter" = tok (L_IN_FUN 4 ('\\':cmd))
  | cmd=="prefix" = tok (L_IN_REL ('\\':cmd))
  | cmd=="suffix" = tok (L_IN_REL ('\\':cmd))
  | cmd=="infix"  = tok (L_IN_REL ('\\':cmd))
  | cmd=="dcat"    = tok (L_IN_FUN 3 ('\\':cmd)) --need to double check (Artur)
  -- Other definitions
  | cmd=="also"   = tok L_ALSO
  | cmd=="bsup"   = tok L_BSUP
  | cmd=="defs"   = tok L_DEFS
  | cmd=="esup"   = tok L_ESUP
  | cmd=="inrel"  = tok L_INREL
  | cmd=="mid"    = tok L_VERT   -- a synonym for |
  | cmd=="spot"   = tok L_AT     -- a synonym for @
  | cmd=="where"  = tok L_WHERE
    -- The next block of tokens follows the tables of
    -- operators on page 46 of "The Z Notation", Spivey (Edition 2).
  | cmd=="inseq"  = tok (L_IN_REL ('\\':cmd))
  -- Circus Commands
  | cmd=="Chaos"                = tok L_CHAOS
  | cmd=="circbegin"            = tok L_CIRCUSBEGIN
  | cmd=="circend"              = tok L_CIRCUSEND
  | cmd=="circchannelset"       = tok L_CIRCCHANSET
  | cmd=="circdef"              = tok L_CIRCDEF
  | cmd=="circelse"             = tok L_CIRCELSE
  | cmd=="circguard"            = tok L_CIRCGUARD
  | cmd=="circchannel"          = tok L_CIRCCHANNEL
  | cmd=="circhide"             = tok L_CIRCHIDE
  | cmd=="circif"               = tok L_CIRCIF
  | cmd=="circindex"            = tok L_CIRCINDEX
  | cmd=="circmu"               = tok L_CIRCMU
  | cmd=="circnameset"          = tok L_CIRCNAMESET
  | cmd=="circprocess"          = tok L_CIRCPROCESS
  | cmd=="circres"              = tok L_CIRCRES
  | cmd=="circseq"              = tok L_CIRCSEQ
  | cmd=="circspot"             = tok L_CIRCSPOT
  | cmd=="circstate"            = tok L_CIRCSTATE
  | cmd=="circthen"             = tok L_CIRCTHEN
  | cmd=="circval"              = tok L_CIRCVAL
  | cmd=="circvar"              = tok L_CIRCVAR
  | cmd=="circvres"             = tok L_CIRCVRES
  | cmd=="circfi"               = tok L_CIRCFI
  | cmd=="Extchoice"            = tok L_REPEXTCHOICE
  | cmd=="extchoice"            = tok L_EXTCHOICE
  | cmd=="IntChoice"            = tok L_REPINTCHOICE
  | cmd=="intchoice"            = tok L_INTCHOICE
  | cmd=="Interleave"           = tok L_REPINTERLEAVE
  | cmd=="interleave"           = tok L_INTERLEAVE
  | cmd=="intersect"            = tok L_INTERSECT
  | cmd=="lchanset"             = tok L_LCHANSET
  | cmd=="lcircindex"           = tok L_LCIRCINDEX
  | cmd=="linter"               = tok L_LINTER
  | cmd=="lpar"                 = tok L_LPAR
  | cmd=="rchanset"             = tok L_RCHANSET
  | cmd=="rcircindex"           = tok L_RCIRCINDEX
  | cmd=="rinter"               = tok L_RINTER
  | cmd=="rpar"                 = tok L_RPAR
  | cmd=="Semi"                 = tok L_REPSEMI
  | cmd=="Skip"                 = tok L_SKIP
  | cmd=="Stop"                 = tok L_STOP
  | cmd=="then"                 = tok L_CTHEN
  | cmd=="union"                = tok L_UNION
  | cmd=="lcircguard"           = tok L_LCIRCGUARD
  | cmd=="rcircguard"           = tok L_RCIRCGUARD
  | cmd=="lschexpract"          = tok L_LSCHEXPRACT
  | cmd=="rschexpract"          = tok L_RSCHEXPRACT
  -- end Circus Commands
  | cmd=="end" && arg=="{zed}"          = tokarg L_END_ZED
  | cmd=="end" && arg=="{syntax}"       = tokarg L_END_ZED
  | cmd=="end" && arg=="{axdef}"        = tokarg L_END_AXDEF
  | cmd=="end" && arg=="{schema}"       = tokarg L_END_SCHEMA
  | cmd=="end" && arg=="{gendef}"       = tokarg L_END_GENDEF
  | cmd=="end" && arg=="{machine}"      = tokarg L_END_MACHINE
  -- Circus paragraphs - end
  | cmd=="end" && arg=="{circus}"       = tokarg L_END_CIRCUS
  | cmd=="end" && arg=="{circusaction}" = tokarg L_END_CIRCUSACTION

  -- treat \\nat_1 specially, so the _1 is not a decoration.
  | cmd=="nat" && underscore1     = tok_1 (L_WORD "\\nat_1")
  | otherwise                     = tok (L_WORD ('\\':cmd))
  where
  (cmd,s2) = span isAlpha s
  arg      = takeWhile isArgChar s2
  tok t    = Token t (line ls) c : zlexz (c + 1 + length cmd) ls s2
  tok_1 t  = Token t (line ls) c : zlexz (c + 3 + length cmd) ls (drop 2 s2)
  tokarg t = Token t (line ls) c : zskipline ls s2  -- skip rest of line
  underscore1 = starts_with_underscore1 s2
  starts_with_underscore1 ('_':'1':[])  = True
  starts_with_underscore1 ('_':'1':c:_) = not (isDigit c)
  starts_with_underscore1 _             = False
zlexz c ls s@('+':_) = zlexinfix c ls s
zlexz c ls s@('-':_) = zlexinfix c ls s
zlexz c ls s@('*':_) = zlexinfix c ls s
zlexz c ls s@('.':_) = zlexinfix c ls s
zlexz c ls s@('=':_) = zlexinfix c ls s
zlexz c ls s@('<':_) = zlexinfix c ls s
zlexz c ls s@('>':_) = zlexinfix c ls s
zlexz c ls s@(',':_) = zlexinfix c ls s
zlexz c ls (':':':':'=':s)
       = Token L_COLON_COLON_EQUALS (line ls) c : zlexz (c+3) ls s
zlexz c ls (':':'=':s)
       = Token L_ASSIGN       (line ls) c : zlexz (c+2) ls s
zlexz c ls (':':s) = Token L_COLON        (line ls) c : zlexz (c+1) ls s
zlexz c ls (';':s) = Token L_SEMICOLON    (line ls) c : zlexz (c+1) ls s
zlexz c ls ('|':s) = Token L_VERT         (line ls) c : zlexz (c+1) ls s
zlexz c ls ('@':s) = Token L_AT           (line ls) c : zlexz (c+1) ls s
zlexz c ls ('/':s) = Token L_SLASH        (line ls) c : zlexz (c+1) ls s
zlexz c ls ('{':s) = Token L_OPENBRACE    (line ls) c : zlexz (c+1) ls s
zlexz c ls ('}':s) = Token L_CLOSEBRACE   (line ls) c : zlexz (c+1) ls s
zlexz c ls ('(':s) = Token L_OPENPAREN    (line ls) c : zlexz (c+1) ls s
zlexz c ls (')':s) = Token L_CLOSEPAREN   (line ls) c : zlexz (c+1) ls s
zlexz c ls ('[':s) = Token L_OPENBRACKET  (line ls) c : zlexz (c+1) ls s
zlexz c ls (']':s) = Token L_CLOSEBRACKET (line ls) c : zlexz (c+1) ls s
zlexz c ls ('\'':s)= Token (L_STROKE "'") (line ls) c : zlexz (c+1) ls s
zlexz c ls ('?':s) = Token (L_STROKE "?") (line ls) c : zlexz (c+1) ls s
zlexz c ls ('!':s) = Token (L_STROKE "!") (line ls) c : zlexz (c+1) ls s
zlexz c ls ('"':s)
  | take 1 rest == "\"" = Token (L_GIVENVAL val) (line ls) c : toks
  | otherwise           = Token (L_ERROR "unclosed string") (line ls) c : toks
  where
  (val,rest) = span string_contents s
  string_contents '"'  = False
  string_contents '\n' = False
  string_contents _    = True
  toks = zlexz (c + length val + 2) ls (drop 1 rest)
zlexz c ls ('_':s)
  = if num==""
    then Token (L_ERROR "_") (line ls) c : zlexz (c+1) ls s
    else Token (L_STROKE ('_':num)) (line ls) c
   : zlexz (c + 1 + length num) ls s2
  where
  (num,s2) = span isDigit s
zlexz c ls (ch:s)
  | isAlpha ch = Token (tok word) (line ls) c
     : zlexz (c + length word) ls s2
  | isDigit ch = Token (L_NUMBER (read num)) (line ls) c
     : zlexz (c + length num) ls s3
  | otherwise  = Token (L_ERROR [ch]) (line ls) c
     : zlexz (c + 1) ls s
  where
  (word,s2) = span_ident (ch:s)
  (num,s3)  = span isDigit (ch:s)
  tok "true"  = L_TRUE
  tok "false" = L_FALSE
  tok w       = L_WORD w


span_ident :: String -> (String, String)
span_ident []           = ([],[])
span_ident ('\\':'_':s) = ('\\':'_':ys,zs)
             where (ys,zs) = span_ident s
span_ident xs@(ch:s)
  | isAlphaNum ch  =  (ch:ys,zs)
  | otherwise      =  ([],xs)
          where (ys,zs) = span_ident s

zlexinfix c ls s
  | op=="="    = tok L_EQUALS
  | op=="=="   = tok L_EQUALS_EQUALS
  | op=="."    = tok L_POINT
  | op==","    = tok L_COMMA
  | op=="-"    = tok L_HYPHEN
  | op=="+"    = tok (L_IN_FUN 3 op)
  | op=="*"    = tok (L_IN_FUN 4 op)
  | op=="<"    = tok (L_IN_REL op)
  | op==">"    = tok (L_IN_REL op)
  | otherwise  = tok (L_WORD op)
  where
  (op,s2) = span isInfixChar s
  tok t = Token t (line ls) c : zlexz (c + length op) ls s2


isInfixChar :: Char -> Bool
isInfixChar '+' = True
isInfixChar '-' = True
isInfixChar '*' = True
isInfixChar '.' = True
isInfixChar '=' = True
isInfixChar '<' = True
isInfixChar '>' = True
isInfixChar ',' = True
isInfixChar  _  = False


isArgChar :: Char -> Bool
isArgChar '{' = True
isArgChar '}' = True
isArgChar c   = isAlpha c