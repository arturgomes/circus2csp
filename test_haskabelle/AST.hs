
module AST where


type GivenSet = ZVar      -- names of given sets.
type GivenValue = String  -- members of given sets are strings
type ZInt = Integer       -- If you change this, you must also change
        -- the definition of L_NUMBER in Lexer.hs
{-
\end{code}

TODO: Make this a separate module, perhaps combined with \texttt{VarSet}.

\subsubsection{Z Names and Decorations}
\begin{code}
-}
type ZDecor = String      -- a decoration: ''', '!', '?' or '_N'
type ZVar = (String, [ZDecor]) -- all kinds of Z names
type ZName = String


data ZGenFilt
  = Choose ZVar ZExpr  -- (Choose x T) means x:T
  | Check ZPred
  | Evaluate ZVar ZExpr ZExpr -- This means Let x==e | e \in t
  deriving (Eq,Ord,Show)

data ZExpr
  = ---------- Basic Z values (non-set values) ----------
    ZVar ZVar           -- for non-schema names (may include decorations)
  | ZInt ZInt           -- an integer constant
  | ZSetComp [ZGenFilt] (Maybe ZExpr) -- set comprehensions
  | ZBinding [(ZVar,ZExpr)] -- always in sorted name order (no duplicates)
  ---------- Data structures for sets ----------
  -- These are roughly ordered by how 'large' a set they typically represent.
  | ZSetDisplay [ZExpr]   -- set displays, like {1,2,4}
  | ZSeqDisplay [ZExpr]   -- sequence displays, like <1,2,4>
  | ZTuple [ZExpr]      -- (a,b,c)
  | ZCross [ZExpr]        -- a \cross b \cross c
  -- | ZFSet ZFSet           -- all elements must be in canonical form.
  ---------- Z constructs that are not necessarily sets ----------
  | ZCall ZExpr ZExpr                 -- function call:  f a
  deriving (Eq,Ord,Show)

data ZPred
  = ZFalse{reason::[ZPred]}
  | ZTrue{reason::[ZPred]}
  | ZAnd ZPred ZPred
  | ZPSchema ZSExpr             -- removed in Unfold
  deriving (Eq,Ord,Show)
data ZSExpr
  = ZSchema [ZGenFilt]
  deriving (Eq,Ord,Show)
data ZSName                     -- schema names including prefix.
  = ZSPlain String | ZSDelta String | ZSXi String
  deriving (Eq,Ord,Show)
{-
\end{code}

\subsubsection{Z Paragraphs}
\begin{code}
-}
data ZPara
  = Process ProcDecl            -- ProcDecl
  | ZSchemaDef ZSName ZSExpr     -- \begin{schema}{XXX}...\end{schema}
  deriving (Eq,Ord,Show)

type ZSpec = [ZPara]

type CProgram = [ZPara]

data CSExp
  = CSExpr ZName                           -- a chanset decl from another chanset
  | CSEmpty                                -- Empty chanset
  | CChanSet [ZName]                       -- named chanset
  | ChanSetUnion CSExp CSExp               -- chanset union
  | ChanSetInter CSExp CSExp               -- chanset intersection
  | ChanSetDiff CSExp CSExp                -- chanset hidding chanset
  deriving (Eq,Ord,Show)

{-
\end{code}

\subsubsection{Circus Process}
\begin{code}
-}
data ProcDecl
  = CProcess ZName ProcessDef              -- \circprocess N \circdef ProcDef
  | CParamProcess ZName [ZName] ProcessDef  -- \circprocess N[N^{+}] \circdef ProcDef
  | CGenProcess ZName [ZName] ProcessDef   -- \circprocess N[N^{+}] \circdef ProcDef
  deriving (Eq,Ord,Show)

data ProcessDef
  = ProcDefSpot [ZGenFilt] ProcessDef      -- Decl \circspot ProcDef
  | ProcDef CProc                          -- Proc
  deriving (Eq,Ord,Show)

data CProc
  = CHide CProc CSExp                      -- Proc \circhide CSExp
  | CExtChoice CProc CProc                 -- Proc \extchoice Proc
  | CIntChoice CProc CProc                 -- Proc \intchoice Proc
  | CParParal CSExp CProc CProc            -- Proc \lpar CSExp \rpar Proc
  | CInterleave CProc CProc                -- Proc \interleave Proc
  -- | ChanProcDecl CDecl ProcessDef [ZExpr]  -- (Decl \circspot ProcDef)(Exp^{+})
  | CGenProc ZName [ZExpr]                 -- N[Exp^{+}]
  | CParamProc ZName [ZExpr]              -- N(Exp^{+})
  -- | CIndexProc [ZGenFilt] ProcessDef    -- \(Decl \circindex ProcDef) \lcircindex Exp^{+} \rcircindex  -- TODO
  | CProcRename ZName [Comm] [Comm]        -- Proc[N^{+}:=N^{+}] -- TODO
  | CSeq CProc CProc                       -- Proc \cirCSeq Proc
  | CSimpIndexProc ZName [ZExpr]           -- N\lcircindex Exp^{+} \rcircindex
  | CircusProc ZName                       -- N
  | ProcMain ZPara [PPar] CAction          -- \circbegin PPar*
                                           --   \circstate SchemaExp PPar*
                                           --   \circspot Action
                                           --   \circend
  | ProcStalessMain [PPar] CAction         -- \circbegin PPar*
                                           --   \circspot Action
                                           --   \circend
 deriving (Eq,Ord,Show)
{-
\end{code}

\subsubsection{Circus Name-Sets}

\begin{code}
-}
data NSExp
  = NSExpEmpty                             -- \{\}
  | NSExprMult [ZName]                     -- \{N^{+}\}
  | NSExprSngl ZName                       -- N
  | NSExprParam ZName [ZExpr]              -- N(Exp)
  | NSUnion NSExp NSExp                    -- NSExp \union NSExp
  | NSIntersect NSExp NSExp                -- NSExp \intersect NSExp
  | NSHide NSExp NSExp                     -- NSExp \circhide \NSExp
  | NSBigUnion ZExpr
  deriving (Eq,Ord,Show)
{-
\end{code}

\subsubsection{Circus Actions}
\begin{code}
-}
data PPar
 = ProcZPara ZPara                         -- Par
 | CParAction ZName ParAction              -- N \circdef ParAction
 | CNameSet ZName NSExp                    -- \circnameset N == NSExp
 deriving (Eq,Ord,Show)

data ParAction
 = CircusAction CAction                                 -- Action
 | ParamActionDecl [ZGenFilt] ParAction    -- Decl \circspot ParAction
 deriving (Eq,Ord,Show)

data CAction
 = CActionCommand CCommand
 | CActionName ZName

 | CSPSkip | CSPStop | CSPChaos
 | CSPCommAction Comm CAction             -- Comm \then Action
 | CSPGuard ZPred CAction                 -- Pred \circguard Action
 | CSPSeq CAction CAction                 -- Action \circseq Action
 | CSPExtChoice CAction CAction           -- Action \extchoice Action
 | CSPIntChoice CAction CAction           -- Action \intchoice Action
 | CSPNSParal NSExp CSExp NSExp CAction CAction -- Action \lpar NSExp | CSExp | NSExp \rpar Action
 | CSPParal CSExp CAction CAction         -- Action \lpar CSExp \rpar Action
 | CSPNSInter NSExp NSExp CAction CAction -- Action \linter NSExp | NSExp \rinter Action
 | CSPInterleave CAction CAction          -- Action \interleave Action
 | CSPHide CAction CSExp                  -- Action \circhide CSExp
 | CSPParAction ZName [ZExpr]             -- Action(Exp^{+})
 | CSPRenAction ZName CReplace            -- Action[x/y,z/n]
 | CSPRecursion ZName CAction             -- \circmu N \circspot Action
 | CSPUnParAction [ZGenFilt] CAction ZName     -- (Decl \circspot Action) (ZName)
 | CSPRepSeq [ZGenFilt] CAction           -- \Semi Decl \circspot Action
 | CSPRepExtChoice [ZGenFilt] CAction     -- \Extchoice Decl \circspot Action
 | CSPRepIntChoice [ZGenFilt] CAction     -- \IntChoice Decl \circspot Action
 | CSPRepParalNS CSExp [ZGenFilt] NSExp CAction -- \lpar CSExp \rpar Decl \circspot \lpar NSExp \rpar Action
 | CSPRepParal CSExp [ZGenFilt] CAction   -- \lpar CSExp \rpar Decl \circspot ction
 | CSPRepInterlNS [ZGenFilt] NSExp CAction  -- \Interleave Decl \circspot \linter NSExp \rinter Action
 | CSPRepInterl [ZGenFilt] CAction        -- \Interleave Decl \circspot  Action
 deriving (Eq,Ord,Show)
{-
\end{code}

\subsubsection{Circus Communication}

\begin{code}
-}
data Comm
  = ChanComm ZName [CParameter]           -- N CParameter*
  | ChanGenComm ZName [ZExpr] [CParameter]-- N [Exp^{+}] CParameter *
  deriving (Eq,Ord,Show)


data CParameter
   = ChanInp ZName                        -- ?N
   | ChanInpPred ZName ZPred              -- ?N : Pred
   | ChanOutExp ZExpr                     -- !Exp
   | ChanDotExp ZExpr                     -- .Exp
   deriving (Eq,Ord,Show)
{-
\end{code}

\subsubsection{Circus Commands}

\begin{code}
-}
data CCommand
  = CAssign [ZVar] [ZExpr]                -- N^{+} := Exp^{+}
  | CIf CGActions                         -- \circif GActions \cirfi
  | CVarDecl [ZGenFilt] CAction           -- \circvar Decl \circspot Action
  | CAssumpt [ZName] ZPred ZPred          -- N^{+} \prefixcolon [Pred,Pred]
  | CAssumpt1 [ZName] ZPred               -- N^{+} \prefixcolon [Pred,Pred]
  | CPrefix ZPred ZPred                   -- \prefixcolon [Pred,Pred]
  | CPrefix1 ZPred                        -- \prefixcolon [Pred]
  | CommandBrace ZPred                    -- \{Pred\}
  | CommandBracket ZPred                  -- [Pred]
  | CValDecl [ZGenFilt] CAction           -- \circval Decl \circspot Action
  | CResDecl [ZGenFilt] CAction           -- \circres Decl \circspot Action
  | CVResDecl [ZGenFilt] CAction          -- \circvres Decl \circspot Action
  deriving (Eq,Ord,Show)

data CGActions
 = CircGAction ZPred CAction                 -- Pred \circthen Action
 | CircThenElse CGActions CGActions    -- CGActions \circelse GActions
 | CircElse ParAction    -- \circelse CAction
 deriving (Eq,Ord,Show)

data CReplace
  = CRename [ZVar] [ZVar]        -- A[yi / xi] = CRename (ZVar xi []) (ZVar yi [])
  | CRenameAssign [ZVar] [ZVar]  -- A[yi := xi] = CRenameAssign (ZVar xi []) (ZVar yi [])
  deriving (Eq,Ord,Show)


data ZTerm
    = ZExpr ZExpr
    | ZPred ZPred
    | ZNull
    deriving (Eq,Ord,Show)
