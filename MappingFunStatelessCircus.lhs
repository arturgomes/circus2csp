%!TEX root = MAIN.tex

\section{Mapping Functions - Stateless Circus}
Mapping Omega Functions from Circus to Circus

\ignore{
\begin{code}
module MappingFunStatelessCircus
( 
  omega_CAction,
  omega_Circus,
  omega_CProc,
  omega_ParAction,
  omega_ProcDecl,
  omega_ProcessDef,
  def_mem_st_Circus_aux
)
where
import AST
import DefSets
import Data.List hiding (union, intersect)
import FormatterToCSP
import CRL

showexpr = zexpr_string (pinfo_extz 80)
\end{code}

\begin{code}
def_delta_mapping :: [(ZName, ZVar, ZExpr)] -> [ZExpr]
def_delta_mapping [(n,(v,[]),t)] 
  = [ZCall (ZVar ("\\mapsto",[])) (ZTuple [ZVar ((join_name (join_name "st_var" n) v),[]),t])]
def_delta_mapping ((n,(v,[]),t):xs) 
  = [ZCall (ZVar ("\\mapsto",[])) (ZTuple [ZVar ((join_name (join_name "st_var" n) v),[]),t])] 
    ++ (def_delta_mapping xs)
def_delta_mapping [] = []
\end{code}

\begin{code}
def_delta_name :: [(ZName, ZVar, ZExpr)] -> [ZBranch]
def_delta_name [(n,(v,[]),t)] 
  = [ZBranch0 ((join_name (join_name "st_var" n) v),[])]
def_delta_name ((n,(v,[]),t):xs) 
  = [ZBranch0 ((join_name (join_name "st_var" n) v),[])] 
    ++ (def_delta_name xs)
def_delta_name [] = []

\end{code}
\begin{code}
get_pre_Circ_proc :: [ZPara] -> [ZPara]
get_pre_Circ_proc ((Process cp):xs) 
  = (get_pre_Circ_proc xs)
get_pre_Circ_proc (x:xs) 
  = x:(get_pre_Circ_proc xs)
get_pre_Circ_proc []
  = []
\end{code}
\begin{code}
omega_Circus :: [ZPara] -> [ZPara]
omega_Circus spec
  = [ZGivenSetDecl ("UNIVERSE",[]),
      ZFreeTypeDef ("NAME",[]) (def_delta_name (def_mem_st_Circus_aux spec1)),
      ZAbbreviation ("BINDINGS",[]) (ZCall (ZVar ("\\fun",[])) (ZTuple [ZVar ("NAME",[]),ZVar ("UNIVERSE",[])])), 
      ZAbbreviation ("\\delta",[]) (ZSetDisplay (def_delta_mapping (def_mem_st_Circus_aux spec1))),
      CircChannel [CChanDecl "mget" (ZCross [ZVar ("NAME",[]),ZVar ("UNIVERSE",[])]), CChanDecl "mset" (ZCross [ZVar ("NAME",[]),ZVar ("UNIVERSE",[])])],
      CircChannel [CChan "terminate"],
      CircChanSet "MEMi" (CChanSet ["mset","mget","terminate"])]
    ++ (omega_Circus_aux spec1 spec1)
    where 
      spec1 = (map (rename_vars_ZPara1 (def_mem_st_Circus_aux spec)) spec) -- renaming variables for highlighting which is state var from which process
\end{code}
\subsection{Creating the Memory process}
\begin{code}
def_mem_st_Circus_aux :: [ZPara] -> [(ZName, ZVar, ZExpr)]
def_mem_st_Circus_aux []
  = []
def_mem_st_Circus_aux [x]
  = def_mem_st_CircParagraphs x
def_mem_st_Circus_aux (x:xs)
  = (def_mem_st_CircParagraphs x)++(def_mem_st_Circus_aux xs)
\end{code}
\begin{code}
def_mem_st_CircParagraphs :: ZPara -> [(ZName, ZVar, ZExpr)]
def_mem_st_CircParagraphs (Process cp)
  = (def_mem_st_ProcDecl cp)
def_mem_st_CircParagraphs x
  = []
\end{code}

\begin{code}
def_mem_st_ProcDecl :: ProcDecl -> [(ZName, ZVar, ZExpr)]
def_mem_st_ProcDecl (CGenProcess zn (x:xs) pd)
  = (def_mem_st_ProcessDef zn pd)
def_mem_st_ProcDecl (CProcess zn pd)
  = (def_mem_st_ProcessDef zn pd)
\end{code}

\begin{code}
def_mem_st_ProcessDef :: ZName -> ProcessDef -> [(ZName, ZVar, ZExpr)]
def_mem_st_ProcessDef name (ProcDefSpot xl pd)
  = (def_mem_st_ProcessDef name pd)
def_mem_st_ProcessDef name (ProcDefIndex xl pd)
  = (def_mem_st_ProcessDef name pd)
def_mem_st_ProcessDef name (ProcDef cp)
  = (def_mem_st_CProc name cp)
\end{code}

\begin{code}
def_mem_st_CProc :: ZName -> CProc -> [(ZName, ZVar, ZExpr)]
def_mem_st_CProc name (ProcMain zp (x:xs) ca)
  = (get_state_var name zp) -- ++(get_local_var ca)
def_mem_st_CProc  name x
  = []
\end{code}
\begin{code}
get_state_var :: ZName -> ZPara -> [(ZName, ZVar, ZExpr)]
get_state_var name (ZSchemaDef n (ZSchema (x:xs)))
  = (get_state_var_aux name x)
    ++
    (get_state_var name (ZSchemaDef n (ZSchema xs)))
get_state_var _ _ = []

\end{code}
\begin{code}
get_state_var_aux name (Choose x y) = [(name, x, y)]
get_state_var_aux _ _ = []
\end{code}
\subsection{Omega functions}
\begin{code}
omega_Circus_aux :: [ZPara] -> [ZPara] -> [ZPara]

omega_Circus_aux spec [(Process cp)]
  = [(Process (omega_ProcDecl spec cp))]
  -- where
  --   ncp = (rename_vars_ProcDecl1 (def_mem_st_Circus_aux spec) cp)
omega_Circus_aux spec [x] = [x]
omega_Circus_aux spec ((Process cp):xs)
  = [(Process (omega_ProcDecl spec cp))]++(omega_Circus_aux spec xs)
  -- where
  -- ncp = (rename_vars_ProcDecl1 (def_mem_st_Circus_aux spec) cp)
omega_Circus_aux spec (x:xs)
  = [x]++(omega_Circus_aux spec xs)
\end{code}



\subsection{Mapping Circus Processes Declaration}

\begin{code}
omega_ProcDecl :: [ZPara] -> ProcDecl -> ProcDecl
omega_ProcDecl spec (CGenProcess zn (x:xs) pd)
  = (CGenProcess zn (x:xs) (omega_ProcessDef spec pd))
    -- where
      -- npd = (rename_vars_ProcessDef1 (def_mem_st_Circus_aux spec) pd)
omega_ProcDecl spec (CProcess zn pd)
  = (CProcess zn (omega_ProcessDef spec pd))
    -- where
      -- npd = (rename_vars_ProcessDef1 (def_mem_st_Circus_aux spec) pd)
\end{code}

\subsection{Mapping Circus Processes Definition}
\begin{code}
omega_ProcessDef :: [ZPara] -> ProcessDef -> ProcessDef
omega_ProcessDef spec (ProcDefSpot xl pd)
  = (ProcDefSpot xl (omega_ProcessDef spec pd))
omega_ProcessDef spec (ProcDefIndex xl pd)
  = (ProcDefIndex xl (omega_ProcessDef spec pd))
omega_ProcessDef spec (ProcDef cp)
  = (ProcDef (omega_CProc spec cp))
\end{code}

\subsection{Mapping Circus Processes}
Note: $CGenProc$ ($N[Exp^{+}]$), $CSimpIndexProc$, and $CParamProc$ ($N(Exp^{+})$) are not yet implemented.
\begin{code}
omega_CProc :: [ZPara] -> CProc -> CProc
omega_CProc spec (CExtChoice a b)
  = (CExtChoice (omega_CProc spec a) (omega_CProc spec b))
omega_CProc spec (CHide a cs)
  = (CHide (omega_CProc spec a) cs)
omega_CProc spec (CIntChoice a b)
  = (CIntChoice (omega_CProc spec a) (omega_CProc spec b))
omega_CProc spec (CInterleave a b)
  = (CInterleave (omega_CProc spec a) (omega_CProc spec b))
omega_CProc spec (CircusProc zn)
  = (CircusProc zn)
omega_CProc spec (CParParal cs a b)
  = (CParParal cs (omega_CProc spec a) (omega_CProc spec b))
omega_CProc spec (CRepExtChProc [(Choose x s)] a)
  = (CRepExtChProc [(Choose x s)] (omega_CProc spec a))
omega_CProc spec (CRepIntChProc [(Choose x s)] a)
  = (CRepIntChProc [(Choose x s)] (omega_CProc spec a))
omega_CProc spec (CRepInterlProc [(Choose x s)] a)
  = (CRepInterlProc [(Choose x s)] (omega_CProc spec a))
omega_CProc spec (CRepParalProc cse [(Choose x s)] a)
  = (CRepParalProc cse [(Choose x s)] (omega_CProc spec a))
omega_CProc spec (CRepSeqProc [(Choose x s)] a)
  = (CRepSeqProc [(Choose x s)] (omega_CProc spec a))
omega_CProc spec (CSeq a b)
  = (CSeq (omega_CProc spec a) (omega_CProc spec b))
omega_CProc spec (ProcStalessMain xls ca)
  = (ProcStalessMain (concat (map omega_PPar xls)) (mk_main_action_bind nstate (omega_CAction ca)))
    where 
      nstate = (def_mem_st_Circus_aux spec)
omega_CProc spec (CGenProc zn (x:xs))
  = (CGenProc zn (x:xs))
omega_CProc spec (CParamProc zn (x:xs))
  = (CParamProc zn (x:xs))
omega_CProc spec (CSimpIndexProc zn (x:xs))
  = (CSimpIndexProc zn (x:xs))
omega_CProc spec (ProcMain zp (x:xs) ca)
  = (ProcStalessMain 
    [make_memory_proc] 
    (get_main_action 
      (concat (map omega_PPar (x:xs)))
      (mk_main_action_bind nstate (omega_CAction ca))))
    where 
      nstate = (def_mem_st_Circus_aux spec)
omega_CProc spec x
  = x
\end{code}
Here I'm making the bindings for the main action. 
\begin{code}
mk_main_action_bind :: [(ZName, ZVar, ZExpr)] -> CAction -> CAction
mk_main_action_bind lst ca
  = (CActionCommand (CValDecl [Choose ("b",[]) (ZSetComp [Choose ("x",[]) (ZVar ("BINDING",[])),Check (mk_inv lst) ] Nothing)] ca))
\end{code}
\begin{code}
mk_inv :: [(ZName, ZVar, ZExpr)] -> ZPred
mk_inv [(a,b,ZVar c)] 
  = (ZMember (ZVar b) (ZVar c))
mk_inv ((a,b,ZVar c):xs) 
  = (ZAnd (mk_inv xs) (ZMember (ZVar b) (ZVar c)) ) 

\end{code}
\subsection{Mapping Parameterised Circus Actions}
\begin{code}
omega_PPar :: PPar -> [PPar]
omega_PPar (ProcZPara zp) = [(ProcZPara zp)]
omega_PPar (CParAction n pa) = [(CParAction n (omega_ParAction pa))]
omega_PPar (CNameSet n ns) = [(CNameSet n ns)]
\end{code}
\begin{code}
omega_ParAction :: ParAction -> ParAction
omega_ParAction (CircusAction ca)
  = (CircusAction (omega_CAction ca))
omega_ParAction (ParamActionDecl xl pa)
  = (ParamActionDecl xl (omega_ParAction pa))
\end{code}
}
\subsection{Stateless Circus - Actions}

\begin{circus}
\Omega_A (\Skip) \circdef \Skip
\also \Omega_A (\Stop) \circdef \Stop
\also \Omega_A (\Chaos) \circdef \Chaos
\end{circus}
is written in Haskell as:
\begin{code}
omega_CAction :: CAction -> CAction
omega_CAction CSPSkip = CSPSkip
omega_CAction CSPStop = CSPStop
omega_CAction CSPChaos = CSPChaos
\end{code}

\begin{circus}
\Omega_A (c \then A) \circdef c \then \Omega_A (A)
\end{circus}

is written in Haskell as:
\begin{code}
omega_CAction (CSPCommAction (ChanComm c []) a)
  = (CSPCommAction (ChanComm c []) (omega_CAction a))
\end{code}

\begin{circus}
\Omega_A (c.e(v_0,\ldots,v_n,l_0,\ldots,l_m) \then A) \circdef
\\\t2 get.v_0?vv_0 \then \ldots \then get.v_n?vv_n \then
\\\t2 get.l_0?vl_0 \then \ldots \then get.l_m?vl_m \then
\\\t2 c.e(vv_0,\ldots,vv_n,vl_0,\ldots,vl_m) \then \Omega'_{A} (A)
\end{circus}
where
\begin{circus}
FV (e) = (v_0,\ldots,v_n,l_0,\ldots,l_m)
\end{circus}

is written in Haskell as:
\begin{code}
omega_CAction (CSPCommAction (ChanComm c ((ChanDotExp e):xs)) a)
  = make_get_com lxs (rename_vars_CAction (CSPCommAction (ChanComm c ((ChanDotExp e):xs)) (omega_prime_CAction a)))
  where lxs = concat (map get_ZVar_st (free_var_ZExpr e))
\end{code}

\begin{circus}
\Omega_A (c!e(v_0,\ldots,v_n,l_0,\ldots,l_m) \then A) \circdef
\\\t2 c.e(v_0,\ldots,v_n,l_0,\ldots,l_m) \then A
\end{circus}
\begin{code}
omega_CAction (CSPCommAction (ChanComm c ((ChanOutExp e):xs)) a)
  = omega_CAction (CSPCommAction (ChanComm c ((ChanDotExp e):xs)) a)
\end{code}

\begin{circus}
\Omega_A (g(v_0,\ldots,v_n,l_0,\ldots,l_m) \then A) \circdef
\\\t2 get.v_0?vv_0 \then \ldots \then get.v_n?vv_n \then
\\\t2 get.l_0?vl_0 \then \ldots \then get.l_m?vl_m \then
\\\t2 g(vv_0,\ldots,vv_n,vl_0,\ldots,vl_m) \circguard \Omega'_{A} (A)
\end{circus}
is written in Haskell as:
\begin{code}
omega_CAction (CSPGuard g a)
  = make_get_com lxs (rename_vars_CAction (CSPGuard (rename_ZPred g) (omega_prime_CAction a)))
  where lxs = concat (map get_ZVar_st (free_var_ZPred g))
\end{code}


I'm considering $x?k \neq x?k : P$ and I'm making the translation straightforward:

\begin{circus}
\Omega_A (c?x \then A) \circdef
\\\t2 c?x \then \Omega'_{A} (A)
\end{circus}

is written in Haskell as:
\begin{code}
omega_CAction (CSPCommAction (ChanComm c [ChanInp (x:xs)]) a)
  = (CSPCommAction (ChanComm c [ChanInp (x:xs)]) (omega_CAction a))
\end{code}


\begin{circus}
\Omega_A (c?x : P(x,v_0,\ldots,v_n,l_0,\ldots,l_m) \then A) \circdef
\\\t2 get.v_0?vv_0 \then \ldots \then get.v_n?vv_n \then
\\\t2 get.l_0?vl_0 \then \ldots \then get.l_m?vl_m \then
\\\t2 c?x : P(x,vv_0,\ldots,vv_n,vl_0,\ldots,vl_m) \then \Omega'_{A} (A)
\end{circus}
where
\begin{circus}
x \in wrtV(A)
\end{circus}

is written in Haskell as:
\begin{code}
omega_CAction (CSPCommAction (ChanComm c [ChanInpPred (x:xs) p]) a)
  = case not (elem x (getWrtV(a))) of
    True -> make_get_com lsx (rename_vars_CAction (CSPCommAction
             (ChanComm c [ChanInpPred x p])
                 (omega_prime_CAction a)))
    _  -> (CSPCommAction (ChanComm c [ChanInpPred x p]) a)
  where lsx = concat (map get_ZVar_st (free_var_ZPred p))
\end{code}



\begin{circus}
\Omega_A (A_1 \circseq A_2) \circdef \Omega_A (A_1) \circseq \Omega_A (A_2)
\end{circus}
is written in Haskell as:
\begin{code}
omega_CAction (CSPSeq ca cb)
  = (CSPSeq (omega_CAction ca) (omega_CAction cb))
\end{code}

\begin{circus}
\Omega_A (A_1 \intchoice A_2) \circdef \Omega_A (A_1) \intchoice \Omega_A (A_2)
\end{circus}
is written in Haskell as:
\begin{code}
omega_CAction (CSPIntChoice ca cb)
  = (CSPIntChoice (omega_CAction ca) (omega_CAction cb))
\end{code}

% TODO: I need to somehow calculate the $FV(A_1)$ and $FV(A_2)$. What should I do?
\begin{circus}
\Omega_A (A_1 \extchoice A_2) \circdef
\\\t1 get.v_0?vv_0 \then \ldots \then get.v_n?vv_n \then
\\\t1 get.l_0?vl_0 \then \ldots \then get.l_m?vl_m \then
\\\t2 (\Omega'_A (A_1) \extchoice \Omega'_A (A_2))
\end{circus}
is written in Haskell as:
\begin{code}
omega_CAction (CSPExtChoice ca cb)
  = make_get_com lsx (rename_vars_CAction (CSPExtChoice (omega_prime_CAction ca) (omega_prime_CAction cb)))
   where
    lsx = (map fst (nub (free_var_CAction (CSPExtChoice ca cb))))
\end{code}

\begin{circus}
\Omega_A (A1 \lpar ns1 | cs | ns2 \rpar A2) \circdef
\\\t1 get.v_0?vv_0 \then \ldots \then get.v_n?vv_n \then
\\\t1 get.l_0?vl_0 \then \ldots \then get.l_m?vl_m \then
      \\\t2\left (\begin{array}{l}
       \left (\begin{array}{l}
        \left (\begin{array}{l}
         \left (\begin{array}{l}
          \Omega'_A (A_1) \circseq terminate \then \Skip
         \end{array}\right )\\
          \lpar \{\} | MEM_I | \{\} \rpar
          \\ MemoryMerge(\{v0 \mapsto vv0,\ldots\},LEFT)
        \end{array}\right )
        \circhide MEM_I \\
       \lpar \{\} | cs | \{\} \rpar \\
        \left (\begin{array}{l}
         \left (\begin{array}{l}
          \Omega'_A (A_2) \circseq terminate \then \Skip
         \end{array}\right )\\
          \lpar \{\} | MEM_I | \{\} \rpar
          \\ MemoryMerge(\{v0 \mapsto vv0,\ldots\},RIGHT)
        \end{array}\right )
        \circhide MEM_I
       \end{array}\right )\\
      \lpar \{\} | MEM_I | \{\} \rpar\\
      Merge
    \end{array}\right )\\
    \t2\circhide \lchanset mleft, mright \rchanset
\end{circus}

\begin{code}
omega_CAction (CSPNSParal ns1 cs ns2 a1 a2)
  = make_get_com lsx (rename_vars_CAction (CSPHide
   (CSPNSParal NSExpEmpty (CSExpr "MEMi") NSExpEmpty
     (CSPNSParal NSExpEmpty cs NSExpEmpty
      (CSPHide
       (CSPNSParal NSExpEmpty (CSExpr "MEMi") NSExpEmpty
        (CSPSeq a1 (CSPCommAction (ChanComm "terminate" []) CSPSkip))
        (CSPParAction "MemoryMerge"
         [ZSetDisplay [],
                ZVar ("LEFT",[])]))
       (CSExpr "MEMi"))
      (CSPHide
       (CSPNSParal NSExpEmpty (CSExpr "MEMi") NSExpEmpty
        (CSPSeq a2 (CSPCommAction (ChanComm "terminate" []) CSPSkip))
        (CSPParAction "MemoryMerge"
         [ZSetDisplay [],
                ZVar ("RIGHT",[])]))
       (CSExpr "MEMi")))
      (CActionName "Merge"))
      (CChanSet ["mleft","mright"])))
   where
    lsx = (map fst (nub (free_var_CAction a1))) `union` (map fst (nub (free_var_CAction a2)))
\end{code}

\begin{circus}
\Omega_A (\Semi x : \langle v_1,...,v_n \rangle \circspot A(x)) \circdef \Omega_A (A(v_1)\circseq \ldots \circseq A(v_n))
\end{circus}
is written in Haskell as:
\begin{code}
omega_CAction (CSPRepSeq [Choose (x,[]) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1,[])]))
  = case x == x1 of
    True -> omega_CAction (rep_CSPRepSeq act xs)
    _  -> (CSPRepSeq [Choose (x,[]) (ZSeqDisplay xs)]
          (CSPParAction act [ZVar (x1,[])]))
omega_CAction (CSPRepSeq [Choose (x,[]) v] act)
  = (CSPRepSeq [Choose (x,[]) v] (omega_CAction act))
\end{code}

\begin{circus}
\Omega_A (\Extchoice x : \langle v_1,...,v_n \rangle \circspot A(x)) \circdef \Omega_A (A(v_1)\extchoice \ldots \extchoice A(v_n))
\end{circus}
is written in Haskell as:
\begin{code}
omega_CAction (CSPRepExtChoice [Choose (x,[]) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1,[])]))
  = case x == x1 of
    True -> omega_CAction (rep_CSPRepExtChoice act xs)
    _  -> (CSPRepExtChoice [Choose (x,[]) (ZSeqDisplay xs)]
          (CSPParAction act [ZVar (x1,[])]))
omega_CAction (CSPRepExtChoice [Choose (x,[]) v] act)
  = (CSPRepExtChoice [Choose (x,[]) v] (omega_CAction act))
\end{code}

\begin{circus}
\Omega_A (\Intchoice x : \langle v_1,...,v_n \rangle \circspot A(x)) \circdef \Omega_A (A(v_1)\intchoice \ldots \intchoice A(v_n))
\end{circus}
is written in Haskell as:
\begin{code}
omega_CAction (CSPRepIntChoice [Choose (x,[]) (ZSeqDisplay xs)]
          (CSPParAction act [ZVar (x1,[])]))
  = case x == x1 of
    True -> omega_CAction(rep_CSPRepIntChoice act xs)
    _  -> (CSPRepIntChoice [Choose (x,[]) (ZSeqDisplay xs)]
          (CSPParAction act [ZVar (x1,[])]))
omega_CAction (CSPRepIntChoice [Choose (x,[]) v] act)
  = (CSPRepIntChoice [Choose (x,[]) v] (omega_CAction act))
\end{code}

\begin{circus}
\Omega_A (\lpar cs \rpar x : \langle v_1,...,v_n \rangle \circspot \lpar ns(x) \rpar A(x)) \circdef
\\\t1
\left (\begin{array}{l}A(v_1)
   \\ \lpar ns(v_1) | cs | \bigcup\{x : \{v_2,...,v_n\} \circspot ns(x)\} \rpar
   \\ \left (\begin{array}{l}
     \ldots
      \left (\begin{array}{l}
      \Omega_A(A(v_n -1))
      \\ \lpar ns(v_n -1 ) | cs | ns(v_n) \rpar
      \\ A(v_n)\end{array}\right )\end{array}\right )\end{array}\right )

\end{circus}
is written in Haskell as:
\begin{code}
omega_CAction (CSPRepParalNS (CSExpr cs) [Choose (x,[]) (ZSetDisplay lsx)]
          (NSExprParam ns [ZVar (x1,[])])
          (CSPParAction a [ZVar (x2,[])]))
  = case (x == x1) && (x == x2) of
    True -> omega_CAction (rep_CSPRepParalNS a cs ns x lsx)
    _  -> (CSPRepParalNS (CSExpr cs) [Choose (x,[]) (ZSetDisplay lsx)]
          (NSExprParam ns [ZVar (x1,[])])
          (CSPParAction a [ZVar (x2,[])]))
omega_CAction (CSPRepParalNS (CSExpr cs) [Choose (x,[]) (ZSetDisplay lsx)]
          (NSExprParam ns [ZVar (x1,[])]) act)
  = (CSPRepParalNS (CSExpr cs) [Choose (x,[]) (ZSetDisplay lsx)]
          (NSExprParam ns [ZVar (x1,[])])
          (omega_CAction act))
\end{code}
% \begin{circus}
% \Omega_A ( \circval Decl \circspot P) \circdef \circval Decl \circspot \Omega_A (P)
% \end{circus}
% is written in Haskell as:
% \begin{code}
% omega_CAction lst (CActionCommand (CValDecl xs a))
%   = (CActionCommand (CValDecl xs (omega_CAction lst a)))
% \end{code}
\begin{circus}
\Omega_A \left (\begin{array}{l}x_0,\ldots,x_n:=e_0\left (\begin{array}{l}v_0,...,v_n,\\l_0,...,l_m\end{array}\right ),\ldots,e_n\left (\begin{array}{l}v_0,...,v_n,\\l_0,...,l_m\end{array}\right )\end{array}\right ) \circdef
\\\t1 get.v_0?vv_0 \then \ldots \then get.v_n?vv_n \then
\\\t1 get.l_0?vl_0 \then \ldots \then get.l_m?vl_m \then
\\\t1 set.x_0!e_0(vv_0,...,vv_n,vl_0,...,vl_m) \then
\\\t1\ldots\then
\\\t1 set.x_n!e_n(vv_0,...,vv_n,vl_0,...,vl_m) \then \Skip
\end{circus}

\begin{code}
omega_CAction (CActionCommand (CAssign varls valls))
  = make_get_com (map fst varls) (rename_vars_CAction (make_set_com varls valls CSPSkip))
\end{code}
\begin{circus}
\Omega_A (\circif g (v_0,...,v_n,l_0,...,l_m) \circthen A \circfi ) \defs
   \\\t1 get.v_0?vv_0 \then \ldots \then get.v_n?vv_n \then
   \\\t1 get.l_0?vl_0 \then \ldots \then get.l_m?vl_m \then
   \\\t1\circif g (v_0,...,v_n,l_0,...,l_m) \circthen \Omega'_A (A) \circfi
\end{circus}
\begin{code}
omega_CAction (CActionCommand (CIf (CircGAction g a)))
  = make_get_com lsx (rename_vars_CAction  (CActionCommand
             (CIf (CircGAction g (omega_prime_CAction a)))))
  where
   lsx = (map fst (nub (free_var_ZPred g)))

\end{code}
\begin{circus}
\Omega_A
   \left (\begin{array}{l}
   \circif g_0 (v_0,...,v_n,l_0,...,l_m) \circthen A_0
   \\\t1\circelse \ldots
   \\\t1 \circelse g_n (v_0,...,v_n,l_0,...,l_m) \circthen A_n
   \\\circfi
   \end{array}\right ) \defs
   \\\t1 get.v_0?vv_0 \then \ldots \then get.v_n?vv_n \then
   \\\t1 get.l_0?vl_0 \then \ldots \then get.l_m?vl_m \then
   \\\t1\circif g_0 (v_0,...,v_n,l_0,...,l_m) \circthen \Omega'_A (A_0)
   \\\t2\circelse \ldots
   \\\t2 \circelse g_n (v_0,...,v_n,l_0,...,l_m) \circthen \Omega'_A (A_n)
   \\\t1\circfi
\end{circus}

\begin{code}
omega_CAction (CActionCommand (CIf (CircThenElse gl glx)))
  = make_get_com lsx (rename_vars_CAction (CActionCommand (CIf (mk_guard_pair guard_pair))))
  where
   guard_pair = get_guard_pair (CircThenElse gl glx)
   lsx = map fst (remdups $ concat $ map free_var_ZPred (map fst guard_pair))
\end{code}

\begin{circus}
\Omega_A (A \circhide cs) \circdef \Omega_A (A) \circhide cs
\end{circus}

is written in Haskell as:

\begin{code}
omega_CAction (CSPHide a cs) = (CSPHide (omega_CAction a) cs)
\end{code}

\begin{circus}
\Omega_A (\circmu X \circspot A(X)) \circdef \circmu X \circspot \Omega_A(A(X))
\end{circus}

is written in Haskell as:

\begin{code}
omega_CAction (CSPRecursion x c) = (CSPRecursion x (omega_CAction c))
\end{code}

\begin{circus}
\Omega_A (\Interleave x : \langle v_1,...,v_n \rangle \circspot A(x)) \circdef
\\\t1
\left (\begin{array}{l}A(v_1)
   \\ \lpar ns(v_1) | \bigcup\{x : \{v_2,...,v_n\} \circspot ns(x)\} \rpar
   \\ \left (\begin{array}{l}
     \ldots
      \left (\begin{array}{l}
      \Omega_A(A(v_n -1))
      \\ \lpar ns(v_n -1 ) | ns(v_n)\rpar
      \\ A(v_n)\end{array}\right )\end{array}\right )\end{array}\right )

\end{circus}

is written in Haskell as:

\begin{code}
omega_CAction (CSPRepInterlNS [Choose (x,[]) (ZSetDisplay lsx)]
          (NSExprParam ns [ZVar (x1,[])])
          (CSPParAction a [ZVar (x2,[])]))
  = case (x == x1) && (x == x2) of
    True -> omega_CAction (rep_CSPRepInterlNS a ns x lsx)
    _  ->  (CSPRepInterlNS [Choose (x,[]) (ZSetDisplay lsx)]
          (NSExprParam ns [ZVar (x1,[])])
          (CSPParAction a [ZVar (x2,[])]))
omega_CAction (CSPRepInterlNS [Choose (x,[]) (ZSetDisplay lsx)]
          (NSExprParam ns [ZVar (x1,[])])
          act)
  = (CSPRepInterlNS [Choose (x,[]) (ZSetDisplay lsx)]
          (NSExprParam ns [ZVar (x1,[])])
          (omega_CAction act))
\end{code}

\begin{circus}
\Omega_A (\{g\}) \circdef \prefixcolon [g, true]
\end{circus}

\begin{code}
omega_CAction (CActionCommand (CommandBrace g))
  = omega_CAction (CActionCommand (CPrefix g (ZTrue {reason = []})))
\end{code}

\begin{circus}
\Omega_A ([g]) \circdef \prefixcolon [g]
\end{circus}

\begin{code}
omega_CAction (CActionCommand (CommandBracket g))
  = omega_CAction (CActionCommand (CPrefix1 g))
\end{code}

\begin{circus}
\Omega_A (A[old_1,...,old_n := new_1,...,new_n) \circdef
\\\t1A[new_1,...,new_n/old_1,...,old_n)
\end{circus}

\begin{code}
omega_CAction (CSPRenAction a (CRenameAssign left right))
  = (CSPRenAction a (CRename right left))
omega_CAction x = x
\end{code}


NOTE: Besides the transformation rules for $[g]$ and ${g}$, the remaining transformation rules from page 91 of the D24.1 document, were not yet implemented.
\subsection{Definitions of $\Omega'_{A}$}


\begin{code}
omega_prime_CAction :: CAction -> CAction
omega_prime_CAction CSPSkip = CSPSkip
omega_prime_CAction CSPStop = CSPStop
omega_prime_CAction CSPChaos = CSPChaos
\end{code}

\begin{circus}
\Omega'_A (c \then A) \circdef c \then \Omega_A (A)
\end{circus}

is written in Haskell as:
\begin{code}
omega_prime_CAction (CSPCommAction (ChanComm c []) a)
  = (CSPCommAction (ChanComm c []) (omega_prime_CAction a))
\end{code}

\begin{circus}
\Omega'_A (c?x \then A) \circdef c?x \then \Omega_A (A)
\end{circus}

is written in Haskell as:
\begin{code}
omega_prime_CAction (CSPCommAction (ChanComm c x) a)
  = (CSPCommAction (ChanComm c x) (omega_prime_CAction a))
\end{code}

\begin{circus}
\Omega'_A (g(v_0,\ldots,v_n,l_0,\ldots,l_m) \then A) \circdef
\\\t2 g(vv_0,\ldots,vv_n,vl_0,\ldots,vl_m) \circguard \Omega'_{A} (A)
\end{circus}
is written in Haskell as:
\begin{code}
omega_prime_CAction (CSPGuard g a)
  = (CSPGuard g (omega_prime_CAction a))
\end{code}


\begin{circus}
\Omega'_A (A_1 \circseq A_2) \circdef \Omega_A (A_1) \circseq \Omega_A (A_2)
\end{circus}
is written in Haskell as:
\begin{code}
omega_prime_CAction (CSPSeq ca cb)
  = (CSPSeq (omega_prime_CAction ca) (omega_prime_CAction cb))
\end{code}

\begin{circus}
\Omega'_A (A_1 \intchoice A_2) \circdef \Omega_A (A_1) \intchoice \Omega_A (A_2)
\end{circus}
is written in Haskell as:
\begin{code}
omega_prime_CAction (CSPIntChoice ca cb)
  = (CSPIntChoice (omega_prime_CAction ca) (omega_prime_CAction cb))
\end{code}

% TODO: I need to somehow calculate the $FV(A_1)$ and $FV(A_2)$. What should I do?
\begin{circus}
\Omega'_A (A_1 \extchoice A_2) \circdef
\\\t1 get.v_0?vv_0 \then \ldots \then get.v_n?vv_n \then
\\\t1 get.l_0?vl_0 \then \ldots \then get.l_m?vl_m \then
\\\t2 (\Omega'_A (A_1) \extchoice \Omega'_A (A_2))
\end{circus}
is written in Haskell as:
\begin{code}
omega_prime_CAction (CSPExtChoice ca cb)
  = make_get_com lsx (CSPExtChoice (omega_prime_CAction ca) (omega_prime_CAction cb))
   where
    lsx = concat (map get_ZVar_st (remdups (free_var_CAction (CSPExtChoice ca cb))) )
\end{code}

\begin{circus}
\Omega'_A (A1 \lpar ns1 | cs | ns2 \rpar A2) \circdef
\\\t1 get.v_0?vv_0 \then \ldots \then get.v_n?vv_n \then
\\\t1 get.l_0?vl_0 \then \ldots \then get.l_m?vl_m \then
      \\\t2\left (\begin{array}{l}
       \left (\begin{array}{l}
        \left (\begin{array}{l}
         \left (\begin{array}{l}
          \Omega'_A (A_1) \circseq terminate \then \Skip
         \end{array}\right )\\
          \lpar \{\} | MEM_I | \{\} \rpar
          \\ MemoryMerge(\{v0 \mapsto vv0,\ldots\},LEFT)
        \end{array}\right )
        \circhide MEM_I \\
       \lpar \{\} | cs | \{\} \rpar \\
        \left (\begin{array}{l}
         \left (\begin{array}{l}
          \Omega'_A (A_2) \circseq terminate \then \Skip
         \end{array}\right )\\
          \lpar \{\} | MEM_I | \{\} \rpar
          \\ MemoryMerge(\{v0 \mapsto vv0,\ldots\},RIGHT)
        \end{array}\right )
        \circhide MEM_I
       \end{array}\right )\\
      \lpar \{\} | MEM_I | \{\} \rpar\\
      Merge
    \end{array}\right )\\
    \t2\circhide \lchanset mleft, mright \rchanset
\end{circus}

\begin{code}
omega_prime_CAction (CSPNSParal ns1 cs ns2 a1 a2)
  = make_get_com lsx (CSPHide
   (CSPNSParal NSExpEmpty (CSExpr "MEMi") NSExpEmpty
     (CSPNSParal NSExpEmpty cs NSExpEmpty
      (CSPHide
       (CSPNSParal NSExpEmpty (CSExpr "MEMi") NSExpEmpty
        (CSPSeq a1 (CSPCommAction (ChanComm "terminate" []) CSPSkip))
        (CSPParAction "MemoryMerge"
         [ZSetDisplay [],
                ZVar ("LEFT",[])]))
       (CSExpr "MEMi"))
      (CSPHide
       (CSPNSParal NSExpEmpty (CSExpr "MEMi") NSExpEmpty
        (CSPSeq a2 (CSPCommAction (ChanComm "terminate" []) CSPSkip))
        (CSPParAction "MemoryMerge"
         [ZSetDisplay [],
                ZVar ("RIGHT",[])]))
       (CSExpr "MEMi")))
      (CActionName "Merge"))
      (CChanSet ["mleft","mright"]))
   where
    lsx = concat (map get_ZVar_st ((free_var_CAction a1) `union` (free_var_CAction a2)))
\end{code}

\begin{circus}
\Omega'_A (\Semi x : \langle v_1,...,v_n \rangle \circspot A(x)) \circdef \Omega_A (A(v_1)\circseq \ldots \circseq A(v_n))
\end{circus}
is written in Haskell as:
\begin{code}
omega_prime_CAction (CSPRepSeq [Choose (x,[]) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1,[])]))
  = case x == x1 of
    True -> omega_prime_CAction (rep_CSPRepSeq act xs)
    _  -> (CSPRepSeq [Choose (x,[]) (ZSeqDisplay xs)]
          (CSPParAction act [ZVar (x1,[])]))
omega_prime_CAction (CSPRepSeq [Choose (x,[]) v] act)
  = (CSPRepSeq [Choose (x,[]) v] (omega_prime_CAction act))
\end{code}

\begin{circus}
\Omega'_A (\Extchoice x : \langle v_1,...,v_n \rangle \circspot A(x)) \circdef \Omega_A (A(v_1)\extchoice \ldots \extchoice A(v_n))
\end{circus}
is written in Haskell as:
\begin{code}
omega_prime_CAction (CSPRepExtChoice [Choose (x,[]) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1,[])]))
  = case x == x1 of
    True -> omega_CAction (rep_CSPRepExtChoice act xs)
    _  -> (CSPRepExtChoice [Choose (x,[]) (ZSeqDisplay xs)]
          (CSPParAction act [ZVar (x1,[])]))
omega_prime_CAction (CSPRepExtChoice [Choose (x,[]) v] act)
  = (CSPRepExtChoice [Choose (x,[]) v] (omega_prime_CAction act))
\end{code}

\begin{circus}
\Omega'_A (\Intchoice x : \langle v_1,...,v_n \rangle \circspot A(x)) \circdef \Omega_A (A(v_1)\intchoice \ldots \intchoice A(v_n))
\end{circus}
is written in Haskell as:
\begin{code}
omega_prime_CAction (CSPRepIntChoice [Choose (x,[]) (ZSeqDisplay xs)]
          (CSPParAction act [ZVar (x1,[])]))
  = case x == x1 of
    True -> omega_CAction (rep_CSPRepIntChoice act xs)
    _  -> (CSPRepIntChoice [Choose (x,[]) (ZSeqDisplay xs)]
          (CSPParAction act [ZVar (x1,[])]))
omega_prime_CAction (CSPRepIntChoice [Choose (x,[]) v] act)
  = (CSPRepIntChoice [Choose (x,[]) v] (omega_prime_CAction act))
\end{code}

\begin{circus}
\Omega'_A (\lpar cs \rpar x : \langle v_1,...,v_n \rangle \circspot \lpar ns(x) \rpar A(x)) \circdef
\\\t1
\left (\begin{array}{l}A(v_1)
   \\ \lpar ns(v_1) | cs | \bigcup\{x : \{v_2,...,v_n\} \circspot ns(x)\} \rpar
   \\ \left (\begin{array}{l}
     \ldots
      \left (\begin{array}{l}
      \Omega_A(A(v_n -1))
      \\ \lpar ns(v_n -1 ) | cs | ns(v_n) \rpar
      \\ A(v_n)\end{array}\right )\end{array}\right )\end{array}\right )

\end{circus}
is written in Haskell as:
\begin{code}
omega_prime_CAction (CSPRepParalNS (CSExpr cs) [Choose (x,[]) (ZSetDisplay lsx)] (NSExprParam ns [ZVar (x1,[])]) (CSPParAction a [ZVar (x2,[])]))
  = case (x == x1) && (x == x2) of 
      True -> omega_CAction (rep_CSPRepParalNS a cs ns x lsx) 
      _  -> (CSPRepParalNS (CSExpr cs) [Choose (x,[]) (ZSetDisplay lsx)] 
              (NSExprParam ns [ZVar (x1,[])]) (omega_prime_CAction (CSPParAction a [ZVar (x2,[])])))

omega_prime_CAction (CSPRepParalNS (CSExpr cs) [Choose (x,[]) (ZSetDisplay lsx)] (NSExprParam ns [ZVar (x1,[])]) act)
  = (CSPRepParalNS (CSExpr cs) [Choose (x,[]) (ZSetDisplay lsx)]
          (NSExprParam ns [ZVar (x1,[])])
          (omega_prime_CAction act))
\end{code}
\begin{circus}
\Omega'_A \left (\begin{array}{l}x_0,\ldots,x_n:=e_0\left (\begin{array}{l}v_0,...,v_n,\\l_0,...,l_m\end{array}\right ),\ldots,e_n\left (\begin{array}{l}v_0,...,v_n,\\l_0,...,l_m\end{array}\right )\end{array}\right ) \circdef
\\\t1 set.x_0!e_0(vv_0,...,vv_n,vl_0,...,vl_m) \then
\\\t1\ldots\then
\\\t1 set.x_n!e_n(vv_0,...,vv_n,vl_0,...,vl_m) \then \Skip
\end{circus}

\begin{code}
omega_prime_CAction (CActionCommand (CAssign varls valls))
  = (make_set_com varls valls CSPSkip)
\end{code}

\begin{circus}
\Omega'_A (\circif g (v_0,...,v_n,l_0,...,l_m) \circthen A \circfi ) \defs

   \\\t1\circif g (v_0,...,v_n,l_0,...,l_m) \circthen \Omega'_A (A) \circfi
\end{circus}
\begin{code}
omega_prime_CAction (CActionCommand (CIf (CircGAction g a)))
  = (CActionCommand (CIf (CircGAction g (omega_prime_CAction a))))

\end{code}
\begin{circus}
\Omega'_A
   \left (\begin{array}{l}
   \circif g_0 (v_0,...,v_n,l_0,...,l_m) \circthen A_0
   \\\t1\circelse \ldots
   \\\t1 \circelse g_n (v_0,...,v_n,l_0,...,l_m) \circthen A_n
   \\\circfi
   \end{array}\right ) \defs
    \\\t1\circif g_0 (v_0,...,v_n,l_0,...,l_m) \circthen \Omega'_A (A_0)
   \\\t2\circelse \ldots
   \\\t2 \circelse g_n (v_0,...,v_n,l_0,...,l_m) \circthen \Omega'_A (A_n)
   \\\t1\circfi
\end{circus}

\begin{code}
omega_prime_CAction (CActionCommand (CIf (CircThenElse gl glx)))
  = (CActionCommand (CIf (mk_guard_pair guard_pair)))
  where
   guard_pair = get_guard_pair (CircThenElse gl glx)
\end{code}

\begin{circus}
\Omega'_A (A \circhide cs) \circdef \Omega_A (A) \circhide cs
\end{circus}

is written in Haskell as:

\begin{code}
omega_prime_CAction (CSPHide a cs) = (CSPHide (omega_prime_CAction a) cs)
\end{code}

\begin{circus}
\Omega'_A (\circmu X \circspot A(X)) \circdef \circmu X \circspot \Omega_A(A(X))
\end{circus}

is written in Haskell as:

\begin{code}
omega_prime_CAction (CSPRecursion x c) = (CSPRecursion x (omega_prime_CAction c))
\end{code}

\begin{circus}
\Omega'_A (\Interleave x : \langle v_1,...,v_n \rangle \circspot A(x)) \circdef
\\\t1
\left (\begin{array}{l}A(v_1)
   \\ \lpar ns(v_1) | \bigcup\{x : \{v_2,...,v_n\} \circspot ns(x)\} \rpar
   \\ \left (\begin{array}{l}
     \ldots
      \left (\begin{array}{l}
      \Omega_A(A(v_n -1))
      \\ \lpar ns(v_n -1 ) | ns(v_n)\rpar
      \\ A(v_n)\end{array}\right )\end{array}\right )\end{array}\right )

\end{circus}

is written in Haskell as:

\begin{code}
omega_prime_CAction (CSPRepInterlNS [Choose (x,[]) (ZSetDisplay lsx)]
          (NSExprParam ns [ZVar (x1,[])])
          (CSPParAction a [ZVar (x2,[])]))
  = case (x == x1) && (x == x2) of
    True -> omega_CAction (rep_CSPRepInterlNS a ns x lsx)
    _  ->  (CSPRepInterlNS [Choose (x,[]) (ZSetDisplay lsx)]
          (NSExprParam ns [ZVar (x1,[])])
          (CSPParAction a [ZVar (x2,[])]))
omega_prime_CAction (CSPRepInterlNS [Choose (x,[]) (ZSetDisplay lsx)]
          (NSExprParam ns [ZVar (x1,[])])
          act)
  = (CSPRepInterlNS [Choose (x,[]) (ZSetDisplay lsx)]
          (NSExprParam ns [ZVar (x1,[])])
          (omega_prime_CAction act))
\end{code}

\begin{circus}
\Omega'_A (\{g\}) \circdef \prefixcolon [g, true]
\end{circus}

\begin{code}
omega_prime_CAction (CActionCommand (CommandBrace g))
  = omega_prime_CAction (CActionCommand (CPrefix g (ZTrue {reason = []})))
\end{code}

\begin{circus}
\Omega'_A ([g]) \circdef \prefixcolon [g]
\end{circus}

\begin{code}
omega_prime_CAction (CActionCommand (CommandBracket g))
  = omega_prime_CAction (CActionCommand (CPrefix1 g))
\end{code}

\begin{circus}
\Omega'_A (A[old_1,...,old_n := new_1,...,new_n) \circdef
\\\t1A[new_1,...,new_n/old_1,...,old_n)
\end{circus}

\begin{code}
omega_prime_CAction (CSPRenAction a (CRenameAssign left right))
  = (CSPRenAction a (CRename right left))
\end{code}

\begin{code}
omega_prime_CAction (CActionName n)
  = (CActionName n)
\end{code}

\begin{code}
omega_prime_CAction x 
  = error ("Not defined for Omega'"++ show x)
\end{code}
\subsection{Auxiliary functions for the definition of $\Omega_{A}$}
The use of Isabelle/HOL made me rethink of what was being produced
with the functions below. First, a $CSPParAction$, $A(x)$, does not need to call $omega_CAction$ again, as it does not change anything, so I removed it when a list of parameters $x$ is a singleton. Then, I realised that I don't need to call $omega_CAction$ at all in any of the $rep\_$ functions as that function is called for the result of any $rep\_$ function. Finally, I don't need to carry the triple with the state variable names/types. 

Function used to propagate $CSPRepSeq$ actions

\begin{code}
rep_CSPRepSeq :: ZName -> [ZExpr] -> CAction
rep_CSPRepSeq a [x]
  = (CSPParAction a [x])
rep_CSPRepSeq a (x:xs)
  = CSPSeq (CSPParAction a [x]) (rep_CSPRepSeq a xs)
\end{code}

Function used to propagate $CSPRepIntChoice$ actions

\begin{code}
rep_CSPRepIntChoice :: ZName -> [ZExpr] -> CAction
rep_CSPRepIntChoice a [x]
  = (CSPParAction a [x])
rep_CSPRepIntChoice a (x:xs)
  = CSPIntChoice (CSPParAction a [x]) (rep_CSPRepIntChoice a xs)
\end{code}

Function used to propagate $CSPRepExtChoice$ actions

\begin{code}
rep_CSPRepExtChoice :: ZName -> [ZExpr] -> CAction
rep_CSPRepExtChoice a [x]
  = (CSPParAction a [x])
rep_CSPRepExtChoice a (x:xs)
  = CSPExtChoice (CSPParAction a [x]) (rep_CSPRepExtChoice a xs)
\end{code}

Function used to propagate $CSPRepInterNS$ actions

\begin{code}
rep_CSPRepParalNS :: ZName -> ZName -> ZName -> String -> [ZExpr] -> CAction
rep_CSPRepParalNS a _ _ _ [x]
  = (CSPParAction a [x])
rep_CSPRepParalNS a cs ns y (x:xs)
  = (CSPNSParal (NSExprParam ns [x]) (CSExpr cs)
    (NSBigUnion (ZSetComp
           [Choose (y,[]) (ZSetDisplay xs)]
           (Just (ZCall (ZVar (ns,[])) (ZVar (y,[])))) ) )
     (CSPParAction a [x]) (rep_CSPRepParalNS a cs ns y xs) )
\end{code}

Function used to propagate $CSPRepInterNS$ actions

\begin{code}
rep_CSPRepInterlNS :: ZName -> ZName -> String -> [ZExpr] -> CAction
rep_CSPRepInterlNS a _ _ [x]
  = (CSPParAction a [x])
rep_CSPRepInterlNS a ns y (x:xs)
  = (CSPNSInter (NSExprParam ns [x])
    (NSBigUnion (ZSetComp
           [Choose (y,[]) (ZSetDisplay xs)]
           (Just (ZCall (ZVar (ns,[])) (ZVar (y,[])))) ) )
     (CSPParAction a [x]) (rep_CSPRepInterlNS a ns y xs) )
\end{code}

Auxiliary function to propagate $get$ communication through the variables and local variables of an action.
\begin{circus}
make\_get\_com\ (v_0,\ldots,v_n,l_0,\ldots,l_m)~A \defs
\\\t2 get.v_0?vv_0 \then \ldots \then get.v_n?vv_n \then
\\\t2 get.l_0?vl_0 \then \ldots \then get.l_m?vl_m \then A
\end{circus}
\begin{code}
make_get_com :: [ZName] -> CAction -> CAction
make_get_com [x] c
  = (CSPCommAction (ChanComm "mget"
    [ChanDotExp (ZVar (x,[])),ChanInp ("v_"++x)]) c)
make_get_com (x:xs) c
  = (CSPCommAction (ChanComm "mget"
    [ChanDotExp (ZVar (x,[])),ChanInp ("v_"++x)]) (make_get_com xs c))
make_get_com x c = c    
\end{code}

\begin{code}
make_set_com :: [ZVar] -> [ZExpr] -> CAction -> CAction
make_set_com [(x,_)] [y] c
  = (CSPCommAction (ChanComm "mset"
    [ChanDotExp (ZVar (x,[])),ChanOutExp y]) (omega_CAction c))
make_set_com ((x,_):xs) (y:ys) c
  = (CSPCommAction (ChanComm "mset"
     [ChanDotExp (ZVar (x,[])),ChanOutExp y]) (make_set_com xs ys c))
\end{code}

Given $\{v_0,\ldots,v_n\}$, the function $make\_maps\_to$ returns $\{v_0 \mapsto vv_o, \ldots, v_n \mapsto vv_n\}$.
\begin{code}
make_maps_to :: [ZVar] -> [ZExpr]
make_maps_to [(x,[])]
  = [ZCall (ZVar ("\\mapsto",[]))
    (ZTuple [ZVar (x,[]),ZVar ("val"++x,[])])]
make_maps_to ((x,[]):xs)
  = [ZCall (ZVar ("\\mapsto",[]))
    (ZTuple [ZVar (x,[]),ZVar ("val"++x,[])])]++(make_maps_to xs)
\end{code}

The function $get\_guard\_pair$ transform $CircGAction$ constructs into a list of tuples $(ZPred, CAction)$
\begin{code}
get_guard_pair :: CGActions -> [(ZPred, CAction)]
get_guard_pair (CircThenElse (CircGAction g2 a2) (CircGAction g3 a3))
  = [(g2,a2),(g3,a3)]
get_guard_pair (CircThenElse (CircGAction g1 a1) glx)
  = [(g1,a1)]++(get_guard_pair glx)
\end{code}

The function $mk\_guard\_pair$ transforms a list of tuples $(ZPred, CAction)$ and produces $CircThenElse$ pieces according to the size of the list.
\begin{code}
mk_guard_pair :: [(ZPred, CAction)] -> CGActions
mk_guard_pair [(g,a)]
  = (CircGAction g (omega_prime_CAction a))
mk_guard_pair ((g,a):ls)
  = (CircThenElse (CircGAction g (omega_prime_CAction a)) (mk_guard_pair ls))
\end{code}
% \subsection{Adding permanent bits of the new \Circus specification ($MemoryMerge$, $MRG$, etc)}

TODO: this function here should somehow propagate any parameter from a replicated operator

EX: [] i: {a,b,c} @ x.i -> SKIP
   = x.a -> SKIP [] x.b -> SKIP [] x.c -> SKIP
EX: [] i: {a,b,c} @ A(x)
   = A(a) [] A(b) [] A(c)
\begin{code}
propagate_CSPRep (CActionSchemaExpr e) = (CActionSchemaExpr e)
propagate_CSPRep (CActionCommand c) = (CActionCommand c) 
propagate_CSPRep (CActionName n) = (CActionName n) 
propagate_CSPRep (CSPSkip) = (CSPSkip) 
propagate_CSPRep (CSPStop ) = (CSPStop ) 
propagate_CSPRep (CSPChaos) = (CSPChaos) 
propagate_CSPRep (CSPCommAction c a) = (CSPCommAction c (propagate_CSPRep a)) 
propagate_CSPRep (CSPGuard p a) = (CSPGuard p (propagate_CSPRep a)) 
propagate_CSPRep (CSPSeq a1 a2) = (CSPSeq (propagate_CSPRep a1) (propagate_CSPRep a2)) 
propagate_CSPRep (CSPExtChoice a1 a2) = (CSPExtChoice (propagate_CSPRep a1) (propagate_CSPRep a2)) 
propagate_CSPRep (CSPIntChoice a1 a2) = (CSPIntChoice (propagate_CSPRep a1) (propagate_CSPRep a2)) 
propagate_CSPRep (CSPNSParal n1 c n2 a1 a2) = (CSPNSParal n1 c n2 (propagate_CSPRep a1) (propagate_CSPRep a2)) 
propagate_CSPRep (CSPParal c a1 a2) = (CSPParal c (propagate_CSPRep a1) (propagate_CSPRep a2)) 
propagate_CSPRep (CSPNSInter n1 n2 a1 a2) = (CSPNSInter n1 n2 (propagate_CSPRep a1) (propagate_CSPRep a2)) 
propagate_CSPRep (CSPInterleave a1 a2) = (CSPInterleave (propagate_CSPRep a1) (propagate_CSPRep a2)) 
propagate_CSPRep (CSPHide a c) = (CSPHide (propagate_CSPRep a) c) 
propagate_CSPRep (CSPParAction n ls) = (CSPParAction n ls) 
propagate_CSPRep (CSPRenAction n r) = (CSPRenAction n r) 
propagate_CSPRep (CSPRecursion n a) = (CSPRecursion n (propagate_CSPRep a)) 
propagate_CSPRep (CSPUnParAction ls a n) = (CSPUnParAction ls (propagate_CSPRep a) n) 
propagate_CSPRep (CSPRepExtChoice ls a) = (CSPRepExtChoice ls (propagate_CSPRep a)) 
propagate_CSPRep (CSPRepIntChoice ls a) = (CSPRepIntChoice ls (propagate_CSPRep a)) 
propagate_CSPRep (CSPRepParalNS c ls n a) = (CSPRepParalNS c ls n (propagate_CSPRep a)) 
propagate_CSPRep (CSPRepParal c ls a) = (CSPRepParal c ls (propagate_CSPRep a)) 
propagate_CSPRep (CSPRepInterlNS ls n a) = (CSPRepInterlNS ls n (propagate_CSPRep a)) 
propagate_CSPRep (CSPRepInterl ls a) = (CSPRepInterl ls (propagate_CSPRep a)) 
\end{code}


\begin{code}
make_memory_proc =
  CParAction "Memory" (CircusAction (CActionCommand (CVResDecl [Choose ("b",[]) (ZVar ("BINDING",[]))] (CSPExtChoice (CSPExtChoice (CSPRepExtChoice [Choose ("n",[]) (ZCall (ZVar ("\\dom",[])) (ZVar ("b",[])))] (CSPCommAction (ChanComm "mget" [ChanDotExp (ZVar ("n",[])),ChanOutExp (ZCall (ZVar ("b",[])) (ZVar ("n",[])))]) (CSPParAction "Memory" [ZVar ("b",[])]))) (CSPRepExtChoice [Choose ("n",[]) (ZCall (ZVar ("\\dom",[])) (ZVar ("b",[])))] (CSPCommAction (ChanComm "mset" [ChanDotExp (ZVar ("n",[])),ChanInpPred "nv" (ZMember (ZVar ("nv",[])) (ZCall (ZVar ("\\delta",[])) (ZVar ("n",[]))))]) (CSPParAction "Memory" [ZCall (ZVar ("\\oplus",[])) (ZTuple [ZVar ("b",[]),ZSetDisplay [ZCall (ZVar ("\\mapsto",[])) (ZTuple [ZVar ("n",[]),ZVar ("nv",[])])]])])))) (CSPCommAction (ChanComm "terminate" []) CSPSkip)))))
\end{code}
