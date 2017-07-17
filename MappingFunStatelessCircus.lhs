
\chapter{Mapping Functions - Stateless Circus}
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
  omega_ProcessDef
)
where
import Subs
import AST
import OmegaDefs
import Data.List hiding (union, intersect)
import FormatterToCSP
import CRL
\end{code}

\begin{code}
omega_Circus :: [ZPara] -> [ZPara]
omega_Circus spec
  = [ZGivenSetDecl ("UNIVERSE",[]),
      ZFreeTypeDef ("NAME",[]) names,
      ZAbbreviation ("BINDINGS",[]) (ZCall (ZVar ("\\fun",[])) (ZTuple [ZVar ("NAME",[]),ZVar ("UNIVERSE",[])])), 
      ZAbbreviation ("\\delta",[]) (ZSetDisplay deltamap),
      CircChannel [CChanDecl "mget" (ZCross [ZVar ("NAME",[]),ZVar ("UNIVERSE",[])]), CChanDecl "mset" (ZCross [ZVar ("NAME",[]),ZVar ("UNIVERSE",[])])],
      CircChannel [CChan "terminate"],
      CircChanSet "MEM_I" (CChanSet ["mset","mget","terminate"])]
    ++ (omega_Circus_aux spec1 spec1)
    where 
      spec1 = (map (rename_vars_ZPara' (def_mem_st_Circus_aux spec spec)) spec) -- renaming variables for highlighting which state var is from which process
      names = (def_delta_name (def_mem_st_Circus_aux spec spec))
      deltamap = (def_delta_mapping (def_mem_st_Circus_aux spec spec))
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
  = (CGenProcess zn (x:xs) (omega_ProcessDef zn spec pd))
omega_ProcDecl spec (CProcess zn pd)
  = (CProcess zn (omega_ProcessDef zn spec pd))
\end{code}

\subsection{Mapping Circus Processes Definition}
\begin{code}
omega_ProcessDef :: ZName -> [ZPara] -> ProcessDef -> ProcessDef
omega_ProcessDef zn spec (ProcDefSpot xl pd)
  = (ProcDefSpot xl (omega_ProcessDef zn spec pd))
omega_ProcessDef zn spec (ProcDefIndex xl pd)
  = (ProcDefIndex xl (omega_ProcessDef zn spec pd))
omega_ProcessDef zn spec (ProcDef cp)
  = (ProcDef (omega_CProc zn spec cp))
\end{code}

\subsection{Mapping Circus Processes}
Note: $CGenProc$ ($N[Exp^{+}]$), $CSimpIndexProc$, and $CParamProc$ ($N(Exp^{+})$) are not yet implemented.
\begin{code}
omega_CProc :: ZName -> [ZPara] -> CProc -> CProc
omega_CProc zn spec (CExtChoice a b)
  = (CExtChoice (omega_CProc zn spec a) (omega_CProc zn spec b))
omega_CProc zn spec (CHide a cs)
  = (CHide (omega_CProc zn spec a) cs)
omega_CProc zn spec (CIntChoice a b)
  = (CIntChoice (omega_CProc zn spec a) (omega_CProc zn spec b))
omega_CProc zn spec (CInterleave a b)
  = (CInterleave (omega_CProc zn spec a) (omega_CProc zn spec b))
omega_CProc zn spec (CircusProc zns)
  = (CircusProc zns)
omega_CProc zn spec (CParParal cs a b)
  = (CParParal cs (omega_CProc zn spec a) (omega_CProc zn spec b))
omega_CProc zn spec (CRepExtChProc [(Choose x s)] a)
  = (CRepExtChProc [(Choose x s)] (omega_CProc zn spec a))
omega_CProc zn spec (CRepIntChProc [(Choose x s)] a)
  = (CRepIntChProc [(Choose x s)] (omega_CProc zn spec a))
omega_CProc zn spec (CRepInterlProc [(Choose x s)] a)
  = (CRepInterlProc [(Choose x s)] (omega_CProc zn spec a))
omega_CProc zn spec (CRepParalProc cse [(Choose x s)] a)
  = (CRepParalProc cse [(Choose x s)] (omega_CProc zn spec a))
omega_CProc zn spec (CRepSeqProc [(Choose x s)] a)
  = (CRepSeqProc [(Choose x s)] (omega_CProc zn spec a))
omega_CProc zn spec (CSeq a b)
  = (CSeq (omega_CProc zn spec a) (omega_CProc zn spec b))
omega_CProc zn spec (ProcStalessMain [] ca)
  = (ProcStalessMain 
    [make_memory_proc] 
    main_action)
    where 
      omegaAC = omega_CAction ca
      refAC = isRefined' omegaAC (runRefinement omegaAC)
      main_action = refAC
omega_CProc zn spec (ProcStalessMain xls ca)
  = (ProcStalessMain 
    [make_memory_proc] 
    main_action)
    where 
      -- newLocVar = map rename_actions_loc_var xls
      -- remRecAct = map recursive_PPar newLocVar
      remRecAct = map recursive_PPar xls
      expAct = map (expand_action_names_PPar remRecAct) remRecAct
      nomegaAC = (expand_action_names_CAction expAct ca)
      omegaAC = omega_CAction nomegaAC
      refAC = isRefined' omegaAC (runRefinement omegaAC)
      main_action = refAC
omega_CProc zn spec (CGenProc zns (x:xs))
  = (CGenProc zns (x:xs))
omega_CProc zn spec (CParamProc zns (x:xs))
  = (CParamProc zns (x:xs))
omega_CProc zn spec (CSimpIndexProc zns (x:xs))
  = (CSimpIndexProc zns (x:xs))

omega_CProc zn spec (ProcMain zp xls ca)
  = (ProcStalessMain 
    [make_memory_proc] 
    main_action)
    where 
      nstate = filter_main_action_bind zn $ (def_mem_st_Circus_aux spec spec)
      -- newLocVar = map rename_actions_loc_var xls
      -- remRecAct = map recursive_PPar newLocVar
      remRecAct = map recursive_PPar xls
      expAct = map (expand_action_names_PPar remRecAct) remRecAct
      nomegaAC = (expand_action_names_CAction expAct ca)
      omegaAC = omega_CAction nomegaAC
      refAC = isRefined' omegaAC (runRefinement omegaAC)
      main_action = mk_main_action_bind nstate $ refAC

omega_CProc zn spec x
  = x
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
omega_CAction (CSPCommAction (ChanComm c [ChanDotExp e]) a)
  = make_get_com lxs (rename_vars_CAction (CSPCommAction (ChanComm c [ChanDotExp e]) (omega_prime_CAction a)))
  where lxs = remdups $ concat (map get_ZVar_st (free_var_ZExpr e))
omega_CAction (CSPCommAction (ChanComm c ((ChanDotExp e):xs)) a)
  = make_get_com lxs (rename_vars_CAction (CSPCommAction (ChanComm c ((ChanDotExp e):xs)) (omega_prime_CAction a)))
  where lxs = remdups $ concat (map get_ZVar_st (free_var_ZExpr e))
\end{code}

\begin{circus}
\Omega_A (c!e(v_0,\ldots,v_n,l_0,\ldots,l_m) \then A) \circdef
\\\t2 c.e(v_0,\ldots,v_n,l_0,\ldots,l_m) \then A
\end{circus}
\begin{code}
omega_CAction (CSPCommAction (ChanComm c [ChanOutExp e]) a)
  = omega_CAction (CSPCommAction (ChanComm c [ChanDotExp e]) a)
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
  where lxs = remdups $ concat (map get_ZVar_st (free_var_ZPred g))
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
omega_CAction (CSPCommAction (ChanComm c [ChanInpPred x p]) a)
  = case not (elem x (getWrtV(a))) of
    True -> make_get_com lsx (rename_vars_CAction (CSPCommAction
             (ChanComm c [ChanInpPred x p])
                 (omega_prime_CAction a)))
    _  -> (CSPCommAction (ChanComm c [ChanInpPred x p]) a)
  where lsx = remdups $ concat (map get_ZVar_st (free_var_ZPred p))
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
  = make_get_com lsx (CSPExtChoice (omega_prime_CAction ca) (omega_prime_CAction cb))
   where
    lsx = remdups $ concat $ map get_ZVar_st $ free_var_CAction (CSPExtChoice ca cb)
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
-- omega_CAction (CSPNSParal ns1 cs ns2 a1 a2)
--   = make_get_com lsx (rename_vars_CAction (CSPHide
--    (CSPNSParal NSExpEmpty (CSExpr "MEMi") NSExpEmpty
--      (CSPNSParal NSExpEmpty cs NSExpEmpty
--       (CSPHide
--        (CSPNSParal NSExpEmpty (CSExpr "MEMi") NSExpEmpty
--         (CSPSeq a1 (CSPCommAction (ChanComm "terminate" []) CSPSkip))
--         (CSPParAction "MemoryMerge"
--          [ZSetDisplay [],
--                 ZVar ("LEFT",[])]))
--        (CSExpr "MEMi"))
--       (CSPHide
--        (CSPNSParal NSExpEmpty (CSExpr "MEMi") NSExpEmpty
--         (CSPSeq a2 (CSPCommAction (ChanComm "terminate" []) CSPSkip))
--         (CSPParAction "MemoryMerge"
--          [ZSetDisplay [],
--                 ZVar ("RIGHT",[])]))
--        (CSExpr "MEMi")))
--       (CActionName "Merge"))
--       (CChanSet ["mleft","mright"])))
--    where
--     lsx = union (map fst (remdups (free_var_CAction a1))) (map fst (remdups (free_var_CAction a2)))
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
omega_CAction (CSPRepParalNS (CSExpr cs) [Choose (x,[]) (ZSetDisplay lsx)] (NSExprParam ns [ZVar (x1,[])]) act)
  = (CSPRepParalNS (CSExpr cs) [Choose (x,[]) (ZSetDisplay lsx)] (NSExprParam ns [ZVar (x1,[])]) (omega_CAction act))
\end{code}
\begin{circus}
\Omega_A ( \circval Decl \circspot P) \circdef \circval Decl \circspot \Omega_A (P)
\end{circus}
is written in Haskell as:
\begin{code}
omega_CAction (CActionCommand (CValDecl xs a))
  = (CActionCommand (CValDecl xs (omega_CAction a)))
\end{code}
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
  = make_get_com (remdups $ concat (map get_ZVar_st varls))  (make_set_com omega_CAction varls (map rename_ZExpr valls) CSPSkip)
\end{code}

\begin{circus}
\Omega_A (A \circhide cs) \circdef \Omega_A (A) \circhide cs
\end{circus}

is written in Haskell as:

\begin{code}
omega_CAction (CSPHide a cs) = (CSPHide (omega_CAction a) cs)
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
omega_CAction (CActionCommand (CIf gax))
  = make_get_com lsx (CActionCommand (CIf (mk_guard_pair omega_prime_CAction (rename_guard_pair lsx gpair))))
  where
   gpair = get_guard_pair gax
   lsx = concat (map get_ZVar_st (remdups (concat (map free_var_ZPred (map fst gpair)))))
\end{code}
% \begin{circus}
% \Omega_A (\circif g (v_0,...,v_n,l_0,...,l_m) \circthen A \circfi ) \defs
%    \\\t1 get.v_0?vv_0 \then \ldots \then get.v_n?vv_n \then
%    \\\t1 get.l_0?vl_0 \then \ldots \then get.l_m?vl_m \then
%    \\\t1\circif g (v_0,...,v_n,l_0,...,l_m) \circthen \Omega'_A (A) \circfi
% \end{circus}
% \begin{code}
% omega_CAction (CActionCommand (CIf (CircGAction g a)))
%   = make_get_com lsx (rename_vars_CAction (CActionCommand
%              (CIf (CircGAction g (omega_prime_CAction a)))))
%   where
%    lsx = remdups $ concat $ map get_ZVar_st $ remdups $ free_var_ZPred g
% \end{code}

\begin{circus}
\Omega_A (\circmu X \circspot A(X)) \circdef \circmu X \circspot \Omega_A(A(X))
\end{circus}

is written in Haskell as:

\begin{code}
--  TODO Jun 30 2017: rename the recursion action name, so it won't clash with any Circus action name.
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
\end{code}

In order to pattern match any other \Circus\ construct not mentioned here, we propagate the $omega\_CAction$ function to the remainder of the constructs.

\begin{code}
omega_CAction (CActionSchemaExpr vZSExpr) = (CActionSchemaExpr vZSExpr)
-- omega_CAction (CActionCommand vCCommand) = (CActionCommand vCCommand)
omega_CAction (CActionName vZName) = (CActionName vZName)
omega_CAction (CSPCommAction vComm vCAction) = (CSPCommAction vComm (omega_CAction vCAction))
-- omega_CAction (CSPGuard vZPred vCAction) = (CSPGuard vZPred (omega_CAction vCAction))
-- omega_CAction (CSPSeq v1CAction v2CAction) = (CSPSeq (omega_CAction (omega_CAction v1CAction)) (omega_CAction v2CAction))
-- omega_CAction (CSPExtChoice v1CAction v2CAction) = (CSPExtChoice (omega_CAction v1CAction) (omega_CAction v2CAction))
-- omega_CAction (CSPIntChoice v1CAction v2CAction) = (CSPIntChoice (omega_CAction v1CAction) (omega_CAction v2CAction))
omega_CAction (CSPNSParal v1NSExp vCSExp v2NSExp v1CAction v2CAction) = (CSPNSParal v1NSExp vCSExp v2NSExp (omega_CAction v1CAction) (omega_CAction v2CAction))
omega_CAction (CSPParal vCSExp v1CAction v2CAction) = (CSPParal vCSExp (omega_CAction v1CAction) (omega_CAction v2CAction))
omega_CAction (CSPNSInter v1NSExp v2NSExp v1CAction v2CAction) = (CSPNSInter v1NSExp v2NSExp (omega_CAction v1CAction) (omega_CAction v2CAction))
omega_CAction (CSPInterleave v1CAction v2CAction) = (CSPInterleave (omega_CAction v1CAction) (omega_CAction v2CAction))
-- omega_CAction (CSPHide vCAction vCSExp) = (CSPHide (omega_CAction vCAction) vCSExp)
omega_CAction (CSPParAction vZName vZExpr_lst) = (CSPParAction vZName vZExpr_lst)
omega_CAction (CSPRenAction vZName vCReplace) = (CSPRenAction vZName vCReplace)
-- omega_CAction (CSPRecursion vZName vCAction) = (CSPRecursion vZName (omega_CAction vCAction))
omega_CAction (CSPUnfAction vZName vCAction) = (CSPUnfAction vZName (omega_CAction vCAction))
omega_CAction (CSPUnParAction vZGenFilt_lst vCAction vZName) = (CSPUnParAction vZGenFilt_lst (omega_CAction vCAction) vZName)
omega_CAction (CSPRepSeq vZGenFilt_lst vCAction) = (CSPRepSeq vZGenFilt_lst (omega_CAction vCAction))
omega_CAction (CSPRepExtChoice vZGenFilt_lst vCAction) = (CSPRepExtChoice vZGenFilt_lst (omega_CAction vCAction))
omega_CAction (CSPRepIntChoice vZGenFilt_lst vCAction) = (CSPRepIntChoice vZGenFilt_lst (omega_CAction vCAction))
omega_CAction (CSPRepParalNS vCSExp vZGenFilt_lst vNSExp vCAction) = (CSPRepParalNS vCSExp vZGenFilt_lst vNSExp (omega_CAction vCAction))
omega_CAction (CSPRepParal vCSExp vZGenFilt_lst vCAction) = (CSPRepParal vCSExp vZGenFilt_lst (omega_CAction vCAction))
omega_CAction (CSPRepInterlNS vZGenFilt_lst vNSExp vCAction) = (CSPRepInterlNS vZGenFilt_lst vNSExp (omega_CAction vCAction))
omega_CAction (CSPRepInterl vZGenFilt_lst vCAction) = (CSPRepInterl vZGenFilt_lst (omega_CAction vCAction))
omega_CAction x = x
\end{code}

% NOTE: Besides the transformation rules for $[g]$ and ${g}$, the remaining transformation rules from page 91 of the D24.1 document, were not yet implemented.
\subsection{Definitions of $\Omega'_{A}$}

\begin{circus}
\Omega'_A (\Skip) \circdef \Skip
\also \Omega'_A (\Stop) \circdef \Stop
\also \Omega'_A (\Chaos) \circdef \Chaos
\end{circus}
is written in Haskell as:
\begin{code}
omega_prime_CAction :: CAction -> CAction
omega_prime_CAction CSPSkip = CSPSkip
omega_prime_CAction CSPStop = CSPStop
omega_prime_CAction CSPChaos = CSPChaos
\end{code}

\begin{circus}
\Omega'_A (c \then A) \circdef c \then \Omega'_A (A)
\end{circus}

is written in Haskell as:
\begin{code}
omega_prime_CAction (CSPCommAction (ChanComm c []) a)
  = (CSPCommAction (ChanComm c []) (omega_prime_CAction a))
\end{code}


\begin{circus}
\Omega'_A (c.e \then A) \circdef c(vv_0,...,vv_n,vl_0,...,vl_m) \then \Omega'_A (A)
\end{circus}

is written in Haskell as:
\begin{code}
omega_prime_CAction (CSPCommAction (ChanComm c [ChanDotExp e]) a) 
  = (CSPCommAction (ChanComm c [ChanDotExp (rename_ZExpr e)]) (omega_prime_CAction a))
\end{code}

\begin{circus}
\Omega'_A (c!e \then A) \circdef
\\\t2 c.e \then A
\end{circus}
\begin{code}
omega_prime_CAction (CSPCommAction (ChanComm c [ChanOutExp e]) a)
  = omega_prime_CAction (CSPCommAction (ChanComm c [ChanDotExp e]) a)
omega_prime_CAction (CSPCommAction (ChanComm c ((ChanOutExp e):xs)) a)
  = omega_prime_CAction (CSPCommAction (ChanComm c ((ChanDotExp e):xs)) a)
\end{code}

\begin{circus}
\Omega'_A (g \then A) \circdef
\\\t2 g \circguard \Omega'_{A} (A)
\end{circus}
is written in Haskell as:
\begin{code}
omega_prime_CAction (CSPGuard g a)
  = (CSPGuard (rename_ZPred g) (omega_prime_CAction a))
\end{code}


I'm considering $x?k \neq x?k : P$ and I'm making the translation straightforward:

\begin{circus}
\Omega'_A (c?x \then A) \circdef
\\\t2 c?x \then \Omega'_{A} (A)
\end{circus}

is written in Haskell as:
\begin{code}
omega_prime_CAction (CSPCommAction (ChanComm c [ChanInp (x:xs)]) a)
  = (CSPCommAction (ChanComm c [ChanInp (x:xs)]) (omega_prime_CAction a))
\end{code}


\begin{circus}
\Omega'_A (c?x : P \then A) \circdef
\\\t2 c?x : P \then \Omega'_{A} (A)
\end{circus}
where
\begin{circus}
x \in wrtV(A)
\end{circus}

is written in Haskell as:

\begin{code}
omega_prime_CAction (CSPCommAction (ChanComm c [ChanInpPred x p]) a)
  = (CSPCommAction (ChanComm c [ChanInpPred x p])
                 (omega_prime_CAction a))
\end{code}

\begin{circus}
\Omega'_A (A_1 \circseq A_2) \circdef \Omega'_A (A_1) \circseq \Omega_A (A_2)
\end{circus}
is written in Haskell as:
\begin{code}
omega_prime_CAction (CSPSeq ca cb)
  = (CSPSeq (omega_prime_CAction ca) (omega_CAction cb))
\end{code}

\begin{circus}
\Omega'_A (A_1 \intchoice A_2) \circdef \Omega'_A (A_1) \intchoice \Omega'_A (A_2)
\end{circus}
is written in Haskell as:
\begin{code}
omega_prime_CAction (CSPIntChoice ca cb)
  = (CSPIntChoice (omega_prime_CAction ca) (omega_prime_CAction cb))
\end{code}

% TODO: I need to somehow calculate the $FV(A_1)$ and $FV(A_2)$. What should I do?
\begin{circus}
\Omega'_A (A_1 \extchoice A_2) \circdef
\\\t2 (\Omega'_A (A_1) \extchoice \Omega'_A (A_2))
\end{circus}
is written in Haskell as:
\begin{code}
omega_prime_CAction (CSPExtChoice ca cb)
  = (CSPExtChoice (omega_prime_CAction ca) (omega_prime_CAction cb))
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
-- omega_prime_CAction (CSPNSParal ns1 cs ns2 a1 a2)
--   = make_get_com lsx (rename_vars_CAction (CSPHide
--    (CSPNSParal NSExpEmpty (CSExpr "MEMi") NSExpEmpty
--      (CSPNSParal NSExpEmpty cs NSExpEmpty
--       (CSPHide
--        (CSPNSParal NSExpEmpty (CSExpr "MEMi") NSExpEmpty
--         (CSPSeq a1 (CSPCommAction (ChanComm "terminate" []) CSPSkip))
--         (CSPParAction "MemoryMerge"
--          [ZSetDisplay [],
--                 ZVar ("LEFT",[])]))
--        (CSExpr "MEMi"))
--       (CSPHide
--        (CSPNSParal NSExpEmpty (CSExpr "MEMi") NSExpEmpty
--         (CSPSeq a2 (CSPCommAction (ChanComm "terminate" []) CSPSkip))
--         (CSPParAction "MemoryMerge"
--          [ZSetDisplay [],
--                 ZVar ("RIGHT",[])]))
--        (CSExpr "MEMi")))
--       (CActionName "Merge"))
--       (CChanSet ["mleft","mright"])))
--    where
--     lsx = union (map fst (remdups (free_var_CAction a1))) (map fst (remdups (free_var_CAction a2)))
\end{code}

\begin{circus}
\Omega'_A (\Semi x : \langle v_1,...,v_n \rangle \circspot A(x)) \circdef \Omega'_A (A(v_1)\circseq \ldots \circseq A(v_n))
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
\Omega'_A (\Extchoice x : \langle v_1,...,v_n \rangle \circspot A(x)) \circdef \Omega'_A (A(v_1)\extchoice \ldots \extchoice A(v_n))
\end{circus}
is written in Haskell as:
\begin{code}
omega_prime_CAction (CSPRepExtChoice [Choose (x,[]) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1,[])]))
  = case x == x1 of
    True -> omega_prime_CAction (rep_CSPRepExtChoice act xs)
    _  -> (CSPRepExtChoice [Choose (x,[]) (ZSeqDisplay xs)]
          (CSPParAction act [ZVar (x1,[])]))
omega_prime_CAction (CSPRepExtChoice [Choose (x,[]) v] act)
  = (CSPRepExtChoice [Choose (x,[]) v] (omega_prime_CAction act))
\end{code}

\begin{circus}
\Omega'_A (\Intchoice x : \langle v_1,...,v_n \rangle \circspot A(x)) \circdef \Omega'_A (A(v_1)\intchoice \ldots \intchoice A(v_n))
\end{circus}
is written in Haskell as:
\begin{code}
omega_prime_CAction (CSPRepIntChoice [Choose (x,[]) (ZSeqDisplay xs)]
          (CSPParAction act [ZVar (x1,[])]))
  = case x == x1 of
    True -> omega_prime_CAction(rep_CSPRepIntChoice act xs)
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
      \Omega'_A(A(v_n -1))
      \\ \lpar ns(v_n -1 ) | cs | ns(v_n) \rpar
      \\ A(v_n)\end{array}\right )\end{array}\right )\end{array}\right )

\end{circus}
is written in Haskell as:
\begin{code}
omega_prime_CAction (CSPRepParalNS (CSExpr cs) [Choose (x,[]) (ZSetDisplay lsx)]
          (NSExprParam ns [ZVar (x1,[])])
          (CSPParAction a [ZVar (x2,[])]))
  = case (x == x1) && (x == x2) of
    True -> omega_prime_CAction (rep_CSPRepParalNS a cs ns x lsx)
    _  -> (CSPRepParalNS (CSExpr cs) [Choose (x,[]) (ZSetDisplay lsx)]
          (NSExprParam ns [ZVar (x1,[])])
          (CSPParAction a [ZVar (x2,[])]))
omega_prime_CAction (CSPRepParalNS (CSExpr cs) [Choose (x,[]) (ZSetDisplay lsx)] (NSExprParam ns [ZVar (x1,[])]) act)
  = (CSPRepParalNS (CSExpr cs) [Choose (x,[]) (ZSetDisplay lsx)] (NSExprParam ns [ZVar (x1,[])]) (omega_prime_CAction act))
\end{code}
\begin{circus}
\Omega'_A ( \circval Decl \circspot P) \circdef \circval Decl \circspot \Omega'_A (P)
\end{circus}
is written in Haskell as:
\begin{code}
omega_prime_CAction (CActionCommand (CValDecl xs a))
  = (CActionCommand (CValDecl xs (omega_prime_CAction a)))
\end{code}
\begin{circus}
\Omega'_A \left (\begin{array}{l}x_0,\ldots,x_n:=e_0,\ldots,e_n\end{array}\right ) \circdef
\\\t1 set.x_0!e_0 \then
\\\t1\ldots\then
\\\t1 set.x_n!e_n \then \Skip
\end{circus}

\begin{code}
omega_prime_CAction (CActionCommand (CAssign varls valls))
  =  (make_set_com omega_prime_CAction varls valls CSPSkip)
\end{code}
% \begin{circus}
% \Omega'_A (\circif g \circthen A \circfi ) \defs
%    \\\t1\circif g \circthen \Omega'_A (A) \circfi
% \end{circus}
% \begin{code}
% omega_prime_CAction (CActionCommand (CIf (CircGAction g a)))
%   = (CActionCommand (CIf (CircGAction g (omega_prime_CAction a))))

% \end{code}

\begin{circus}
\Omega'_A (A \circhide cs) \circdef \Omega'_A (A) \circhide cs
\end{circus}

is written in Haskell as:

\begin{code}
omega_prime_CAction (CSPHide a cs) = (CSPHide (omega_prime_CAction a) cs)
\end{code}

\begin{circus}
\Omega'_A
   \left (\begin{array}{l}
   \circif g_0  \circthen A_0
   \\\t1\circelse \ldots
   \\\t1 \circelse g_n  \circthen A_n
   \\\circfi
   \end{array}\right ) \defs
   \\\t1\circif g_0 \circthen \Omega'_A (A_0)
   \\\t2\circelse \ldots
   \\\t2 \circelse g_n \circthen \Omega'_A (A_n)
   \\\t1\circfi
\end{circus}

\begin{code}
omega_prime_CAction (CActionCommand (CIf glx))
  = (CActionCommand (CIf (mk_guard_pair omega_prime_CAction guard_pair)))
  where
   guard_pair = get_guard_pair glx
\end{code}

\begin{circus}
\Omega'_A (\circmu X \circspot A(X)) \circdef \circmu X \circspot \Omega'_A(A(X))
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
      \Omega'_A(A(v_n -1))
      \\ \lpar ns(v_n -1 ) | ns(v_n)\rpar
      \\ A(v_n)\end{array}\right )\end{array}\right )\end{array}\right )

\end{circus}

is written in Haskell as:

\begin{code}
omega_prime_CAction (CSPRepInterlNS [Choose (x,[]) (ZSetDisplay lsx)]
          (NSExprParam ns [ZVar (x1,[])])
          (CSPParAction a [ZVar (x2,[])]))
  = case (x == x1) && (x == x2) of
    True -> omega_prime_CAction (rep_CSPRepInterlNS a ns x lsx)
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

In order to pattern match any other \Circus\ construct not mentioned here, we propagate the $omega\_CAction$ function to the remainder of the constructs.

\begin{code}
omega_prime_CAction (CActionSchemaExpr vZSExpr) = (CActionSchemaExpr vZSExpr)
-- omega_prime_CAction (CActionCommand vCCommand) = (CActionCommand vCCommand)
omega_prime_CAction (CActionName vZName) = (CActionName vZName)
omega_prime_CAction (CSPCommAction vComm vCAction) = (CSPCommAction vComm (omega_prime_CAction vCAction))
-- omega_prime_CAction (CSPGuard vZPred vCAction) = (CSPGuard vZPred (omega_prime_CAction vCAction))
-- omega_prime_CAction (CSPSeq v1CAction v2CAction) = (CSPSeq (omega_prime_CAction (omega_prime_CAction v1CAction)) (omega_prime_CAction v2CAction))
-- omega_prime_CAction (CSPExtChoice v1CAction v2CAction) = (CSPExtChoice (omega_prime_CAction v1CAction) (omega_prime_CAction v2CAction))
-- omega_prime_CAction (CSPIntChoice v1CAction v2CAction) = (CSPIntChoice (omega_prime_CAction v1CAction) (omega_prime_CAction v2CAction))
omega_prime_CAction (CSPNSParal v1NSExp vCSExp v2NSExp v1CAction v2CAction) = (CSPNSParal v1NSExp vCSExp v2NSExp (omega_prime_CAction v1CAction) (omega_prime_CAction v2CAction))
omega_prime_CAction (CSPParal vCSExp v1CAction v2CAction) = (CSPParal vCSExp (omega_prime_CAction v1CAction) (omega_prime_CAction v2CAction))
omega_prime_CAction (CSPNSInter v1NSExp v2NSExp v1CAction v2CAction) = (CSPNSInter v1NSExp v2NSExp (omega_prime_CAction v1CAction) (omega_prime_CAction v2CAction))
omega_prime_CAction (CSPInterleave v1CAction v2CAction) = (CSPInterleave (omega_prime_CAction v1CAction) (omega_prime_CAction v2CAction))
-- omega_prime_CAction (CSPHide vCAction vCSExp) = (CSPHide (omega_prime_CAction vCAction) vCSExp)
omega_prime_CAction (CSPParAction vZName vZExpr_lst) = (CSPParAction vZName vZExpr_lst)
omega_prime_CAction (CSPRenAction vZName vCReplace) = (CSPRenAction vZName vCReplace)
-- omega_prime_CAction (CSPRecursion vZName vCAction) = (CSPRecursion vZName (omega_prime_CAction vCAction))
omega_prime_CAction (CSPUnfAction vZName vCAction) = (CSPUnfAction vZName (omega_prime_CAction vCAction))
omega_prime_CAction (CSPUnParAction vZGenFilt_lst vCAction vZName) = (CSPUnParAction vZGenFilt_lst (omega_prime_CAction vCAction) vZName)
omega_prime_CAction (CSPRepSeq vZGenFilt_lst vCAction) = (CSPRepSeq vZGenFilt_lst (omega_prime_CAction vCAction))
omega_prime_CAction (CSPRepExtChoice vZGenFilt_lst vCAction) = (CSPRepExtChoice vZGenFilt_lst (omega_prime_CAction vCAction))
omega_prime_CAction (CSPRepIntChoice vZGenFilt_lst vCAction) = (CSPRepIntChoice vZGenFilt_lst (omega_prime_CAction vCAction))
omega_prime_CAction (CSPRepParalNS vCSExp vZGenFilt_lst vNSExp vCAction) = (CSPRepParalNS vCSExp vZGenFilt_lst vNSExp (omega_prime_CAction vCAction))
omega_prime_CAction (CSPRepParal vCSExp vZGenFilt_lst vCAction) = (CSPRepParal vCSExp vZGenFilt_lst (omega_prime_CAction vCAction))
omega_prime_CAction (CSPRepInterlNS vZGenFilt_lst vNSExp vCAction) = (CSPRepInterlNS vZGenFilt_lst vNSExp (omega_prime_CAction vCAction))
omega_prime_CAction (CSPRepInterl vZGenFilt_lst vCAction) = (CSPRepInterl vZGenFilt_lst (omega_prime_CAction vCAction))
omega_prime_CAction x = x
\end{code}

