\chapter{Mapping Functions - Stateless Circus}
Mapping Omega Functions from \Circus\ to \Circus

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
-- import FormatterToCSP
import CRL
\end{code}
}
\begin{omegaenv}
\begin{code}
omega_Circus :: [ZPara] -> [ZPara]
omega_Circus spec =
   [ZFreeTypeDef ("UNIVERSE",[],"") nuniv]++
        subuniv ++
\end{code}
\end{omegaenv}
\begin{omegaenv}
\begin{code}
   [ZFreeTypeDef ("NAME",[],"") names]++
    (def_sub_name zb)++
    (def_sub_bind zb) ++
     [ZAbbreviation ("BINDINGS",[],"")
        (ZCall (ZVar ("\\cup",[],""))
          (ZTuple (remdups $ def_sub_bindn zb)))]++
     (def_delta_mapping_t zb)++
         [CircChannel [CChanDecl "mget" (ZCross [ZVar ("NAME",[],""),ZVar ("UNIVERSE",[],"")]), CChanDecl "mset" (ZCross [ZVar ("NAME",[],""),ZVar ("UNIVERSE",[],"")])],
         CircChannel [CChan "terminate"],
         CircChanSet "MEMI" (CChanSet ["mset","mget","terminate"]),
         CircChannel [CChanDecl "lget" (ZCross [ZVar ("NAME",[],""),ZVar ("UNIVERSE",[],"")]), CChanDecl "lset" (ZCross [ZVar ("NAME",[],""),ZVar ("UNIVERSE",[],"")])],
         CircChannel [CChan "lterminate"],
         CircChanSet "MEML" (CChanSet ["lset","lget","lterminate"])]
         ++ (map (upd_type_ZPara (genfilt_names zb)) para)
       where
         spec0 = normal_state_proc spec spec
         spec1 = (map (rename_vars_ZPara' (def_mem_st_Circus_aux spec0 spec0)) spec0)
         (zb,para) = (omega_Circus_aux' spec1)
          -- renaming variables for highlighting which state var is from which process
         names = remdups (def_delta_name zb)
         deltamap = (def_delta_mapping zb)
         nuniv = remdups (def_new_universe zb)
         subuniv = remdups (def_sub_univ zb)
\end{code}
\end{omegaenv}
\section{Omega functions}
\begin{omegaenv}
\begin{code}

omega_Circus_aux' :: [ZPara] -> ([ZGenFilt],[ZPara])
omega_Circus_aux' spec
  = (zb,para)
  where
    res =(omega_Circus_aux spec spec)
    zb = concat (map fst res)
    para = (map snd res)

omega_Circus_aux :: [ZPara] -> [ZPara] -> [([ZGenFilt],ZPara)]
-- [x]
omega_Circus_aux _ [] = []
omega_Circus_aux spec
  [e@(Process (CProcess _ (ProcDefSpot _ (ProcDef (ProcMain _ _ _)))))]
  = [(zb,res)]
  where
    (zb,res) = proc_ref1 e
omega_Circus_aux spec
  [e@(Process (CProcess _ (ProcDef (ProcMain _ _ _))))]
  = [(zb,res)]
  where
    (zb,res) = proc_ref1 e
omega_Circus_aux spec
  [e@(Process (CProcess _ (ProcDefSpot _ (ProcDef (ProcStalessMain _ _)))))]
  = [(zb,res)]
  where
    (zb,res) = proc_ref1 e
omega_Circus_aux spec
  [e@(Process (CProcess _ (ProcDef (ProcStalessMain _ _))))]
  = [(zb,res)]
  where
    (zb,res) = proc_ref1 e
omega_Circus_aux spec [(Process cp)]
  = [((getType_ProcDecl cp),(Process (omega_ProcDecl spec cp)))]
omega_Circus_aux spec [x] = [([],x)]
-- e@(Process (CProcess _ (ProcDefSpot _ (ProcDef (ProcMain _ _ _)))))
-- x:xs
omega_Circus_aux spec
  (e@(Process (CProcess _ (ProcDefSpot _ (ProcDef (ProcMain _ _ _))))):xs)
  = [(zb,res)]++(omega_Circus_aux spec xs)
  where
    (zb,res) = proc_ref1 e
omega_Circus_aux spec
  (e@(Process (CProcess _ (ProcDef (ProcMain _ _ _)))):xs)
  = [(zb,res)]++(omega_Circus_aux spec xs)
  where
    (zb,res) = proc_ref1 e
omega_Circus_aux spec
  ((e@(Process (CProcess _ (ProcDefSpot _ (ProcDef (ProcStalessMain _ _)))))):xs)
  = [(zb,res)]++(omega_Circus_aux spec xs)
    where
      (zb,res) = proc_ref1 e
omega_Circus_aux spec
  ((e@(Process (CProcess _ (ProcDef (ProcStalessMain _ _))))):xs)
  = [(zb,res)]++(omega_Circus_aux spec xs)
    where
      (zb,res) = proc_ref1 e
omega_Circus_aux spec
  ((Process cp):xs)
  = [((getType_ProcDecl cp),(Process (omega_ProcDecl spec cp)))]
      ++(omega_Circus_aux spec xs)
-- omega_Circus_aux spec ((Process cp):xs)
--   = [([],(Process (omega_ProcDecl spec cp)))]++(omega_Circus_aux spec xs)
omega_Circus_aux spec (x:xs)
  = [([],x)]++(omega_Circus_aux spec xs)
\end{code}


\end{omegaenv}
\section{Mapping Circus Processes Declaration}

\begin{omegaenv}
\begin{code}
omega_ProcDecl :: [ZPara] -> ProcDecl -> ProcDecl
omega_ProcDecl spec (CGenProcess zn (x:xs) pd)
  = (CGenProcess zn (x:xs) (omega_ProcessDef zn spec pd))
omega_ProcDecl spec (CProcess zn pd)
  = (CProcess zn (omega_ProcessDef zn spec pd))
\end{code}
\end{omegaenv}
\section{Mapping Circus Processes Definition}
\begin{omegaenv}

\begin{code}
omega_ProcessDef :: ZName -> [ZPara] -> ProcessDef -> ProcessDef
omega_ProcessDef zn spec (ProcDefSpot xl pd)
  = (ProcDefSpot xl (omega_ProcessDef zn spec pd))
omega_ProcessDef zn spec (ProcDefIndex xl pd)
  = (ProcDefIndex xl (omega_ProcessDef zn spec pd))
omega_ProcessDef zn spec (ProcDef cp)
  = (ProcDef (omega_CProc zn spec cp))
\end{code}
\end{omegaenv}
\section{Mapping Circus Processes with $begin$ and $end$}
This is the implementation of the entire refinement process end-to-end
from the description of the Deliverable 24.1, page 83 and 84. All of
the refinement actions and processes are split in boxes, with the steps.
What I did here is to implement that sequence of steps in such a way
that the functions are recursive until the last refinement step of the
second iteration of refinement strategy.
\begin{argue}
  \circprocess P\circdef\\
  \quad
    \begin{array}{l}
      \circbegin\\
        \quad
        \begin{array}{l}
        \circstate State \defs [ v_0 : T_0; \ldots ; v_n : T_n | inv(v_0,\ldots,v_n) ]\\
         P.Actions \defs_{\Delta} P.State\\
        \circspot MA(v_0,\ldots,v_n,l_0,\ldots,l_m)\\
      \end{array}\\
    \circend\\
    \end{array}
\\= & Action Refinement\\
\end{argue}
\begin{code}
proc_ref1 (Process (CProcess p (ProcDefSpot x (ProcDef (ProcMain st aclst ma)))))
  = rest11
  where
    remRecAct = map recursive_PPar aclst
    expAct = map (expand_action_names_PPar remRecAct []) remRecAct
    nomegaAC = (expand_action_names_CAction expAct [] ma)
    refAC = isRefined' nomegaAC (runRefinement nomegaAC)
    rest11 = proc_ref2 (Process (CProcess p (ProcDefSpot x (ProcDef (ProcMain st [] refAC)))))

proc_ref1 (Process (CProcess p (ProcDefSpot x (ProcDef (ProcStalessMain aclst ma)))))
  = rest11
  where
    remRecAct = map recursive_PPar aclst
    expAct = map (expand_action_names_PPar remRecAct []) remRecAct
    nomegaAC = (expand_action_names_CAction expAct [] ma)
    refAC = isRefined' nomegaAC (runRefinement nomegaAC)
    rest11 = proc_ref2 (Process (CProcess p (ProcDefSpot x (ProcDef (ProcStalessMain [] refAC)))))
proc_ref1 (Process (CProcess p (ProcDef (ProcMain st aclst ma))))
  = rest11
  where
    remRecAct = map recursive_PPar aclst
    expAct = map (expand_action_names_PPar remRecAct []) remRecAct
    nomegaAC = (expand_action_names_CAction expAct [] ma)
    refAC = isRefined' nomegaAC (runRefinement nomegaAC)
    rest11 = proc_ref2 (Process (CProcess p (ProcDef (ProcMain st [] refAC))))

proc_ref1 (Process (CProcess p (ProcDef (ProcStalessMain aclst ma))))
  = rest11
  where
    remRecAct = map recursive_PPar aclst
    expAct = map (expand_action_names_PPar remRecAct []) remRecAct
    nomegaAC = (expand_action_names_CAction expAct [] ma)
    refAC = isRefined' nomegaAC (runRefinement nomegaAC)
    rest11 = proc_ref2 (Process (CProcess p (ProcDef (ProcStalessMain [] refAC))))
proc_ref1 x = ([],x)
\end{code}
\begin{argue}
  \\= & Action Refinement\\
  \circprocess P\circdef\\
  \quad
    \begin{array}{l}
      \circbegin\\
        \quad
        \begin{array}{l}
        \circstate State \defs [ v_0 : T_0; \ldots ; v_n : T_n | inv(v_0,\ldots,v_n) ]\\
        % P.Actions \defs_{\Delta} P.State\\
        \circspot \circvar l_0: U_0; \ldots ; l_m;U_m \circspot
        MA(v_0,\ldots,v_n,l_0,\ldots,l_m)\\
      \end{array}\\
    \circend\\
    \end{array}
  \\= & Process Refinement, $crl\_prom\_var\_state$, $crl\_prom\_var\_state2$\\
\end{argue}
\begin{code}
proc_ref2 :: ZPara -> ([ZGenFilt],ZPara)
proc_ref2 e@(Process (CProcess p (ProcDef
      (ProcMain (ZSchemaDef (ZSPlain x) (ZSchema zs)) aclst ma))))
  = case ref of
      Just xe@(Process (CProcess pq (ProcDef
          (ProcMain (ZSchemaDef (ZSPlain xa) (ZSchema xzs)) aclsta maa)))) ->
        (xzs++(getType_CAction ma),(proc_ref3 xe))
      Nothing -> (zs++(getType_CAction ma),(proc_ref3 e))
  where ref = runRefinementZp e
proc_ref2 e@(Process (CProcess p (ProcDef (ProcStalessMain aclst ma))))
  = case ref of
      Just xe@(Process (CProcess pq (ProcDef
          (ProcMain (ZSchemaDef (ZSPlain xa) (ZSchema xzs)) aclsta maa)))) ->
        (xzs++(getType_CAction ma),(proc_ref3 xe))
      Nothing ->([]++(getType_CAction ma),(proc_ref3 e))
  where ref = runRefinementZp e
proc_ref2 e@(Process (CProcess p (ProcDefSpot x1a (ProcDef
      (ProcMain (ZSchemaDef (ZSPlain x) (ZSchema zs)) aclst ma)))))
  = case ref of
      Just xe@(Process (CProcess pq (ProcDefSpot x1a (ProcDef
          (ProcMain (ZSchemaDef (ZSPlain xa) (ZSchema xzs)) aclsta maa))))) ->
        (xzs++(getType_CAction ma),(proc_ref3 xe))
      Nothing -> (zs++(getType_CAction ma),(proc_ref3 e))
  where ref = runRefinementZp e
proc_ref2 e@(Process (CProcess p (ProcDefSpot x1a (ProcDef (ProcStalessMain aclst ma)))))
  = case ref of
      Just xe@(Process (CProcess pq (ProcDefSpot x1a (ProcDef
          (ProcMain (ZSchemaDef (ZSPlain xa) (ZSchema xzs)) aclsta maa))))) ->
        (xzs++(getType_CAction ma),(proc_ref3 xe))
      Nothing ->([]++(getType_CAction ma),(proc_ref3 e))
  where ref = runRefinementZp e
proc_ref2 x = ([],x)
\end{code}
\begin{argue}
  \\= & Process Refinement, $crl\_prom\_var\_state$, $crl\_prom\_var\_state2$\\
  \qquad\begin{array}{l}
  \circprocess P\circdef\\
  \qquad
    \begin{array}{l}
      \circbegin\\
        \qquad
        \begin{array}{l}
        \circstate S \defs [ v_0 : T_0; \ldots ; v_n : T_n; l_0: U_0; \ldots ; l_m;U_m | inv(v_0,\ldots,v_n) ]\\
        \ldots\\
        \circspot A(v_0,\ldots,v_n,l_0,\ldots,l_m)
      \end{array}\\
    \circend\\
    \end{array}
  \end{array}
  \\= & Data Refinement\\
\end{argue}
\begin{code}
proc_ref3 (Process (CProcess p
   (ProcDef (ProcMain (ZSchemaDef (ZSPlain sn) (ZSchema stv)) aclst ma))))
  =  proc_ref4 (Process (CProcess p
   (ProcDef (ProcMain (ZSchemaDef (ZSPlain sn) (ZSchema bst)) aclst ma))))
  where bst = data_refinement stv
proc_ref3 (Process (CProcess p
  (ProcDefSpot xa (ProcDef (ProcMain (ZSchemaDef (ZSPlain sn) (ZSchema stv)) aclst ma)))))
  =  proc_ref4 (Process (CProcess p
    (ProcDefSpot xa (ProcDef (ProcMain (ZSchemaDef (ZSPlain sn) (ZSchema bst)) aclst ma)))))
  where bst = data_refinement stv
proc_ref3 x = proc_ref4 x
\end{code}

\begin{argue}
  \\= & Data Refinement\\
  \qquad\begin{array}{l}
  \circprocess P\circdef\\
  \qquad
    \begin{array}{l}
      \circbegin\\
        \qquad
        \begin{array}{l}
        \circstate S \defs [ b : BINDING | b(v_0) \in T_0 \land \ldots \land inv(b(v_0),\ldots,b(v_n)) ]\\
        \ldots\\
        \circspot A(b(v_0),\ldots,b(v_n),b(l_0),\ldots,b(l_m))
      \end{array}\\
    \circend\\
    \end{array}
  \end{array}
  \\= & Action Refinement\\
\end{argue}
\begin{code}
proc_ref4 (Process (CProcess p (ProcDef (ProcMain (ZSchemaDef (ZSPlain sn) (ZSchema bst)) aclst ma))))
  =  proc_ref5 (Process (CProcess p
    (ProcDef (ProcMain (ZSchemaDef (ZSPlain sn) (ZSchema bst))
    ((nmem_mkMemoryTYPVar bst)++
    (nmem_mkMemoryTYP bst)++
    (nmem_mkMemory bst)++
    (nmem_mkMemoryMergeTYPVar bst)++
    (nmem_mkMemoryMergeTYP bst)++
    (nmem_mkMemoryMerge bst))
    (CActionCommand (CVarDecl [Choose ("b",[],[]) nbd]
    (CSPHide (CSPNSParal [] (CSExpr "MEMI") nbst
      (CSPSeq nma (CSPCommAction (ChanComm "terminate" []) CSPSkip))
       (CSPParAction "Memory" nbst)) (CSExpr "MEMI"))))))))
  where
    nma = isRefined' (omega_CAction ma) (runRefinement (omega_CAction ma))
    ne = sub_pred (make_subinfo (mk_subinfo_bndg nbst)
            (varset_from_zvars (map fst (mk_subinfo_bndg nbst))))
            (head $ filter_ZGenFilt_Check bst)
    nbd = ZSetComp ((filter_ZGenFilt_Choose bst)++[Check ne]) Nothing
    nbst = remdups (filter_bnd_var $ filter_ZGenFilt_Choose bst)
proc_ref4 (Process (CProcess p (ProcDefSpot xa (ProcDef (ProcMain (ZSchemaDef (ZSPlain sn) (ZSchema bst)) aclst ma)))))
  =  proc_ref5 (Process (CProcess p
    (ProcDefSpot xa (ProcDef (ProcMain (ZSchemaDef (ZSPlain sn) (ZSchema bst))
    ((nmem_mkMemoryTYPVar bst)++
    (nmem_mkMemoryTYP bst)++
    (nmem_mkMemory bst)++
    (nmem_mkMemoryMergeTYPVar bst)++
    (nmem_mkMemoryMergeTYP bst)++
    (nmem_mkMemoryMerge bst))
    (CActionCommand (CVarDecl [Choose ("b",[],[]) nbd]
    (CSPHide (CSPNSParal [] (CSExpr "MEMI") nbst
      (CSPSeq nma (CSPCommAction (ChanComm "terminate" []) CSPSkip))
       (CSPParAction "Memory" nbst)) (CSExpr "MEMI")))))))))
  where
    nma = isRefined' (omega_CAction ma) (runRefinement (omega_CAction ma))
    ne = sub_pred (make_subinfo (mk_subinfo_bndg nbst)
            (varset_from_zvars (map fst (mk_subinfo_bndg nbst))))
            (head $ filter_ZGenFilt_Check bst)
    nbd = ZSetComp ((filter_ZGenFilt_Choose bst)++[Check ne]) Nothing
    nbst = remdups (filter_bnd_var $ filter_ZGenFilt_Choose bst)
proc_ref4 x = proc_ref5 x
\end{code}
\begin{argue}
  \\= & Action Refinement\\
  \qquad\begin{array}{l}
  \circprocess P'\circdef\\
  \qquad
    \begin{array}{l}
      \circbegin\\
        \qquad
        \begin{array}{l}
        \circstate S \defs [ b : BINDING | b(v_0) \in T_0 \land \ldots \land inv(b(v_0),\ldots,b(v_n)) ]\\
        Memory \circdef\\
        \qquad\begin{array}{l}
          \circvres b : BINDING \circspot \\
          \qquad \begin{array}{l}
          (\Extchoice n: \dom\ b \circspot mget.n!b(n) \then Memory(b))\\
          \extchoice \left(\begin{array}{l}
          \Extchoice n: \dom\ b \circspot\\
          \qquad
          mset.n?nv : (nv \in \delta(n)) \then Memory(b \oplus {n \mapsto nv})
          \end{array}\right)\\
          \extchoice~terminate \then \Skip
          \end{array}
          \end{array} \\
        MemoryMerge \circdef\\
        \qquad\begin{array}{l}
          \circvres b : BINDING \\
          \qquad \begin{array}{l}
          (\Extchoice n: \dom\ b \circspot lget.n!b(n) \then MemoryMerge(b))\\
          \extchoice \left(\begin{array}{l}
          \Extchoice n: \dom\ b \circspot\\
          \qquad
          lset.n?nv : (nv \in \delta(n)) \then MemoryMerge(b \oplus {n \mapsto nv})
          \end{array}\right)\\
          \extchoice~lterminate \then \left(\begin{array}{l}\Semi n : ns \circspot\left(\begin{array}{l}\lcircguard n \in \dom\ b \rcircguard \circguard mset.n.b(n)\then \Skip\\\extchoice \\\lcircguard n \notin \dom\ b \rcircguard \circguard \Skip\end{array}\right)\end{array}\right)
          \end{array}
          \end{array}\\
        \circspot \circvar b :
          \left\{\begin{array}{l}
          x : BINDING | \begin{array}{l}
            x(v_0) \in T_0 \land \ldots \land inv(x(v_0),\ldots,x(v_n))
          \end{array}\end{array}\right\} \circspot\\
          \qquad \left(\begin{array}{l}
            \left(\begin{array}{l}
              \Omega_A(A)\circseq\\terminate \then \Skip
            \end{array}\right)\\
            \lpar \emptyset | MEMI | \{b\} \rpar\\
            Memory(b)
          \end{array}\right) \circhide MEMI
      \end{array}\\
    \circend\\
    \end{array}
  \end{array}
  \\= & Process Refinement\\
\end{argue}
\begin{code}
proc_ref5 (Process (CProcess p (ProcDef (ProcMain x as ma)))) =
  proc_ref6 (Process (CProcess p (ProcDef (ProcStalessMain as ma))))
proc_ref5 (Process (CProcess p (ProcDefSpot xa (ProcDef (ProcMain x as ma))))) =
  proc_ref6 (Process (CProcess p (ProcDefSpot xa (ProcDef (ProcStalessMain as ma)))))
proc_ref5 x = proc_ref6 x
\end{code}
\begin{argue}
  \\= & Process Refinement\\
  \qquad\begin{array}{l}
  \circprocess P'\circdef\\
  \qquad
    \begin{array}{l}
      \circbegin\\
        \qquad
        \begin{array}{l}
        Memory \circdef\\
        \qquad\begin{array}{l}
          \circvres b : BINDING \circspot \\
          \qquad \begin{array}{l}
          (\Extchoice n: \dom\ b \circspot mget.n!b(n) \then Memory(b))\\
          \extchoice \left(\begin{array}{l}
          \Extchoice n: \dom\ b \circspot\\
          \qquad
          mset.n?nv : (nv \in \delta(n)) \then Memory(b \oplus {n \mapsto nv})
          \end{array}\right)\\
          \extchoice~terminate \then \Skip
          \end{array}
          \end{array} \\
        \circspot \circvar b :
          \left\{\begin{array}{l}
          x : BINDING | \begin{array}{l}
            x(v_0) \in T_0 \land \ldots \land inv(x(v_0),\ldots,x(v_n))
          \end{array}\end{array}\right\} \circspot\\
          \qquad \left(\begin{array}{l}
            \left(\begin{array}{l}
              \Omega_A(A)\circseq\\terminate \then \Skip
            \end{array}\right)\\
            \lpar \emptyset | MEMI | \{b\} \rpar\\
            Memory(b)
          \end{array}\right) \circhide MEMI
      \end{array}\\
    \circend\\
    \end{array}
  \end{array}
  \\= & Action Refinement\\
\end{argue}
\begin{code}
proc_ref6 (Process (CProcess p (ProcDef (ProcStalessMain mem (CActionCommand (CVarDecl [Choose ("b",[],"") (ZSetComp bst Nothing)] ma ))))))
  = Process (CProcess p (ProcDefSpot (filter_ZGenFilt_Choose bst) (ProcDef (ProcStalessMain mem ma))))
proc_ref6 (Process (CProcess p (ProcDefSpot xa (ProcDef (ProcStalessMain mem (CActionCommand (CVarDecl [Choose ("b",[],"") (ZSetComp bst Nothing)] ma )))))))
  = Process (CProcess p (ProcDefSpot ((filter_ZGenFilt_Choose bst)++xa) (ProcDef (ProcStalessMain mem ma))))
proc_ref6 x = x
\end{code}
\begin{argue}
  \\= & Action Refinement\\
  \qquad\begin{array}{l}
  \circprocess P'\circdef b : BINDING\\
  \quad
    \begin{array}{l}
      \circbegin\\
        \quad
        \begin{array}{l}
        Memory \circdef\\
        \quad\begin{array}{l}
          \circvres b : BINDING \circspot \\
          \quad \begin{array}{l}
          (\Extchoice n: \dom\ b \circspot mget.n!b(n) \then Memory(b))\\
          \extchoice \left(\begin{array}{l}
          \Extchoice n: \dom\ b \circspot
          \begin{block}
            mset.n?nv : (nv \in \delta(n)) \then\\
            Memory(b \oplus \{n \mapsto nv\})
          \end{block}
          \end{array}\right)\\
          \extchoice~terminate \then \Skip
          \end{array}
          \end{array} \\
        \circspot
          \quad \left(\begin{array}{l}
            \left(\begin{array}{l}
              \Omega_A(A)\circseq\\terminate \then \Skip
            \end{array}\right) \lpar \emptyset | MEMI | \{b\} \rpar Memory(b)
          \end{array}\right) \circhide MEM_I
      \end{array}\\
    \circend\\
    \end{array}
  \end{array}
  \end{argue}


\section{Mapping Circus Processes}
So far we have no other mapping functions for these constructs. They are basically translated directly into CSP.
% Note: $CGenProc$ ($N[Exp^{+}]$), $CSimpIndexProc$, and $CParamProc$ ($N(Exp^{+})$) are not yet implemented.
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
omega_CProc zn spec (CGenProc zns (x:xs))
  = (CGenProc zns (x:xs))
omega_CProc zn spec (CParamProc zns (x:xs))
  = (CParamProc zns (x:xs))
omega_CProc zn spec (CSimpIndexProc zns (x:xs))
  = (CSimpIndexProc zns (x:xs))
omega_CProc zn spec x
  = x
\end{code}

\section{Mapping Parameterised Circus Actions}

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

\section{Stateless Circus - Actions}

\begin{omegaenv}
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
\end{omegaenv}
\begin{omegaenv}
\begin{circus}
\Omega_A (c \then A) \circdef c \then \Omega_A (A)
\end{circus}

is written in Haskell as:
\begin{code}
omega_CAction (CSPCommAction (ChanComm c []) a)
  = (CSPCommAction (ChanComm c []) (omega_CAction a))
\end{code}
\end{omegaenv}
\begin{omegaenv}
\begin{circus}
\Omega_A (c.e(v_0,\ldots,v_n,l_0,\ldots,l_m) \then A) \circdef
\\\t2 mget.v_0?vv_0 \then \ldots \then mget.v_n?vv_n \then
\\\t2 mget.l_0?vl_0 \then \ldots \then mget.l_m?vl_m \then
\\\t2 c.e(vv_0,\ldots,vv_n,vl_0,\ldots,vl_m) \then \Omega'_{A} (A)
\end{circus}
where
\begin{circus}
FV (e) = (v_0,\ldots,v_n,l_0,\ldots,l_m)
\end{circus}

is written in Haskell as:
\begin{code}
omega_CAction (CSPCommAction (ChanComm c fe) a) =
  case lxs of
      [] -> (CSPCommAction (ChanComm c fe) (omega_CAction a))
      _ -> make_get_com lxs (rename_vars_CAction (CSPCommAction (ChanComm c fe) (omega_prime_CAction a)))
  where e = getChanDotExpVar fe
        lxs = (remdups $ concat $ map get_ZVar_st $ concat $ map varset_to_zvars $ map free_var_ZExpr e)
\end{code}
\end{omegaenv}

Included by Artur - any prefixed action which does not uses any state variables should propagate $\Omega_A$ and not $\Omega'_A$.


\begin{omegaenv}
\begin{circus}
\Omega_A (c.e(v_0,\ldots,v_n,l_0,\ldots,l_m) \then A) \circdef
\\\t2 mget.v_0?vv_0 \then \ldots \then mget.v_n?vv_n \then
\\\t2 mget.l_0?vl_0 \then \ldots \then mget.l_m?vl_m \then
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
  where lxs = remdups $ concat (map get_ZVar_st $ varset_to_zvars (free_var_ZExpr e))
omega_CAction (CSPCommAction (ChanComm c ((ChanDotExp e):xs)) a)
  = make_get_com lxs (rename_vars_CAction (CSPCommAction (ChanComm c ((ChanDotExp e):xs)) (omega_prime_CAction a)))
  where lxs = remdups $ concat (map get_ZVar_st $ varset_to_zvars (free_var_ZExpr e))
\end{code}
\end{omegaenv}


Included by Artur - An input carrying a value named with a state variable is defined as an assignment to that, but as assignments are not allowed,
we directly make a mset with that value.

\begin{omegaenv}
\begin{circus}
\Omega_A (c?v_n \then A) \circdef
\\\t2 mget.v_0?vv_0 \then \ldots \then mget.v_n?vv_n \then
\\\t2 mget.l_0?vl_0 \then \ldots \then mget.l_m?vl_m \then
\\\t2 c.e(vv_0,\ldots,vv_n,vl_0,\ldots,vl_m) \then \Omega'_{A} (A)
\end{circus}
where
\begin{circus}
v_n \in StateVariables
\end{circus}
\begin{circus}
\Omega_A (c?x \then A) \circdef
\\\t2 c?x \then \Omega'_{A} (A)
\end{circus}

is written in Haskell as:
\begin{code}
omega_CAction (CSPCommAction (ChanComm c [ChanInp e]) a)
  = case is_ZVar_st e of
      True -> (CSPCommAction (ChanComm c [ChanInp (join_name "t" e)]) (make_set_com omega_CAction [(e,[],"")] [ZVar ((join_name "t" e),[],"")] a))
      False -> (CSPCommAction (ChanComm c [ChanInp e]) (omega_CAction a))
omega_CAction (CSPCommAction (ChanComm c ((ChanInp e):xs)) a)
  = case is_ZVar_st e of
      True -> (CSPCommAction
        (ChanComm c
          ( (ChanInp (join_name "t" e)):
            ( map (\e -> (ChanInp (join_name "t" e))) ( map getChanName xs))))
            (make_set_com
              omega_CAction
              ((e,[],""):( map (\e -> (e,[],"")) ( map getChanName xs)))
              ((ZVar ((join_name "t" e),[],"")):
                (map (\e -> (ZVar ((join_name "t" e),[],"")))
                  ( map getChanName xs))) a))

      False -> (CSPCommAction (ChanComm c ((ChanInp e):xs)) (omega_CAction a))
\end{code}
\end{omegaenv}

\begin{omegaenv}
\begin{code}
omega_CAction (CSPInterleave a b) = (CSPInterleave (omega_CAction a) (omega_CAction b))
\end{code}
\end{omegaenv}
\begin{omegaenv}
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
\end{omegaenv}
\begin{omegaenv}
\begin{circus}
\Omega_A (g(v_0,\ldots,v_n,l_0,\ldots,l_m) \then A) \circdef
\\\t2 mget.v_0?vv_0 \then \ldots \then mget.v_n?vv_n \then
\\\t2 mget.l_0?vl_0 \then \ldots \then mget.l_m?vl_m \then
\\\t2 g(vv_0,\ldots,vv_n,vl_0,\ldots,vl_m) \circguard \Omega'_{A} (A)
\end{circus}
is written in Haskell as:
\begin{code}
omega_CAction (CSPGuard g a)
  -- 24/01/2018 - I think CSP won't accept the mgets before the guard, and therefore, it needs to be omega_CAction again.
  = make_get_com lxs (rename_vars_CAction (CSPGuard (rename_ZPred g) (omega_CAction a)))
  -- = make_get_com lxs (rename_vars_CAction (CSPGuard (rename_ZPred g) (omega_prime_CAction a)))
  where lxs = concat (map get_ZVar_st $ get_v_ZPred g)
  -- where lxs = remdups $ concat (map get_ZVar_st $ get_v_ZPred g)
\end{code}

\end{omegaenv}
\begin{omegaenv}

\begin{circus}
\Omega_A (c?x : P(x,v_0,\ldots,v_n,l_0,\ldots,l_m) \then A) \circdef
\\\t2 mget.v_0?vv_0 \then \ldots \then mget.v_n?vv_n \then
\\\t2 mget.l_0?vl_0 \then \ldots \then mget.l_m?vl_m \then
\\\t2 c?x : P(x,vv_0,\ldots,vv_n,vl_0,\ldots,vl_m) \then \Omega'_{A} (A)
\end{circus}
where
\begin{circus}
x \in wrtV(A)
\end{circus}

is written in Haskell as:
\begin{code}
omega_CAction (CSPCommAction (ChanComm c [ChanInpPred x p]) a)
  = case not (elem x (wrtV(a))) of
    True -> make_get_com lsx (rename_vars_CAction (CSPCommAction
             (ChanComm c [ChanInpPred x p])
                 (omega_prime_CAction a)))
    _  -> (CSPCommAction (ChanComm c [ChanInpPred x p]) a)
  where lsx = remdups $ concat (map get_ZVar_st $ varset_to_zvars (free_var_ZPred p))
\end{code}
\end{omegaenv}
\begin{omegaenv}


\begin{circus}
\Omega_A (A_1 \circseq A_2) \circdef \Omega_A (A_1) \circseq \Omega_A (A_2)
\end{circus}
is written in Haskell as:
\begin{code}
omega_CAction (CSPSeq ca cb)
  = (CSPSeq (omega_CAction ca) (omega_CAction cb))
\end{code}
\end{omegaenv}
\begin{omegaenv}
\begin{circus}
\Omega_A (A_1 \intchoice A_2) \circdef \Omega_A (A_1) \intchoice \Omega_A (A_2)
\end{circus}
is written in Haskell as:
\begin{code}
omega_CAction (CSPIntChoice ca cb)
  = (CSPIntChoice (omega_CAction ca) (omega_CAction cb))
\end{code}
\end{omegaenv}
\begin{omegaenv}
% TODO: I need to somehow calculate the $FV(A_1)$ and $FV(A_2)$. What should I do?
\begin{circus}
\Omega_A (A_1 \extchoice A_2) \circdef
\\\t1 mget.v_0?vv_0 \then \ldots \then mget.v_n?vv_n \then
\\\t1 mget.l_0?vl_0 \then \ldots \then mget.l_m?vl_m \then
\\\t2 (\Omega'_A (A_1) \extchoice \Omega'_A (A_2))
\end{circus}
is written in Haskell as:
\begin{code}
omega_CAction (CSPExtChoice ca cb)
  = make_get_com lsx (CSPExtChoice (omega_prime_CAction ca) (omega_prime_CAction cb))
   where
    lsx = remdups $ concat $ map get_ZVar_st $ varset_to_zvars $ free_var_CAction (CSPExtChoice ca cb)
\end{code}
\end{omegaenv}
\begin{omegaenv}
  % \begin{circus}
% \Omega_A (A1 \lpar ns1 | cs | ns2 \rpar A2) \circdef
% \\\t1 mget.v_0?vv_0 \then \ldots \then mget.v_n?vv_n \then
% \\\t1 mget.l_0?vl_0 \then \ldots \then mget.l_m?vl_m \then
%       \\\t2\left (\begin{array}{l}
%        \left (\begin{array}{l}
%         \left (\begin{array}{l}
%          \left (\begin{array}{l}
%           \Omega'_A (A_1) \circseq terminate \then \Skip
%          \end{array}\right )\\
%           \lpar \{\} | MEMI | \{\} \rpar
%           \\ MemoryMerge(\{v0 \mapsto vv0,\ldots\},ns1)
%         \end{array}\right )
%         \circhide MEMI \\
%        \lpar \{\} | cs | \{\} \rpar \\
%         \left (\begin{array}{l}
%          \left (\begin{array}{l}
%           \Omega'_A (A_2) \circseq terminate \then \Skip
%          \end{array}\right )\\
%           \lpar \{\} | MEMI | \{\} \rpar
%           \\ MemoryMerge(\{v0 \mapsto vv0,\ldots\},ns2)
%         \end{array}\right )
%         \circhide MEMI
%        \end{array}\right )
%     \end{array}\right )\\
% \end{circus}

\begin{circus}
\Omega_A (A1 \lpar ns1 | cs | ns2 \rpar A2) \circdef
\\\t1 mget.v_0?vv_0 \then \ldots \then mget.v_n?vv_n \then
\\\t1 mget.l_0?vl_0 \then \ldots \then mget.l_m?vl_m \then
      \\\t2\left (\begin{array}{l}
       \left (\begin{array}{l}
        \left (\begin{array}{l}
         \left (\begin{array}{l}
          \Omega'_A (A_1) \circseq lterminate \then \Skip
         \end{array}\right )\\
          \lpar \{\} | MEML | \{\} \rpar
          \\ MemoryMerge(\{v0 \mapsto vv0,\ldots\},ns1)
        \end{array}\right )
        \circhide MEML \\
       \lpar \{\} | cs | \{\} \rpar \\
        \left (\begin{array}{l}
         \left (\begin{array}{l}
          \Omega'_A (A_2) \circseq lterminate \then \Skip
         \end{array}\right )\\
          \lpar \{\} | MEML | \{\} \rpar
          \\ MemoryMerge(\{v0 \mapsto vv0,\ldots\},ns2)
        \end{array}\right )
        \circhide MEML
       \end{array}\right )
    \end{array}\right )
\end{circus}

The definition of parallel composition (and interleaving), as defined in the D24.1, has a $MemoryMerge$, $MRG_I$ and $Merge$ components and channel sets. Whilst translating them into CSP, the tool would rather expand their definition

\begin{code}
omega_CAction (CSPNSParal [ZVar ("\\emptyset",[],"")] cs [ZVar ("\\emptyset",[],"")] a1 a2)
  = make_get_com lsx
      (CSPNSParal [] cs []
      (CSPSeq (gamma_prime_CAction a1) (CSPCommAction (ChanComm "lterminate" []) CSPSkip))
      (CSPSeq (gamma_prime_CAction a2) (CSPCommAction (ChanComm "lterminate" []) CSPSkip)))
   where
    lsx = concat (map get_ZVar_st (remdups (varset_to_zvars (union_varset (free_var_CAction a1) (free_var_CAction a2)))))
omega_CAction (CSPNSParal [ZVar ("\\emptyset",[],"")] cs [ZSetDisplay ns2] a1 a2)
  = make_get_com lsx
      (CSPNSParal [] cs []
      (CSPHide
       (CSPNSParal [] (CSExpr "MEML") []
        (CSPSeq (gamma_prime_CAction a1) (CSPCommAction (ChanComm "lterminate" []) CSPSkip))
        (CSPParAction "MemoryMerge"
         [ZSetDisplay (mk_var_v_var_bnds $ zvar_to_zexpr lsx),ZSeqDisplay []]))
       (CSExpr "MEML"))
      (CSPHide
       (CSPNSParal [] (CSExpr "MEML") []
        (CSPSeq (gamma_prime_CAction a2) (CSPCommAction (ChanComm "lterminate" []) CSPSkip))
        (CSPParAction "MemoryMerge"
         [ZSetDisplay (mk_var_v_var_bnds $ zvar_to_zexpr lsx),ZSeqDisplay ns2]))
       (CSExpr "MEML")))
   where
    lsx = concat (map get_ZVar_st (remdups (varset_to_zvars (union_varset (free_var_CAction a1) (free_var_CAction a2)))))
omega_CAction (CSPNSParal [ZSetDisplay ns1] cs [ZVar ("\\emptyset",[],"")] a1 a2)
  = make_get_com lsx
      (CSPNSParal [] cs []
      (CSPHide
       (CSPNSParal [] (CSExpr "MEML") []
        (CSPSeq (gamma_prime_CAction a1) (CSPCommAction (ChanComm "lterminate" []) CSPSkip))
        (CSPParAction "MemoryMerge"
         [ZSetDisplay (mk_var_v_var_bnds $ zvar_to_zexpr lsx),ZSeqDisplay ns1]))
       (CSExpr "MEML"))
      (CSPHide
       (CSPNSParal [] (CSExpr "MEML") []
        (CSPSeq (gamma_prime_CAction a2) (CSPCommAction (ChanComm "lterminate" []) CSPSkip))
        (CSPParAction "MemoryMerge"
         [ZSetDisplay (mk_var_v_var_bnds $ zvar_to_zexpr lsx),ZSeqDisplay []]))
       (CSExpr "MEML")))
   where
    lsx = concat (map get_ZVar_st (remdups (varset_to_zvars (union_varset (free_var_CAction a1) (free_var_CAction a2)))))
omega_CAction (CSPNSParal [ZSetDisplay ns1] cs [ZSetDisplay ns2] a1 a2)
  = make_get_com lsx
      (CSPNSParal [] cs []
      (CSPHide
       (CSPNSParal [] (CSExpr "MEML") []
        (CSPSeq (gamma_prime_CAction a1) (CSPCommAction (ChanComm "lterminate" []) CSPSkip))
        (CSPParAction "MemoryMerge"
         [ZSetDisplay (mk_var_v_var_bnds $ zvar_to_zexpr lsx),ZSeqDisplay ns1]))
       (CSExpr "MEML"))
      (CSPHide
       (CSPNSParal [] (CSExpr "MEML") []
        (CSPSeq (gamma_prime_CAction a2) (CSPCommAction (ChanComm "lterminate" []) CSPSkip))
        (CSPParAction "MemoryMerge"
         [ZSetDisplay (mk_var_v_var_bnds $ zvar_to_zexpr lsx),ZSeqDisplay ns2]))
       (CSExpr "MEML")))
   where
    lsx = concat (map get_ZVar_st (remdups (varset_to_zvars (union_varset (free_var_CAction a1) (free_var_CAction a2)))))
\end{code}
\end{omegaenv}
\begin{omegaenv}
\begin{circus}
\Omega_A (\Semi x : \langle v_1,...,v_n \rangle \circspot A(x)) \circdef \Omega_A (A(v_1)\circseq \ldots \circseq A(v_n))
\end{circus}
is written in Haskell as:
\begin{code}
{-
omega_CAction (CSPRepSeq [Choose (x,[],tx) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1,[],tx1)]))
  = case x == x1 of
    True -> omega_CAction (rep_CSPRepSeq act xs)
    _  -> (CSPRepSeq [Choose (x,[],tx) (ZSeqDisplay xs)]
          (CSPParAction act [ZVar (x1,[],tx1)]))-}
omega_CAction (CSPRepSeq [Choose (x,[],tx) v] act)
  = (CSPRepSeq [Choose (x,[],tx) v] (omega_CAction act))
\end{code}
\end{omegaenv}
\begin{omegaenv}
\begin{circus}
\Omega_A (\Extchoice x : \langle v_1,...,v_n \rangle \circspot A(x)) \circdef \Omega_A (A(v_1)\extchoice \ldots \extchoice A(v_n))
\end{circus}
is written in Haskell as:
\begin{code}
omega_CAction (CSPRepExtChoice [Choose (x,[],tx) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1,[],tx1)]))
  = case x == x1 of
    True -> omega_CAction (rep_CSPRepExtChoice act xs)
    _  -> (CSPRepExtChoice [Choose (x,[],tx) (ZSeqDisplay xs)]
          (CSPParAction act [ZVar (x1,[],tx1)]))
omega_CAction (CSPRepExtChoice [Choose (x,[],tx) v] act)
  = (CSPRepExtChoice [Choose (x,[],tx) v] (omega_CAction act))
\end{code}
\end{omegaenv}
\begin{omegaenv}
\begin{circus}
\Omega_A (\Intchoice x : \langle v_1,...,v_n \rangle \circspot A(x)) \circdef \Omega_A (A(v_1)\intchoice \ldots \intchoice A(v_n))
\end{circus}
is written in Haskell as:
\begin{code}
omega_CAction (CSPRepIntChoice [Choose (x,[],tx) (ZSeqDisplay xs)]
          (CSPParAction act [ZVar (x1,[],tx1)]))
  = case x == x1 of
    True -> omega_CAction(rep_CSPRepIntChoice act xs)
    _  -> (CSPRepIntChoice [Choose (x,[],tx) (ZSeqDisplay xs)]
          (CSPParAction act [ZVar (x1,[],tx1)]))
omega_CAction (CSPRepIntChoice [Choose (x,[],tx) v] act)
  = (CSPRepIntChoice [Choose (x,[],tx) v] (omega_CAction act))
\end{code}
\end{omegaenv}
\begin{omegaenv}
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
omega_CAction (CSPRepParalNS (CSExpr cs) [Choose x (ZSetDisplay lsx)]
          [ZVar (x1,[],tx1)]
          (CSPParAction a [ZVar (x2,[],tx2)]))
  = case (member (ZVar x) [ZVar (x1,[],tx1)]) && (member (ZVar x) [ZVar (x2,[],tx2)]) of
    True -> omega_CAction (rep_CSPRepParalNS a cs (x1,[],tx1) x lsx)
    _  -> (CSPRepParalNS (CSExpr cs) [Choose x (ZSetDisplay lsx)]
          [ZVar (x1,[],tx1)]
          (CSPParAction a [ZVar (x2,[],tx2)]))
omega_CAction (CSPRepParalNS (CSExpr cs) [Choose x (ZSetDisplay lsx)] [ZVar (x1,[],tx1)] act)
  = (CSPRepParalNS (CSExpr cs) [Choose x (ZSetDisplay lsx)] [ZVar (x1,[],tx1)] (omega_CAction act))
\end{code}
\end{omegaenv}
\begin{omegaenv}
\begin{circus}
\Omega_A ( \circval Decl \circspot P) \circdef \circval Decl \circspot \Omega_A (P)
\end{circus}
is written in Haskell as:
\begin{code}
omega_CAction (CActionCommand (CValDecl xs a))
  = (CActionCommand (CValDecl xs (omega_CAction a)))
\end{code}
\end{omegaenv}
\begin{omegaenv}
\begin{circus}
\Omega_A \left (\begin{array}{l}x_0,\ldots,x_n:=e_0\left (\begin{array}{l}v_0,...,v_n,\\l_0,...,l_m\end{array}\right ),\ldots,e_n\left (\begin{array}{l}v_0,...,v_n,\\l_0,...,l_m\end{array}\right )\end{array}\right ) \circdef
\\\t1 mget.v_0?vv_0 \then \ldots \then mget.v_n?vv_n \then
\\\t1 mget.l_0?vl_0 \then \ldots \then mget.l_m?vl_m \then
\\\t1 set.x_0!e_0(vv_0,...,vv_n,vl_0,...,vl_m) \then
\\\t1\ldots\then
\\\t1 set.x_n!e_n(vv_0,...,vv_n,vl_0,...,vl_m) \then \Skip
\end{circus}

\begin{code}
omega_CAction (CActionCommand (CAssign varls valls))
  = make_get_com lxs (make_set_com omega_CAction varls (map rename_ZExpr valls) CSPSkip)
    where
      lxsvalls = (concat (map get_ZVar_st (varset_to_zvars $ union_varsets (map fvars_expr valls))))
      lxs = remdups lxsvalls
\end{code}
\end{omegaenv}
\begin{omegaenv}
\begin{circus}
\Omega_A (A \circhide cs) \circdef \Omega_A (A) \circhide cs
\end{circus}

is written in Haskell as:

\begin{code}
omega_CAction (CSPHide a cs) = (CSPHide (omega_CAction a) cs)
\end{code}
\end{omegaenv}
\begin{omegaenv}
\begin{circus}
\Omega_A
   \left (\begin{array}{l}
   \circif g_0 (v_0,...,v_n,l_0,...,l_m) \circthen A_0
   \\\t1\circelse \ldots
   \\\t1 \circelse g_n (v_0,...,v_n,l_0,...,l_m) \circthen A_n
   \\\circfi
   \end{array}\right ) \defs
   \\\t1 mget.v_0?vv_0 \then \ldots \then mget.v_n?vv_n \then
   \\\t1 mget.l_0?vl_0 \then \ldots \then mget.l_m?vl_m \then
   \\\t1\circif g_0 (v_0,...,v_n,l_0,...,l_m) \circthen \Omega'_A (A_0)
   \\\t2\circelse \ldots
   \\\t2 \circelse g_n (v_0,...,v_n,l_0,...,l_m) \circthen \Omega'_A (A_n)
   \\\t1\circfi
\end{circus}

\begin{code}
omega_CAction (CActionCommand (CIf gax))
-- = make_get_com lsx (CActionCommand (CIf (mk_guard_pair omega_prime_CAction (rename_guard_pair lsx gpair))))
  = make_get_com lsx (CActionCommand (CIf (mk_guard_pair omega_CAction (rename_guard_pair lsx gpair))))
  where
   gpair = get_guard_pair gax
   lsx = concat (map get_ZVar_st (remdups (concat (map (varset_to_zvars . free_var_ZPred) (map fst gpair)))))
\end{code}
% \begin{circus}
% \Omega_A (\circif g (v_0,...,v_n,l_0,...,l_m) \circthen A \circfi ) \defs
%    \\\t1 mget.v_0?vv_0 \then \ldots \then mget.v_n?vv_n \then
%    \\\t1 mget.l_0?vl_0 \then \ldots \then mget.l_m?vl_m \then
%    \\\t1\circif g (v_0,...,v_n,l_0,...,l_m) \circthen \Omega'_A (A) \circfi
% \end{circus}
% \begin{code}
% omega_CAction (CActionCommand (CIf (CircGAction g a)))
%   = make_get_com lsx (rename_vars_CAction (CActionCommand
%              (CIf (CircGAction g (omega_prime_CAction a)))))
%   where
%    lsx = remdups $ concat $ map get_ZVar_st $ remdups $ free_var_ZPred g
% \end{code}
\end{omegaenv}
\begin{omegaenv}
\begin{circus}
\Omega_A (\circmu X \circspot A(X)) \circdef \circmu X \circspot \Omega_A(A(X))
\end{circus}

is written in Haskell as:

\begin{code}
--  TODO Jun 30 2017: rename the recursion action name, so it won't clash with any Circus action name.
omega_CAction (CSPRecursion x c) = (CSPRecursion x (omega_CAction c))
\end{code}
\end{omegaenv}
\begin{omegaenv}
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
omega_CAction (CSPRepInterlNS [Choose x (ZSetDisplay lsx)]
          [ZVar (x1,[],tx1)]
          (CSPParAction a [ZVar (x2,[],tx2)]))
  = case (member (ZVar x) [ZVar (x1,[],tx1)]) && (member (ZVar x) [ZVar (x2,[],tx2)]) of
    True -> omega_CAction (rep_CSPRepInterlNS a (x1,[],tx1) x lsx)
    _  ->  (CSPRepInterlNS [Choose x (ZSetDisplay lsx)]
          [ZVar (x1,[],tx1)]
          (CSPParAction a [ZVar (x2,[],tx2)]))
omega_CAction (CSPRepInterlNS [Choose (x,[],tx) (ZSetDisplay lsx)]
          [ZVar (x1,[],tx1)]
          act)
  = (CSPRepInterlNS [Choose (x,[],tx) (ZSetDisplay lsx)]
          [ZVar (x1,[],tx1)]
          (omega_CAction act))
\end{code}
\end{omegaenv}
\begin{omegaenv}
\begin{circus}
\Omega_A (\{g\}) \circdef \prefixcolon [g, true]
\end{circus}

\begin{code}
omega_CAction (CActionCommand (CommandBrace g))
  = omega_CAction (CActionCommand (CPrefix g (ZTrue {reason = []})))
\end{code}
\end{omegaenv}
\begin{omegaenv}
\begin{circus}
\Omega_A ([g]) \circdef \prefixcolon [g]
\end{circus}

\begin{code}
omega_CAction (CActionCommand (CommandBracket g))
  = omega_CAction (CActionCommand (CPrefix1 g))
\end{code}
\end{omegaenv}
\begin{omegaenv}
\begin{circus}
\Omega_A (A[old_1,...,old_n := new_1,...,new_n) \circdef
\\\t1A[new_1,...,new_n/old_1,...,old_n)
\end{circus}
\end{omegaenv}
\begin{omegaenv}
\begin{code}
omega_CAction (CSPRenAction a (CRenameAssign left right))
  = (CSPRenAction a (CRename right left))
\end{code}
\end{omegaenv}
In order to pattern match any other \Circus\ construct not mentioned here, we propagate the $omega\_CAction$ function to the remainder of the constructs.

% I left the replicated operators for future work as they are similar to what I already implemented. Once I'm done with the verification bits, I'll get back here

\begin{omega
\begin{code}
omega_CAction (CActionSchemaExpr vZSExpr)
  = (CActionSchemaExpr vZSExpr)
omega_CAction (CActionName vZName)
  = (CActionName vZName)
omega_CAction (CSPCommAction vComm vCAction)
  = (CSPCommAction vComm (omega_CAction vCAction))
omega_CAction (CSPParal vCSExp v1CAction v2CAction)
  = (CSPParal vCSExp (omega_CAction v1CAction) (omega_CAction v2CAction))
omega_CAction (CSPNSInter v1NSExp v2NSExp v1CAction v2CAction)
  = (CSPNSInter v1NSExp v2NSExp (omega_CAction v1CAction) (omega_CAction v2CAction))
-- omega_CAction (CSPInterleave v1CAction v2CAction)
--   = (CSPInterleave (omega_CAction v1CAction) (omega_CAction v2CAction))
omega_CAction (CSPParAction vZName vZExpr_lst)
  = (CSPParAction vZName vZExpr_lst)
omega_CAction (CSPRenAction vZName vCReplace)
  = (CSPRenAction vZName vCReplace)
omega_CAction (CSPUnfAction vZName vCAction)
  = (CSPUnfAction vZName (omega_CAction vCAction))
omega_CAction (CSPUnParAction vZGenFilt_lst vCAction vZName)
  = (CSPUnParAction vZGenFilt_lst (omega_CAction vCAction) vZName)
omega_CAction x = x
\end{code}
\end{omegaenv}
% NOTE: Besides the transformation rules for $[g]$ and ${g}$, the remaining transformation rules from page 91 of the D24.1 document, were not yet implemented.
\section{Definitions of $\Omega'_{A}$}

\begin{omegaprime}
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
\end{omegaprime}
\begin{omegaprime}
\begin{circus}
\Omega'_A (c \then A) \circdef c \then \Omega'_A (A)
\end{circus}

is written in Haskell as:
\begin{code}
omega_prime_CAction (CSPCommAction (ChanComm c []) a)
  = (CSPCommAction (ChanComm c []) (omega_prime_CAction a))
\end{code}

\end{omegaprime}
\begin{omegaprime}

\begin{circus}
\Omega'_A (c.e \then A) \circdef c(vv_0,...,vv_n,vl_0,...,vl_m) \then \Omega'_A (A)
\end{circus}

is written in Haskell as:
\begin{code}
omega_prime_CAction (CSPCommAction (ChanComm c [ChanDotExp e]) a)
  = (CSPCommAction (ChanComm c [ChanDotExp (rename_ZExpr e)]) (omega_prime_CAction a))
\end{code}

\end{omegaprime}
\begin{omegaprime}
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

\end{omegaprime}
\begin{omegaprime}
\begin{circus}
\Omega'_A (g \then A) \circdef
\\\t2 g \circguard \Omega'_{A} (A)
\end{circus}
is written in Haskell as:
\begin{code}
omega_prime_CAction (CSPGuard g a)
  = (CSPGuard (rename_ZPred g) (omega_prime_CAction a))
\end{code}

\end{omegaprime}
\begin{omegaprime}

I'm considering $x?k \neq x?k : P$ and I'm making the translation straightforward:

\begin{circus}
\Omega'_A (c?x \then A) \circdef
\\\t2 c?x \then \Omega'_{A} (A)
\end{circus}

is written in Haskell as:
\begin{code}
omega_prime_CAction (CSPCommAction (ChanComm c [ChanInp e]) a)
  = case is_ZVar_st e of
      True -> (CSPCommAction (ChanComm c [ChanInp (join_name "t" e)]) (make_set_com omega_prime_CAction [(e,[],"")] [ZVar ((join_name "t" e),[],"")] a))
      False -> (CSPCommAction (ChanComm c [ChanInp e]) (omega_prime_CAction a))
omega_prime_CAction (CSPCommAction (ChanComm c ((ChanInp e):xs)) a)
  = case is_ZVar_st e of
      True -> (CSPCommAction (ChanComm c ((ChanInp (join_name "t" e)):xs)) (make_set_com omega_prime_CAction [(e,[],"")] [ZVar ((join_name "t" e),[],"")] a))
      False -> (CSPCommAction (ChanComm c ((ChanInp e):xs)) (omega_prime_CAction a))
\end{code}


\end{omegaprime}
\begin{omegaprime}
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
  = (CSPCommAction (ChanComm c [ChanInpPred x p]) (omega_prime_CAction a))
\end{code}

\end{omegaprime}
\begin{omegaprime}
\begin{circus}
\Omega'_A (A_1 \circseq A_2) \circdef \Omega'_A (A_1) \circseq \Omega_A (A_2)
\end{circus}
is written in Haskell as:
\begin{code}
omega_prime_CAction (CSPSeq ca cb)
  = (CSPSeq (omega_prime_CAction ca) (omega_CAction cb))
\end{code}

\end{omegaprime}
\begin{omegaprime}
\begin{circus}
\Omega'_A (A_1 \intchoice A_2) \circdef \Omega'_A (A_1) \intchoice \Omega'_A (A_2)
\end{circus}
is written in Haskell as:
\begin{code}
omega_prime_CAction (CSPIntChoice ca cb)
  = (CSPIntChoice (omega_prime_CAction ca) (omega_prime_CAction cb))
\end{code}

\end{omegaprime}
\begin{omegaprime}
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

\end{omegaprime}
\begin{omegaprime}
\begin{circus}
\Omega'_A (A1 \lpar ns1 | cs | ns2 \rpar A2) \circdef
\\\t1 mget.v_0?vv_0 \then \ldots \then mget.v_n?vv_n \then
\\\t1 mget.l_0?vl_0 \then \ldots \then mget.l_m?vl_m \then
      \\\t2\left (\begin{array}{l}
       \left (\begin{array}{l}
        \left (\begin{array}{l}
         \left (\begin{array}{l}
          \Omega'_A (A_1) \circseq terminate \then \Skip
         \end{array}\right )\\
          \lpar \{\} | MEMI | \{\} \rpar
          \\ MemoryMerge(\{v0 \mapsto vv0,\ldots\},LEFT)
        \end{array}\right )
        \circhide MEMI \\
       \lpar \{\} | cs | \{\} \rpar \\
        \left (\begin{array}{l}
         \left (\begin{array}{l}
          \Omega'_A (A_2) \circseq terminate \then \Skip
         \end{array}\right )\\
          \lpar \{\} | MEMI | \{\} \rpar
          \\ MemoryMerge(\{v0 \mapsto vv0,\ldots\},RIGHT)
        \end{array}\right )
        \circhide MEMI
       \end{array}\right )\\
      \lpar \{\} | MEMI | \{\} \rpar\\
      Merge
    \end{array}\right )\\
    \t2\circhide \lchanset mleft, mright \rchanset
\end{circus}

\begin{code}
-- omega_prime_CAction (CSPNSParal ns1 cs ns2 a1 a2)
--   = make_get_com lsx (rename_vars_CAction (CSPHide
--    (CSPNSParal [] (CSExpr "MEMI") []
--      (CSPNSParal [] cs []
--       (CSPHide
--        (CSPNSParal [] (CSExpr "MEMI") []
--         (CSPSeq a1 (CSPCommAction (ChanComm "lterminate" []) CSPSkip))
--         (CSPParAction "MemoryMerge"
--          [ZSetDisplay [],
--                 ZVar ("LEFT",[])]))
--        (CSExpr "MEMI"))
--       (CSPHide
--        (CSPNSParal [] (CSExpr "MEMI") []
--         (CSPSeq a2 (CSPCommAction (ChanComm "lterminate" []) CSPSkip))
--         (CSPParAction "MemoryMerge"
--          [ZSetDisplay [],
--                 ZVar ("RIGHT",[])]))
--        (CSExpr "MEMI")))
--       (CActionName "Merge"))
--       (CChanSet ["mleft","mright"])))
--    where
--     lsx = union (map fst (remdups (free_var_CAction a1))) (map fst (remdups (free_var_CAction a2)))
\end{code}

\end{omegaprime}
\begin{omegaprime}
\begin{circus}
\Omega'_A (\Semi x : \langle v_1,...,v_n \rangle \circspot A(x)) \circdef \Omega'_A (A(v_1)\circseq \ldots \circseq A(v_n))
\end{circus}
is written in Haskell as:
\begin{code}
omega_prime_CAction (CSPRepSeq [Choose (x,[],tx) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1,[],tx1)]))
  = case x == x1 of
    True -> omega_prime_CAction (rep_CSPRepSeq act xs)
    _  -> (CSPRepSeq [Choose (x,[],tx) (ZSeqDisplay xs)]
          (CSPParAction act [ZVar (x1,[],tx1)]))
omega_prime_CAction (CSPRepSeq [Choose (x,[],tx) v] act)
  = (CSPRepSeq [Choose (x,[],tx) v] (omega_prime_CAction act))
\end{code}

\end{omegaprime}
\begin{omegaprime}
\begin{circus}
\Omega'_A (\Extchoice x : \langle v_1,...,v_n \rangle \circspot A(x)) \circdef \Omega'_A (A(v_1)\extchoice \ldots \extchoice A(v_n))
\end{circus}
is written in Haskell as:
\begin{code}
omega_prime_CAction (CSPRepExtChoice [Choose (x,[],tx) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1,[],tx1)]))
  = case x == x1 of
    True -> omega_prime_CAction (rep_CSPRepExtChoice act xs)
    _  -> (CSPRepExtChoice [Choose (x,[],tx) (ZSeqDisplay xs)]
          (CSPParAction act [ZVar (x1,[],tx1)]))
omega_prime_CAction (CSPRepExtChoice [Choose (x,[],s) v] act)
  = (CSPRepExtChoice [Choose (x,[],s) v] (omega_prime_CAction act))
\end{code}

\end{omegaprime}
\begin{omegaprime}
\begin{circus}
\Omega'_A (\Intchoice x : \langle v_1,...,v_n \rangle \circspot A(x)) \circdef \Omega'_A (A(v_1)\intchoice \ldots \intchoice A(v_n))
\end{circus}
is written in Haskell as:
\begin{code}
omega_prime_CAction (CSPRepIntChoice [Choose (x,[],tx) (ZSeqDisplay xs)]
          (CSPParAction act [ZVar (x1,[],tx1)]))
  = case x == x1 of
    True -> omega_prime_CAction(rep_CSPRepIntChoice act xs)
    _  -> (CSPRepIntChoice [Choose (x,[],tx) (ZSeqDisplay xs)]
          (CSPParAction act [ZVar (x1,[],tx1)]))
omega_prime_CAction (CSPRepIntChoice [Choose (x,[],tx) v] act)
  = (CSPRepIntChoice [Choose (x,[],tx) v] (omega_prime_CAction act))
\end{code}

\end{omegaprime}
\begin{omegaprime}
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
omega_prime_CAction (CSPRepParalNS (CSExpr cs) [Choose x (ZSetDisplay lsx)]
          [ZVar (x1,[],tx2)]
          (CSPParAction a [ZVar (x2,[],tx3)]))
  = case (member (ZVar x) [ZVar (x1,[],tx2)]) && (member (ZVar x) [ZVar (x2,[],tx3)]) of
    True -> omega_prime_CAction (rep_CSPRepParalNS a cs (x1,[],tx2) x lsx)
    _  -> (CSPRepParalNS (CSExpr cs) [Choose x (ZSetDisplay lsx)]
          [ZVar (x1,[],tx2)]
          (CSPParAction a [ZVar (x2,[],tx3)]))
omega_prime_CAction (CSPRepParalNS (CSExpr cs) [Choose (x,[],tx) (ZSetDisplay lsx)] [ZVar (x1,[],tx1)] act)
  = (CSPRepParalNS (CSExpr cs) [Choose (x,[],tx) (ZSetDisplay lsx)] [ZVar (x1,[],tx1)] (omega_prime_CAction act))
\end{code}

\end{omegaprime}
\begin{omegaprime}
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

\end{omegaprime}
% \begin{omegaprime}
% \begin{circus}
% \Omega'_A (\circif g \circthen A \circfi ) \defs
%    \\\t1\circif g \circthen \Omega'_A (A) \circfi
% \end{circus}
% \begin{code}
% omega_prime_CAction (CActionCommand (CIf (CircGAction g a)))
%   = (CActionCommand (CIf (CircGAction g (omega_prime_CAction a))))

% \end{code}

% \end{omegaprime}
\begin{omegaprime}
\begin{circus}
\Omega'_A (A \circhide cs) \circdef \Omega'_A (A) \circhide cs
\end{circus}

is written in Haskell as:

\begin{code}
omega_prime_CAction (CSPHide a cs) = (CSPHide (omega_prime_CAction a) cs)
\end{code}

\end{omegaprime}
\begin{omegaprime}
\begin{circus}
\Omega'_A
   \left (\begin{array}{l}
   \circif g_0  \circthen A_0
   \\\t1\circelse \ldots
   \\\t1 \circelse g_n  \circthen A_n
   \\\circfi
   \end{array}\right ) \defs
   \left (\begin{array}{l}\circif g_0 \circthen \Omega'_A (A_0)
   \\\t2\circelse \ldots
   \\\t2 \circelse g_n \circthen \Omega'_A (A_n)
   \\\t1\circfi\end{array}\right )
\end{circus}

\begin{code}
omega_prime_CAction (CActionCommand (CIf glx))
  = (CActionCommand (CIf (mk_guard_pair omega_prime_CAction guard_pair)))
  where
   guard_pair = get_guard_pair glx
\end{code}

\end{omegaprime}
\begin{omegaprime}
\begin{circus}
\Omega'_A (\circmu X \circspot A(X)) \circdef \circmu X \circspot \Omega'_A(A(X))
\end{circus}

is written in Haskell as:

\begin{code}
omega_prime_CAction (CSPRecursion x c) = (CSPRecursion x (omega_prime_CAction c))
\end{code}

\end{omegaprime}
\begin{omegaprime}
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
omega_prime_CAction (CSPRepInterlNS [Choose x (ZSetDisplay lsx)]
          [ZVar ns1]
          (CSPParAction a ns2))
  = case (member (ZVar x) [ZVar ns1] ) && (member (ZVar x) ns2 ) of
    True -> omega_prime_CAction (rep_CSPRepInterlNS a ns1 x lsx)
    _  ->  (CSPRepInterlNS [Choose x (ZSetDisplay lsx)]
          [ZVar ns1]
          (CSPParAction a ns2))
omega_prime_CAction (CSPRepInterlNS [Choose (x,[],t1) (ZSetDisplay lsx)]
          ([ZVar (x1,[],t2)])
          act)
  = (CSPRepInterlNS [Choose (x,[],t1) (ZSetDisplay lsx)]
          ([ZVar (x1,[],t2)])
          (omega_prime_CAction act))
\end{code}

\end{omegaprime}
\begin{omegaprime}
\begin{circus}
\Omega'_A (\{g\}) \circdef \prefixcolon [g, true]
\end{circus}

\begin{code}
omega_prime_CAction (CActionCommand (CommandBrace g))
  = omega_prime_CAction (CActionCommand (CPrefix g (ZTrue {reason = []})))
\end{code}

\end{omegaprime}
\begin{omegaprime}
\begin{circus}
\Omega'_A ([g]) \circdef \prefixcolon [g]
\end{circus}

\begin{code}
omega_prime_CAction (CActionCommand (CommandBracket g))
  = omega_prime_CAction (CActionCommand (CPrefix1 g))
\end{code}

\end{omegaprime}
\begin{omegaprime}
\begin{circus}
\Omega'_A (A[old_1,...,old_n := new_1,...,new_n) \circdef
\\\t1A[new_1,...,new_n/old_1,...,old_n)
\end{circus}

\begin{code}
omega_prime_CAction (CSPRenAction a (CRenameAssign left right))
  = (CSPRenAction a (CRename right left))
\end{code}

\end{omegaprime}

In order to pattern match any other \Circus\ construct not mentioned here, we propagate the $omega\_prime_CAction$ function to the remainder of the constructs.


\begin{omegaprime}
\begin{code}
omega_prime_CAction (CActionSchemaExpr vZSExpr) = (CActionSchemaExpr vZSExpr)
omega_prime_CAction (CActionName vZName) = (CActionName vZName)
omega_prime_CAction (CSPCommAction vComm vCAction) = (CSPCommAction vComm (omega_prime_CAction vCAction))
omega_prime_CAction (CSPNSParal v1NSExp vCSExp v2NSExp v1CAction v2CAction) = (CSPNSParal v1NSExp vCSExp v2NSExp (omega_prime_CAction v1CAction) (omega_prime_CAction v2CAction))
omega_prime_CAction (CSPParal vCSExp v1CAction v2CAction) = (CSPParal vCSExp (omega_prime_CAction v1CAction) (omega_prime_CAction v2CAction))
omega_prime_CAction (CSPNSInter v1NSExp v2NSExp v1CAction v2CAction) = (CSPNSInter v1NSExp v2NSExp (omega_prime_CAction v1CAction) (omega_prime_CAction v2CAction))
omega_prime_CAction (CSPInterleave v1CAction v2CAction) = (CSPInterleave (omega_prime_CAction v1CAction) (omega_prime_CAction v2CAction))
omega_prime_CAction (CSPParAction vZName vZExpr_lst) = (CSPParAction vZName vZExpr_lst)
omega_prime_CAction (CSPRenAction vZName vCReplace) = (CSPRenAction vZName vCReplace)
omega_prime_CAction (CSPUnfAction vZName vCAction) = (CSPUnfAction vZName (omega_prime_CAction vCAction))
omega_prime_CAction (CSPUnParAction vZGenFilt_lst vCAction vZName) = (CSPUnParAction vZGenFilt_lst (omega_prime_CAction vCAction) vZName)
-- omega_prime_CAction (CSPRepSeq vZGenFilt_lst vCAction) = (CSPRepSeq vZGenFilt_lst (omega_prime_CAction vCAction))
-- omega_prime_CAction (CSPRepExtChoice vZGenFilt_lst vCAction) = (CSPRepExtChoice vZGenFilt_lst (omega_prime_CAction vCAction))
-- omega_prime_CAction (CSPRepIntChoice vZGenFilt_lst vCAction) = (CSPRepIntChoice vZGenFilt_lst (omega_prime_CAction vCAction))
-- omega_prime_CAction (CSPRepParalNS vCSExp vZGenFilt_lst vNSExp vCAction) = (CSPRepParalNS vCSExp vZGenFilt_lst vNSExp (omega_prime_CAction vCAction))
-- omega_prime_CAction (CSPRepParal vCSExp vZGenFilt_lst vCAction) = (CSPRepParal vCSExp vZGenFilt_lst (omega_prime_CAction vCAction))
-- omega_prime_CAction (CSPRepInterlNS vZGenFilt_lst vNSExp vCAction) = (CSPRepInterlNS vZGenFilt_lst vNSExp (omega_prime_CAction vCAction))
-- omega_prime_CAction (CSPRepInterl vZGenFilt_lst vCAction) = (CSPRepInterl vZGenFilt_lst (omega_prime_CAction vCAction))
omega_prime_CAction x = x
\end{code}

\end{omegaprime}


\section{$\Gamma$ functions}

Set of mapping functions for those actions that runs within the scope of a parallel actions


\section{Stateless Circus - Actions}


\begin{gammaenv}
\begin{circus}
\Gamma_A (\Skip) \circdef \Skip
\also \Gamma_A (\Stop) \circdef \Stop
\also \Gamma_A (\Chaos) \circdef \Chaos
\end{circus}
is written in Haskell as:
\begin{code}
gamma_CAction :: CAction -> CAction
gamma_CAction CSPSkip = CSPSkip
gamma_CAction CSPStop = CSPStop
gamma_CAction CSPChaos = CSPChaos
\end{code}
\end{gammaenv}
\begin{gammaenv}
\begin{circus}
\Gamma_A (c \then A) \circdef c \then \Gamma_A (A)
\end{circus}

is written in Haskell as:
\begin{code}
gamma_CAction (CSPCommAction (ChanComm c []) a)
  = (CSPCommAction (ChanComm c []) (gamma_CAction a))
\end{code}
\end{gammaenv}
\begin{gammaenv}
\begin{circus}
\Gamma_A (c.e(v_0,\ldots,v_n,l_0,\ldots,l_m) \then A) \circdef
\\\t2 lget.v_0?vv_0 \then \ldots \then lget.v_n?vv_n \then
\\\t2 lget.l_0?vl_0 \then \ldots \then lget.l_m?vl_m \then
\\\t2 c.e(vv_0,\ldots,vv_n,vl_0,\ldots,vl_m) \then \Gamma'_{A} (A)
\end{circus}
where
\begin{circus}
FV (e) = (v_0,\ldots,v_n,l_0,\ldots,l_m)
\end{circus}

is written in Haskell as:
\begin{code}
gamma_CAction (CSPCommAction (ChanComm c [ChanDotExp e]) a)
  = make_lget_com lxs (rename_vars_CAction (CSPCommAction (ChanComm c [ChanDotExp e]) (gamma_prime_CAction a)))
  where lxs = remdups $ concat (map get_ZVar_st $ varset_to_zvars (free_var_ZExpr e))
gamma_CAction (CSPCommAction (ChanComm c ((ChanDotExp e):xs)) a)
  = make_lget_com lxs (rename_vars_CAction (CSPCommAction (ChanComm c ((ChanDotExp e):xs)) (gamma_prime_CAction a)))
  where lxs = remdups $ concat (map get_ZVar_st $ varset_to_zvars (free_var_ZExpr e))
\end{code}
\end{gammaenv}
\begin{gammaenv}
\begin{circus}
\Gamma_A (c!e(v_0,\ldots,v_n,l_0,\ldots,l_m) \then A) \circdef
\\\t2 c.e(v_0,\ldots,v_n,l_0,\ldots,l_m) \then A
\end{circus}
\begin{code}
gamma_CAction (CSPCommAction (ChanComm c [ChanOutExp e]) a)
  = gamma_CAction (CSPCommAction (ChanComm c [ChanDotExp e]) a)
gamma_CAction (CSPCommAction (ChanComm c ((ChanOutExp e):xs)) a)
  = gamma_CAction (CSPCommAction (ChanComm c ((ChanDotExp e):xs)) a)
\end{code}
\end{gammaenv}
\begin{gammaenv}
\begin{circus}
\Gamma_A (g(v_0,\ldots,v_n,l_0,\ldots,l_m) \then A) \circdef
\\\t2 lget.v_0?vv_0 \then \ldots \then lget.v_n?vv_n \then
\\\t2 lget.l_0?vl_0 \then \ldots \then lget.l_m?vl_m \then
\\\t2 g(vv_0,\ldots,vv_n,vl_0,\ldots,vl_m) \circguard \Gamma'_{A} (A)
\end{circus}
is written in Haskell as:
\begin{code}
gamma_CAction (CSPGuard g a)
  = make_lget_com lxs (rename_vars_CAction (CSPGuard (rename_ZPred g) (gamma_prime_CAction a)))
  where lxs = remdups $ concat (map get_ZVar_st $ varset_to_zvars (free_var_ZPred g))
\end{code}
\end{gammaenv}
\begin{gammaenv}

I'm considering $x?k \neq x?k : P$ and I'm making the translation straightforward:

\begin{circus}
\Gamma_A (c?x \then A) \circdef
\\\t2 c?x \then \Gamma'_{A} (A)
\end{circus}

is written in Haskell as:
\begin{code}
gamma_CAction (CSPCommAction (ChanComm c [ChanInp e]) a)
  = case is_ZVar_st e of
      True -> (CSPCommAction (ChanComm c [ChanInp (join_name "t" e)]) (make_set_com omega_CAction [(e,[],"")] [ZVar ((join_name "t" e),[],"")] a))
      False -> (CSPCommAction (ChanComm c [ChanInp e]) (gamma_CAction a))
gamma_CAction (CSPCommAction (ChanComm c ((ChanInp e):xs)) a)
  = case is_ZVar_st e of
      True -> (CSPCommAction (ChanComm c ((ChanInp (join_name "t" e)):xs)) (make_set_com omega_CAction [(e,[],"")] [ZVar ((join_name "t" e),[],"")] a))
      False -> (CSPCommAction (ChanComm c ((ChanInp e):xs)) (gamma_CAction a))

\end{code}
\end{gammaenv}
\begin{gammaenv}

\begin{circus}
\Gamma_A (c?x : P(x,v_0,\ldots,v_n,l_0,\ldots,l_m) \then A) \circdef
\\\t2 lget.v_0?vv_0 \then \ldots \then lget.v_n?vv_n \then
\\\t2 lget.l_0?vl_0 \then \ldots \then lget.l_m?vl_m \then
\\\t2 c?x : P(x,vv_0,\ldots,vv_n,vl_0,\ldots,vl_m) \then \Gamma'_{A} (A)
\end{circus}
where
\begin{circus}
x \in wrtV(A)
\end{circus}

is written in Haskell as:
\begin{code}
gamma_CAction (CSPCommAction (ChanComm c [ChanInpPred x p]) a)
  = case not (elem x (wrtV(a))) of
    True -> make_lget_com lsx (rename_vars_CAction (CSPCommAction
             (ChanComm c [ChanInpPred x p])
                 (gamma_prime_CAction a)))
    _  -> (CSPCommAction (ChanComm c [ChanInpPred x p]) a)
  where lsx = remdups $ concat (map get_ZVar_st $ varset_to_zvars (free_var_ZPred p))
\end{code}
\end{gammaenv}
\begin{gammaenv}


\begin{circus}
\Gamma_A (A_1 \circseq A_2) \circdef \Gamma_A (A_1) \circseq \Gamma_A (A_2)
\end{circus}
is written in Haskell as:
\begin{code}
gamma_CAction (CSPSeq ca cb)
  = (CSPSeq (gamma_CAction ca) (gamma_CAction cb))
\end{code}
\end{gammaenv}
\begin{gammaenv}
\begin{circus}
\Gamma_A (A_1 \intchoice A_2) \circdef \Gamma_A (A_1) \intchoice \Gamma_A (A_2)
\end{circus}
is written in Haskell as:
\begin{code}
gamma_CAction (CSPIntChoice ca cb)
  = (CSPIntChoice (gamma_CAction ca) (gamma_CAction cb))
\end{code}
\end{gammaenv}
\begin{gammaenv}
% TODO: I need to somehow calculate the $FV(A_1)$ and $FV(A_2)$. What should I do?
\begin{circus}
\Gamma_A (A_1 \extchoice A_2) \circdef
\\\t1 lget.v_0?vv_0 \then \ldots \then lget.v_n?vv_n \then
\\\t1 lget.l_0?vl_0 \then \ldots \then lget.l_m?vl_m \then
\\\t2 (\Gamma'_A (A_1) \extchoice \Gamma'_A (A_2))
\end{circus}
is written in Haskell as:
\begin{code}
gamma_CAction (CSPExtChoice ca cb)
  = make_lget_com lsx (CSPExtChoice (gamma_prime_CAction ca) (gamma_prime_CAction cb))
   where
    lsx = remdups $ concat $ map get_ZVar_st $ varset_to_zvars $ free_var_CAction (CSPExtChoice ca cb)
\end{code}
% \begin{circus}
% \Gamma_A (A1 \lpar ns1 | cs | ns2 \rpar A2) \circdef
% \\\t1 lget.v_0?vv_0 \then \ldots \then lget.v_n?vv_n \then
% \\\t1 lget.l_0?vl_0 \then \ldots \then lget.l_m?vl_m \then
%       \\\t2\left (\begin{array}{l}
%        \left (\begin{array}{l}
%         \left (\begin{array}{l}
%          \left (\begin{array}{l}
%           \Gamma'_A (A_1) \circseq terminate \then \Skip
%          \end{array}\right )\\
%           \lpar \{\} | MEMI | \{\} \rpar
%           \\ MemoryMerge(\{v0 \mapsto vv0,\ldots\},LEFT)
%         \end{array}\right )
%         \circhide MEMI \\
%        \lpar \{\} | cs | \{\} \rpar \\
%         \left (\begin{array}{l}
%          \left (\begin{array}{l}
%           \Gamma'_A (A_2) \circseq terminate \then \Skip
%          \end{array}\right )\\
%           \lpar \{\} | MEMI | \{\} \rpar
%           \\ MemoryMerge(\{v0 \mapsto vv0,\ldots\},RIGHT)
%         \end{array}\right )
%         \circhide MEMI
%        \end{array}\right )\\
%       \lpar \{\} | MRG_I | \{\} \rpar\\
%       Merge
%     \end{array}\right )\\
%     \t2\circhide \lchanset mleft, mright \rchanset
% \end{circus}
\end{gammaenv}
\begin{gammaenv}
\begin{circus}
\Gamma_A (A1 \lpar ns1 | cs | ns2 \rpar A2) \circdef
\\\t1 lget.v_0?vv_0 \then \ldots \then lget.v_n?vv_n \then
\\\t1 lget.l_0?vl_0 \then \ldots \then lget.l_m?vl_m \then
      \\\t2\left (\begin{array}{l}
       \left (\begin{array}{l}
        \left (\begin{array}{l}
         \left (\begin{array}{l}
          \Gamma'_A (A_1) \circseq terminate \then \Skip
         \end{array}\right )\\
          \lpar \{\} | MEMI | \{\} \rpar
          \\ MemoryMerge(\{v0 \mapsto vv0,\ldots\},LEFT)
        \end{array}\right )
        \circhide MEMI \\
       \lpar \{\} | cs | \{\} \rpar \\
        \left (\begin{array}{l}
         \left (\begin{array}{l}
          \Gamma'_A (A_2) \circseq terminate \then \Skip
         \end{array}\right )\\
          \lpar \{\} | MEMI | \{\} \rpar
          \\ MemoryMerge(\{v0 \mapsto vv0,\ldots\},RIGHT)
        \end{array}\right )
        \circhide MEMI
       \end{array}\right )\\
      \lpar \{\} | MRG_I | \{\} \rpar\\
      \left (\begin{array}{l}mleft?l \then (\Semi n:ns1 \circspot mset.n!l(n) \then \Skip)\\ \interleave~mright?r \then (\Semi n:ns2 \circspot mset.n!r(n) \then \Skip)\end{array}\right )
    \end{array}\right )\\
    \t2\circhide \lchanset mleft, mright \rchanset
\end{circus}

The definition of parallel composition (and interleaving), as defined in the D24.1, has a $MemoryMerge$, $MRG_I$ and $Merge$ components and channel sets. Whilst translating them into CSP, the tool would rather expand their definition

\begin{code}
gamma_CAction (CSPNSParal [ZSetDisplay ns1] cs [ZSetDisplay ns2] a1 a2)
  = make_lget_com lsx ( (CSPHide
     (CSPNSParal [] cs []
      (CSPHide
       (CSPNSParal [] (CSExpr "MEMI") []
        (CSPSeq (gamma_prime_CAction a1) (CSPCommAction (ChanComm "lterminate" []) CSPSkip))
        (CSPParAction "MemoryMerge"
         [ZSetDisplay (mk_var_v_var_bnds ns1),
                ZVar ("LEFT",[],[]),ZSeqDisplay ns1,ZSeqDisplay ns2]))
       (CSExpr "MEMI"))
      (CSPHide
       (CSPNSParal [] (CSExpr "MEMI") []
        (CSPSeq (gamma_prime_CAction a2) (CSPCommAction (ChanComm "lterminate" []) CSPSkip))
        (CSPParAction "MemoryMerge"
         [ZSetDisplay (mk_var_v_var_bnds ns2),
                ZVar ("RIGHT",[],[]),ZSeqDisplay ns1,ZSeqDisplay ns2]))
       (CSExpr "MEMI")))
      (CChanSet ["mleft","mright"])))
   where
    lsx = concat (map get_ZVar_st (remdups (varset_to_zvars (union_varset (free_var_CAction a1) (free_var_CAction a2)))))
\end{code}
\end{gammaenv}
\begin{gammaenv}
\begin{circus}
\Gamma_A (\Semi x : \langle v_1,...,v_n \rangle \circspot A(x)) \circdef \Gamma_A (A(v_1)\circseq \ldots \circseq A(v_n))
\end{circus}
is written in Haskell as:
\begin{code}
{-
gamma_CAction (CSPRepSeq [Choose (x,[],tx) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1,[],tx1)]))
  = case x == x1 of
    True -> gamma_CAction (rep_CSPRepSeq act xs)
    _  -> (CSPRepSeq [Choose (x,[],tx) (ZSeqDisplay xs)]
          (CSPParAction act [ZVar (x1,[],tx1)]))-}
gamma_CAction (CSPRepSeq [Choose (x,[],tx) v] act)
  = (CSPRepSeq [Choose (x,[],tx) v] (gamma_CAction act))
\end{code}
\end{gammaenv}
\begin{gammaenv}
\begin{circus}
\Gamma_A (\Extchoice x : \langle v_1,...,v_n \rangle \circspot A(x)) \circdef \Gamma_A (A(v_1)\extchoice \ldots \extchoice A(v_n))
\end{circus}
is written in Haskell as:
\begin{code}
gamma_CAction (CSPRepExtChoice [Choose (x,[],tx) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1,[],tx1)]))
  = case x == x1 of
    True -> gamma_CAction (rep_CSPRepExtChoice act xs)
    _  -> (CSPRepExtChoice [Choose (x,[],tx) (ZSeqDisplay xs)]
          (CSPParAction act [ZVar (x1,[],tx1)]))
gamma_CAction (CSPRepExtChoice [Choose (x,[],tx) v] act)
  = (CSPRepExtChoice [Choose (x,[],tx) v] (gamma_CAction act))
\end{code}
\end{gammaenv}
\begin{gammaenv}
\begin{circus}
\Gamma_A (\Intchoice x : \langle v_1,...,v_n \rangle \circspot A(x)) \circdef \Gamma_A (A(v_1)\intchoice \ldots \intchoice A(v_n))
\end{circus}
is written in Haskell as:
\begin{code}
gamma_CAction (CSPRepIntChoice [Choose (x,[],tx) (ZSeqDisplay xs)]
          (CSPParAction act [ZVar (x1,[],tx1)]))
  = case x == x1 of
    True -> gamma_CAction(rep_CSPRepIntChoice act xs)
    _  -> (CSPRepIntChoice [Choose (x,[],tx) (ZSeqDisplay xs)]
          (CSPParAction act [ZVar (x1,[],tx1)]))
gamma_CAction (CSPRepIntChoice [Choose (x,[],tx) v] act)
  = (CSPRepIntChoice [Choose (x,[],tx) v] (gamma_CAction act))
\end{code}
\end{gammaenv}
\begin{gammaenv}
\begin{circus}
\Gamma_A (\lpar cs \rpar x : \langle v_1,...,v_n \rangle \circspot \lpar ns(x) \rpar A(x)) \circdef
\\\t1
\left (\begin{array}{l}A(v_1)
   \\ \lpar ns(v_1) | cs | \bigcup\{x : \{v_2,...,v_n\} \circspot ns(x)\} \rpar
   \\ \left (\begin{array}{l}
     \ldots
      \left (\begin{array}{l}
      \Gamma_A(A(v_n -1))
      \\ \lpar ns(v_n -1 ) | cs | ns(v_n) \rpar
      \\ A(v_n)\end{array}\right )\end{array}\right )\end{array}\right )

\end{circus}
is written in Haskell as:
\begin{code}
gamma_CAction (CSPRepParalNS (CSExpr cs) [Choose x (ZSetDisplay lsx)]
          [ZVar (x1,[],tx1)]
          (CSPParAction a [ZVar (x2,[],tx2)]))
  = case (member (ZVar x) [ZVar (x1,[],tx1)]) && (member (ZVar x) [ZVar (x2,[],tx2)]) of
    True -> gamma_CAction (rep_CSPRepParalNS a cs (x1,[],tx1) x lsx)
    _  -> (CSPRepParalNS (CSExpr cs) [Choose x (ZSetDisplay lsx)]
          [ZVar (x1,[],tx1)]
          (CSPParAction a [ZVar (x2,[],tx2)]))
gamma_CAction (CSPRepParalNS (CSExpr cs) [Choose x (ZSetDisplay lsx)] [ZVar (x1,[],tx1)] act)
  = (CSPRepParalNS (CSExpr cs) [Choose x (ZSetDisplay lsx)] [ZVar (x1,[],tx1)] (gamma_CAction act))
\end{code}
\end{gammaenv}
\begin{gammaenv}
\begin{circus}
\Gamma_A ( \circval Decl \circspot P) \circdef \circval Decl \circspot \Gamma_A (P)
\end{circus}
is written in Haskell as:
\begin{code}
gamma_CAction (CActionCommand (CValDecl xs a))
  = (CActionCommand (CValDecl xs (gamma_CAction a)))
\end{code}
\end{gammaenv}
\begin{gammaenv}
\begin{circus}
\Gamma_A \left (\begin{array}{l}x_0,\ldots,x_n:=e_0\left (\begin{array}{l}v_0,...,v_n,\\l_0,...,l_m\end{array}\right ),\ldots,e_n\left (\begin{array}{l}v_0,...,v_n,\\l_0,...,l_m\end{array}\right )\end{array}\right ) \circdef
\\\t1 lget.v_0?vv_0 \then \ldots \then lget.v_n?vv_n \then
\\\t1 lget.l_0?vl_0 \then \ldots \then lget.l_m?vl_m \then
\\\t1 set.x_0!e_0(vv_0,...,vv_n,vl_0,...,vl_m) \then
\\\t1\ldots\then
\\\t1 set.x_n!e_n(vv_0,...,vv_n,vl_0,...,vl_m) \then \Skip
\end{circus}

\begin{code}
gamma_CAction (CActionCommand (CAssign varls valls))
  = make_lget_com lxs (make_lset_com gamma_CAction varls (map rename_ZExpr valls) CSPSkip)
    where
      lxsvarls = (concat (map get_ZVar_st varls))
      lxsvalls = (concat (map get_ZVar_st (varset_to_zvars $ union_varsets (map fvars_expr valls))))
      lxs = remdups (lxsvalls ++ lxsvarls)
\end{code}
\end{gammaenv}
\begin{gammaenv}
\begin{circus}
\Gamma_A (A \circhide cs) \circdef \Gamma_A (A) \circhide cs
\end{circus}

is written in Haskell as:

\begin{code}
gamma_CAction (CSPHide a cs) = (CSPHide (gamma_CAction a) cs)
\end{code}
\end{gammaenv}
\begin{gammaenv}
\begin{circus}
\Gamma_A
   \left (\begin{array}{l}
   \circif g_0 (v_0,...,v_n,l_0,...,l_m) \circthen A_0
   \\\t1\circelse \ldots
   \\\t1 \circelse g_n (v_0,...,v_n,l_0,...,l_m) \circthen A_n
   \\\circfi
   \end{array}\right ) \defs
   \\\t1 lget.v_0?vv_0 \then \ldots \then lget.v_n?vv_n \then
   \\\t1 lget.l_0?vl_0 \then \ldots \then lget.l_m?vl_m \then
   \\\t1\circif g_0 (v_0,...,v_n,l_0,...,l_m) \circthen \Gamma'_A (A_0)
   \\\t2\circelse \ldots
   \\\t2 \circelse g_n (v_0,...,v_n,l_0,...,l_m) \circthen \Gamma'_A (A_n)
   \\\t1\circfi
\end{circus}

\begin{code}
gamma_CAction (CActionCommand (CIf gax))
  = make_lget_com lsx (CActionCommand (CIf (mk_guard_pair gamma_prime_CAction (rename_guard_pair lsx gpair))))
  where
   gpair = get_guard_pair gax
   lsx = concat (map get_ZVar_st (remdups (concat (map (varset_to_zvars . free_var_ZPred) (map fst gpair)))))
\end{code}
\end{gammaenv}
\begin{gammaenv}
% \begin{circus}
% \Gamma_A (\circif g (v_0,...,v_n,l_0,...,l_m) \circthen A \circfi ) \defs
%    \\\t1 lget.v_0?vv_0 \then \ldots \then lget.v_n?vv_n \then
%    \\\t1 lget.l_0?vl_0 \then \ldots \then lget.l_m?vl_m \then
%    \\\t1\circif g (v_0,...,v_n,l_0,...,l_m) \circthen \Gamma'_A (A) \circfi
% \end{circus}
% \begin{code}
% gamma_CAction (CActionCommand (CIf (CircGAction g a)))
%   = make_lget_com lsx (rename_vars_CAction (CActionCommand
%              (CIf (CircGAction g (gamma_prime_CAction a)))))
%   where
%    lsx = remdups $ concat $ map get_ZVar_st $ remdups $ free_var_ZPred g
% \end{code}
\end{gammaenv}
\begin{gammaenv}
\begin{circus}
\Gamma_A (\circmu X \circspot A(X)) \circdef \circmu X \circspot \Gamma_A(A(X))
\end{circus}

is written in Haskell as:

\begin{code}
--  TODO Jun 30 2017: rename the recursion action name, so it won't clash with any Circus action name.
gamma_CAction (CSPRecursion x c) = (CSPRecursion x (gamma_CAction c))
\end{code}
\end{gammaenv}
\begin{gammaenv}
\begin{circus}
\Gamma_A (\Interleave x : \langle v_1,...,v_n \rangle \circspot A(x)) \circdef
\\\t1
\left (\begin{array}{l}A(v_1)
   \\ \lpar ns(v_1) | \bigcup\{x : \{v_2,...,v_n\} \circspot ns(x)\} \rpar
   \\ \left (\begin{array}{l}
     \ldots
      \left (\begin{array}{l}
      \Gamma_A(A(v_n -1))
      \\ \lpar ns(v_n -1 ) | ns(v_n)\rpar
      \\ A(v_n)\end{array}\right )\end{array}\right )\end{array}\right )

\end{circus}

is written in Haskell as:

\begin{code}
gamma_CAction (CSPRepInterlNS [Choose x (ZSetDisplay lsx)]
          [ZVar (x1,[],tx1)]
          (CSPParAction a [ZVar (x2,[],tx2)]))
  = case (member (ZVar x) [ZVar (x1,[],tx1)]) && (member (ZVar x) [ZVar (x2,[],tx2)]) of
    True -> gamma_CAction (rep_CSPRepInterlNS a (x1,[],tx1) x lsx)
    _  ->  (CSPRepInterlNS [Choose x (ZSetDisplay lsx)]
          [ZVar (x1,[],tx1)]
          (CSPParAction a [ZVar (x2,[],tx2)]))
gamma_CAction (CSPRepInterlNS [Choose (x,[],tx) (ZSetDisplay lsx)]
          [ZVar (x1,[],tx1)]
          act)
  = (CSPRepInterlNS [Choose (x,[],tx) (ZSetDisplay lsx)]
          [ZVar (x1,[],tx1)]
          (gamma_CAction act))
\end{code}
\end{gammaenv}
\begin{gammaenv}
\begin{circus}
\Gamma_A (\{g\}) \circdef \prefixcolon [g, true]
\end{circus}

\begin{code}
gamma_CAction (CActionCommand (CommandBrace g))
  = gamma_CAction (CActionCommand (CPrefix g (ZTrue {reason = []})))
\end{code}
\end{gammaenv}
\begin{gammaenv}
\begin{circus}
\Gamma_A ([g]) \circdef \prefixcolon [g]
\end{circus}

\begin{code}
gamma_CAction (CActionCommand (CommandBracket g))
  = gamma_CAction (CActionCommand (CPrefix1 g))
\end{code}
\end{gammaenv}
\begin{gammaenv}
\begin{circus}
\Gamma_A (A[old_1,...,old_n := new_1,...,new_n) \circdef
\\\t1A[new_1,...,new_n/old_1,...,old_n)
\end{circus}

\begin{code}
gamma_CAction (CSPRenAction a (CRenameAssign left right))
  = (CSPRenAction a (CRename right left))
\end{code}
\end{gammaenv}
\begin{gammaenv}
In order to pattern match any other \Circus\ construct not mentioned here, we propagate the $gamma\_CAction$ function to the remainder of the constructs.

% I left the replicated operators for future work as they are similar to what I already implemented. Once I'm done with the verification bits, I'll get back here
\begin{code}
gamma_CAction (CActionSchemaExpr vZSExpr) = (CActionSchemaExpr vZSExpr)
gamma_CAction (CActionName vZName) = (CActionName vZName)
gamma_CAction (CSPCommAction vComm vCAction) = (CSPCommAction vComm (gamma_CAction vCAction))
-- gamma_CAction (CSPNSParal v1NSExp vCSExp v2NSExp v1CAction v2CAction) = (CSPNSParal v1NSExp vCSExp v2NSExp (gamma_CAction v1CAction) (gamma_CAction v2CAction))
gamma_CAction (CSPParal vCSExp v1CAction v2CAction) = (CSPParal vCSExp (gamma_CAction v1CAction) (gamma_CAction v2CAction))
gamma_CAction (CSPNSInter v1NSExp v2NSExp v1CAction v2CAction) = (CSPNSInter v1NSExp v2NSExp (gamma_CAction v1CAction) (gamma_CAction v2CAction))
gamma_CAction (CSPInterleave v1CAction v2CAction) = (CSPInterleave (gamma_CAction v1CAction) (gamma_CAction v2CAction))
gamma_CAction (CSPParAction vZName vZExpr_lst) = (CSPParAction vZName vZExpr_lst)
gamma_CAction (CSPRenAction vZName vCReplace) = (CSPRenAction vZName vCReplace)
gamma_CAction (CSPUnfAction vZName vCAction) = (CSPUnfAction vZName (gamma_CAction vCAction))
gamma_CAction (CSPUnParAction vZGenFilt_lst vCAction vZName) = (CSPUnParAction vZGenFilt_lst (gamma_CAction vCAction) vZName)
-- gamma_CAction (CSPRepSeq vZGenFilt_lst vCAction) = (CSPRepSeq vZGenFilt_lst (gamma_CAction vCAction))
-- gamma_CAction (CSPRepExtChoice vZGenFilt_lst vCAction) = (CSPRepExtChoice vZGenFilt_lst (gamma_CAction vCAction))
-- gamma_CAction (CSPRepIntChoice vZGenFilt_lst vCAction) = (CSPRepIntChoice vZGenFilt_lst (gamma_CAction vCAction))
-- gamma_CAction (CSPRepParalNS vCSExp vZGenFilt_lst vNSExp vCAction) = (CSPRepParalNS vCSExp vZGenFilt_lst vNSExp (gamma_CAction vCAction))
-- gamma_CAction (CSPRepParal vCSExp vZGenFilt_lst vCAction) = (CSPRepParal vCSExp vZGenFilt_lst (gamma_CAction vCAction))
-- gamma_CAction (CSPRepInterl vZGenFilt_lst vCAction) = (CSPRepInterl vZGenFilt_lst (gamma_CAction vCAction))
gamma_CAction x = x
\end{code}
\end{gammaenv}
% NOTE: Besides the transformation rules for $[g]$ and ${g}$, the remaining transformation rules from page 91 of the D24.1 document, were not yet implemented.
\section{Definitions of $\Gamma'_{A}$}

\begin{gammaprime}
\begin{circus}
\Gamma'_A (\Skip) \circdef \Skip
\also \Gamma'_A (\Stop) \circdef \Stop
\also \Gamma'_A (\Chaos) \circdef \Chaos
\end{circus}
is written in Haskell as:
\begin{code}
gamma_prime_CAction :: CAction -> CAction
gamma_prime_CAction CSPSkip = CSPSkip
gamma_prime_CAction CSPStop = CSPStop
gamma_prime_CAction CSPChaos = CSPChaos
\end{code}
\end{gammaprime}
\begin{gammaprime}
\begin{circus}
\Gamma'_A (c \then A) \circdef c \then \Gamma'_A (A)
\end{circus}

is written in Haskell as:
\begin{code}
gamma_prime_CAction (CSPCommAction (ChanComm c []) a)
  = (CSPCommAction (ChanComm c []) (gamma_prime_CAction a))
\end{code}

\end{gammaprime}
\begin{gammaprime}
\begin{circus}
\Gamma'_A (c.e \then A) \circdef c(vv_0,...,vv_n,vl_0,...,vl_m) \then \Gamma'_A (A)
\end{circus}

is written in Haskell as:
\begin{code}
gamma_prime_CAction (CSPCommAction (ChanComm c [ChanDotExp e]) a)
  = (CSPCommAction (ChanComm c [ChanDotExp (rename_ZExpr e)]) (gamma_prime_CAction a))
\end{code}
\end{gammaprime}
\begin{gammaprime}
\begin{circus}
\Gamma'_A (c!e \then A) \circdef
\\\t2 c.e \then A
\end{circus}
\begin{code}
gamma_prime_CAction (CSPCommAction (ChanComm c [ChanOutExp e]) a)
  = gamma_prime_CAction (CSPCommAction (ChanComm c [ChanDotExp e]) a)
gamma_prime_CAction (CSPCommAction (ChanComm c ((ChanOutExp e):xs)) a)
  = gamma_prime_CAction (CSPCommAction (ChanComm c ((ChanDotExp e):xs)) a)
\end{code}
\end{gammaprime}
\begin{gammaprime}
\begin{circus}
\Gamma'_A (g \then A) \circdef
\\\t2 g \circguard \Gamma'_{A} (A)
\end{circus}
is written in Haskell as:
\begin{code}
gamma_prime_CAction (CSPGuard g a)
  = (CSPGuard (rename_ZPred g) (gamma_prime_CAction a))
\end{code}
\end{gammaprime}
\begin{gammaprime}

I'm considering $x?k \neq x?k : P$ and I'm making the translation straightforward:

\begin{circus}
\Gamma'_A (c?x \then A) \circdef
\\\t2 c?x \then \Gamma'_{A} (A)
\end{circus}

is written in Haskell as:
\begin{code}

gamma_prime_CAction (CSPCommAction (ChanComm c [ChanInp e]) a)
  = case is_ZVar_st e of
      True -> (CSPCommAction (ChanComm c [ChanInp (join_name "t" e)]) (make_set_com omega_CAction [(e,[],"")] [ZVar ((join_name "t" e),[],"")] a))
      False -> (CSPCommAction (ChanComm c [ChanInp e]) (gamma_prime_CAction a))
gamma_prime_CAction (CSPCommAction (ChanComm c ((ChanInp e):xs)) a)
  = case is_ZVar_st e of
      True -> (CSPCommAction (ChanComm c ((ChanInp (join_name "t" e)):xs)) (make_set_com omega_CAction [(e,[],"")] [ZVar ((join_name "t" e),[],"")] a))
      False -> (CSPCommAction (ChanComm c ((ChanInp e):xs)) (gamma_prime_CAction a))
\end{code}
\end{gammaprime}
\begin{gammaprime}

\begin{circus}
\Gamma'_A (c?x : P \then A) \circdef
\\\t2 c?x : P \then \Gamma'_{A} (A)
\end{circus}
where
\begin{circus}
x \in wrtV(A)
\end{circus}

is written in Haskell as:

\begin{code}
gamma_prime_CAction (CSPCommAction (ChanComm c [ChanInpPred x p]) a)
  = (CSPCommAction (ChanComm c [ChanInpPred x p])
                 (gamma_prime_CAction a))
\end{code}
\end{gammaprime}
\begin{gammaprime}
\begin{circus}
\Gamma'_A (A_1 \circseq A_2) \circdef \Gamma'_A (A_1) \circseq \Gamma_A (A_2)
\end{circus}
is written in Haskell as:
\begin{code}
gamma_prime_CAction (CSPSeq ca cb)
  = (CSPSeq (gamma_prime_CAction ca) (gamma_CAction cb))
\end{code}
\end{gammaprime}
\begin{gammaprime}
\begin{circus}
\Gamma'_A (A_1 \intchoice A_2) \circdef \Gamma'_A (A_1) \intchoice \Gamma'_A (A_2)
\end{circus}
is written in Haskell as:
\begin{code}
gamma_prime_CAction (CSPIntChoice ca cb)
  = (CSPIntChoice (gamma_prime_CAction ca) (gamma_prime_CAction cb))
\end{code}
\end{gammaprime}
\begin{gammaprime}
% TODO: I need to somehow calculate the $FV(A_1)$ and $FV(A_2)$. What should I do?
\begin{circus}
\Gamma'_A (A_1 \extchoice A_2) \circdef
\\\t2 (\Gamma'_A (A_1) \extchoice \Gamma'_A (A_2))
\end{circus}
is written in Haskell as:
\begin{code}
gamma_prime_CAction (CSPExtChoice ca cb)
  = (CSPExtChoice (gamma_prime_CAction ca) (gamma_prime_CAction cb))
\end{code}
\end{gammaprime}
\begin{gammaprime}
\begin{circus}
\Gamma'_A (A1 \lpar ns1 | cs | ns2 \rpar A2) \circdef
\\\t1 lget.v_0?vv_0 \then \ldots \then lget.v_n?vv_n \then
\\\t1 lget.l_0?vl_0 \then \ldots \then lget.l_m?vl_m \then
      \\\t2\left (\begin{array}{l}
       \left (\begin{array}{l}
        \left (\begin{array}{l}
         \left (\begin{array}{l}
          \Gamma'_A (A_1) \circseq lterminate \then \Skip
         \end{array}\right )\\
          \lpar \{\} | MEMI | \{\} \rpar
          \\ MemoryMerge(\{v0 \mapsto vv0,\ldots\},LEFT)
        \end{array}\right )
        \circhide MEMI \\
       \lpar \{\} | cs | \{\} \rpar \\
        \left (\begin{array}{l}
         \left (\begin{array}{l}
          \Gamma'_A (A_2) \circseq lterminate \then \Skip
         \end{array}\right )\\
          \lpar \{\} | MEMI | \{\} \rpar
          \\ MemoryMerge(\{v0 \mapsto vv0,\ldots\},RIGHT)
        \end{array}\right )
        \circhide MEMI
       \end{array}\right )\\
      \lpar \{\} | MEMI | \{\} \rpar\\
      Merge
    \end{array}\right )\\
    \t2\circhide \lchanset mleft, mright \rchanset
\end{circus}

\begin{code}
-- gamma_prime_CAction (CSPNSParal ns1 cs ns2 a1 a2)
--   = make_lget_com lsx (rename_vars_CAction (CSPHide
--    (CSPNSParal [] (CSExpr "MEMI") []
--      (CSPNSParal [] cs []
--       (CSPHide
--        (CSPNSParal [] (CSExpr "MEMI") []
--         (CSPSeq a1 (CSPCommAction (ChanComm "lterminate" []) CSPSkip))
--         (CSPParAction "MemoryMerge"
--          [ZSetDisplay [],
--                 ZVar ("LEFT",[])]))
--        (CSExpr "MEMI"))
--       (CSPHide
--        (CSPNSParal [] (CSExpr "MEMI") []
--         (CSPSeq a2 (CSPCommAction (ChanComm "lterminate" []) CSPSkip))
--         (CSPParAction "MemoryMerge"
--          [ZSetDisplay [],
--                 ZVar ("RIGHT",[])]))
--        (CSExpr "MEMI")))
--       (CActionName "Merge"))
--       (CChanSet ["mleft","mright"])))
--    where
--     lsx = union (map fst (remdups (free_var_CAction a1))) (map fst (remdups (free_var_CAction a2)))
\end{code}
\end{gammaprime}
\begin{gammaprime}
\begin{circus}
\Gamma'_A (\Semi x : \langle v_1,...,v_n \rangle \circspot A(x)) \circdef \Gamma'_A (A(v_1)\circseq \ldots \circseq A(v_n))
\end{circus}
is written in Haskell as:
\begin{code}
gamma_prime_CAction (CSPRepSeq [Choose (x,[],tx) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1,[],tx1)]))
  = case x == x1 of
    True -> gamma_prime_CAction (rep_CSPRepSeq act xs)
    _  -> (CSPRepSeq [Choose (x,[],tx) (ZSeqDisplay xs)]
          (CSPParAction act [ZVar (x1,[],tx1)]))
gamma_prime_CAction (CSPRepSeq [Choose (x,[],tx) v] act)
  = (CSPRepSeq [Choose (x,[],tx) v] (gamma_prime_CAction act))
\end{code}
\end{gammaprime}
\begin{gammaprime}
\begin{circus}
\Gamma'_A (\Extchoice x : \langle v_1,...,v_n \rangle \circspot A(x)) \circdef \Gamma'_A (A(v_1)\extchoice \ldots \extchoice A(v_n))
\end{circus}
is written in Haskell as:
\begin{code}
gamma_prime_CAction (CSPRepExtChoice [Choose (x,[],tx) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1,[],tx1)]))
  = case x == x1 of
    True -> gamma_prime_CAction (rep_CSPRepExtChoice act xs)
    _  -> (CSPRepExtChoice [Choose (x,[],tx) (ZSeqDisplay xs)]
          (CSPParAction act [ZVar (x1,[],tx1)]))
gamma_prime_CAction (CSPRepExtChoice [Choose (x,[],s) v] act)
  = (CSPRepExtChoice [Choose (x,[],s) v] (gamma_prime_CAction act))
\end{code}
\end{gammaprime}
\begin{gammaprime}
\begin{circus}
\Gamma'_A (\Intchoice x : \langle v_1,...,v_n \rangle \circspot A(x)) \circdef \Gamma'_A (A(v_1)\intchoice \ldots \intchoice A(v_n))
\end{circus}
is written in Haskell as:
\begin{code}
gamma_prime_CAction (CSPRepIntChoice [Choose (x,[],tx) (ZSeqDisplay xs)]
          (CSPParAction act [ZVar (x1,[],tx1)]))
  = case x == x1 of
    True -> gamma_prime_CAction(rep_CSPRepIntChoice act xs)
    _  -> (CSPRepIntChoice [Choose (x,[],tx) (ZSeqDisplay xs)]
          (CSPParAction act [ZVar (x1,[],tx1)]))
gamma_prime_CAction (CSPRepIntChoice [Choose (x,[],tx) v] act)
  = (CSPRepIntChoice [Choose (x,[],tx) v] (gamma_prime_CAction act))
\end{code}
\end{gammaprime}
\begin{gammaprime}
\begin{circus}
\Gamma'_A (\lpar cs \rpar x : \langle v_1,...,v_n \rangle \circspot \lpar ns(x) \rpar A(x)) \circdef
\\\t1
\left (\begin{array}{l}A(v_1)
   \\ \lpar ns(v_1) | cs | \bigcup\{x : \{v_2,...,v_n\} \circspot ns(x)\} \rpar
   \\ \left (\begin{array}{l}
     \ldots
      \left (\begin{array}{l}
      \Gamma'_A(A(v_n -1))
      \\ \lpar ns(v_n -1 ) | cs | ns(v_n) \rpar
      \\ A(v_n)\end{array}\right )\end{array}\right )\end{array}\right )

\end{circus}
is written in Haskell as:
\begin{code}
gamma_prime_CAction (CSPRepParalNS (CSExpr cs) [Choose x (ZSetDisplay lsx)]
          [ZVar (x1,[],tx2)]
          (CSPParAction a [ZVar (x2,[],tx3)]))
  = case (member (ZVar x) [ZVar (x1,[],tx2)]) && (member (ZVar x) [ZVar (x2,[],tx3)]) of
    True -> gamma_prime_CAction (rep_CSPRepParalNS a cs (x1,[],tx2) x lsx)
    _  -> (CSPRepParalNS (CSExpr cs) [Choose x (ZSetDisplay lsx)]
          [ZVar (x1,[],tx2)]
          (CSPParAction a [ZVar (x2,[],tx3)]))
gamma_prime_CAction (CSPRepParalNS (CSExpr cs) [Choose (x,[],tx) (ZSetDisplay lsx)] [ZVar (x1,[],tx1)] act)
  = (CSPRepParalNS (CSExpr cs) [Choose (x,[],tx) (ZSetDisplay lsx)] [ZVar (x1,[],tx1)] (gamma_prime_CAction act))
\end{code}
\end{gammaprime}
\begin{gammaprime}
\begin{circus}
\Gamma'_A ( \circval Decl \circspot P) \circdef \circval Decl \circspot \Gamma'_A (P)
\end{circus}
is written in Haskell as:
\begin{code}
gamma_prime_CAction (CActionCommand (CValDecl xs a))
  = (CActionCommand (CValDecl xs (gamma_prime_CAction a)))
\end{code}
\end{gammaprime}
\begin{gammaprime}
\begin{circus}
\Gamma'_A \left (\begin{array}{l}x_0,\ldots,x_n:=e_0,\ldots,e_n\end{array}\right ) \circdef
\\\t1 set.x_0!e_0 \then
\\\t1\ldots\then
\\\t1 set.x_n!e_n \then \Skip
\end{circus}

\begin{code}
gamma_prime_CAction (CActionCommand (CAssign varls valls))
  =  (make_lset_com gamma_prime_CAction varls valls CSPSkip)
\end{code}
% \begin{circus}
% \Gamma'_A (\circif g \circthen A \circfi ) \defs
%    \\\t1\circif g \circthen \Gamma'_A (A) \circfi
% \end{circus}
% \begin{code}
% gamma_prime_CAction (CActionCommand (CIf (CircGAction g a)))
%   = (CActionCommand (CIf (CircGAction g (gamma_prime_CAction a))))

% \end{code}
\end{gammaprime}
\begin{gammaprime}
\begin{circus}
\Gamma'_A (A \circhide cs) \circdef \Gamma'_A (A) \circhide cs
\end{circus}

is written in Haskell as:

\begin{code}
gamma_prime_CAction (CSPHide a cs) = (CSPHide (gamma_prime_CAction a) cs)
\end{code}
\end{gammaprime}
\begin{gammaprime}
\begin{circus}
\Gamma'_A
   \left (\begin{array}{l}
   \circif g_0  \circthen A_0
   \\\t1\circelse \ldots
   \\\t1 \circelse g_n  \circthen A_n
   \\\circfi
   \end{array}\right ) \defs
   \\\t1\circif g_0 \circthen \Gamma'_A (A_0)
   \\\t2\circelse \ldots
   \\\t2 \circelse g_n \circthen \Gamma'_A (A_n)
   \\\t1\circfi
\end{circus}

\begin{code}
gamma_prime_CAction (CActionCommand (CIf glx))
  = (CActionCommand (CIf (mk_guard_pair gamma_prime_CAction guard_pair)))
  where
   guard_pair = get_guard_pair glx
\end{code}
\end{gammaprime}
\begin{gammaprime}
\begin{circus}
\Gamma'_A (\circmu X \circspot A(X)) \circdef \circmu X \circspot \Gamma'_A(A(X))
\end{circus}

is written in Haskell as:

\begin{code}
gamma_prime_CAction (CSPRecursion x c) = (CSPRecursion x (gamma_prime_CAction c))
\end{code}
\end{gammaprime}
\begin{gammaprime}
\begin{circus}
\Gamma'_A (\Interleave x : \langle v_1,...,v_n \rangle \circspot A(x)) \circdef
\\\t1
\left (\begin{array}{l}A(v_1)
   \\ \lpar ns(v_1) | \bigcup\{x : \{v_2,...,v_n\} \circspot ns(x)\} \rpar
   \\ \left (\begin{array}{l}
     \ldots
      \left (\begin{array}{l}
      \Gamma'_A(A(v_n -1))
      \\ \lpar ns(v_n -1 ) | ns(v_n)\rpar
      \\ A(v_n)\end{array}\right )\end{array}\right )\end{array}\right )

\end{circus}

is written in Haskell as:

\begin{code}
gamma_prime_CAction (CSPRepInterlNS [Choose x (ZSetDisplay lsx)]
          [ZVar ns1]
          (CSPParAction a ns2))
  = case (member (ZVar x) [ZVar ns1] ) && (member (ZVar x) ns2 ) of
    True -> gamma_prime_CAction (rep_CSPRepInterlNS a ns1 x lsx)
    _  ->  (CSPRepInterlNS [Choose x (ZSetDisplay lsx)]
          [ZVar ns1]
          (CSPParAction a ns2))
gamma_prime_CAction (CSPRepInterlNS [Choose (x,[],t1) (ZSetDisplay lsx)]
          ([ZVar (x1,[],t2)])
          act)
  = (CSPRepInterlNS [Choose (x,[],t1) (ZSetDisplay lsx)]
          ([ZVar (x1,[],t2)])
          (gamma_prime_CAction act))
\end{code}
\end{gammaprime}
\begin{gammaprime}
\begin{circus}
\Gamma'_A (\{g\}) \circdef \prefixcolon [g, true]
\end{circus}

\begin{code}
gamma_prime_CAction (CActionCommand (CommandBrace g))
  = gamma_prime_CAction (CActionCommand (CPrefix g (ZTrue {reason = []})))
\end{code}
\end{gammaprime}
\begin{gammaprime}
\begin{circus}
\Gamma'_A ([g]) \circdef \prefixcolon [g]
\end{circus}

\begin{code}
gamma_prime_CAction (CActionCommand (CommandBracket g))
  = gamma_prime_CAction (CActionCommand (CPrefix1 g))
\end{code}
\end{gammaprime}
\begin{gammaprime}
\begin{circus}
\Gamma'_A (A[old_1,...,old_n := new_1,...,new_n) \circdef
\\\t1A[new_1,...,new_n/old_1,...,old_n)
\end{circus}

\begin{code}
gamma_prime_CAction (CSPRenAction a (CRenameAssign left right))
  = (CSPRenAction a (CRename right left))
\end{code}
\end{gammaprime}
\begin{gammaprime}
In order to pattern match any other \Circus\ construct not mentioned here, we propagate the $gamma\_prime_CAction$ function to the remainder of the constructs.

\begin{code}
gamma_prime_CAction (CActionSchemaExpr vZSExpr) = (CActionSchemaExpr vZSExpr)
gamma_prime_CAction (CActionName vZName) = (CActionName vZName)
gamma_prime_CAction (CSPCommAction vComm vCAction) = (CSPCommAction vComm (gamma_prime_CAction vCAction))
gamma_prime_CAction (CSPNSParal v1NSExp vCSExp v2NSExp v1CAction v2CAction) = (CSPNSParal v1NSExp vCSExp v2NSExp (gamma_prime_CAction v1CAction) (gamma_prime_CAction v2CAction))
gamma_prime_CAction (CSPParal vCSExp v1CAction v2CAction) = (CSPParal vCSExp (gamma_prime_CAction v1CAction) (gamma_prime_CAction v2CAction))
gamma_prime_CAction (CSPNSInter v1NSExp v2NSExp v1CAction v2CAction) = (CSPNSInter v1NSExp v2NSExp (gamma_prime_CAction v1CAction) (gamma_prime_CAction v2CAction))
gamma_prime_CAction (CSPInterleave v1CAction v2CAction) = (CSPInterleave (gamma_prime_CAction v1CAction) (gamma_prime_CAction v2CAction))
gamma_prime_CAction (CSPParAction vZName vZExpr_lst) = (CSPParAction vZName vZExpr_lst)
gamma_prime_CAction (CSPRenAction vZName vCReplace) = (CSPRenAction vZName vCReplace)
gamma_prime_CAction (CSPUnfAction vZName vCAction) = (CSPUnfAction vZName (gamma_prime_CAction vCAction))
gamma_prime_CAction (CSPUnParAction vZGenFilt_lst vCAction vZName) = (CSPUnParAction vZGenFilt_lst (gamma_prime_CAction vCAction) vZName)
-- gamma_prime_CAction (CSPRepSeq vZGenFilt_lst vCAction) = (CSPRepSeq vZGenFilt_lst (gamma_prime_CAction vCAction))
-- gamma_prime_CAction (CSPRepExtChoice vZGenFilt_lst vCAction) = (CSPRepExtChoice vZGenFilt_lst (gamma_prime_CAction vCAction))
-- gamma_prime_CAction (CSPRepIntChoice vZGenFilt_lst vCAction) = (CSPRepIntChoice vZGenFilt_lst (gamma_prime_CAction vCAction))
-- gamma_prime_CAction (CSPRepParalNS vCSExp vZGenFilt_lst vNSExp vCAction) = (CSPRepParalNS vCSExp vZGenFilt_lst vNSExp (gamma_prime_CAction vCAction))
-- gamma_prime_CAction (CSPRepParal vCSExp vZGenFilt_lst vCAction) = (CSPRepParal vCSExp vZGenFilt_lst (gamma_prime_CAction vCAction))
-- gamma_prime_CAction (CSPRepInterlNS vZGenFilt_lst vNSExp vCAction) = (CSPRepInterlNS vZGenFilt_lst vNSExp (gamma_prime_CAction vCAction))
-- gamma_prime_CAction (CSPRepInterl vZGenFilt_lst vCAction) = (CSPRepInterl vZGenFilt_lst (gamma_prime_CAction vCAction))
gamma_prime_CAction x = x
\end{code}
\end{gammaprime}
