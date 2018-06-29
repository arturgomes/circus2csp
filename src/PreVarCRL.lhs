%!TEX root = MAIN.tex
\chapter{Implemented \Circus\ Refinement Laws}

\ignore{
\begin{code}
{-# OPTIONS -Wall #-}

module PreVarCRL
where
import AST
import PreVarOmegaDefs
import Subs

\end{code}
}
\section{Process prevar_refinement}


\begin{lawn}[prom-var-state]{3}
\begin{circus}
\circbegin
\\\qquad (\circstate S)
\\\qquad L(x : T)
\\\qquad \circspot (\circvar x : T \circspot MA)
\\\circend
\\=\\
\circbegin
\\\qquad (\circstate S \land [ x : T ])
\\\qquad L(\_)
\\\quad \circspot MA
\\\circend
\end{circus}
\label{law:promVarState}

\end{lawn}

Both prevar_refinement laws mention the use of $L$ as schemas. However, as we do not
support schemas as actions in our tool, and as we expand the definition of all
actions to the main action $MA$, we'll have the following implementation.
\begin{code}
prevar_crl_prom_var_state :: ZPara -> Refinement ZPara
prevar_crl_prom_var_state e@(Process (CProcess p (ProcDef (ProcMain (ZSchemaDef (ZSPlain s []) (ZSchema zs)) aclst (CActionCommand (CVarDecl va2 ma2))))))
  = Done{orig = Just e, refined = Just ref, proviso = []}
      where
        fvs1 = free_var_CAction (CActionCommand (CVarDecl va2 ma2))
        fvs2 = free_var_CAction ma2
        ffvs = diff_varset fvs2 fvs1
        gfs = rename_genfilt_lv p va2
        nl = rename_list_lv p (varset_to_zvars ffvs) va2
        subs = make_subinfo nl fvs2
        finalsubs = sub_CAction subs ma2
        ref = (Process (CProcess p (ProcDef (ProcMain (ZSchemaDef (ZSPlain s []) (ZSchema (zs++gfs))) aclst finalsubs))))
prevar_crl_prom_var_state e@(Process (CProcess p (ProcDefSpot x1a (ProcDef (ProcMain (ZSchemaDef (ZSPlain s []) (ZSchema zs)) aclst (CActionCommand (CVarDecl va2 ma2)))))))
  = Done{orig = Just e, refined = Just ref, proviso = []}
      where
        fvs1 = free_var_CAction (CActionCommand (CVarDecl va2 ma2))
        fvs2 = free_var_CAction ma2
        ffvs = diff_varset fvs2 fvs1
        gfs = rename_genfilt_lv p va2
        nl = rename_list_lv p (varset_to_zvars ffvs) va2
        subs = make_subinfo nl fvs2
        finalsubs = sub_CAction subs ma2
        ref = (Process (CProcess p (ProcDefSpot x1a (ProcDef (ProcMain (ZSchemaDef (ZSPlain s []) (ZSchema (zs++gfs))) aclst finalsubs)))))
prevar_crl_prom_var_state _ = None
\end{code}


\begin{lawn}[prom-var-state-2]{3}
\begin{circus}
\circbegin
\\\qquad L(x : T)
\\\qquad \circspot (\circvar x : T \circspot MA)
\\\circend
\\=\\
\circbegin\\
\qquad (\circstate [ x : T ]) \\
\qquad L(\_)\\
\qquad \circspot MA\\
 \circend
\end{circus}
\label{law:promVarState2}


\end{lawn}

\begin{code}

prevar_crl_prom_var_state2 :: ZPara -> Refinement ZPara

prevar_crl_prom_var_state2 e@(Process (CProcess p (ProcDef (ProcStalessMain aclst (CActionCommand (CVarDecl va2 ma2))))))
  = Done{orig = Just e, refined = Just ref, proviso = []}
      where
  ref = (Process (CProcess p (ProcDef (ProcMain (ZSchemaDef (ZSPlain ("S"++p) []) (ZSchema gfs)) aclst finalsubs))))
  fvs1 = free_var_CAction (CActionCommand (CVarDecl va2 ma2))
  fvs2 = free_var_CAction ma2
  ffvs = diff_varset fvs2 fvs1
  nl = rename_list_lv p (varset_to_zvars ffvs) va2
  gfs = rename_genfilt_lv p va2
  subs = make_subinfo nl fvs2
  finalsubs = sub_CAction subs ma2
prevar_crl_prom_var_state2 e@(Process (CProcess p (ProcDefSpot x1a (ProcDef (ProcStalessMain aclst (CActionCommand (CVarDecl va2 ma2)))))))
  = Done{orig = Just e, refined = Just ref, proviso = []}
      where
  ref = (Process (CProcess p (ProcDefSpot x1a (ProcDef (ProcMain (ZSchemaDef (ZSPlain ("S"++p) []) (ZSchema gfs)) aclst finalsubs)))))
  fvs1 = free_var_CAction (CActionCommand (CVarDecl va2 ma2))
  fvs2 = free_var_CAction ma2
  ffvs = diff_varset fvs2 fvs1
  nl = rename_list_lv p (varset_to_zvars ffvs) va2
  gfs = rename_genfilt_lv p va2
  subs = make_subinfo nl fvs2
  finalsubs = sub_CAction subs ma2
prevar_crl_prom_var_state2 _ = None
\end{code}
\section{Refinement calculator at \Circus\ process level}
\begin{code}
reflawsZPara :: [ZPara -> Refinement ZPara]
reflawsZPara = [prevar_crl_prom_var_state,prevar_crl_prom_var_state2]
\end{code}
\begin{code}
applyZPara :: (PRFun ZPara) -> (PRFun ZPara)
applyZPara r e@(Process _) = r e
applyZPara _ _ = None
\end{code}

\begin{code}
applyZParas :: PRFun ZPara -> [ZPara] -> [Refinement ZPara]
applyZParas _ [] = []
applyZParas r [e] = [applyZPara r e]
applyZParas r (e:es) = (applyZPara r e):(applyZParas r es)
\end{code}

\subsection{Checking the prevar_refinement results}

\begin{code}
prevar_runRefinementZp :: ZPara -> Maybe ZPara
prevar_runRefinementZp x = prevar_getRef $ prevar_refineZp reflawsZPara x

prevar_runStepRefinementZp :: ZPara -> [Refinement ZPara]
prevar_runStepRefinementZp x = prevar_refineZp reflawsZPara x

refineCActionZp :: ZPara -> ZPara
refineCActionZp x = prevar_get_refinedZp $ last (prevar_refineZp reflawsZPara x)
\end{code}
\begin{code}
prevar_cprevar_refineZp :: [PRFun ZPara]
                 -> [PRFun ZPara]
                 -> ZPara
                 -> [Refinement ZPara]
                 -> [Refinement ZPara]

prevar_cprevar_refineZp _ [] _ _ = [None]
prevar_cprevar_refineZp _ [r] e steps =
    reverse (results:steps)
    where
      results = applyZPara r e

prevar_cprevar_refineZp lst (r:rs) e steps =
    case rsx of
      ei@(Done{orig=Just a, refined=Just e', proviso=_}) ->
        case a==e' of
          True -> prevar_cprevar_refineZp lst rs e steps
          False -> prevar_cprevar_refineZp lst lst e' (ei:steps)
      None -> prevar_cprevar_refineZp lst rs e steps
      _ -> [None]
    where rsx = applyZPara r e

prevar_refineZp :: [PRFun ZPara] -> ZPara -> [Refinement ZPara]
prevar_refineZp f g = prevar_cprevar_refineZp f f g []
\end{code}

\subsection{Printing the Refinement Steps}
First we get the bits from the $Refinement$ record
\begin{code}
prevar_get_origZp :: Refinement ZPara -> ZPara
prevar_get_origZp (Done{orig=Just a,refined=_,proviso=_}) = a
prevar_get_origZp _ = error "Unable to find the original ZPara on the prevar_refinement"
prevar_get_refinedZp :: Refinement ZPara -> ZPara
prevar_get_refinedZp (Done{orig=_,refined=Just b,proviso=_}) = b
prevar_get_refinedZp (Done{orig=Just a,refined=Nothing,proviso=_}) = a
prevar_get_refinedZp _ = error "Unable to find the refined ZPara on the prevar_refinement"
prevar_get_provisoZp :: Refinement ZPara -> [ZPred]
prevar_get_provisoZp None = []
prevar_get_provisoZp (Done{orig=_,refined=_,proviso=c}) = c
\end{code}

\subsection{Testing the tool}
\begin{code}
prevar_testproc1 :: ZPara
prevar_testproc1 = (Process (CProcess "P" (ProcDef (ProcStalessMain [CParAction "L" (CircusAction (CActionCommand (CVarDecl [Choose ("x",[],[]) (ZVar ("T",[],[]))] CSPSkip)))] (CActionCommand (CVarDecl [Choose ("x",[],[]) (ZVar ("T",[],[]))] CSPSkip))))))
prevar_testproc2 :: ZPara
prevar_testproc2 = (Process (CProcess "AChrono" (ProcDef (ProcMain (ZSchemaDef (ZSPlain "AState" []) (ZSchema [Choose ("sec",[],[]) (ZVar ("RANGE",[],[])),Choose ("min",[],[]) (ZVar ("RANGE",[],[]))])) [] (CActionCommand (CVarDecl [Choose ("ms",[],[]) (ZVar ("RANGE",[],[]))] (CActionCommand (CAssign [("sec",[],[]),("min",[],[])] [ZVar ("ms",[],[]),ZInt 0]))))))))

-- testcac0 = (Process (CProcess "LocWakeUp" (ProcDef (ProcMain (ZSchemaDef (ZSPlain "WState") (ZSchema [Choose ("sec",[],[]) (ZVar ("RANGE",[],[])),Choose ("min",[],[]) (ZVar ("RANGE",[],[])),Choose ("buzz",[],[]) (ZVar ("ALARM",[],[]))])) [] (CActionCommand (CVarDecl [Choose ("ms",[],[]) (ZVar ("RANGE",[],[]))] (CSPSeq (CActionCommand (CAssign [("sec",[],[])] [ZVar ("ms",[],[])])) (CSPSeq (CActionCommand (CAssign [("sec",[],[]),("min",[],[]),("buzz",[],[])] [ZInt 0,ZInt 0,ZVar ("OFF",[],[])])) (CSPRecursion "X" (CSPSeq (CSPHide (CSPCommAction (ChanComm "tick" []) (CSPSeq (CActionName "WIncSec") (CSPExtChoice (CSPExtChoice (CSPExtChoice (CSPExtChoice (CSPGuard (ZEqual (ZVar ("sec",[],[])) (ZInt 0)) (CActionName "WIncMin")) (CSPGuard (ZNot (ZEqual (ZVar ("sec",[],[])) (ZInt 0))) CSPSkip)) (CSPGuard (ZEqual (ZVar ("min",[],[])) (ZInt 1)) (CSPCommAction (ChanComm "radioOn" []) (CActionCommand (CAssign [("buzz",[],[])] [ZVar ("ON",[],[])]))))) (CSPCommAction (ChanComm "time" []) (CSPCommAction (ChanComm "out" [ChanOutExp (ZTuple [ZVar ("min",[],[]),ZVar ("sec",[],[])])]) CSPSkip))) (CSPCommAction (ChanComm "snooze" []) (CActionCommand (CAssign [("buzz",[],[])] [ZVar ("OFF",[],[])])))))) (CChanSet ["tick"])) (CActionName "X")))))))))) )
-- testcac2 = (CActionCommand (CVarDecl [Choose ("ms",[],[]) (ZVar ("RANGE",[],[]))] (CSPSeq (CActionCommand (CAssign [("sec",[],[])] [ZVar ("ms",[],[])])) (CSPSeq (CActionCommand (CAssign [("sec",[],[]),("min",[],[]),("buzz",[],[])] [ZInt 0,ZInt 0,ZVar ("OFF",[],[])])) (CSPRecursion "X" (CSPSeq (CSPHide (CSPCommAction (ChanComm "tick" []) (CSPSeq (CActionName "WIncSec") (CSPExtChoice (CSPExtChoice (CSPExtChoice (CSPExtChoice (CSPGuard (ZEqual (ZVar ("sec",[],[])) (ZInt 0)) (CActionName "WIncMin")) (CSPGuard (ZNot (ZEqual (ZVar ("sec",[],[])) (ZInt 0))) CSPSkip)) (CSPGuard (ZEqual (ZVar ("min",[],[])) (ZInt 1)) (CSPCommAction (ChanComm "radioOn" []) (CActionCommand (CAssign [("buzz",[],[])] [ZVar ("ON",[],[])]))))) (CSPCommAction (ChanComm "time" []) (CSPCommAction (ChanComm "out" [ChanOutExp (ZTuple [ZVar ("min",[],[]),ZVar ("sec",[],[])])]) CSPSkip))) (CSPCommAction (ChanComm "snooze" []) (CActionCommand (CAssign [("buzz",[],[])] [ZVar ("OFF",[],[])])))))) (CChanSet ["tick"])) (CActionName "X")))))))
-- testvac1 = [Choose ("ms",[],[]) (ZVar ("RANGE",[],[]))]
-- testcac1 =  (CSPSeq (CActionCommand (CAssign [("sec",[],[])] [ZVar ("ms",[],[])])) (CSPSeq (CActionCommand (CAssign [("sec",[],[]),("min",[],[]),("buzz",[],[])] [ZInt 0,ZInt 0,ZVar ("OFF",[],[])])) (CSPRecursion "X" (CSPSeq (CSPHide (CSPCommAction (ChanComm "tick" []) (CSPSeq (CActionName "WIncSec") (CSPExtChoice (CSPExtChoice (CSPExtChoice (CSPExtChoice (CSPGuard (ZEqual (ZVar ("sec",[],[])) (ZInt 0)) (CActionName "WIncMin")) (CSPGuard (ZNot (ZEqual (ZVar ("sec",[],[])) (ZInt 0))) CSPSkip)) (CSPGuard (ZEqual (ZVar ("min",[],[])) (ZInt 1)) (CSPCommAction (ChanComm "radioOn" []) (CActionCommand (CAssign [("buzz",[],[])] [ZVar ("ON",[],[])]))))) (CSPCommAction (ChanComm "time" []) (CSPCommAction (ChanComm "out" [ChanOutExp (ZTuple [ZVar ("min",[],[]),ZVar ("sec",[],[])])]) CSPSkip))) (CSPCommAction (ChanComm "snooze" []) (CActionCommand (CAssign [("buzz",[],[])] [ZVar ("OFF",[],[])])))))) (CChanSet ["tick"])) (CActionName "X")))))

-- test2 = (ZAnd (ZAnd (ZMember (ZVar ("sv_LocWakeUp_sv_LocWakeUp_buzz_U_ALA_U_ALA",[],[])) (ZVar ("ALARM",[],[]))) (ZMember (ZVar ("sv_LocWakeUp_sv_LocWakeUp_min_U_RAN_U_RAN",[],[])) (ZVar ("RANGE",[],[])))) (ZMember (ZVar ("sv_LocWakeUp_sv_LocWakeUp_sec_U_RAN_U_RAN",[],[])) (ZVar ("RANGE",[],[]))))
\end{code}

\section{Action Refinement}
% law 1


\begin{lawn}[var-exp-par]{3}\sl%ok

    \begin{circus}
        (\circvar\ d:T \circspot A1) \lpar ns1 | cs | ns2 \rpar A2
        \\ = \\
        (\circvar\ d:T \circspot A1 \lpar ns1 | cs | ns2 \rpar A2) %
    \end{circus}%
    \begin{itemize}
        \item From D24.1 -- $\{d,d'\} \cap FV(A2) = \emptyset$
    \end{itemize}
  \label{law:var-exp-par}

\end{lawn}
\begin{code}
prevar_crl_var_exp_par :: CAction -> Refinement CAction
prevar_crl_var_exp_par e@(CSPNSParal ns1 cs ns2 (CActionCommand (CVarDecl [(Choose (d,[],tx) t)] a1)) a2)
  = Done{orig = Just e, refined = Just ref, proviso = [p1]}
    where
      ref = (CActionCommand (CVarDecl [(Choose (d,[],tx) t)] (CSPNSParal ns1 cs ns2 a1 a2)))
      p1 = (ZEqual (ZCall (ZVar ("\\cap",[],[])) (ZTuple [ZSetDisplay [ZVar (d,[],tx),ZVar (d,[ZPrime],tx)],ZSetDisplay $ zvar_to_zexpr $ varset_to_zvars (free_var_CAction a2)])) (ZVar ("\\emptyset",[],[])))
prevar_crl_var_exp_par _ = None
\end{code}
% law 2


\begin{lawn}[var-exp-par-2]{3}\sl

    \begin{circus}
        (\circvar\ d:T \circspot A1) \lpar ns1 | cs | ns2 \rpar (\circvar\ d:T \circspot A2)
        \\ = \\
        (\circvar\ d:T \circspot A1 \lpar ns1 | cs | ns2 \rpar A2) %
    \end{circus}%
  \label{law:var-exp-par2}

\end{lawn}
\begin{code}
prevar_crl_var_exp_par2 :: CAction -> Refinement CAction
prevar_crl_var_exp_par2 e@(CSPNSParal ns1 cs ns2
                  (CActionCommand (CVarDecl d1 a1))
                  (CActionCommand (CVarDecl d2 a2)))
  = case (d1 == d2) of
      True -> Done{orig = Just e, refined = Just (CActionCommand (CVarDecl d1
                      (CSPNSParal ns1 cs ns2 a1 a2))),
          proviso = []}
      False -> None
prevar_crl_var_exp_par2 _ = None
\end{code}
% law 3


\begin{lawn}[var-exp-rec]{3}\sl
    \begin{circus}
      \circmu X \circspot (\circvar x : T \circspot F(X))
      \\=\\
      \circvar x : T  \circspot (\circmu X \circspot F(X))
    \end{circus}
    \begin{prov}
    \textbf{x is initiated before use in F}
    \end{prov}
  \label{law:varExpRec}

\end{lawn}
\begin{code}
prevar_crl_var_exp_rec :: CAction -> Refinement CAction
prevar_crl_var_exp_rec e@(CSPRecursion mX (CActionCommand (CValDecl [Choose (x,[],tx) (ZVar (t,[],s))] (CSPUnfAction f (CActionName mX1)))))
  = case (mX == mX1) of
      True -> Done{orig = Just e, refined = Just (CActionCommand (CValDecl [Choose (x,[],tx) (ZVar (t,[],s))] (CSPRecursion mX (CSPUnfAction f (CActionName mX))))), proviso=[]}
      False -> None
prevar_crl_var_exp_rec _ = None
\end{code}
% law 4


\begin{lawn}[Variable block/Sequence---extension$^*$]{3}\sl
   \begin{circus}
       A1 \circseq (\circvar\ x:T \circspot A2) \circseq A3
      \\ = \\
      (\circvar\ x:T \circspot A1 \circseq\ A2 \circseq A3) %
   \end{circus}%
   \begin{prov}
       $x \notin FV(A1) \cup FV(A3)$
   \end{prov}
 \label{law:variableBlockSequenceExtension}

\end{lawn}
\begin{code}
prevar_crl_variableBlockSequenceExtension :: CAction -> Refinement CAction
prevar_crl_variableBlockSequenceExtension
      e@(CSPSeq a1 (CSPSeq (CActionCommand (CVarDecl [(Choose x t)] a2)) a3))
  =  Done{orig = Just e, refined = Just ref, proviso=[prov]}
  where
    ref = (CActionCommand (CVarDecl [(Choose x t)] (CSPSeq a1 (CSPSeq a2 a3))))
    prov = (ZMember (ZSetDisplay [ZVar x]) (ZCall (ZVar ("\\cup",[],[])) (ZTuple [ZSetDisplay  $ zvar_to_zexpr $ varset_to_zvars (free_var_CAction a1),ZSetDisplay $ zvar_to_zexpr $ varset_to_zvars (free_var_CAction a3)])))
prevar_crl_variableBlockSequenceExtension
        e@(CSPSeq a1 (CSPSeq a3 (CActionCommand (CVarDecl [(Choose x t)] a2))))
  =  Done{orig = Just e, refined = Just ref, proviso=[prov]}
  where
    ref = (CActionCommand (CVarDecl [(Choose x t)] (CSPSeq a1 (CSPSeq a2 a3))))
    prov = (ZMember (ZSetDisplay [ZVar x]) (ZCall (ZVar ("\\cup",[],[])) (ZTuple [ZSetDisplay  $ zvar_to_zexpr $ varset_to_zvars (free_var_CAction a1),ZSetDisplay $ zvar_to_zexpr $ varset_to_zvars (free_var_CAction a3)])))
prevar_crl_variableBlockSequenceExtension
        e@(CSPSeq a1 (CActionCommand (CVarDecl [(Choose x t)] a2)))
  =  Done{orig = Just e, refined = Just ref, proviso=[prov]}
  where
    ref = (CActionCommand (CVarDecl [(Choose x t)] (CSPSeq a1 a2)))
    prov = (ZMember (ZSetDisplay [ZVar x]) (ZSetDisplay $ zvar_to_zexpr $ varset_to_zvars (free_var_CAction a1)))
prevar_crl_variableBlockSequenceExtension
      e@(CSPSeq (CActionCommand (CVarDecl [(Choose x t)] a1)) a2)
  =  Done{orig = Just e, refined = Just ref, proviso=[prov]}
  where
    ref = (CActionCommand (CVarDecl [(Choose x t)] (CSPSeq a1 a2)))
    prov = (ZMember (ZSetDisplay [ZVar x]) (ZSetDisplay $ zvar_to_zexpr $ varset_to_zvars (free_var_CAction a2)))
prevar_crl_variableBlockSequenceExtension _ = None
\end{code}
% law 5 - NOT WORKING AND I DONT KNOW WHY!!!!
%

% \begin{lawn}[Variable Substitution$^*$]{3}\sl
%    \begin{circus}
%        A(x)
%        \\ = \\
%        \circvar\ y \circspot y \prefixcolon [y'=x] \circseq\ A(y)%
%    \end{circus}%
%    \begin{prov}
%        $y \notin FV(A)$
%    \end{prov}
%  \label{law:variableSubstitution}
%
% \end{lawn}

% \begin{code}
% prevar_crl_variableSubstitution (CSPParAction a [ZVar (x,[])]) y
%   =undefined --CVarDecl [(ZVar (y,[]))] (CSPSeq (CActionCommand (CAssumpt [(y)] ZTrue{reason=[]} )))
% \end{code}
% law 6


\begin{lawn}[Variable block introduction$^*$]{3}\sl
   \begin{circus}
       A = \circvar\ x:T \circspot A %
   \end{circus}%
   \begin{prov}
       $x \notin FV(A)$
   \end{prov}
 \label{law:variableBlockIntroduction}

\end{lawn}
\begin{code}
prevar_crl_variableBlockIntroduction :: CAction -> ZVar -> ZExpr -> Refinement CAction
prevar_crl_variableBlockIntroduction a x t
  =  Done{orig = Just a, refined = Just (CActionCommand (CVarDecl [(Choose x t)] a)),
          proviso=[prov]}
  where
    prov = (ZNot (ZMember (ZVar x) (ZSetDisplay $ zvar_to_zexpr $ varset_to_zvars (free_var_CAction a))))
\end{code}
\begin{code}
prevar_crl_variableBlockIntroduction_backwards :: CAction -> Refinement CAction
prevar_crl_variableBlockIntroduction_backwards e@(CActionCommand (CVarDecl [(Choose (x,[],tx1) _)] a))
  =  Done{orig = Just e, refined = Just a, proviso = [prov]}
  where
  prov = (ZNot (ZMember (ZVar (x,[],tx1)) (ZSetDisplay $ zvar_to_zexpr $ varset_to_zvars (free_var_CAction a))))

prevar_crl_variableBlockIntroduction_backwards e@(CSPCommAction (ChanComm x f) (CActionCommand (CValDecl [Choose (y,[],tx1) (ZVar (t,[],tx2))] a)))
  =  Done{orig = Just e, refined = Just ref, proviso = [prov]}
  where
    ref = (CActionCommand (CValDecl [Choose (y,[],tx1) (ZVar (t,[],tx2))] (CSPCommAction (ChanComm x f) a)))
    prov = (ZNot (ZMember (ZVar (y,[],tx1)) (ZSetDisplay $ zvar_to_zexpr $ varset_to_zvars (free_var_CAction (CSPCommAction (ChanComm x f) a)))))
prevar_crl_variableBlockIntroduction_backwards _ = None
\end{code}
% law 6


\begin{lawn}[Variable block introduction---2$^*$]{3}\sl
   \begin{circus}
       \circvar\ x:T_1 ; y:T_2 \circspot A  = \circvar\ y:T_2 \circspot A %
   \end{circus}%
   \begin{prov}
       $x \notin FV(A)$
   \end{prov}
 \label{law:variableBlockIntroduction}

\end{lawn}
\begin{code}
prevar_crl_variableBlockIntroduction2_backwards :: CAction -> Refinement CAction
prevar_crl_variableBlockIntroduction2_backwards e@(CActionCommand (CVarDecl ((Choose (x,[],tx) _):xs) a))
  =  Done{orig = Just e, refined = Just (CActionCommand (CVarDecl xs a)), proviso = [prov]}
  where
    prov = (ZNot (ZMember (ZVar (x,[],tx)) (ZSetDisplay $ zvar_to_zexpr $ varset_to_zvars (free_var_CAction a))))
prevar_crl_variableBlockIntroduction2_backwards _ = None
\end{code}
% law 7


\begin{lawn}[join---blocks]{3}\sl
    \begin{circus}
        \circvar\ x:T_1 \circspot \circvar\ y:T_2 \circspot A
        \\ = \\
        \circvar\ x:T_1 ; y:T_2 \circspot A
    \end{circus}%

  \label{law:joinBlocks}

\end{lawn}
\begin{code}
prevar_crl_joinBlocks :: CAction -> Refinement CAction
prevar_crl_joinBlocks e@(CActionCommand (CVarDecl [(Choose x t1)] (CActionCommand (CVarDecl [(Choose y t2)] a))))
  =  Done{orig = Just e, refined = Just (CActionCommand (CVarDecl [(Choose x t1),(Choose y t2)] a)),
          proviso=[]}
prevar_crl_joinBlocks _ = None
\end{code}



\begin{lawn}[Sequence unit]{3}\sl
   \begin{circus}
     (A) \Skip \circseq A = A\\ %
     (B) A = A \circseq \Skip %
   \end{circus}
 \label{law:seqSkipUnit}

\end{lawn}
\begin{code}
prevar_crl_seqSkipUnit_a :: CAction -> Refinement CAction
prevar_crl_seqSkipUnit_a e@(CSPSeq CSPSkip a) =  Done{orig = Just e, refined = Just a, proviso=[]}
prevar_crl_seqSkipUnit_a _ = None
prevar_crl_seqSkipUnit_b :: CAction -> Refinement CAction
prevar_crl_seqSkipUnit_b e@(CSPSeq a CSPSkip) =  Done{orig = Just e, refined = Just a, proviso=[]}
prevar_crl_seqSkipUnit_b _ = None
-- prevar_crl_seqSkipUnit_b :: CAction -> Refinement CAction
-- prevar_crl_seqSkipUnit_b a =  Done{orig = Just a, refined = Just (CSPSeq a CSPSkip),proviso=[]}
\end{code}



\begin{lawn}[Recursion unfold]{3}\sl
   \begin{circus}
    \circmu X \circspot F(X)
    \\ = \\
    F(\circmu X \circspot F(X))
   \end{circus}
 \label{law:recUnfold}

\end{lawn}
\begin{code}
prevar_crl_recUnfold :: CAction -> Refinement CAction
prevar_crl_recUnfold e@(CSPRecursion x1 (CSPUnfAction f (CActionName x2)))
  = case (x1 == x2) of
      True -> Done{orig = Just e, refined = Just (CSPUnfAction f (CSPRecursion x1 (CSPUnfAction f (CActionName x1)))),proviso=[]}
      False -> None
prevar_crl_recUnfold _ = None
\end{code}



\begin{lawn}[Parallelism composition/External choice---expansion$^*$]{3}\sl
   \begin{circus}
       (\Extchoice i \circspot a_i \then A_i) \lpar ns1 | cs | ns2 \rpar (\Extchoice j \circspot b_j \then B_j)
       \\ = \\
       (\Extchoice i \circspot a_i \then A_i) \lpar ns1 | cs | ns2 \rpar ((\Extchoice j \circspot b_j \then B_j) \extchoice (c \then C)) \\ %
   \end{circus}%
   \begin{provs}
       \item $\bigcup_i \{ a_i \} \subseteq cs$
       \item $c \in cs$ %
       \item $c \notin \bigcup_i \{ a_i \} $%
       \item $c \notin \bigcup_j \{ b_j \}$%
   \end{provs}
 \label{law:parallelismExternalChoiceExpansion}

\end{lawn}
%
% \begin{code}
% prevar_crl_parallelismExternalChoiceExpansion :: CAction -> Refinement CAction
% prevar_crl_parallelismExternalChoiceExpansion
%   e@(CSPNSParal ns1 cs ns2
%       (CSPRepExtChoice i (CSPCommAction ai aAi))
%       (CSPRepExtChoice j (CSPCommAction bj aBj))) c aC
%   = Done{orig = Just e, refined = Just (CSPNSParal ns1 cs ns2
%       (CSPRepExtChoice i (CSPCommAction ai aAi))
%       (CSPExtChoice (CSPRepExtChoice j
%           (CSPCommAction bj aBj))
%       (CSPCommAction c aC))),proviso=[]}
% prevar_crl_parallelismExternalChoiceExpansion _ _ _ = None
% \end{code}

\begin{code}
prevar_crl_parallelismExternalChoiceExpansionB :: CAction -> Refinement CAction
prevar_crl_parallelismExternalChoiceExpansionB
  e@(CSPNSParal ns1 cs ns2
      (CSPRepExtChoice i (CSPCommAction ai aAi))
      (CSPExtChoice (CSPRepExtChoice j
          (CSPCommAction bj aBj))
      (CSPCommAction c aC)))
  = Done{orig = Just e, refined = Just (CSPNSParal ns1 cs ns2
  (CSPRepExtChoice i (CSPCommAction ai aAi))
  (CSPRepExtChoice j (CSPCommAction bj aBj))),proviso=[]}
prevar_crl_parallelismExternalChoiceExpansionB _ = None
\end{code}



\begin{lawn}[Parallelism composition introduction 1$^*$]{3}\sl
    \begin{circus}
        c \then A
        \\ = \\
        (c \then A \lpar ns1 | \lchanset c \rchanset | ns2 \rpar c \then Skip)%
        \also
        c.e \then A
        \\ = \\
        (c.e \then A \lpar ns1 | \lchanset c \rchanset | ns2 \rpar c.e \then Skip)%
    \end{circus}%
    \begin{provs}
        \item $c \notin prevar_usedC(A)$
        \item $wrtV(A) \subseteq ns1$
    \end{provs}
  \label{law:parallelismIntroduction1}

\end{lawn}
\begin{code}
prevar_crl_parallelismIntroduction1b :: CAction -> [ZExpr] -> [ZName] -> [ZExpr] -> Refinement CAction
prevar_crl_parallelismIntroduction1b
  ei@(CSPCommAction (ChanComm c
      [ChanDotExp e]) a)
      ns1 cs ns2
  =  Done{orig = Just ei,
          refined = Just (CSPNSParal ns1 (CChanSet cs) ns2
                (CSPCommAction (ChanComm c [ChanDotExp e]) a)
                (CSPCommAction (ChanComm c [ChanDotExp e]) CSPSkip)),
          proviso=[p1,p2]}
    where
      p1 = (ZNot (ZMember (ZVar (c,[],[])) (ZTuple [ZSetDisplay (prevar_usedC a)])))
      p2 = (ZMember (ZTuple [ZSetDisplay (zname_to_zexpr $ wrtV a),ZSetDisplay  ns1]) (ZVar ("\\subseteq",[],[])))
prevar_crl_parallelismIntroduction1b _ _ _ _ = None

prevar_crl_parallelismIntroduction1a :: CAction -> [ZExpr] -> [ZName] -> [ZExpr] -> Refinement CAction
prevar_crl_parallelismIntroduction1a
    ei@(CSPCommAction (ChanComm c e) a)
        ns1 cs ns2
  =  Done{orig = Just ei, refined = Just (CSPNSParal ns1 (CChanSet cs) ns2
                  (CSPCommAction (ChanComm c e) a)
                  (CSPCommAction (ChanComm c e) CSPSkip)),proviso=[p1,p2]}
    where
      p1 = (ZNot (ZMember (ZVar (c,[],[]))  (ZTuple [ZSetDisplay (prevar_usedC a)])))
      p2 = (ZMember (ZTuple [ZSetDisplay (zname_to_zexpr $ wrtV a),ZSetDisplay ns1]) (ZVar ("\\subseteq",[],[])))
prevar_crl_parallelismIntroduction1a _ _ _ _ = None
\end{code}
% \begin{code}
% prevar_crl_parallelismIntroduction1b_backwards :: CAction -> Refinement CAction
% prevar_crl_parallelismIntroduction1b_backwards
%   e@(CSPNSParal ns1 (CChanSet cs) ns2
%                 (CSPCommAction (ChanComm c1 [ChanDotExp e1]) a)
%                 (CSPCommAction (ChanComm c2 [ChanDotExp e2]) CSPSkip))
%   = case (c1 == c2) && (e1 == e2) of
%       True -> Done{orig = Just e, refined = Just (CSPCommAction (ChanComm c1 [ChanDotExp e1]) a),
%                     proviso=[p1,p2]}
%       False -> None
%     where
%       p1 = (ZNot (ZMember (ZVar (c1,[])) (ZTuple [ZSetDisplay (prevar_usedC a)])))
%       p2 = (ZMember (ZTuple [ZSetDisplay (wrtV a),ZSetDisplay $ zname_to_zexpr ns1]) (ZVar ("\\subseteq",[],[])))
% prevar_crl_parallelismIntroduction1b_backwards _ = None

% prevar_crl_parallelismIntroduction1a_backwards :: CAction -> Refinement CAction
% prevar_crl_parallelismIntroduction1a_backwards
%     e@(CSPNSParal ns1 (CChanSet cs) ns2
%                   (CSPCommAction (ChanComm c1 []) a)
%                   (CSPCommAction (ChanComm c2 []) CSPSkip))
%   = case (c1 == c2) of
%       True -> Done{orig = Just e, refined = Just (CSPCommAction (ChanComm c1 []) a),
%                     proviso=[p1,p2]}
%       False -> None
%     where
%       p1 = (ZNot (ZMember (ZVar (c1,[])) (ZTuple [ZSetDisplay (prevar_usedC a)])))
%       p2 = (ZMember (ZTuple [ZSetDisplay (getWrtV a),ZSetDisplay $ zname_to_zexpr ns1]) (ZVar ("\\subseteq",[],[])))
% prevar_crl_parallelismIntroduction1a_backwards _ = None
% \end{code}


\begin{lawn}[Channel extension 1]{3}\sl\label{law:chanExt1}
    \begin{zed}
      A1 \lpar ns1 | cs | ns2 \rpar A2
      \\ = \\
      A1 \lpar ns1 | cs \cup \lchanset c \rchanset | ns2 \rpar A2%
    \end{zed}
    \begin{prov}
      $c \notin prevar_usedC(A1) \cup prevar_usedC(A2)$
    \end{prov}

\end{lawn}
\begin{code}
prevar_crl_chanExt1 :: CAction -> ZName -> Refinement CAction
prevar_crl_chanExt1 e@(CSPNSParal ns1 (CChanSet cs) ns2 a1 a2) c
  =  Done{orig = Just e, refined = Just (CSPNSParal ns1 (ChanSetUnion
                    (CChanSet cs) (CChanSet [c])) ns2 a1 a2),
                    proviso=[p1]}
    where
      p1 = (ZNot (ZMember (ZVar (c,[],[])) (ZCall (ZVar ("\\cup",[],[])) (ZTuple [ZSetDisplay (prevar_usedC a1),ZSetDisplay (prevar_usedC a2)]))))
prevar_crl_chanExt1 _ _ = None
\end{code}
% Law 13 (Hiding expansion 2$^*$)


\begin{lawn}[Hiding expansion 2$^*$]{3}\sl
    \begin{zed}
      A \circhide cs
      \\ = \\
      A \circhide (cs \cup \lchanset c \rchanset)
    \end{zed}
    \begin{prov} $c \notin prevar_usedC(A)$ \end{prov}
  \label{law:hidingExpansion2}

\end{lawn}
\begin{code}
prevar_crl_hidingExpansion2 :: CAction -> ZName -> Refinement CAction
prevar_crl_hidingExpansion2 e@(CSPHide a (CChanSet cs)) c
  = Done{orig = Just e, refined = Just (CSPHide a (ChanSetUnion (CChanSet cs) (CChanSet [c]))),
                    proviso=[p1]}
    where
      p1 = (ZNot (ZMember (ZVar (c,[],[])) (ZSetDisplay (prevar_usedC a))))
prevar_crl_hidingExpansion2 _ _ = None
\end{code}
% Law 14 (Prefix/Hiding$^*$)


\begin{lawn}[Prefix/Hiding$^*$]{3}\sl
    \begin{circus}
        (c \then Skip) \circhide \lchanset c \rchanset = \Skip%
        \also
        (c.e \then Skip) \circhide \lchanset c \rchanset = \Skip%
    \end{circus}%
 \label{law:prefixHiding}

\end{lawn}
\begin{code}
prevar_crl_prefixHiding :: CAction -> Refinement CAction
prevar_crl_prefixHiding
  e@(CSPHide (CSPCommAction (ChanComm c _) CSPSkip) (CChanSet [c1]))
  = case (c == c1) of
      True        -> Done{orig = Just e, refined = Just CSPSkip,proviso=[]}
      _   -> None
prevar_crl_prefixHiding _ = None
\end{code}
% Law 15 (Hiding Identity$^*$)


\begin{lawn}[Hiding Identity$^*$]{3}\sl

    \begin{circus}
      A \circhide cs = A
    \end{circus}
    \begin{prov} $cs \cap prevar_usedC(A) = \emptyset$ \end{prov}

  \label{law:hidingIdentity}

\end{lawn}
\begin{code}
prevar_crl_hidingIdentity :: CAction -> Refinement CAction
prevar_crl_hidingIdentity e@(CSPHide a (CChanSet cs))
  = Done{orig = Just e, refined = Just a, proviso=[p1]}
    where
      p1 = (ZEqual (ZCall (ZVar ("\\cap",[],[])) (ZTuple [ZSetDisplay $zname_to_zexpr cs,ZSetDisplay (prevar_usedC a)])) (ZVar ("\\emptyset",[],[])))
prevar_crl_hidingIdentity _ = None
\end{code}
% Law 16 (Parallelism composition/External choice---exchange)


\begin{lawn}[Parallelism composition/External choice---exchange]{3}\sl\label{law:parExtChoiceExchange}
    \begin{circus}
      (A1 \lpar ns1 | cs | ns2 \rpar A2) \extchoice (B1 \lpar ns1 | cs | ns2 \rpar B2)
      \\ = \\
      (A1 \extchoice B1) \lpar ns1 | cs | ns2\rpar (A2 \extchoice B2)
    \end{circus}
    \begin{prov} $A1 \lpar ns1 | cs | ns2 \rpar B2 = A2 \lpar ns1 | cs | ns2 \rpar B1 = Stop$
    \end{prov}

\end{lawn}
\begin{code}
prevar_crl_parExtChoiceExchange :: CAction -> Refinement CAction
prevar_crl_parExtChoiceExchange
    e@(CSPExtChoice
      (CSPNSParal ns1 cs ns2 a1 a2)
      (CSPNSParal ns11 cs1 ns21 b1 b2))
  = case pred1 of
      True ->  Done{orig = Just e, refined = Just ref, proviso=[]}
      False -> None
      where
        astop = (CSPNSParal ns1 cs ns2 a1 b2) == (CSPNSParal ns2 cs ns1 a2 b1)
        ref = (CSPNSParal ns1 cs ns2
                  (CSPExtChoice a1 b1)
                  (CSPExtChoice a2 b2))
        pred1 = (ns1 == ns11 && cs1 == cs && ns2 == ns21) && astop
prevar_crl_parExtChoiceExchange _ = None
\end{code}
% Law 17 (Parallelism composition/External choice---distribution$^*$)
%

\begin{lawn}[Parallelism composition/External choice---distribution$^*$]{3}\sl

  \begin{circus}
      \Extchoice i \circspot (A_i \lpar ns1 | cs | ns2 \rpar A)
      \\ = \\
      (\Extchoice i \circspot A_i) \lpar ns1 | cs | ns2 \rpar A
  \end{circus}%
  \begin{provs}
      \item $prevar_initials(A) \subseteq cs$ %
      \item $A$ is prevar_deterministic %
  \end{provs}
\label{law:parallelismExternalChoiceDistribution}

\end{lawn}
\begin{code}
isJustToZPred True = ZTrue{reason=[]}
isJustToZPred False = ZFalse{reason=[]}
prevar_crl_parallelismExternalChoiceDistribution :: CAction -> Refinement CAction
prevar_crl_parallelismExternalChoiceDistribution
    e@(CSPRepExtChoice i (CSPNSParal ns1 (CChanSet cs) ns2 ai a))
  = Done{orig = Just e,
        refined = Just (CSPNSParal ns1 (CChanSet cs) ns2 (CSPRepExtChoice i ai) a),
        proviso=[-- (ZEqual ZTrue{reason=[]} $ isJustToZPred (isJust (prevar_deterministic a))), -- yet to be implemented
                (ZMember (ZTuple [ZSetDisplay (prevar_initials a),ZSetDisplay $ zname_to_zexpr cs]) (ZVar ("\\subseteq",[],[])))]}
prevar_crl_parallelismExternalChoiceDistribution _ = None
\end{code}
% Law 18 (External choice unit)


\begin{lawn}[External choice unit]{3}\sl
    \begin{circus}
      Stop \extchoice A = A
    \end{circus}
  \label{law:extChoiceStopUnit}

\end{lawn}

\begin{code}
prevar_crl_extChoiceStopUnit :: CAction -> Refinement CAction
prevar_crl_extChoiceStopUnit e@(CSPExtChoice CSPStop a)
  = Done{orig = Just e, refined = Just a,proviso=[]}
prevar_crl_extChoiceStopUnit _
  = None

\end{code}
% Law 19 (External choice/Sequence---distribution)
%

\begin{lawn}[External choice/Sequence---distribution]{3}\
    \begin{circus}
      (\Extchoice\ i \circspot g_i \circguard c_i \then A_i)\circseq B
      \\ = \\
      \Extchoice\ i \circspot g_i \circguard c_i \then A_i\circseq B%
    \end{circus}
  \label{law:extChoiceSeqDist}
%
\end{lawn}
\begin{code}
prevar_crl_extChoiceSeqDist :: CAction -> Refinement CAction
prevar_crl_extChoiceSeqDist e@(CSPSeq (CSPRepExtChoice i
                        (CSPGuard gi (CSPCommAction ci ai))) b)
  =  Done{orig = Just e, refined = Just (CSPRepExtChoice i (CSPSeq
          (CSPGuard gi (CSPCommAction ci ai)) b)),proviso=[]}
prevar_crl_extChoiceSeqDist _ = None
\end{code}
% Law 20 (Hiding/External choice---distribution$^*$)


\begin{lawn}[Hiding/External choice---distribution$^*$]{3}\sl
    \begin{zed}
      (A1 \extchoice A2) \circhide cs
      \\ = \\
      (A1 \circhide cs) \extchoice (A2 \circhide cs)
    \end{zed}
    \begin{prov}
      $(prevar_initials(A1) \cup prevar_initials(A2)) \cap cs = \emptyset$
    \end{prov}
  \label{law:hidingExternalChoiceDistribution}

\end{lawn}
\begin{code}
prevar_crl_hidingExternalChoiceDistribution :: CAction -> Refinement CAction
prevar_crl_hidingExternalChoiceDistribution
    e@(CSPHide (CSPExtChoice a1 a2) (CChanSet cs))
  = Done{orig = Just e, refined = Just ref, proviso=[p1]}
    where
      p1 = (ZEqual (ZCall (ZVar ("\\cap",[],[])) (ZTuple [ZCall (ZVar ("\\cup",[],[])) (ZTuple [ZSetDisplay (prevar_initials a1),ZSetDisplay (prevar_initials a1)]),ZSetDisplay (zname_to_zexpr cs)])) (ZVar ("\\emptyset",[],[])))
      ref = (CSPExtChoice
              (CSPHide a1 (CChanSet cs))
              (CSPHide a2 (CChanSet cs)))


prevar_crl_hidingExternalChoiceDistribution _ = None
\end{code}
% Law 21 (Hiding/External choice---distribution$^*$)


\begin{lawn}[Parallelism composition Deadlocked 1$^*$]{3}\sl

    \begin{circus}
        (c1 \then A1) \lpar ns1 | cs | ns2 \rpar (c2 \then A2)
        \\ = \\
        \Stop %
        \\ = \\
        \Stop \lpar ns1 | cs | ns2 \rpar (c2 \then A2)
    \end{circus}%
    \begin{provs}
        \item $c1 \neq c2$
        \item $\{c1,c2\} \subseteq cs$
    \end{provs}
  \label{law:parallelismDeadlocked1}

\end{lawn}
\begin{code}
prevar_crl_parallelismDeadlocked1 :: CAction -> Refinement CAction
prevar_crl_parallelismDeadlocked1
    e@(CSPNSParal ns1 (CChanSet cs) ns2
          (CSPCommAction (ChanComm c1 _) _)
          (CSPCommAction (ChanComm c2 y) a2))
  =  Done{orig = Just e, refined = Just ref, proviso=[p1,p2]}
    where
      p1 = ZNot (ZEqual (ZVar (c1,[],[])) (ZVar (c2,[],[])))
      p2 = (ZMember (ZTuple [ZSetDisplay [ZVar (c1,[],[]),ZVar (c2,[],[])],ZSetDisplay $ zname_to_zexpr cs]) (ZVar ("\\subseteq",[],[])))
      ref = (CSPNSParal ns1 (CChanSet cs) ns2
              CSPStop
              (CSPCommAction (ChanComm c2 y) a2))
prevar_crl_parallelismDeadlocked1 e@(CSPNSParal _ _ _
                              CSPStop (CSPCommAction _ _))
  = Done{orig = Just e, refined = Just ref, proviso=[]}
    where
      ref = CSPStop
prevar_crl_parallelismDeadlocked1 _ = None

\end{code}
% Law 22 (Sequence zero)


\begin{lawn}[Sequence zero]{3}\sl
    \begin{circus}
      \Stop \circseq A = \Stop
    \end{circus}
  \label{law:seqStopZero}

\end{lawn}
\begin{code}
prevar_crl_seqStopZero :: CAction -> Refinement CAction
prevar_crl_seqStopZero e@(CSPSeq CSPStop _)
  =  Done{orig = Just e, refined = Just CSPStop,proviso=[]}
prevar_crl_seqStopZero _ = None
\end{code}
% Law 23 (Communication/Parallelism composition---distribution)


\begin{lawn}[Communication/Parallelism composition---distribution]{3}\sl
    \begin{circus}
      (c!e \then A1) \lpar ns1 | cs | ns2 \rpar (c?x \then A2(x))
      \\ = \\
      c.e \then (A1 \lpar ns1 | cs | ns2 \rpar A2(e)) %
    \end{circus}
    \begin{provs}
        \item $c \in cs$
        \item $x \notin FV(A2)$.
    \end{provs}


  \label{law:communicationParallelismDistribution}

\end{lawn}
\begin{code}
prevar_crl_communicationParallelismDistribution :: CAction -> Refinement CAction
prevar_crl_communicationParallelismDistribution
    ei@(CSPNSParal ns1 (CChanSet cs) ns2
        (CSPCommAction (ChanComm c [ChanOutExp e]) a1)
        (CSPCommAction (ChanComm c1 [ChanInp x1])
          (CSPParAction a2 [ZVar (x,[],tx1)])))
  = case pred1 of
      True  -> Done{orig = Just ei, refined = Just ref, proviso=[p1,p2]}
      False -> None
    where
       p1 = (ZNot (ZMember (ZVar (c,[],[])) (ZSetDisplay $ zname_to_zexpr cs)))
       p2 = (ZNot (ZMember (ZVar (x,[],tx1)) (ZSetDisplay $ zvar_to_zexpr $ varset_to_zvars(free_var_CAction (CSPParAction a2 [ZVar (x,[],tx1)])))))
       ref = (CSPCommAction (ChanComm c [ChanDotExp e])
                    (CSPNSParal ns1 (CChanSet cs) ns2 a1 (CSPParAction a2 [e])))
       pred1 = (c == c1 && x == x1)
prevar_crl_communicationParallelismDistribution _ = None
\end{code}
% Law 24 (Channel extension 3$^*$)


\begin{lawn}[Channel extension 3$^*$]{3}\sl
    \begin{circus}
      (A1 \lpar ns1 | cs1 | ns2 \rpar A2(e)) \circhide cs2
      \\ = \\
      ((c!e \then A1) \lpar ns1 | cs1 | ns2 \rpar (c?x \then A2(x))) \circhide cs2 %
    \end{circus}%
    \begin{provs}
        \item $c \in cs1$
        \item $c \in cs2$
        \item $x \notin FV(A2)$
    \end{provs}
  \label{law:channelExtension3}


\end{lawn}
\begin{code}
prevar_crl_channelExtension3 :: CAction
                               -> ZName -> ZName -> Refinement CAction
prevar_crl_channelExtension3 ei@(CSPHide
          (CSPNSParal ns1 (CChanSet cs1) ns2 a1 (CActionCommand (CVarDecl [Choose (e,[],tx1) t1] mact))) (CChanSet cs2)) c x
  =  Done{orig = Just ei, refined = Just ref, proviso=[p1,p2,p3]}
    where
      p1 = (ZNot (ZMember (ZVar (c,[],[])) (ZSetDisplay $ zname_to_zexpr cs1)))
      p2 = (ZNot (ZMember (ZVar (c,[],[])) (ZSetDisplay $ zname_to_zexpr cs2)))
      p3 = (ZNot (ZMember (ZVar (x,[],[])) (ZSetDisplay $ zvar_to_zexpr $ varset_to_zvars(free_var_CAction (CActionCommand (CVarDecl [Choose (e,[],tx1) t1] mact))))))
      ref = (CSPHide
                (CSPNSParal ns1 (CChanSet cs1) ns2
                    (CSPCommAction (ChanComm c [ChanOutExp (ZVar (e,[],tx1))]) a1)
                    (CSPCommAction (ChanComm c [ChanInp x])
                        (CActionCommand (CVarDecl [Choose (x,[],"") t1] mact))))
                (CChanSet cs2))
prevar_crl_channelExtension3 _ _ _= None
\end{code}
\begin{code}
prevar_crl_channelExtension3_backwards :: CAction -> Refinement CAction
prevar_crl_channelExtension3_backwards ei@(CSPHide (CSPNSParal ns1 (CChanSet cs1) ns2 (CSPCommAction (ChanComm c2 [ChanOutExp (e)]) a1) (CSPCommAction (ChanComm c1 [ChanInp x]) (CSPParAction a2 [ZVar (x1,[],_)]))) (CChanSet cs2))
  = case pred1 of
      True -> Done{orig = Just ei, refined = Just ref, proviso=[p1,p2,p3]}
      False -> None
    where
       p1 = (ZNot (ZMember (ZVar (c1,[],[])) (ZSetDisplay $ zname_to_zexpr cs1)))
       p2 = (ZNot (ZMember (ZVar (c2,[],[])) (ZSetDisplay $ zname_to_zexpr cs2)))
       p3 = (ZNot (ZMember (ZVar (x,[],[])) (ZSetDisplay $ zvar_to_zexpr $ varset_to_zvars(free_var_CAction (CSPParAction a2 [e])))))
       pred1 = (c1 == c2) && (x == x1)
       ref = (CSPHide (CSPNSParal ns1 (CChanSet cs1) ns2 a1 (CSPParAction a2 [e])) (CChanSet cs2))
prevar_crl_channelExtension3_backwards _ = None
\end{code}
% Law 25 (Channel extension 4$^*$)


\begin{lawn}[Channel extension 4$^*$]{3}\sl
    \begin{circus}
      (A1 \lpar ns1 | cs1 | ns2 \rpar A2) \circhide cs2
      \\ = \\
      ((c \then A1) \lpar ns1 | cs1 | ns2 \rpar (c \then A2)) \circhide cs2%
      \also
      (A1 \lpar ns1 | cs1 | ns2 \rpar A2) \circhide cs2
      \\ = \\
      ((c.e \then A1) \lpar ns1 | cs1 | ns2 \rpar (c.e \then A2)) \circhide cs2%
    \end{circus}%
    \begin{provs}
        \item $c \in cs1$%
        \item $c \in cs2$%
    \end{provs}
  \label{law:channelExtension4}

\end{lawn}
\begin{code}
prevar_crl_channelExtension4 :: CAction -> Comm -> Refinement CAction
prevar_crl_channelExtension4 ei@(CSPHide (CSPNSParal ns1 (CChanSet cs1) ns2 a1 a2) (CChanSet cs2)) (ChanComm c [ChanOutExp (e)])
  =  Done{orig = Just ei, refined = Just ref, proviso=[p1,p2]}
    where
       p1 = (ZNot (ZMember (ZVar (c,[],[])) (ZSetDisplay $ zname_to_zexpr cs1)))
       p2 = (ZNot (ZMember (ZVar (c,[],[])) (ZSetDisplay $ zname_to_zexpr cs2)))
       ref = (CSPHide (CSPNSParal ns1 (CChanSet cs1) ns2 (CSPCommAction (ChanComm c [ChanOutExp (e)]) a1) (CSPCommAction (ChanComm c [ChanOutExp (e)]) a2)) (CChanSet cs2))
prevar_crl_channelExtension4 ei@(CSPHide (CSPNSParal ns1 (CChanSet cs1) ns2 a1 a2)
                                (CChanSet cs2)) (ChanComm c e)
  = Done{orig = Just ei, refined = Just ref, proviso=[p1,p2]}
    where
      p1 = (ZNot (ZMember (ZVar (c,[],[])) (ZSetDisplay $ zname_to_zexpr cs1)))
      p2 = (ZNot (ZMember (ZVar (c,[],[])) (ZSetDisplay $ zname_to_zexpr cs2)))
      ref = (CSPHide (CSPNSParal ns1 (CChanSet cs1) ns2
                          (CSPCommAction (ChanComm c e) a1)
                           (CSPCommAction (ChanComm c e) a2))
                        (CChanSet cs2))
prevar_crl_channelExtension4 _ _ = None
\end{code}

\begin{lawn}[prom-var-state]{3}
\begin{circus}
\circbegin
\\\qquad (\circstate S)
\\\qquad L(x : T)
\\\qquad \circspot (\circvar x : T \circspot MA)
\\\circend
\\=\\
\circbegin
\\\qquad (\circstate S \land [ x : T ])
\\\qquad L(\_)
\\\quad \circspot MA
\\\circend
\end{circus}

\label{law:promVarState}

\end{lawn}
\begin{code}
prevar_crl_promVarState :: CProc -> Refinement CProc
prevar_crl_promVarState
  e@(ProcMain
      (ZSchemaDef (ZSPlain st []) s)
      [CParAction l (CircusAction (CActionCommand (CValDecl [Choose (x,[],tx1) (ZVar (t,[],tx2))] a)))]
      (CActionCommand (CValDecl [Choose (x1,[],_) (ZVar (t1,[],_))] ma)))
  = case (x==x1 && t == t1) of
        True -> Done{orig = Just e, refined = Just ref, proviso=[]}
        False -> None
    where
      ref = (ProcMain
                  (ZSchemaDef (ZSPlain st []) (ZS2 ZSAnd s (ZSchema [Choose (x,[],tx1) (ZVar (t,[],tx2))])))
                  [CParAction l (CircusAction a)] ma)

prevar_crl_promVarState _ = None
\end{code}

\begin{lawn}[prom-var-state-2]{3}
\begin{circus}
\\\quad \begin{array}{l}
          \circbegin
          \\ L(x : T)
          \\ \circspot (\circvar x : T \circspot MA)
          \\\circend
        \end{array}
\\=
\\\quad \begin{array}{l}
        \circbegin\\
        (\circstate [ x : T ]) \\
        L(\_)\\
        \circspot MA\\
         \circend
        \end{array}

\end{circus}
\label{law:promVarState2}

\end{lawn}

\begin{code}
prevar_crl_promVarState2 :: CProc -> ZSName -> Refinement CProc
prevar_crl_promVarState2
    e@(ProcStalessMain
      [CParAction lact (ParamActionDecl [(Choose v t)] act)]
      (CActionCommand (CVarDecl [Choose v1 t1] mact))) st
  = case (v==v1 && t == t1) of
      True -> Done{orig = Just e, refined = Just ref, proviso=[]}
      False -> None
      where
        ref = (ProcMain (ZSchemaDef st (ZSchema [Choose v1 t1]))
                [CParAction lact act] mact)
prevar_crl_promVarState2
    e@(ProcStalessMain
      [CParAction lact (ParamActionDecl ((Choose v t):xs) act)]
      (CActionCommand (CVarDecl ((Choose v1 t1):ys) mact))) st
  = case (v==v1 && t == t1) of
      True -> Done{orig = Just e, refined = Just ref, proviso=[]}
      False -> None
      where
        ref = (ProcMain (ZSchemaDef st (ZSchema [Choose v1 t1]))
                [CParAction lact (ParamActionDecl xs act)]
                (CActionCommand (CVarDecl ys mact)))
prevar_crl_promVarState2 _ _ = None
\end{code}


\begin{lawn}[Parallelism composition unit$^*$]{3}\sl
    \begin{circus}
        \Skip \lpar ns1 | cs | ns2 \rpar \Skip = \Skip
    \end{circus}%
  \label{law:parallelismUnit1}

\end{lawn}
\begin{code}
prevar_crl_parallelismUnit1 :: CAction -> Refinement CAction
prevar_crl_parallelismUnit1 e@(CSPNSParal _ _ _ CSPSkip CSPSkip)
  =  Done{orig = Just e, refined = Just CSPSkip, proviso=[]}
prevar_crl_parallelismUnit1 _ = None
\end{code}



\begin{lawn}[Parallelism composition/Interleaving Equivalence$^*$]{3}\sl
    \begin{circus}
      A1 \linter ns2 | ns2 \rinter A2
      \\ = \\
      A1 \lpar ns2 | \emptyset | ns2 \rpar A2%
    \end{circus}%
  \label{law:parallelism-interleaving-equivalence}

\end{lawn}

\begin{code}
prevar_crl_parallInterlEquiv :: CAction -> Refinement CAction
prevar_crl_parallInterlEquiv e@(CSPNSInter ns1 ns2 a1 a2)
  =  Done{orig = Just e, refined = Just ref, proviso=[]}
    where
      ref = (CSPNSParal ns1 CSEmpty ns2 a1 a2)
prevar_crl_parallInterlEquiv _ = None
-- prevar_crl_parallInterlEquiv_backwards :: CAction -> Refinement CAction
-- prevar_crl_parallInterlEquiv_backwards e@(CSPNSParal ns1 CSEmpty ns2 a1 a2)
--   = Done{orig = Just e, refined = Just ref, proviso=[]}
--     where
--       ref = (CSPNSInter ns1 ns2 a1 a2)
-- prevar_crl_parallInterlEquiv_backwards _ = None
\end{code}
%

\begin{lawn}[Parallelism composition/Sequence---step$^*$]{3}\sl
\label{law:parSeqStep}
  \begin{circus}
    (A1\circseq A2) \lpar ns1 | cs | ns_ 2 \rpar A3
    \\ = \\
    A1\circseq (A2 \lpar ns_ 1 | cs | ns2 \rpar A3)%
  \end{circus}
    \begin{provs}
      \item $prevar_initials(A3) \subseteq cs$
      \item $cs \cap prevar_usedC(A1) = \emptyset$
      \item $wrtV(A1) \cap prevar_usedV(A3) = \emptyset$
        \item $A3$ is divergence-free
      \item $wrtV(A1) \subseteq ns1$
    \end{provs}

\end{lawn}


\begin{code}
prevar_crl_parSeqStep :: CAction -> Refinement CAction
prevar_crl_parSeqStep e@(CSPNSParal ns1 (CChanSet cs) ns2 (CSPSeq a1 a2) a3)
    =  Done{orig = Just e, refined = Just ref, proviso=[]}
    where
      ref =  (CSPSeq a1 (CSPNSParal ns1 (CChanSet cs) ns2 a2 a3))
      p1 = (subset (prevar_initials a3) (zname_to_zexpr cs))
      p2 = null $ (zname_to_zexpr cs) `intersect` (prevar_usedC a1)
      p3 = null $ (zname_to_zexpr $ wrtV a1) `intersect` (zname_to_zexpr $ wrtV a3)
      p4 = True -- a3 is divergence-free -- implement that!!
      p5 = (subset (zname_to_zexpr $ wrtV a1) (zname_to_zexpr cs))
      pred1 = p1 && p2 && p3 && p4 && p5
prevar_crl_parSeqStep _ = None
\end{code}



\begin{lawn}[Hiding/Sequence---distribution$^*$]{3}\sl
    \begin{circus}
      (A1 \circseq\ A2) \circhide cs
      \\ = \\
      (A1 \circhide cs) \circseq\ (A2 \circhide cs)
    \end{circus}
  \label{law:hidingSequenceDistribution}

\end{lawn}

\begin{code}
prevar_crl_hidingSequenceDistribution :: CAction -> Refinement CAction
prevar_crl_hidingSequenceDistribution e@(CSPHide (CSPSeq a1 a2) cs)
    = Done{orig = Just e, refined = Just ref, proviso=[]}
    where
      ref = (CSPSeq (CSPHide a1 cs) (CSPHide a2 cs))
prevar_crl_hidingSequenceDistribution _ = None
\end{code}



\begin{lawn}[Guard/Sequence---associativity]{3}\sl
    \begin{circus}
      (g \circguard A1)\circseq A2
      \\ = \\
      g \circguard (A1\circseq A2)
    \end{circus}
  \label{law:guardSeqAssoc}

\end{lawn}

\begin{code}
prevar_crl_guardSeqAssoc :: CAction -> Refinement CAction
prevar_crl_guardSeqAssoc e@(CSPSeq (CSPGuard g a1) a2)
  = Done{orig = Just e, refined = Just ref, proviso=[]}
    where ref = (CSPGuard g (CSPSeq a1 a2))
prevar_crl_guardSeqAssoc _ = None
\end{code}



\begin{lawn}[Input prefix/Parallelism composition---distribution 2$^*$]{3}\sl
    \begin{circus}
        c?x \then (A1 \lpar ns1 | cs | ns2 \rpar A2) %
        \\ = \\
        (c?x \then A1) \lpar ns1 | cs | ns2 \rpar A2%
    \end{circus}%
    \begin{provs}
        \item $c \notin cs$%
        \item $x \notin prevar_usedV(A2)$
        \item $prevar_initials(A2) \subseteq cs$
        \item $A2$ is prevar_deterministic
    \end{provs}
  \label{law:inputPrefixParallelismDistribution2}

\end{lawn}


\begin{code}
prevar_crl_inputPrefixParallelismDistribution2 :: CAction -> Refinement CAction
prevar_crl_inputPrefixParallelismDistribution2
      e@(CSPCommAction (ChanComm c [ChanInp x])
          (CSPNSParal ns1 (CChanSet cs) ns2 a1 a2))
  = Done{orig = Just e, refined = Just ref, proviso=[p1,p2,p3]}
    where
      ref = (CSPNSParal ns1 (CChanSet cs) ns2 (CSPCommAction (ChanComm c [ChanInp x]) a1) a2)
      p1 = (ZNot (ZMember (ZVar (c,[],[])) (ZSetDisplay $ zname_to_zexpr cs)))
      p2 = (ZNot (ZMember (ZVar (c,[],[])) (ZSetDisplay $ zname_to_zexpr(prevar_usedV a2))))
      p3 = (ZMember (ZTuple [ZSetDisplay (prevar_initials a2),ZSetDisplay (zname_to_zexpr cs)]) (ZVar ("\\subseteq",[],[])))
prevar_crl_inputPrefixParallelismDistribution2 _ = None
\end{code}
% Law 34 (Prefix/$Skip$$^*$)


\begin{lawn}[Prefix/$Skip$$^*$]{3}\sl
    \begin{circus}
        c \then A = (c \then \Skip) \circseq\ A
        \also
        c.e \then A = (c.e \then \Skip) \circseq\ A
    \end{circus}%

  \label{law:prefixSkip}

\end{lawn}
\begin{code}

-- prevar_crl_prefixSkip :: CAction -> Refinement CAction
-- prevar_crl_prefixSkip e@(CSPCommAction (ChanComm c [ChanDotExp x]) a)
--   = Done{orig = Just e, refined = Just ref, proviso=[]}
--     where
--       ref = (CSPSeq (CSPCommAction
--               (ChanComm c [ChanDotExp x]) CSPSkip) a)
-- prevar_crl_prefixSkip e@(CSPCommAction c a)
--   = Done{orig = Just e, refined = Just ref, proviso=[]}
--     where
--       ref = (CSPSeq (CSPCommAction c CSPSkip) a)
-- prevar_crl_prefixSkip _ = None

-- 9/04/17
-- I had to make these two auxiliary functions in order to
-- put the prevar_crl_prefixSkip_backwards function working properly.
-- Basically, it searches for a CSPSkip within a prefixed action
-- and then removes the CSPSkip replacing it with a2, the RHS of
-- a CSPSeq action.
endPrefWithSkip :: CAction -> Bool
endPrefWithSkip (CSPCommAction _ CSPSkip) = True
endPrefWithSkip (CSPCommAction _ c1) = endPrefWithSkip c1
endPrefWithSkip _ = False

remPrefSkip :: CAction -> CAction -> CAction
remPrefSkip a2 (CSPCommAction c CSPSkip) = (CSPCommAction c a2)
remPrefSkip a2 (CSPCommAction c c1) = (CSPCommAction c (remPrefSkip a2 c1))
remPrefSkip _ _ = error "Unable to get the remPrefSkip"
-- remPrefSkip a2 a1 = (CSPSeq a1 a2)

prevar_crl_prefixSkip_backwards :: CAction -> Refinement CAction
prevar_crl_prefixSkip_backwards e@(CSPSeq (CSPCommAction c a1) a)
  | endPrefWithSkip a1
    = Done{orig = Just e, refined = Just ref, proviso=[]}
      where
        ref = remPrefSkip a (CSPCommAction c a1)
prevar_crl_prefixSkip_backwards _ = None


prevar_crl_prefixSeq_backwards :: CAction -> Refinement CAction
prevar_crl_prefixSeq_backwards e@(CSPSeq (CSPCommAction c a1) a2)
  = Done{orig = Just e, refined = Just ref, proviso=[]}
      where
        ref =  (CSPCommAction c (CSPSeq a1 a2))
prevar_crl_prefixSeq_backwards _ = None
\end{code}


\begin{lawn}[Prefix/Parallelism composition---distribution]{3}\sl
    \begin{circus}
      c \then (A1 \lpar ns1 | cs | ns2 \rpar A2)
      \\ = \\
      (c \then A1) \lpar ns1 | cs \cup \lchanset c \rchanset | ns2 \rpar (c \then A2)%
      \also
      c.e \then (A1 \lpar ns1 | cs | ns2 \rpar A2)
      \\ = \\
      (c.e \then A1) \lpar ns1 | cs \cup \lchanset c \rchanset | ns2 \rpar (c.e \then A2)%
    \end{circus}
    \begin{prov} $c \notin prevar_usedC(A1) \cup prevar_usedC(A2)$ or $c \in cs$
    \end{prov}
  \label{law:prefixParDist}

\end{lawn}
\begin{code}
prevar_crl_prefixParDist :: CAction -> Refinement CAction
prevar_crl_prefixParDist e@(CSPCommAction (ChanComm c [])
                    (CSPNSParal ns1 (CChanSet cs) ns2 a1 a2))
  = Done{orig = Just e, refined = Just ref, proviso=[ZAnd p1 p2]}
    where
      ref = (CSPNSParal
                    ns1 (ChanSetUnion (CChanSet cs) (CChanSet [c])) ns2
                    (CSPCommAction (ChanComm c []) a1)
                    (CSPCommAction (ChanComm c []) a2))
      p1 = (ZNot (ZMember (ZVar (c,[],[])) (ZCall (ZVar ("\\cup",[],[])) (ZTuple [ZSetDisplay $ zvar_to_zexpr $ varset_to_zvars(free_var_CAction a1),ZSetDisplay $ zvar_to_zexpr $ varset_to_zvars (free_var_CAction a2)]))))
      p2 = (ZMember (ZVar (c,[],[])) (ZSetDisplay $ zname_to_zexpr cs))
prevar_crl_prefixParDist ei@(CSPCommAction (ChanComm c [ChanDotExp e])
                    (CSPNSParal ns1 (CChanSet cs) ns2 a1 a2))
 = Done{orig = Just ei, refined = Just ref, proviso=[ZAnd p1 p2]}
    where
      ref = (CSPNSParal ns1 (ChanSetUnion (CChanSet cs) (CChanSet [c])) ns2
                    (CSPCommAction (ChanComm c [ChanDotExp e]) a1)
                    (CSPCommAction (ChanComm c [ChanDotExp e]) a2))
      p1 = (ZNot (ZMember (ZVar (c,[],[])) (ZCall (ZVar ("\\cup",[],[])) (ZTuple [ZSetDisplay $ zvar_to_zexpr $ varset_to_zvars(free_var_CAction a1),ZSetDisplay $ zvar_to_zexpr $ varset_to_zvars(free_var_CAction a2)]))))
      p2 = (ZMember (ZVar (c,[],[])) (ZSetDisplay $ zname_to_zexpr cs))
prevar_crl_prefixParDist _ = None
\end{code}
% Law 36 (External choice/Sequence---distribution 2$^*$)


\begin{lawn}[External choice/Sequence---distribution 2$^*$]{3}\sl
    \begin{circus}
      ((g1 \circguard A1) \extchoice (g2 \circguard A2))\circseq B
      \\ = \\
      ((g1 \circguard A1) \circseq B) \extchoice ((g2 \circguard A2) \circseq B)%
    \end{circus}
    \begin{prov} $g1 \implies \lnot g2$ \end{prov}
  \label{law:externalChoiceSequenceDistribution2}

\end{lawn}

\begin{code}
prevar_crl_externalChoiceSequenceDistribution2 :: CAction -> Refinement CAction
prevar_crl_externalChoiceSequenceDistribution2
      e@(CSPSeq (CSPExtChoice (CSPGuard g1 a1) (CSPGuard g2 a2)) b)
  = Done{orig = Just e, refined = Just ref, proviso=[]}
    where
      ref = (CSPExtChoice (CSPSeq (CSPGuard g1 a1) b)
                  (CSPSeq (CSPGuard g2 a2) b))
prevar_crl_externalChoiceSequenceDistribution2 _ = None
\end{code}
% Law 37 (True guard)


\begin{lawn}[True guard]{3}\sl
    \begin{circus}
      \true \circguard A = A
    \end{circus}
  \label{law:trueGuard}

\end{lawn}
\begin{code}
prevar_crl_trueGuard :: CAction -> Refinement CAction
prevar_crl_trueGuard e@(CSPGuard ZTrue{reason=[]} a)
  = Done{orig = Just e, refined = Just ref, proviso=[]}
    where
      ref = a
prevar_crl_trueGuard _ = None
\end{code}
% Law 38 (False guard)


\begin{lawn}[False guard]{3}\sl
    \begin{circus}
      \false \circguard A = \Stop
    \end{circus}
  \label{law:falseGuard}

\end{lawn}
\begin{code}
prevar_crl_falseGuard :: CAction -> Refinement CAction
prevar_crl_falseGuard e@(CSPGuard ZFalse{reason=[]} _)
  = Done{orig = Just e, refined = Just ref, proviso=[]}
    where
      ref = CSPStop
prevar_crl_falseGuard _ = None
\end{code}
% Law 39 (Hiding/$Chaos$---distribution$^*$)


\begin{lawn}[Hiding/$Chaos$---distribution$^*$]{3}\sl
    \begin{circus}
      \Chaos \circhide cs = \Chaos
    \end{circus}
  \label{law:hidingChaos}

\end{lawn}
\begin{code}
prevar_crl_hidingChaos :: CAction -> Refinement CAction
prevar_crl_hidingChaos e@(CSPHide CSPChaos _)
  = Done{orig = Just e, refined = Just ref, proviso=[]}
    where
      ref = CSPChaos
prevar_crl_hidingChaos _ = None
\end{code}

\begin{lawn}[Sequence zero 2$^*$]{3}\sl
    \begin{circus}
      \Chaos \circseq A = \Chaos
    \end{circus}
  \label{law:seqChaosZero}

\end{lawn}
\begin{code}
prevar_crl_seqChaosZero :: CAction -> Refinement CAction
prevar_crl_seqChaosZero e@(CSPSeq CSPChaos _)
  = Done{orig = Just e, refined = Just ref, proviso=[]}
    where
      ref = CSPChaos
prevar_crl_seqChaosZero _ = None
\end{code}

\begin{lawn}[Parallelism composition Zero$^*$]{3}\sl
    \begin{circus}
        Chaos \lpar ns1 | cs | ns2 \rpar A = Chaos%
    \end{circus}%
  \label{law:parallelismZero}

\end{lawn}
\begin{code}
prevar_crl_parallelismZero :: CAction -> Refinement CAction
prevar_crl_parallelismZero e@(CSPNSParal _ _ _ CSPChaos _)
  = Done{orig = Just e, refined = Just ref, proviso=[]}
    where
      ref = CSPChaos
prevar_crl_parallelismZero _ = None
\end{code}
% Law 42 (Internal choice/Parallelism composition Distribution$^*$)


\begin{lawn}[Internal choice/Parallelism composition Distribution$^*$]{3}\sl
    \begin{circus}
      (A1 \intchoice A2) \lpar ns1 | cs | ns2 \rpar A3
      \\ = \\
      (A1 \lpar ns1 | cs | ns2 \rpar A3) \intchoice (A2 \lpar ns1 | cs | ns2 \rpar A3) \\ %
    \end{circus}%
  \label{law:internalChoiceParallelismDistribution}

\end{lawn}
\begin{code}
prevar_crl_internalChoiceParallelismDistribution :: CAction -> Refinement CAction
prevar_crl_internalChoiceParallelismDistribution e@(CSPNSParal ns1 cs ns2 (CSPIntChoice a1 a2) a3)
  = Done{orig = Just e, refined = Just ref, proviso=[]}
    where
      ref = (CSPIntChoice (CSPNSParal ns1 cs ns2 a1 a3) (CSPNSParal ns1 cs ns2 a2 a3))
prevar_crl_internalChoiceParallelismDistribution _ = None
\end{code}


\begin{lawn}[Sequence/Internal choice---distribution$^*$]{3}\sl
    \begin{circus}
        A_1 \Semi\ (A_2 \intchoice A_3) = (A_1 \Semi\ A_2) \intchoice (A_1 \Semi\ A_3)%
    \end{circus}%
  \label{law:sequenceInternalChoiceDistribution}

\end{lawn}
\begin{code}
--Law 43 (Sequence/Internal choice—distribution)
prevar_crl_sequenceInternalChoiceDistribution :: CAction -> Refinement CAction
prevar_crl_sequenceInternalChoiceDistribution e@(CSPSeq a1 (CSPIntChoice a2 a3))
  = Done{orig = Just e, refined = Just ref, proviso=[]}
    where
      ref = (CSPIntChoice (CSPSeq a1 a2) (CSPSeq a1 a3))
prevar_crl_sequenceInternalChoiceDistribution _ = None
\end{code}
% Law 44 (Sequence/Internal choice---distribution$^*$)


\begin{lawn}[Hiding/Parallelism composition---distribution$^*$]{3}\sl
    \begin{zed}
      (A_1 \lpar ns_1 | cs_1 | ns_2 \rpar A_2) \hide cs_2 = (A_1 \hide cs_2) \lpar ns_1 | cs_1 | ns_2 \rpar (A_2 \hide cs_2)
    \end{zed}
    \begin{prov}
        $cs_1 \cap cs_2 = \emptyset$
    \end{prov}
  \label{law:hidingParallelismDistribution}

\end{lawn}
\begin{code}
prevar_crl_hidingParallelismDistribution :: CAction -> Refinement CAction
prevar_crl_hidingParallelismDistribution
    e@(CSPHide (CSPNSParal ns1 (CChanSet cs1) ns2 a1 a2) (CChanSet cs2))
  = Done{orig = Just e, refined = Just ref, proviso=[prov]}
    where
      ref = (CSPNSParal ns1 (CChanSet cs1) ns2 (CSPHide a1 (CChanSet cs1)) (CSPHide a2 (CChanSet cs2)))
      prov = (ZEqual (ZCall (ZVar ("\\cap",[],[])) (ZTuple [ZSetDisplay $ zname_to_zexpr cs1,ZSetDisplay $ zname_to_zexpr cs2])) (ZVar ("\\emptyset",[],[])))
prevar_crl_hidingParallelismDistribution _ = None
\end{code}
% Law 45 (Hiding combination)


\begin{lawn}[Hiding combination]{3}\sl
    \begin{circus}
      (A \circhide cs1) \circhide cs2
      \\ = \\
      A \circhide (cs1 \cup cs2)
   \end{circus}
  \label{law:hidingCombination}

\end{lawn}
\begin{code}
prevar_crl_hidingCombination :: CAction -> Refinement CAction
prevar_crl_hidingCombination e@(CSPHide (CSPHide a cs1) cs2)
  = Done{orig = Just e, refined = Just ref, proviso=[]}
    where
      ref = (CSPHide a (ChanSetUnion cs1 cs2))
prevar_crl_hidingCombination _ = None
\end{code}
% Law 46 (Parallelism composition Deadlocked 3$^*$)
%

\begin{lawn}[Parallelism composition Deadlocked 3$^*$]{3}\sl
    \begin{circus}
        (\Extchoice_i c_i \then A_i) \lpar ns1 | cs | ns2 \rpar (\Extchoice_j c_j \then A_j)
        = Stop %
        = Stop \lpar ns1 | cs | ns2 \rpar (\Extchoice_j c_j \then A_j)
    \end{circus}%
    \begin{provs}
        \item $\bigcup_i\{c_i\} \cap \bigcup_i\{c_i\} = \emptyset$
        \item $\bigcup_i\{c_i\} \cap \bigcup_i\{c_i\} \subseteq cs$
    \end{provs}
  \label{law:parallelismDeadlocked3}

\end{lawn}

% QUESTION: can we interpret $c_i --> A_i$ the same of $c.i --> A(i)$

\begin{code}
prevar_crl_parallelismDeadlocked3 :: CAction -> Refinement CAction
prevar_crl_parallelismDeadlocked3
  e@(CSPNSParal ns1 (CChanSet cs) ns2
      (CSPRepExtChoice _ (CSPCommAction ci _))
      (CSPRepExtChoice j (CSPCommAction cj aj)))
  = Done{orig = Just e, refined = Just ref, proviso=[]}
  where
      ref = (CSPNSParal ns1 (CChanSet cs) ns2 CSPStop (CSPRepExtChoice j (CSPCommAction cj aj)))
prevar_crl_parallelismDeadlocked3 _ = None
\end{code}
% Law 47 (Assignment Removal$^*$)

\begin{lawn}[Assignment Removal$^*$]{3}\sl
    \begin{circus}
      x := e \circseq A(x) = A(e)
   \end{circus}%
    \begin{provs}
        \item $x$ is not free in $A(e)$
    \end{provs}

  \label{law:assignmentRemoval}

\end{lawn}
\begin{code}

prevar_crl_assignmentRemoval :: CAction -> Refinement CAction
prevar_crl_assignmentRemoval ei@(CSPSeq
                            (CActionCommand (CAssign [(x,[],_)] [ZVar (e,[],t2)]))
                            (CActionCommand (CValDecl [Choose (x1,[],_) (ZVar (t,[],t4))] a)))
  = case x == x1 of
      True -> Done{orig = Just ei, refined = Just ref, proviso=[prov]}
      _ -> None
    where
      ref = (CActionCommand (CValDecl [Choose (e,[],t2) (ZVar (t,[],t4))] a))
      prov = (ZNot (ZMember (ZVar (x,[],[])) (ZSetDisplay $ zvar_to_zexpr $ varset_to_zvars(free_var_CAction ref))))
prevar_crl_assignmentRemoval _ = None
\end{code}
% Law 48 (Innocuous Assignment$^*$)

\begin{lawn}[Innocuous Assignment$^*$]{3}\sl
    \begin{circus}
      x := x = \Skip
   \end{circus}%
  \label{law:innocuousAssignment}

\end{lawn}
\begin{code}
prevar_crl_innocuousAssignment :: CAction -> Refinement CAction
prevar_crl_innocuousAssignment e@(CActionCommand (CAssign [(x1,[],_)] [ZVar (x2,[],_)]))
  = case (x1 == x2) of
      True -> Done{orig = Just e, refined = Just ref, proviso=[]}
      False -> None
    where
      ref = CSPSkip
prevar_crl_innocuousAssignment _ = None
\end{code}

\begin{lawn}[Variable Substitution$^*$]{3}\sl
    \begin{circus}
        \circvar x \circspot A(x) = \circvar y \circspot A(y)%
    \end{circus}%
    \begin{prov}
        $x$ is not free in A
        $y$ is not free in A
    \end{prov}
  \label{law:variableSubstitution}
\end{lawn}

\begin{code}
prevar_crl_variableSubstitution2 :: CAction -> ZName -> Refinement CAction
prevar_crl_variableSubstitution2
    e@(CActionCommand (CVarDecl [Include (ZSRef (ZSPlain _ []) [] [])]
             (CSPParAction a [ZVar _]))) y
  =  Done{orig = Just e, refined = Just ref, proviso=[]}
    where
      ref = (CActionCommand (CVarDecl [Include (ZSRef (ZSPlain y []) [] [])]
        (CSPParAction a [ZVar (y,[],[])])))
prevar_crl_variableSubstitution2 _ _ = None
\end{code}
% Law 50 (Input Prefix/Sequence Distribution$^*$)

\begin{lawn}[Input Prefix/Sequence Distribution$^*$]{3}\sl
    \begin{circus}
        (c?x \then A1) \circseq A2
      \\ = \\
      c?x \then (A1 \circseq A2)
    \end{circus}%
    \begin{provs}
        \item $x \notin FV(A2)$
    \end{provs}
  \label{law:inputPrefixSequenceDistribution}
\end{lawn}

\begin{code}
prevar_crl_inputPrefixSequenceDistribution :: CAction -> Refinement CAction
prevar_crl_inputPrefixSequenceDistribution
    e@(CSPSeq (CSPCommAction (ChanComm c ((ChanInp x):xs)) a1) a2 )
  =  Done{orig = Just e, refined = Just ref, proviso=[]}
    where
      ref = (CSPCommAction (ChanComm c ((ChanInp x):xs)) (CSPSeq a1 a2))
prevar_crl_inputPrefixSequenceDistribution _ = None
\end{code}
% Law 51 (Input Prefix/Hiding Identity$^*$)

\begin{lawn}[Input Prefix/Hiding Identity$^*$]{3}\sl
    \begin{circus}
        (c?x \then A1) \circhide cs
      \\ = \\
      c?x \then (A1 \circhide cs2)
    \end{circus}%
    \begin{provs}
        \item $x \notin FV(A2)$
    \end{provs}
  \label{law:inputPrefixHidIdentity}
\end{lawn}
\begin{code}
prevar_crl_inputPrefixHidIdentity :: CAction -> Refinement CAction
prevar_crl_inputPrefixHidIdentity
    e@(CSPHide (CSPCommAction (ChanComm c [ChanInp x]) a1) (CChanSet cs))
  =  Done{orig = Just e, refined = Just ref, proviso=[prov]}
    where
      ref = (CSPCommAction (ChanComm c [ChanInp x]) (CSPHide a1 (CChanSet cs)))
      prov = (ZNot (ZMember (ZVar (x,[],[])) (ZSetDisplay (zname_to_zexpr cs))))
prevar_crl_inputPrefixHidIdentity _ = None
\end{code}
% Law 52 (Guard/Parallelism composition---distribution$^*$)

\begin{lawn}[Guard/Parallelism composition---distribution$^*$]{3}\sl
    \begin{circus}
      \lcircguard g \rcircguard \circguard (A_1 \lpar ns_1 | cs | ns_2 \rpar A_2) =
      (\lcircguard g \rcircguard \circguard A_1) \lpar ns_1 | cs | ns_2 \rpar (\lcircguard g \rcircguard \circguard A_2)
    \end{circus}
    \begin{provs}
        \item $prevar_initials(A2) \subseteq cs$
    \end{provs}
  \label{law:guardParDist}
\end{lawn}
\begin{code}
prevar_crl_guardParDist :: CAction -> Refinement CAction
prevar_crl_guardParDist
    e@(CSPNSParal ns1 (CChanSet cs) ns2 (CSPGuard g a1) a2)
  =  Done{orig = Just e, refined = Just ref, proviso=[prov]}
    where
      ref = (CSPGuard g (CSPNSParal ns1 (CChanSet cs) ns2 a1 a2))
      prov = (ZMember (ZTuple [ZSetDisplay (prevar_initials a2),ZSetDisplay (zname_to_zexpr cs)]) (ZVar ("\\subseteq",[],[])))
prevar_crl_guardParDist
    e@(CSPNSParal ns1 (CChanSet cs) ns2 a1 (CSPGuard g a2))
  =  Done{orig = Just e, refined = Just ref, proviso=[prov]}
    where
      ref = (CSPGuard g (CSPNSParal ns1 (CChanSet cs) ns2 a1 a2))
      prov = (ZMember (ZTuple [ZSetDisplay (prevar_initials a1),ZSetDisplay (zname_to_zexpr cs)]) (ZVar ("\\subseteq",[],[])))
prevar_crl_guardParDist _ = None
\end{code}
% Law 53 (Internal choice/Hiding composition Distribution)

\begin{lawn}[Internal choice/Hiding composition Distribution]{3}\sl
    \begin{circus}
        (A1 \intchoice A2) \circhide cs
      \\ = \\
      (A1 \circhide cs) \intchoice (A2\circhide cs )
    \end{circus}%
  \label{law:internalChoiceHidingDistribution}
\end{lawn}
\begin{code}
prevar_crl_internalChoiceHidingDistribution :: CAction -> Refinement CAction
prevar_crl_internalChoiceHidingDistribution
    e@(CSPHide (CSPIntChoice a1 a2) cs)
  =  Done{orig = Just e, refined = Just ref, proviso=[]}
    where
      ref = (CSPIntChoice (CSPHide a1 cs) (CSPHide a2 cs))
prevar_crl_internalChoiceHidingDistribution _ = None
\end{code}
% Law 54 (Alternation Zero)
%

% \begin{lawn}[Alternation Zero]{3}\sl
%     \begin{circus}
%         \circif\ \circelse\ i \circspot g_i \then A_i \ \circfi =\Chaos
%     \end{circus}%
%     \begin{provs}
%         \item $\bigvee_i \circspot\ g_i \equiv false$
%     \end{provs}
%   \label{law:alternationZero}
%
% \end{lawn}

% \begin{code}
% prevar_crl_alternationZero
%   = undefined

% \end{code}
% Law 55 (Alternation)
%

% \begin{lawn}[Alternation]{3}\sl
%     \begin{circus}
%         \circif\ \circelse\ i : S \circspot g_i \then\ A_i \circfi
%       \\ = \\
%       \Intchoice i: T \circspot A_i%
%     \end{circus}%
%     \begin{provs}
%         \item $T \subseteq S$
%         \item $\bigwedge i : T \circspot g_i \equiv \true$
%         \item $\bigvee i : S\setminus T \circspot g_i \equiv false$
%     \end{provs}
%   \label{law:alternation}
%
% \end{lawn}

% \begin{code}
% prevar_crl_alternation
%   = undefined

% \end{code}
% Law 56 (Assignment $Skip$)


\begin{lawn}[Assignment $Skip$]{3}\sl

    \begin{circus}
        \circvar x \circspot x := e
      \\ = \\
      \circvar x \circspot \Skip%
    \end{circus}%

  \label{law:assignmentSkip}

\end{lawn}
\begin{code}
prevar_crl_assignmentSkip :: CAction -> Refinement CAction
prevar_crl_assignmentSkip
    ei@(CActionCommand (CValDecl
        [Include (ZSRef (ZSPlain x []) [] [])]
        (CActionCommand (CAssign [_] [ZVar _]))))
  =  Done{orig = Just ei, refined = Just ref, proviso=[]}
    where
      ref = (CActionCommand (CValDecl
        [Include (ZSRef (ZSPlain x []) [] [])] CSPSkip))
prevar_crl_assignmentSkip _ = None
\end{code}

\begin{lawn}[Guard combination]{3}\sl
    \begin{zed}
      \lcircguard g_1 \rcircguard \circguard (\lcircguard g_2 \rcircguard \circguard A) = \lcircguard(g_1 \land g_2)\rcircguard \circguard A%
    \end{zed}
  \label{law:guardComb}
\end{lawn}

\begin{code}
prevar_crl_guardComb :: CAction -> Refinement CAction
prevar_crl_guardComb e@(CSPGuard g1 (CSPGuard g2 c))
  =  Done{orig = Just e, refined = Just ref, proviso=[]}
    where
      ref = (CSPGuard (ZAnd g1 g2) c)
prevar_crl_guardComb _ = None

\end{code}

\begin{lawn}[Assignment then choice]{3}\sl
    \begin{zed}
      (((x := a1) \circseq (a \then \Skip)) \extchoice ((y := a2) \circseq (b \then \Skip)))
      \\=\\
      ((a \then (x := a1)) \extchoice (b \then (x := a2)))
    \end{zed}
  \label{law:asgThenChoose}
\end{lawn}

\begin{code}
prevar_crl_asgThenChoose :: CAction -> Refinement CAction
prevar_crl_asgThenChoose e@(CSPExtChoice e1 e2)
  =  Done{orig = Just e, refined = Just ref, proviso=[]}
    where
      ref = (CSPExtChoice (prevar_crl_asgThenChoose_aux e1) (prevar_crl_asgThenChoose_aux e2))
prevar_crl_asgThenChoose _ = None

prevar_crl_asgThenChoose_aux :: CAction -> CAction
prevar_crl_asgThenChoose_aux (CSPSeq (CActionCommand (CAssign [v1] [a1])) (CSPCommAction (ChanComm a []) na))
  = (CSPCommAction (ChanComm a []) (CSPSeq (CActionCommand (CAssign [v1] [a1])) na))
prevar_crl_asgThenChoose_aux x = x
\end{code}


\begin{lawn}[Skip and Interleave]{3}\sl
    \begin{zed}
      \Skip \interleave A = A\\
      A \interleave \Skip = A\\
    \end{zed}
  \label{law:skipInterleave}
\end{lawn}

\begin{code}
prevar_crl_skipInterleave :: CAction -> Refinement CAction
prevar_crl_skipInterleave e@(CSPInterleave CSPSkip e2)
  =  Done{orig = Just e, refined = Just e2, proviso=[]}

prevar_crl_skipInterleave e@(CSPInterleave e2 CSPSkip)
  =  Done{orig = Just e, refined = Just e2, proviso=[]}
prevar_crl_skipInterleave _ = None

\end{code}


\subsection{Auxiliary functions from Oliveira's PhD thesis}
Function for $prevar_usedC(A)$
\begin{code}
prevar_usedC :: CAction -> [ZExpr]
prevar_usedC (CSPCommAction x c) = [getCommName x] ++ prevar_usedC c
prevar_usedC (CSPGuard _ c) = prevar_usedC c
prevar_usedC (CSPSeq ca cb) = (prevar_usedC ca) ++ (prevar_usedC cb)
prevar_usedC (CSPExtChoice ca cb) = (prevar_usedC ca) ++ (prevar_usedC cb)
prevar_usedC (CSPIntChoice ca cb) = (prevar_usedC ca) ++ (prevar_usedC cb)
prevar_usedC (CSPNSParal _ _ _ ca cb) = (prevar_usedC ca) ++ (prevar_usedC cb)
prevar_usedC (CSPParal _ ca cb) = (prevar_usedC ca) ++ (prevar_usedC cb)
prevar_usedC (CSPNSInter _ _ ca cb) = (prevar_usedC ca) ++ (prevar_usedC cb)
prevar_usedC (CSPInterleave ca cb) = (prevar_usedC ca) ++ (prevar_usedC cb)
prevar_usedC (CSPHide c _) = prevar_usedC c
prevar_usedC (CSPRecursion _ c) = prevar_usedC c
prevar_usedC (CSPRepSeq _ c) = prevar_usedC c
prevar_usedC (CSPRepExtChoice _ c) = prevar_usedC c
prevar_usedC (CSPRepIntChoice _ c) = prevar_usedC c
prevar_usedC (CSPRepParalNS _ _ _ c) = prevar_usedC c
prevar_usedC (CSPRepParal _ _ c) = prevar_usedC c
prevar_usedC (CSPRepInterlNS _ _ c) = prevar_usedC c
prevar_usedC (CSPRepInterl _ c) = prevar_usedC c
prevar_usedC _ = []
\end{code}Function for $prevar_usedV(A)$
\begin{code}
prevar_usedV :: CAction -> [a]
prevar_usedV (CSPCommAction _ c) = [] ++ prevar_usedV c
prevar_usedV (CSPGuard _ c) = prevar_usedV c
prevar_usedV (CSPSeq ca cb) = (prevar_usedV ca) ++ (prevar_usedV cb)
prevar_usedV (CSPExtChoice ca cb) = (prevar_usedV ca) ++ (prevar_usedV cb)
prevar_usedV (CSPIntChoice ca cb) = (prevar_usedV ca) ++ (prevar_usedV cb)
prevar_usedV (CSPNSParal _ _ _ ca cb) = (prevar_usedV ca) ++ (prevar_usedV cb)
prevar_usedV (CSPParal _ ca cb) = (prevar_usedV ca) ++ (prevar_usedV cb)
prevar_usedV (CSPNSInter _ _ ca cb) = (prevar_usedV ca) ++ (prevar_usedV cb)
prevar_usedV (CSPInterleave ca cb) = (prevar_usedV ca) ++ (prevar_usedV cb)
prevar_usedV (CSPHide c _) = prevar_usedV c
prevar_usedV (CSPRecursion _ c) = prevar_usedV c
prevar_usedV (CSPRepSeq _ c) = prevar_usedV c
prevar_usedV (CSPRepExtChoice _ c) = prevar_usedV c
prevar_usedV (CSPRepIntChoice _ c) = prevar_usedV c
prevar_usedV (CSPRepParalNS _ _ _ c) = prevar_usedV c
prevar_usedV (CSPRepParal _ _ c) = prevar_usedV c
prevar_usedV (CSPRepInterlNS _ _ c) = prevar_usedV c
prevar_usedV (CSPRepInterl _ c) = prevar_usedV c
prevar_usedV _ = []
\end{code}
\begin{code}
getCommName :: Comm -> ZExpr
getCommName (ChanComm n _) = ZVar (n,[],[])
getCommName (ChanGenComm n _ _) = ZVar (n,[],[])

\end{code}
Function used for $prevar_initials$
\begin{code}
prevar_initials :: CAction -> [ZExpr]
prevar_initials (CSPCommAction x _) = [getCommName x]
prevar_initials (CSPGuard _ c) = prevar_initials c
prevar_initials (CSPSeq ca _) = (prevar_initials ca)
prevar_initials (CSPExtChoice ca cb) = (prevar_initials ca) ++ (prevar_initials cb)
prevar_initials (CSPIntChoice ca cb) = (prevar_initials ca) ++ (prevar_initials cb)
prevar_initials (CSPNSParal _ _ _ ca cb) = (prevar_initials ca) ++ (prevar_initials cb)
prevar_initials (CSPParal _ ca cb) = (prevar_initials ca) ++ (prevar_initials cb)
prevar_initials (CSPNSInter _ _ ca cb) = (prevar_initials ca) ++ (prevar_initials cb)
prevar_initials (CSPInterleave ca cb) = (prevar_initials ca) ++ (prevar_initials cb)
prevar_initials (CSPHide c _) = prevar_initials c
prevar_initials (CSPRecursion _ c) = prevar_initials c
prevar_initials (CSPRepSeq _ c) = prevar_initials c
prevar_initials (CSPRepExtChoice _ c) = prevar_initials c
prevar_initials (CSPRepIntChoice _ c) = prevar_initials c
prevar_initials (CSPRepParalNS _ _ _ c) = prevar_initials c
prevar_initials (CSPRepParal _ _ c) = prevar_initials c
prevar_initials (CSPRepInterlNS _ _ c) = prevar_initials c
prevar_initials (CSPRepInterl _ c) = prevar_initials c
prevar_initials CSPSkip = [ZVar ("tick",[],[])]
prevar_initials _ = []
\end{code}
\begin{code}
--prevar_trace (CSPCommAction (ChanComm x _) c) =
--  [[],[x],map (x:) (prevar_trace c)]
--prevar_trace (CSPCommAction (ChanGenComm x _ _) c) =
--  [[],[x],map (x:) (prevar_trace c)]
--prevar_trace (CSPSeq ca cb) = (prevar_trace ca)
--prevar_trace (CSPExtChoice ca cb) = (prevar_trace ca) ++ (prevar_trace cb)
data CSPOp = Com Char CSPOp | Seq CSPOp CSPOp | ExtCh CSPOp CSPOp | CSPSkp
prevar_trace :: CSPOp -> [[Char]]
prevar_trace (Com a p) = map (a:) (prevar_trace p)
prevar_trace (Seq a b) = (prevar_trace a) ++ (prevar_trace b)
prevar_trace (ExtCh a b) = (prevar_trace a)++ (prevar_trace b)
prevar_trace (CSPSkp)
 = [[]]
\end{code}
Function used for $prevar_deterministic$
\begin{code}
prevar_deterministic :: CAction -> Maybe [Char]
prevar_deterministic (CSPCommAction _ c) = prevar_deterministic c
prevar_deterministic (CSPGuard _ c) = prevar_deterministic c
prevar_deterministic (CSPSeq ca cb) =
  case (da == Nothing)
    && (da == db)
    of
        False -> Just "Deterministic"
        True -> Nothing
  where
    da = (prevar_deterministic ca)
    db = (prevar_deterministic cb)

prevar_deterministic (CSPExtChoice ca cb) =
  case (da == Nothing)
    && (da == db)
    of
        False -> Just "Deterministic"
        True -> Nothing
  where
    da = (prevar_deterministic ca)
    db = (prevar_deterministic cb)

prevar_deterministic (CSPIntChoice _ _) = Nothing
prevar_deterministic (CSPNSParal _ _ _ _ _) = Nothing
prevar_deterministic (CSPParal _ _ _) =  Nothing
prevar_deterministic (CSPNSInter _ _ ca cb) =
  case (da == Nothing)
    && (da == db)
    of
        False -> Just "Deterministic"
        True -> Nothing
  where
    da = (prevar_deterministic ca)
    db = (prevar_deterministic cb)

prevar_deterministic (CSPInterleave ca cb) =
  case (da == Nothing)
    && (da == db)
    of
        False -> Just "Deterministic"
        True -> Nothing
  where
    da = (prevar_deterministic ca)
    db = (prevar_deterministic cb)
prevar_deterministic (CSPHide _ _) = Nothing
prevar_deterministic (CSPRecursion _ c) = prevar_deterministic c
prevar_deterministic (CSPRepSeq _ c) = prevar_deterministic c
prevar_deterministic (CSPRepExtChoice _ c) = prevar_deterministic c
prevar_deterministic (CSPRepIntChoice _ _) = Nothing
prevar_deterministic (CSPRepParalNS _ _ _ _) = Nothing
prevar_deterministic (CSPRepParal _ _ _) = Nothing
prevar_deterministic (CSPRepInterlNS _ _ c) = prevar_deterministic c
prevar_deterministic (CSPRepInterl _ c) = prevar_deterministic c
prevar_deterministic CSPSkip = Just "Deterministic"
prevar_deterministic _ = Just "Undefined"
\end{code}
\begin{code}
prevar_isDeterministic :: CAction -> [Char]
prevar_isDeterministic a
  = case x of
      Just "Deterministic" -> "Deterministic"
      Just _               -> "undefined"
      Nothing              -> "Non-prevar_deterministic"
    where x = (prevar_deterministic a)
\end{code}

\subsection{Mechanism for applying the prevar_refinement laws}

First I'm listing all the prevar_refinement laws currently available. Then I'm putting it as the variable "reflaws".\ignore{
\begin{code}
-- Description of each function:

-- For Circus Actions:
-- prevar_crl_assignmentRemoval :: CAction -> Refinement CAction
-- prevar_crl_assignmentSkip :: CAction -> Refinement CAction
-- prevar_crl_chanExt1 :: CAction -> ZName -> Refinement CAction
-- prevar_crl_communicationParallelismDistribution :: CAction -> CAction
-- prevar_crl_extChoiceSeqDist :: CAction -> CAction
-- prevar_crl_extChoiceStopUnit :: CAction -> CAction
-- prevar_crl_externalChoiceSequenceDistribution2 :: CAction -> Refinement CAction
-- prevar_crl_falseGuard :: CAction -> Refinement CAction
-- prevar_crl_guardParDist :: CAction -> Refinement CAction
-- prevar_crl_guardSeqAssoc :: CAction -> Refinement CAction
-- prevar_crl_hidingChaos :: CAction -> Refinement CAction
-- prevar_crl_hidingCombination :: CAction -> Refinement CAction
-- prevar_crl_hidingExpansion2 :: CAction -> ZName -> Refinement CAction
-- prevar_crl_hidingExternalChoiceDistribution :: CAction -> CAction
-- prevar_crl_hidingIdentity :: CAction -> Refinement CAction
-- prevar_crl_hidingParallelismDistribution :: CAction -> Refinement CAction
-- prevar_crl_hidingSequenceDistribution :: CAction -> Refinement CAction
-- prevar_crl_innocuousAssignment :: CAction -> Refinement CAction
-- prevar_crl_inputPrefixHidIdentity :: CAction -> Refinement CAction
-- prevar_crl_inputPrefixParallelismDistribution2 :: CAction -> Refinement CAction
-- prevar_crl_inputPrefixSequenceDistribution :: CAction -> Refinement CAction
-- prevar_crl_internalChoiceHidingDistribution :: CAction -> Refinement CAction
-- prevar_crl_internalChoiceParallelismDistribution :: CAction -> Refinement CAction
-- prevar_crl_joinBlocks :: CAction -> Refinement CAction
-- prevar_crl_parallelismDeadlocked1 :: CAction -> CAction
-- prevar_crl_parallelismDeadlocked3 :: CAction -> Refinement CAction
-- prevar_crl_parallelismExternalChoiceDistribution :: CAction -> CAction
-- prevar_crl_parallelismExternalChoiceExpansion :: CAction -> Comm -> CAction -> Refinement CAction
-- prevar_crl_parallelismIntroduction1a :: CAction -> ZExpr -> [ZName] -> ZExpr -> Refinement CAction
-- prevar_crl_parallelismIntroduction1b :: CAction -> ZExpr -> [ZName] -> ZExpr -> Refinement CAction
-- prevar_crl_parallelismUnit1 :: CAction -> Refinement CAction
-- prevar_crl_parallelismZero :: CAction -> Refinement CAction
-- prevar_crl_parallInterlEquiv :: CAction -> Refinement CAction
-- prevar_crl_parallInterlEquiv_backwards :: CAction -> Refinement CAction
-- prevar_crl_parExtChoiceExchange :: CAction -> Refinement CAction
-- prevar_crl_parSeqStep :: CAction -> Refinement CAction
-- prevar_crl_prefixHiding :: CAction -> Refinement CAction
-- prevar_crl_prefixParDist :: CAction -> Refinement CAction
-- prevar_crl_prefixSkip :: CAction -> Refinement CAction
-- prevar_crl_recUnfold :: CAction -> Refinement CAction
-- prevar_crl_seqChaosZero :: CAction -> Refinement CAction
-- prevar_crl_seqSkipUnit_a :: CAction -> Refinement CAction
-- prevar_crl_seqSkipUnit_b :: CAction -> Refinement CAction
-- prevar_crl_seqStopZero :: CAction -> CAction
-- prevar_crl_sequenceInternalChoiceDistribution :: CAction -> Refinement CAction
-- prevar_crl_trueGuard :: CAction -> Refinement CAction
-- prevar_crl_var_exp_par :: CAction -> Refinement CAction
-- prevar_crl_var_exp_par2 :: CAction -> Refinement CAction
-- prevar_crl_var_exp_rec :: CAction -> Refinement CAction
-- prevar_crl_variableBlockIntroduction :: CAction -> ZVar -> ZExpr -> Refinement CAction
-- prevar_crl_variableBlockSequenceExtension :: CAction -> Refinement CAction
-- prevar_crl_variableSubstitution2 :: CAction -> ZName -> Refinement CAction

-- For Circus Processes:
-- prevar_crl_promVarState :: CProc -> Refinement CProc
-- prevar_crl_promVarState2 :: CProc -> ZSName -> Refinement CProc
\end{code}
}
\begin{code}
prevar_reflawsCAction :: [CAction -> Refinement CAction]
prevar_reflawsCAction
        = [prevar_crl_assignmentRemoval,
           prevar_crl_asgThenChoose,
            -- ,
            -- prevar_crl_chanExt1,
            -- prevar_crl_hidingExpansion2,
            -- prevar_crl_parallelismIntroduction1a,
            -- prevar_crl_parallelismIntroduction1a_backwards,
            -- prevar_crl_parallelismIntroduction1b,
            -- prevar_crl_parallelismIntroduction1b_backwards,
            -- prevar_crl_parallInterlEquiv_backwards,
            -- prevar_crl_promVarState,
            -- prevar_crl_promVarState2,
            -- prevar_crl_var_exp_par,
            -- prevar_crl_variableBlockIntroduction,
            -- prevar_crl_variableSubstitution2,
            prevar_crl_variableBlockSequenceExtension,
            prevar_crl_assignmentSkip,
            prevar_crl_communicationParallelismDistribution,
            prevar_crl_extChoiceStopUnit,
            prevar_crl_externalChoiceSequenceDistribution2,
            prevar_crl_falseGuard,
            prevar_crl_skipInterleave,
           prevar_crl_guardParDist,
            prevar_crl_guardComb,
             prevar_crl_guardSeqAssoc,
            prevar_crl_hidingChaos,
            prevar_crl_hidingCombination,
            prevar_crl_hidingExternalChoiceDistribution,
            prevar_crl_hidingIdentity,
            prevar_crl_hidingParallelismDistribution,
            prevar_crl_hidingSequenceDistribution,
            prevar_crl_innocuousAssignment,
            prevar_crl_inputPrefixHidIdentity,
            prevar_crl_inputPrefixParallelismDistribution2,
            prevar_crl_inputPrefixSequenceDistribution,
            prevar_crl_internalChoiceHidingDistribution,
            prevar_crl_internalChoiceParallelismDistribution,
            prevar_crl_joinBlocks,
            prevar_crl_parallelismDeadlocked1,
            prevar_crl_parallelismUnit1,
            prevar_crl_parallelismZero,
            prevar_crl_parallInterlEquiv,
            prevar_crl_parExtChoiceExchange,
            prevar_crl_prefixHiding,
            prevar_crl_prefixParDist,
            prevar_crl_parallelismExternalChoiceExpansionB,
            -- prevar_crl_prefixSkip, -- This one is going into an infinite loop with prevar_crl_seqSkipUnit_a
            prevar_crl_prefixSkip_backwards, -- this one fixes the probl above
            prevar_crl_prefixSeq_backwards,
            prevar_crl_recUnfold,
            prevar_crl_seqChaosZero,
            prevar_crl_seqSkipUnit_a,
            prevar_crl_seqSkipUnit_b,
            prevar_crl_seqStopZero,
            prevar_crl_sequenceInternalChoiceDistribution,
            prevar_crl_trueGuard,
            prevar_crl_var_exp_par2,
            prevar_crl_var_exp_rec,
            prevar_crl_variableBlockIntroduction_backwards
          ]
-- reflawsCProc = [prevar_crl_promVarState, prevar_crl_promVarState2]
\end{code}

I'm defining a type for the result of the prevar_refinement. It can either be $None$, when the prevar_refinement is not applied to that specification, or, it can be $Done\{refined :: t, proviso :: [Bool]\}$ with a list of provisos to be proved true, where $t$ can either be used for a $CProc$ or a $CAction$. We then will write those provisos in a text file so it can be used in a theorem prover, like Isabelle/HOL.
\begin{code}
data Refinement t = None
                  | Done{orig :: Maybe t,
                          refined :: Maybe t,
                          proviso :: [ZPred]
                    } deriving (Eq,Show)
\end{code}
Then I'm starting to implement the mechanism itself. Basically, it will try to apply the prevar_refinement laws one by one until a result $Refinement CAction$ is returned.
\begin{code}
type PRFun t = t -> Refinement t
\end{code}
The function $prevar_applyCAction$ will try to apply a prevar_refinement law $r$ on an action $e$. If the result from applying it is $Done\{\ldots\}$, then this is the result. Otherwise, it will try to apply recursively to the inner parts of the $CAction$.
\begin{code}

prevar_applyCAction :: (PRFun CAction) -> (PRFun CAction)
prevar_applyCAction r e@(CActionCommand (CIf g))
 = case r e of
     r'@(Done{orig = _or, refined = _re, proviso=_pr}) -> r'
     None
      -> (case prevar_applyCActionsIf r g of
          (a,b) ->
              Done{orig = Just e, refined = Just (CActionCommand (CIf a)), proviso=b})
{-
prevar_applyCAction r e@(CSPSeq a1 a2) = case r e of
     r'@(Done{orig = _or, refined = _re, proviso=_pr}) -> r'
     None
      -> case prevar_applyCActions r [a1,a2]  of
            [a1', a2'] ->
                Done{orig = Just e,
                    refined = Just (CSPSeq (prevar_isRefined a1 a1') (prevar_isRefined a2 a2')),
                    proviso=(prevar_get_proviso a1')++(prevar_get_proviso a2')}
            _ -> None
-}

prevar_applyCAction r e@(CActionCommand (CVarDecl gf c))
 = case r e of
     r'@(Done{orig = _or, refined = _re, proviso=_pr}) -> r'
     None
      -> case prevar_applyCActions r [c]  of
          [c'] ->
              Done{orig = Just e, refined = Just (CActionCommand (CVarDecl gf (prevar_isRefined c c'))), proviso=(prevar_get_proviso c')}
          _ -> None

prevar_applyCAction r e@(CActionCommand (CValDecl gf c))
 = case r e of
     r'@(Done{orig = _or, refined = _re, proviso=_pr}) -> r'
     None
      -> case prevar_applyCActions r [c]  of
          [c'] ->
              Done{orig = Just e, refined = Just (CActionCommand (CValDecl gf (prevar_isRefined c c'))), proviso=(prevar_get_proviso c')}
          _ -> None

prevar_applyCAction r e@(CActionCommand (CResDecl gf c))
 = case r e of
     r'@(Done{orig = _or, refined = _re, proviso=_pr}) -> r'
     None
      -> case prevar_applyCActions r [c]  of
          [c'] ->
              Done{orig = Just e, refined = Just (CActionCommand (CResDecl gf (prevar_isRefined c c'))), proviso=(prevar_get_proviso c')}
          _ -> None

prevar_applyCAction r e@(CActionCommand (CVResDecl gf c))
 = case r e of
     r'@(Done{orig = _or, refined = _re, proviso=_pr}) -> r'
     None
      -> case prevar_applyCActions r [c]  of
          [c'] ->
              Done{orig = Just e, refined = Just (CActionCommand (CVResDecl gf (prevar_isRefined c c'))), proviso=(prevar_get_proviso c')}
          _ -> None

prevar_applyCAction r e@(CSPCommAction cc c)
 = case r e of
     r'@(Done{orig = _or, refined = _re, proviso=_pr}) -> r'
     None
      -> case prevar_applyCActions r [c]  of
          [c'] ->
              Done{orig = Just e,
                  refined = Just (CSPCommAction cc (prevar_isRefined c c')), proviso=(prevar_get_proviso c')}
          _ -> None

prevar_applyCAction r e@(CSPGuard p c) = case r e of
     r'@(Done{orig = _or, refined = _re, proviso=_pr}) -> r'
     None
      -> case prevar_applyCActions r [c]  of
          [c'] ->
              Done{orig = Just e, refined = Just (CSPGuard p (prevar_isRefined c c')), proviso=(prevar_get_proviso c')}
          _ -> None

prevar_applyCAction r e@(CSPSeq a1 a2) = case r e of
     r'@(Done{orig = _or, refined = _re, proviso=_pr}) -> r'
     None
      -> case prevar_applyCActions r [a1,a2]  of
            [a1', a2'] ->
                Done{orig = Just e,
                    refined = Just (CSPSeq (prevar_isRefined a1 a1') (prevar_isRefined a2 a2')),
                    proviso=(prevar_get_proviso a1')++(prevar_get_proviso a2')}
            _ -> None

prevar_applyCAction r e@(CSPExtChoice a1 a2) = case r e of
     r'@( Done{orig = _or, refined = _re, proviso=_pr}) -> r'
     None
      -> case prevar_applyCActions r [a1,a2]  of
            [a1', a2'] ->
                Done{orig = Just e,
                    refined = Just (CSPExtChoice (prevar_isRefined a1 a1') (prevar_isRefined a2 a2')),
                    proviso=(prevar_get_proviso a1')++(prevar_get_proviso a2')}
            _ -> None

prevar_applyCAction r e@(CSPIntChoice a1 a2) = case r e of
     r'@( Done{orig = _or, refined = _re, proviso=_pr}) -> r'
     None
      -> case prevar_applyCActions r [a1,a2]  of
            [a1', a2'] ->
                Done{orig = Just e,
                    refined = Just (CSPIntChoice (prevar_isRefined a1 a1') (prevar_isRefined a2 a2')),
                    proviso=(prevar_get_proviso a1')++(prevar_get_proviso a2')}
            _ -> None

prevar_applyCAction r e@(CSPParal cs a1 a2) = case r e of
     r'@( Done{orig = _or, refined = _re, proviso=_pr}) -> r'
     None
      -> case prevar_applyCActions r [a1,a2]  of
            [a1', a2'] ->
                Done{orig = Just e,
                    refined = Just (CSPParal cs (prevar_isRefined a1 a1') (prevar_isRefined a2 a2')),
                    proviso=(prevar_get_proviso a1')++(prevar_get_proviso a2')}
            _ -> None

prevar_applyCAction r e@(CSPNSParal ns1 cs ns2 a1 a2)
 = case r e of
     r'@(Done{orig = _or, refined = _re, proviso=_pr}) -> r'
     None
      -> case prevar_applyCActions r [a1,a2]  of
            [a1', a2'] ->
                Done{orig = Just e,
                    refined = Just (CSPNSParal ns1 cs ns2 (prevar_isRefined a1 a1') (prevar_isRefined a2 a2')),
                    proviso=(prevar_get_proviso a1')++(prevar_get_proviso a2')}
            _ -> None

prevar_applyCAction r e@(CSPNSInter ns1 ns2 a1 a2) = case r e of
     r'@( Done{orig = _or, refined = _re, proviso=_pr}) -> r'
     None
      -> case prevar_applyCActions r [a1,a2]  of
            [a1', a2'] ->
                Done{orig = Just e,
                    refined = Just (CSPNSInter ns1 ns2 (prevar_isRefined a1 a1') (prevar_isRefined a2 a2')),
                    proviso=(prevar_get_proviso a1')++(prevar_get_proviso a2')}
            _ -> None

prevar_applyCAction r e@(CSPInterleave a1 a2) = case r e of
     r'@( Done{orig = _or, refined = _re, proviso=_pr}) -> r'
     None
      -> case prevar_applyCActions r [a1,a2]  of
            [a1', a2'] ->
                Done{orig = Just e,
                    refined = Just (CSPInterleave (prevar_isRefined a1 a1') (prevar_isRefined a2 a2')),
                    proviso=(prevar_get_proviso a1')++(prevar_get_proviso a2')}
            _ -> None
prevar_applyCAction r e@(CSPHide c cs) = case r e of
     r'@( Done{orig = _or, refined = _re, proviso=_pr}) -> r'
     None
      -> case prevar_applyCActions r [c]  of
          [c'] -> Done{orig = Just e,
                       refined = Just (CSPHide (prevar_isRefined c c') cs),
                       proviso=(prevar_get_proviso c')}
          _ -> None

prevar_applyCAction r e@(CSPUnfAction nm c) = case r e of
     r'@( Done{orig = _or, refined = _re, proviso=_pr}) -> r'
     None
      -> case prevar_applyCActions r [c]  of
          [c'] ->
              Done{orig = Just e, refined = Just (CSPUnfAction nm (prevar_isRefined c c')), proviso=(prevar_get_proviso c')}
          _ -> None

prevar_applyCAction r e@(CSPRecursion nm c) = case r e of
     r'@( Done{orig = _or, refined = _re, proviso=_pr}) -> r'
     None
      -> case prevar_applyCActions r [c]  of
          [c'] ->
              Done{orig = Just e, refined = Just (CSPRecursion nm (prevar_isRefined c c')), proviso=(prevar_get_proviso c')}
          _ -> None

prevar_applyCAction r e@(CSPUnParAction lst c nm) = case r e of
     r'@( Done{orig = _or, refined = _re, proviso=_pr}) -> r'
     None
      -> case prevar_applyCActions r [c]  of
          [c'] ->
              Done{orig = Just e, refined = Just (CSPUnParAction lst (prevar_isRefined c c') nm), proviso=(prevar_get_proviso c')}
          _ -> None

prevar_applyCAction r e@(CSPRepSeq lst c) = case r e of
     r'@( Done{orig = _or, refined = _re, proviso=_pr}) -> r'
     None
      -> case prevar_applyCActions r [c]  of
          [c'] ->
              Done{orig = Just e, refined = Just (CSPRepSeq lst (prevar_isRefined c c')), proviso=(prevar_get_proviso c')}
          _ -> None

prevar_applyCAction r e@(CSPRepExtChoice lst c) = case r e of
     r'@( Done{orig = _or, refined = _re, proviso=_pr}) -> r'
     None
      -> case prevar_applyCActions r [c]  of
          [c'] ->
              Done{orig = Just e, refined = Just (CSPRepExtChoice lst (prevar_isRefined c c')), proviso=(prevar_get_proviso c')}
          _ -> None

prevar_applyCAction r e@(CSPRepIntChoice lst c) = case r e of
     r'@( Done{orig = _or, refined = _re, proviso=_pr}) -> r'
     None
      -> case prevar_applyCActions r [c]  of
          [c'] ->
              Done{orig = Just e, refined = Just (CSPRepIntChoice lst (prevar_isRefined c c')), proviso=(prevar_get_proviso c')}
          _ -> None

prevar_applyCAction r e@(CSPRepParalNS cs lst ns c) = case r e of
     r'@( Done{orig = _or, refined = _re, proviso=_pr}) -> r'
     None
      -> case prevar_applyCActions r [c]  of
          [c'] ->
              Done{orig = Just e, refined = Just (CSPRepParalNS cs lst ns (prevar_isRefined c c')), proviso=(prevar_get_proviso c')}
          _ -> None

prevar_applyCAction r e@(CSPRepParal cs lst c) = case r e of
     r'@( Done{orig = _or, refined = _re, proviso=_pr}) -> r'
     None
      -> case prevar_applyCActions r [c]  of
          [c'] ->
              Done{orig = Just e, refined = Just (CSPRepParal cs lst (prevar_isRefined c c')), proviso=(prevar_get_proviso c')}
          _ -> None
prevar_applyCAction r e@(CSPRepInterlNS lst ns c) = case r e of
     r'@( Done{orig = _or, refined = _re, proviso=_pr} )-> r'
     None
      -> case prevar_applyCActions r [c]  of
          [c'] ->
              Done{orig = Just e, refined = Just (CSPRepInterlNS lst ns (prevar_isRefined c c')), proviso=(prevar_get_proviso c')}
          _  -> None

prevar_applyCAction r e@(CSPRepInterl lst c) = case r e of
     r'@(Done{orig = _or, refined = _re, proviso=_pr}) -> r'
     None
      -> case prevar_applyCActions r [c]  of
          [c'] ->
              Done{orig = Just e, refined = Just (CSPRepInterl lst (prevar_isRefined c c')), proviso=(prevar_get_proviso c')}
          _ -> None
prevar_applyCAction r e
 = case r e of
     r'@(Done{orig = _or, refined = _re, proviso=_pr}) -> r'
     None ->  None

\end{code}
\subsection{Applying to a list of actions -- $prevar_applyCActions$}
Applies a prevar_refinement law into a list of actions.
\begin{code}
prevar_applyCActions :: PRFun CAction -> [CAction] -> [Refinement CAction]
prevar_applyCActions _ [] = []
-- prevar_applyCActions r [e] = [prevar_applyCAction r e]
prevar_applyCActions r (e:es) = (prevar_applyCAction r e):(prevar_applyCActions r es)
\end{code}
\subsection{Applying to a list of guarded actions -- $prevar_applyCActionsIf$}
Applies a prevar_refinement law into a list of actions.
\begin{code}
prevar_applyCActionsIf :: PRFun CAction -> CGActions -> (CGActions,[ZPred])
prevar_applyCActionsIf r (CircGAction zp ca)
  = ((CircGAction zp (prevar_isRefined ca ca')), prevar_get_proviso ca')
  where ca' = (prevar_applyCAction r ca)
prevar_applyCActionsIf r (CircThenElse ga gb)
 = ((CircThenElse ga' gb'),prova++provb)
  where (ga',prova) = (prevar_applyCActionsIf r ga)
        (gb',provb) = (prevar_applyCActionsIf r gb)
\end{code}

\subsection{Checking the prevar_refinement results}
This will control if something was refined or not
\begin{code}
prevar_isRefined :: t-> Refinement t -> t
prevar_isRefined a b
  = case b of
      (Done{orig=_, refined=Just e', proviso=_}) -> e'
      _ -> a
prevar_isRefined' :: t-> Maybe t -> t
prevar_isRefined' a b
  = case b of
      Just e' -> e'
      Nothing -> a

\end{code}

\subsection{The automated prevar_refinement tool}

\begin{code}
prevar_crefine :: [PRFun CAction]
                 -> [PRFun CAction]
                 -> CAction
                 -> [Refinement CAction]
                 -> [Refinement CAction]
prevar_crefine _ [] _ _ = [None]
prevar_crefine _ [r] e steps =
    reverse (results:steps)
    where
      results = prevar_applyCAction r e

prevar_crefine lst (r:rs) e steps =
    case rsx of
      ei@(Done{orig=Just a, refined=Just e', proviso=_}) ->
        case a==e' of
          True -> prevar_crefine lst rs e steps
          False -> prevar_crefine lst lst e' (ei:steps)
      _ -> prevar_crefine lst rs e steps
    where rsx = prevar_applyCAction r e

prevar_refine :: [PRFun CAction] -> CAction -> [Refinement CAction]
prevar_refine f g = prevar_crefine f f g []
\end{code}
\begin{code}
prevar_getRef ::  [Refinement t] -> Maybe t
prevar_getRef [] = Nothing
prevar_getRef [(Done{orig=_, refined=y, proviso=_})] = y
prevar_getRef [_] = Nothing
prevar_getRef [(Done{orig=_, refined=y, proviso=_}),_] = y
prevar_getRef (_ : xs) = prevar_getRef xs
\end{code}

\subsection{Testing the tool}
\begin{code}
prevar_runStepRefinement :: CAction -> [Refinement CAction]
prevar_runStepRefinement x = prevar_refine prevar_reflawsCAction x

prevar_runRefinement :: CAction -> Maybe CAction
prevar_runRefinement x = prevar_getRef $ prevar_refine prevar_reflawsCAction x

refineCAction :: CAction -> CAction
refineCAction x = prevar_get_refined $ last (prevar_refine prevar_reflawsCAction x)
\end{code}

\subsection{Printing the Refinement Steps}
First we get the bits from the $Refinement$ record
\begin{code}
prevar_get_orig :: Refinement CAction -> CAction
prevar_get_orig (Done{orig=Just a,refined=_,proviso=_}) = a
prevar_get_orig _ = error "Unable to get the Action prevar_refinement original CAction"

prevar_get_refined :: Refinement CAction -> CAction
prevar_get_refined (Done{orig=_,refined=Just b,proviso=_}) = b
prevar_get_refined (Done{orig=Just a,refined=Nothing,proviso=_}) = a
prevar_get_refined _ = error "Unable to get the refined CAction"

prevar_get_proviso :: Refinement CAction -> [ZPred]
prevar_get_proviso None = []
prevar_get_proviso (Done{orig=_,refined=_,proviso=c}) = c
\end{code}

Then we define some printing functions, so the prevar_refinement can look better on screen.

\begin{code}
prevar_print_proviso :: Show a => [a] -> [Char]
prevar_print_proviso [] = "none"
prevar_print_proviso [c] = show c
prevar_print_proviso (c:cs) = (show c) ++ "] and also [" ++ (prevar_print_proviso cs)

prevar_print_ref_head :: Refinement CAction -> [Char]
prevar_print_ref_head c = "LHS\n=\n"
                 ++ (show (prevar_get_orig c)) ++"\n\n=   provided["
                 ++ (prevar_print_proviso (prevar_get_proviso c)) ++"]\n\n"
                 ++ (show (prevar_get_refined c)) ++"\n\n"

prevar_print_ref_steps :: Refinement CAction -> [Char]
prevar_print_ref_steps c = "=   provided["
                 ++ (prevar_print_proviso (prevar_get_proviso c)) ++"]\n\n"
                 ++ (show (prevar_get_refined c)) ++ "\n\n"
\end{code}
Finally, we define a $print\_ref$ function which prints out on screen the prevar_refinement. We can take that to a file with $print\_file\_ref$.
\begin{code}

prevar_print_ref :: [Refinement CAction] -> [Char]
prevar_print_ref [] = "No prevar_refinement was performed\n"
prevar_print_ref [None] = "No prevar_refinement was performed\n"
prevar_print_ref [x] = prevar_print_ref_head x
prevar_print_ref (x:xs) = prevar_print_ref_head x ++ (prevar_print_ref' xs)

prevar_print_ref' :: [Refinement CAction] -> [Char]
prevar_print_ref' [] = "=\nRHS"
prevar_print_ref' [x] = prevar_print_ref_steps x
prevar_print_ref' (x:xs) = prevar_print_ref_steps x ++ (prevar_print_ref' xs)

prevar_print_file_ref :: FilePath -> CAction -> IO ()
prevar_print_file_ref fname example = writeFile fname $ prevar_print_ref $prevar_runStepRefinement example

\end{code}
\ignore{
Testing area
\begin{code}
-- Usage:
-- you can type
-- $ prevar_print_file_ref "ref_steps.txt" prevar_cexample2
-- And it will write the prevar_refinement of prevar_cexample2 into the ref_steps.txt file.
prevar_cexample :: CAction
prevar_cexample = (CSPNSParal [] (CChanSet ["c1","c2"]) [] (CSPGuard (ZMember (ZTuple [ZVar ("v1",[],[]),ZInt 0]) (ZVar (">",[],[])))  (CActionName "a1")) (CActionName "a2"))
prevar_cexample2 :: CAction
prevar_cexample2 = (CSPGuard (ZMember (ZTuple [ZVar ("v1",[],[]),ZInt 0]) (ZVar (">",[],[])))  (CSPNSParal [] (CChanSet ["c1","c2"]) [] (CSPGuard (ZMember (ZTuple [ZVar ("v2",[],[]),ZInt 0]) (ZVar (">",[],[])))  (CActionName "a1")) (CActionName "a2")))
prevar_cexample3 :: CAction
prevar_cexample3 = (CActionCommand (CValDecl [Choose ("b",[],[]) (ZSetComp [Choose ("x",[],[]) (ZVar ("BINDING",[],[])),Check (ZAnd (ZMember (ZVar ("time",[],[])) (ZVar ("\\nat",[],[]))) (ZMember (ZVar ("time",[],[])) (ZVar ("\\nat",[],[]))))] Nothing)] (CSPSeq (CActionCommand (CAssign [("sv_SysClock2_time",[],[])] [ZInt 0])) (CSPRecursion "X" (CSPSeq (CSPExtChoice (CSPGuard (ZMember (ZTuple [ZVar ("sv_SysClock2_time",[],[]),ZInt 2]) (ZVar (">",[],[]))) (CSPSeq (CActionCommand (CAssign [("sv_SysClock2_time",[],[])] [ZInt 0])) (CActionName "X"))) (CSPInterleave (CSPCommAction (ChanComm "tick" []) (CActionCommand (CAssign [("sv_SysClock2_time",[],[])] [ZCall (ZVar ("+",[],[])) (ZTuple [ZVar ("sv_SysClock2_time",[],[]),ZInt 1])]))) (CSPCommAction (ChanComm "getCurrentTime" [ChanOutExp (ZVar ("sv_SysClock2_time",[],[]))]) CSPSkip))) (CActionName "X"))))))
prevar_cexample4 :: CAction
prevar_cexample4 = (CActionCommand (CValDecl [Choose ("b",[],[]) (ZSetComp [Choose ("x",[],[]) (ZVar ("BINDING",[],[])),Check (ZAnd (ZMember (ZVar ("time",[],[])) (ZVar ("\\nat",[],[]))) (ZMember (ZVar ("time",[],[])) (ZVar ("\\nat",[],[]))))] Nothing)] (CSPSeq (CActionCommand (CAssign [("sv_SysClock2_time",[],[])] [ZInt 0])) (CSPRecursion "X" (CSPSeq (CSPExtChoice (CSPGuard (ZMember (ZTuple [ZVar ("sv_SysClock2_time",[],[]),ZInt 2]) (ZVar (">",[],[]))) (CSPSeq (CActionCommand (CAssign [("sv_SysClock2_time",[],[])] [ZInt 0])) (CActionName "X"))) (CSPInterleave (CSPCommAction (ChanComm "tick" []) (CActionCommand (CAssign [("sv_SysClock2_time",[],[])] [ZCall (ZVar ("+",[],[])) (ZTuple [ZVar ("sv_SysClock2_time",[],[]),ZInt 1])]))) (CSPCommAction (ChanComm "getCurrentTime" [ChanOutExp (ZVar ("sv_SysClock2_time",[],[]))]) CSPSkip))) (CActionName "X"))))))
prevar_cexample5 :: CAction
prevar_cexample5= (CSPInterleave (CSPCommAction (ChanComm "tick" []) (CActionCommand (CAssign [("sv_SysClock2_time",[],[])] [ZCall (ZVar ("+",[],[])) (ZTuple [ZVar ("sv_SysClock2_time",[],[]),ZInt 1])]))) (CSPCommAction (ChanComm "getCurrentTime" [ChanOutExp (ZVar ("sv_SysClock2_time",[],[]))]) CSPSkip))
prevar_cexample6 :: CAction
prevar_cexample6 = (CSPSeq (CActionCommand (CVarDecl [Choose ("ms",[],[]) (ZVar ("RANGE",[],[]))] (CSPSeq (CActionCommand (CAssign [("sv_LocWakeUp_sec_U_RAN",[],[])] [ZVar ("ms",[],[])])) (CActionCommand (CAssign [("sv_LocWakeUp_sec_U_RAN",[],[]),("sv_LocWakeUp_min_U_RAN",[],[]),("sv_LocWakeUp_buzz_U_ALA",[],[])] [ZInt 0,ZInt 0,ZVar ("OFF",[],[])]))))) (CSPRecursion "X" (CSPSeq (CSPHide (CSPCommAction (ChanComm "tick" []) (CSPSeq (CActionCommand (CAssign [("sv_LocWakeUp_sec_U_RAN",[],[]),("sv_LocWakeUp_min_U_RAN",[],[])] [ZCall (ZVar ("\\mod",[],[])) (ZTuple [ZCall (ZVar ("+",[],[])) (ZTuple [ZVar ("sv_LocWakeUp_sec_U_RAN",[],[]),ZInt 1]),ZInt 3]),ZVar ("sv_LocWakeUp_min_U_RAN",[],[])])) (CSPExtChoice (CSPExtChoice (CSPExtChoice (CSPExtChoice (CSPGuard (ZEqual (ZVar ("sv_LocWakeUp_sec_U_RAN",[],[])) (ZInt 0)) (CActionCommand (CAssign [("sv_LocWakeUp_min_U_RAN",[],[]),("sv_LocWakeUp_sec_U_RAN",[],[])] [ZCall (ZVar ("\\mod",[],[])) (ZTuple [ZCall (ZVar ("+",[],[])) (ZTuple [ZVar ("sv_LocWakeUp_min_U_RAN",[],[]),ZInt 1]),ZInt 3]),ZVar ("sv_LocWakeUp_sec_U_RAN",[],[])]))) (CSPGuard (ZNot (ZEqual (ZVar ("sv_LocWakeUp_sec_U_RAN",[],[])) (ZInt 0))) CSPSkip)) (CSPGuard (ZEqual (ZVar ("sv_LocWakeUp_min_U_RAN",[],[])) (ZInt 1)) (CSPCommAction (ChanComm "radioOn" []) (CActionCommand (CAssign [("sv_LocWakeUp_buzz_U_ALA",[],[])] [ZVar ("ON",[],[])]))))) (CSPCommAction (ChanComm "time" []) (CSPCommAction (ChanComm "out" [ChanOutExp (ZTuple [ZVar ("sv_LocWakeUp_min_U_RAN",[],[]),ZVar ("sv_LocWakeUp_sec_U_RAN",[],[])])]) CSPSkip))) (CSPCommAction (ChanComm "snooze" []) (CActionCommand (CAssign [("sv_LocWakeUp_buzz_U_ALA",[],[])] [ZVar ("OFF",[],[])])))))) (CChanSet ["tick"])) (CActionName "X"))))

\end{code}}
