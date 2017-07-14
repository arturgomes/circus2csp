%!TEX root = MAIN.tex
\chapter{Circus Refinement Laws}

\ignore{
\begin{code}
{-# OPTIONS -Wall #-} 

module CRL
where
import AST
import OmegaDefs
import Subs
import Data.List hiding (union, intersect)
import Data.Maybe
import Data.Time

\end{code}
}
% law 1
\begin{lawn}[var-exp-par]\sl%ok

    \begin{circus}
        (\circvar\ d:T \circspot A1) \lpar ns1 | cs | ns2 \rpar A2
        \\ = \\
        (\circvar\ d:T \circspot A1 \lpar ns1 | cs | ns2 \rpar A2) %
    \end{circus}%
    \begin{itemize}
        \item From D24.1 -- $\{d,d'\} \cap FV(A2) = \emptyset$
        \item From Oliveira's Thesis: $x \notin FV(A_2) \cup ns_1 \cup ns_2$
    \end{itemize}
  \label{law:var-exp-par}
\end{lawn}
\begin{code}
crl_var_exp_par :: CAction -> Refinement CAction
crl_var_exp_par e@(CSPNSParal ns1 cs ns2 (CActionCommand (CVarDecl [(Choose (d,[]) t)] a1)) a2)
  = Done{orig = Just e, refined = Just ref, proviso = [p1]}
    where 
      ref = (CActionCommand (CVarDecl [(Choose (d,[]) t)] (CSPNSParal ns1 cs ns2 a1 a2)))
      p1 = (ZEqual (ZCall (ZVar ("\\cap",[])) (ZTuple [ZSetDisplay [ZVar (d,[]),ZVar (d,["'"])],ZSetDisplay $ zvar_to_zexpr (free_var_CAction a2)])) (ZVar ("\\emptyset",[])))
crl_var_exp_par _ = None
\end{code}
% law 2
\begin{lawn}[var-exp-par-2]\sl

    \begin{circus}
        (\circvar\ d:T \circspot A1) \lpar ns1 | cs | ns2 \rpar (\circvar\ d:T \circspot A2)
        \\ = \\
        (\circvar\ d:T \circspot A1 \lpar ns1 | cs | ns2 \rpar A2) %
    \end{circus}%
  \label{law:var-exp-par2}
\end{lawn}
\begin{code}
crl_var_exp_par2 :: CAction -> Refinement CAction
crl_var_exp_par2 e@(CSPNSParal ns1 cs ns2
                  (CActionCommand (CVarDecl d1 a1))
                  (CActionCommand (CVarDecl d2 a2)))
  = case (d1 == d2) of
      True -> Done{orig = Just e, refined = Just (CActionCommand (CVarDecl d1
                      (CSPNSParal ns1 cs ns2 a1 a2))),
          proviso = []}
      False -> None
crl_var_exp_par2 _ = None
\end{code}
% law 3
\begin{lawn}[var-exp-rec]\sl
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
crl_var_exp_rec :: CAction -> Refinement CAction
crl_var_exp_rec e@(CSPRecursion mX (CActionCommand (CValDecl [Choose (x,[]) (ZVar (t,[]))] (CSPUnfAction f (CActionName mX1)))))
  = case (mX == mX1) of
      True -> Done{orig = Just e, refined = Just (CActionCommand (CValDecl [Choose (x,[]) (ZVar (t,[]))] (CSPRecursion mX (CSPUnfAction f (CActionName mX))))), proviso=[]}
      False -> None
crl_var_exp_rec _ = None
\end{code}
% law 4
\begin{lawn}[Variable block/Sequence---extension$^*$]\sl
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
crl_variableBlockSequenceExtension :: CAction -> Refinement CAction
crl_variableBlockSequenceExtension
      e@(CSPSeq (CSPSeq a1
            (CActionCommand (CVarDecl [(Choose (x,[]) t)] a2))) a3)
  =  Done{orig = Just e, refined = Just (CActionCommand (CVarDecl [(Choose (x,[]) t)] (CSPSeq (CSPSeq a1 a2) a3))), proviso=[prov]}
  where
    prov = (ZMember (ZSetDisplay [ZVar (x,[])]) (ZCall (ZVar ("\\cup",[])) (ZTuple [ZSetDisplay  $ zvar_to_zexpr (free_var_CAction a1),ZSetDisplay $ zvar_to_zexpr (free_var_CAction a3)])))
crl_variableBlockSequenceExtension
      e@(CSPSeq a1
            (CActionCommand (CVarDecl [(Choose (x,[]) t)] a2)))
  =  Done{orig = Just e, refined = Just (CActionCommand (CVarDecl [(Choose (x,[]) t)] (CSPSeq a1 a2))), proviso=[prov]}
  where
    prov = (ZMember (ZSetDisplay [ZVar (x,[])]) (ZCall (ZVar ("\\cup",[])) (ZTuple [ZSetDisplay  $ zvar_to_zexpr (free_var_CAction a1)])))
crl_variableBlockSequenceExtension _ = None
\end{code}
% law 5 - NOT WORKING AND I DONT KNOW WHY!!!!
% \begin{lawn}[Variable Substitution$^*$]\sl
%    \begin{circus}
%        A(x)
%        \\ = \\
%        \circvar\ y \circspot y \prefixcolon [y'=x] \circseq\ A(y)%
%    \end{circus}%
%    \begin{prov}
%        $y \notin FV(A)$
%    \end{prov}
%  \label{law:variableSubstitution}
% \end{lawn}
% TODO: implement proviso
% \begin{code}
% crl_variableSubstitution (CSPParAction a [ZVar (x,[])]) y
%   =undefined --CVarDecl [(ZVar (y,[]))] (CSPSeq (CActionCommand (CAssumpt [(y)] ZTrue{reason=[]} )))
% \end{code}
% law 6
\begin{lawn}[Variable block introduction$^*$]\sl
   \begin{circus}
       A = \circvar\ x:T \circspot A %
   \end{circus}%
   \begin{prov}
       $x \notin FV(A)$
   \end{prov}
 \label{law:variableBlockIntroduction}
\end{lawn}
\begin{code}
crl_variableBlockIntroduction :: CAction -> ZVar -> ZExpr -> Refinement CAction
crl_variableBlockIntroduction a x t
  =  Done{orig = Just a, refined = Just (CActionCommand (CVarDecl [(Choose x t)] a)),
          proviso=[prov]}
  where
    prov = (ZNot (ZMember (ZVar x) (ZSetDisplay $ zvar_to_zexpr (free_var_CAction a))))
crl_variableBlockIntroduction _ _ _ = None
\end{code}
\begin{code}
crl_variableBlockIntroduction_backwards :: CAction -> Refinement CAction
crl_variableBlockIntroduction_backwards e@(CActionCommand (CVarDecl [(Choose (x,[]) t)] a))
  =  Done{orig = Just e, refined = Just a, proviso = [prov]}
  where
  prov = (ZNot (ZMember (ZVar (x,[])) (ZSetDisplay $ zvar_to_zexpr (free_var_CAction a))))

crl_variableBlockIntroduction_backwards e@(CSPCommAction (ChanComm x f) (CActionCommand (CValDecl [Choose (y,[]) (ZVar (t,[]))] a)))
  =  Done{orig = Just e, refined = Just ref, proviso = [prov]}
  where
    ref = (CActionCommand (CValDecl [Choose (y,[]) (ZVar (t,[]))] (CSPCommAction (ChanComm x f) a)))
    prov = (ZNot (ZMember (ZVar (y,[])) (ZSetDisplay $ zvar_to_zexpr (free_var_CAction (CSPCommAction (ChanComm x f) a)))))
crl_variableBlockIntroduction_backwards _ = None
\end{code}
% law 6
\begin{lawn}[Variable block introduction---2$^*$]\sl
   \begin{circus}
       \circvar\ x:T_1 ; y:T_2 \circspot A  = \circvar\ y:T_2 \circspot A %
   \end{circus}%
   \begin{prov}
       $x \notin FV(A)$
   \end{prov}
 \label{law:variableBlockIntroduction}
\end{lawn}
\begin{code}
crl_variableBlockIntroduction2_backwards e@(CActionCommand (CVarDecl ((Choose (x,[]) t):xs) a))
  =  Done{orig = Just e, refined = Just (CActionCommand (CVarDecl xs a)), proviso = [prov]}
  where
    prov = (ZNot (ZMember (ZVar (x,[])) (ZSetDisplay $ zvar_to_zexpr (free_var_CAction a))))
crl_variableBlockIntroduction2_backwards _ = None
\end{code}
% law 7
\begin{lawn}[join---blocks]\sl
    \begin{circus}
        \circvar\ x:T_1 \circspot \circvar\ y:T_2 \circspot A
        \\ = \\
        \circvar\ x:T_1 ; y:T_2 \circspot A
    \end{circus}%
   
  \label{law:joinBlocks}
\end{lawn}
\begin{code}
crl_joinBlocks :: CAction -> Refinement CAction
crl_joinBlocks e@(CActionCommand (CVarDecl [(Choose x t1)] (CActionCommand (CVarDecl [(Choose y t2)] a))))
  =  Done{orig = Just e, refined = Just (CActionCommand (CVarDecl [(Choose x t1),(Choose y t2)] a)),
          proviso=[]}
crl_joinBlocks _ = None
\end{code}

\begin{lawn}[Sequence unit]\sl
   \begin{circus}
     (A) \Skip \circseq A = A\\ %
     (B) A = A \circseq \Skip %
   \end{circus}
 \label{law:seqSkipUnit}
\end{lawn}
\begin{code}
crl_seqSkipUnit_a :: CAction -> Refinement CAction
crl_seqSkipUnit_a e@(CSPSeq CSPSkip a) =  Done{orig = Just e, refined = Just a, proviso=[]}
crl_seqSkipUnit_a _ = None
crl_seqSkipUnit_b e@(CSPSeq a CSPSkip) =  Done{orig = Just e, refined = Just a, proviso=[]}
crl_seqSkipUnit_b _ = None
-- crl_seqSkipUnit_b :: CAction -> Refinement CAction
-- crl_seqSkipUnit_b a =  Done{orig = Just a, refined = Just (CSPSeq a CSPSkip),proviso=[]}
\end{code}

\begin{lawn}[Recursion unfold]\sl
   \begin{circus}
    \circmu X \circspot F(X)
    \\ = \\
    F(\circmu X \circspot F(X))
   \end{circus}
 \label{law:recUnfold}
\end{lawn}
\begin{code}
crl_recUnfold :: CAction -> Refinement CAction
crl_recUnfold e@(CSPRecursion x1 (CSPUnfAction f (CActionName x2)))
  = case (x1 == x2) of
      True -> Done{orig = Just e, refined = Just (CSPUnfAction f (CSPRecursion x1 (CSPUnfAction f (CActionName x1)))),proviso=[]}
      False -> None
crl_recUnfold _ = None 
\end{code}

% \begin{lawn}[Parallelism composition/External choice---expansion$^*$]\sl
%    \begin{circus}
%        (\Extchoice i \circspot a_i \then A_i) \lpar ns1 | cs | ns2 \rpar (\Extchoice j \circspot b_j \then B_j)
%        \\ = \\
%        (\Extchoice i \circspot a_i \then A_i) \lpar ns1 | cs | ns2 \rpar ((\Extchoice j \circspot b_j \then B_j) \extchoice (c \then C)) \\ %
%    \end{circus}%
%    \begin{provs}
%        \item $\bigcup_i \{ a_i \} \subseteq cs$
%        \item $c \in cs$ %
%        \item $c \notin \bigcup_i \{ a_i \} $%
%        \item $c \notin \bigcup_j \{ b_j \}$%
%    \end{provs}
%  \label{law:parallelismExternalChoiceExpansion}
% \end{lawn}
% TODO: implement proviso
% \begin{code}
% crl_parallelismExternalChoiceExpansion :: CAction -> Comm -> CAction -> Refinement CAction
% crl_parallelismExternalChoiceExpansion
%   (CSPNSParal ns1 cs ns2
%       (CSPRepExtChoice i (CSPCommAction ai aAi))
%       (CSPRepExtChoice j (CSPCommAction bj aBj))) c aC
%   = Just (CSPNSParal ns1 cs ns2
%       (CSPRepExtChoice i (CSPCommAction ai aAi))
%       (CSPExtChoice (CSPRepExtChoice j
%           (CSPCommAction bj aBj))
%       (CSPCommAction c aC)))
% crl_parallelismExternalChoiceExpansion _ _ _ = None
% \end{code}

\begin{lawn}[Parallelism composition introduction 1$^*$]\sl
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
        \item $c \notin usedC(A)$
        \item $wrtV(A) \subseteq ns1$
    \end{provs}
  \label{law:parallelismIntroduction1}
\end{lawn}
\begin{code}
crl_parallelismIntroduction1b :: CAction -> NSExp -> [ZName] -> NSExp -> Refinement CAction
crl_parallelismIntroduction1b
  ei@(CSPCommAction (ChanComm c
      [ChanDotExp e]) a)
      (NSExprMult ns1) cs (NSExprMult ns2)
  =  Done{orig = Just ei, 
          refined = Just (CSPNSParal (NSExprMult ns1) (CChanSet cs) (NSExprMult ns2)
                (CSPCommAction (ChanComm c [ChanDotExp e]) a)
                (CSPCommAction (ChanComm c [ChanDotExp e]) CSPSkip)),
          proviso=[p1,p2]} 
    where
      p1 = (ZNot (ZMember (ZVar (c,[])) (ZTuple [ZSetDisplay (usedC a)])))
      p2 = (ZMember (ZTuple [ZSetDisplay (getWrtV a),ZSetDisplay $ zname_to_zexpr ns1]) (ZVar ("\\subseteq",[])))
crl_parallelismIntroduction1b _ _ _ _ = None

crl_parallelismIntroduction1a :: CAction -> NSExp -> [ZName] -> NSExp -> Refinement CAction
crl_parallelismIntroduction1a
    ei@(CSPCommAction (ChanComm c e) a)
        (NSExprMult ns1) cs (NSExprMult ns2)
  =  Done{orig = Just ei, refined = Just (CSPNSParal (NSExprMult ns1) (CChanSet cs) (NSExprMult ns2)
                  (CSPCommAction (ChanComm c e) a)
                  (CSPCommAction (ChanComm c e) CSPSkip)),proviso=[p1,p2]} 
    where
      p1 = (ZNot (ZMember (ZVar (c,[]))  (ZTuple [ZSetDisplay (usedC a)])))
      p2 = (ZMember (ZTuple [ZSetDisplay (getWrtV a),ZSetDisplay $ zname_to_zexpr ns1]) (ZVar ("\\subseteq",[])))
crl_parallelismIntroduction1a _ _ _ _ = None
\end{code}
% \begin{code}
% crl_parallelismIntroduction1b_backwards :: CAction -> Refinement CAction
% crl_parallelismIntroduction1b_backwards
%   e@(CSPNSParal (NSExprMult ns1) (CChanSet cs) (NSExprMult ns2)
%                 (CSPCommAction (ChanComm c1 [ChanDotExp e1]) a)
%                 (CSPCommAction (ChanComm c2 [ChanDotExp e2]) CSPSkip))
%   = case (c1 == c2) && (e1 == e2) of
%       True -> Done{orig = Just e, refined = Just (CSPCommAction (ChanComm c1 [ChanDotExp e1]) a),
%                     proviso=[p1,p2]} 
%       False -> None
%     where
%       p1 = (ZNot (ZMember (ZVar (c1,[])) (ZTuple [ZSetDisplay (usedC a)])))
%       p2 = (ZMember (ZTuple [ZSetDisplay (getWrtV a),ZSetDisplay $ zname_to_zexpr ns1]) (ZVar ("\\subseteq",[])))
% crl_parallelismIntroduction1b_backwards _ = None

% crl_parallelismIntroduction1a_backwards :: CAction -> Refinement CAction
% crl_parallelismIntroduction1a_backwards
%     e@(CSPNSParal (NSExprMult ns1) (CChanSet cs) (NSExprMult ns2)
%                   (CSPCommAction (ChanComm c1 []) a)
%                   (CSPCommAction (ChanComm c2 []) CSPSkip))
%   = case (c1 == c2) of
%       True -> Done{orig = Just e, refined = Just (CSPCommAction (ChanComm c1 []) a),
%                     proviso=[p1,p2]} 
%       False -> None
%     where
%       p1 = (ZNot (ZMember (ZVar (c1,[])) (ZTuple [ZSetDisplay (usedC a)])))
%       p2 = (ZMember (ZTuple [ZSetDisplay (getWrtV a),ZSetDisplay $ zname_to_zexpr ns1]) (ZVar ("\\subseteq",[])))
% crl_parallelismIntroduction1a_backwards _ = None
% \end{code}
\begin{lawn}[Channel extension 1]\sl\label{law:chanExt1}
    \begin{zed}
      A1 \lpar ns1 | cs | ns2 \rpar A2
      \\ = \\
      A1 \lpar ns1 | cs \cup \lchanset c \rchanset | ns2 \rpar A2%
    \end{zed}
    \begin{prov}
      $c \notin usedC(A1) \cup usedC(A2)$
    \end{prov}
\end{lawn}
\begin{code}
crl_chanExt1 :: CAction -> ZName -> Refinement CAction
crl_chanExt1 e@(CSPNSParal ns1 (CChanSet cs) ns2 a1 a2) c
  =  Done{orig = Just e, refined = Just (CSPNSParal ns1 (ChanSetUnion
                    (CChanSet cs) (CChanSet [c])) ns2 a1 a2),
                    proviso=[p1]}
    where
      p1 = (ZNot (ZMember (ZVar (c,[])) (ZCall (ZVar ("\\cup",[])) (ZTuple [ZSetDisplay (usedC a1),ZSetDisplay (usedC a2)]))))
crl_chanExt1 _ _ = None
\end{code}
% Law 13 (Hiding expansion 2$^*$)
\begin{lawn}[Hiding expansion 2$^*$]\sl
    \begin{zed}
      A \circhide cs
      \\ = \\
      A \circhide (cs \cup \lchanset c \rchanset)
    \end{zed}
    \begin{prov} $c \notin usedC(A)$ \end{prov}
  \label{law:hidingExpansion2}
\end{lawn}
\begin{code}
crl_hidingExpansion2 :: CAction -> ZName -> Refinement CAction
crl_hidingExpansion2 e@(CSPHide a (CChanSet cs)) c
  = Done{orig = Just e, refined = Just (CSPHide a (ChanSetUnion (CChanSet cs) (CChanSet [c]))),
                    proviso=[p1]}
    where
      p1 = (ZNot (ZMember (ZVar (c,[])) (ZSetDisplay (usedC a))))
crl_hidingExpansion2 _ _ = None
\end{code}
% Law 14 (Prefix/Hiding$^*$)
\begin{lawn}[Prefix/Hiding$^*$]\sl
    \begin{circus}
        (c \then Skip) \circhide \lchanset c \rchanset = \Skip%
        \also
        (c.e \then Skip) \circhide \lchanset c \rchanset = \Skip%
    \end{circus}%
 \label{law:prefixHiding}
\end{lawn}
\begin{code}
crl_prefixHiding :: CAction -> Refinement CAction
crl_prefixHiding
  e@(CSPHide (CSPCommAction (ChanComm c _) CSPSkip) (CChanSet [c1]))
  = case (c == c1) of
      True        -> Done{orig = Just e, refined = Just CSPSkip,proviso=[]}
      otherwise   -> None
crl_prefixHiding _ = None
\end{code}
% Law 15 (Hiding Identity$^*$)
\begin{lawn}[Hiding Identity$^*$]\sl

    \begin{circus}
      A \circhide cs = A
    \end{circus}
    \begin{prov} $cs \cap usedC(A) = \emptyset$ \end{prov}

  \label{law:hidingIdentity}
\end{lawn}
\begin{code}
crl_hidingIdentity :: CAction -> Refinement CAction
crl_hidingIdentity e@(CSPHide a (CChanSet cs))
  = Done{orig = Just e, refined = Just a, proviso=[p1]}
    where
      p1 = (ZEqual (ZCall (ZVar ("\\cap",[])) (ZTuple [ZSetDisplay $zname_to_zexpr cs,ZSetDisplay (usedC a)])) (ZVar ("\\emptyset",[])))
crl_hidingIdentity _ = None
\end{code}
% Law 16 (Parallelism composition/External choice---exchange)
\begin{lawn}[Parallelism composition/External choice---exchange]\sl\label{law:parExtChoiceExchange}
    \begin{circus}
      (A1 \lpar ns1 | cs | ns2 \rpar A2) \extchoice (B1 \lpar ns1 | cs | ns2 \rpar B2)
      \\ = \\
      (A1 \extchoice B1) \lpar ns1 | cs | ns2\rpar (A2 \extchoice B2)
    \end{circus}
    \begin{prov} $A1 \lpar ns1 | cs | ns2 \rpar B2 = A2 \lpar ns1 | cs | ns2 \rpar B1 = Stop$
    \end{prov}
\end{lawn}
\begin{code}
crl_parExtChoiceExchange :: CAction -> Refinement CAction
crl_parExtChoiceExchange
    e@(CSPExtChoice
      (CSPNSParal ns1 cs ns2 a1 a2)
      (CSPNSParal ns11 cs1 ns21 b1 b2))
  = case pred of
      True ->  Done{orig = Just e, refined = Just ref, proviso=[]}
      False -> None
      where 
        astop = (CSPNSParal ns1 cs ns2 a1 b2) == (CSPNSParal ns2 cs ns1 a2 b1)
        ref = (CSPNSParal ns1 cs ns2
                  (CSPExtChoice a1 b1)
                  (CSPExtChoice a2 b2))
        pred = (ns1 == ns11 && cs1 == cs && ns2 == ns21) && astop
crl_parExtChoiceExchange _ = None
\end{code}
% Law 17 (Parallelism composition/External choice---distribution$^*$)
% \begin{lawn}[Parallelism composition/External choice---distribution$^*$]\sl

%   \begin{circus}
%       \Extchoice i \circspot (A_i \lpar ns1 | cs | ns2 \rpar A)
%       \\ = \\
%       (\Extchoice i \circspot A_i) \lpar ns1 | cs | ns2 \rpar A
%   \end{circus}%
%   \begin{provs}
%       \item $initials(A) \subseteq cs$ %
%       \item $A$ is deterministic %
%   \end{provs}
% \label{law:parallelismExternalChoiceDistribution}
% \end{lawn}
% \begin{code}
% crl_parallelismExternalChoiceDistribution :: CAction -> Refinement CAction
% crl_parallelismExternalChoiceDistribution
%     (CSPRepExtChoice i (CSPNSParal ns1 (CChanSet cs) ns2 ai a))
%   = case p1 && p2 of
%       True  -> Just (CSPNSParal ns1
%                   (CChanSet cs) ns2 (CSPRepExtChoice i ai) a)
%       False -> None
%     where
%       p1 = (subset (initials a) cs)
%       p2 = isJust (deterministic a)
% crl_parallelismExternalChoiceDistribution _ = None
% \end{code}
% Law 18 (External choice unit)
\begin{lawn}[External choice unit]\sl
    \begin{circus}
      Stop \extchoice A = A
    \end{circus}
  \label{law:extChoiceStopUnit}
\end{lawn}

\begin{code}
crl_extChoiceStopUnit :: CAction -> Refinement CAction
crl_extChoiceStopUnit e@(CSPExtChoice CSPStop a) 
  = Done{orig = Just e, refined = Just a,proviso=[]}
crl_extChoiceStopUnit _ 
  = None

\end{code}
% Law 19 (External choice/Sequence---distribution)
% \begin{lawn}[External choice/Sequence---distribution]\
%     \begin{circus}
%       (\Extchoice\ i \circspot g_i \circguard c_i \then A_i)\circseq B
%       \\ = \\
%       \Extchoice\ i \circspot g_i \circguard c_i \then A_i\circseq B%
%     \end{circus}
%   \label{law:extChoiceSeqDist}
% \end{lawn}
% \begin{code}
% crl_extChoiceSeqDist :: CAction -> Refinement CAction
% crl_extChoiceSeqDist (CSPSeq (CSPRepExtChoice i
%                         (CSPGuard gi (CSPCommAction ci ai))) b)
%   = Just (CSPRepExtChoice i (CSPSeq
%           (CSPGuard gi (CSPCommAction ci ai)) b))
% crl_extChoiceSeqDist _ = None
% \end{code}
% Law 20 (Hiding/External choice---distribution$^*$)
\begin{lawn}[Hiding/External choice---distribution$^*$]\sl
    \begin{zed}
      (A1 \extchoice A2) \circhide cs
      \\ = \\
      (A1 \circhide cs) \extchoice (A2 \circhide cs)
    \end{zed}
    \begin{prov}
      $(initials(A1) \cup initials(A2)) \cap cs = \emptyset$
    \end{prov}
  \label{law:hidingExternalChoiceDistribution}
\end{lawn}
\begin{code}
crl_hidingExternalChoiceDistribution :: CAction -> Refinement CAction
crl_hidingExternalChoiceDistribution
    e@(CSPHide (CSPExtChoice a1 a2) (CChanSet cs))
  = Done{orig = Just e, refined = Just ref, proviso=[p1]}
    where
      p1 = (ZEqual (ZCall (ZVar ("\\cap",[])) (ZTuple [ZCall (ZVar ("\\cup",[])) (ZTuple [ZSetDisplay (initials a1),ZSetDisplay (initials a1)]),ZSetDisplay (zname_to_zexpr cs)])) (ZVar ("\\emptyset",[])))
      ref = (CSPExtChoice
              (CSPHide a1 (CChanSet cs))
              (CSPHide a2 (CChanSet cs)))


crl_hidingExternalChoiceDistribution _ = None
\end{code}
% Law 21 (Hiding/External choice---distribution$^*$)
\begin{lawn}[Parallelism composition Deadlocked 1$^*$]\sl

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
crl_parallelismDeadlocked1 :: CAction -> Refinement CAction
crl_parallelismDeadlocked1
    e@(CSPNSParal ns1 (CChanSet cs) ns2
          (CSPCommAction (ChanComm c1 x) a1)
          (CSPCommAction (ChanComm c2 y) a2))
  =  Done{orig = Just e, refined = Just ref, proviso=[p1,p2]}
    where
      p1 = ZNot (ZEqual (ZVar (c1,[])) (ZVar (c2,[])))
      p2 = (ZMember (ZTuple [ZSetDisplay [ZVar (c1,[]),ZVar (c2,[])],ZSetDisplay $ zname_to_zexpr cs]) (ZVar ("\\subseteq",[])))
      ref = (CSPNSParal ns1 (CChanSet cs) ns2
              CSPStop
              (CSPCommAction (ChanComm c2 y) a2))
crl_parallelismDeadlocked1 e@(CSPNSParal ns1 (CChanSet cs) ns2
                              CSPStop (CSPCommAction c2 a2))
  = Done{orig = Just e, refined = Just ref, proviso=[]}
    where
      ref = CSPStop
crl_parallelismDeadlocked1 _ = None

\end{code}
% Law 22 (Sequence zero)
\begin{lawn}[Sequence zero]\sl
    \begin{circus}
      \Stop \circseq A = \Stop
    \end{circus}
  \label{law:seqStopZero}
\end{lawn}
\begin{code}
crl_seqStopZero :: CAction -> Refinement CAction
crl_seqStopZero e@(CSPSeq CSPStop a)
  =  Done{orig = Just e, refined = Just CSPStop,proviso=[]}
crl_seqStopZero _ = None
\end{code}
% Law 23 (Communication/Parallelism composition---distribution)
\begin{lawn}[Communication/Parallelism composition---distribution]\sl
    \begin{circus}
      (c!e \then A1) \lpar ns1 | cs | ns2 \rpar (c?x \then A2(x))
      \\ = \\
      c.e \then (A1 \lpar ns1 | cs | ns2 \rpar A2(e)) %
    \end{circus}
    \begin{provs}
        \item $c \in cs$
        \item $x \notin FV(A2)$.
    \end{provs}
TODO: implement proviso

  \label{law:communicationParallelismDistribution}
\end{lawn}
\begin{code}
crl_communicationParallelismDistribution :: CAction -> Refinement CAction
crl_communicationParallelismDistribution
    ei@(CSPNSParal ns1 (CChanSet cs) ns2
        (CSPCommAction (ChanComm c [ChanOutExp e]) a1)
        (CSPCommAction (ChanComm c1 [ChanInp x1])
          (CSPParAction a2 [ZVar (x,[])])))
  = case pred of
      True  -> Done{orig = Just ei, refined = Just ref, proviso=[p1,p2]}
      False -> None
    where
       p1 = (ZNot (ZMember (ZVar (c,[])) (ZSetDisplay $ zname_to_zexpr cs)))
       p2 = (ZNot (ZMember (ZVar (x,[])) (ZSetDisplay $ zvar_to_zexpr(free_var_CAction (CSPParAction a2 [ZVar (x,[])])))))
       ref = (CSPCommAction (ChanComm c [ChanDotExp e])
                    (CSPNSParal ns1 (CChanSet cs) ns2 a1 (CSPParAction a2 [e])))
       pred = (c == c1 && x == x1)
crl_communicationParallelismDistribution _ = None
\end{code}
% Law 24 (Channel extension 3$^*$)
\begin{lawn}[Channel extension 3$^*$]\sl
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
TODO: implement proviso
\end{lawn}
\begin{code}
crl_channelExtension3 ei@(CSPHide 
          (CSPNSParal ns1 (CChanSet cs1) ns2 a1 (CActionCommand (CVarDecl [Choose (e,[]) t1] mact))) (CChanSet cs2)) c x
  =  Done{orig = Just ei, refined = Just ref, proviso=[p1,p2,p3]}
    where
      p1 = (ZNot (ZMember (ZVar (c,[])) (ZSetDisplay $ zname_to_zexpr cs1)))
      p2 = (ZNot (ZMember (ZVar (c,[])) (ZSetDisplay $ zname_to_zexpr cs2)))
      p3 = (ZNot (ZMember (ZVar (x,[])) (ZSetDisplay $ zvar_to_zexpr(free_var_CAction (CActionCommand (CVarDecl [Choose (e,[]) t1] mact))))))
      ref = (CSPHide 
                (CSPNSParal ns1 (CChanSet cs1) ns2 
                    (CSPCommAction (ChanComm c [ChanOutExp (ZVar (e,[]))]) a1) 
                    (CSPCommAction (ChanComm c [ChanInp x]) 
                        (CActionCommand (CVarDecl [Choose (x,[]) t1] mact)))) 
                (CChanSet cs2))
crl_channelExtension3 _ _ _= None
\end{code}
\begin{code}
crl_channelExtension3_backwards ei@(CSPHide (CSPNSParal ns1 (CChanSet cs1) ns2 (CSPCommAction (ChanComm c2 [ChanOutExp (e)]) a1) (CSPCommAction (ChanComm c1 [ChanInp x]) (CSPParAction a2 [ZVar (x1,[])]))) (CChanSet cs2))
  = case pred of
      True -> Done{orig = Just ei, refined = Just ref, proviso=[p1,p2,p3]} 
      False -> None
    where
       p1 = (ZNot (ZMember (ZVar (c1,[])) (ZSetDisplay $ zname_to_zexpr cs1)))
       p2 = (ZNot (ZMember (ZVar (c2,[])) (ZSetDisplay $ zname_to_zexpr cs2)))
       p3 = (ZNot (ZMember (ZVar (x,[])) (ZSetDisplay $ zvar_to_zexpr(free_var_CAction (CSPParAction a2 [e])))))
       pred = (c1 == c2) && (x == x1)
       ref = (CSPHide (CSPNSParal ns1 (CChanSet cs1) ns2 a1 (CSPParAction a2 [e])) (CChanSet cs2))
crl_channelExtension3_backwards _ = None
\end{code}
% Law 25 (Channel extension 4$^*$)
\begin{lawn}[Channel extension 4$^*$]\sl
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
crl_channelExtension4 ei@(CSPHide (CSPNSParal ns1 (CChanSet cs1) ns2 a1 a2) (CChanSet cs2)) (ChanComm c [ChanOutExp (e)])
  =  Done{orig = Just ei, refined = Just ref, proviso=[p1,p2]}
    where
       p1 = (ZNot (ZMember (ZVar (c,[])) (ZSetDisplay $ zname_to_zexpr cs1)))
       p2 = (ZNot (ZMember (ZVar (c,[])) (ZSetDisplay $ zname_to_zexpr cs2)))
       ref = (CSPHide (CSPNSParal ns1 (CChanSet cs1) ns2 (CSPCommAction (ChanComm c [ChanOutExp (e)]) a1) (CSPCommAction (ChanComm c [ChanOutExp (e)]) a2)) (CChanSet cs2))
crl_channelExtension4 ei@(CSPHide (CSPNSParal ns1 (CChanSet cs1) ns2 a1 a2)
                                (CChanSet cs2)) (ChanComm c e)
  = Done{orig = Just ei, refined = Just ref, proviso=[p1,p2]} 
    where
      p1 = (ZNot (ZMember (ZVar (c,[])) (ZSetDisplay $ zname_to_zexpr cs1)))
      p2 = (ZNot (ZMember (ZVar (c,[])) (ZSetDisplay $ zname_to_zexpr cs2)))
      ref = (CSPHide (CSPNSParal ns1 (CChanSet cs1) ns2
                          (CSPCommAction (ChanComm c e) a1)
                           (CSPCommAction (ChanComm c e) a2))
                        (CChanSet cs2))
crl_channelExtension4 _ _ = None
\end{code}
Law 26 (prom-var-state)
\begin{code}
crl_promVarState :: CProc -> Refinement CProc
crl_promVarState
  e@(ProcMain 
      (ZSchemaDef (ZSPlain st) s) 
      [CParAction l (CircusAction (CActionCommand (CValDecl [Choose (x,[]) (ZVar (t,[]))] a)))] 
      (CActionCommand (CValDecl [Choose (x1,[]) (ZVar (t1,[]))] ma)))
  = case (x==x1 && t == t1) of
        True -> Done{orig = Just e, refined = Just ref, proviso=[]}
        False -> None
    where
      ref = (ProcMain 
                  (ZSchemaDef (ZSPlain st) (ZS2 ZSAnd s (ZSchema [Choose (x,[]) (ZVar (t,[]))]))) 
                  [CParAction l (CircusAction a)] ma)

crl_promVarState _ = None
\end{code}
Law 27 (prom-var-state-2)
\begin{code}
crl_promVarState2 :: CProc -> ZSName -> Refinement CProc
crl_promVarState2
    e@(ProcStalessMain
      [CParAction lact (ParamActionDecl [(Choose v t)] act)]
      (CActionCommand (CVarDecl [Choose v1 t1] mact))) st
  = case (v==v1 && t == t1) of
      True -> Done{orig = Just e, refined = Just ref, proviso=[]}
      False -> None
      where
        ref = (ProcMain (ZSchemaDef st (ZSchema [Choose v1 t1]))
                [CParAction lact act] mact)
crl_promVarState2
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
\end{code}
\begin{lawn}[Parallelism composition unit$^*$]\sl
    \begin{circus}
        \Skip \lpar ns1 | cs | ns2 \rpar \Skip = \Skip
    \end{circus}%
  \label{law:parallelismUnit1}
\end{lawn}
\begin{code}
crl_parallelismUnit1 :: CAction -> Refinement CAction
crl_parallelismUnit1 e@(CSPNSParal _ _ _ CSPSkip CSPSkip) 
  =  Done{orig = Just e, refined = Just CSPSkip, proviso=[]}
crl_parallelismUnit1 _ = None
\end{code}

\begin{lawn}[Parallelism composition/Interleaving Equivalence$^*$]\sl
    \begin{circus}
      A1 \linter ns2 | ns2 \rinter A2
      \\ = \\
      A1 \lpar ns2 | \emptyset | ns2 \rpar A2%
    \end{circus}%
  \label{law:parallelism-interleaving-equivalence}
\end{lawn}

\begin{code}
crl_parallInterlEquiv :: CAction -> Refinement CAction
crl_parallInterlEquiv e@(CSPNSInter ns1 ns2 a1 a2)
  =  Done{orig = Just e, refined = Just ref, proviso=[]}
    where 
      ref = (CSPNSParal ns1 CSEmpty ns2 a1 a2)
crl_parallInterlEquiv _ = None
-- crl_parallInterlEquiv_backwards :: CAction -> Refinement CAction
-- crl_parallInterlEquiv_backwards e@(CSPNSParal ns1 CSEmpty ns2 a1 a2)
--   = Done{orig = Just e, refined = Just ref, proviso=[]}
--     where 
--       ref = (CSPNSInter ns1 ns2 a1 a2)
-- crl_parallInterlEquiv_backwards _ = None
\end{code}
% \begin{lawn}[Parallelism composition/Sequence---step$^*$]\sl
% \label{law:parSeqStep}
%   \begin{circus}
%     (A1\circseq A2) \lpar ns1 | cs | ns_ 2 \rpar A3
%     \\ = \\
%     A1\circseq (A2 \lpar ns_ 1 | cs | ns2 \rpar A3)%
%   \end{circus}
%     \begin{provs}
%       \item $initials(A3) \subseteq cs$
%       \item $cs \cap usedC(A1) = \emptyset$
%       \item $wrtV(A1) \cap usedV(A3) = \emptyset$
%         \item $A3$ is divergence-free
%       \item $wrtV(A1) \subseteq ns1$
%     \end{provs}
% \end{lawn}
% TODO: implement proviso

% \begin{code}
% crl_parSeqStep :: CAction -> Refinement CAction
% crl_parSeqStep (CSPNSParal ns1 cs ns2 (CSPSeq a1 a2) a3)
%     = Just (CSPSeq a1 (CSPNSParal ns1 cs ns2 a2 a3))
%     where
%       p1 = (subset (initials a3) cs)
%       p2 = null $ cs `intersect` (usedC a1)
%       p3 = null $ (wrtV a1) `intersect` (wrtV a3)
%       p4 = True -- a3 is divergence-free -- implement that!!
%       p5 = (subset (wrtV a1) cs)
%       pred = p1 && p2 && p3 && p4 && p5
% crl_parSeqStep _ = None
% \end{code}

\begin{lawn}[Hiding/Sequence---distribution$^*$]\sl
    \begin{circus}
      (A1 \circseq\ A2) \circhide cs
      \\ = \\
      (A1 \circhide cs) \circseq\ (A2 \circhide cs)
    \end{circus}
  \label{law:hidingSequenceDistribution}
\end{lawn}

\begin{code}
crl_hidingSequenceDistribution :: CAction -> Refinement CAction
crl_hidingSequenceDistribution e@(CSPHide (CSPSeq a1 a2) cs)
    = Done{orig = Just e, refined = Just ref, proviso=[]}
    where 
      ref = (CSPSeq (CSPHide a1 cs) (CSPHide a2 cs))
crl_hidingSequenceDistribution _ = None
\end{code}

\begin{lawn}[Guard/Sequence---associativity]\sl
    \begin{circus}
      (g \circguard A1)\circseq A2
      \\ = \\
      g \circguard (A1\circseq A2)
    \end{circus}
  \label{law:guardSeqAssoc}
\end{lawn}

\begin{code}
crl_guardSeqAssoc :: CAction -> Refinement CAction
crl_guardSeqAssoc e@(CSPSeq (CSPGuard g a1) a2) 
  = Done{orig = Just e, refined = Just ref, proviso=[]}
    where ref = (CSPGuard g (CSPSeq a1 a2))
crl_guardSeqAssoc _ = None
\end{code}

\begin{lawn}[Input prefix/Parallelism composition---distribution 2$^*$]\sl
    \begin{circus}
        c?x \then (A1 \lpar ns1 | cs | ns2 \rpar A2) %
        \\ = \\
        (c?x \then A1) \lpar ns1 | cs | ns2 \rpar A2%
    \end{circus}%
    \begin{provs}
        \item $c \notin cs$%
        \item $x \notin usedV(A2)$
        \item $initials(A2) \subseteq cs$
        \item $A2$ is deterministic
    \end{provs}
  \label{law:inputPrefixParallelismDistribution2}
\end{lawn}
TODO: implement proviso

\begin{code}
crl_inputPrefixParallelismDistribution2 :: CAction -> Refinement CAction
crl_inputPrefixParallelismDistribution2
      e@(CSPCommAction (ChanComm c [ChanInp x])
          (CSPNSParal ns1 (CChanSet cs) ns2 a1 a2))
  = Done{orig = Just e, refined = Just ref, proviso=[p1,p2,p3]}
    where
      ref = (CSPNSParal ns1 (CChanSet cs) ns2 (CSPCommAction (ChanComm c [ChanInp x]) a1) a2)
      p1 = (ZNot (ZMember (ZVar (c,[])) (ZSetDisplay $ zname_to_zexpr cs)))
      p2 = (ZNot (ZMember (ZVar (c,[])) (ZSetDisplay $ zname_to_zexpr(usedV a2))))
      p3 = (ZMember (ZTuple [ZSetDisplay (initials a2),ZSetDisplay (zname_to_zexpr cs)]) (ZVar ("\\subseteq",[])))
      p4 = "a2 is deterministic"
crl_inputPrefixParallelismDistribution2 _ = None
\end{code}
% Law 34 (Prefix/$Skip$$^*$)
\begin{lawn}[Prefix/$Skip$$^*$]\sl
    \begin{circus}
        c \then A = (c \then \Skip) \circseq\ A
        \also
        c.e \then A = (c.e \then \Skip) \circseq\ A
    \end{circus}%

  \label{law:prefixSkip}
\end{lawn}
\begin{code}

-- crl_prefixSkip :: CAction -> Refinement CAction
-- crl_prefixSkip e@(CSPCommAction (ChanComm c [ChanDotExp x]) a)
--   = Done{orig = Just e, refined = Just ref, proviso=[]}
--     where
--       ref = (CSPSeq (CSPCommAction
--               (ChanComm c [ChanDotExp x]) CSPSkip) a)
-- crl_prefixSkip e@(CSPCommAction c a)
--   = Done{orig = Just e, refined = Just ref, proviso=[]}
--     where
--       ref = (CSPSeq (CSPCommAction c CSPSkip) a)
-- crl_prefixSkip _ = None

-- 9/04/18
-- I had to make these two auxiliary functions in order to
-- put the crl_prefixSkip_backwards function working properly.
-- Basically, it searches for a CSPSkip within a prefixed action
-- and then removes the CSPSkip replacing it with a2, the RHS of 
-- a CSPSeq action.
endPrefWithSkip (CSPCommAction c CSPSkip) = True
endPrefWithSkip (CSPCommAction c c1) = endPrefWithSkip c1
endPrefWithSkip _ = False

remPrefSkip a2 (CSPCommAction c CSPSkip) = (CSPCommAction c a2)
remPrefSkip a2 (CSPCommAction c c1) = (CSPCommAction c (remPrefSkip a2 c1))

crl_prefixSkip_backwards :: CAction -> Refinement CAction
crl_prefixSkip_backwards e@(CSPSeq (CSPCommAction (ChanComm c [ChanDotExp x]) CSPSkip) a)
  = Done{orig = Just e, refined = Just ref, proviso=[]}
    where
      ref = (CSPCommAction (ChanComm c [ChanDotExp x]) a)
crl_prefixSkip_backwards e@(CSPSeq a1 a2)
  | endPrefWithSkip a1 
      = Done{orig = Just e, refined = Just ref, proviso=[]}
  | otherwise = None
    where
      ref = remPrefSkip a2 a1
crl_prefixSkip_backwards _ = None
\end{code}
\begin{lawn}[Prefix/Parallelism composition---distribution]\sl
    \begin{circus}
      c \then (A1 \lpar ns1 | cs | ns2 \rpar A2)
      \\ = \\
      (c \then A1) \lpar ns1 | cs \cup \lchanset c \rchanset | ns2 \rpar (c \then A2)%
      \also
      c.e \then (A1 \lpar ns1 | cs | ns2 \rpar A2)
      \\ = \\
      (c.e \then A1) \lpar ns1 | cs \cup \lchanset c \rchanset | ns2 \rpar (c.e \then A2)%
    \end{circus}
    \begin{prov} $c \notin usedC(A1) \cup usedC(A2)$ or $c \in cs$
    \end{prov}
  \label{law:prefixParDist}
\end{lawn}
\begin{code}
crl_prefixParDist :: CAction -> Refinement CAction
crl_prefixParDist e@(CSPCommAction (ChanComm c [])
                    (CSPNSParal ns1 (CChanSet cs) ns2 a1 a2))
  = Done{orig = Just e, refined = Just ref, proviso=[ZAnd p1 p2]}
    where
      ref = (CSPNSParal
                    ns1 (ChanSetUnion (CChanSet cs) (CChanSet [c])) ns2
                    (CSPCommAction (ChanComm c []) a1)
                    (CSPCommAction (ChanComm c []) a2))
      p1 = (ZNot (ZMember (ZVar (c,[])) (ZCall (ZVar ("\\cup",[])) (ZTuple [ZSetDisplay $ zvar_to_zexpr(free_var_CAction a1),ZSetDisplay $ zvar_to_zexpr (free_var_CAction a2)]))))
      p2 = (ZMember (ZVar (c,[])) (ZSetDisplay $ zname_to_zexpr cs))
crl_prefixParDist ei@(CSPCommAction (ChanComm c [ChanDotExp e])
                    (CSPNSParal ns1 (CChanSet cs) ns2 a1 a2))
 = Done{orig = Just ei, refined = Just ref, proviso=[ZAnd p1 p2]}
    where
      ref = (CSPNSParal ns1 (ChanSetUnion (CChanSet cs) (CChanSet [c])) ns2 
                    (CSPCommAction (ChanComm c [ChanDotExp e]) a1) 
                    (CSPCommAction (ChanComm c [ChanDotExp e]) a2))
      p1 = (ZNot (ZMember (ZVar (c,[])) (ZCall (ZVar ("\\cup",[])) (ZTuple [ZSetDisplay $ zvar_to_zexpr(free_var_CAction a1),ZSetDisplay $ zvar_to_zexpr(free_var_CAction a2)]))))
      p2 = (ZMember (ZVar (c,[])) (ZSetDisplay $ zname_to_zexpr cs))
crl_prefixParDist _ = None
\end{code}
% Law 36 (External choice/Sequence---distribution 2$^*$)
\begin{lawn}[External choice/Sequence---distribution 2$^*$]\sl
    \begin{circus}
      ((g1 \circguard A1) \extchoice (g2 \circguard A2))\circseq B
      \\ = \\
      ((g1 \circguard A1) \circseq B) \extchoice ((g2 \circguard A2) \circseq B)%
    \end{circus}
    \begin{prov} $g1 \implies \lnot g2$ \end{prov}
  \label{law:externalChoiceSequenceDistribution2}
\end{lawn}
TODO: implement proviso
\begin{code}
crl_externalChoiceSequenceDistribution2 :: CAction -> Refinement CAction
crl_externalChoiceSequenceDistribution2
      e@(CSPSeq (CSPExtChoice (CSPGuard g1 a1) (CSPGuard g2 a2)) b)
  = Done{orig = Just e, refined = Just ref, proviso=[]}
    where
      ref = (CSPExtChoice (CSPSeq (CSPGuard g1 a1) b)
                  (CSPSeq (CSPGuard g2 a2) b))
crl_externalChoiceSequenceDistribution2 _ = None
\end{code}
% Law 37 (True guard)
\begin{lawn}[True guard]\sl
    \begin{circus}
      \true \circguard A = A
    \end{circus}
  \label{law:trueGuard}
\end{lawn}
\begin{code}
crl_trueGuard :: CAction -> Refinement CAction
crl_trueGuard e@(CSPGuard ZTrue{reason=[]} a)
  = Done{orig = Just e, refined = Just ref, proviso=[]}
    where
      ref = a
crl_trueGuard _ = None
\end{code}
% Law 38 (False guard)
\begin{lawn}[False guard]\sl
    \begin{circus}
      \false \circguard A = \Stop
    \end{circus}
  \label{law:falseGuard}
\end{lawn}
\begin{code}
crl_falseGuard :: CAction -> Refinement CAction
crl_falseGuard e@(CSPGuard ZFalse{reason=[]} _)
  = Done{orig = Just e, refined = Just ref, proviso=[]}
    where
      ref = CSPStop
crl_falseGuard _ = None
\end{code}
% Law 39 (Hiding/$Chaos$---distribution$^*$)
\begin{lawn}[Hiding/$Chaos$---distribution$^*$]\sl
    \begin{circus}
      \Chaos \circhide cs = \Chaos
    \end{circus}
  \label{law:hidingChaos}
\end{lawn}
\begin{code}
crl_hidingChaos :: CAction -> Refinement CAction
crl_hidingChaos e@(CSPHide CSPChaos _)
  = Done{orig = Just e, refined = Just ref, proviso=[]}
    where
      ref = CSPChaos
crl_hidingChaos _ = None
\end{code}
Law 40 (Sequence zero 2$^*$)
\begin{lawn}[Sequence zero 2$^*$]\sl
    \begin{circus}
      \Chaos \circseq A = \Chaos
    \end{circus}
  \label{law:seqChaosZero}
\end{lawn}
\begin{code}
crl_seqChaosZero :: CAction -> Refinement CAction
crl_seqChaosZero e@(CSPSeq CSPChaos _)
  = Done{orig = Just e, refined = Just ref, proviso=[]}
    where
      ref = CSPChaos
crl_seqChaosZero _ = None
\end{code}
Law 41 (Parallelism composition Zero$^*$)
\begin{lawn}[Parallelism composition Zero$^*$]\sl
    \begin{circus}
        Chaos \lpar ns1 | cs | ns2 \rpar A = Chaos%
    \end{circus}%
  \label{law:parallelismZero}
\end{lawn}
\begin{code}
crl_parallelismZero :: CAction -> Refinement CAction
crl_parallelismZero e@(CSPNSParal _ _ _ CSPChaos _)
  = Done{orig = Just e, refined = Just ref, proviso=[]}
    where
      ref = CSPChaos
crl_parallelismZero _ = None
\end{code}
% Law 42 (Internal choice/Parallelism composition Distribution$^*$)
\begin{lawn}[Internal choice/Parallelism composition Distribution$^*$]\sl
    \begin{circus}
      (A1 \intchoice A2) \lpar ns1 | cs | ns2 \rpar A3
      \\ = \\
      (A1 \lpar ns1 | cs | ns2 \rpar A3) \intchoice (A2 \lpar ns1 | cs | ns2 \rpar A3) \\ %
    \end{circus}%
  \label{law:internalChoiceParallelismDistribution}
\end{lawn}
\begin{code}
crl_internalChoiceParallelismDistribution :: CAction -> Refinement CAction
crl_internalChoiceParallelismDistribution e@(CSPNSParal ns1 cs ns2 (CSPIntChoice a1 a2) a3)
  = Done{orig = Just e, refined = Just ref, proviso=[]}
    where
      ref = (CSPIntChoice (CSPNSParal ns1 cs ns2 a1 a3) (CSPNSParal ns1 cs ns2 a2 a3))
crl_internalChoiceParallelismDistribution _ = None
\end{code}
\begin{lawn}[Sequence/Internal choice---distribution$^*$]\sl
    \begin{circus}
        A_1 \Semi\ (A_2 \intchoice A_3) = (A_1 \Semi\ A_2) \intchoice (A_1 \Semi\ A_3)%
    \end{circus}%
  \label{law:sequenceInternalChoiceDistribution}
\end{lawn}
\begin{code}
--Law 43 (Sequence/Internal choice—distribution)
crl_sequenceInternalChoiceDistribution :: CAction -> Refinement CAction
crl_sequenceInternalChoiceDistribution e@(CSPSeq a1 (CSPIntChoice a2 a3))
  = Done{orig = Just e, refined = Just ref, proviso=[]}
    where
      ref = (CSPIntChoice (CSPSeq a1 a2) (CSPSeq a1 a3))
crl_sequenceInternalChoiceDistribution _ = None
\end{code}
% Law 44 (Sequence/Internal choice---distribution$^*$)
\begin{lawn}[Hiding/Parallelism composition---distribution$^*$]\sl
    \begin{zed}
      (A_1 \lpar ns_1 | cs_1 | ns_2 \rpar A_2) \hide cs_2 = (A_1 \hide cs_2) \lpar ns_1 | cs_1 | ns_2 \rpar (A_2 \hide cs_2)
    \end{zed}
    \begin{prov}
        $cs_1 \cap cs_2 = \emptyset$
    \end{prov}
  \label{law:hidingParallelismDistribution}
\end{lawn}
\begin{code}
crl_hidingParallelismDistribution :: CAction -> Refinement CAction
crl_hidingParallelismDistribution
    e@(CSPHide (CSPNSParal ns1 (CChanSet cs1) ns2 a1 a2) (CChanSet cs2))
  = Done{orig = Just e, refined = Just ref, proviso=[prov]}
    where
      ref = (CSPNSParal ns1 (CChanSet cs1) ns2 (CSPHide a1 (CChanSet cs1)) (CSPHide a2 (CChanSet cs2)))
      prov = (ZEqual (ZCall (ZVar ("\\cap",[])) (ZTuple [ZSetDisplay $ zname_to_zexpr cs1,ZSetDisplay $ zname_to_zexpr cs2])) (ZVar ("\\emptyset",[])))
crl_hidingParallelismDistribution _ = None 
\end{code}
% Law 45 (Hiding combination)
\begin{lawn}[Hiding combination]\sl
    \begin{circus}
      (A \circhide cs1) \circhide cs2
      \\ = \\
      A \circhide (cs1 \cup cs2)
   \end{circus}
  \label{law:hidingCombination}
\end{lawn}
\begin{code}
crl_hidingCombination :: CAction -> Refinement CAction
crl_hidingCombination e@(CSPHide (CSPHide a cs1) cs2)
  = Done{orig = Just e, refined = Just ref, proviso=[]}
    where
      ref = (CSPHide a (ChanSetUnion cs1 cs2))
crl_hidingCombination _ = None
\end{code}
% Law 46 (Parallelism composition Deadlocked 3$^*$)
% \begin{lawn}[Parallelism composition Deadlocked 3$^*$]\sl
%     \begin{circus}
%         (\Extchoice_i c_i \then A_i) \lpar ns1 | cs | ns2 \rpar (\Extchoice_j c_j \then A_j)
%         = Stop %
%         = Stop \lpar ns1 | cs | ns2 \rpar (\Extchoice_j c_j \then A_j)
%     \end{circus}%
%     \begin{provs}
%         \item $\bigcup_i\{c_i\} \cap \bigcup_i\{c_i\} = \emptyset$
%         \item $\bigcup_i\{c_i\} \cap \bigcup_i\{c_i\} \subseteq cs$
%     \end{provs}
%   \label{law:parallelismDeadlocked3}
% \end{lawn}
% TODO: implement proviso
% QUESTION: can we interpret $c_i --> A_i$ the same of $c.i --> A(i)$

% \begin{code}
% crl_parallelismDeadlocked3 :: CAction -> Refinement CAction
% crl_parallelismDeadlocked3
%   (CSPNSParal ns1 cs ns2
%       (CSPRepExtChoice i (CSPCommAction ci ai))
%       (CSPRepExtChoice j (CSPCommAction cj aj)))
%   = Just (CSPNSParal ns1 cs ns2 CSPStop
%       (CSPRepExtChoice j (CSPCommAction cj aj)))
% crl_parallelismDeadlocked3 _ = None
% \end{code}
% Law 47 (Assignment Removal$^*$)
% TODO: implement proviso
\begin{lawn}[Assignment Removal$^*$]\sl

    \begin{circus}
      x := e \circseq A(x) = A(e)
   \end{circus}%
    \begin{provs}
        \item $x$ is not free in $A(e)$
    \end{provs}

  \label{law:assignmentRemoval}
\end{lawn}
TODO: implement proviso
\begin{code}

crl_assignmentRemoval :: CAction -> Refinement CAction
crl_assignmentRemoval ei@(CSPSeq 
                            (CActionCommand (CAssign [(x,[])] [ZVar (e,[])])) 
                            (CActionCommand (CValDecl [Choose (x1,[]) (ZVar (t,[]))] a)))
  = case x == x1 of
      True -> Done{orig = Just ei, refined = Just ref, proviso=[prov]}
      _ -> None
    where
      ref = (CActionCommand (CValDecl [Choose (e,[]) (ZVar (t,[]))] a))
      prov = (ZNot (ZMember (ZVar (x,[])) (ZSetDisplay $ zvar_to_zexpr(free_var_CAction ref))))
crl_assignmentRemoval _ = None
\end{code}
% Law 48 (Innocuous Assignment$^*$)

\begin{lawn}[Assignment Removal]\sl
    \begin{circus}
      x := e \circseq A(x) = A(e)
   \end{circus}%
    \begin{provs}
        \item $x$ is not free in $A(e)$
    \end{provs}
  \label{law:innocuousAssignment}
\end{lawn}
TODO: implement proviso
\begin{code}
crl_innocuousAssignment :: CAction -> Refinement CAction
crl_innocuousAssignment e@(CActionCommand (CAssign [(x1,[])] [ZVar (x2,[])]))
  = case (x1 == x2) of
      True -> Done{orig = Just e, refined = Just ref, proviso=[]}
      False -> None
    where
      ref = CSPSkip
crl_innocuousAssignment _ = None
\end{code}
% TODO: implement proviso
\begin{lawn}[Variable Substitution$^*$]\sl
    \begin{circus}
        \circvar x \circspot A(x) = \circvar y \circspot A(y)%
    \end{circus}%
    \begin{prov}
        $x$ is not free in A
        $y$ is not free in A
    \end{prov}

  \label{law:variableSubstitution}
\end{lawn}
TODO: implement proviso

\begin{code}
crl_variableSubstitution2 :: CAction -> ZName -> Refinement CAction
crl_variableSubstitution2
    e@(CActionCommand (CVarDecl [Include (ZSRef (ZSPlain x) [] [])]
             (CSPParAction a [ZVar (x1,[])]))) y
  =  Done{orig = Just e, refined = Just ref, proviso=[]}
    where
      ref = (CActionCommand (CVarDecl [Include (ZSRef (ZSPlain y) [] [])]
        (CSPParAction a [ZVar (y,[])])))
crl_variableSubstitution2 _ _ = None
\end{code}
% Law 50 (Input Prefix/Sequence Distribution$^*$)
% TODO: implement proviso
\begin{lawn}[Input Prefix/Sequence Distribution$^*$]\sl
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
TODO: implement proviso

\begin{code}
crl_inputPrefixSequenceDistribution :: CAction -> Refinement CAction
crl_inputPrefixSequenceDistribution
    e@(CSPSeq (CSPCommAction (ChanComm c [ChanInp x]) a1) a2 )
  =  Done{orig = Just e, refined = Just ref, proviso=[]}
    where
      ref = (CSPCommAction (ChanComm c [ChanInp x]) (CSPSeq a1 a2))
crl_inputPrefixSequenceDistribution _ = None
\end{code}
% Law 51 (Input Prefix/Hiding Identity$^*$)
\begin{lawn}[Input Prefix/Hiding Identity$^*$]\sl
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
TODO: implement proviso
\begin{code}
crl_inputPrefixHidIdentity :: CAction -> Refinement CAction
crl_inputPrefixHidIdentity
    e@(CSPHide (CSPCommAction (ChanComm c [ChanInp x]) a1) (CChanSet cs))
  =  Done{orig = Just e, refined = Just ref, proviso=[prov]}
    where
      ref = (CSPCommAction (ChanComm c [ChanInp x]) (CSPHide a1 (CChanSet cs)))
      prov = (ZNot (ZMember (ZVar (x,[])) (ZSetDisplay (zname_to_zexpr cs))))
crl_inputPrefixHidIdentity _ = None
\end{code}
% Law 52 (Guard/Parallelism composition---distribution$^*$)
\begin{lawn}[Guard/Parallelism composition---distribution$^*$]\sl
    \begin{circus}
     (g \circguard A1) \lpar ns1 | cs | ns2 \rpar A2
      \\ = \\
      g \circguard (A1 \lpar ns1 | cs | ns2 \rpar A2)
    \end{circus}
    \begin{provs}
        \item $initials(A2) \subseteq cs$
    \end{provs}
  \label{law:guardParDist}
\end{lawn}
\begin{code}
crl_guardParDist :: CAction -> Refinement CAction
crl_guardParDist
    e@(CSPNSParal ns1 (CChanSet cs) ns2 (CSPGuard g a1) a2)
  =  Done{orig = Just e, refined = Just ref, proviso=[prov]}
    where
      ref = (CSPGuard g (CSPNSParal ns1 (CChanSet cs) ns2 a1 a2))
      prov = (ZMember (ZTuple [ZSetDisplay (initials a2),ZSetDisplay (zname_to_zexpr cs)]) (ZVar ("\\subseteq",[])))
crl_guardParDist
    e@(CSPNSParal ns1 (CChanSet cs) ns2 a1 (CSPGuard g a2))
  =  Done{orig = Just e, refined = Just ref, proviso=[prov]}
    where
      ref = (CSPGuard g (CSPNSParal ns1 (CChanSet cs) ns2 a1 a2))
      prov = (ZMember (ZTuple [ZSetDisplay (initials a1),ZSetDisplay (zname_to_zexpr cs)]) (ZVar ("\\subseteq",[])))
crl_guardParDist _ = None

\end{code}
% Law 53 (Internal choice/Hiding composition Distribution)
\begin{lawn}[Internal choice/Hiding composition Distribution]\sl
    \begin{circus}
        (A1 \intchoice A2) \circhide cs
      \\ = \\
      (A1 \circhide cs) \intchoice (A2\circhide cs )
    \end{circus}%
  \label{law:internalChoiceHidingDistribution}
\end{lawn}
\begin{code}
crl_internalChoiceHidingDistribution :: CAction -> Refinement CAction
crl_internalChoiceHidingDistribution
    e@(CSPHide (CSPIntChoice a1 a2) cs)
  =  Done{orig = Just e, refined = Just ref, proviso=[]}
    where
      ref = (CSPIntChoice (CSPHide a1 cs) (CSPHide a2 cs))
crl_internalChoiceHidingDistribution _ = None
\end{code}
% Law 54 (Alternation Zero)
% \begin{lawn}[Alternation Zero]\sl
%     \begin{circus}
%         \circif\ \circelse\ i \circspot g_i \then A_i \ \circfi =\Chaos
%     \end{circus}%
%     \begin{provs}
%         \item $\bigvee_i \circspot\ g_i \equiv false$
%     \end{provs}
%   \label{law:alternationZero}
% \end{lawn}
% TODO: implement proviso
% \begin{code}
% crl_alternationZero
%   = undefined

% \end{code}
% Law 55 (Alternation)
% \begin{lawn}[Alternation]\sl
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
% \end{lawn}

% \begin{code}
% crl_alternation
%   = undefined

% \end{code}
% Law 56 (Assignment $Skip$)
\begin{lawn}[Assignment $Skip$]\sl

    \begin{circus}
        \circvar x \circspot x := e
      \\ = \\
      \circvar x \circspot \Skip%
    \end{circus}%

  \label{law:assignmentSkip}
\end{lawn}
\begin{code}
crl_assignmentSkip :: CAction -> Refinement CAction
crl_assignmentSkip
    ei@(CActionCommand (CValDecl
        [Include (ZSRef (ZSPlain x) [] [])]
        (CActionCommand (CAssign [(x1,[])] [ZVar (e,[])]))))
  =  Done{orig = Just ei, refined = Just ref, proviso=[]}
    where
      ref = (CActionCommand (CValDecl
        [Include (ZSRef (ZSPlain x) [] [])] CSPSkip))
crl_assignmentSkip _ = None
\end{code}

For testing purposes
\begin{lawn}[Guard combination]\sl
    \begin{zed}
      g_1 \circguard (g_2 \circguard A) = (g_1 \land g_2) \circguard A%
    \end{zed}
  \label{law:guardComb}
\end{lawn}

\begin{code}
crl_guardComb :: CAction -> Refinement CAction
crl_guardComb e@(CSPGuard g1 (CSPGuard g2 c))
  =  Done{orig = Just e, refined = Just ref, proviso=[]}
    where
      ref = (CSPGuard (ZAnd g1 g2) c)
crl_guardComb _ = None

\end{code}
\subsection{Auxiliary functions from Oliveira's PhD thesis}
Function for $usedC(A)$
\begin{code}
usedC :: CAction -> [ZExpr]
usedC (CSPCommAction x c) = [getCommName x] ++ usedC c
usedC (CSPGuard _ c) = usedC c
usedC (CSPSeq ca cb) = (usedC ca) ++ (usedC cb)
usedC (CSPExtChoice ca cb) = (usedC ca) ++ (usedC cb)
usedC (CSPIntChoice ca cb) = (usedC ca) ++ (usedC cb)
usedC (CSPNSParal _ _ _ ca cb) = (usedC ca) ++ (usedC cb)
usedC (CSPParal _ ca cb) = (usedC ca) ++ (usedC cb)
usedC (CSPNSInter _ _ ca cb) = (usedC ca) ++ (usedC cb)
usedC (CSPInterleave ca cb) = (usedC ca) ++ (usedC cb)
usedC (CSPHide c _) = usedC c
usedC (CSPRecursion _ c) = usedC c
usedC (CSPRepSeq _ c) = usedC c
usedC (CSPRepExtChoice _ c) = usedC c
usedC (CSPRepIntChoice _ c) = usedC c
usedC (CSPRepParalNS _ _ _ c) = usedC c
usedC (CSPRepParal _ _ c) = usedC c
usedC (CSPRepInterlNS _ _ c) = usedC c
usedC (CSPRepInterl _ c) = usedC c
usedC _ = []
\end{code}Function for $usedV(A)$
\begin{code}
usedV :: CAction -> [a]
usedV (CSPCommAction x c) = [] ++ usedV c
usedV (CSPGuard _ c) = usedV c
usedV (CSPSeq ca cb) = (usedV ca) ++ (usedV cb)
usedV (CSPExtChoice ca cb) = (usedV ca) ++ (usedV cb)
usedV (CSPIntChoice ca cb) = (usedV ca) ++ (usedV cb)
usedV (CSPNSParal _ _ _ ca cb) = (usedV ca) ++ (usedV cb)
usedV (CSPParal _ ca cb) = (usedV ca) ++ (usedV cb)
usedV (CSPNSInter _ _ ca cb) = (usedV ca) ++ (usedV cb)
usedV (CSPInterleave ca cb) = (usedV ca) ++ (usedV cb)
usedV (CSPHide c _) = usedV c
usedV (CSPRecursion _ c) = usedV c
usedV (CSPRepSeq _ c) = usedV c
usedV (CSPRepExtChoice _ c) = usedV c
usedV (CSPRepIntChoice _ c) = usedV c
usedV (CSPRepParalNS _ _ _ c) = usedV c
usedV (CSPRepParal _ _ c) = usedV c
usedV (CSPRepInterlNS _ _ c) = usedV c
usedV (CSPRepInterl _ c) = usedV c
usedV _ = []
\end{code}
\begin{code}
getCommName :: Comm -> ZExpr
getCommName (ChanComm n _) = ZVar (n,[])
getCommName (ChanGenComm n _ _) = ZVar (n,[])

\end{code}
Function used for $initials$
\begin{code}
initials :: CAction -> [ZExpr]
initials (CSPCommAction x c) = [getCommName x]
initials (CSPGuard _ c) = initials c
initials (CSPSeq ca cb) = (initials ca)
initials (CSPExtChoice ca cb) = (initials ca) ++ (initials cb)
initials (CSPIntChoice ca cb) = (initials ca) ++ (initials cb)
initials (CSPNSParal _ _ _ ca cb) = (initials ca) ++ (initials cb)
initials (CSPParal _ ca cb) = (initials ca) ++ (initials cb)
initials (CSPNSInter _ _ ca cb) = (initials ca) ++ (initials cb)
initials (CSPInterleave ca cb) = (initials ca) ++ (initials cb)
initials (CSPHide c _) = initials c
initials (CSPRecursion _ c) = initials c
initials (CSPRepSeq _ c) = initials c
initials (CSPRepExtChoice _ c) = initials c
initials (CSPRepIntChoice _ c) = initials c
initials (CSPRepParalNS _ _ _ c) = initials c
initials (CSPRepParal _ _ c) = initials c
initials (CSPRepInterlNS _ _ c) = initials c
initials (CSPRepInterl _ c) = initials c
initials CSPSkip = [ZVar ("tick",[])]
initials _ = []
\end{code}
\begin{code}
--trace (CSPCommAction (ChanComm x _) c) =
--  [[],[x],map (x:) (trace c)]
--trace (CSPCommAction (ChanGenComm x _ _) c) =
--  [[],[x],map (x:) (trace c)]
--trace (CSPSeq ca cb) = (trace ca)
--trace (CSPExtChoice ca cb) = (trace ca) ++ (trace cb)
data CSPOp = Com Char CSPOp | Seq CSPOp CSPOp | ExtCh CSPOp CSPOp | CSPSkp
trace :: CSPOp -> [[Char]]
trace (Com a p) = map (a:) (trace p)
trace (Seq a b) = (trace a) ++ (trace b)
trace (ExtCh a b) = (trace a)++ (trace b)
trace (CSPSkp)
 = [[]]
\end{code}
Function used for $deterministic$
\begin{code}
deterministic :: CAction -> Maybe [Char]
deterministic (CSPCommAction x c) = deterministic c
deterministic (CSPGuard _ c) = deterministic c
deterministic (CSPSeq ca cb) =
  case (da == Nothing)
    && (da == db)
    of
        false -> Just "Deterministic"
  where
    da = (deterministic ca)
    db = (deterministic cb)

deterministic (CSPExtChoice ca cb) =
  case (da == Nothing)
    && (da == db)
    of
        false -> Just "Deterministic"
  where
    da = (deterministic ca)
    db = (deterministic cb)

deterministic (CSPIntChoice ca cb) = Nothing
deterministic (CSPNSParal _ _ _ ca cb) = Nothing
deterministic (CSPParal _ ca cb) =  Nothing
deterministic (CSPNSInter _ _ ca cb) =
  case (da == Nothing)
    && (da == db)
    of
        false -> Just "Deterministic"
  where
    da = (deterministic ca)
    db = (deterministic cb)

deterministic (CSPInterleave ca cb) =
  case (da == Nothing)
    && (da == db)
    of
        false -> Just "Deterministic"
  where
    da = (deterministic ca)
    db = (deterministic cb)
deterministic (CSPHide c _) = Nothing
deterministic (CSPRecursion _ c) = deterministic c
deterministic (CSPRepSeq _ c) = deterministic c
deterministic (CSPRepExtChoice _ c) = deterministic c
deterministic (CSPRepIntChoice _ c) = Nothing
deterministic (CSPRepParalNS _ _ _ c) = Nothing
deterministic (CSPRepParal _ _ c) = Nothing
deterministic (CSPRepInterlNS _ _ c) = deterministic c
deterministic (CSPRepInterl _ c) = deterministic c
deterministic CSPSkip = Just "Deterministic"
deterministic _ = Just "Undefined"
\end{code}
\begin{code}
isDeterministic :: CAction -> [Char]
isDeterministic a
  = case x of
      Just "Deterministic" -> "Deterministic"
      Just x               -> "undefined"
      Nothing              -> "Non-deterministic"
    where x = (deterministic a)
\end{code}

\subsection{Mechanism for applying the refinement laws}

First I'm listing all the refinement laws currently available. Then I'm putting it as the variable "reflaws".\ignore{
\begin{code}
-- Description of each function:

-- For Circus Actions:
-- crl_assignmentRemoval :: CAction -> Refinement CAction
-- crl_assignmentSkip :: CAction -> Refinement CAction
-- crl_chanExt1 :: CAction -> ZName -> Refinement CAction
-- crl_communicationParallelismDistribution :: CAction -> CAction
-- crl_extChoiceSeqDist :: CAction -> CAction
-- crl_extChoiceStopUnit :: CAction -> CAction
-- crl_externalChoiceSequenceDistribution2 :: CAction -> Refinement CAction
-- crl_falseGuard :: CAction -> Refinement CAction
-- crl_guardParDist :: CAction -> Refinement CAction
-- crl_guardSeqAssoc :: CAction -> Refinement CAction
-- crl_hidingChaos :: CAction -> Refinement CAction
-- crl_hidingCombination :: CAction -> Refinement CAction
-- crl_hidingExpansion2 :: CAction -> ZName -> Refinement CAction
-- crl_hidingExternalChoiceDistribution :: CAction -> CAction
-- crl_hidingIdentity :: CAction -> Refinement CAction
-- crl_hidingParallelismDistribution :: CAction -> Refinement CAction
-- crl_hidingSequenceDistribution :: CAction -> Refinement CAction
-- crl_innocuousAssignment :: CAction -> Refinement CAction
-- crl_inputPrefixHidIdentity :: CAction -> Refinement CAction
-- crl_inputPrefixParallelismDistribution2 :: CAction -> Refinement CAction
-- crl_inputPrefixSequenceDistribution :: CAction -> Refinement CAction
-- crl_internalChoiceHidingDistribution :: CAction -> Refinement CAction
-- crl_internalChoiceParallelismDistribution :: CAction -> Refinement CAction
-- crl_joinBlocks :: CAction -> Refinement CAction
-- crl_parallelismDeadlocked1 :: CAction -> CAction
-- crl_parallelismDeadlocked3 :: CAction -> Refinement CAction
-- crl_parallelismExternalChoiceDistribution :: CAction -> CAction
-- crl_parallelismExternalChoiceExpansion :: CAction -> Comm -> CAction -> Refinement CAction
-- crl_parallelismIntroduction1a :: CAction -> NSExp -> [ZName] -> NSExp -> Refinement CAction
-- crl_parallelismIntroduction1b :: CAction -> NSExp -> [ZName] -> NSExp -> Refinement CAction
-- crl_parallelismUnit1 :: CAction -> Refinement CAction
-- crl_parallelismZero :: CAction -> Refinement CAction
-- crl_parallInterlEquiv :: CAction -> Refinement CAction
-- crl_parallInterlEquiv_backwards :: CAction -> Refinement CAction
-- crl_parExtChoiceExchange :: CAction -> Refinement CAction
-- crl_parSeqStep :: CAction -> Refinement CAction
-- crl_prefixHiding :: CAction -> Refinement CAction
-- crl_prefixParDist :: CAction -> Refinement CAction
-- crl_prefixSkip :: CAction -> Refinement CAction
-- crl_recUnfold :: CAction -> Refinement CAction
-- crl_seqChaosZero :: CAction -> Refinement CAction
-- crl_seqSkipUnit_a :: CAction -> Refinement CAction
-- crl_seqSkipUnit_b :: CAction -> Refinement CAction
-- crl_seqStopZero :: CAction -> CAction
-- crl_sequenceInternalChoiceDistribution :: CAction -> Refinement CAction
-- crl_trueGuard :: CAction -> Refinement CAction
-- crl_var_exp_par :: CAction -> Refinement CAction
-- crl_var_exp_par2 :: CAction -> Refinement CAction
-- crl_var_exp_rec :: CAction -> Refinement CAction
-- crl_variableBlockIntroduction :: CAction -> ZVar -> ZExpr -> Refinement CAction
-- crl_variableBlockSequenceExtension :: CAction -> Refinement CAction
-- crl_variableSubstitution2 :: CAction -> ZName -> Refinement CAction

-- For Circus Processes:
-- crl_promVarState :: CProc -> Refinement CProc
-- crl_promVarState2 :: CProc -> ZSName -> Refinement CProc
\end{code}
}
\begin{code}
reflawsCAction :: [CAction -> Refinement CAction]
reflawsCAction 
        = [crl_assignmentRemoval,
            -- ,
            -- crl_chanExt1,
            -- crl_hidingExpansion2,
            -- crl_parallelismIntroduction1a,
            -- crl_parallelismIntroduction1a_backwards,
            -- crl_parallelismIntroduction1b,
            -- crl_parallelismIntroduction1b_backwards,
            -- crl_parallInterlEquiv_backwards,
            -- crl_promVarState,
            -- crl_promVarState2,
            -- crl_var_exp_par,
            -- crl_variableBlockIntroduction,
            -- crl_variableSubstitution2
            crl_assignmentSkip,
            crl_communicationParallelismDistribution,
            crl_extChoiceStopUnit,
            crl_externalChoiceSequenceDistribution2,
            crl_falseGuard,
           crl_guardParDist,
            crl_guardComb,
             crl_guardSeqAssoc,
            crl_hidingChaos,
            crl_hidingCombination,
            crl_hidingExternalChoiceDistribution,
            crl_hidingIdentity,
            crl_hidingParallelismDistribution,
            crl_hidingSequenceDistribution,
            crl_innocuousAssignment,
            crl_inputPrefixHidIdentity,
            crl_inputPrefixParallelismDistribution2,
            crl_inputPrefixSequenceDistribution,
            crl_internalChoiceHidingDistribution,
            crl_internalChoiceParallelismDistribution,
            crl_joinBlocks,
            crl_parallelismDeadlocked1,
            crl_parallelismUnit1,
            crl_parallelismZero,
            crl_parallInterlEquiv,
            crl_parExtChoiceExchange,
            crl_prefixHiding,
            crl_prefixParDist,
            -- crl_prefixSkip, -- This one is going into an infinite loop with crl_seqSkipUnit_a
            crl_prefixSkip_backwards, -- this one fixes the probl above
            crl_recUnfold,
            crl_seqChaosZero,
            crl_seqSkipUnit_a,
            crl_seqSkipUnit_b,
            crl_seqStopZero,
            crl_sequenceInternalChoiceDistribution,
            crl_trueGuard,
            crl_var_exp_par2,
            crl_var_exp_rec,
            crl_variableBlockIntroduction_backwards,
            crl_variableBlockSequenceExtension
          ]
-- reflawsCProc = [crl_promVarState, crl_promVarState2]
\end{code}

I'm defining a type for the result of the refinement. It can either be $None$, when the refinement is not applied to that specification, or, it can be $Done\{refined :: t, proviso :: [Bool]\}$ with a list of provisos to be proved true, where $t$ can either be used for a $CProc$ or a $CAction$. We then will write those provisos in a text file so it can be used in a theorem prover, like Isabelle/HOL.
\begin{code}
data Refinement t = None 
                  | Done{orig :: Maybe t, 
                          refined :: Maybe t, 
                          proviso :: [ZPred]
                    } deriving (Eq,Show)
\end{code}
Then I'm starting to implement the mechanism itself. Basically, it will try to apply the refinement laws one by one until a result $Refinement CAction$ is returned.
\begin{code}
type RFun t = t -> Refinement t 
\end{code}
The function $applyCAction$ will try to apply a refinement law $r$ on an action $e$. If the result from applying it is $Done\{\ldots\}$, then this is the result. Otherwise, it will try to apply recursively to the inner parts of the $CAction$.
\begin{code}

applyCAction :: (RFun CAction) -> (RFun CAction)
applyCAction r e@(CActionCommand (CIf g))
 = case r e of
     r'@(Done{orig = _or, refined = _re, proviso=_pr}) -> r'
     None 
      -> case applyCActionsIf r g of
          (a,b) -> 
              Done{orig = Just e, refined = Just (CActionCommand (CIf a)), proviso=b}
          _ -> None
{-
applyCAction r e@(CSPSeq a1 a2) = case r e of
     r'@(Done{orig = _or, refined = _re, proviso=_pr}) -> r'
     None 
      -> case applyCActions r [a1,a2]  of
            [a1', a2'] -> 
                Done{orig = Just e, 
                    refined = Just (CSPSeq (isRefined a1 a1') (isRefined a2 a2')), 
                    proviso=(get_proviso a1')++(get_proviso a2')}
            _ -> None
-}

applyCAction r e@(CActionCommand (CVarDecl gf c)) 
 = case r e of
     r'@(Done{orig = _or, refined = _re, proviso=_pr}) -> r'
     None 
      -> case applyCActions r [c]  of
          [c'] -> 
              Done{orig = Just e, refined = Just (CActionCommand (CVarDecl gf (isRefined c c'))), proviso=(get_proviso c')}
          _ -> None

applyCAction r e@(CActionCommand (CValDecl gf c))
 = case r e of
     r'@(Done{orig = _or, refined = _re, proviso=_pr}) -> r'
     None 
      -> case applyCActions r [c]  of
          [c'] -> 
              Done{orig = Just e, refined = Just (CActionCommand (CValDecl gf (isRefined c c'))), proviso=(get_proviso c')}
          _ -> None

applyCAction r e@(CActionCommand (CResDecl gf c))
 = case r e of
     r'@(Done{orig = _or, refined = _re, proviso=_pr}) -> r'
     None 
      -> case applyCActions r [c]  of
          [c'] -> 
              Done{orig = Just e, refined = Just (CActionCommand (CResDecl gf (isRefined c c'))), proviso=(get_proviso c')}
          _ -> None

applyCAction r e@(CActionCommand (CVResDecl gf c))
 = case r e of
     r'@(Done{orig = _or, refined = _re, proviso=_pr}) -> r'
     None 
      -> case applyCActions r [c]  of
          [c'] -> 
              Done{orig = Just e, refined = Just (CActionCommand (CVResDecl gf (isRefined c c'))), proviso=(get_proviso c')}
          _ -> None

applyCAction r e@(CSPCommAction (ChanComm com xs) c)
 = case r e of
     r'@(Done{orig = _or, refined = _re, proviso=_pr}) -> r'
     None 
      -> case applyCActions r [c]  of
          [c'] -> 
              Done{orig = Just e, refined = Just (CSPCommAction (ChanComm com xs) (isRefined c c')), proviso=(get_proviso c')}
          _ -> None

applyCAction r e@(CSPGuard p c) = case r e of
     r'@(Done{orig = _or, refined = _re, proviso=_pr}) -> r'
     None 
      -> case applyCActions r [c]  of
          [c'] -> 
              Done{orig = Just e, refined = Just (CSPGuard p (isRefined c c')), proviso=(get_proviso c')}
          _ -> None

applyCAction r e@(CSPSeq a1 a2) = case r e of
     r'@(Done{orig = _or, refined = _re, proviso=_pr}) -> r'
     None 
      -> case applyCActions r [a1,a2]  of
            [a1', a2'] -> 
                Done{orig = Just e, 
                    refined = Just (CSPSeq (isRefined a1 a1') (isRefined a2 a2')), 
                    proviso=(get_proviso a1')++(get_proviso a2')}
            _ -> None

applyCAction r e@(CSPExtChoice a1 a2) = case r e of
     r'@( Done{orig = _or, refined = _re, proviso=_pr}) -> r'
     None 
      -> case applyCActions r [a1,a2]  of
            [a1', a2'] -> 
                Done{orig = Just e, 
                    refined = Just (CSPExtChoice (isRefined a1 a1') (isRefined a2 a2')), 
                    proviso=(get_proviso a1')++(get_proviso a2')}
            _ -> None

applyCAction r e@(CSPIntChoice a1 a2) = case r e of
     r'@( Done{orig = _or, refined = _re, proviso=_pr}) -> r'
     None 
      -> case applyCActions r [a1,a2]  of
            [a1', a2'] -> 
                Done{orig = Just e, 
                    refined = Just (CSPIntChoice (isRefined a1 a1') (isRefined a2 a2')), 
                    proviso=(get_proviso a1')++(get_proviso a2')}
            _ -> None

applyCAction r e@(CSPParal cs a1 a2) = case r e of
     r'@( Done{orig = _or, refined = _re, proviso=_pr}) -> r'
     None 
      -> case applyCActions r [a1,a2]  of
            [a1', a2'] -> 
                Done{orig = Just e, 
                    refined = Just (CSPParal cs (isRefined a1 a1') (isRefined a2 a2')), 
                    proviso=(get_proviso a1')++(get_proviso a2')}
            _ -> None

applyCAction r e@(CSPNSParal ns1 cs ns2 a1 a2)
 = case r e of
     r'@(Done{orig = _or, refined = _re, proviso=_pr}) -> r'
     None 
      -> case applyCActions r [a1,a2]  of
            [a1', a2'] -> 
                Done{orig = Just e, 
                    refined = Just (CSPNSParal ns1 cs ns2 (isRefined a1 a1') (isRefined a2 a2')), 
                    proviso=(get_proviso a1')++(get_proviso a2')}
            _ -> None

applyCAction r e@(CSPNSInter ns1 ns2 a1 a2) = case r e of
     r'@( Done{orig = _or, refined = _re, proviso=_pr}) -> r'
     None 
      -> case applyCActions r [a1,a2]  of
            [a1', a2'] -> 
                Done{orig = Just e, 
                    refined = Just (CSPNSInter ns1 ns2 (isRefined a1 a1') (isRefined a2 a2')), 
                    proviso=(get_proviso a1')++(get_proviso a2')}
            _ -> None

applyCAction r e@(CSPInterleave a1 a2) = case r e of
     r'@( Done{orig = _or, refined = _re, proviso=_pr}) -> r'
     None 
      -> case applyCActions r [a1,a2]  of
            [a1', a2'] -> 
                Done{orig = Just e, 
                    refined = Just (CSPInterleave (isRefined a1 a1') (isRefined a2 a2')), 
                    proviso=(get_proviso a1')++(get_proviso a2')}
            _ -> None
applyCAction r e@(CSPHide c cs) = case r e of
     r'@( Done{orig = _or, refined = _re, proviso=_pr}) -> r'
     None 
      -> case applyCActions r [c]  of
          [c'] -> 
              Done{orig = Just e, refined = Just (CSPHide (isRefined c c') cs), proviso=(get_proviso c')}
          _ -> None

applyCAction r e@(CSPUnfAction nm c) = case r e of
     r'@( Done{orig = _or, refined = _re, proviso=_pr}) -> r'
     None 
      -> case applyCActions r [c]  of
          [c'] -> 
              Done{orig = Just e, refined = Just (CSPUnfAction nm (isRefined c c')), proviso=(get_proviso c')}
          _ -> None

applyCAction r e@(CSPRecursion nm c) = case r e of
     r'@( Done{orig = _or, refined = _re, proviso=_pr}) -> r'
     None 
      -> case applyCActions r [c]  of
          [c'] -> 
              Done{orig = Just e, refined = Just (CSPRecursion nm (isRefined c c')), proviso=(get_proviso c')}
          _ -> None

applyCAction r e@(CSPUnParAction lst c nm) = case r e of
     r'@( Done{orig = _or, refined = _re, proviso=_pr}) -> r'
     None 
      -> case applyCActions r [c]  of
          [c'] -> 
              Done{orig = Just e, refined = Just (CSPUnParAction lst (isRefined c c') nm), proviso=(get_proviso c')}
          _ -> None

applyCAction r e@(CSPRepSeq lst c) = case r e of
     r'@( Done{orig = _or, refined = _re, proviso=_pr}) -> r'
     None 
      -> case applyCActions r [c]  of
          [c'] -> 
              Done{orig = Just e, refined = Just (CSPRepSeq lst (isRefined c c')), proviso=(get_proviso c')}
          _ -> None

applyCAction r e@(CSPRepExtChoice lst c) = case r e of
     r'@( Done{orig = _or, refined = _re, proviso=_pr}) -> r'
     None 
      -> case applyCActions r [c]  of
          [c'] -> 
              Done{orig = Just e, refined = Just (CSPRepExtChoice lst (isRefined c c')), proviso=(get_proviso c')}
          _ -> None

applyCAction r e@(CSPRepIntChoice lst c) = case r e of
     r'@( Done{orig = _or, refined = _re, proviso=_pr}) -> r'
     None 
      -> case applyCActions r [c]  of
          [c'] -> 
              Done{orig = Just e, refined = Just (CSPRepIntChoice lst (isRefined c c')), proviso=(get_proviso c')}
          _ -> None

applyCAction r e@(CSPRepParalNS cs lst ns c) = case r e of
     r'@( Done{orig = _or, refined = _re, proviso=_pr}) -> r'
     None 
      -> case applyCActions r [c]  of
          [c'] -> 
              Done{orig = Just e, refined = Just (CSPRepParalNS cs lst ns (isRefined c c')), proviso=(get_proviso c')}
          _ -> None

applyCAction r e@(CSPRepParal cs lst c) = case r e of
     r'@( Done{orig = _or, refined = _re, proviso=_pr}) -> r'
     None 
      -> case applyCActions r [c]  of
          [c'] -> 
              Done{orig = Just e, refined = Just (CSPRepParal cs lst (isRefined c c')), proviso=(get_proviso c')}
          _ -> None
applyCAction r e@(CSPRepInterlNS lst ns c) = case r e of
     r'@( Done{orig = _or, refined = _re, proviso=_pr} )-> r'
     None 
      -> case applyCActions r [c]  of
          [c'] -> 
              Done{orig = Just e, refined = Just (CSPRepInterlNS lst ns (isRefined c c')), proviso=(get_proviso c')}
          _  -> None

applyCAction r e@(CSPRepInterl lst c) = case r e of
     r'@(Done{orig = _or, refined = _re, proviso=_pr}) -> r'
     None 
      -> case applyCActions r [c]  of
          [c'] -> 
              Done{orig = Just e, refined = Just (CSPRepInterl lst (isRefined c c')), proviso=(get_proviso c')}
          _ -> None
applyCAction r e
 = case r e of
     r'@(Done{orig = _or, refined = _re, proviso=_pr}) -> r'
     None ->  None

\end{code}
\subsection{Applying to a list of actions -- $applyCActions$}
Applies a refinement law into a list of actions.
\begin{code}
applyCActions :: RFun CAction -> [CAction] -> [Refinement CAction]
applyCActions r [] = []
applyCActions r [e]
 = [applyCAction r e]
applyCActions r (e:es)
 = (applyCAction r e):(applyCActions r es)
\end{code}
\subsection{Applying to a list of guarded actions -- $applyCActionsIf$}
Applies a refinement law into a list of actions.
\begin{code}
applyCActionsIf :: RFun CAction -> CGActions -> (CGActions,[ZPred])
applyCActionsIf r (CircGAction zp ca)
  = ((CircGAction zp (isRefined ca ca')), get_proviso ca')
  where ca' = (applyCAction r ca)
applyCActionsIf r (CircThenElse ga gb)
 = ((CircThenElse ga' gb'),prova++provb)
  where (ga',prova) = (applyCActionsIf r ga)
        (gb',provb) = (applyCActionsIf r gb)
\end{code}

\subsection{Checking the refinement results}
This will control if something was refined or not
\begin{code}
isRefined :: CAction-> Refinement CAction -> CAction
isRefined a b
  = case b of 
      (Done{orig=_, refined=Just e', proviso=z}) -> e'
      None -> a
isRefined' :: CAction-> Maybe CAction -> CAction
isRefined' a b
  = case b of 
      Just e' -> e'
      Nothing -> a

\end{code}

\subsection{The automated refinement tool}

\begin{code}
crefine :: [RFun CAction]
                 -> [RFun CAction]
                 -> CAction
                 -> [Refinement CAction]
                 -> [Refinement CAction]
crefine lst [r] e steps = 
    reverse (results:steps)
    where 
      results = applyCAction r e

crefine lst (r:rs) e steps = 
    case rsx of 
      ei@(Done{orig=Just a, refined=Just e', proviso=z}) -> 
        case a==e' of
          True -> crefine lst rs e steps
          False -> crefine lst lst e' (ei:steps)
      None -> crefine lst rs e steps
    where rsx = applyCAction r e

refine :: [RFun CAction] -> CAction -> [Refinement CAction]
refine f g = crefine f f g []
\end{code}
\begin{code}
getRef ::  [Refinement CAction] -> Maybe CAction
getRef [] = Nothing
getRef [e@(Done{orig=x, refined=y, proviso=z})] = y
getRef [None] = Nothing
getRef xs = getRef [last xs]
\end{code}

\subsection{Testing the tool}
\begin{code}
runStepRefinement :: CAction -> [Refinement CAction]
runStepRefinement x = refine reflawsCAction x

runRefinement :: CAction -> Maybe CAction
runRefinement x = getRef $ refine reflawsCAction x

refineCAction :: CAction -> CAction
refineCAction x = get_refined $ last (refine reflawsCAction x)
\end{code}

\subsection{Printing the Refinement Steps}
First we get the bits from the $Refinement$ record
\begin{code}
get_orig :: Refinement CAction -> CAction
get_orig (Done{orig=Just a,refined=_,proviso=_}) = a
get_refined :: Refinement CAction -> CAction
get_refined (Done{orig=_,refined=Just b,proviso=_}) = b
get_refined (Done{orig=Just a,refined=Nothing,proviso=_}) = a
get_proviso :: Refinement CAction -> [ZPred]
get_proviso None = []
get_proviso (Done{orig=_,refined=_,proviso=c}) = c
\end{code}
Then we define some printing functions, so the refinement can look better on screen.
\begin{code}
print_proviso [] = "none"
print_proviso [c] = show c
print_proviso (c:cs) = (show c) ++ "] and also [" ++ (print_proviso cs)

print_ref_head c = "LHS\n=\n"
                 ++ (show (get_orig c)) ++"\n\n=   provided["
                 ++ (print_proviso (get_proviso c)) ++"]\n\n"
                 ++ (show (get_refined c)) ++"\n\n"
print_ref_steps c = "=   provided[" 
                 ++ (print_proviso (get_proviso c)) ++"]\n\n"
                 ++ (show (get_refined c)) ++ "\n\n"
\end{code}
Finally, we define a $print\_ref$ function which prints out on screen the refinement. We can take that to a file with $print\_file\_ref$.
\begin{code}
print_ref [] = "No refinement was performed\n"
print_ref [None] = "No refinement was performed\n"
print_ref [x] = print_ref_head x
print_ref (x:xs) = print_ref_head x ++ (print_ref' xs)
print_ref' [] = "=\nRHS"
print_ref' [x] = print_ref_steps x
print_ref' (x:xs) = print_ref_steps x ++ (print_ref' xs)
print_file_ref fname example = writeFile fname $ print_ref $runStepRefinement example

\end{code}
\ignore{
Testing area
\begin{code}
-- Usage:
-- you can type 
-- $ print_file_ref "ref_steps.txt" cexample2
-- And it will write the refinement of cexample2 into the ref_steps.txt file.

cexample = (CSPNSParal NSExpEmpty (CChanSet ["c1","c2"]) NSExpEmpty (CSPGuard (ZMember (ZTuple [ZVar ("v1",[]),ZInt 0]) (ZVar (">",[])))  (CActionName "a1")) (CActionName "a2"))
cexample2 = (CSPGuard (ZMember (ZTuple [ZVar ("v1",[]),ZInt 0]) (ZVar (">",[])))  (CSPNSParal NSExpEmpty (CChanSet ["c1","c2"]) NSExpEmpty (CSPGuard (ZMember (ZTuple [ZVar ("v2",[]),ZInt 0]) (ZVar (">",[])))  (CActionName "a1")) (CActionName "a2")))
cexample3 = (CActionCommand (CValDecl [Choose ("b",[]) (ZSetComp [Choose ("x",[]) (ZVar ("BINDING",[])),Check (ZAnd (ZMember (ZVar ("time",[])) (ZVar ("\\nat",[]))) (ZMember (ZVar ("time",[])) (ZVar ("\\nat",[]))))] Nothing)] (CSPSeq (CActionCommand (CAssign [("sv_SysClock2_time",[])] [ZInt 0])) (CSPRecursion "X" (CSPSeq (CSPExtChoice (CSPGuard (ZMember (ZTuple [ZVar ("sv_SysClock2_time",[]),ZInt 2]) (ZVar (">",[]))) (CSPSeq (CActionCommand (CAssign [("sv_SysClock2_time",[])] [ZInt 0])) (CActionName "X"))) (CSPInterleave (CSPCommAction (ChanComm "tick" []) (CActionCommand (CAssign [("sv_SysClock2_time",[])] [ZCall (ZVar ("+",[])) (ZTuple [ZVar ("sv_SysClock2_time",[]),ZInt 1])]))) (CSPCommAction (ChanComm "getCurrentTime" [ChanOutExp (ZVar ("sv_SysClock2_time",[]))]) CSPSkip))) (CActionName "X"))))))
cexample4 = (CActionCommand (CValDecl [Choose ("b",[]) (ZSetComp [Choose ("x",[]) (ZVar ("BINDING",[])),Check (ZAnd (ZMember (ZVar ("time",[])) (ZVar ("\\nat",[]))) (ZMember (ZVar ("time",[])) (ZVar ("\\nat",[]))))] Nothing)] (CSPSeq (CActionCommand (CAssign [("sv_SysClock2_time",[])] [ZInt 0])) (CSPRecursion "X" (CSPSeq (CSPExtChoice (CSPGuard (ZMember (ZTuple [ZVar ("sv_SysClock2_time",[]),ZInt 2]) (ZVar (">",[]))) (CSPSeq (CActionCommand (CAssign [("sv_SysClock2_time",[])] [ZInt 0])) (CActionName "X"))) (CSPInterleave (CSPCommAction (ChanComm "tick" []) (CActionCommand (CAssign [("sv_SysClock2_time",[])] [ZCall (ZVar ("+",[])) (ZTuple [ZVar ("sv_SysClock2_time",[]),ZInt 1])]))) (CSPCommAction (ChanComm "getCurrentTime" [ChanOutExp (ZVar ("sv_SysClock2_time",[]))]) CSPSkip))) (CActionName "X"))))))
cexample5= (CSPInterleave (CSPCommAction (ChanComm "tick" []) (CActionCommand (CAssign [("sv_SysClock2_time",[])] [ZCall (ZVar ("+",[])) (ZTuple [ZVar ("sv_SysClock2_time",[]),ZInt 1])]))) (CSPCommAction (ChanComm "getCurrentTime" [ChanOutExp (ZVar ("sv_SysClock2_time",[]))]) CSPSkip))
            

\end{code}}