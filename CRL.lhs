\section{Circus Refinement Laws}

\ignore{
\begin{code}
module CRL
where
import AST
import DefSets
import Data.List
import Data.Maybe

\end{code}
}

\begin{lawn}[var-exp-par]\sl

    \begin{circus}
        (\circvar\ d:T \circspot A1) \lpar ns1 | cs | ns2 \rpar A2
        \\ = \\
        (\circvar\ d:T \circspot A1 \lpar ns1 | cs | ns2 \rpar A2) %
    \end{circus}%
    \begin{prov}
        $\{d,d'\} \cap FV(A2) = \emptyset$
    \end{prov}


  \label{law:var-exp-par}
\end{lawn}
\begin{code}
crl_var_exp_par (CSPNSParal ns1 cs ns2 (CActionCommand
                    (CVarDecl [(Choose (d,[]) t)] a1)) a2)
  = case p1 of
      True -> (CActionCommand (CVarDecl [(Choose (d,[]) t)]
                  (CSPNSParal ns1 cs ns2 a1 a2)))
      False -> (CSPNSParal ns1 cs ns2
                  (CActionCommand (CVarDecl [(Choose (d,[]) t)] a1)) a2)
    where
      p1 = False
      --p1 = isEmpty (intersectionSet ([(d,[]),(d,["'"])]) (getFV a2))
\end{code}
\begin{lawn}[var-exp-par-2]\sl

    \begin{circus}
        (\circvar\ d:T \circspot A1) \lpar ns1 | cs | ns2 \rpar (\circvar\ d:T \circspot A2)
        \\ = \\
        (\circvar\ d:T \circspot A1 \lpar ns1 | cs | ns2 \rpar A2) %
    \end{circus}%
    \begin{prov}
        $\{d,d'\} \cap FV(A2) = \emptyset$
    \end{prov}


  \label{law:var-exp-par2}
\end{lawn}
\begin{code}
crl_var_exp_par2 (CSPNSParal ns1 cs ns2
                  (CActionCommand (CVarDecl d1 a1))
                  (CActionCommand (CVarDecl d2 a2)))
  = case (d1 == d2) of
      True  -> (CActionCommand (CVarDecl d1
                      (CSPNSParal ns1 cs ns2 a1 a2)))
      False -> (CSPNSParal ns1 cs ns2
                      (CActionCommand (CVarDecl d1 a1))
                      (CActionCommand (CVarDecl d2 a2)))
\end{code}

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
 TODO: implement proviso
\begin{code}
crl_var_exp_rec (CSPRecursion x1 (CActionCommand
                  (CVarDecl [(Choose xv t)]
                    (CSPParAction f [ZVar (x2,[])]))))
  = case (x1 == x2) of
      True  -> (CActionCommand (CVarDecl [(Choose xv t)]
                  (CSPRecursion x1 (CSPParAction f [ZVar (x1,[])]))))
      False -> (CSPRecursion x1 (CActionCommand (CVarDecl [(Choose xv t)]
                   (CSPParAction f [ZVar (x2,[])]))))
\end{code}
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
crl_variableBlockSequenceExtension
      (CSPSeq (CSPSeq a1
            (CActionCommand (CVarDecl [(Choose x t)] a2))) a3)
  = case p1 of
      True -> CActionCommand (CVarDecl
                [(Choose x t)] (CSPSeq (CSPSeq a1 a2) a3))
      False -> (CSPSeq (CSPSeq a1 (CActionCommand
                  (CVarDecl [(Choose x t)] a2))) a3)
    where
      p1 = null (([(x,[]),(x,["'"])]) `intersect` ((getFV a2) `union`(getFV a1)))
\end{code}
\begin{lawn}[Variable Substitution$^*$]\sl
   \begin{circus}
       A(x)
       \\ = \\
       \circvar\ y \circspot y \prefixcolon [y'=x] \circseq\ A(y)%
   \end{circus}%
   \begin{prov}
       $y$ is not free in A
   \end{prov}
 \label{law:variableSubstitution}
\end{lawn}
TODO: implement proviso
\begin{code}
crl_variableSubstitution (CSPParAction a exp)
-- = CVarDecl [(ZVar ("y",[]))] (CSPSeq (CActionCommand (CAssumpt [("y")] ZTrue{reason=[]} )))
  = undefined
\end{code}

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
crl_variableBlockIntroduction a x t
  = case p1 of
      True -> CActionCommand (CVarDecl [(Choose x t)] a)
      False -> a
    where
      p1 = not (elem x (getFV a))
\end{code}
\begin{lawn}[join---blocks]\sl
    \begin{circus}
        \circvar\ x:T_1 \circspot \circvar\ x:T_2 \circspot A2
        \\ = \\
        \circvar\ x:T_1 ; x:T_2 \circspot A2
    \end{circus}%
    \begin{prov}
        $x \notin FV(A_1) \cup FV(A_3)$
    \end{prov}
  \label{law:joinBlocks}
\end{lawn}
\begin{code}
crl_joinBlocks (CActionCommand (CVarDecl
                [(Choose x t1)] (CActionCommand
                  (CVarDecl [(Choose y t2)] a))))
  = (CActionCommand (CVarDecl [(Choose x t1),(Choose y t2)] a))
\end{code}

\begin{lawn}[Sequence unit]\sl

   \begin{circus}
     (A) \Skip \circseq A \\ %
     (B) A = A \circseq \Skip %
   \end{circus}

 \label{law:seqSkipUnit}
\end{lawn}
\begin{code}
crl_seqSkipUnit_a (CSPSeq CSPSkip a) = a
crl_seqSkipUnit_b a = (CSPSeq a CSPSkip)
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
crl_recUnfold (CSPRecursion x1 (CSPParAction f [ZVar (x2,[])]))
  -- = case (x1 == x2) of _
  --                       | True         -> (CSPParAction f (CSPRecursion x1 (CSPParAction f [ZVar (x2,[])])))
  --                       | otherwise    -> (CSPRecursion x1 (CSPParAction f [ZVar (x2,[])]))
  = undefined
\end{code}

\begin{lawn}[Parallelism composition/External choice---expansion$^*$]\sl
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
TODO: implement proviso
\begin{code}
crl_parallelismExternalChoiceExpansion
  (CSPNSParal ns1 cs ns2
      (CSPRepExtChoice i (CSPCommAction ai aAi))
      (CSPRepExtChoice j (CSPCommAction bj aBj))) c aC
  = (CSPNSParal ns1 cs ns2
      (CSPRepExtChoice i (CSPCommAction ai aAi))
      (CSPExtChoice (CSPRepExtChoice j
          (CSPCommAction bj aBj))
      (CSPCommAction c aC)))
\end{code}

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
crl_parallelismIntroduction1b
  (CSPCommAction (ChanComm c
      [ChanDotExp e]) a)
      (NSExprMult ns1) cs (NSExprMult ns2)
  = case p1 && p2 of
      True -> (CSPNSParal (NSExprMult ns1) (CChanSet cs) (NSExprMult ns2)
                (CSPCommAction (ChanComm c [ChanDotExp e]) a)
                (CSPCommAction (ChanComm c [ChanDotExp e]) CSPSkip))
      False -> (CSPCommAction (ChanComm c [ChanDotExp e]) a)
    where
      p1 = not (elem c (usedC a))
      p2 = (subset (getWrtV a) ns1)

crl_parallelismIntroduction1a
    (CSPCommAction (ChanComm c e) a)
        (NSExprMult ns1) cs (NSExprMult ns2)
  = case p1 && p2 of
      True -> (CSPNSParal (NSExprMult ns1) (CChanSet cs) (NSExprMult ns2)
                  (CSPCommAction (ChanComm c e) a)
                  (CSPCommAction (ChanComm c e) CSPSkip))
      False -> (CSPCommAction (ChanComm c e) a)
    where
      p1 = elem c (usedC a)
      p2 = (subset (getWrtV a) ns1)
\end{code}

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
crl_chanExt1 (CSPNSParal ns1 (CChanSet cs) ns2 a1 a2) c
  = case p1 of
      True -> (CSPNSParal ns1 (ChanSetUnion
                    (CChanSet cs) (CChanSet [c])) ns2 a1 a2)
      False -> (CSPNSParal ns1 (CChanSet cs) ns2 a1 a2)
    where
      p1 = not (elem c ((usedC a1) `union` (usedC a2)))
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
crl_hidingExpansion2 (CSPHide a (CChanSet cs)) c
  = case p1 of
      True -> (CSPHide a (ChanSetUnion (CChanSet cs) (CChanSet [c])))
      False -> (CSPHide a (CChanSet cs))
    where
      p1 = not (c `elem` cs)
\end{code}
% Law 14 (Prefix/Hiding$^*$)
\begin{lawn}[Prefix/Hiding$^*$]\sl
    \begin{circus}
        (c \then Skip) \circhide \lchanset c \rchanset = \Skip%
        \also
        (c.e \then Skip) \circhide \lchanset c \rchanset = Skip%
    \end{circus}%
 \label{law:prefixHiding}
\end{lawn}
\begin{code}
crl_prefixHiding
  (CSPHide (CSPCommAction (ChanComm c []) CSPSkip) (CChanSet [c1]))
  = case (c == c1) of
      True        -> CSPSkip
      otherwise   -> (CSPHide (CSPCommAction (ChanComm c []) CSPSkip)
                        (CChanSet [c1]))
crl_prefixHiding (CSPHide (CSPCommAction
                    (ChanComm c [ChanDotExp e]) CSPSkip)
                    (CChanSet [c1]))
  = case (c == c1) of
      True        -> CSPSkip
      otherwise   -> (CSPHide (CSPCommAction
                        (ChanComm c [ChanDotExp e]) CSPSkip)
                          (CChanSet [c1]))
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
crl_hidingIdentity (CSPHide a (CChanSet cs))
  = case p1 of
      True -> a
      False -> (CSPHide a (CChanSet cs))
    where
      p1 = null (cs `intersect` (usedC a))
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
crl_parExtChoiceExchange
    (CSPExtChoice
      (CSPNSParal ns1 cs ns2 a1 a2)
      (CSPNSParal ns11 cs1 ns21 b1 b2))
  = case (ns1 == ns11 && cs1 == cs && ns2 == ns21) of
      True ->  (CSPNSParal ns1 cs ns2
                  (CSPExtChoice a1 b1)
                  (CSPExtChoice a2 b2))
      False -> (CSPExtChoice
                  (CSPNSParal ns1 cs ns2 a1 a2)
                  (CSPNSParal ns11 cs1 ns21 b1 b2))
\end{code}
% Law 17 (Parallelism composition/External choice---distribution$^*$)
\begin{lawn}[Parallelism composition/External choice---distribution$^*$]\sl

  \begin{circus}
      \Extchoice i \circspot (A_i \lpar ns1 | cs | ns2 \rpar A)
      \\ = \\
      (\Extchoice i \circspot A_i) \lpar ns1 | cs | ns2 \rpar A
  \end{circus}%
  \begin{provs}
      \item $initials(A) \subseteq cs$ %
      \item $A$ is deterministic %
  \end{provs}


\label{law:parallelismExternalChoiceDistribution}
\end{lawn}
\begin{code}
crl_parallelismExternalChoiceDistribution
    (CSPRepExtChoice i (CSPNSParal ns1 (CChanSet cs) ns2 ai a))
  = case p1 && p2 of
      True  -> (CSPNSParal ns1
                  (CChanSet cs) ns2 (CSPRepExtChoice i ai) a)
      False -> (CSPRepExtChoice i (CSPNSParal ns1 (CChanSet cs) ns2 ai a))
    where
      p1 = (subset (initials a) cs)
      p2 = isJust (deterministic a)
\end{code}
% Law 18 (External choice unit)
\begin{lawn}[External choice unit]\sl
    \begin{circus}
      Stop \extchoice A = A
    \end{circus}
  \label{law:extChoiceStopUnit}
\end{lawn}

\begin{code}
crl_extChoiceStopUnit (CSPExtChoice CSPStop a) = a
\end{code}
% Law 19 (External choice/Sequence---distribution)
\begin{lawn}[External choice/Sequence---distribution]\
    \begin{circus}
      (\Extchoice\ i \circspot g_i \circguard c_i \then A_i)\circseq B
      \\ = \\
      \Extchoice\ i \circspot g_i \circguard c_i \then A_i\circseq B%
    \end{circus}
  \label{law:extChoiceSeqDist}
\end{lawn}
\begin{code}
crl_extChoiceSeqDist (CSPSeq (CSPRepExtChoice i
                        (CSPGuard gi (CSPCommAction ci ai))) b)
  = (CSPRepExtChoice i (CSPSeq
          (CSPGuard gi (CSPCommAction ci ai)) b))
\end{code}
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
crl_hidingExternalChoiceDistribution
    (CSPHide (CSPExtChoice a1 a2) (CChanSet cs))
  = case p1 of
      True  -> (CSPExtChoice
                  (CSPHide a1 (CChanSet cs))
                  (CSPHide a2 (CChanSet cs)))
      False -> (CSPHide (CSPExtChoice a1 a2) (CChanSet cs))
    where
      p1 = null ((initials a1 `union` initials a2) `intersect` cs)
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
crl_parallelismDeadlocked1
    (CSPNSParal ns1 (CChanSet cs) ns2
          (CSPCommAction (ChanComm c1 x) a1)
          (CSPCommAction (ChanComm c2 y) a2))
  = case p1 && p2 of
    True -> (CSPNSParal ns1 (CChanSet cs) ns2
              CSPStop
              (CSPCommAction (ChanComm c2 y) a2))
    False -> (CSPNSParal ns1 (CChanSet cs) ns2
              (CSPCommAction (ChanComm c1 x) a1)
              (CSPCommAction (ChanComm c2 y) a2))
    where
      p1 = (c1 == c2)
      p2 = (subset [c1,c2] cs)
crl_parallelismDeadlocked1 (CSPNSParal ns1 (CChanSet cs) ns2
                              CSPStop (CSPCommAction c2 a2))
  = CSPStop
\end{code}
% Law 22 (Sequence zero)
\begin{lawn}[Sequence zero]\sl
    \begin{circus}
      \Stop \circseq A = \Stop
    \end{circus}
  \label{law:seqStopZero}
\end{lawn}
\begin{code}
crl_seqStopZero (CSPSeq CSPStop a)
  = CSPStop
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

  \label{law:communicationParallelismDistribution}
\end{lawn}
\begin{code}
crl_communicationParallelismDistribution
    (CSPNSParal ns1 cs ns2
        (CSPCommAction (ChanComm c [ChanOutExp e]) (CActionName a1))
        (CSPCommAction (ChanComm c1 [ChanInp x1])
          (CSPParAction a2 [ZVar (x,[])])))
  = case (c == c1 && x == x1) of
      True  ->  (CSPCommAction (ChanComm c [ChanDotExp e])
                    (CSPNSParal ns1 cs ns2
                          (CActionName a1)
                          (CSPParAction a2 [e])))
      False -> (CSPNSParal ns1 cs ns2
                    (CSPCommAction (ChanComm c [ChanOutExp e])
                      (CActionName a1))
                    (CSPCommAction (ChanComm c1 [ChanInp x1])
                      (CSPParAction a2 [ZVar (x,[])])))
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
\end{lawn}
\begin{code}
crl_channelExtension3
      (CSPHide (CSPNSParal ns1 cs1 ns2 a1
                (CSPParAction a2 [e])) cs2) c x
  = (CSPHide (CSPNSParal ns1 cs1 ns2
        (CSPCommAction (ChanComm c [ChanOutExp (e)]) a1)
        (CSPCommAction (ChanComm c [ChanInp x])
          (CSPParAction a2 [ZVar (x,[])]))) cs2)
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
crl_channelExtension4 (CSPHide (CSPNSParal ns1 (CChanSet cs1) ns2 a1 a2) (CChanSet cs2)) (ChanComm c [ChanOutExp (e)])
  = case p1 && p2
    of
      True -> (CSPHide (CSPNSParal ns1 (CChanSet cs1) ns2 (CSPCommAction (ChanComm c [ChanOutExp (e)]) a1) (CSPCommAction (ChanComm c [ChanOutExp (e)]) a2)) (CChanSet cs2))
      False -> (CSPHide (CSPNSParal ns1 (CChanSet cs1) ns2 a1 a2) (CChanSet cs2))
    where
      p1 = c `elem` cs1
      p2 = c `elem` cs2

crl_channelExtension4 (CSPHide (CSPNSParal ns1 (CChanSet cs1) ns2 a1 a2)
                                (CChanSet cs2)) (ChanComm c e)
  = case p1 && p2 of
      True -> (CSPHide (CSPNSParal ns1 (CChanSet cs1) ns2
                          (CSPCommAction (ChanComm c e) a1)
                           (CSPCommAction (ChanComm c e) a2))
                        (CChanSet cs2))
      False -> (CSPHide (CSPNSParal ns1 (CChanSet cs1) ns2 a1 a2)
                      (CChanSet cs2))
    where
      p1 = c `elem` cs1
      p2 = c `elem` cs2
\end{code}
Law 26 (prom-var-state)
\begin{code}
crl_promVarState
  (ProcMain
      (ZSchemaDef st (ZSchema exsc))
        [CParAction lact (ParamActionDecl (xt:zvar1) act)]
        (CActionCommand (CValDecl [xt1] mact)))
  = case (xt == xt1) of
      True -> (ProcMain
                (ZSchemaDef st (ZS2 ZSAnd (ZSchema exsc) (ZSchema [xt])))
                [CParAction lact act] mact)
      False -> (ProcMain
                (ZSchemaDef st (ZSchema exsc))
                [CParAction lact
                    (ParamActionDecl (xt:zvar1) act)]
                    (CActionCommand (CValDecl [xt1] mact)))

\end{code}
Law 27 (prom-var-state-2)
\begin{code}
crl_promVarState2
    (ProcStalessMain
      [CParAction lact (ParamActionDecl (xt1:zvar1) act)]
      (CActionCommand (CValDecl [xt] mact))) st
  = case (xt == xt1) of
      True -> (ProcMain (ZSchemaDef st (ZSchema [xt]))
                [CParAction lact act] mact)
      False -> (ProcStalessMain
                  [CParAction lact (ParamActionDecl (xt1:zvar1) act)]
                  (CActionCommand (CValDecl [xt] mact)))
\end{code}
\begin{lawn}[Parallelism composition unit$^*$]\sl
    \begin{circus}
        \Skip \lpar ns1 | cs | ns2 \rpar \Skip = \Skip
    \end{circus}%
  \label{law:parallelismUnit1}
\end{lawn}
\begin{code}
crl_parallelismUnit1 (CSPNSParal _ _ _ CSPSkip CSPSkip) = CSPSkip
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
crl_parallInterlEquiv (CSPNSInter ns1 ns2 a1 a2)
  = (CSPNSParal ns1 CSEmpty ns2 a1 a2)
crl_parallInterlEquiv_backwards (CSPNSParal ns1 CSEmpty ns2 a1 a2)
  = (CSPNSInter ns1 ns2 a1 a2)
\end{code}
\begin{lawn}[Parallelism composition/Sequence---step$^*$]\sl
\label{law:parSeqStep}
  \begin{circus}
    (A1\circseq A2) \lpar ns1 | cs | ns_ 2 \rpar A3
    \\ = \\
    A1\circseq (A2 \lpar ns_ 1 | cs | ns2 \rpar A3)%
  \end{circus}
    \begin{provs}
      \item $initials(A3) \subseteq cs$
      \item $cs \cap usedC(A1) = \emptyset$
      \item $wrtV(A1) \cap usedV(A3) = \emptyset$
        \item $A3$ is divergence-free
      \item $wrtV(A1) \subseteq ns1$
    \end{provs}
\end{lawn}
TODO: implement proviso

\begin{code}
crl_parSeqStep (CSPNSParal ns1 cs ns2 (CSPSeq a1 a2) a3)
    = (CSPSeq a1 (CSPNSParal ns1 cs ns2 a2 a3))
\end{code}

\begin{lawn}[Hiding/Sequence---distribution$^*$]\sl
    \begin{circus}
      (A1 \circseq\ A2) \circhide cs
      \\ = \\
      (A1 \circhide cs) \circseq\ (A2 \circhide cs)
    \end{circus}
  \label{law:hidingSequenceDistribution}
\end{lawn}

\begin{code}
crl_hidingSequenceDistribution (CSPHide (CSPSeq a1 a2) cs)
    = (CSPSeq (CSPHide a1 cs) (CSPHide a2 cs))
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
crl_guardSeqAssoc (CSPSeq (CSPGuard g a1) a2) = (CSPGuard g (CSPSeq a1 a2))
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
crl_inputPrefixParallelismDistribution2
      (CSPCommAction (ChanComm c [ChanInp x])
          (CSPNSParal ns1 cs ns2 a1 a2))
  = (CSPNSParal ns1 cs ns2
      (CSPCommAction (ChanComm c [ChanInp x]) a1)
      a2)
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
crl_prefixSkip (CSPCommAction (ChanComm c [ChanDotExp x]) a)
  = (CSPSeq (CSPCommAction
              (ChanComm c [ChanDotExp x]) CSPSkip) a)
crl_prefixSkip (CSPCommAction c a)
  = (CSPSeq (CSPCommAction c CSPSkip) a)
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
TODO: implement proviso
\begin{code}
crl_prefixParDist (CSPCommAction (ChanComm cc [])
                    (CSPNSParal ns1 cs ns2 a1 a2))
  = (CSPNSParal
      ns1 (ChanSetUnion cs (CChanSet [cc])) ns2
      (CSPCommAction (ChanComm cc []) a1)
      (CSPCommAction (ChanComm cc []) a2))

crl_prefixParDist (CSPCommAction (ChanComm c [ChanDotExp e])
                    (CSPNSParal ns1 cs ns2 a1 a2))
  = (CSPNSParal
      ns1 (ChanSetUnion cs (CChanSet [c])) ns2
      (CSPCommAction (ChanComm c [ChanDotExp e]) a1)
      (CSPCommAction (ChanComm c [ChanDotExp e]) a2))
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
crl_externalChoiceSequenceDistribution2
      (CSPSeq (CSPExtChoice (CSPGuard g1 a1) (CSPGuard g2 a2)) b)
  = (CSPExtChoice (CSPSeq (CSPGuard g1 a1) b)
                  (CSPSeq (CSPGuard g2 a2) b))
\end{code}
% Law 37 (True guard)
\begin{lawn}[True guard]\sl
    \begin{circus}
      \true \circguard A = A
    \end{circus}
  \label{law:trueGuard}
\end{lawn}
\begin{code}
crl_trueGuard (CSPGuard ZTrue{reason=[]} a)
  = a
\end{code}
% Law 38 (False guard)
\begin{lawn}[False guard]\sl
    \begin{circus}
      \false \circguard A = \Stop
    \end{circus}
  \label{law:falseGuard}
\end{lawn}
\begin{code}
crl_falseGuard (CSPGuard ZFalse{reason=[]} _)
  = CSPStop
\end{code}
% Law 39 (Hiding/$Chaos$---distribution$^*$)
\begin{lawn}[Hiding/$Chaos$---distribution$^*$]\sl
    \begin{circus}
      \Chaos \circhide cs = \Chaos
    \end{circus}
  \label{law:hidingChaos}
\end{lawn}
\begin{code}
crl_hidingChaos (CSPHide CSPChaos _)
  = CSPChaos
\end{code}
Law 40 (Sequence zero 2$^*$)
\begin{lawn}[Sequence zero 2$^*$]\sl
    \begin{circus}
      \Chaos \circseq A = \Chaos
    \end{circus}
  \label{law:seqChaosZero}
\end{lawn}
\begin{code}
crl_seqChaosZero (CSPSeq CSPChaos _)
  = CSPChaos
\end{code}
Law 41 (Parallelism composition Zero$^*$)
\begin{lawn}[Parallelism composition Zero$^*$]\sl
    \begin{circus}
        Chaos \lpar ns1 | cs | ns2 \rpar A = Chaos%
    \end{circus}%
  \label{law:parallelismZero}
\end{lawn}
\begin{code}
crl_parallelismZero (CSPNSParal _ _ _ CSPChaos _)
  = CSPChaos
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
crl_internalChoiceParallelismDistribution (CSPNSParal ns1 cs ns2 (CSPIntChoice a1 a2) a3)
  = (CSPIntChoice
      (CSPNSParal ns1 cs ns2 a1 a3)
      (CSPNSParal ns1 cs ns2 a2 a3))
\end{code}
\begin{code}
--Law 43 (Sequence/Internal choice—distribution)
crl43 (CSPSeq a1 (CSPIntChoice a2 a3))
  = (CSPIntChoice
      (CSPSeq a1 a2)
      (CSPSeq a1 a3))
\end{code}
% Law 44 (Sequence/Internal choice---distribution$^*$)
\begin{lawn}[Sequence/Internal choice---distribution$^*$]\sl
    \begin{circus}
      A1 \circseq\ (A2 \intchoice A3)
      \\ = \\
      (A1 \Semi\ A2) \intchoice (A1 \circseq\ A3)%
    \end{circus}%
  \label{law:sequenceInternalChoiceDistribution}
\end{lawn}
TODO: implement proviso
\begin{code}
crl_sequenceInternalChoiceDistribution
    (CSPHide (CSPNSParal ns1 cs1 ns2 a1 a2) cs2)
  = (CSPNSParal ns1 cs1 ns2
      (CSPHide a1 cs2)
      (CSPHide a2 cs2))
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
crl_hidingCombination (CSPHide (CSPHide a cs1) cs2)
  = (CSPHide a (ChanSetUnion cs1 cs2))
\end{code}
% Law 46 (Parallelism composition Deadlocked 3$^*$)
\begin{lawn}[Parallelism composition Deadlocked 3$^*$]\sl
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
QUESTION: can we interpret $c_i --> A_i$ the same of $c.i --> A(i)$

\begin{code}
crl_parallelismDeadlocked3
  (CSPNSParal ns1 cs ns2
      (CSPRepExtChoice i (CSPCommAction ci ai))
      (CSPRepExtChoice j (CSPCommAction cj aj)))
  = (CSPNSParal ns1 cs ns2 CSPStop
      (CSPRepExtChoice j (CSPCommAction cj aj)))
\end{code}
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
crl_assignmentRemoval (CSPSeq (CActionCommand (CAssign _ e)) (CSPParAction a _))
  = (CSPParAction a e)
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
crl_innocuousAssignment (CActionCommand (CAssign [(x1,[])] [ZVar (x2,[])]))
  = do {case (x1 == x2) of
      True -> CSPSkip
      False -> (CActionCommand (CAssign [(x1,[])] [ZVar (x2,[])]))}
\end{code}
% TODO: implement proviso
\begin{lawn}[Variable Substitution$^*$]\sl
    \begin{circus}
        \circvar x \circspot A(x) = \circvar y \circspot A(y)%
    \end{circus}%
    \begin{prov}
        $y$ is not free in A
        $y$ is not free in A
    \end{prov}

  \label{law:variableSubstitution}
\end{lawn}
TODO: implement proviso

\begin{code}
crl_variableSubstitution2
    (CValDecl [Include (ZSRef (ZSPlain x) [] [])]
        (CSPParAction a [ZVar (x1,[])])) y
  = (CValDecl [Include (ZSRef (ZSPlain y) [] [])]
        (CSPParAction a [ZVar (y,[])]))
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

crl_inputPrefixSequenceDistribution
    (CSPSeq (CSPCommAction (ChanComm c [ChanInp x]) a1) a2 )
  = (CSPCommAction (ChanComm c [ChanInp x]) (CSPSeq a1 a2))
\end{code}
% Law 51 (Input Prefix/Hiding Identity$^*$)
\begin{lawn}[Input Prefix/Hiding Identity$^*$]\sl
    \begin{circus}
        (c?x \then A1) \circseq A2
      \\ = \\
      c?x \then (A1 \circseq A2)
    \end{circus}%
    \begin{provs}
        \item $x \notin FV(A2)$
    \end{provs}
  \label{law:inputPrefixHidIdentity}
\end{lawn}
\begin{code}
crl_inputPrefixHidIdentity
    (CSPSeq (CSPCommAction (ChanComm c [ChanInp x]) a1) a2)
  = (CSPCommAction (ChanComm c [ChanInp x]) (CSPSeq a1 a2))
\end{code}
% Law 52 (Guard/Parallelism composition---distribution$^*$)
\begin{lawn}[Guard/Parallelism composition---distribution$^*$]\sl
    \begin{circus}
     (g \circguard A1) \lpar ns1 | cs | ns2 \rpar A2
      \\ = \\
      g \circguard (A1 \lpar ns1 | cs | ns2 \rpar A2)
    \end{circus}
  \label{law:guardParDist}
\end{lawn}
\begin{code}
crl_guardParDist
    (CSPNSParal ns1 cs ns2 (CSPGuard g a1) a2)
  = (CSPGuard g (CSPNSParal ns1 cs ns2 a1 a2))

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
crl_internalChoiceHidingDistribution
    (CSPHide (CSPIntChoice a1 a2) cs)
  = (CSPIntChoice (CSPHide a1 cs) (CSPHide a2 cs))
\end{code}
% Law 54 (Alternation Zero)
\begin{lawn}[Alternation Zero]\sl
    \begin{circus}
        \circif\ \circelse\ i \circspot g_i \then A_i \ \circfi =\Chaos
    \end{circus}%
    \begin{provs}
        \item $\bigvee_i \circspot\ g_i \equiv false$
    \end{provs}
  \label{law:alternationZero}
\end{lawn}
\begin{code}
crl_alternationZero
  = undefined

\end{code}
% Law 55 (Alternation)
\begin{lawn}[Alternation]\sl
    \begin{circus}
        \circif\ \circelse\ i : S \circspot g_i \then\ A_i \circfi
      \\ = \\
      \Intchoice i: T \circspot A_i%
    \end{circus}%
    \begin{provs}
        \item $T \subseteq S$
        \item $\bigwedge i : T \circspot g_i \equiv \true$
        \item $\bigvee i : S\setminus T \circspot g_i \equiv false$
    \end{provs}
  \label{law:alternation}
\end{lawn}

\begin{code}
crl_alternation
  = undefined

\end{code}
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
crl_assignmentSkip
    (CActionCommand (CValDecl
        [Include (ZSRef (ZSPlain x) [] [])]
        (CActionCommand (CAssign [(x1,[])] [ZVar (e,[])]))))
  = (CActionCommand (CValDecl
        [Include (ZSRef (ZSPlain x) [] [])] CSPSkip))
\end{code}


\subsection{Auxiliary functions from Oliveira's PhD thesis}
Function for $usedC(A)$
\begin{code}
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
\end{code}
\begin{code}
getCommName (ChanComm n _) = n
getCommName (ChanGenComm n _ _) = n

\end{code}
Function used for $initials$
\begin{code}
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
initials CSPSkip = ["tick"]
initials _ = [[]]
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
trace (Com a p)
 = map (a:) (trace p)
trace (Seq a b)
 = (trace a) ++ (trace b)
trace (ExtCh a b)
 = (trace a)++ (trace b)
trace (CSPSkp)
 = [[]]
\end{code}
Function used for $deterministic$
\begin{code}
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
isDeterministic a
  = case x of
      Just "Deterministic" -> "Deterministic"
      Just x               -> "undefined"
      Nothing              -> "Non-deterministic"
    where x = (deterministic a)
\end{code}