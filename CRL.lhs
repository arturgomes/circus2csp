\section{Introduction}

This is a trivial program that prints the first 20 factorials.
\ignore{
\begin{code}
module CRL
where
import AST

\end{code}
}

Law 1 (var-exp-par) - TODO: implement proviso
TODO: implement proviso
% \begin{lawn}[var-exp-par^*$]\sl
%   \begin{law}
%     \begin{circus}
%         (\circvar\ d:T @ A_1) \lpar ns_1 | cs | ns_2 \rpar A_2 \\ %
%         = \\ %
%         (\circvar\ d:T @ A_1 \lpar ns_1 | cs | ns_2 \rpar A_2) %
%     \end{circus}%
%     \begin{prov}
%         $\{d,d'\} \cap FV(A_2) = \emptyset$
%     \end{prov}

%   \end{law}
%   \label{law:var-exp-par}
% \end{lawn}
\begin{code}
crl_var_exp_par (CSPNSParal ns1 cs ns2 (CActionCommand (CVarDecl [(Choose d t)] a1)) a2)
  = (CActionCommand (CVarDecl [(Choose d t)] (CSPNSParal ns1 cs ns2 a1 a2)))
\end{code}
Law 2 (var-exp-par-2)

% \begin{lawn}[var-exp-par^*$]\sl
%   \begin{law}
%     \begin{circus}
%         (\circvar\ d:T @ A_1) \lpar ns_1 | cs | ns_2 \rpar (\circvar\ d:T @ A_2) \\ %
%         = \\ %
%         (\circvar\ d:T @ A_1 \lpar ns_1 | cs | ns_2 \rpar A_2) %
%     \end{circus}%
%     \begin{prov}
%         $\{d,d'\} \cap FV(A_2) = \emptyset$
%     \end{prov}

%   \end{law}
%   \label{law:var-exp-par}
% \end{lawn}
\begin{code}
crl_var_exp_par_2 (CSPNSParal ns1 cs ns2 (CActionCommand (CVarDecl d1 a1)) (CActionCommand (CVarDecl d2 a2)))
  = case (d1 == d2) of _
                        | True       -> (CActionCommand (CVarDecl d1 (CSPNSParal ns1 cs ns2 a1 a2)))
                        | otherwise   -> (CSPNSParal ns1 cs ns2 (CActionCommand (CVarDecl d1 a1)) (CActionCommand (CVarDecl d2 a2)))
\end{code}
 Law 3 - (var-exp-rec)
 TODO: implement proviso
\begin{code}
crl_var_exp_rec (CSPRecursion x1 (CActionCommand (CVarDecl [(Choose xv t)] (CSPParAction f [ZVar (x2,[])]))))
  = case (x1 == x2) of _
                        | True       -> (CActionCommand (CVarDecl [(Choose xv t)]  (CSPRecursion x1 (CSPParAction f [ZVar (x1,[])]))))
                        | otherwise   -> (CSPRecursion x1 (CActionCommand (CVarDecl [(Choose xv t)] (CSPParAction f [ZVar (x2,[])]))))
\end{code}
Law 4 (var-exp-seq)
% \begin{lawn}[Variable block/Sequence---extension$^*$]\sl
%  \begin{law}
%    \begin{circus}
%        A_1 \Semi\ (\circvar\ x:T @ A_2) \Semi\ A_3 = (\circvar\ x:T @ A_1 \Semi\ A_2 \Semi\ A_3) %
%    \end{circus}%
%    \begin{prov}
%        $x \notin FV(A_1) \cup FV(A_3)$
%    \end{prov}

%  \end{law}
%  \label{law:variableBlockSequenceExtension}
% \end{lawn}
TODO: implement proviso
\begin{code}
crl_variableBlockSequenceExtension (CSPSeq (CSPSeq a1 (CActionCommand (CVarDecl [(Choose x t)] a2))) a3) 
  = CActionCommand (CVarDecl [(Choose x t)] (CSPSeq (CSPSeq a1 a2) a3))
\end{code}
Law 5 (Variable Substitution) TODO
% \begin{lawn}[Variable Substitution$^*$]\sl
%  \begin{law}
%    \begin{circus}
%        A(x) = \circvar\ y @ y:[y'=x] \Semi\ A(y)%
%    \end{circus}%
%    \begin{prov}
%        $y$ is not free in A
%    \end{prov}
%  \end{law}
%  \label{law:variableSubstitution}
% \end{lawn}
TODO: implement proviso
\begin{code}
crl_variableSubstitution (CSPParAction a exp)
-- = CVarDecl [(ZVar ("y",[]))] (CSPSeq (CActionCommand (CAssumpt [("y")] ZTrue{reason=[]} )))
  = undefined
\end{code}
Law 6 (Variable block introduction)
% \begin{lawn}[Variable block introduction$^*$]\sl
%  \begin{law}
%    \begin{circus}
%        A = \circvar\ x:T @ A %
%    \end{circus}%
%    \begin{prov}
%        $x \notin FV(A)$
%    \end{prov}
%  \end{law}
%  \label{law:variableBlockIntroduction}
% \end{lawn}
TODO: implement proviso
\begin{code}
crl_variableBlockIntroduction a x t = CActionCommand (CVarDecl [(Choose x t)] a)
\end{code}
\begin{code}
crl_07 (CActionCommand (CVarDecl [(Choose x t1)] (CActionCommand (CVarDecl [(Choose y t2)] a))))
  = (CActionCommand (CVarDecl [(Choose x t1),(Choose y t2)] a))
\end{code}
Law 8 (Sequence unit)
% \begin{lawn}[Sequence unit]\sl
%  \begin{law}
%    \begin{zed}
%      (A) Skip; A \\ %
%      (B) A = A; Skip %
%    \end{zed}
%  \end{law}
%  \label{law:seqSkipUnit}
% \end{lawn}
\begin{code}
crl_seqSkipUnit_a (CSPSeq CSPSkip a) = a
crl_seqSkipUnit_b a = (CSPSeq a CSPSkip)
\end{code}
Law 9 (Recursion unfold)
% \begin{lawn}[Recursion unfold]\sl
%  \begin{law}
%    \begin{zed}
%      \mu X @ F(X) = F(\mu X @ F(X))
%    \end{zed}
%  \end{law}
%  \label{law:recUnfold}
% \end{lawn}
\begin{code}
crl_recUnfold (CSPRecursion x1 (CSPParAction f [ZVar (x2,[])]))
  -- = case (x1 == x2) of _
  --                       | True         -> (CSPParAction f (CSPRecursion x1 (CSPParAction f [ZVar (x2,[])])))
  --                       | otherwise    -> (CSPRecursion x1 (CSPParAction f [ZVar (x2,[])]))
  = undefined
\end{code}
Law 10 (Parallelism composition/External choice—expansion)
% \begin{lawn}[Parallelism composition/External choice---expansion$^*$]\sl
%  \begin{law}
%    \begin{circus}
%        (\Extchoice i @ a_i \then A_i) \lpar ns_1 | cs | ns_2 \rpar (\Extchoice j @ b_j \then B_j) \\ %
%        = \\ %
%        (\Extchoice i @ a_i \then A_i) \lpar ns_1 | cs | ns_2 \rpar ((\Extchoice j @ b_j \then B_j) \extchoice (c \then C)) \\ %
%    \end{circus}%
%    provided
%    \begin{itemize}
%        \item $\bigcup_i \{ a_i \} \subseteq cs$
%        \item $c \in cs$ %
%        \item $c \notin \bigcup_i \{ a_i \} $%
%        \item $c \notin \bigcup_j \{ b_j \}$%
%    \end{itemize}

%  \end{law}
%  \label{law:parallelismExternalChoiceExpansion}
% \end{lawn}
TODO: implement proviso
\begin{code}
crl_parallelismExternalChoiceExpansion (CSPNSParal ns1 cs ns2 (CSPRepExtChoice i (CSPCommAction ai aAi)) (CSPRepExtChoice j (CSPCommAction bj aBj))) c aC
  = (CSPNSParal ns1 cs ns2 (CSPRepExtChoice i (CSPCommAction ai aAi)) (CSPExtChoice (CSPRepExtChoice j (CSPCommAction bj aBj)) (CSPCommAction c aC)))
\end{code}
Law 11 (Parallelism composition introduction 1$^*$)
% \begin{lawn}[Parallelism composition introduction 1$^*$]\sl
%   \begin{law}
%     \begin{circus}
%         c \then A = (c \then A \lpar ns_1 | \lchanset c \rchanset | ns_2 \rpar c \then Skip)%
%         \also
%         c.e \then A = (c.e \then A \lpar ns_1 | \lchanset c \rchanset | ns_2 \rpar c.e \then Skip)%
%     \end{circus}%
%     \begin{provs}
%         \item $c \notin usedC(A)$
%         \item $wrtV(A) \subseteq ns_1$
%     \end{provs}

%   \end{law}
%   \label{law:parallelismIntroduction1}
% \end{lawn}
\begin{code}
crl_parallelismIntroduction1a (CSPCommAction c a) ns1 cs ns2
  = (CSPNSParal ns1 (CChanSet cs) ns2 (CSPCommAction c a) (CSPCommAction c CSPSkip))
crl_parallelismIntroduction1b (CSPCommAction (ChanComm c [ChanDotExp e]) a)  ns1 cs ns2
  = (CSPNSParal ns1 (CChanSet cs) ns2 (CSPCommAction (ChanComm c [ChanDotExp e]) a) (CSPCommAction (ChanComm c [ChanDotExp e]) CSPSkip))
\end{code}
Law 12 (Channel extension 1)

% \begin{lawn}[Channel extension 1]\sl\label{law:chanExt1}
%   \begin{law}
%     \begin{zed}
%       A_1 \lpar ns_1 | cs | ns_2 \rpar A_2 = A_1 \lpar ns_1 | cs \cup \lchan c \rchan | ns_2 \rpar A_2%
%     \end{zed}
%     \begin{prov}
%       $c \notin usedC(A_1) \cup usedC(A_2)$
%     \end{prov}
%   \end{law}
% \end{lawn}
\begin{code}
crl_chanExt1  = undefined
\end{code}
Law 13 (Hiding expansion 2$^*$)
% \begin{lawn}[Hiding expansion 2$^*$]\sl
%   \begin{law}
%     \begin{zed}
%       A \hide cs = A \hide cs \cup \{ c \}
%     \end{zed}
%     \begin{prov} $c \notin usedC(A)$ \end{prov}

%   \end{law}
%   \label{law:hidingExpansion2}
% \end{lawn}
\begin{code}
crl_hidingExpansion2 = undefined
\end{code}
Law 14 (Prefix/Hiding$^*$)
% \begin{lawn}[Prefix/Hiding$^*$]\sl
%   \begin{law}
%     \begin{circus}
%         (c \then Skip) \hide \{ c \} = Skip%
%         \also
%         (c.e \then Skip) \hide \{ c \} = Skip%
%     \end{circus}%
%   \end{law}
%   \label{law:prefixHiding}
% \end{lawn}
\begin{code}
crl_prefixHiding = undefined
\end{code}
Law 15 (Hiding Identity$^*$)
% \begin{lawn}[Hiding Identity$^*$]\sl
%   \begin{law}
%     \begin{zed}
%       A \hide cs = A
%     \end{zed}
%     \begin{prov} $cs \cap usedC(A) = \emptyset$ \end{prov}
%   \end{law}
%   \label{law:hidingIdentity}
% \end{lawn}
\begin{code}
crl_hidingIdentity = undefined
\end{code}
Law 16 (Parallelism composition/External choice---exchange)
% \begin{lawn}[Parallelism composition/External choice---exchange]\sl\label{law:parExtChoiceExchange}
%   \begin{law}
%     \begin{zed}
%       (A_1 \lpar ns_1 | cs | ns_2 \rpar A_2) \extchoice (B_1 \lpar ns_1 | cs | ns_2 \rpar B_2) \\%
%       = \\
%       (A_1 \extchoice B_1) \lpar ns_1 | cs | ns_2\rpar (A_2 \extchoice B_2)
%     \end{zed}
%     \begin{prov} $A_1 \lpar ns_1 | cs | ns_2 \rpar B_2 = A_2 \lpar ns_1 | cs | ns_2 \rpar B_1 = Stop$
%     \end{prov}

%   \end{law}
% \end{lawn}
\begin{code}
crl_parExtChoiceExchange = undefined
\end{code}
Law 17 (Parallelism composition/External choice---distribution$^*$)
% \begin{lawn}[Parallelism composition/External choice---distribution$^*$]\sl
% \begin{law}
%   \begin{circus}
%       \Extchoice i @ (A_i \lpar ns_1 | cs | ns_2 \rpar A) = (\Extchoice i @ A_i) \lpar ns_1 | cs | ns_2 \rpar A
%   \end{circus}%
%   \begin{provs}
%       \item $initials(A) \subseteq cs$ %
%       \item $A$ is deterministic %
%   \end{provs}

% \end{law}
% \label{law:parallelismExternalChoiceDistribution}
% \end{lawn}
\begin{code}
crl_parallelismExternalChoiceDistribution = undefined
\end{code}
Law 18 (External choice unit)
% \begin{lawn}[External choice unit]\sl
%   \begin{law}
%     \begin{zed}
%       Stop \extchoice A = A
%     \end{zed}
%   \end{law}
%   \label{law:extChoiceStopUnit}
% \end{lawn}
\begin{code}
crl_extChoiceStopUnit = undefined
\end{code}
Law 19 (External choice/Sequence---distribution)
% \begin{lawn}[External choice/Sequence---distribution]\sl
%   \begin{law}
%     \begin{zed}
%       (\Extchoice i @ g_i \guard c_i \then A_i); B = \Extchoice i @ g_i \guard c_i \then A_i; B%
%     \end{zed}
%   \end{law}
%   \label{law:extChoiceSeqDist}
% \end{lawn}
\begin{code}
crl_extChoiceSeqDist = undefined
\end{code}
Law 20 (Hiding/External choice---distribution$^*$)
% \begin{lawn}[Hiding/External choice---distribution$^*$]\sl
%   \begin{law}
%     \begin{zed}
%       (A_1 \extchoice A_2) \hide cs = (A_1 \hide cs) \extchoice (A_2 \hide cs)
%     \end{zed}
%     \begin{prov} $(initials(A_1) \cup initials(A_2)) \cap cs = \emptyset$ \end{prov}
%   \end{law}
%   \label{law:hidingExternalChoiceDistribution}
% \end{lawn}
\begin{code}
crl_hidingExternalChoiceDistribution = undefined
\end{code}
Law 21 (Hiding/External choice---distribution$^*$)
% \begin{lawn}[Parallelism composition Deadlocked 1$^*$]\sl
%   \begin{law}
%     \begin{circus}
%         (c_1 \then A_1) \lpar ns_1 | cs | ns_2 \rpar (c_2 \then A_2)
%         = Stop %
%         = Stop \lpar ns_1 | cs | ns_2 \rpar (c_2 \then A_2)
%     \end{circus}%
%     \begin{provs}
%         \item $c_1 \neq c_2$
%         \item $\{c_1,c_2\} \subseteq cs$
%     \end{provs}

%   \end{law}
%   \label{law:parallelismDeadlocked1}
% \end{lawn}
\begin{code}
crl_parallelismDeadlocked1 = undefined
\end{code}
Law 22 (Sequence zero)
% \begin{lawn}[Sequence zero]\sl
%   \begin{law}
%     \begin{zed}
%       Stop; A = Stop
%     \end{zed}
%   \end{law}
%   \label{law:seqStopZero}
% \end{lawn}
\begin{code}
crl_seqStopZero = undefined
\end{code}
Law 23 (Communication/Parallelism composition---distribution)
% \begin{lawn}[Communication/Parallelism composition---distribution]\sl
%   \begin{law}
%     \begin{zed}
%       (c!e \then A_1) \lpar ns_1 | cs | ns_2 \rpar (c?x \then A_2(x)) = c.e \then (A_1 \lpar ns_1 | cs | ns_2 \rpar A_2(e)) %
%     \end{zed}
%     \begin{provs}
%         \item $c \in cs$
%         \item $x \notin FV(A_2)$.
%     \end{provs}
%   \end{law}
%   \label{law:communicationParallelismDistribution}
% \end{lawn}
\begin{code}
crl_communicationParallelismDistribution = undefined
\end{code}
Law 24 (Channel extension 3$^*$)
% \begin{lawn}[Channel extension 3$^*$]\sl
%   \begin{law}
%     \begin{circus}
%         (A_1 \lpar ns_1 | cs_1 | ns_2 \rpar A_2(e)) \hide cs_2 \\ %
%         = \\ %
%         ((c!e \then A_1) \lpar ns_1 | cs_1 | ns_2 \rpar (c?x \then A_2(x))) \hide cs_2 %
%     \end{circus}%
%     \begin{provs}
%         \item $c \in cs_1$
%         \item $c \in cs_2$
%         \item $x \notin FV(A_2)$
%     \end{provs}

%   \end{law}
%   \label{law:channelExtension3}
% \end{lawn}
\begin{code}
crl_channelExtension3 = undefined
\end{code}
Law 25 (Channel extension 4$^*$)
% \begin{lawn}[Channel extension 4$^*$]\sl
%   \begin{law}
%     \begin{circus}
%         (A_1 \lpar ns_1 | cs_1 | ns_2 \rpar A_2) \hide cs_2 = ((c \then A_1) \lpar ns_1 | cs_1 | ns_2 \rpar (c \then A_2)) \hide cs_2%
%         \also
%         (A_1 \lpar ns_1 | cs_1 | ns_2 \rpar A_2) \hide cs_2 = ((c.e \then A_1) \lpar ns_1 | cs_1 | ns_2 \rpar (c.e \then A_2)) \hide cs_2%
%     \end{circus}%
%     \begin{provs}
%         \item $c \in cs_1$%
%         \item $c \in cs_2$%
%     \end{provs}

%   \end{law}
%   \label{law:channelExtension4}
% \end{lawn}
\begin{code}
crl_channelExtension4 = undefined
\end{code}
Law 26 (prom-var-state)
\begin{code}
crl_promVarState (ProcMain (ZSchemaDef st (ZSchema exsc)) [CParAction lact (ParamActionDecl (xt:zvar1) act)] (CActionCommand (CValDecl [xt1] mact)))
  = (ProcMain (ZSchemaDef st (ZS2 ZSAnd (ZSchema exsc) (ZSchema [xt]))) [CParAction lact act] mact)
\end{code}
Law 27 (prom-var-state-2)
\begin{code}
crl_promVarState2 (ProcStalessMain [CParAction lact (ParamActionDecl (at:zvar1) act)] (CActionCommand (CValDecl [xt] mact))) st
  = (ProcMain (ZSchemaDef st (ZSchema [xt])) [CParAction lact act] mact)
\end{code}
Law 28 (Parallelism composition unit)

\begin{code}

crl_28 (CSPNSParal _ _ _ CSPSkip CSPSkip) = CSPSkip
\end{code}
\begin{code}
-- Law 29 (Parallelism composition/Interleaving Equivalence)
crl_29 (CSPNSInter ns1 ns2 a1 a2) = (CSPNSParal ns1 CSEmpty ns2 a1 a2)
crl_29_backwards (CSPNSParal ns1 CSEmpty ns2 a1 a2) = (CSPNSInter ns1 ns2 a1 a2)
\end{code}
\begin{code}
-- Law 30 (Parallelism composition/Sequence—step)
-- TODO: implement proviso
crl_30 (CSPNSParal ns1 cs ns2 (CSPSeq a1 a2) a3)
    = (CSPSeq a1 (CSPNSParal ns1 cs ns2 a2 a3))
\end{code}
\begin{code}
-- Law 31 (Hiding/Sequence—distribution⇤)
crl_31 (CSPHide (CSPSeq a1 a2) cs) = (CSPSeq (CSPHide a1 cs) (CSPHide a2 cs))
\end{code}
\begin{code}
-- Law 32 (Guard/Sequence—associativity)
crl_32 (CSPSeq (CSPGuard g a1) a2) = (CSPGuard g (CSPSeq a1 a2))
\end{code}
\begin{code}
-- Law 33 (Input prefix/Parallelism composition—distribution 2⇤)
-- TODO: implement proviso
crl_33 (CSPCommAction (ChanComm c [ChanInp x]) (CSPNSParal ns1 cs ns2 a1 a2))
  = (CSPNSParal ns1 cs ns2 (CSPCommAction (ChanComm c [ChanInp x]) a1) a2)
\end{code}
\begin{code}
-- Law 34 (Prefix/Skip⇤)
crl_34 (CSPCommAction (ChanComm c [ChanDotExp x]) a) = (CSPSeq (CSPCommAction (ChanComm c [ChanDotExp x]) CSPSkip) a)
crl_34 (CSPCommAction c a) = (CSPSeq (CSPCommAction c CSPSkip) a)
\end{code}
\begin{code}
-- Law 35 (Prefix/Parallelism composition—distribution)
-- TODO: implement proviso
crl_35 (CSPCommAction (ChanComm cc []) (CSPNSParal ns1 cs ns2 a1 a2))
  = (CSPNSParal
      ns1 (ChanSetUnion cs (CChanSet [cc])) ns2
      (CSPCommAction (ChanComm cc []) a1)
      (CSPCommAction (ChanComm cc []) a2))
\end{code}
\begin{code}
crl_35 (CSPCommAction (ChanComm c [ChanDotExp e]) (CSPNSParal ns1 cs ns2 a1 a2))
  = (CSPNSParal
      ns1 (ChanSetUnion cs (CChanSet [c])) ns2
      (CSPCommAction (ChanComm c [ChanDotExp e]) a1)
      (CSPCommAction (ChanComm c [ChanDotExp e]) a2))
\end{code}
\begin{code}
-- Law 36 (External choice/Sequence—distribution 2⇤)
-- TODO: implement proviso
crl_36 (CSPSeq (CSPExtChoice (CSPGuard g1 a1) (CSPGuard g2 a2)) b)
  = (CSPExtChoice (CSPSeq (CSPGuard g1 a1) b) (CSPSeq (CSPGuard g2 a2) b))
\end{code}
\begin{code}
-- Law 37 (True guard)
crl_37 (CSPGuard ZTrue{reason=[]} a) = a
\end{code}
\begin{code}
-- Law 38 (False guard)
crl_38 (CSPGuard ZFalse{reason=[]} _) = CSPStop
\end{code}
\begin{code}
-- Law 39 (Hiding/Chaos–distribution)
crl_39 (CSPHide CSPChaos _) = CSPChaos
\end{code}
\begin{code}
-- Law 40 (Sequence zero 2)
crl_40 (CSPSeq CSPChaos _) = CSPChaos
\end{code}
\begin{code}
-- Law 41 (Parallelism composition Zero)
crl_41 (CSPNSParal _ _ _ CSPChaos _) = CSPChaos
\end{code}
\begin{code}
-- Law 42 (Internal choice/Parallelism composition Distribution)
crl_42 (CSPNSParal ns1 cs ns2 (CSPIntChoice a1 a2) a3)
  = (CSPIntChoice (CSPNSParal ns1 cs ns2 a1 a3) (CSPNSParal ns1 cs ns2 a2 a3))
\end{code}
\begin{code}
--Law 43 (Sequence/Internal choice—distribution)
crl_43 (CSPSeq a1 (CSPIntChoice a2 a3))
  = (CSPIntChoice (CSPSeq a1 a2) (CSPSeq a1 a3))
\end{code}
\begin{code}
--Law 44 (Hiding/Parallelism composition—distribution⇤)
-- TODO: implement proviso
crl_44 (CSPHide (CSPNSParal ns1 cs1 ns2 a1 a2) cs2)
  =  (CSPNSParal ns1 cs1 ns2 (CSPHide a1 cs2) (CSPHide a2 cs2))
\end{code}
\begin{code}
--Law 45 (Hiding combination)
crl_45 (CSPHide (CSPHide a cs1) cs2)
  = (CSPHide a (ChanSetUnion cs1 cs2))
\end{code}
\begin{code}
-- Law 47 (Assignment Removal⇤)
-- TODO: implement proviso
crl_47 (CSPSeq (CActionCommand (CAssign _ e)) (CSPParAction a _))
  = (CSPParAction a e)
\end{code}
\begin{code}
-- Law 48 (Innocuous Assignment⇤)
crl_48 (CActionCommand (CAssign [(x1,[])] [ZVar (x2,[])]))
  = do {case (x1 == x2) of _
                            | True -> CSPSkip
                            | otherwise -> (CActionCommand (CAssign [(x1,[])] [ZVar (x2,[])]))}
\end{code}
\begin{code}
-- Law 50 (Input Prefix/Sequence Distribution⇤)
-- TODO: implement proviso
crl_50 (CSPSeq (CSPCommAction (ChanComm c [ChanInp x]) a1) a2 )
  = (CSPCommAction (ChanComm c [ChanInp x]) (CSPSeq a1 a2))
\end{code}
\begin{code}
--Law 51 (Input Prefix/Hiding Identity⇤)
--crl_51
\end{code}
\begin{code}
-- Law 56 (Assignment Skip)
-- crl_56 (CActionCommand (CVarDecl [(Choose x t)] (CActionCommand (CAssign [(x1,[])] [ZVar (e,[])]))))
--  = do {case (x == (ZVar x1)) of _
--              | True -> (CActionCommand (CVarDecl [(Choose x t)] CSPSkip))
--              | otherwise -> (CActionCommand (CVarDecl x (CActionCommand (CAssign [(x1,[])] [ZVar (e,[])]))))}


\end{code}
