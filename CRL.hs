module CRL
where
import AST


--Law 1 (var-exp-par)
-- TODO: implement proviso
crl_01 (CSPNSParal ns1 cs ns2 (CActionCommand (CVarDecl [(Choose d t)] a1)) a2)
	= (CActionCommand (CVarDecl [(Choose d t)] (CSPNSParal ns1 cs ns2 a1 a2)))

-- Law 2 (var-exp-par-2)
crl_02 (CSPNSParal ns1 cs ns2 (CActionCommand (CVarDecl d1 a1)) (CActionCommand (CVarDecl d2 a2)))
	= case (d1 == d2) of _
						| True 			-> (CActionCommand (CVarDecl d1 (CSPNSParal ns1 cs ns2 a1 a2)))
						| otherwise 	-> (CSPNSParal ns1 cs ns2 (CActionCommand (CVarDecl d1 a1)) (CActionCommand (CVarDecl d2 a2)))

-- Law 3(var-exp-rec)
-- TODO: implement proviso
crl_03 (CSPRecursion x1 (CActionCommand (CVarDecl [(Choose xv t)] (CSPParAction f [ZVar (x2,[])]))))
	= case (x1 == x2) of _
						| True 			-> (CActionCommand (CVarDecl [(Choose xv t)]  (CSPRecursion x1 (CSPParAction f [ZVar (x1,[])]))))
						| otherwise 	-> (CSPRecursion x1 (CActionCommand (CVarDecl [(Choose xv t)] (CSPParAction f [ZVar (x2,[])]))))

-- Law 4 (var-exp-seq)
-- \begin{lawn}[Variable block/Sequence---extension$^*$]\sl
--  \begin{law}
--    \begin{circus}
--        A_1 \Semi\ (\circvar\ x:T @ A_2) \Semi\ A_3 = (\circvar\ x:T @ A_1 \Semi\ A_2 \Semi\ A_3) %
--    \end{circus}%
--    \begin{prov}
--        $x \notin FV(A_1) \cup FV(A_3)$
--    \end{prov}

--  \end{law}
--  \label{law:variableBlockSequenceExtension}
-- \end{lawn}
-- TODO: implement proviso
crl_04 (CSPSeq (CSPSeq a1 (CActionCommand (CVarDecl [(Choose x t)] a2))) a3)
	= CActionCommand (CVarDecl [(Choose x t)] (CSPSeq (CSPSeq a1 a2) a3))

--Law 5 (Variable Substitution)
-- \begin{lawn}[Variable Substitution$^*$]\sl
--  \begin{law}
--    \begin{circus}
--        A(x) = \circvar\ y @ y:[y'=x] \Semi\ A(y)%
--    \end{circus}%
--    \begin{prov}
--        $y$ is not free in A
--    \end{prov}
--  \end{law}
--  \label{law:variable-substitution}
-- \end{lawn}
-- TODO: implement proviso


-- Law 6 (Variable block introduction⇤)
-- \begin{lawn}[Variable block introduction$^*$]\sl
--  \begin{law}
--    \begin{circus}
--        A = \circvar\ x:T @ A %
--    \end{circus}%
--    \begin{prov}
--        $x \notin FV(A)$
--    \end{prov}
--  \end{law}
--  \label{law:variableBlockIntroduction}
-- \end{lawn}
-- TODO: implement proviso

crl_06 a x t = CActionCommand (CVarDecl [(Choose x t)] a)

-- Law 7 (join-blocks)
crl_07 (CActionCommand (CVarDecl [(Choose x t1)] (CActionCommand (CVarDecl [(Choose y t2)] a))))
	= (CActionCommand (CVarDecl [(Choose x t1),(Choose y t2)] a))


-- Law 8 (Sequence unit)
-- \begin{lawn}[Sequence unit]\sl
--  \begin{law}
--    \begin{zed}
--      (A) Skip; A \\ %
--      (B) A = A; Skip %
--    \end{zed}
--  \end{law}
--  \label{law:seqSkipUnit}
-- \end{lawn}

crl_08 (CSPSeq CSPSkip a) = a
crl_08 a = (CSPSeq a CSPSkip)

-- Law 9 (Recursion unfold)
	-- \begin{lawn}[Recursion unfold]\sl
	--  \begin{law}
	--    \begin{zed}
	--      \mu X @ F(X) = F(\mu X @ F(X))
	--    \end{zed}
	--  \end{law}
	--  \label{law:recUnfold}
	-- \end{lawn}
-- crl_09 (CSPRecursion x1 (CSPParAction f [ZVar (x2,[])]))
--	= case (x1 == x2) of _
--						| True 			-> (CSPParAction f (CSPRecursion x1 (CSPParAction f [ZVar (x2,[])])))
--						| otherwise 	-> (CSPRecursion x1 (CSPParAction f [ZVar (x2,[])]))

--Law 10 (Parallelism composition/External choice—expansion)
-- \begin{lawn}[Parallelism composition/External choice---expansion$^*$]\sl
--  \begin{law}
--    \begin{circus}
--        (\Extchoice i @ a_i \then A_i) \lpar ns_1 | cs | ns_2 \rpar (\Extchoice j @ b_j \then B_j) \\ %
--        = \\ %
--        (\Extchoice i @ a_i \then A_i) \lpar ns_1 | cs | ns_2 \rpar ((\Extchoice j @ b_j \then B_j) \extchoice (c \then C)) \\ %
--    \end{circus}%
--    provided
--    \begin{itemize}
--        \item $\bigcup_i \{ a_i \} \subseteq cs$
--        \item $c \in cs$ %
--        \item $c \notin \bigcup_i \{ a_i \} $%
--        \item $c \notin \bigcup_j \{ b_j \}$%
--    \end{itemize}

--  \end{law}
--  \label{law:parallelismExternalChoiceExpansion}
-- \end{lawn}
-- crl_10
-- (2 i • ai ! Ai ) |[ ns1 | cs | ns2 ]| (2 j • bj ! Bj )
-- =
-- (2i•ai !Ai)|[ns1|cs|ns2]|((2j•bj !Bj)2(c!C))


-- Law 28 (Parallelism composition unit)
crl_28 (CSPNSParal _ _ _ CSPSkip CSPSkip) = CSPSkip

-- Law 29 (Parallelism composition/Interleaving Equivalence)
crl_29 (CSPNSInter ns1 ns2 a1 a2) = (CSPNSParal ns1 CSEmpty ns2 a1 a2)
crl_29_backwards (CSPNSParal ns1 CSEmpty ns2 a1 a2) = (CSPNSInter ns1 ns2 a1 a2)

-- Law 30 (Parallelism composition/Sequence—step)
-- TODO: implement proviso
crl_30 (CSPNSParal ns1 cs ns2 (CSPSeq a1 a2) a3)
		= (CSPSeq a1 (CSPNSParal ns1 cs ns2 a2 a3))

-- Law 31 (Hiding/Sequence—distribution⇤)
crl_31 (CSPHide (CSPSeq a1 a2) cs) = (CSPSeq (CSPHide a1 cs) (CSPHide a2 cs))

-- Law 32 (Guard/Sequence—associativity)
crl_32 (CSPSeq (CSPGuard g a1) a2) = (CSPGuard g (CSPSeq a1 a2))

-- Law 33 (Input prefix/Parallelism composition—distribution 2⇤)
-- TODO: implement proviso
crl_33 (CSPCommAction (ChanComm c [ChanInp x]) (CSPNSParal ns1 cs ns2 a1 a2))
	= (CSPNSParal ns1 cs ns2 (CSPCommAction (ChanComm c [ChanInp x]) a1) a2)

-- Law 34 (Prefix/Skip⇤)
crl_34 (CSPCommAction (ChanComm c [ChanDotExp x]) a) = (CSPSeq (CSPCommAction (ChanComm c [ChanDotExp x]) CSPSkip) a)
crl_34 (CSPCommAction c a) = (CSPSeq (CSPCommAction c CSPSkip) a)

-- Law 35 (Prefix/Parallelism composition—distribution)
-- TODO: implement proviso
crl_35 (CSPCommAction (ChanComm cc []) (CSPNSParal ns1 cs ns2 a1 a2))
	= (CSPNSParal
			ns1 (ChanSetUnion cs (CChanSet [cc])) ns2
			(CSPCommAction (ChanComm cc []) a1)
			(CSPCommAction (ChanComm cc []) a2))

crl_35 (CSPCommAction (ChanComm c [ChanDotExp e]) (CSPNSParal ns1 cs ns2 a1 a2))
	= (CSPNSParal
			ns1 (ChanSetUnion cs (CChanSet [c])) ns2
			(CSPCommAction (ChanComm c [ChanDotExp e]) a1)
			(CSPCommAction (ChanComm c [ChanDotExp e]) a2))

-- Law 36 (External choice/Sequence—distribution 2⇤)
-- TODO: implement proviso
crl_36 (CSPSeq (CSPExtChoice (CSPGuard g1 a1) (CSPGuard g2 a2)) b)
	= (CSPExtChoice (CSPSeq (CSPGuard g1 a1) b) (CSPSeq (CSPGuard g2 a2) b))

-- Law 37 (True guard)
crl_37 (CSPGuard ZTrue{reason=[]} a) = a

-- Law 38 (False guard)
crl_38 (CSPGuard ZFalse{reason=[]} _) = CSPStop

-- Law 39 (Hiding/Chaos–distribution)
crl_39 (CSPHide CSPChaos _) = CSPChaos

-- Law 40 (Sequence zero 2)
crl_40 (CSPSeq CSPChaos _) = CSPChaos

-- Law 41 (Parallelism composition Zero)
crl_41 (CSPNSParal _ _ _ CSPChaos _) = CSPChaos

-- Law 42 (Internal choice/Parallelism composition Distribution)
crl_42 (CSPNSParal ns1 cs ns2 (CSPIntChoice a1 a2) a3)
	= (CSPIntChoice (CSPNSParal ns1 cs ns2 a1 a3) (CSPNSParal ns1 cs ns2 a2 a3))

--Law 43 (Sequence/Internal choice—distribution)
crl_43 (CSPSeq a1 (CSPIntChoice a2 a3))
	= (CSPIntChoice (CSPSeq a1 a2) (CSPSeq a1 a3))

--Law 44 (Hiding/Parallelism composition—distribution⇤)
-- TODO: implement proviso
crl_44 (CSPHide (CSPNSParal ns1 cs1 ns2 a1 a2) cs2)
	=  (CSPNSParal ns1 cs1 ns2 (CSPHide a1 cs2) (CSPHide a2 cs2))

--Law 45 (Hiding combination)
crl_45 (CSPHide (CSPHide a cs1) cs2)
	= (CSPHide a (ChanSetUnion cs1 cs2))

-- Law 47 (Assignment Removal⇤)
-- TODO: implement proviso
crl_47 (CSPSeq (CActionCommand (CAssign _ e)) (CSPParAction a _))
	= (CSPParAction a e)

-- Law 48 (Innocuous Assignment⇤)
crl_48 (CActionCommand (CAssign [(x1,[])] [ZVar (x2,[])]))
	= do {case (x1 == x2) of _
						| True -> CSPSkip
						| otherwise -> (CActionCommand (CAssign [(x1,[])] [ZVar (x2,[])]))}

-- Law 50 (Input Prefix/Sequence Distribution⇤)
-- TODO: implement proviso
crl_50 (CSPSeq (CSPCommAction (ChanComm c [ChanInp x]) a1) a2 )
	= (CSPCommAction (ChanComm c [ChanInp x]) (CSPSeq a1 a2))

--Law 51 (Input Prefix/Hiding Identity⇤)
--crl_51

-- Law 56 (Assignment Skip)
-- crl_56 (CActionCommand (CVarDecl [(Choose x t)] (CActionCommand (CAssign [(x1,[])] [ZVar (e,[])]))))
--	= do {case (x == (ZVar x1)) of _
--							| True -> (CActionCommand (CVarDecl [(Choose x t)] CSPSkip))
--							| otherwise -> (CActionCommand (CVarDecl x (CActionCommand (CAssign [(x1,[])] [ZVar (e,[])]))))}


