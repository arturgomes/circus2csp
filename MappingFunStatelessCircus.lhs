\section{Mapping Functions - Stateless Circus}

Mapping Functions - Stateless Circus
\ignore{
\begin{code}
module MappingFunStatelessCircus
where
import AST
--import CRL
import FormatterToCSP


showexpr = zexpr_string (pinfo_extz 80)
\end{code}
}
\subsection{Stateless Circus - Actions}

\begin{code}
omega_CActions :: CAction -> CAction
omega_CActions CSPSkip = CSPSkip
omega_CActions CSPStop = CSPStop
omega_CActions CSPChaos = CSPChaos
omega_CActions (CSPCommAction x c) = (CSPCommAction x (omega_CActions c))
-- omega_CActions (CSPGuard x c) = (CSPGuard x c)
omega_CActions (CSPSeq ca cb) = (CSPSeq (omega_CActions ca) (omega_CActions cb))
omega_CActions (CSPUnParAction [Choose (x,[]) t] (CSPParAction a [ZVar (x1,[])]) e)
  = case x == x1 of
      True -> (CSPRenAction x [CRename (e,[]) (x,[])])
      _    -> (CSPUnParAction [Choose (x,[]) t] (CSPParAction a [ZVar (x1,[])]) e)
-- omega_CActions (CSPExtChoice ca cb) = (CSPExtChoice (omega_CActions ca) (omega_CActions cb))
omega_CActions (CSPIntChoice ca cb) = (CSPIntChoice (omega_CActions ca) (omega_CActions cb))
omega_CActions (CSPNSParal a b c ca cb) = (CSPNSParal a b c (omega_CActions ca) (omega_CActions cb))
omega_CActions (CSPParal x ca cb) = (CSPParal x (omega_CActions ca) (omega_CActions cb))
omega_CActions (CSPNSInter x y ca cb) = (CSPNSInter x y (omega_CActions ca) (omega_CActions cb))
omega_CActions (CSPInterleave ca cb) = (CSPInterleave (omega_CActions ca) (omega_CActions cb))

omega_CActions (CSPHide c y) = (CSPHide (omega_CActions c) y)

omega_CActions (CSPRecursion x c) = (CSPRecursion x (omega_CActions c))

omega_CActions (CSPRepSeq [Choose (x,[]) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1,[])]))
  = case x == x1 of
      True -> omega_CActions (rep_seq_CActions act xs)
      _    -> (CSPRepSeq [Choose (x,[]) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1,[])]))

omega_CActions (CSPRepExtChoice [Choose (x,[]) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1,[])]))
  = case x == x1 of
      True -> rep_extAct_CActions act xs
      _    -> (CSPRepExtChoice [Choose (x,[]) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1,[])]))
omega_CActions (CSPRepIntChoice [Choose (x,[]) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1,[])]))
  = case x == x1 of
      True -> rep_intAct_CActions act xs
      _    -> (CSPRepIntChoice [Choose (x,[]) (ZSeqDisplay xs)] (CSPParAction act [ZVar (x1,[])]))
omega_CActions (CSPRepParalNS a b x c) = (CSPRepParalNS a b x  (omega_CActions c))
omega_CActions (CSPRepParal a b c) = (CSPRepParal a b  (omega_CActions c))
omega_CActions (CSPRepInterlNS a b c) = (CSPRepInterlNS a b  (omega_CActions c))
omega_CActions (CSPRepInterl a c) = (CSPRepInterl a  (omega_CActions c))
omega_CActions  _ = undefined

rep_seq_CActions a (x:xs) = CSPSeq (CSPParAction a [x]) (rep_seq_CActions a xs)
rep_intAct_CActions a (x:xs) = CSPIntChoice (CSPParAction a [x]) (rep_intAct_CActions a xs)
rep_extAct_CActions a (x:xs) = CSPExtChoice (CSPParAction a [x]) (rep_extAct_CActions a xs)
\end{code}
