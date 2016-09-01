\section{Mapping Functions - Stateless Circus --  File: MappingFunStatelessCircus.lhs}

Mapping Functions - Stateless Circus
\ignore{
\begin{code}
module MappingFunStatelessCircus
where
import AST
--import CRL
import FormatterToCSP
import DefSets

showexpr = zexpr_string (pinfo_extz 80)
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
omega_CActions :: CAction -> CAction
omega_CActions CSPSkip = CSPSkip
omega_CActions CSPStop = CSPStop
omega_CActions CSPChaos = CSPChaos
\end{code}

\begin{circus}
\Omega_A (c \then A) \circdef c \then \Omega_A (A)
\end{circus}

is written in Haskell as:
\begin{code}
omega_CActions (CSPCommAction (ChanComm c []) a)
  = (CSPCommAction (ChanComm c []) (omega_CActions a))
\end{code}

\begin{circus}
\Omega_A (c.e(v_0,\ldots,v_n,l_0,\ldots,l_n) \then A) \circdef
\\\t2 get.v_0?vv_0 \then \ldots \then get.v_n?vv_n \then
\\\t2 get.l_0?vl_0 \then \ldots \then get.l_n?vl_n \then
\\\t2 c.e(vv_0,\ldots,vv_n,vl_0,\ldots,vl_n) \then \Omega'_{A} (A)
\end{circus}
where
\begin{circus}
FV (e) = (v_0,\ldots,v_n,l_0,\ldots,l_n)
\end{circus}

is written in Haskell as:
\begin{code}
omega_CActions (CSPCommAction (ChanComm c [ChanDotExp e]) a)
  = make_get_com lxs (CSPCommAction (ChanComm c [ChanDotExp e]) (omega_prime_CActions a))
  where lxs = free_var_ZExpr(e)
\end{code}
\begin{circus}
\Omega_A (c!e(v_0,\ldots,v_n,l_0,\ldots,l_n) \then A) \circdef
\\\t2 c.e(v_0,\ldots,v_n,l_0,\ldots,l_n) \then A
\end{circus}
\begin{code}
omega_CActions (CSPCommAction (ChanComm c [ChanOutExp e]) a)
  = omega_CActions (CSPCommAction (ChanComm c [ChanDotExp e]) a)
\end{code}

\begin{circus}
\Omega_A (g(v_0,\ldots,v_n,l_0,\ldots,l_n) \then A) \circdef
\\\t2 get.v_0?vv_0 \then \ldots \then get.v_n?vv_n \then
\\\t2 get.l_0?vl_0 \then \ldots \then get.l_n?vl_n \then
\\\t2 g(vv_0,\ldots,vv_n,vl_0,\ldots,vl_n) \circguard \Omega'_{A} (A)
\end{circus}
is written in Haskell as:
\begin{code}
omega_CActions (CSPGuard g a)
  = make_get_com lxs (CSPGuard g (omega_prime_CActions a))
  where lxs = free_var_ZPred(g)
\end{code}

\begin{circus}
\Omega_A (c?x : P(x,v_0,\ldots,v_n,l_0,\ldots,l_n) \then A) \circdef
\\\t2 get.v_0?vv_0 \then \ldots \then get.v_n?vv_n \then
\\\t2 get.l_0?vl_0 \then \ldots \then get.l_n?vl_n \then
\\\t2 c?x : P(x,vv_0,\ldots,vv_n,vl_0,\ldots,vl_n) \then \Omega'_{A} (A)
\end{circus}
where
\begin{circus}
x \in wrtV(A)
\end{circus}

is written in Haskell as:
\begin{code}
omega_CActions (CSPCommAction (ChanComm c [ChanInpPred x p]) a)
  = case notinSet x (getWrtV(a)) of
      True -> make_get_com lsx (CSPCommAction (ChanComm c [ChanInpPred x p])
                                (omega_prime_CActions a))
      _    -> (CSPCommAction (ChanComm c [ChanInpPred x p]) a)
  where lsx = free_var_ZExpr(p)
\end{code}


\begin{circus}
\Omega_A (A_1 \circseq A_2) \circdef \Omega_A (A_1) \circseq \Omega_A (A_2)
\end{circus}
is written in Haskell as:
\begin{code}
omega_CActions (CSPSeq ca cb)
  = (CSPSeq (omega_CActions ca) (omega_CActions cb))
\end{code}

\begin{circus}
\Omega_A (A_1 \intchoice A_2) \circdef \Omega_A (A_1) \intchoice \Omega_A (A_2)
\end{circus}
is written in Haskell as:
\begin{code}
omega_CActions (CSPIntChoice ca cb)
  = (CSPIntChoice (omega_CActions ca) (omega_CActions cb))
\end{code}

TODO: I need to somehow calculate the $FV(A_1)$ and $FV(A_2)$.
What should I do?
\begin{circus}
\Omega_A (A_1 \extchoice A_2) \circdef
\\\t1 get.v_0?vv_0 \then \ldots \then get.v_n?vv_n \then
\\\t1 get.l_0?vl_0 \then \ldots \then get.l_n?vl_n \then
\\\t2 (\Omega'_A (A_1) \extchoice \Omega'_A (A_2))
\end{circus}
is written in Haskell as:
\begin{code}
omega_CActions (CSPExtChoice ca cb)
  = undefined
\end{code}

% \begin{circus}
% \Omega_A (c \then A) \circdef c \then \Omega_A (A)
% \end{circus}
% is written in Haskell as:
% \begin{code}
% omega_CActions (CSPUnParAction [Choose (x,[]) t] (CSPParAction a [ZVar (x1,[])]) e)
%   = case x == x1 of
%       True -> (CSPRenAction x [CRename (e,[]) (x,[])])
%       _    -> (CSPUnParAction [Choose (x,[]) t] (CSPParAction a [ZVar (x1,[])]) e)
% -- omega_CActions (CSPExtChoice ca cb) = (CSPExtChoice (omega_CActions ca) (omega_CActions cb))



% \end{code}

% \begin{circus}
% \Omega_A (c \then A) \circdef c \then \Omega_A (A)
% \end{circus}
% is written in Haskell as:
% \begin{code}
% omega_CActions x = (CSPHide (CSPNSParal NSExpEmpty memi NSExpEmpty (CSPNSParal NSExpEmpty cs NSExpEmpty (CSPHide (CSPNSParal NSExpEmpty memi NSExpEmpty (CSPSeq a1 (CSPCommAction (ChanComm "terminate" []) CSPSkip)) (CSPParAction "MemoryMerge" [ZSetDisplay (make_maps_to lxs),ZVar ("LEFT",[])])) memi) (CSPHide (CSPNSParal NSExpEmpty memi NSExpEmpty (CSPSeq a2 (CSPCommAction (ChanComm "terminate" []) CSPSkip)) (CSPParAction "MemoryMerge" [ZSetDisplay (make_maps_to lxs),ZVar ("RIGHT",[])])) memi)) (CActionName "Merge")) (CChanSet ["mleft","mright"]))
% \end{code}



% \begin{circus}
% \Omega_A (c \then A) \circdef c \then \Omega_A (A)
% \end{circus}
% is written in Haskell as:
% \begin{code}
% omega_CActions (CSPNSParal a b c ca cb)
%   = (CSPNSParal a b c (omega_CActions ca) (omega_CActions cb))
% \end{code}

% \begin{circus}
% \Omega_A (c \then A) \circdef c \then \Omega_A (A)
% \end{circus}
% is written in Haskell as:
% \begin{code}
% omega_CActions (CSPParal x ca cb)
%   = (CSPParal x (omega_CActions ca) (omega_CActions cb))
% \end{code}

% \begin{circus}
% \Omega_A (c \then A) \circdef c \then \Omega_A (A)
% \end{circus}
% is written in Haskell as:
% \begin{code}
% omega_CActions (CSPNSInter x y ca cb)
%   = (CSPNSInter x y (omega_CActions ca) (omega_CActions cb))
% \end{code}

% \begin{circus}
% \Omega_A (c \then A) \circdef c \then \Omega_A (A)
% \end{circus}
% is written in Haskell as:
% \begin{code}
% omega_CActions (CSPInterleave ca cb)
%   = (CSPInterleave (omega_CActions ca) (omega_CActions cb))
% \end{code}

\begin{circus}
\Omega_A (A \circhide cs) \circdef \Omega_A (A) \circhide cs
\end{circus}
is written in Haskell as:
\begin{code}
omega_CActions (CSPHide a cs) = (CSPHide (omega_CActions a) cs)
\end{code}

\begin{circus}
\Omega_A (\circmu X \circspot A(X)) \circdef \circmu X \circspot \Omega_A(A(X))
\end{circus}
is written in Haskell as:
\begin{code}
omega_CActions (CSPRecursion x c) = (CSPRecursion x (omega_CActions c))
\end{code}

\begin{circus}
\Omega_A (\Semi x : \langle v_1,...,v_n \rangle \circspot A(x)) \circdef \Omega_A (A(v_1)\circseq \ldots \circseq A(v_n))
\end{circus}
is written in Haskell as:
\begin{code}
omega_CActions (CSPRepSeq [Choose (x,[]) (ZSeqDisplay xs)]
                  (CSPParAction act [ZVar (x1,[])]))
  = case x == x1 of
      True -> omega_CActions (rep_CSPRepSeq act xs)
      _    -> (CSPRepSeq [Choose (x,[]) (ZSeqDisplay xs)]
                  (CSPParAction act [ZVar (x1,[])]))
\end{code}

\begin{circus}
\Omega_A (\Extchoice x : \langle v_1,...,v_n \rangle \circspot A(x)) \circdef \Omega_A (A(v_1)\extchoice \ldots \extchoice A(v_n))
\end{circus}
is written in Haskell as:
\begin{code}
omega_CActions (CSPRepExtChoice [Choose (x,[]) (ZSeqDisplay xs)]
                  (CSPParAction act [ZVar (x1,[])]))
  = case x == x1 of
      True -> rep_CSPRepExtChoice act xs
      _    -> (CSPRepExtChoice [Choose (x,[]) (ZSeqDisplay xs)]
                  (CSPParAction act [ZVar (x1,[])]))
\end{code}

\begin{circus}
\Omega_A (\Intchoice x : \langle v_1,...,v_n \rangle \circspot A(x)) \circdef \Omega_A (A(v_1)\intchoice \ldots \intchoice A(v_n))
\end{circus}
is written in Haskell as:
\begin{code}
omega_CActions (CSPRepIntChoice [Choose (x,[]) (ZSeqDisplay xs)]
                  (CSPParAction act [ZVar (x1,[])]))
  = case x == x1 of
      True -> rep_CSPRepIntChoice act xs
      _    -> (CSPRepIntChoice [Choose (x,[]) (ZSeqDisplay xs)]
                  (CSPParAction act [ZVar (x1,[])]))
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
         \\ \lpar ns(v_n -1 ) | cs |  ns(v_n) \rpar
         \\ A(v_n)\end{array}\right )\end{array}\right )\end{array}\right )

\end{circus}
is written in Haskell as:
\begin{code}
omega_CActions (CSPRepParalNS (CSExpr cs) [Choose (x,[]) (ZSetDisplay lsx)]
                  (NSExprParam ns [ZVar (x1,[])])
                  (CSPParAction a [ZVar (x2,[])]))
  = case (x == x1) && (x == x2) of
      True -> rep_CSPRepParalNS a cs ns x lsx
      _    -> (CSPRepParalNS (CSExpr cs) [Choose (x,[]) (ZSetDisplay lsx)]
                  (NSExprParam ns [ZVar (x1,[])])
                  (CSPParAction a [ZVar (x2,[])]))
\end{code}

% \begin{circus}
% \Omega_A (c \then A) \circdef c \then \Omega_A (A)
% \end{circus}
% is written in Haskell as:
% \begin{code}
% omega_CActions (CSPRepParal a b c)
%   = (CSPRepParal a b (omega_CActions c))
% \end{code}

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
omega_CActions (CSPRepInterlNS [Choose (x,[]) (ZSetDisplay lsx)]
                  (NSExprParam ns [ZVar (x1,[])])
                  (CSPParAction a [ZVar (x2,[])]))
  = case (x == x1) && (x == x2) of
      True -> rep_CSPRepInterlNS a ns x lsx
      _    -> (CSPRepInterlNS [Choose (x,[]) (ZSetDisplay lsx)]
                  (NSExprParam ns [ZVar (x1,[])])
                  (CSPParAction a [ZVar (x2,[])]))
\end{code}

% \begin{circus}
% \Omega_A (c \then A) \circdef c \then \Omega_A (A)
% \end{circus}
% is written in Haskell as:
% \begin{code}
% omega_CActions (CSPRepInterl a c)
%   = (CSPRepInterl a (omega_CActions c))
% \end{code}

% \begin{circus}
% \Omega_A (c \then A) \circdef c \then \Omega_A (A)
% \end{circus}
% is written in Haskell as:
% \begin{code}
% omega_CActions  _ = undefined
% \end{code}

TODO!
\begin{code}
omega_prime_CActions a = undefined
\end{code}

Function used to propagate $CSPRepSeq$ actions

\begin{code}
rep_CSPRepSeq :: ZName -> [ZExpr] -> CAction
rep_CSPRepSeq a [x]
  = CSPParAction a [x]
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
\pagebreak
Auxiliary function to propagate $get$ communication through the variables and local variables of an action.
\begin{circus}
make\_get\_com\ (v_0,\ldots,v_n,l_0,\ldots,l_n)~A \defs
\\\t2 get.v_0?vv_0 \then \ldots \then get.v_n?vv_n \then
\\\t2 get.l_0?vl_0 \then \ldots \then get.l_n?vl_n \then A
\end{circus}
\begin{code}
make_get_com :: [ZVar] -> CAction -> CAction
make_get_com [(x,[])] c
  = (CSPCommAction (ChanComm "get"
      [ChanDotExp (ZVar (x,[])),ChanInp ("v"++x)]) c)
make_get_com ((x,[]):xs) c
  = (CSPCommAction (ChanComm "get"
      [ChanDotExp (ZVar (x,[])),ChanInp ("v"++x)]) (make_get_com xs c))
\end{code}

\begin{code}
make_v_chan :: [ZVar] -> [ZExpr]
make_v_chan [(x,[])] = [ZVar (("v"++x),[])]
make_v_chan ((x,[]):xs) = ((ZVar (("v"++x),[])):(make_v_chan xs))
\end{code}

\begin{code}
make_maps_to [ZVar (x,[])]
  = [ZCall (ZVar ("\\mapsto",[]))
      (ZTuple [ZVar (x,[]),ZVar ("v"++x,[])])]
make_maps_to ((ZVar (x,[])):xs)
  = (ZCall (ZVar ("\\mapsto",[]))
      (ZTuple [ZVar (x,[]),ZVar ("v"++x,[])])):(make_maps_to xs)
\end{code}


% \subsection{Adding permanent bits of the new \Circus specification ($MemoryMerge$, $MRG$, etc)}

