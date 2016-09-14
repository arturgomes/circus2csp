\section{Mapping Functions - Stateless Circus}

File: MappingFunStatelessCircus.lhs
\ignore{
\begin{code}
module MappingFunStatelessCircus
where
import AST
--import CRL
import FormatterToCSP
import DefSets
import Data.List

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
omega_CActions (CSPCommAction (ChanComm c [ChanDotExp e]) a)
  = make_get_com lxs (CSPCommAction (ChanComm c [ChanDotExp e]) (omega_prime_CActions a))
  where lxs = free_var_ZExpr(e)
\end{code}
\begin{circus}
\Omega_A (c!e(v_0,\ldots,v_n,l_0,\ldots,l_m) \then A) \circdef
\\\t2 c.e(v_0,\ldots,v_n,l_0,\ldots,l_m) \then A
\end{circus}
\begin{code}
omega_CActions (CSPCommAction (ChanComm c [ChanOutExp e]) a)
  = omega_CActions (CSPCommAction (ChanComm c [ChanDotExp e]) a)
\end{code}

\begin{circus}
\Omega_A (g(v_0,\ldots,v_n,l_0,\ldots,l_m) \then A) \circdef
\\\t2 get.v_0?vv_0 \then \ldots \then get.v_n?vv_n \then
\\\t2 get.l_0?vl_0 \then \ldots \then get.l_m?vl_m \then
\\\t2 g(vv_0,\ldots,vv_n,vl_0,\ldots,vl_m) \circguard \Omega'_{A} (A)
\end{circus}
is written in Haskell as:
\begin{code}
omega_CActions (CSPGuard g a)
  = make_get_com lxs (CSPGuard g (omega_prime_CActions a))
  where lxs = free_var_ZPred(g)
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
omega_CActions (CSPCommAction (ChanComm c [ChanInpPred x p]) a)
  = case not (elem x (getWrtV(a))) of
      True -> make_get_com lsx (CSPCommAction
                        (ChanComm c [ChanInpPred x p])
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

% TODO: I need to somehow calculate the $FV(A_1)$ and $FV(A_2)$. What should I do?
\begin{circus}
\Omega_A (A_1 \extchoice A_2) \circdef
\\\t1 get.v_0?vv_0 \then \ldots \then get.v_n?vv_n \then
\\\t1 get.l_0?vl_0 \then \ldots \then get.l_m?vl_m \then
\\\t2 (\Omega'_A (A_1) \extchoice \Omega'_A (A_2))
\end{circus}
is written in Haskell as:
\begin{code}
omega_CActions (CSPExtChoice ca cb)
  = make_get_com lsx (CSPExtChoice (omega_prime_CActions ca) (omega_prime_CActions cb))
    where
      lsx = free_var_CAction (CSPExtChoice ca cb)
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
omega_CActions (CSPNSParal ns1 cs ns2 a1 a2)
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
      lsx = (free_var_CAction a1) `union` (free_var_CAction a2)
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

\begin{circus}
\Omega_A \left (\begin{array}{l}x_0,\ldots,x_n:=e_0\left (\begin{array}{l}v_0,...,v_n,\\l_0,...,l_m\end{array}\right ),\ldots,e_n\left (\begin{array}{l}v_0,...,v_n,\\l_0,...,l_m\end{array}\right )\end{array}\right ) \circdef
\\\t1 get.v_0?vv_0 \then \ldots \then get.v_n?vv_n \then
\\\t1 get.l_0?vl_0 \then \ldots \then get.l_m?vl_m \then
\\\t1 set.x_0!e_0(vv_0,...,vv_n,vl_0,...,vl_m) \then
\\\t1\ldots\then
\\\t1 set.x_n!e_n(vv_0,...,vv_n,vl_0,...,vl_m) \then \Skip
\end{circus}


\begin{code}
omega_CActions (CActionCommand (CAssign varls valls))
  = make_get_com lsx (make_set_com varls valls CSPSkip)
  where
    lsx = nub $ concat  (map free_var_ZExpr valls)
\end{code}
\begin{circus}
\Omega_A (\circif g (v_0,...,v_n,l_0,...,l_m) \circthen A \circfi ) \defs
    \\\t1 get.v_0?vv_0 \then \ldots \then get.v_n?vv_n \then
    \\\t1 get.l_0?vl_0 \then \ldots \then get.l_m?vl_m \then
    \\\t1\circif g (v_0,...,v_n,l_0,...,l_m) \circthen \Omega'_A (A) \circfi
\end{circus}
\begin{code}
omega_CActions (CActionCommand (CIf (CircGAction g a)))
  = make_get_com lsx (CActionCommand
                        (CIf (CircGAction g (omega_prime_CActions a))))
  where
    lsx = free_var_ZPred g

\end{code}
\begin{circus}
\Omega_A
    \left (\begin{array}{l}
    \circif g_0 (v_0,...,v_n,l_0,...,l_m) \circthen A_0
    \\\t1\circelse \ldots
    \\\t1 \circelse g_n (v_0,...,v_n,l_0,...,l_m)  \circthen A_n
    \\\circfi
    \end{array}\right ) \defs
    \\\t1 get.v_0?vv_0 \then \ldots \then get.v_n?vv_n \then
    \\\t1 get.l_0?vl_0 \then \ldots \then get.l_m?vl_m \then
    \\\t1\circif g_0 (v_0,...,v_n,l_0,...,l_m) \circthen \Omega'_A (A_0)
    \\\t2\circelse \ldots
    \\\t2 \circelse g_n (v_0,...,v_n,l_0,...,l_m)  \circthen \Omega'_A (A_n)
    \\\t1\circfi
\end{circus}

\begin{code}
omega_CActions (CActionCommand (CIf (CircThenElse gl glx)))
  = make_get_com lsx (CActionCommand (CIf (mk_guard_pair guard_pair)))
  where
    guard_pair = get_guard_pair (CircThenElse gl glx)
    lsx = nub $ concat $ map free_var_ZPred (map fst guard_pair)
\end{code}

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

\begin{circus}
\Omega_A (\{g\}) \circdef \prefixcolon [g, true]
\end{circus}

\begin{code}
omega_CActions (CActionCommand (CommandBrace g))
  = omega_CActions (CActionCommand (CPrefix g (ZTrue {reason = []})))
\end{code}

\begin{circus}
\Omega_A ([g]) \circdef \prefixcolon [g]
\end{circus}

\begin{code}
omega_CActions (CActionCommand (CommandBracket g))
  = omega_CActions (CActionCommand (CPrefix1 g))
\end{code}

\begin{circus}
\Omega_A (A[old_1,...,old_n := new_1,...,new_n) \circdef
\\\t1A[new_1,...,new_n/old_1,...,old_n)
\end{circus}

\begin{code}
omega_CActions (CSPRenAction a (CRenameAssign left right))
  = (CSPRenAction a (CRename right left))
\end{code}


NOTE: Besides the transformation rules for $[g]$ and ${g}$, the remaining transformation rules from page 91 of the D24.1 document, were not yet implemented.
\subsection{Definitions of $\Omega'_{A}$}

\begin{circus}
 \Omega'_{A}  (c \then A) \circdef c \then \Omega'_{A} (A)
\end{circus}

is written in Haskell as:
\begin{code}
omega_prime_CActions (CSPCommAction (ChanComm c []) a)
  = (CSPCommAction (ChanComm c []) (omega_prime_CActions a))
\end{code}


\begin{circus}
 \Omega'_{A} (c.e(v_0,\ldots,v_n,l_0,\ldots,l_m) \then A) \circdef
\\\t2 c.e(vv_0,\ldots,vv_n,vl_0,\ldots,vl_m) \then \Omega'_{A} (A)
\end{circus}

is written in Haskell as:
\begin{code}
omega_prime_CActions (CSPCommAction (ChanComm c [ChanDotExp e]) a)
  = (CSPCommAction (ChanComm c [ChanDotExp e]) (omega_prime_CActions a))
  where lxs = free_var_ZExpr(e)
\end{code}

\begin{circus}
 \Omega'_{A} (A_1 \circseq A_2) \circdef \Omega_A (A_1) \circseq  \Omega'_{A} (A_2)
\end{circus}
is written in Haskell as:
\begin{code}
omega_prime_CActions (CSPSeq ca cb)
  = (CSPSeq (omega_prime_CActions ca) (omega_CActions cb))
\end{code}

\begin{code}
omega_prime_CActions _ = error "Not defined for Omega'"
\end{code}

\subsection{Auxiliary functions for the definition of $\Omega_{A}$}
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

Auxiliary function to propagate $get$ communication through the variables and local variables of an action.
\begin{circus}
make\_get\_com\ (v_0,\ldots,v_n,l_0,\ldots,l_m)~A \defs
\\\t2 get.v_0?vv_0 \then \ldots \then get.v_n?vv_n \then
\\\t2 get.l_0?vl_0 \then \ldots \then get.l_m?vl_m \then A
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
make_set_com :: [ZVar] -> [ZExpr] -> CAction -> CAction
make_set_com [(x,[])] [y] c
  = (CSPCommAction (ChanComm "set"
      [ChanDotExp (ZVar (x,[])),ChanOutExp y]) c)
make_set_com (((x,[])):xs) (y:ys) c
  = (CSPCommAction (ChanComm "set"
        [ChanDotExp (ZVar (x,[])),ChanOutExp y]) (make_set_com xs ys c))
\end{code}

Given $\{v_0,\ldots,v_n\}$, the function $make\_maps\_to$ returns $\{v_0 \mapsto vv_o, \ldots, v_n \mapsto vv_n\}$.
\begin{code}
make_maps_to :: [ZVar] -> [ZExpr]
make_maps_to [(x,[])]
  = [ZCall (ZVar ("\\mapsto",[]))
      (ZTuple [ZVar (x,[]),ZVar ("v"++x,[])])]
make_maps_to ((x,[]):xs)
  = [ZCall (ZVar ("\\mapsto",[]))
      (ZTuple [ZVar (x,[]),ZVar ("v"++x,[])])]++(make_maps_to xs)
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
  = (CircGAction g (omega_prime_CActions a))
mk_guard_pair ((g,a):ls)
  = (CircThenElse (CircGAction g (omega_prime_CActions a)) (mk_guard_pair ls))
\end{code}
% \subsection{Adding permanent bits of the new \Circus specification ($MemoryMerge$, $MRG$, etc)}

