\begin{code}
data CSPOp = Com Char CSPOp | Seq CSPOp CSPOp | ExtCh CSPOp CSPOp

trace (Com a p) = [] ++ [a] ++ [ a ++ [trace p]]
trace (Seq a b) = (trace a) ++ (trace b)
trace (ExtCh a b) = [trace a] ++ [trace b]
\end{code}
