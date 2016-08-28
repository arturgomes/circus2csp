\section{Introduction}

\ignore{
\begin{code}
module DefSets
where
import Data.List
\end{code}
}
\begin{code}
inSet c acls = [ x | x <- acls, x == c]
\end{code}
\begin{code}
invertBool x
  = case x of
      False -> True
      True  -> False
\end{code}
\begin{code}
subsetEq as bs = isPrefixOf as bs
\end{code}
\begin{code}
notinSet c acls = isEmpty [ x | x <- acls, x == c]
\end{code}
\begin{code}
intersectionSet as bs
  = let ns = [ a | a <- as, elem a bs] in [ b | b <- bs, elem b ns]
\end{code}

\begin{code}
unionSet as bs
  = let ns = [ a | a <- as++bs]
  	in [x | (x,y) <- zip ns [0..], x `notElem` (take y as)]
\end{code}
\begin{code}
isEmpty xs
  = case xs of
      [] -> True
      _  -> False
\end{code}
\begin{code}
isNotEmpty xs
  = case xs of
      [] -> True
      _  -> False
\end{code}
\begin{code}
-- TODO: Need to do it
getFV xs = []
\end{code}
\begin{code}
-- TODO: Need to do it
getWrtV xs = []
\end{code}
\begin{code}
maybeToBool x
 = case x
 of
 	Just _  -> True
 	Nothing -> False
\end{code}
