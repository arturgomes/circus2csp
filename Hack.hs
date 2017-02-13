module Hack where

data E 
 = N Int | V String | A String [E] | B E String E
 deriving (Eq,Ord)

isN :: E -> Bool
isN (N _) =  True
isN _ = False

getN :: E -> Int
getN (N i) = i

instance Show E where
  show (N i) = show i
  show (V v) = v
  show (A n es) = n ++ show es
  show (B e1 n e2) = "("++show e1 ++ pad n ++ show e2++")"

pad s = ' ':s ++ " "

type RFun = E -> Maybe E


-- do one rewrite

apply :: RFun -> RFun
apply r e@(A n es)
 = case r e of
     r'@(Just _) -> r'
     Nothing 
      -> case applys r es of
          Just es' ->  Just $ A n es'
          Nothing  ->  Nothing
apply r e@(B e1 n e2)
 = case r e of
     r'@(Just _) -> r'
     Nothing 
      -> case applys r [e1,e2]  of
          Just [e1',e2'] ->  Just $ B e1' n e2'
          Nothing  ->  Nothing
apply _ _ = Nothing

mapply r (Just e) = apply r e
mapply r Nothing = Nothing

applys :: RFun -> [E] -> Maybe [E]
applys r [] = Nothing
applys r (e:es)
 = case apply r e of
    Just e' -> Just (e':es)
    Nothing
     -> case applys r es of
          Nothing -> Nothing
          Just es' -> Just (e:es')


zero = N 0
one = N 1
two = N 2

v = V "v"
x = V "x"
y = V "y"
add a b = B a "+" b
mul a b = B a "*" b
sumup es = A "sum" es

simp (B (N i) "+" (N j)) = Just $ N (i+j)
simp (B (N i) "*" (N j)) = Just $ N (i*j)
simp (A "sum" es)
 | all isN es = Just $ N $ sum $ map getN es
simp _ = Nothing

example = sumup [one,add two zero,mul two two]