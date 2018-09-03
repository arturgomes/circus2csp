theory Tree
imports Nats Prelude
begin
 
datatype ('a) Tree = Tip 'a
                   | Branch "'a Tree" "'a Tree"
 
fun size :: "'a Tree \<Rightarrow> Nat"
where
  "size (Tip a) = Suc Zero"
| "size (Branch x y) = plus_nat (size x) (size y)"

 
fun insert :: "'a \<Rightarrow> 'a Tree \<Rightarrow> 'a Tree"
where
  "insert x (Tip y) = Branch (Tip x) (Tip y)"
| "insert x (Branch y z) = (if less_eq_nat (size y) (size z)
                            then Branch (insert x y) z else Branch y (insert x z))"


end
