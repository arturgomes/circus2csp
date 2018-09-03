theory Integers
imports Prelude
begin
 
fun fibs :: "int \<Rightarrow> int list \<Rightarrow> int list"
where
  "fibs k xs = (let ys' = case xs of
                             (x # (y # _)) \<Rightarrow> (x + y) # xs
                           | _ \<Rightarrow> 1 # xs
                in if k <= 0 then rev xs else fibs (k - 1) ys')"


end
