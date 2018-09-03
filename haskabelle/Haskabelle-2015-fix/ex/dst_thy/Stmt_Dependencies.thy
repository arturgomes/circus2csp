theory Stmt_Dependencies
imports Prelude
begin
 
datatype ('a, 'b) Twin = Twin 'a 'b
 
fun dest_Twin :: "('a, 'b) Twin \<Rightarrow> 'a * 'b"
where
  "dest_Twin (Twin x y) = (x, y)"

 
fun h :: "'a \<Rightarrow> 'a"
where
  "h x = x"

 
fun g :: "'a \<Rightarrow> ('a, 'a) Twin"
where
  "g x = Twin (h x) (h x)"

 
fun f :: "'a \<Rightarrow> 'a * 'a"
where
  "f x = dest_Twin (g x)"

 
fun k :: "'a * 'b \<Rightarrow> 'a * 'b"
where
  "k (x, y) = dest_Twin (Twin x y)"


end
