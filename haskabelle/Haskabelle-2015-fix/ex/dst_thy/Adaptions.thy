theory Adaptions
imports Prelude
begin
 
fun implies :: "bool \<Rightarrow> bool \<Rightarrow> bool"
where
  "implies False _ = True"
| "implies True True = True"
| "implies True False = False"

 
fun nand :: "bool \<Rightarrow> bool \<Rightarrow> bool"
where
  "nand p q = Not (p & q)"

 
fun nor :: "bool \<Rightarrow> bool \<Rightarrow> bool"
where
  "nor p q = Not (p | q)"

 
fun append :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "append Nil ys = ys"
| "append xs Nil = xs"
| "append (x # xs) ys = (x # append xs ys)"

 
fun rev :: "'a list \<Rightarrow> 'a list"
where
  "rev Nil = Nil"
| "rev (x # xs) = append (rev xs) [x]"

 
fun who_am_i_smile :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a option \<Rightarrow> 'b option"
where
  "who_am_i_smile f None = None"
| "who_am_i_smile f (Some x) = Some (f x)"


end
