theory Classes
imports Nats Prelude
begin
 
class Monoid =
  fixes nothing :: 'a
  fixes plus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
 
instantiation Nat :: Monoid
begin
   
  definition nothing_Nat :: "Nat"
  where
    "nothing_Nat = Zero"
  
   
  definition plus_Nat :: "Nat \<Rightarrow> Nat \<Rightarrow> Nat"
  where
    "plus_Nat = plus_nat"
  
 
instance sorry

end
 
instantiation int :: Monoid
begin
   
  definition nothing_int :: "int"
  where
    "nothing_int = 0"
  
   
  definition plus_int :: "int \<Rightarrow> int \<Rightarrow> int"
  where
    "plus_int = (op +)"
  
 
instance sorry

end
 
fun summ :: "('a :: Monoid) list \<Rightarrow> ('a :: Monoid)"
where
  "summ Nil = nothing"
| "summ (x # xs) = plus x (summ xs)"

 
class Group = Monoid +
  fixes inverse :: "'a \<Rightarrow> 'a"
 
instantiation int :: Group
begin
   
  definition inverse_int :: "int \<Rightarrow> int"
  where
    "inverse_int = uminus"
  
 
instance sorry

end
 
fun sub :: "('a :: Group) \<Rightarrow> ('a :: Group) \<Rightarrow> ('a :: Group)"
where
  "sub a b = plus a (inverse b)"

 
fun pow_nat :: "Nat \<Rightarrow> ('a :: Monoid) \<Rightarrow> ('a :: Monoid)"
where
  "pow_nat Zero _ = nothing"
| "pow_nat (Suc n) x = plus x (pow_nat n x)"

 
function (sequential) pow_int :: "int \<Rightarrow> ('a :: Group) \<Rightarrow> ('a :: Group)"
where
  "pow_int k x = (if eq k 0 then nothing
                  else if k < 0 then pow_int (uminus k) (inverse x)
                       else plus x (pow_int (k - 1) x))"
sorry termination sorry
 
class Order =
  fixes less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  fixes less :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
 
instantiation Nat :: Order
begin
   
  definition less_eq_Nat :: "Nat \<Rightarrow> Nat \<Rightarrow> bool"
  where
    "less_eq_Nat = less_eq_nat"
  
   
  definition less_Nat :: "Nat \<Rightarrow> Nat \<Rightarrow> bool"
  where
    "less_Nat = less_nat"
  
 
instance sorry

end
 
instantiation int :: Order
begin
   
  definition less_eq_int :: "int \<Rightarrow> int \<Rightarrow> bool"
  where
    "less_eq_int = (op <=)"
  
   
  definition less_int :: "int \<Rightarrow> int \<Rightarrow> bool"
  where
    "less_int = (op <)"
  
 
instance sorry

end
 
instantiation prod :: (Order, Order) Order
begin
   
  fun less_eq_prod :: "'a * 'b \<Rightarrow> 'a * 'b \<Rightarrow> bool"
  where
    "less_eq_prod (x, y) (w, z) = (less x w | (Not (less w x) & less_eq y z))"
  
   
  fun less_prod :: "'a * 'b \<Rightarrow> 'a * 'b \<Rightarrow> bool"
  where
    "less_prod (x, y) (w, z) = (less x w | (Not (less w x) & less y z))"
  
 
instance sorry

end
 
instantiation list :: (Order) Order
begin
   
  fun less_eq_list :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
  where
    "less_eq_list (x # xs) (y # ys) = (less x y | (Not (less y x) & less_eq xs ys))"
  | "less_eq_list Nil xs = True"
  | "less_eq_list (x # xs) Nil = False"
  
   
  fun less_list :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
  where
    "less_list (x # xs) (y # ys) = (less x y | (Not (less y x) & less xs ys))"
  | "less_list xs Nil = False"
  | "less_list Nil (x # xs) = True"
  
 
instance sorry

end
 
datatype Linord = Less
                | Equal
                | Greater
 
class Linorder = eq +
  fixes linord :: "'a \<Rightarrow> 'a \<Rightarrow> Linord"
 
instantiation Nat :: Linorder
begin
   
  fun linord_Nat :: "Nat \<Rightarrow> Nat \<Rightarrow> Linord"
  where
    "linord_Nat Zero (Suc _) = Less"
  | "linord_Nat Zero Zero = Equal"
  | "linord_Nat (Suc _) Zero = Greater"
  | "linord_Nat (Suc m) (Suc n) = linord m n"
  
 
instance sorry

end
 
instantiation int :: Linorder
begin
   
  fun linord_int :: "int \<Rightarrow> int \<Rightarrow> Linord"
  where
    "linord_int k l = (if k < l then Less
                       else if l < k then Greater else Equal)"
  
 
instance sorry

end
 
instantiation prod :: (Linorder, Linorder) Linorder
begin
   
  fun linord_prod :: "'a * 'b \<Rightarrow> 'a * 'b \<Rightarrow> Linord"
  where
    "linord_prod (x, y) (w, z) = (case linord x w of
                                     Less \<Rightarrow> Less
                                   | Equal \<Rightarrow> linord y z
                                   | Greater \<Rightarrow> Greater)"
  
 
instance sorry

end
 
instantiation list :: (Linorder) Linorder
begin
   
  fun linord_list :: "'a list \<Rightarrow> 'a list \<Rightarrow> Linord"
  where
    "linord_list Nil Nil = Equal"
  | "linord_list xs Nil = Greater"
  | "linord_list Nil ys = Less"
  | "linord_list (x # xs) (y # ys) = (case linord x y of
                                         Less \<Rightarrow> Less
                                       | Equal \<Rightarrow> linord xs ys
                                       | Greater \<Rightarrow> Greater)"
  
 
instance sorry

end

end
