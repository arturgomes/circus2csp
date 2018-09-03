theory ClassAdaptions
imports Prelude
begin
 
datatype Nat = Succ Nat
             | Zero
 
instantiation Nat :: eq
begin
   
  fun eq_Nat
  where
    "eq_Nat Zero Zero = True"
  | "eq_Nat (Succ m) (Succ n) = eq m n"
  | "eq_Nat Zero (Succ n) = False"
  | "eq_Nat (Succ m) Zero = False"
  
 
instance sorry

end
 
class Ident = eq +
  fixes ident :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
 
fun fromEq :: "('a :: eq) \<Rightarrow> ('a :: eq) \<Rightarrow> 'b \<Rightarrow> 'b option"
where
  "fromEq a1 a2 b = (if eq a1 a2 then Some b else None)"

 
fun fromIdent :: "('a :: Ident) \<Rightarrow> ('a :: Ident) \<Rightarrow> 'b \<Rightarrow> 'b option"
where
  "fromIdent a1 a2 b = (if ident a1 a2 then Some b else None)"


end
