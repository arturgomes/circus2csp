theory Nats
imports Prelude
begin
 
datatype Nat = Suc Nat
             | Zero
 
fun eq_nat :: "Nat \<Rightarrow> Nat \<Rightarrow> bool"
where
  "eq_nat Zero Zero = True"
| "eq_nat (Suc m) (Suc n) = eq_nat m n"
| "eq_nat Zero (Suc a) = False"
| "eq_nat (Suc a) Zero = False"

 
instantiation Nat :: eq
begin
   
  definition eq_Nat
  where
    "eq_Nat = eq_nat"
  
 
instance sorry

end
 
fun less_eq_nat :: "Nat \<Rightarrow> Nat \<Rightarrow> bool" and 
    less_nat :: "Nat \<Rightarrow> Nat \<Rightarrow> bool"
where
  "less_eq_nat (Suc m) n = less_nat m n"
| "less_eq_nat Zero n = True"
| "less_nat m (Suc n) = less_eq_nat m n"
| "less_nat n Zero = False"

 
fun greater_nat :: "Nat \<Rightarrow> Nat \<Rightarrow> bool"
where
  "greater_nat m n = Not (less_eq_nat m n)"

 
fun mina :: "Nat \<Rightarrow> Nat \<Rightarrow> Nat"
where
  "mina a b = (if less_eq_nat a b then a else b)"

 
fun nat_rec :: "'t \<Rightarrow> (Nat \<Rightarrow> 't \<Rightarrow> 't) \<Rightarrow> Nat \<Rightarrow> 't"
where
  "nat_rec f1 f2 (Suc n) = f2 n (nat_rec f1 f2 n)"
| "nat_rec f1 f2 Zero = f1"

 
definition one_nat :: "Nat"
where
  "one_nat = Suc Zero"

 
fun maxa :: "Nat \<Rightarrow> Nat \<Rightarrow> Nat"
where
  "maxa a b = (if less_eq_nat a b then b else a)"

 
fun nat_case :: "'t \<Rightarrow> (Nat \<Rightarrow> 't) \<Rightarrow> Nat \<Rightarrow> 't"
where
  "nat_case f1 f2 Zero = f1"
| "nat_case f1 f2 (Suc n) = f2 n"

 
fun plus_nat :: "Nat \<Rightarrow> Nat \<Rightarrow> Nat"
where
  "plus_nat (Suc m) n = plus_nat m (Suc n)"
| "plus_nat Zero n = n"

 
fun minus_nat :: "Nat \<Rightarrow> Nat \<Rightarrow> Nat"
where
  "minus_nat (Suc m) (Suc n) = minus_nat m n"
| "minus_nat Zero n = Zero"
| "minus_nat m Zero = m"

 
fun times_nat :: "Nat \<Rightarrow> Nat \<Rightarrow> Nat"
where
  "times_nat (Suc m) n = plus_nat n (times_nat m n)"
| "times_nat Zero n = Zero"


end
