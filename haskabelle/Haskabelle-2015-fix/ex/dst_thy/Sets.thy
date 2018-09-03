theory Sets
imports Prelude
begin
 
datatype Nat = Suc Nat
             | Zero
 
datatype ('a) Set = Insert 'a "'a Set"
                  | Empty
 
fun bex :: "'a Set \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
where
  "bex Empty p = False"
| "bex (Insert a aa) p = (p a | bex aa p)"

 
fun ball :: "'a Set \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
where
  "ball Empty p = True"
| "ball (Insert a aa) p = (p a & ball aa p)"

 
fun eq_nat :: "Nat \<Rightarrow> Nat \<Rightarrow> bool"
where
  "eq_nat Zero Zero = True"
| "eq_nat (Suc m) (Suc n) = eq_nat m n"
| "eq_nat Zero (Suc a) = False"
| "eq_nat (Suc a) Zero = False"

 
fun member :: "Nat \<Rightarrow> Nat Set \<Rightarrow> bool"
where
  "member a aa = bex aa (eq_nat a)"

 
fun uniona :: "Nat Set \<Rightarrow> Nat Set \<Rightarrow> Nat Set"
where
  "uniona a Empty = a"
| "uniona Empty a = a"
| "uniona (Insert a aa) b = (let c = uniona aa b
                             in (if member a b then c else Insert a c))"

 
fun union :: "'b Set \<Rightarrow> ('b \<Rightarrow> Nat Set) \<Rightarrow> Nat Set"
where
  "union Empty f = Empty"
| "union (Insert a aa) f = uniona (f a) (union aa f)"

 
fun image :: "('b \<Rightarrow> Nat) \<Rightarrow> 'b Set \<Rightarrow> Nat Set"
where
  "image f a = union a (% x . Insert (f x) Empty)"

 
fun intersect :: "Nat Set \<Rightarrow> Nat Set \<Rightarrow> Nat Set"
where
  "intersect a Empty = Empty"
| "intersect Empty a = Empty"
| "intersect (Insert a aa) b = (let c = intersect aa b
                                in (if member a b then Insert a c else c))"

 
fun intera :: "'b Set \<Rightarrow> ('b \<Rightarrow> Nat Set) \<Rightarrow> Nat Set"
where
  "intera (Insert a Empty) f = f a"
| "intera (Insert a aa) f = intersect (f a) (intera aa f)"

 
fun inter :: "(Nat Set) Set \<Rightarrow> Nat Set"
where
  "inter a = intera a (% x . x)"

 
fun less_eq_set :: "Nat Set \<Rightarrow> Nat Set \<Rightarrow> bool"
where
  "less_eq_set a b = ball a (% x . member x b)"

 
fun eq_set :: "Nat Set \<Rightarrow> Nat Set \<Rightarrow> bool"
where
  "eq_set a b = (less_eq_set a b & less_eq_set b a)"

 
fun unionb :: "(Nat Set) Set \<Rightarrow> Nat Set"
where
  "unionb a = union a (% x . x)"

 
fun project :: "(Nat \<Rightarrow> bool) \<Rightarrow> Nat Set \<Rightarrow> Nat Set"
where
  "project p a = union a (% aa .
                            (if p aa then Insert aa Empty else Empty))"

 
fun minus_set :: "Nat Set \<Rightarrow> Nat Set \<Rightarrow> Nat Set"
where
  "minus_set a Empty = a"
| "minus_set Empty a = Empty"
| "minus_set (Insert a aa) b = (let c = minus_set aa b
                                in (if member a b then c else Insert a c))"

 
fun is_empty :: "'a Set \<Rightarrow> bool"
where
  "is_empty Empty = True"
| "is_empty (Insert a aa) = False"

 
fun less_set :: "Nat Set \<Rightarrow> Nat Set \<Rightarrow> bool"
where
  "less_set a b = (less_eq_set a b & Not (less_eq_set b a))"


end
