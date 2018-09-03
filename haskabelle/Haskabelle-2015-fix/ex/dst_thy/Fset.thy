theory Fset
imports Prelude
begin
 
datatype Nat = Zero
             | Suc Nat
 
datatype ('a) Fset = Set "'a list"
 
fun mapb :: "('b \<Rightarrow> 'a) \<Rightarrow> 'b list \<Rightarrow> 'a list"
where
  "mapb f Nil = Nil"
| "mapb f (x # xs) = (f x # mapb f xs)"

 
fun membera :: "('a :: eq) \<Rightarrow> ('a :: eq) list \<Rightarrow> bool"
where
  "membera x Nil = False"
| "membera x (y # ys) = (eq x y | membera x ys)"

 
fun remdups :: "('a :: eq) list \<Rightarrow> ('a :: eq) list"
where
  "remdups Nil = Nil"
| "remdups (x # xs) = (if membera x xs then remdups xs
                       else x # remdups xs)"

 
fun mapa :: "('b \<Rightarrow> ('a :: eq)) \<Rightarrow> 'b Fset \<Rightarrow> ('a :: eq) Fset"
where
  "mapa f (Set xs) = Set (remdups (mapb f xs))"

 
fun length_unique :: "('a :: eq) list \<Rightarrow> Nat"
where
  "length_unique Nil = Zero"
| "length_unique (x # xs) = (if membera x xs then length_unique xs
                             else Suc (length_unique xs))"

 
fun card :: "('a :: eq) Fset \<Rightarrow> Nat"
where
  "card (Set xs) = length_unique xs"

 
fun nulla :: "'a list \<Rightarrow> bool"
where
  "nulla Nil = True"
| "nulla (x # xs) = False"

 
definition empty :: "'a Fset"
where
  "empty = Set Nil"

 
fun list_ex :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "list_ex p Nil = False"
| "list_ex p (x # xs) = (p x | list_ex p xs)"

 
fun exists :: "('a \<Rightarrow> bool) \<Rightarrow> 'a Fset \<Rightarrow> bool"
where
  "exists p (Set xs) = list_ex p xs"

 
fun member :: "('a :: eq) Fset \<Rightarrow> ('a :: eq) \<Rightarrow> bool"
where
  "member a y = exists (% aa . eq y aa) a"

 
fun filterb :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "filterb p Nil = Nil"
| "filterb p (x # xs) = (if p x then x # filterb p xs
                         else filterb p xs)"

 
fun filtera :: "('a \<Rightarrow> bool) \<Rightarrow> 'a Fset \<Rightarrow> 'a Fset"
where
  "filtera p (Set xs) = Set (filterb p xs)"

 
fun inter :: "('a :: eq) Fset \<Rightarrow> ('a :: eq) Fset \<Rightarrow> ('a :: eq) Fset"
where
  "inter a b = filtera (member a) b"

 
fun inserta :: "('a :: eq) \<Rightarrow> ('a :: eq) list \<Rightarrow> ('a :: eq) list"
where
  "inserta x xs = (if membera x xs then xs else x # xs)"

 
fun insert :: "('a :: eq) \<Rightarrow> ('a :: eq) Fset \<Rightarrow> ('a :: eq) Fset"
where
  "insert x (Set xs) = Set (inserta x xs)"

 
fun foldla :: "('a \<Rightarrow> 'b \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'b list \<Rightarrow> 'a"
where
  "foldla f a Nil = a"
| "foldla f a (x # xs) = foldla f (f a x) xs"

 
fun union :: "('a :: eq) Fset \<Rightarrow> ('a :: eq) Fset \<Rightarrow> ('a :: eq) Fset"
where
  "union (Set xs) a = foldla (% aa x . insert x aa) a xs"

 
fun list_all :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "list_all p Nil = True"
| "list_all p (x # xs) = (p x & list_all p xs)"

 
fun foralla :: "('a \<Rightarrow> bool) \<Rightarrow> 'a Fset \<Rightarrow> bool"
where
  "foralla p (Set xs) = list_all p xs"

 
fun intera :: "(('a :: eq) Fset) Fset \<Rightarrow> ('a :: eq) Fset"
where
  "intera (Set (a # asa)) = foldla inter a asa"

 
fun remove_all :: "('a :: eq) \<Rightarrow> ('a :: eq) list \<Rightarrow> ('a :: eq) list"
where
  "remove_all x xs = filterb (Not o (% a . eq x a)) xs"

 
fun remove :: "('a :: eq) \<Rightarrow> ('a :: eq) Fset \<Rightarrow> ('a :: eq) Fset"
where
  "remove x (Set xs) = Set (remove_all x xs)"

 
fun uniona :: "(('a :: eq) Fset) Fset \<Rightarrow> ('a :: eq) Fset"
where
  "uniona (Set asa) = foldla union empty asa"

 
fun subfset_eq :: "('a :: eq) Fset \<Rightarrow> ('a :: eq) Fset \<Rightarrow> bool"
where
  "subfset_eq a b = foralla (member b) a"

 
fun eq_fset :: "('a :: eq) Fset \<Rightarrow> ('a :: eq) Fset \<Rightarrow> bool"
where
  "eq_fset a b = (subfset_eq a b & subfset_eq b a)"

 
fun subfset :: "('a :: eq) Fset \<Rightarrow> ('a :: eq) Fset \<Rightarrow> bool"
where
  "subfset a b = (subfset_eq a b & Not (subfset_eq b a))"

 
fun is_empty :: "'a Fset \<Rightarrow> bool"
where
  "is_empty (Set xs) = nulla xs"

 
fun subtracta :: "('a :: eq) Fset \<Rightarrow> ('a :: eq) Fset \<Rightarrow> ('a :: eq) Fset"
where
  "subtracta (Set xs) a = foldla (% aa x . remove x aa) a xs"


end
