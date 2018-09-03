theory Enumerations
imports Prelude
begin
 
datatype Nat = Zero
             | Suc Nat
 
fun mapa :: "('b \<Rightarrow> 'a) \<Rightarrow> 'b list \<Rightarrow> 'a list"
where
  "mapa f Nil = Nil"
| "mapa f (x # xs) = (f x # mapa f xs)"

 
fun list_case :: "'a \<Rightarrow> ('b \<Rightarrow> 'b list \<Rightarrow> 'a) \<Rightarrow> 'b list \<Rightarrow> 'a"
where
  "list_case f1 f2 (a # list) = f2 a list"
| "list_case f1 f2 Nil = f1"

 
fun zipa :: "'a list \<Rightarrow> 'b list \<Rightarrow> ('a * 'b) list"
where
  "zipa xs Nil = Nil"
| "zipa xs (y # ys) = (case xs of
                          Nil \<Rightarrow> Nil
                        | z # zs \<Rightarrow> (z, y) # zipa zs ys)"

 
class Finite
  
 
class Enuma = Finite +
  fixes enum :: "'a list"
 
datatype ('a, 'b) Sum = Inl 'a
                      | Inr 'b
 
fun append :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "append Nil ys = ys"
| "append (x # xs) ys = (x # append xs ys)"

 
definition enuma :: "((('a :: Enuma), ('b :: Enuma)) Sum) list"
where
  "enuma = append (mapa Inl enum) (mapa Inr enum)"

 
fun producta :: "'a list \<Rightarrow> 'b list \<Rightarrow> ('a * 'b) list"
where
  "producta Nil uu = Nil"
| "producta (x # xs) ys = append (mapa (% a .
                                          (x, a)) ys) (producta xs ys)"

 
definition enumb :: "(('a :: Enuma) * ('b :: Enuma)) list"
where
  "enumb = producta enum enum"

 
fun map_of :: "(('b :: eq) * 'a) list \<Rightarrow> ('b :: eq) \<Rightarrow> 'a option"
where
  "map_of ((l, v) # ps) k = (if eq l k then Some v
                             else map_of ps k)"
| "map_of Nil k = None"

 
fun the :: "'a option \<Rightarrow> 'a"
where
  "the (Some x) = x"

 
fun list_all :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "list_all p Nil = True"
| "list_all p (x # xs) = (p x & list_all p xs)"

 
fun eq_fun :: "(('a :: Enuma) \<Rightarrow> ('b :: eq)) \<Rightarrow> (('a :: Enuma) \<Rightarrow> ('b :: eq)) \<Rightarrow> bool"
where
  "eq_fun f g = list_all (% x . eq (f x) (g x)) enum"

 
fun concata :: "('a list) list \<Rightarrow> 'a list"
where
  "concata Nil = Nil"
| "concata (x # xs) = append x (concata xs)"

 
fun n_lists :: "Nat \<Rightarrow> 'a list \<Rightarrow> ('a list) list"
where
  "n_lists Zero xs = [Nil]"
| "n_lists (Suc n) xs = concata (mapa (% ys .
                                         mapa (% y . y # ys) xs) (n_lists n xs))"

 
fun plus_nat :: "Nat \<Rightarrow> Nat \<Rightarrow> Nat"
where
  "plus_nat (Suc m) n = plus_nat m (Suc n)"
| "plus_nat Zero n = n"

 
fun len :: "'a list \<Rightarrow> Nat"
where
  "len Nil = Zero"
| "len (_ # xs) = Suc (len xs)"

 
definition enum_fun :: "(('a :: {eq, Enuma}) \<Rightarrow> ('b :: Enuma)) list"
where
  "enum_fun = (let enum_a = enum
               in mapa (% ys .
                          the o map_of (zipa enum_a ys)) (n_lists (len enum_a) enum))"

 
fun sublists :: "'a list \<Rightarrow> ('a list) list"
where
  "sublists Nil = [Nil]"
| "sublists (x # xs) = (let xss = sublists xs
                        in append (mapa (% a . x # a) xss) xss)"

 
definition enum_bool :: "bool list"
where
  "enum_bool = [False, True]"

 
definition enum_unit :: "unit list"
where
  "enum_unit = [Unity]"

 
definition enum_option :: "(('a :: Enuma) option) list"
where
  "enum_option = (None # mapa Some enum)"


end
