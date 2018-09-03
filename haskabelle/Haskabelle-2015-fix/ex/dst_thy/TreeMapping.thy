theory TreeMapping
imports Prelude
begin
 
datatype Nat = Zero
             | Suc Nat
 
class Orda =
  fixes less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  fixes less :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
 
fun mapa :: "('b \<Rightarrow> 'a) \<Rightarrow> 'b list \<Rightarrow> 'a list"
where
  "mapa f Nil = Nil"
| "mapa f (x # xs) = (f x # mapa f xs)"

 
fun nth :: "'a list \<Rightarrow> Nat \<Rightarrow> 'a"
where
  "nth (x # xs) (Suc n) = nth xs n"
| "nth (x # xs) Zero = x"

 
fun insert :: "('a :: eq) \<Rightarrow> (('a :: eq) \<Rightarrow> bool) \<Rightarrow> ('a :: eq) \<Rightarrow> bool"
where
  "insert y a x = (eq y x | a x)"

 
class Preorder = Orda
  
 
class Bot = Preorder +
  fixes bot :: 'a
 
instantiation bool :: Orda
begin
   
  fun less_eq_bool :: "bool \<Rightarrow> bool \<Rightarrow> bool"
  where
    "less_eq_bool True b = b"
  | "less_eq_bool False b = True"
  
   
  fun less_bool :: "bool \<Rightarrow> bool \<Rightarrow> bool"
  where
    "less_bool True b = False"
  | "less_bool False b = b"
  
 
instance sorry

end
 
instantiation bool :: Preorder
begin
  
 
instance sorry

end
 
instantiation bool :: Bot
begin
   
  definition bot_bool :: "bool"
  where
    "bot_bool = False"
  
 
instance sorry

end
 
definition bot_fun :: "'a \<Rightarrow> ('b :: Bot)"
where
  "bot_fun = (% _ . bot)"

 
fun set :: "('a :: eq) list \<Rightarrow> ('a :: eq) \<Rightarrow> bool"
where
  "set Nil = bot_fun"
| "set (x # xs) = insert x (set xs)"

 
datatype ('a, 'b) Tree = Empty
                       | Branch 'b 'a "('a, 'b) Tree" "('a, 'b) Tree"
 
fun dropa :: "Nat \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "dropa n Nil = Nil"
| "dropa n (x # xs) = (case n of
                          Zero \<Rightarrow> x # xs
                        | Suc m \<Rightarrow> dropa m xs)"

 
class Order = Preorder
  
 
class Linorder = Order
  
 
fun insort :: "('a :: Linorder) \<Rightarrow> ('a :: Linorder) list \<Rightarrow> ('a :: Linorder) list"
where
  "insort x Nil = [x]"
| "insort x (y # ys) = (if less_eq x y then x # (y # ys)
                        else y # insort x ys)"

 
fun sort :: "('a :: Linorder) list \<Rightarrow> ('a :: Linorder) list"
where
  "sort Nil = Nil"
| "sort (x # xs) = insort x (sort xs)"

 
fun takea :: "Nat \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "takea n Nil = Nil"
| "takea n (x # xs) = (case n of
                          Zero \<Rightarrow> Nil
                        | Suc m \<Rightarrow> x # takea m xs)"

 
datatype ('a) Itself = Type
 
fun append :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "append Nil ys = ys"
| "append (x # xs) ys = (x # append xs ys)"

 
fun keysa :: "(('a :: Linorder), 'b) Tree \<Rightarrow> ('a :: Linorder) list"
where
  "keysa Empty = Nil"
| "keysa (Branch uu k l r) = (k # append (keysa l) (keysa r))"

 
fun member :: "('a :: eq) \<Rightarrow> ('a :: eq) list \<Rightarrow> bool"
where
  "member x Nil = False"
| "member x (y # ys) = (eq x y | member x ys)"

 
fun remdups :: "('a :: eq) list \<Rightarrow> ('a :: eq) list"
where
  "remdups Nil = Nil"
| "remdups (x # xs) = (if member x xs then remdups xs
                       else x # remdups xs)"

 
fun lookupb :: "(('a :: {eq, Linorder}), 'b) Tree \<Rightarrow> ('a :: {eq, Linorder}) \<Rightarrow> 'b option"
where
  "lookupb Empty = (% _ . None)"
| "lookupb (Branch v k l r) = (% k' .
                                 (if eq k' k then Some v
                                  else (if less_eq k' k then lookupb l k' else lookupb r k')))"

 
fun is_none :: "'a option \<Rightarrow> bool"
where
  "is_none (Some x) = False"
| "is_none None = True"

 
fun filtera :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "filtera p Nil = Nil"
| "filtera p (x # xs) = (if p x then x # filtera p xs
                         else filtera p xs)"

 
fun plus_nat :: "Nat \<Rightarrow> Nat \<Rightarrow> Nat"
where
  "plus_nat (Suc m) n = plus_nat m (Suc n)"
| "plus_nat Zero n = n"

 
fun size_list :: "'a list \<Rightarrow> Nat"
where
  "size_list Nil = Zero"
| "size_list (a # list) = plus_nat (size_list list) (Suc Zero)"

 
fun sizea :: "(('a :: {eq, Linorder}), 'b) Tree \<Rightarrow> Nat"
where
  "sizea t = size_list (filtera (% x .
                                   Not (is_none x)) (mapa (lookupb t) (remdups (keysa t))))"

 
fun foldla :: "('a \<Rightarrow> 'b \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'b list \<Rightarrow> 'a"
where
  "foldla f a Nil = a"
| "foldla f a (x # xs) = foldla f (f a x) xs"

 
datatype ('a, 'b) Map = Tree "('a, 'b) Tree"
 
fun eq_nat :: "Nat \<Rightarrow> Nat \<Rightarrow> bool"
where
  "eq_nat (Suc nat') Zero = False"
| "eq_nat Zero (Suc nat') = False"
| "eq_nat (Suc nat0) (Suc nat') = eq_nat nat0 nat'"
| "eq_nat Zero Zero = True"

 
fun updatea :: "('a :: {eq, Linorder}) \<Rightarrow> 'b \<Rightarrow> (('a :: {eq, Linorder}), 'b) Tree \<Rightarrow> (('a :: {eq, Linorder}), 'b) Tree"
where
  "updatea k v Empty = Branch v k Empty Empty"
| "updatea k' v' (Branch v k l r) = (if eq k' k
                                     then Branch v' k l r
                                     else (if less_eq k' k then Branch v k (updatea k' v' l) r
                                           else Branch v k l (updatea k' v' r)))"

 
fun keys :: "(('a :: {eq, Linorder}), 'b) Map \<Rightarrow> ('a :: {eq, Linorder}) \<Rightarrow> bool"
where
  "keys (Tree t) = set (filtera (% k .
                                   Not (is_none (lookupb t k))) (remdups (keysa t)))"

 
fun size :: "(('a :: {eq, Linorder}), 'b) Map \<Rightarrow> Nat"
where
  "size (Tree t) = sizea t"

 
fun less_eq_nat :: "Nat \<Rightarrow> Nat \<Rightarrow> bool" and 
    less_nat :: "Nat \<Rightarrow> Nat \<Rightarrow> bool"
where
  "less_eq_nat (Suc m) n = less_nat m n"
| "less_eq_nat Zero n = True"
| "less_nat m (Suc n) = less_eq_nat m n"
| "less_nat n Zero = False"

 
fun eq_tree :: "(('a :: eq), ('b :: eq)) Tree \<Rightarrow> (('a :: eq), ('b :: eq)) Tree \<Rightarrow> bool"
where
  "eq_tree (Branch b' a' tree1' tree2') Empty = False"
| "eq_tree Empty (Branch b' a' tree1' tree2') = False"
| "eq_tree (Branch b a tree1 tree2) (Branch b' a' tree1' tree2') = (eq b b' & (eq a a' & (eq_tree tree1 tree1' & eq_tree tree2 tree2')))"
| "eq_tree Empty Empty = True"

 
definition empty :: "(('a :: Linorder), 'b) Map"
where
  "empty = Tree Empty"

 
fun minus_nat :: "Nat \<Rightarrow> Nat \<Rightarrow> Nat"
where
  "minus_nat (Suc m) (Suc n) = minus_nat m n"
| "minus_nat Zero n = Zero"
| "minus_nat m Zero = m"

 
fun lookupa :: "(('a :: {eq, Linorder}), 'b) Map \<Rightarrow> ('a :: {eq, Linorder}) \<Rightarrow> 'b option"
where
  "lookupa (Tree t) = lookupb t"

 
fun update :: "('a :: {eq, Linorder}) \<Rightarrow> 'b \<Rightarrow> (('a :: {eq, Linorder}), 'b) Map \<Rightarrow> (('a :: {eq, Linorder}), 'b) Map"
where
  "update k v (Tree t) = Tree (updatea k v t)"

 
fun replace :: "('a :: {eq, Linorder}) \<Rightarrow> 'b \<Rightarrow> (('a :: {eq, Linorder}), 'b) Map \<Rightarrow> (('a :: {eq, Linorder}), 'b) Map"
where
  "replace k v m = (if is_none (lookupa m k) then m
                    else update k v m)"


end
