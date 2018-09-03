theory ListsAndMaps
imports Prelude
begin
 
datatype Inta = Number_of_int Inta
              | Bit1 Inta
              | Bit0 Inta
              | Min
              | Pls
 
datatype Nat = Suc Nat
             | Zero
 
fun leta :: "'b \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'a"
where
  "leta s f = f s"

 
class Orda =
  fixes less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  fixes less :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
 
fun hd :: "'a list \<Rightarrow> 'a"
where
  "hd (x # xs) = x"

 
fun tl :: "'a list \<Rightarrow> 'a list"
where
  "tl (x # xs) = xs"
| "tl Nil = Nil"

 
fun eqop :: "('a :: eq) \<Rightarrow> ('a :: eq) \<Rightarrow> bool"
where
  "eqop a = (% b . eq a b)"

 
class Plus =
  fixes plus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
 
class Zero =
  fixes zero :: 'a
 
fun preda :: "Inta \<Rightarrow> Inta"
where
  "preda (Bit1 k) = Bit0 k"
| "preda (Bit0 k) = Bit1 (preda k)"
| "preda Min = Bit0 Min"
| "preda Pls = Min"

 
fun succa :: "Inta \<Rightarrow> Inta"
where
  "succa (Bit1 k) = Bit0 (succa k)"
| "succa (Bit0 k) = Bit1 k"
| "succa Min = Pls"
| "succa Pls = Bit1 Pls"

 
datatype Nibble = NibbleF
                | NibbleE
                | NibbleD
                | NibbleC
                | NibbleB
                | NibbleA
                | Nibble9
                | Nibble8
                | Nibble7
                | Nibble6
                | Nibble5
                | Nibble4
                | Nibble3
                | Nibble2
                | Nibble1
                | Nibble0
 
datatype Chara = Chara Nibble Nibble
 
fun mapa :: "('b \<Rightarrow> 'a) \<Rightarrow> 'b list \<Rightarrow> 'a list"
where
  "mapa f (x # xs) = (f x # mapa f xs)"
| "mapa f Nil = Nil"

 
fun nat_case :: "'t \<Rightarrow> (Nat \<Rightarrow> 't) \<Rightarrow> Nat \<Rightarrow> 't"
where
  "nat_case f1 f2 Zero = f1"
| "nat_case f1 f2 (Suc nat0) = f2 nat0"

 
fun nth :: "'a list \<Rightarrow> Nat \<Rightarrow> 'a"
where
  "nth (x # xs) n = (case n of
                        Zero \<Rightarrow> x
                      | Suc a \<Rightarrow> nth xs a)"

 
fun foldla :: "('a \<Rightarrow> 'b \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'b list \<Rightarrow> 'a"
where
  "foldla f a (x # xs) = foldla f (f a x) xs"
| "foldla f a Nil = a"

 
fun rev :: "'a list \<Rightarrow> 'a list"
where
  "rev xs = foldla (% xsa x . x # xsa) Nil xs"

 
fun less_eq_nat :: "Nat \<Rightarrow> Nat \<Rightarrow> bool" and 
    less_nat :: "Nat \<Rightarrow> Nat \<Rightarrow> bool"
where
  "less_eq_nat (Suc m) n = less_nat m n"
| "less_eq_nat Zero n = True"
| "less_nat m (Suc n) = less_eq_nat m n"
| "less_nat n Zero = False"

 
fun list_case :: "'t \<Rightarrow> ('a \<Rightarrow> 'a list \<Rightarrow> 't) \<Rightarrow> 'a list \<Rightarrow> 't"
where
  "list_case f1 f2 Nil = f1"
| "list_case f1 f2 (a # list) = f2 a list"

 
fun zipa :: "'a list \<Rightarrow> 'b list \<Rightarrow> ('a * 'b) list"
where
  "zipa xs (y # ys) = (case xs of
                          Nil \<Rightarrow> Nil
                        | z # zs \<Rightarrow> (z, y) # zipa zs ys)"
| "zipa xs Nil = Nil"

 
fun dropa :: "Nat \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "dropa n (x # xs) = (case n of
                          Zero \<Rightarrow> x # xs
                        | Suc m \<Rightarrow> dropa m xs)"
| "dropa n Nil = Nil"

 
fun nulla :: "'a list \<Rightarrow> bool"
where
  "nulla (x # xs) = False"
| "nulla Nil = True"

 
fun lasta :: "'a list \<Rightarrow> 'a"
where
  "lasta (x # xs) = (if nulla xs then x else lasta xs)"

 
class Order = Orda
  
 
class Linorder = Order
  
 
fun insort :: "('a :: Linorder) \<Rightarrow> ('a :: Linorder) list \<Rightarrow> ('a :: Linorder) list"
where
  "insort x (y # ys) = (if less_eq x y then x # (y # ys)
                        else y # insort x ys)"
| "insort x Nil = [x]"

 
fun sort :: "('a :: Linorder) list \<Rightarrow> ('a :: Linorder) list"
where
  "sort (x # xs) = insort x (sort xs)"
| "sort Nil = Nil"

 
fun takea :: "Nat \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "takea n (x # xs) = (case n of
                          Zero \<Rightarrow> Nil
                        | Suc m \<Rightarrow> x # takea m xs)"
| "takea n Nil = Nil"

 
class Finite_intvl_succ = Linorder +
  fixes successor :: "'a \<Rightarrow> 'a"
 
datatype ('a) Itself = Type
 
fun foldra :: "('b \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'b list \<Rightarrow> 'a \<Rightarrow> 'a"
where
  "foldra f (x # xs) a = f x (foldra f xs a)"
| "foldra f Nil a = a"

 
fun map_of :: "(('b :: eq) * 'c) list \<Rightarrow> ('b :: eq) \<Rightarrow> 'c option"
where
  "map_of ((l, v) # ps) k = (if eqop l k then Some v
                             else map_of ps k)"
| "map_of Nil k = None"

 
fun append :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "append (x # xs) ys = (x # append xs ys)"
| "append Nil ys = ys"

 
fun concata :: "('a list) list \<Rightarrow> 'a list"
where
  "concata (x # xs) = append x (concata xs)"
| "concata Nil = Nil"

 
fun filtera :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "filtera p (x # xs) = (if p x then x # filtera p xs
                         else filtera p xs)"
| "filtera p Nil = Nil"

 
fun member :: "('a :: eq) \<Rightarrow> ('a :: eq) list \<Rightarrow> bool"
where
  "member x (y # ys) = (if eqop y x then True else member x ys)"
| "member x Nil = False"

 
fun rotate1 :: "'a list \<Rightarrow> 'a list"
where
  "rotate1 xs = (case xs of
                    Nil \<Rightarrow> Nil
                  | x # xsa \<Rightarrow> append xsa [x])"

 
fun fun_pow :: "Nat \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a"
where
  "fun_pow (Suc n) f = (f o fun_pow n f)"
| "fun_pow Zero f = id"

 
fun rotate :: "Nat \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "rotate n = fun_pow n rotate1"

 
fun sorted :: "('a :: Linorder) list \<Rightarrow> bool"
where
  "sorted (x # (y # zs)) = (less_eq x y & sorted (y # zs))"
| "sorted [x] = True"
| "sorted Nil = True"

 
fun splice :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "splice (x # xs) (y # ys) = (x # (y # splice xs ys))"
| "splice xs Nil = xs"
| "splice Nil ys = ys"

 
fun option_case :: "'t \<Rightarrow> ('a \<Rightarrow> 't) \<Rightarrow> 'a option \<Rightarrow> 't"
where
  "option_case f1 f2 None = f1"
| "option_case f1 f2 (Some a) = f2 a"

 
fun map_add :: "('a \<Rightarrow> 'b option) \<Rightarrow> ('a \<Rightarrow> 'b option) \<Rightarrow> 'a \<Rightarrow> 'b option"
where
  "map_add m1 m2 = (% x .
                      (case m2 x of
                          None \<Rightarrow> m1 x
                        | Some a \<Rightarrow> Some a))"

 
fun plus_int :: "Inta \<Rightarrow> Inta \<Rightarrow> Inta"
where
  "plus_int (Number_of_int v) (Number_of_int w) = Number_of_int (plus_int v w)"
| "plus_int (Bit1 k) (Bit1 l) = Bit0 (plus_int k (succa l))"
| "plus_int (Bit1 k) (Bit0 l) = Bit1 (plus_int k l)"
| "plus_int (Bit0 k) (Bit1 l) = Bit1 (plus_int k l)"
| "plus_int (Bit0 k) (Bit0 l) = Bit0 (plus_int k l)"
| "plus_int k Min = preda k"
| "plus_int k Pls = k"
| "plus_int Min k = preda k"
| "plus_int Pls k = k"

 
fun butlast :: "'a list \<Rightarrow> 'a list"
where
  "butlast (x # xs) = (if nulla xs then Nil else x # butlast xs)"
| "butlast Nil = Nil"

 
fun list_ex :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "list_ex p (x # xs) = (p x | list_ex p xs)"
| "list_ex p Nil = False"

 
class Semigroup_add = Plus
  
 
class Monoid_add = Zero+ Semigroup_add
  
 
fun listsum :: "('a :: Monoid_add) list \<Rightarrow> ('a :: Monoid_add)"
where
  "listsum (x # xs) = plus x (foldla plus zero xs)"
| "listsum Nil = zero"

 
fun remdups :: "('a :: eq) list \<Rightarrow> ('a :: eq) list"
where
  "remdups (x # xs) = (if member x xs then remdups xs
                       else x # remdups xs)"
| "remdups Nil = Nil"

 
fun remove1 :: "('a :: eq) \<Rightarrow> ('a :: eq) list \<Rightarrow> ('a :: eq) list"
where
  "remove1 x (y # xs) = (if eqop x y then xs
                         else y # remove1 x xs)"
| "remove1 x Nil = Nil"

 
fun map_comp :: "('b \<Rightarrow> 'c option) \<Rightarrow> ('a \<Rightarrow> 'b option) \<Rightarrow> 'a \<Rightarrow> 'c option"
where
  "map_comp f g = (% k .
                     (case g k of
                         None \<Rightarrow> None
                       | Some a \<Rightarrow> f a))"

 
fun map_upds :: "(('a :: eq) \<Rightarrow> 'b option) \<Rightarrow> ('a :: eq) list \<Rightarrow> 'b list \<Rightarrow> ('a :: eq) \<Rightarrow> 'b option"
where
  "map_upds m xs ys = map_add m (map_of (rev (zipa xs ys)))"

 
fun plus_nat :: "Nat \<Rightarrow> Nat \<Rightarrow> Nat"
where
  "plus_nat (Suc m) n = plus_nat m (Suc n)"
| "plus_nat Zero n = n"

 
fun char_rec :: "(Nibble \<Rightarrow> Nibble \<Rightarrow> 't) \<Rightarrow> Chara \<Rightarrow> 't"
where
  "char_rec f1 (Chara nibble1 nibble2) = f1 nibble1 nibble2"

 
fun distinct :: "('a :: eq) list \<Rightarrow> bool"
where
  "distinct (x # xs) = (Not (member x xs) & distinct xs)"
| "distinct Nil = True"

 
fun list_all :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "list_all p (x # xs) = (p x & list_all p xs)"
| "list_all p Nil = True"

 
fun list_rec :: "'t \<Rightarrow> ('a \<Rightarrow> 'a list \<Rightarrow> 't \<Rightarrow> 't) \<Rightarrow> 'a list \<Rightarrow> 't"
where
  "list_rec f1 f2 (a # list) = f2 a list (list_rec f1 f2 list)"
| "list_rec f1 f2 Nil = f1"

 
fun char_case :: "(Nibble \<Rightarrow> Nibble \<Rightarrow> 't) \<Rightarrow> Chara \<Rightarrow> 't"
where
  "char_case f1 (Chara nibble1 nibble2) = f1 nibble1 nibble2"

 
fun char_size :: "Chara \<Rightarrow> Nat"
where
  "char_size (Chara nibble1 nibble2) = Zero"

 
fun dropWhilea :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "dropWhilea p (x # xs) = (if p x then dropWhilea p xs
                            else x # xs)"
| "dropWhilea p Nil = Nil"

 
fun filtermap :: "('a \<Rightarrow> 'b option) \<Rightarrow> 'a list \<Rightarrow> 'b list"
where
  "filtermap f (x # xs) = (case f x of
                              None \<Rightarrow> filtermap f xs
                            | Some y \<Rightarrow> y # filtermap f xs)"
| "filtermap f Nil = Nil"

 
fun list_all2 :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> bool"
where
  "list_all2 p (x # xs) (y # ys) = (p x y & list_all2 p xs ys)"
| "list_all2 p xs Nil = nulla xs"
| "list_all2 p Nil ys = nulla ys"

 
fun list_size :: "('a \<Rightarrow> Nat) \<Rightarrow> 'a list \<Rightarrow> Nat"
where
  "list_size fa (a # list) = plus_nat (plus_nat (fa a) (list_size fa list)) (Suc Zero)"
| "list_size fa Nil = Zero"

 
fun split :: "('b \<Rightarrow> 'c \<Rightarrow> 'a) \<Rightarrow> 'b * 'c \<Rightarrow> 'a"
where
  "split f (a, b) = f a b"

 
fun partition :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> ('a list) * ('a list)"
where
  "partition p (x # xs) = (let a = partition p xs;
                               (yes, no) = a
                           in (if p x then (x # yes, no) else (yes, (x # no))))"
| "partition p Nil = (Nil, Nil)"

 
fun replicatea :: "Nat \<Rightarrow> 'a \<Rightarrow> 'a list"
where
  "replicatea (Suc n) x = (x # replicatea n x)"
| "replicatea Zero x = Nil"

 
fun size_char :: "Chara \<Rightarrow> Nat"
where
  "size_char (Chara nibble1 nibble2) = Zero"

 
fun size_list :: "'a list \<Rightarrow> Nat"
where
  "size_list (a # list) = plus_nat (size_list list) (Suc Zero)"
| "size_list Nil = Zero"

 
fun takeWhilea :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "takeWhilea p (x # xs) = (if p x then x # takeWhilea p xs
                            else Nil)"
| "takeWhilea p Nil = Nil"

 
fun list_inter :: "('a :: eq) list \<Rightarrow> ('a :: eq) list \<Rightarrow> ('a :: eq) list"
where
  "list_inter (a # asa) bs = (if member a bs
                              then a # list_inter asa bs else list_inter asa bs)"
| "list_inter Nil bs = Nil"

 
fun map_filter :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'b list"
where
  "map_filter f p (x # xs) = (if p x then f x # map_filter f p xs
                              else map_filter f p xs)"
| "map_filter f p Nil = Nil"

 
definition itself_char :: "Chara Itself"
where
  "itself_char = Type"

 
definition itself_list :: "('a list) Itself"
where
  "itself_list = Type"

 
fun list_update :: "'a list \<Rightarrow> Nat \<Rightarrow> 'a \<Rightarrow> 'a list"
where
  "list_update (x # xs) i v = (case i of
                                  Zero \<Rightarrow> v # xs
                                | Suc j \<Rightarrow> x # list_update xs j v)"
| "list_update Nil i v = Nil"

 
definition itself_nibble :: "Nibble Itself"
where
  "itself_nibble = Type"

 
definition successor_int :: "Inta \<Rightarrow> Inta"
where
  "successor_int = (% i . plus_int i (Number_of_int (Bit1 Pls)))"


end
