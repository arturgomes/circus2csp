theory Lists
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
  "tl Nil = Nil"
| "tl (x # xs) = xs"

 
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
  "mapa f Nil = Nil"
| "mapa f (x # xs) = (f x # mapa f xs)"

 
fun nat_case :: "'t \<Rightarrow> (Nat \<Rightarrow> 't) \<Rightarrow> Nat \<Rightarrow> 't"
where
  "nat_case f1 f2 (Suc nat0) = f2 nat0"
| "nat_case f1 f2 Zero = f1"

 
fun nth :: "'a list \<Rightarrow> Nat \<Rightarrow> 'a"
where
  "nth (x # xs) n = (case n of
                        Zero \<Rightarrow> x
                      | Suc a \<Rightarrow> nth xs a)"

 
fun foldla :: "('a \<Rightarrow> 'b \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'b list \<Rightarrow> 'a"
where
  "foldla f a Nil = a"
| "foldla f a (x # xs) = foldla f (f a x) xs"

 
fun rev :: "'a list \<Rightarrow> 'a list"
where
  "rev xs = foldla (% xsa x . x # xsa) Nil xs"

 
fun insert :: "('a :: eq) \<Rightarrow> (('a :: eq) \<Rightarrow> bool) \<Rightarrow> ('a :: eq) \<Rightarrow> bool"
where
  "insert y a x = (eq y x | a x)"

 
fun empty :: "'a \<Rightarrow> bool"
where
  "empty x = False"

 
fun set :: "('a :: eq) list \<Rightarrow> ('a :: eq) \<Rightarrow> bool"
where
  "set Nil = empty"
| "set (x # xs) = insert x (set xs)"

 
fun less_eq_nat :: "Nat \<Rightarrow> Nat \<Rightarrow> bool" and 
    less_nat :: "Nat \<Rightarrow> Nat \<Rightarrow> bool"
where
  "less_eq_nat (Suc m) n = less_nat m n"
| "less_eq_nat Zero n = True"
| "less_nat m (Suc n) = less_eq_nat m n"
| "less_nat n Zero = False"

 
fun list_case :: "'t \<Rightarrow> ('a \<Rightarrow> 'a list \<Rightarrow> 't) \<Rightarrow> 'a list \<Rightarrow> 't"
where
  "list_case f1 f2 (a # list) = f2 a list"
| "list_case f1 f2 Nil = f1"

 
fun zipa :: "'a list \<Rightarrow> 'b list \<Rightarrow> ('a * 'b) list"
where
  "zipa xs Nil = Nil"
| "zipa xs (y # ys) = (case xs of
                          Nil \<Rightarrow> Nil
                        | z # zs \<Rightarrow> (z, y) # zipa zs ys)"

 
fun dropa :: "Nat \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "dropa n Nil = Nil"
| "dropa n (x # xs) = (case n of
                          Zero \<Rightarrow> x # xs
                        | Suc m \<Rightarrow> dropa m xs)"

 
fun nulla :: "'a list \<Rightarrow> bool"
where
  "nulla Nil = True"
| "nulla (x # xs) = False"

 
fun lasta :: "'a list \<Rightarrow> 'a"
where
  "lasta (x # xs) = (if nulla xs then x else lasta xs)"

 
class Preorder = Orda
  
 
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

 
class Finite_intvl_succ = Linorder +
  fixes successor :: "'a \<Rightarrow> 'a"
 
datatype ('a) Itself = Type
 
fun foldra :: "('b \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'b list \<Rightarrow> 'a \<Rightarrow> 'a"
where
  "foldra f Nil a = a"
| "foldra f (x # xs) a = f x (foldra f xs a)"

 
fun membera :: "'a \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
where
  "membera x s = s x"

 
fun append :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "append Nil ys = ys"
| "append (x # xs) ys = (x # append xs ys)"

 
fun concata :: "('a list) list \<Rightarrow> 'a list"
where
  "concata Nil = Nil"
| "concata (x # xs) = append x (concata xs)"

 
fun filtera :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "filtera p Nil = Nil"
| "filtera p (x # xs) = (if p x then x # filtera p xs
                         else filtera p xs)"

 
fun member :: "('a :: eq) \<Rightarrow> ('a :: eq) list \<Rightarrow> bool"
where
  "member x Nil = False"
| "member x (y # ys) = (eq x y | member x ys)"

 
fun rotate1 :: "'a list \<Rightarrow> 'a list"
where
  "rotate1 xs = (case xs of
                    Nil \<Rightarrow> Nil
                  | x # xsa \<Rightarrow> append xsa [x])"

 
fun fun_pow :: "Nat \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a"
where
  "fun_pow Zero f = id"
| "fun_pow (Suc n) f = (f o fun_pow n f)"

 
fun rotate :: "Nat \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "rotate n = fun_pow n rotate1"

 
fun sorted :: "('a :: Linorder) list \<Rightarrow> bool"
where
  "sorted Nil = True"
| "sorted [x] = True"
| "sorted (x # (y # zs)) = (less_eq x y & sorted (y # zs))"

 
fun splice :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "splice (x # xs) (y # ys) = (x # (y # splice xs ys))"
| "splice xs Nil = xs"

 
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
  "butlast Nil = Nil"
| "butlast (x # xs) = (if nulla xs then Nil else x # butlast xs)"

 
fun list_ex :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "list_ex p Nil = False"
| "list_ex p (x # xs) = (p x | list_ex p xs)"

 
class Semigroup_add = Plus
  
 
class Monoid_add = Zero+ Semigroup_add
  
 
fun listsum :: "('a :: Monoid_add) list \<Rightarrow> ('a :: Monoid_add)"
where
  "listsum Nil = zero"
| "listsum (x # xs) = plus x (foldla plus zero xs)"

 
fun remdups :: "('a :: eq) list \<Rightarrow> ('a :: eq) list"
where
  "remdups Nil = Nil"
| "remdups (x # xs) = (if member x xs then remdups xs
                       else x # remdups xs)"

 
fun remove1 :: "('a :: eq) \<Rightarrow> ('a :: eq) list \<Rightarrow> ('a :: eq) list"
where
  "remove1 x Nil = Nil"
| "remove1 x (y # xs) = (if eq x y then xs else y # remove1 x xs)"

 
fun plus_nat :: "Nat \<Rightarrow> Nat \<Rightarrow> Nat"
where
  "plus_nat (Suc m) n = plus_nat m (Suc n)"
| "plus_nat Zero n = n"

 
fun size_list :: "'a list \<Rightarrow> Nat"
where
  "size_list Nil = Zero"
| "size_list (a # list) = plus_nat (size_list list) (Suc Zero)"

 
fun split :: "('b \<Rightarrow> 'c \<Rightarrow> 'a) \<Rightarrow> 'b * 'c \<Rightarrow> 'a"
where
  "split f (a, b) = f a b"

 
fun distinct :: "('a :: eq) list \<Rightarrow> bool"
where
  "distinct Nil = True"
| "distinct (x # xs) = (Not (member x xs) & distinct xs)"

 
fun list_all :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "list_all p Nil = True"
| "list_all p (x # xs) = (p x & list_all p xs)"

 
fun list_rec :: "'t \<Rightarrow> ('a \<Rightarrow> 'a list \<Rightarrow> 't \<Rightarrow> 't) \<Rightarrow> 'a list \<Rightarrow> 't"
where
  "list_rec f1 f2 Nil = f1"
| "list_rec f1 f2 (a # list) = f2 a list (list_rec f1 f2 list)"

 
fun char_size :: "Chara \<Rightarrow> Nat"
where
  "char_size c = Zero"

 
fun dropWhilea :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "dropWhilea p Nil = Nil"
| "dropWhilea p (x # xs) = (if p x then dropWhilea p xs
                            else x # xs)"

 
fun option_case :: "'t \<Rightarrow> ('a \<Rightarrow> 't) \<Rightarrow> 'a option \<Rightarrow> 't"
where
  "option_case f1 f2 (Some a) = f2 a"
| "option_case f1 f2 None = f1"

 
fun filtermap :: "('a \<Rightarrow> 'b option) \<Rightarrow> 'a list \<Rightarrow> 'b list"
where
  "filtermap f Nil = Nil"
| "filtermap f (x # xs) = (case f x of
                              None \<Rightarrow> filtermap f xs
                            | Some y \<Rightarrow> y # filtermap f xs)"

 
fun list_all2 :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> bool"
where
  "list_all2 p (x # xs) (y # ys) = (p x y & list_all2 p xs ys)"
| "list_all2 p xs Nil = nulla xs"
| "list_all2 p Nil ys = nulla ys"

 
fun list_size :: "('a \<Rightarrow> Nat) \<Rightarrow> 'a list \<Rightarrow> Nat"
where
  "list_size fa Nil = Zero"
| "list_size fa (a # list) = plus_nat (plus_nat (fa a) (list_size fa list)) (Suc Zero)"

 
fun partition :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> ('a list) * ('a list)"
where
  "partition p Nil = (Nil, Nil)"
| "partition p (x # xs) = (let a = partition p xs;
                               (yes, no) = a
                           in (if p x then (x # yes, no) else (yes, (x # no))))"

 
fun removeAll :: "('a :: eq) \<Rightarrow> ('a :: eq) list \<Rightarrow> ('a :: eq) list"
where
  "removeAll x Nil = Nil"
| "removeAll x (y # xs) = (if eq x y then removeAll x xs
                           else y # removeAll x xs)"

 
fun replicatea :: "Nat \<Rightarrow> 'a \<Rightarrow> 'a list"
where
  "replicatea Zero x = Nil"
| "replicatea (Suc n) x = (x # replicatea n x)"

 
fun size_char :: "Chara \<Rightarrow> Nat"
where
  "size_char c = Zero"

 
fun takeWhilea :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "takeWhilea p Nil = Nil"
| "takeWhilea p (x # xs) = (if p x then x # takeWhilea p xs
                            else Nil)"

 
fun list_inter :: "('a :: eq) list \<Rightarrow> ('a :: eq) list \<Rightarrow> ('a :: eq) list"
where
  "list_inter Nil bs = Nil"
| "list_inter (a # asa) bs = (if member a bs
                              then a # list_inter asa bs else list_inter asa bs)"

 
fun map_filter :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'b list"
where
  "map_filter f p Nil = Nil"
| "map_filter f p (x # xs) = (if p x then f x # map_filter f p xs
                              else map_filter f p xs)"

 
fun nibble_rec :: "'t \<Rightarrow> 't \<Rightarrow> 't \<Rightarrow> 't \<Rightarrow> 't \<Rightarrow> 't \<Rightarrow> 't \<Rightarrow> 't \<Rightarrow> 't \<Rightarrow> 't \<Rightarrow> 't \<Rightarrow> 't \<Rightarrow> 't \<Rightarrow> 't \<Rightarrow> 't \<Rightarrow> 't \<Rightarrow> Nibble \<Rightarrow> 't"
where
  "nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble0 = f1"
| "nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble1 = f2"
| "nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble2 = f3"
| "nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble3 = f4"
| "nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble4 = f5"
| "nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble5 = f6"
| "nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble6 = f7"
| "nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble7 = f8"
| "nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble8 = f9"
| "nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble9 = f10"
| "nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 NibbleA = f11"
| "nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 NibbleB = f12"
| "nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 NibbleC = f13"
| "nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 NibbleD = f14"
| "nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 NibbleE = f15"
| "nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 NibbleF = f16"

 
definition itself_char :: "Chara Itself"
where
  "itself_char = Type"

 
definition itself_list :: "('a list) Itself"
where
  "itself_list = Type"

 
fun list_update :: "'a list \<Rightarrow> Nat \<Rightarrow> 'a \<Rightarrow> 'a list"
where
  "list_update Nil i v = Nil"
| "list_update (x # xs) i v = (case i of
                                  Zero \<Rightarrow> v # xs
                                | Suc j \<Rightarrow> x # list_update xs j v)"

 
fun nibble_case :: "'t \<Rightarrow> 't \<Rightarrow> 't \<Rightarrow> 't \<Rightarrow> 't \<Rightarrow> 't \<Rightarrow> 't \<Rightarrow> 't \<Rightarrow> 't \<Rightarrow> 't \<Rightarrow> 't \<Rightarrow> 't \<Rightarrow> 't \<Rightarrow> 't \<Rightarrow> 't \<Rightarrow> 't \<Rightarrow> Nibble \<Rightarrow> 't"
where
  "nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 NibbleF = f16"
| "nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 NibbleE = f15"
| "nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 NibbleD = f14"
| "nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 NibbleC = f13"
| "nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 NibbleB = f12"
| "nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 NibbleA = f11"
| "nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble9 = f10"
| "nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble8 = f9"
| "nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble7 = f8"
| "nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble6 = f7"
| "nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble5 = f6"
| "nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble4 = f5"
| "nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble3 = f4"
| "nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble2 = f3"
| "nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble1 = f2"
| "nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble0 = f1"

 
fun nibble_size :: "Nibble \<Rightarrow> Nat"
where
  "nibble_size Nibble0 = Zero"
| "nibble_size Nibble1 = Zero"
| "nibble_size Nibble2 = Zero"
| "nibble_size Nibble3 = Zero"
| "nibble_size Nibble4 = Zero"
| "nibble_size Nibble5 = Zero"
| "nibble_size Nibble6 = Zero"
| "nibble_size Nibble7 = Zero"
| "nibble_size Nibble8 = Zero"
| "nibble_size Nibble9 = Zero"
| "nibble_size NibbleA = Zero"
| "nibble_size NibbleB = Zero"
| "nibble_size NibbleC = Zero"
| "nibble_size NibbleD = Zero"
| "nibble_size NibbleE = Zero"
| "nibble_size NibbleF = Zero"

 
fun size_nibble :: "Nibble \<Rightarrow> Nat"
where
  "size_nibble Nibble0 = Zero"
| "size_nibble Nibble1 = Zero"
| "size_nibble Nibble2 = Zero"
| "size_nibble Nibble3 = Zero"
| "size_nibble Nibble4 = Zero"
| "size_nibble Nibble5 = Zero"
| "size_nibble Nibble6 = Zero"
| "size_nibble Nibble7 = Zero"
| "size_nibble Nibble8 = Zero"
| "size_nibble Nibble9 = Zero"
| "size_nibble NibbleA = Zero"
| "size_nibble NibbleB = Zero"
| "size_nibble NibbleC = Zero"
| "size_nibble NibbleD = Zero"
| "size_nibble NibbleE = Zero"
| "size_nibble NibbleF = Zero"

 
definition itself_nibble :: "Nibble Itself"
where
  "itself_nibble = Type"

 
fun length_unique :: "('a :: eq) list \<Rightarrow> Nat"
where
  "length_unique Nil = Zero"
| "length_unique (x # xs) = (if member x xs then length_unique xs
                             else Suc (length_unique xs))"

 
definition successor_int :: "Inta \<Rightarrow> Inta"
where
  "successor_int = (% i . plus_int i (Number_of_int (Bit1 Pls)))"


end
