theory AVL
imports Prelude
begin
 
datatype Nat = Suc Nat
             | Zero
 
datatype ('a) Set = Insert 'a "'a Set"
                  | Empty
 
datatype ('a) Tree = Mkt 'a "'a Tree" "'a Tree" Nat
                   | Et
 
fun ht :: "'a Tree \<Rightarrow> Nat"
where
  "ht (Mkt x l r h) = h"
| "ht Et = Zero"

 
fun bex :: "'a Set \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
where
  "bex Empty p = False"
| "bex (Insert a aa) p = (p a | bex aa p)"

 
datatype ('a) Tree_isub_0 = MKT_isub_0 'a "'a Tree_isub_0" "'a Tree_isub_0"
                          | ET_isub_0
 
fun erase :: "'a Tree \<Rightarrow> 'a Tree_isub_0"
where
  "erase (Mkt x l r h) = MKT_isub_0 x (erase l) (erase r)"
| "erase Et = ET_isub_0"

 
fun less_eq_nat :: "Nat \<Rightarrow> Nat \<Rightarrow> bool" and 
    less_nat :: "Nat \<Rightarrow> Nat \<Rightarrow> bool"
where
  "less_eq_nat (Suc m) n = less_nat m n"
| "less_eq_nat Zero n = True"
| "less_nat m (Suc n) = less_eq_nat m n"
| "less_nat n Zero = False"

 
fun maxa :: "Nat \<Rightarrow> Nat \<Rightarrow> Nat"
where
  "maxa a b = (if less_eq_nat a b then b else a)"

 
definition one_nat :: "Nat"
where
  "one_nat = Suc Zero"

 
fun plus_nat :: "Nat \<Rightarrow> Nat \<Rightarrow> Nat"
where
  "plus_nat (Suc m) n = plus_nat m (Suc n)"
| "plus_nat Zero n = n"

 
fun height :: "'a Tree_isub_0 \<Rightarrow> Nat"
where
  "height (MKT_isub_0 n l r) = plus_nat one_nat (maxa (height l) (height r))"
| "height ET_isub_0 = Zero"

 
fun eq_nat :: "Nat \<Rightarrow> Nat \<Rightarrow> bool"
where
  "eq_nat Zero Zero = True"
| "eq_nat (Suc m) (Suc n) = eq_nat m n"
| "eq_nat Zero (Suc a) = False"
| "eq_nat (Suc a) Zero = False"

 
fun hinv :: "'a Tree \<Rightarrow> bool"
where
  "hinv (Mkt x l r h) = (eq_nat h (plus_nat one_nat (maxa (height (erase l)) (height (erase r)))) & (hinv l & hinv r))"
| "hinv Et = True"

 
fun is_bal :: "'a Tree_isub_0 \<Rightarrow> bool"
where
  "is_bal (MKT_isub_0 n l r) = ((eq_nat (height l) (height r) | (eq_nat (height l) (plus_nat one_nat (height r)) | eq_nat (height r) (plus_nat one_nat (height l)))) & (is_bal l & is_bal r))"
| "is_bal ET_isub_0 = True"

 
fun avl :: "'a Tree \<Rightarrow> bool"
where
  "avl t = (is_bal (erase t) & hinv t)"

 
fun ball :: "'a Set \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
where
  "ball Empty p = True"
| "ball (Insert a aa) p = (p a & ball aa p)"

 
fun mkta :: "'a \<Rightarrow> 'a Tree \<Rightarrow> 'a Tree \<Rightarrow> 'a Tree"
where
  "mkta x l r = Mkt x l r (plus_nat (maxa (ht l) (ht r)) one_nat)"

 
fun member :: "Nat \<Rightarrow> Nat Set \<Rightarrow> bool"
where
  "member a aa = bex aa (eq_nat a)"

 
fun union :: "Nat Set \<Rightarrow> Nat Set \<Rightarrow> Nat Set"
where
  "union a Empty = a"
| "union Empty a = a"
| "union (Insert a aa) b = (let c = union aa b
                            in (if member a b then c else Insert a c))"

 
fun tree_case :: "'t \<Rightarrow> ('a \<Rightarrow> 'a Tree \<Rightarrow> 'a Tree \<Rightarrow> Nat \<Rightarrow> 't) \<Rightarrow> 'a Tree \<Rightarrow> 't"
where
  "tree_case f1 f2 Et = f1"
| "tree_case f1 f2 (Mkt a tree1 tree2 n) = f2 a tree1 tree2 n"

 
fun r_bal :: "'a * (('a Tree) * ('a Tree)) \<Rightarrow> 'a Tree"
where
  "r_bal (n, (l, (Mkt rn rl rr h))) = (if less_nat (ht rr) (ht rl)
                                       then (case rl of
                                                Et \<Rightarrow> Et
                                              | Mkt rln rll rlr ha \<Rightarrow> mkta rln (mkta n l rll) (mkta rn rlr rr))
                                       else mkta rn (mkta n l rl) rr)"

 
fun l_bal :: "'a * (('a Tree) * ('a Tree)) \<Rightarrow> 'a Tree"
where
  "l_bal (n, (Mkt ln ll lr h, r)) = (if less_nat (ht ll) (ht lr)
                                     then (case lr of
                                              Et \<Rightarrow> Et
                                            | Mkt lrn lrl lrr lrh \<Rightarrow> mkta lrn (mkta ln ll lrl) (mkta n lrr r))
                                     else mkta ln ll (mkta n lr r))"

 
fun insrt :: "Nat \<Rightarrow> Nat Tree \<Rightarrow> Nat Tree"
where
  "insrt x (Mkt n l r h) = (if eq_nat x n then Mkt n l r h
                            else (if less_nat x n
                                  then let l' = insrt x l;
                                           hl' = ht l';
                                           hr = ht r
                                       in (if eq_nat hl' (plus_nat (Suc (Suc Zero)) hr)
                                           then l_bal (n, (l', r))
                                           else Mkt n l' r (plus_nat one_nat (maxa hl' hr)))
                                  else let r' = insrt x r;
                                           hl = ht l;
                                           hr' = ht r'
                                       in (if eq_nat hr' (plus_nat (Suc (Suc Zero)) hl)
                                           then r_bal (n, (l, r'))
                                           else Mkt n l r' (plus_nat one_nat (maxa hl hr')))))"
| "insrt x Et = Mkt x Et Et one_nat"

 
fun is_in :: "Nat \<Rightarrow> Nat Tree \<Rightarrow> bool"
where
  "is_in k (Mkt n l r h) = (if eq_nat k n then True
                            else (if less_nat k n then is_in k l else is_in k r))"
| "is_in k Et = False"

 
fun set_of :: "Nat Tree_isub_0 \<Rightarrow> Nat Set"
where
  "set_of (MKT_isub_0 n l r) = Insert n (union (set_of l) (set_of r))"
| "set_of ET_isub_0 = Empty"

 
fun is_ord :: "Nat Tree_isub_0 \<Rightarrow> bool"
where
  "is_ord (MKT_isub_0 n l r) = (ball (set_of l) (% n' .
                                                   less_nat n' n) & (ball (set_of r) (less_nat n) & (is_ord l & is_ord r)))"
| "is_ord ET_isub_0 = True"

 
fun tree_rec :: "'t \<Rightarrow> ('a \<Rightarrow> 'a Tree \<Rightarrow> 'a Tree \<Rightarrow> Nat \<Rightarrow> 't \<Rightarrow> 't \<Rightarrow> 't) \<Rightarrow> 'a Tree \<Rightarrow> 't"
where
  "tree_rec f1 f2 (Mkt a tree1 tree2 n) = f2 a tree1 tree2 n (tree_rec f1 f2 tree1) (tree_rec f1 f2 tree2)"
| "tree_rec f1 f2 Et = f1"

 
fun size_tree :: "'a Tree \<Rightarrow> Nat"
where
  "size_tree (Mkt a tree1 tree2 n) = plus_nat (plus_nat (size_tree tree1) (size_tree tree2)) (Suc Zero)"
| "size_tree Et = Zero"

 
fun tree_size :: "('a \<Rightarrow> Nat) \<Rightarrow> 'a Tree \<Rightarrow> Nat"
where
  "tree_size fa (Mkt a tree1 tree2 n) = plus_nat (plus_nat (plus_nat (fa a) (tree_size fa tree1)) (tree_size fa tree2)) (Suc Zero)"
| "tree_size fa Et = Zero"

 
fun tree_isub_0_case :: "'t \<Rightarrow> ('a \<Rightarrow> 'a Tree_isub_0 \<Rightarrow> 'a Tree_isub_0 \<Rightarrow> 't) \<Rightarrow> 'a Tree_isub_0 \<Rightarrow> 't"
where
  "tree_isub_0_case f1 f2 ET_isub_0 = f1"
| "tree_isub_0_case f1 f2 (MKT_isub_0 a tree_isub_01 tree_isub_02) = f2 a tree_isub_01 tree_isub_02"

 
fun r_bal_isub_0 :: "'a * (('a Tree_isub_0) * ('a Tree_isub_0)) \<Rightarrow> 'a Tree_isub_0"
where
  "r_bal_isub_0 (n, (l, (MKT_isub_0 rn rl rr))) = (if less_nat (height rr) (height rl)
                                                   then (case rl of
                                                            ET_isub_0 \<Rightarrow> ET_isub_0
                                                          | MKT_isub_0 rln rll rlr \<Rightarrow> MKT_isub_0 rln (MKT_isub_0 n l rll) (MKT_isub_0 rn rlr rr))
                                                   else MKT_isub_0 rn (MKT_isub_0 n l rl) rr)"

 
fun l_bal_isub_0 :: "'a * (('a Tree_isub_0) * ('a Tree_isub_0)) \<Rightarrow> 'a Tree_isub_0"
where
  "l_bal_isub_0 (n, (MKT_isub_0 ln ll lr, r)) = (if less_nat (height ll) (height lr)
                                                 then (case lr of
                                                          ET_isub_0 \<Rightarrow> ET_isub_0
                                                        | MKT_isub_0 lrn lrl lrr \<Rightarrow> MKT_isub_0 lrn (MKT_isub_0 ln ll lrl) (MKT_isub_0 n lrr r))
                                                 else MKT_isub_0 ln ll (MKT_isub_0 n lr r))"

 
fun insrt_isub_0 :: "Nat \<Rightarrow> Nat Tree_isub_0 \<Rightarrow> Nat Tree_isub_0"
where
  "insrt_isub_0 x (MKT_isub_0 n l r) = (if eq_nat x n
                                        then MKT_isub_0 n l r
                                        else (if less_nat x n
                                              then let l' = insrt_isub_0 x l
                                                   in (if eq_nat (height l') (plus_nat (Suc (Suc Zero)) (height r))
                                                       then l_bal_isub_0 (n, (l', r))
                                                       else MKT_isub_0 n l' r)
                                              else let r' = insrt_isub_0 x r
                                                   in (if eq_nat (height r') (plus_nat (Suc (Suc Zero)) (height l))
                                                       then r_bal_isub_0 (n, (l, r'))
                                                       else MKT_isub_0 n l r')))"
| "insrt_isub_0 x ET_isub_0 = MKT_isub_0 x ET_isub_0 ET_isub_0"

 
fun is_in_isub_0 :: "Nat \<Rightarrow> Nat Tree_isub_0 \<Rightarrow> bool"
where
  "is_in_isub_0 k (MKT_isub_0 n l r) = (if eq_nat k n then True
                                        else (if less_nat k n then is_in_isub_0 k l
                                              else is_in_isub_0 k r))"
| "is_in_isub_0 k ET_isub_0 = False"

 
fun tree_isub_0_rec :: "'t \<Rightarrow> ('a \<Rightarrow> 'a Tree_isub_0 \<Rightarrow> 'a Tree_isub_0 \<Rightarrow> 't \<Rightarrow> 't \<Rightarrow> 't) \<Rightarrow> 'a Tree_isub_0 \<Rightarrow> 't"
where
  "tree_isub_0_rec f1 f2 (MKT_isub_0 a tree_isub_01 tree_isub_02) = f2 a tree_isub_01 tree_isub_02 (tree_isub_0_rec f1 f2 tree_isub_01) (tree_isub_0_rec f1 f2 tree_isub_02)"
| "tree_isub_0_rec f1 f2 ET_isub_0 = f1"

 
fun size_tree_isub_0 :: "'a Tree_isub_0 \<Rightarrow> Nat"
where
  "size_tree_isub_0 (MKT_isub_0 a tree_isub_01 tree_isub_02) = plus_nat (plus_nat (size_tree_isub_0 tree_isub_01) (size_tree_isub_0 tree_isub_02)) (Suc Zero)"
| "size_tree_isub_0 ET_isub_0 = Zero"

 
fun tree_isub_0_size :: "('a \<Rightarrow> Nat) \<Rightarrow> 'a Tree_isub_0 \<Rightarrow> Nat"
where
  "tree_isub_0_size fa (MKT_isub_0 a tree_isub_01 tree_isub_02) = plus_nat (plus_nat (plus_nat (fa a) (tree_isub_0_size fa tree_isub_01)) (tree_isub_0_size fa tree_isub_02)) (Suc Zero)"
| "tree_isub_0_size fa ET_isub_0 = Zero"


end
