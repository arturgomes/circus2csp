theory Rationals
imports Prelude
begin
 
datatype Nat = Zero
             | Suc Nat
 
fun leta :: "'b \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'a"
where
  "leta s f = f s"

 
class One =
  fixes one :: 'a
 
class Orda =
  fixes less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  fixes less :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
 
fun nat_aux :: "int \<Rightarrow> Nat \<Rightarrow> Nat"
where
  "nat_aux i n = (if i <= 0 then n else nat_aux (i - 1) (Suc n))"

 
fun nat :: "int \<Rightarrow> Nat"
where
  "nat i = nat_aux i Zero"

 
class Plus =
  fixes plus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
 
class Zero =
  fixes zero :: 'a
 
class Minus =
  fixes minus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
 
class Times =
  fixes times :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
 
datatype ('a) Itself = Type
 
class Inverse =
  fixes inverse :: "'a \<Rightarrow> 'a"
  fixes divide :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
 
class Uminus =
  fixes neg :: "'a \<Rightarrow> 'a"
 
instantiation int :: Times
begin
   
  fun times_int :: "int \<Rightarrow> int \<Rightarrow> int"
  where
    "times_int a b = (a * b)"
  
 
instance sorry

end
 
class Dvd = Times
  
 
instantiation int :: Dvd
begin
  
 
instance sorry

end
 
class Zero_neq_one = One+ Zero
  
 
class Semigroup_mult = Times
  
 
class Semigroup_add = Plus
  
 
class Ab_semigroup_add = Semigroup_add
  
 
class Semiring = Ab_semigroup_add+ Semigroup_mult
  
 
class Mult_zero = Times+ Zero
  
 
class Monoid_add = Zero+ Semigroup_add
  
 
class Comm_monoid_add = Ab_semigroup_add+ Monoid_add
  
 
class Semiring_0 = Comm_monoid_add+ Mult_zero+ Semiring
  
 
class Cancel_semigroup_add = Semigroup_add
  
 
class Cancel_ab_semigroup_add = Ab_semigroup_add+ Cancel_semigroup_add
  
 
class Cancel_comm_monoid_add = Cancel_ab_semigroup_add+ Comm_monoid_add
  
 
class Semiring_0_cancel = Cancel_comm_monoid_add+ Semiring_0
  
 
class Power = One+ Times
  
 
class Monoid_mult = Semigroup_mult+ Power
  
 
class Semiring_1 = Monoid_mult+ Semiring_0+ Zero_neq_one
  
 
class Semiring_1_cancel = Semiring_0_cancel+ Semiring_1
  
 
fun split :: "('b \<Rightarrow> 'c \<Rightarrow> 'a) \<Rightarrow> 'b * 'c \<Rightarrow> 'a"
where
  "split f (a, b) = f a b"

 
fun abs_int :: "int \<Rightarrow> int"
where
  "abs_int i = (if i < 0 then uminus i else i)"

 
fun sgn_int :: "int \<Rightarrow> int"
where
  "sgn_int i = (if eq i 0 then 0
                else (if 0 < i then 1 else uminus 1))"

 
fun apsnd :: "('c \<Rightarrow> 'b) \<Rightarrow> 'a * 'c \<Rightarrow> 'a * 'b"
where
  "apsnd f (x, y) = (x, (f y))"

 
function (sequential) divmod'0
where
  "divmod'0 k l = (if eq l 0 | (k < l) then (0, k)
                   else let (q, r) = divmod'0 (k - l) l
                        in (q + 1, r))"
sorry termination sorry
 
function (sequential) divmod_int :: "int \<Rightarrow> int \<Rightarrow> int * int"
where
  "divmod_int k l = (let divmod' = divmod'0
                     in (if eq k 0 then (0, 0)
                         else (if eq l 0 then (0, k)
                               else apsnd (% a . sgn_int l * a) (if eq (sgn_int k) (sgn_int l)
                                                                 then (% k l .
                                                                         divmod' (abs k) (abs l)) k l
                                                                 else let (r, s) = (% k l .
                                                                                      divmod' (abs k) (abs l)) k l
                                                                      in (if eq s 0
                                                                          then (uminus r, 0)
                                                                          else (uminus r - 1, (abs_int l - s)))))))"
sorry termination sorry
 
class Group_add = Minus+ Uminus+ Monoid_add
  
 
class Ab_group_add = Cancel_comm_monoid_add+ Group_add
  
 
class Ring = Ab_group_add+ Semiring_0_cancel
  
 
class Ring_1 = Ring+ Semiring_1_cancel
  
 
function (sequential) of_int :: "int \<Rightarrow> ('a :: Ring_1)"
where
  "of_int k = (if eq k 0 then zero
               else (if k < 0 then neg (of_int (uminus k))
                     else let (l, m) = divmod_int k 2;
                              l' = of_int l
                          in (if eq m 0 then plus l' l' else plus (plus l' l') one)))"
sorry termination sorry
 
instantiation int :: One
begin
   
  definition one_int :: "int"
  where
    "one_int = 1"
  
 
instance sorry

end
 
instantiation int :: Zero
begin
   
  definition zero_int :: "int"
  where
    "zero_int = 1"
  
 
instance sorry

end
 
fun eq_nat :: "Nat \<Rightarrow> Nat \<Rightarrow> bool"
where
  "eq_nat (Suc nat') Zero = False"
| "eq_nat Zero (Suc nat') = False"
| "eq_nat (Suc nat2) (Suc nat') = eq_nat nat2 nat'"
| "eq_nat Zero Zero = True"

 
fun of_nat_aux :: "(('a :: Semiring_1) \<Rightarrow> ('a :: Semiring_1)) \<Rightarrow> Nat \<Rightarrow> ('a :: Semiring_1) \<Rightarrow> ('a :: Semiring_1)"
where
  "of_nat_aux inc Zero i = i"
| "of_nat_aux inc (Suc n) i = of_nat_aux inc n (inc i)"

 
function (sequential) of_nat :: "Nat \<Rightarrow> ('a :: Semiring_1)"
where
  "of_nat n = of_nat_aux (% i . plus i one) n zero"
sorry termination sorry
 
datatype Nibble = Nibble0
                | Nibble1
                | Nibble2
                | Nibble3
                | Nibble4
                | Nibble5
                | Nibble6
                | Nibble7
                | Nibble8
                | Nibble9
                | NibbleA
                | NibbleB
                | NibbleC
                | NibbleD
                | NibbleE
                | NibbleF
 
datatype Chara = Chara Nibble Nibble
 
class Div = Dvd +
  fixes diva :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  fixes moda :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
 
fun minus_nat :: "Nat \<Rightarrow> Nat \<Rightarrow> Nat"
where
  "minus_nat (Suc m) (Suc n) = minus_nat m n"
| "minus_nat Zero n = Zero"
| "minus_nat m Zero = m"

 
fun less_eq_nat :: "Nat \<Rightarrow> Nat \<Rightarrow> bool" and 
    less_nat :: "Nat \<Rightarrow> Nat \<Rightarrow> bool"
where
  "less_eq_nat (Suc m) n = less_nat m n"
| "less_eq_nat Zero n = True"
| "less_nat m (Suc n) = less_eq_nat m n"
| "less_nat n Zero = False"

 
function (sequential) divmod :: "Nat \<Rightarrow> Nat \<Rightarrow> Nat * Nat"
where
  "divmod m n = (if eq_nat n Zero | less_nat m n then (Zero, m)
                 else let (q, a) = divmod (minus_nat m n) n
                      in (Suc q, a))"
sorry termination sorry
 
fun mod_nat :: "Nat \<Rightarrow> Nat \<Rightarrow> Nat"
where
  "mod_nat m n = snd (divmod m n)"

 
function (sequential) gcd_nat :: "Nat \<Rightarrow> Nat \<Rightarrow> Nat"
where
  "gcd_nat x y = (if eq_nat y Zero then x
                  else gcd_nat y (mod_nat x y))"
sorry termination sorry
 
instantiation int :: Zero_neq_one
begin
  
 
instance sorry

end
 
instantiation int :: Semigroup_mult
begin
  
 
instance sorry

end
 
instantiation int :: Plus
begin
   
  fun plus_int :: "int \<Rightarrow> int \<Rightarrow> int"
  where
    "plus_int a b = (a + b)"
  
 
instance sorry

end
 
instantiation int :: Semigroup_add
begin
  
 
instance sorry

end
 
instantiation int :: Ab_semigroup_add
begin
  
 
instance sorry

end
 
instantiation int :: Semiring
begin
  
 
instance sorry

end
 
instantiation int :: Mult_zero
begin
  
 
instance sorry

end
 
instantiation int :: Monoid_add
begin
  
 
instance sorry

end
 
instantiation int :: Comm_monoid_add
begin
  
 
instance sorry

end
 
instantiation int :: Semiring_0
begin
  
 
instance sorry

end
 
instantiation int :: Power
begin
  
 
instance sorry

end
 
instantiation int :: Monoid_mult
begin
  
 
instance sorry

end
 
instantiation int :: Semiring_1
begin
  
 
instance sorry

end
 
fun gcd_int :: "int \<Rightarrow> int \<Rightarrow> int"
where
  "gcd_int x y = of_nat (gcd_nat (nat (abs_int x)) (nat (abs_int y)))"

 
datatype Rat = Fract int int
 
fun collect :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool"
where
  "collect p = p"

 
fun scomp :: "('a \<Rightarrow> 'c * 'd) \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b"
where
  "scomp f g = (% x .
                  let (a, b) = f x
                  in g a b)"

 
datatype Typerep = Typerep string "Typerep list"
 
datatype Term = Const string Typerep
              | App Term Term
 
fun mod_int :: "int \<Rightarrow> int \<Rightarrow> int"
where
  "mod_int a b = snd (divmod_int a b)"

 
fun div_int :: "int \<Rightarrow> int \<Rightarrow> int"
where
  "div_int a b = fst (divmod_int a b)"

 
instantiation int :: Div
begin
   
  definition diva_int :: "int \<Rightarrow> int \<Rightarrow> int"
  where
    "diva_int = div_int"
  
   
  definition moda_int :: "int \<Rightarrow> int \<Rightarrow> int"
  where
    "moda_int = mod_int"
  
 
instance sorry

end
 
fun maxaa :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
where
  "maxaa less_eq3 a b = (if less_eq3 a b then b else a)"

 
definition maxa :: "('a :: Orda) \<Rightarrow> ('a :: Orda) \<Rightarrow> ('a :: Orda)"
where
  "maxa = maxaa less_eq"

 
fun minaa :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
where
  "minaa less_eq4 a b = (if less_eq4 a b then a else b)"

 
definition mina :: "('a :: Orda) \<Rightarrow> ('a :: Orda) \<Rightarrow> ('a :: Orda)"
where
  "mina = minaa less_eq"

 
class Semiring_char_0 = Semiring_1
  
 
class Ring_char_0 = Semiring_char_0+ Ring_1
  
 
fun eq_rat :: "Rat \<Rightarrow> Rat \<Rightarrow> bool"
where
  "eq_rat (Fract a b) (Fract c d) = (if eq b 0 then eq c 0 | eq d 0
                                     else (if eq d 0 then eq a 0 | eq b 0 else eq (a * d) (b * c)))"

 
class No_zero_divisors = Times+ Zero
  
 
class Ring_no_zero_divisors = No_zero_divisors+ Ring
  
 
class Ring_1_no_zero_divisors = Ring_1+ Ring_no_zero_divisors
  
 
class Division_ring = Inverse+ Ring_1_no_zero_divisors
  
 
class Ab_semigroup_mult = Semigroup_mult
  
 
class Comm_semiring = Ab_semigroup_mult+ Semiring
  
 
class Comm_semiring_0 = Comm_semiring+ Semiring_0
  
 
class Comm_monoid_mult = Ab_semigroup_mult+ Monoid_mult
  
 
class Comm_semiring_1 = Comm_monoid_mult+ Comm_semiring_0+ Dvd+ Semiring_1
  
 
class Comm_semiring_0_cancel = Comm_semiring_0+ Semiring_0_cancel
  
 
class Comm_semiring_1_cancel = Comm_semiring_0_cancel+ Comm_semiring_1+ Semiring_1_cancel
  
 
class Comm_ring = Comm_semiring_0_cancel+ Ring
  
 
class Comm_ring_1 = Comm_ring+ Comm_semiring_1_cancel+ Ring_1
  
 
class Idom = Comm_ring_1+ Ring_1_no_zero_divisors
  
 
class Field = Division_ring+ Idom
  
 
class Field_char_0 = Ring_char_0+ Field
  
 
function (sequential) of_rat :: "Rat \<Rightarrow> ('a :: Field_char_0)"
where
  "of_rat (Fract a b) = (if Not (eq b 0)
                         then divide (of_int a) (of_int b) else zero)"
sorry termination sorry
 
definition one_rat :: "Rat"
where
  "one_rat = Fract 1 1"

 
instantiation Rat :: One
begin
   
  definition one_Rat :: "Rat"
  where
    "one_Rat = one_rat"
  
 
instance sorry

end
 
fun less_rat :: "Rat \<Rightarrow> Rat \<Rightarrow> bool"
where
  "less_rat (Fract a b) (Fract c d) = (if eq b 0
                                       then 0 < (sgn_int c * sgn_int d)
                                       else (if eq d 0 then (sgn_int a * sgn_int b) < 0
                                             else ((a * abs_int d) * sgn_int b) < ((c * abs_int b) * sgn_int d)))"

 
fun less_eq_rat :: "Rat \<Rightarrow> Rat \<Rightarrow> bool"
where
  "less_eq_rat (Fract a b) (Fract c d) = (if eq b 0
                                          then 0 <= (sgn_int c * sgn_int d)
                                          else (if eq d 0 then (sgn_int a * sgn_int b) <= 0
                                                else ((a * abs_int d) * sgn_int b) <= ((c * abs_int b) * sgn_int d)))"

 
instantiation Rat :: Orda
begin
   
  definition less_eq_Rat :: "Rat \<Rightarrow> Rat \<Rightarrow> bool"
  where
    "less_eq_Rat = less_eq_rat"
  
   
  definition less_Rat :: "Rat \<Rightarrow> Rat \<Rightarrow> bool"
  where
    "less_Rat = less_rat"
  
 
instance sorry

end
 
fun abs_rat :: "Rat \<Rightarrow> Rat"
where
  "abs_rat (Fract a b) = Fract (abs_int a) (abs_int b)"

 
definition inf_rat :: "Rat \<Rightarrow> Rat \<Rightarrow> Rat"
where
  "inf_rat = mina"

 
fun fract_norm :: "int \<Rightarrow> int \<Rightarrow> Rat"
where
  "fract_norm a b = (if eq a 0 | eq b 0 then Fract 0 1
                     else let c = gcd_int a b
                          in (if 0 < b then Fract (div_int a c) (div_int b c)
                              else Fract (uminus (div_int a c)) (uminus (div_int b c))))"

 
fun plus_rat :: "Rat \<Rightarrow> Rat \<Rightarrow> Rat"
where
  "plus_rat (Fract a b) (Fract c d) = (if eq b 0 then Fract c d
                                       else (if eq d 0 then Fract a b
                                             else fract_norm ((a * d) + (c * b)) (b * d)))"

 
instantiation Rat :: Plus
begin
   
  definition plus_Rat :: "Rat \<Rightarrow> Rat \<Rightarrow> Rat"
  where
    "plus_Rat = plus_rat"
  
 
instance sorry

end
 
fun times_rat :: "Rat \<Rightarrow> Rat \<Rightarrow> Rat"
where
  "times_rat (Fract a b) (Fract c d) = fract_norm (a * c) (b * d)"

 
instantiation Rat :: Times
begin
   
  definition times_Rat :: "Rat \<Rightarrow> Rat \<Rightarrow> Rat"
  where
    "times_Rat = times_rat"
  
 
instance sorry

end
 
instantiation Rat :: Semigroup_mult
begin
  
 
instance sorry

end
 
instantiation Rat :: Semigroup_add
begin
  
 
instance sorry

end
 
instantiation Rat :: Ab_semigroup_add
begin
  
 
instance sorry

end
 
instantiation Rat :: Semiring
begin
  
 
instance sorry

end
 
definition zero_rat :: "Rat"
where
  "zero_rat = Fract 0 1"

 
instantiation Rat :: Zero
begin
   
  definition zero_Rat :: "Rat"
  where
    "zero_Rat = zero_rat"
  
 
instance sorry

end
 
instantiation Rat :: Mult_zero
begin
  
 
instance sorry

end
 
instantiation Rat :: Monoid_add
begin
  
 
instance sorry

end
 
instantiation Rat :: Comm_monoid_add
begin
  
 
instance sorry

end
 
instantiation Rat :: Semiring_0
begin
  
 
instance sorry

end
 
instantiation Rat :: Cancel_semigroup_add
begin
  
 
instance sorry

end
 
instantiation Rat :: Cancel_ab_semigroup_add
begin
  
 
instance sorry

end
 
instantiation Rat :: Cancel_comm_monoid_add
begin
  
 
instance sorry

end
 
instantiation Rat :: Semiring_0_cancel
begin
  
 
instance sorry

end
 
fun neg_rat :: "Rat \<Rightarrow> Rat"
where
  "neg_rat (Fract a b) = Fract (uminus a) b"

 
instantiation Rat :: Uminus
begin
   
  definition neg_Rat :: "Rat \<Rightarrow> Rat"
  where
    "neg_Rat = neg_rat"
  
 
instance sorry

end
 
fun minus_rat :: "Rat \<Rightarrow> Rat \<Rightarrow> Rat"
where
  "minus_rat (Fract a b) (Fract c d) = (if eq b 0
                                        then Fract (uminus c) d
                                        else (if eq d 0 then Fract a b
                                              else fract_norm ((a * d) - (c * b)) (b * d)))"

 
instantiation Rat :: Minus
begin
   
  definition minus_Rat :: "Rat \<Rightarrow> Rat \<Rightarrow> Rat"
  where
    "minus_Rat = minus_rat"
  
 
instance sorry

end
 
instantiation Rat :: Group_add
begin
  
 
instance sorry

end
 
instantiation Rat :: Ab_group_add
begin
  
 
instance sorry

end
 
instantiation Rat :: Ring
begin
  
 
instance sorry

end
 
instantiation Rat :: Zero_neq_one
begin
  
 
instance sorry

end
 
instantiation Rat :: Power
begin
  
 
instance sorry

end
 
instantiation Rat :: Monoid_mult
begin
  
 
instance sorry

end
 
instantiation Rat :: Semiring_1
begin
  
 
instance sorry

end
 
instantiation Rat :: Semiring_1_cancel
begin
  
 
instance sorry

end
 
instantiation Rat :: Ring_1
begin
  
 
instance sorry

end
 
fun sgn_rat :: "Rat \<Rightarrow> Rat"
where
  "sgn_rat (Fract a b) = of_int (sgn_int a * sgn_int b)"

 
definition sup_rat :: "Rat \<Rightarrow> Rat \<Rightarrow> Rat"
where
  "sup_rat = maxa"

 
fun divide_rat :: "Rat \<Rightarrow> Rat \<Rightarrow> Rat"
where
  "divide_rat (Fract a b) (Fract c d) = fract_norm (a * d) (b * c)"

 
instantiation int :: No_zero_divisors
begin
  
 
instance sorry

end
 
class Semiring_div = Div+ Comm_semiring_1_cancel+ No_zero_divisors
  
 
instantiation int :: Cancel_semigroup_add
begin
  
 
instance sorry

end
 
instantiation int :: Cancel_ab_semigroup_add
begin
  
 
instance sorry

end
 
instantiation int :: Cancel_comm_monoid_add
begin
  
 
instance sorry

end
 
instantiation int :: Semiring_0_cancel
begin
  
 
instance sorry

end
 
instantiation int :: Semiring_1_cancel
begin
  
 
instance sorry

end
 
instantiation int :: Ab_semigroup_mult
begin
  
 
instance sorry

end
 
instantiation int :: Comm_semiring
begin
  
 
instance sorry

end
 
instantiation int :: Comm_semiring_0
begin
  
 
instance sorry

end
 
instantiation int :: Comm_monoid_mult
begin
  
 
instance sorry

end
 
instantiation int :: Comm_semiring_1
begin
  
 
instance sorry

end
 
instantiation int :: Comm_semiring_0_cancel
begin
  
 
instance sorry

end
 
instantiation int :: Comm_semiring_1_cancel
begin
  
 
instance sorry

end
 
instantiation int :: Semiring_div
begin
  
 
instance sorry

end

end
