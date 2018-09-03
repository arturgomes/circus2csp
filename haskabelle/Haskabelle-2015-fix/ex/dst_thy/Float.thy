theory Float
imports Prelude
begin
 
fun positive :: "int \<Rightarrow> int"
where
  "positive k = (if k < 0 then 0 else k)"

 
fun leta :: "'b \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'a"
where
  "leta s f = f s"

 
class One =
  fixes one :: 'a
 
class Plus =
  fixes plus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
 
class Zero =
  fixes zero :: 'a
 
class Minus =
  fixes minus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
 
class Times =
  fixes times :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
 
datatype ('a) Itself = Type
 
datatype Floata = Floata int int
 
datatype Rat = Fract int int
 
fun inverse_rat :: "Rat \<Rightarrow> Rat"
where
  "inverse_rat (Fract a b) = (if eq b 0 then Fract 1 0
                              else (if a < 0 then Fract (uminus b) (uminus a) else Fract b a))"

 
datatype Reala = Ratreal Rat
 
fun inverse_real :: "Reala \<Rightarrow> Reala"
where
  "inverse_real (Ratreal x) = Ratreal (inverse_rat x)"

 
fun abs_int :: "int \<Rightarrow> int"
where
  "abs_int i = (if i < 0 then uminus i else i)"

 
fun split :: "('b \<Rightarrow> 'c \<Rightarrow> 'a) \<Rightarrow> 'b * 'c \<Rightarrow> 'a"
where
  "split f (a, b) = f a b"

 
fun sgn_int :: "int \<Rightarrow> int"
where
  "sgn_int i = (if eq i 0 then 0
                else (if 0 < i then 1 else uminus 1))"

 
fun apsnd :: "('c \<Rightarrow> 'b) \<Rightarrow> 'a * 'c \<Rightarrow> 'a * 'b"
where
  "apsnd f (x, y) = (x, (f y))"

 
function (sequential) div_mod :: "int \<Rightarrow> int \<Rightarrow> int * int"
where
  "div_mod m n = (if eq n 0 | (m < n) then (0, m)
                  else let (q, a) = div_mod (m - n) n
                       in (q + 1, a))"
sorry termination sorry
 
function (sequential) divmoda :: "int \<Rightarrow> int \<Rightarrow> int * int"
where
  "divmoda k l = (if eq k 0 then (0, 0)
                  else (if eq l 0 then (0, k)
                        else apsnd (% a . sgn_int l * a) (if eq (sgn_int k) (sgn_int l)
                                                          then (% k l . div_mod (abs k) (abs l)) k l
                                                          else let (r, s) = (% k l .
                                                                               div_mod (abs k) (abs l)) k l
                                                               in (if eq s 0 then (uminus r, 0)
                                                                   else (uminus r - 1, (abs_int l - s))))))"
sorry termination sorry
 
fun div_int :: "int \<Rightarrow> int \<Rightarrow> int"
where
  "div_int a b = fst (divmoda a b)"

 
fun divmod :: "int \<Rightarrow> int \<Rightarrow> int * int"
where
  "divmod n m = (if eq m 0 then (0, n) else div_mod n m)"

 
fun mod_nat :: "int \<Rightarrow> int \<Rightarrow> int"
where
  "mod_nat m n = snd (divmod m n)"

 
function (sequential) gcd_nat :: "int \<Rightarrow> int \<Rightarrow> int"
where
  "gcd_nat x y = (if eq y 0 then x else gcd_nat y (mod_nat x y))"
sorry termination sorry
 
fun gcd_int :: "int \<Rightarrow> int \<Rightarrow> int"
where
  "gcd_int x y = id (gcd_nat (positive (abs_int x)) (positive (abs_int y)))"

 
function (sequential) fract_norm :: "int \<Rightarrow> int \<Rightarrow> Rat"
where
  "fract_norm a b = (if eq a 0 | eq b 0 then Fract 0 1
                     else let c = gcd_int a b
                          in (if 0 < b then Fract (div_int a c) (div_int b c)
                              else Fract (uminus (div_int a c)) (uminus (div_int b c))))"
sorry termination sorry
 
fun times_rat :: "Rat \<Rightarrow> Rat \<Rightarrow> Rat"
where
  "times_rat (Fract a b) (Fract c d) = fract_norm (a * c) (b * d)"

 
fun times_real :: "Reala \<Rightarrow> Reala \<Rightarrow> Reala"
where
  "times_real (Ratreal x) (Ratreal y) = Ratreal (times_rat x y)"

 
instantiation Reala :: Times
begin
   
  definition times_Reala :: "Reala \<Rightarrow> Reala \<Rightarrow> Reala"
  where
    "times_Reala = times_real"
  
 
instance sorry

end
 
class Power = One+ Times
  
 
definition one_real :: "Reala"
where
  "one_real = Ratreal (Fract 1 1)"

 
instantiation Reala :: One
begin
   
  definition one_Reala :: "Reala"
  where
    "one_Reala = one_real"
  
 
instance sorry

end
 
instantiation Reala :: Power
begin
  
 
instance sorry

end
 
fun minus_nat :: "int \<Rightarrow> int \<Rightarrow> int"
where
  "minus_nat n m = positive (id n - id m)"

 
function (sequential) power :: "('a :: Power) \<Rightarrow> int \<Rightarrow> ('a :: Power)"
where
  "power a n = (if eq n 0 then one
                else times a (power a (minus_nat n 1)))"
sorry termination sorry
 
fun pow2 :: "int \<Rightarrow> Reala"
where
  "pow2 a = (if 0 <= a
             then power (Ratreal (Fract 2 1)) (positive a)
             else inverse_real (power (Ratreal (Fract 2 1)) (positive (uminus a))))"

 
class Neg =
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
  
 
class Monoid_mult = Semigroup_mult+ Power
  
 
class Semiring_1 = Monoid_mult+ Semiring_0+ Zero_neq_one
  
 
class Semiring_1_cancel = Semiring_0_cancel+ Semiring_1
  
 
class Group_add = Minus+ Neg+ Monoid_add
  
 
class Ab_group_add = Cancel_comm_monoid_add+ Group_add
  
 
class Ring = Ab_group_add+ Semiring_0_cancel
  
 
class Ring_1 = Ring+ Semiring_1_cancel
  
 
function (sequential) of_int :: "int \<Rightarrow> ('a :: Ring_1)"
where
  "of_int k = (if eq k 0 then zero
               else (if k < 0 then neg (of_int (uminus k))
                     else let (l, m) = divmoda k 2;
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
 
fun foldla :: "('a \<Rightarrow> 'b \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'b list \<Rightarrow> 'a"
where
  "foldla f a Nil = a"
| "foldla f a (x # xs) = foldla f (f a x) xs"

 
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
 
fun scale :: "Floata \<Rightarrow> int"
where
  "scale (Floata a b) = b"

 
instantiation int :: Plus
begin
   
  fun plus_int :: "int \<Rightarrow> int \<Rightarrow> int"
  where
    "plus_int a b = (a + b)"
  
 
instance sorry

end
 
instantiation int :: Zero
begin
   
  definition zero_int :: "int"
  where
    "zero_int = 0"
  
 
instance sorry

end
 
function (sequential) bitlen :: "int \<Rightarrow> int"
where
  "bitlen x = (if eq x 0 then 0
               else (if eq x (uminus 1) then 1 else 1 + bitlen (div_int x 2)))"
sorry termination sorry
 
fun times_float :: "Floata \<Rightarrow> Floata \<Rightarrow> Floata"
where
  "times_float (Floata a_m a_e) (Floata b_m b_e) = Floata (a_m * b_m) (a_e + b_e)"

 
fun mod_int :: "int \<Rightarrow> int \<Rightarrow> int"
where
  "mod_int a b = snd (divmoda a b)"

 
fun even_int :: "int \<Rightarrow> bool"
where
  "even_int x = eq (mod_int x 2) 0"

 
function (sequential) normfloat :: "Floata \<Rightarrow> Floata"
where
  "normfloat (Floata a b) = (if Not (eq a 0) & even_int a
                             then normfloat (Floata (div_int a 2) (b + 1))
                             else (if eq a 0 then Floata 0 0 else Floata a b))"
sorry termination sorry
 
instantiation int :: Power
begin
  
 
instance sorry

end
 
fun lapprox_posrat :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> Floata"
where
  "lapprox_posrat prec x y = (let l = positive ((id prec + bitlen y) - bitlen x);
                                  d = div_int (x * power 2 l) y
                              in normfloat (Floata d (uminus (id l))))"

 
fun neg_float :: "Floata \<Rightarrow> Floata"
where
  "neg_float (Floata m e) = Floata (uminus m) e"

 
fun rapprox_posrat :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> Floata"
where
  "rapprox_posrat prec x y = (let l = positive ((id prec + bitlen y) - bitlen x);
                                  xa = x * power 2 l;
                                  d = div_int xa y;
                                  m = mod_int xa y
                              in normfloat (Floata (d + (if eq m 0 then 0
                                                         else 1)) (uminus (id l))))"

 
definition zero_float :: "Floata"
where
  "zero_float = Floata 0 0"

 
fun rapprox_rat :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> Floata"
where
  "rapprox_rat prec x y = (if eq y 0 then zero_float
                           else (if 0 <= x
                                 then (if 0 < y then rapprox_posrat prec x y
                                       else neg_float (lapprox_posrat prec x (uminus y)))
                                 else (if 0 < y then neg_float (lapprox_posrat prec (uminus x) y)
                                       else rapprox_posrat prec (uminus x) (uminus y))))"

 
fun float_divr :: "int \<Rightarrow> Floata \<Rightarrow> Floata \<Rightarrow> Floata"
where
  "float_divr prec (Floata m1 s1) (Floata m2 s2) = (let r = rapprox_rat prec m1 m2;
                                                        f = Floata 1 (s1 - s2)
                                                    in times_float f r)"

 
fun ceiling_fl :: "Floata \<Rightarrow> Floata"
where
  "ceiling_fl (Floata m e) = (if 0 <= e then Floata m e
                              else Floata (div_int m (power 2 (positive (uminus e))) + 1) 0)"

 
fun plus_float :: "Floata \<Rightarrow> Floata \<Rightarrow> Floata"
where
  "plus_float (Floata a_m a_e) (Floata b_m b_e) = (if a_e <= b_e
                                                   then Floata (a_m + (b_m * power 2 (positive (b_e - a_e)))) a_e
                                                   else Floata ((a_m * power 2 (positive (a_e - b_e))) + b_m) b_e)"

 
fun minus_float :: "Floata \<Rightarrow> Floata \<Rightarrow> Floata"
where
  "minus_float z w = plus_float z (neg_float w)"

 
fun lb_mod :: "int \<Rightarrow> Floata \<Rightarrow> Floata \<Rightarrow> Floata \<Rightarrow> Floata"
where
  "lb_mod prec x ub lb = minus_float x (times_float (ceiling_fl (float_divr prec x lb)) ub)"

 
fun lapprox_rat :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> Floata"
where
  "lapprox_rat prec x y = (if eq y 0 then zero_float
                           else (if 0 <= x
                                 then (if 0 < y then lapprox_posrat prec x y
                                       else neg_float (rapprox_posrat prec x (uminus y)))
                                 else (if 0 < y then neg_float (rapprox_posrat prec (uminus x) y)
                                       else lapprox_posrat prec (uminus x) (uminus y))))"

 
fun float_divl :: "int \<Rightarrow> Floata \<Rightarrow> Floata \<Rightarrow> Floata"
where
  "float_divl prec (Floata m1 s1) (Floata m2 s2) = (let l = lapprox_rat prec m1 m2;
                                                        f = Floata 1 (s1 - s2)
                                                    in times_float f l)"

 
fun floor_fl :: "Floata \<Rightarrow> Floata"
where
  "floor_fl (Floata m e) = (if 0 <= e then Floata m e
                            else Floata (div_int m (power 2 (positive (uminus e)))) 0)"

 
fun ub_mod :: "int \<Rightarrow> Floata \<Rightarrow> Floata \<Rightarrow> Floata \<Rightarrow> Floata"
where
  "ub_mod prec x ub lb = minus_float x (times_float (floor_fl (float_divl prec x ub)) lb)"

 
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
 
fun eq_float :: "Floata \<Rightarrow> Floata \<Rightarrow> bool"
where
  "eq_float (Floata int1 int2) (Floata int1' int2') = (eq int1 int1' & eq int2 int2')"

 
fun mantissa :: "Floata \<Rightarrow> int"
where
  "mantissa (Floata a b) = a"

 
definition zero_real :: "Reala"
where
  "zero_real = Ratreal (Fract 0 1)"

 
instantiation Reala :: Zero
begin
   
  definition zero_Reala :: "Reala"
  where
    "zero_Reala = zero_real"
  
 
instance sorry

end
 
instantiation Reala :: Zero_neq_one
begin
  
 
instance sorry

end
 
instantiation Reala :: Semigroup_mult
begin
  
 
instance sorry

end
 
fun plus_rat :: "Rat \<Rightarrow> Rat \<Rightarrow> Rat"
where
  "plus_rat (Fract a b) (Fract c d) = (if eq b 0 then Fract c d
                                       else (if eq d 0 then Fract a b
                                             else fract_norm ((a * d) + (c * b)) (b * d)))"

 
fun plus_real :: "Reala \<Rightarrow> Reala \<Rightarrow> Reala"
where
  "plus_real (Ratreal x) (Ratreal y) = Ratreal (plus_rat x y)"

 
instantiation Reala :: Plus
begin
   
  definition plus_Reala :: "Reala \<Rightarrow> Reala \<Rightarrow> Reala"
  where
    "plus_Reala = plus_real"
  
 
instance sorry

end
 
instantiation Reala :: Semigroup_add
begin
  
 
instance sorry

end
 
instantiation Reala :: Ab_semigroup_add
begin
  
 
instance sorry

end
 
instantiation Reala :: Semiring
begin
  
 
instance sorry

end
 
instantiation Reala :: Mult_zero
begin
  
 
instance sorry

end
 
instantiation Reala :: Monoid_add
begin
  
 
instance sorry

end
 
instantiation Reala :: Comm_monoid_add
begin
  
 
instance sorry

end
 
instantiation Reala :: Semiring_0
begin
  
 
instance sorry

end
 
instantiation Reala :: Monoid_mult
begin
  
 
instance sorry

end
 
instantiation Reala :: Semiring_1
begin
  
 
instance sorry

end
 
instantiation Reala :: Cancel_semigroup_add
begin
  
 
instance sorry

end
 
instantiation Reala :: Cancel_ab_semigroup_add
begin
  
 
instance sorry

end
 
instantiation Reala :: Cancel_comm_monoid_add
begin
  
 
instance sorry

end
 
instantiation Reala :: Semiring_0_cancel
begin
  
 
instance sorry

end
 
instantiation Reala :: Semiring_1_cancel
begin
  
 
instance sorry

end
 
fun neg_rat :: "Rat \<Rightarrow> Rat"
where
  "neg_rat (Fract a b) = Fract (uminus a) b"

 
fun neg_real :: "Reala \<Rightarrow> Reala"
where
  "neg_real (Ratreal x) = Ratreal (neg_rat x)"

 
instantiation Reala :: Neg
begin
   
  definition neg_Reala :: "Reala \<Rightarrow> Reala"
  where
    "neg_Reala = neg_real"
  
 
instance sorry

end
 
fun minus_rat :: "Rat \<Rightarrow> Rat \<Rightarrow> Rat"
where
  "minus_rat (Fract a b) (Fract c d) = (if eq b 0
                                        then Fract (uminus c) d
                                        else (if eq d 0 then Fract a b
                                              else fract_norm ((a * d) - (c * b)) (b * d)))"

 
fun minus_real :: "Reala \<Rightarrow> Reala \<Rightarrow> Reala"
where
  "minus_real (Ratreal x) (Ratreal y) = Ratreal (minus_rat x y)"

 
instantiation Reala :: Minus
begin
   
  definition minus_Reala :: "Reala \<Rightarrow> Reala \<Rightarrow> Reala"
  where
    "minus_Reala = minus_real"
  
 
instance sorry

end
 
instantiation Reala :: Group_add
begin
  
 
instance sorry

end
 
instantiation Reala :: Ab_group_add
begin
  
 
instance sorry

end
 
instantiation Reala :: Ring
begin
  
 
instance sorry

end
 
instantiation Reala :: Ring_1
begin
  
 
instance sorry

end
 
fun of_float :: "Floata \<Rightarrow> Reala"
where
  "of_float (Floata a b) = times_real (of_int a) (pow2 b)"

 
function (sequential) round_up :: "int \<Rightarrow> Floata \<Rightarrow> Floata"
where
  "round_up prec (Floata m e) = (let d = bitlen m - id prec
                                 in (if 0 < d
                                     then let p = power 2 (positive d);
                                              n = div_int m p;
                                              r = mod_int m p
                                          in Floata (n + (if eq r 0 then 0 else 1)) (e + d)
                                     else Floata m e))"
sorry termination sorry
 
fun float_abs :: "Floata \<Rightarrow> Floata"
where
  "float_abs (Floata m e) = Floata (abs_int m) e"

 
fun abs_float :: "Floata \<Rightarrow> Floata"
where
  "abs_float x = float_abs x"

 
definition one_float :: "Floata"
where
  "one_float = Floata 1 0"

 
instantiation int :: Semigroup_mult
begin
  
 
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
 
fun float_nprt :: "Floata \<Rightarrow> Floata"
where
  "float_nprt (Floata a e) = (if 0 <= a then zero_float
                              else Floata a e)"

 
fun float_pprt :: "Floata \<Rightarrow> Floata"
where
  "float_pprt (Floata a e) = (if 0 <= a then Floata a e
                              else zero_float)"

 
fun float_size :: "Floata \<Rightarrow> int"
where
  "float_size (Floata int1 int2) = 0"

 
fun less_rat :: "Rat \<Rightarrow> Rat \<Rightarrow> bool"
where
  "less_rat (Fract a b) (Fract c d) = (if eq b 0
                                       then 0 < (sgn_int c * sgn_int d)
                                       else (if eq d 0 then (sgn_int a * sgn_int b) < 0
                                             else ((a * abs_int d) * sgn_int b) < (c * (abs_int b * sgn_int d))))"

 
fun less_real :: "Reala \<Rightarrow> Reala \<Rightarrow> bool"
where
  "less_real (Ratreal x) (Ratreal y) = less_rat x y"

 
fun less_float :: "Floata \<Rightarrow> Floata \<Rightarrow> bool"
where
  "less_float z w = less_real (of_float z) (of_float w)"

 
function (sequential) round_down :: "int \<Rightarrow> Floata \<Rightarrow> Floata"
where
  "round_down prec (Floata m e) = (let d = bitlen m - id prec
                                   in (if 0 < d
                                       then let p = power 2 (positive d);
                                                n = div_int m p
                                            in Floata n (e + d)
                                       else Floata m e))"
sorry termination sorry
 
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
 
instantiation int :: Zero_neq_one
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
 
class No_zero_divisors = Times+ Zero
  
 
instantiation int :: No_zero_divisors
begin
  
 
instance sorry

end
 
class Ab_semigroup_mult = Semigroup_mult
  
 
class Comm_semiring = Ab_semigroup_mult+ Semiring
  
 
class Comm_semiring_0 = Comm_semiring+ Semiring_0
  
 
class Comm_monoid_mult = Ab_semigroup_mult+ Monoid_mult
  
 
class Comm_semiring_1 = Comm_monoid_mult+ Comm_semiring_0+ Dvd+ Semiring_1
  
 
class Comm_semiring_0_cancel = Comm_semiring_0+ Semiring_0_cancel
  
 
class Comm_semiring_1_cancel = Comm_semiring_0_cancel+ Comm_semiring_1+ Semiring_1_cancel
  
 
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
 
fun less_eq_rat :: "Rat \<Rightarrow> Rat \<Rightarrow> bool"
where
  "less_eq_rat (Fract a b) (Fract c d) = (if eq b 0
                                          then 0 <= (sgn_int c * sgn_int d)
                                          else (if eq d 0 then (sgn_int a * sgn_int b) <= 0
                                                else ((a * abs_int d) * sgn_int b) <= ((c * abs_int b) * sgn_int d)))"

 
fun less_eq_real :: "Reala \<Rightarrow> Reala \<Rightarrow> bool"
where
  "less_eq_real (Ratreal x) (Ratreal y) = less_eq_rat x y"

 
fun less_eq_float :: "Floata \<Rightarrow> Floata \<Rightarrow> bool"
where
  "less_eq_float z w = less_eq_real (of_float z) (of_float w)"


end
