{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  MutualRecursion(Num(..), plus_num, times_num, Int(..), times_int, Times(..),
                   one_int, One(..), uminus_int, bitM, dup, minus_int, sub,
                   plus_int, equal_num, equal_int, less_num, less_eq_num,
                   less_int, sgn_int, abs_int, apsnd, Ord(..), Plus(..),
                   Numeral, numeral, Minus(..), Zero(..), Monoid_add,
                   Semiring_1, Div(..), Semiring_numeral_div, divmod_step,
                   divmod, less_eq_int, divmod_abs, divmod_int, div_int,
                   mod_int, Natural(..), integer_of_natural, plus_natural,
                   zero_natural, less_eq_natural, less_natural, Typerepa(..),
                   Itself(..), Typerep(..), Nat(..), Nibble(..), Char(..),
                   Exp(..), Bexp(..), Term(..), Exp_pre_Exp, Bexp_pre_Bexp,
                   Narrowing_type(..), Narrowing_term(..), Narrowing_cons(..),
                   Exp_Bexp_IITN_Exp_Bexp, Exp_Bexp_sbdT_Exp_Bexp, foldr,
                   one_natural, sgn_integer, abs_integer, divmod_integer,
                   div_integer, div_natural, log, times_natural, mod_integer,
                   mod_natural, max, natural_of_integer, minus_natural,
                   minus_shift, next, pick, scomp, equal_natural, iterate,
                   range, listsum, select_weight, valapp, eq_int, evalExp,
                   evalBexp, one_nat, sum, beyond, cons, plus_nat, collapse,
                   int_of_integer, nat_of_integer, nat_of_natural, rec_Exp,
                   rec_Bexp, of_nat_aux, of_nat, size_Exp, size_Bexp,
                   term_of_num, term_of_int, random_int, random_aux_Exp,
                   random_aux_Bexp, non_empty, drawn_from, around_zero,
                   size_Expa, size_Bexpa, equal_Exp, equal_Bexp, one_integer,
                   random_Exp, full_exhaustive_int, random_Bexp, term_of_Exp,
                   term_of_Bexp, typerep_Exp, typerep_Bexp, partial_term_of_int,
                   full_exhaustive_inta, full_exhaustive_Exp,
                   full_exhaustive_Bexp, partial_term_of_Exp,
                   partial_term_of_Bexp, typerep_Exp_pre_Exp,
                   typerep_Bexp_pre_Bexp, typerep_Exp_Bexp_IITN_Exp_Bexp,
                   typerep_Exp_Bexp_sbdT_Exp_Bexp)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;

data Num = One | Bit0 Num | Bit1 Num;

plus_num :: Num -> Num -> Num;
plus_num (Bit1 m) (Bit1 n) = Bit0 (plus_num (plus_num m n) One);
plus_num (Bit1 m) (Bit0 n) = Bit1 (plus_num m n);
plus_num (Bit1 m) One = Bit0 (plus_num m One);
plus_num (Bit0 m) (Bit1 n) = Bit1 (plus_num m n);
plus_num (Bit0 m) (Bit0 n) = Bit0 (plus_num m n);
plus_num (Bit0 m) One = Bit1 m;
plus_num One (Bit1 n) = Bit0 (plus_num n One);
plus_num One (Bit0 n) = Bit1 n;
plus_num One One = Bit0 One;

times_num :: Num -> Num -> Num;
times_num (Bit1 m) (Bit1 n) =
  Bit1 (plus_num (plus_num m n) (Bit0 (times_num m n)));
times_num (Bit1 m) (Bit0 n) = Bit0 (times_num (Bit1 m) n);
times_num (Bit0 m) (Bit1 n) = Bit0 (times_num m (Bit1 n));
times_num (Bit0 m) (Bit0 n) = Bit0 (Bit0 (times_num m n));
times_num One n = n;
times_num m One = m;

data Int = Zero_int | Pos Num | Neg Num;

times_int :: Int -> Int -> Int;
times_int (Neg m) (Neg n) = Pos (times_num m n);
times_int (Neg m) (Pos n) = Neg (times_num m n);
times_int (Pos m) (Neg n) = Neg (times_num m n);
times_int (Pos m) (Pos n) = Pos (times_num m n);
times_int Zero_int l = Zero_int;
times_int k Zero_int = Zero_int;

class Times a where {
  times :: a -> a -> a;
};

class (Times a) => Dvd a where {
};

instance Times Int where {
  times = times_int;
};

instance Dvd Int where {
};

one_int :: Int;
one_int = Pos One;

class One a where {
  one :: a;
};

instance One Int where {
  one = one_int;
};

uminus_int :: Int -> Int;
uminus_int (Neg m) = Pos m;
uminus_int (Pos m) = Neg m;
uminus_int Zero_int = Zero_int;

bitM :: Num -> Num;
bitM One = One;
bitM (Bit0 n) = Bit1 (bitM n);
bitM (Bit1 n) = Bit1 (Bit0 n);

dup :: Int -> Int;
dup (Neg n) = Neg (Bit0 n);
dup (Pos n) = Pos (Bit0 n);
dup Zero_int = Zero_int;

minus_int :: Int -> Int -> Int;
minus_int (Neg m) (Neg n) = sub n m;
minus_int (Neg m) (Pos n) = Neg (plus_num m n);
minus_int (Pos m) (Neg n) = Pos (plus_num m n);
minus_int (Pos m) (Pos n) = sub m n;
minus_int Zero_int l = uminus_int l;
minus_int k Zero_int = k;

sub :: Num -> Num -> Int;
sub (Bit0 m) (Bit1 n) = minus_int (dup (sub m n)) (Pos One);
sub (Bit1 m) (Bit0 n) = plus_int (dup (sub m n)) (Pos One);
sub (Bit1 m) (Bit1 n) = dup (sub m n);
sub (Bit0 m) (Bit0 n) = dup (sub m n);
sub One (Bit1 n) = Neg (Bit0 n);
sub One (Bit0 n) = Neg (bitM n);
sub (Bit1 m) One = Pos (Bit0 m);
sub (Bit0 m) One = Pos (bitM m);
sub One One = Zero_int;

plus_int :: Int -> Int -> Int;
plus_int (Neg m) (Neg n) = Neg (plus_num m n);
plus_int (Neg m) (Pos n) = sub n m;
plus_int (Pos m) (Neg n) = sub m n;
plus_int (Pos m) (Pos n) = Pos (plus_num m n);
plus_int Zero_int l = l;
plus_int k Zero_int = k;

equal_num :: Num -> Num -> Bool;
equal_num (Bit0 x2) (Bit1 x3) = False;
equal_num (Bit1 x3) (Bit0 x2) = False;
equal_num One (Bit1 x3) = False;
equal_num (Bit1 x3) One = False;
equal_num One (Bit0 x2) = False;
equal_num (Bit0 x2) One = False;
equal_num (Bit1 x3) (Bit1 y3) = equal_num x3 y3;
equal_num (Bit0 x2) (Bit0 y2) = equal_num x2 y2;
equal_num One One = True;

equal_int :: Int -> Int -> Bool;
equal_int (Neg k) (Neg l) = equal_num k l;
equal_int (Neg k) (Pos l) = False;
equal_int (Neg k) Zero_int = False;
equal_int (Pos k) (Neg l) = False;
equal_int (Pos k) (Pos l) = equal_num k l;
equal_int (Pos k) Zero_int = False;
equal_int Zero_int (Neg l) = False;
equal_int Zero_int (Pos l) = False;
equal_int Zero_int Zero_int = True;

less_num :: Num -> Num -> Bool;
less_num (Bit1 m) (Bit0 n) = less_num m n;
less_num (Bit1 m) (Bit1 n) = less_num m n;
less_num (Bit0 m) (Bit1 n) = less_eq_num m n;
less_num (Bit0 m) (Bit0 n) = less_num m n;
less_num One (Bit1 n) = True;
less_num One (Bit0 n) = True;
less_num m One = False;

less_eq_num :: Num -> Num -> Bool;
less_eq_num (Bit1 m) (Bit0 n) = less_num m n;
less_eq_num (Bit1 m) (Bit1 n) = less_eq_num m n;
less_eq_num (Bit0 m) (Bit1 n) = less_eq_num m n;
less_eq_num (Bit0 m) (Bit0 n) = less_eq_num m n;
less_eq_num (Bit1 m) One = False;
less_eq_num (Bit0 m) One = False;
less_eq_num One n = True;

less_int :: Int -> Int -> Bool;
less_int (Neg k) (Neg l) = less_num l k;
less_int (Neg k) (Pos l) = True;
less_int (Neg k) Zero_int = True;
less_int (Pos k) (Neg l) = False;
less_int (Pos k) (Pos l) = less_num k l;
less_int (Pos k) Zero_int = False;
less_int Zero_int (Neg l) = False;
less_int Zero_int (Pos l) = True;
less_int Zero_int Zero_int = False;

sgn_int :: Int -> Int;
sgn_int i =
  (if equal_int i Zero_int then Zero_int
    else (if less_int Zero_int i then Pos One else Neg One));

abs_int :: Int -> Int;
abs_int i = (if less_int i Zero_int then uminus_int i else i);

apsnd :: forall a b c. (a -> b) -> (c, a) -> (c, b);
apsnd f (x, y) = (x, f y);

class Ord a where {
  less_eq :: a -> a -> Bool;
  less :: a -> a -> Bool;
};

class Plus a where {
  plus :: a -> a -> a;
};

class (Plus a) => Semigroup_add a where {
};

class (One a, Semigroup_add a) => Numeral a where {
};

numeral :: forall a. (Numeral a) => Num -> a;
numeral (Bit1 n) = let {
                     m = numeral n;
                   } in plus (plus m m) one;
numeral (Bit0 n) = let {
                     m = numeral n;
                   } in plus m m;
numeral One = one;

class Minus a where {
  minus :: a -> a -> a;
};

class (Semigroup_add a) => Cancel_semigroup_add a where {
};

class (Semigroup_add a) => Ab_semigroup_add a where {
};

class (Ab_semigroup_add a, Cancel_semigroup_add a,
        Minus a) => Cancel_ab_semigroup_add a where {
};

class Zero a where {
  zero :: a;
};

class (Semigroup_add a, Zero a) => Monoid_add a where {
};

class (Ab_semigroup_add a, Monoid_add a) => Comm_monoid_add a where {
};

class (Cancel_ab_semigroup_add a,
        Comm_monoid_add a) => Cancel_comm_monoid_add a where {
};

class (Times a, Zero a) => Mult_zero a where {
};

class (Times a) => Semigroup_mult a where {
};

class (Ab_semigroup_add a, Semigroup_mult a) => Semiring a where {
};

class (Comm_monoid_add a, Mult_zero a, Semiring a) => Semiring_0 a where {
};

class (Cancel_comm_monoid_add a, Semiring_0 a) => Semiring_0_cancel a where {
};

class (Semigroup_mult a) => Ab_semigroup_mult a where {
};

class (Ab_semigroup_mult a, Semiring a) => Comm_semiring a where {
};

class (Comm_semiring a, Semiring_0 a) => Comm_semiring_0 a where {
};

class (Comm_semiring_0 a,
        Semiring_0_cancel a) => Comm_semiring_0_cancel a where {
};

class (One a, Times a) => Power a where {
};

class (Semigroup_mult a, Power a) => Monoid_mult a where {
};

class (Monoid_mult a, Numeral a, Semiring a) => Semiring_numeral a where {
};

class (One a, Zero a) => Zero_neq_one a where {
};

class (Semiring_numeral a, Semiring_0 a, Zero_neq_one a) => Semiring_1 a where {
};

class (Semiring_0_cancel a, Semiring_1 a) => Semiring_1_cancel a where {
};

class (Ab_semigroup_mult a, Monoid_mult a, Dvd a) => Comm_monoid_mult a where {
};

class (Comm_monoid_mult a, Comm_semiring_0 a,
        Semiring_1 a) => Comm_semiring_1 a where {
};

class (Comm_semiring_0_cancel a, Comm_semiring_1 a,
        Semiring_1_cancel a) => Comm_semiring_1_cancel a where {
};

class (Comm_semiring_1_cancel a) => Comm_semiring_1_diff_distrib a where {
};

class (Comm_semiring_1_diff_distrib a) => Semiring_parity a where {
};

class (Semiring_0 a) => Semiring_no_zero_divisors a where {
};

class (Comm_semiring_1_diff_distrib a,
        Semiring_no_zero_divisors a) => Semidom a where {
};

class (Dvd a) => Div a where {
  div :: a -> a -> a;
  mod :: a -> a -> a;
};

class (Div a, Semidom a) => Semiring_div a where {
};

class (Semiring_div a, Semiring_parity a) => Semiring_div_parity a where {
};

class (Ord a) => Preorder a where {
};

class (Preorder a) => Order a where {
};

class (Ab_semigroup_add a, Order a) => Ordered_ab_semigroup_add a where {
};

class (Comm_monoid_add a, Ordered_ab_semigroup_add a,
        Semiring a) => Ordered_semiring a where {
};

class (Ordered_semiring a,
        Semiring_0_cancel a) => Ordered_cancel_semiring a where {
};

class (Comm_semiring_0 a, Ordered_semiring a) => Ordered_comm_semiring a where {
};

class (Comm_semiring_0_cancel a, Ordered_cancel_semiring a,
        Ordered_comm_semiring a) => Ordered_cancel_comm_semiring a where {
};

class (Cancel_ab_semigroup_add a,
        Ordered_ab_semigroup_add a) => Ordered_cancel_ab_semigroup_add a where {
};

class (Ordered_cancel_ab_semigroup_add a) => Ordered_ab_semigroup_add_imp_le a where {
};

class (Order a) => Linorder a where {
};

class (Ordered_ab_semigroup_add a,
        Linorder a) => Linordered_ab_semigroup_add a where {
};

class (Linordered_ab_semigroup_add a,
        Ordered_ab_semigroup_add_imp_le a) => Linordered_cancel_ab_semigroup_add a where {
};

class (Comm_monoid_add a,
        Ordered_cancel_ab_semigroup_add a) => Ordered_comm_monoid_add a where {
};

class (Linordered_cancel_ab_semigroup_add a, Ordered_comm_monoid_add a,
        Ordered_cancel_semiring a) => Linordered_semiring a where {
};

class (Linordered_semiring a) => Linordered_semiring_strict a where {
};

class (Linordered_semiring_strict a,
        Ordered_cancel_comm_semiring a) => Linordered_comm_semiring_strict a where {
};

class (Semiring_1 a) => Semiring_char_0 a where {
};

class (Semiring_char_0 a, Linordered_comm_semiring_strict a,
        Semidom a) => Linordered_semidom a where {
};

class (Semiring_div_parity a,
        Linordered_semidom a) => Semiring_numeral_div a where {
};

divmod_step :: forall a. (Semiring_numeral_div a) => Num -> (a, a) -> (a, a);
divmod_step l (q, r) =
  (if less_eq (numeral l) r
    then (plus (times (numeral (Bit0 One)) q) one, minus r (numeral l))
    else (times (numeral (Bit0 One)) q, r));

divmod :: forall a. (Semiring_numeral_div a) => Num -> Num -> (a, a);
divmod (Bit1 m) (Bit0 n) =
  let {
    (q, r) = divmod m n;
  } in (q, plus (times (numeral (Bit0 One)) r) one);
divmod (Bit0 m) (Bit0 n) =
  let {
    (q, r) = divmod m n;
  } in (q, times (numeral (Bit0 One)) r);
divmod m n =
  (if less_num m n then (zero, numeral m)
    else divmod_step n (divmod m (Bit0 n)));

less_eq_int :: Int -> Int -> Bool;
less_eq_int (Neg k) (Neg l) = less_eq_num l k;
less_eq_int (Neg k) (Pos l) = True;
less_eq_int (Neg k) Zero_int = True;
less_eq_int (Pos k) (Neg l) = False;
less_eq_int (Pos k) (Pos l) = less_eq_num k l;
less_eq_int (Pos k) Zero_int = False;
less_eq_int Zero_int (Neg l) = False;
less_eq_int Zero_int (Pos l) = True;
less_eq_int Zero_int Zero_int = True;

instance Plus Int where {
  plus = plus_int;
};

instance Semigroup_add Int where {
};

instance Cancel_semigroup_add Int where {
};

instance Ab_semigroup_add Int where {
};

instance Minus Int where {
  minus = minus_int;
};

instance Cancel_ab_semigroup_add Int where {
};

instance Zero Int where {
  zero = Zero_int;
};

instance Monoid_add Int where {
};

instance Comm_monoid_add Int where {
};

instance Cancel_comm_monoid_add Int where {
};

instance Mult_zero Int where {
};

instance Semigroup_mult Int where {
};

instance Semiring Int where {
};

instance Semiring_0 Int where {
};

instance Semiring_0_cancel Int where {
};

instance Ab_semigroup_mult Int where {
};

instance Comm_semiring Int where {
};

instance Comm_semiring_0 Int where {
};

instance Comm_semiring_0_cancel Int where {
};

instance Power Int where {
};

instance Monoid_mult Int where {
};

instance Numeral Int where {
};

instance Semiring_numeral Int where {
};

instance Zero_neq_one Int where {
};

instance Semiring_1 Int where {
};

instance Semiring_1_cancel Int where {
};

instance Comm_monoid_mult Int where {
};

instance Comm_semiring_1 Int where {
};

instance Comm_semiring_1_cancel Int where {
};

instance Comm_semiring_1_diff_distrib Int where {
};

instance Semiring_parity Int where {
};

instance Semiring_no_zero_divisors Int where {
};

instance Semidom Int where {
};

instance Ord Int where {
  less_eq = less_eq_int;
  less = less_int;
};

instance Preorder Int where {
};

instance Order Int where {
};

instance Ordered_ab_semigroup_add Int where {
};

instance Ordered_semiring Int where {
};

instance Ordered_cancel_semiring Int where {
};

instance Ordered_comm_semiring Int where {
};

instance Ordered_cancel_comm_semiring Int where {
};

instance Ordered_cancel_ab_semigroup_add Int where {
};

instance Ordered_ab_semigroup_add_imp_le Int where {
};

instance Linorder Int where {
};

instance Linordered_ab_semigroup_add Int where {
};

instance Linordered_cancel_ab_semigroup_add Int where {
};

instance Ordered_comm_monoid_add Int where {
};

instance Linordered_semiring Int where {
};

instance Linordered_semiring_strict Int where {
};

instance Linordered_comm_semiring_strict Int where {
};

instance Semiring_char_0 Int where {
};

instance Linordered_semidom Int where {
};

instance Div Int where {
  div = div_int;
  mod = mod_int;
};

instance Semiring_div Int where {
};

instance Semiring_div_parity Int where {
};

instance Semiring_numeral_div Int where {
};

divmod_abs :: Int -> Int -> (Int, Int);
divmod_abs Zero_int j = (Zero_int, Zero_int);
divmod_abs j Zero_int = (Zero_int, abs_int j);
divmod_abs (Pos k) (Neg l) = divmod k l;
divmod_abs (Neg k) (Pos l) = divmod k l;
divmod_abs (Neg k) (Neg l) = divmod k l;
divmod_abs (Pos k) (Pos l) = divmod k l;

divmod_int :: Int -> Int -> (Int, Int);
divmod_int k l =
  (if equal_int k Zero_int then (Zero_int, Zero_int)
    else (if equal_int l Zero_int then (Zero_int, k)
           else apsnd (times_int (sgn_int l))
                  (if equal_int (sgn_int k) (sgn_int l) then divmod_abs k l
                    else let {
                           (r, s) = divmod_abs k l;
                         } in (if equal_int s Zero_int
                                then (uminus_int r, Zero_int)
                                else (minus_int (uminus_int r) (Pos One),
                                       minus_int (abs_int l) s)))));

div_int :: Int -> Int -> Int;
div_int a b = fst (divmod_int a b);

mod_int :: Int -> Int -> Int;
mod_int a b = snd (divmod_int a b);

instance Ord Integer where {
  less_eq = (\ a b -> a <= b);
  less = (\ a b -> a < b);
};

newtype Natural = Nat Integer;

integer_of_natural :: Natural -> Integer;
integer_of_natural (Nat x) = x;

plus_natural :: Natural -> Natural -> Natural;
plus_natural m n = Nat (integer_of_natural m + integer_of_natural n);

instance Plus Natural where {
  plus = plus_natural;
};

zero_natural :: Natural;
zero_natural = Nat (0 :: Integer);

instance Zero Natural where {
  zero = zero_natural;
};

less_eq_natural :: Natural -> Natural -> Bool;
less_eq_natural m n = integer_of_natural m <= integer_of_natural n;

less_natural :: Natural -> Natural -> Bool;
less_natural m n = integer_of_natural m < integer_of_natural n;

instance Ord Natural where {
  less_eq = less_eq_natural;
  less = less_natural;
};

instance Semigroup_add Natural where {
};

instance Monoid_add Natural where {
};

data Typerepa = Typerep String [Typerepa];

data Itself a = Type;

class Typerep a where {
  typerep :: Itself a -> Typerepa;
};

data Nat = Zero_nat | Suc Nat;

data Nibble = Nibble0 | Nibble1 | Nibble2 | Nibble3 | Nibble4 | Nibble5
  | Nibble6 | Nibble7 | Nibble8 | Nibble9 | NibbleA | NibbleB | NibbleC
  | NibbleD | NibbleE | NibbleF;

data Char = Char Nibble Nibble;

data Exp = Plus Exp Exp | Times Exp Exp | Cond Bexp Exp Exp | Val Int;

data Bexp = Equal Exp Exp | Greater Exp Exp;

data Term = Const String Typerepa | App Term Term | Abs String Typerepa Term
  | Free String Typerepa;

data Exp_pre_Exp a b;

data Bexp_pre_Bexp a;

newtype Narrowing_type = Narrowing_sum_of_products [[Narrowing_type]];

data Narrowing_term = Narrowing_variable [Integer] Narrowing_type
  | Narrowing_constructor Integer [Narrowing_term];

data Narrowing_cons a = Narrowing_cons Narrowing_type [[Narrowing_term] -> a];

data Exp_Bexp_IITN_Exp_Bexp;

data Exp_Bexp_sbdT_Exp_Bexp;

foldr :: forall a b. (a -> b -> b) -> [a] -> b -> b;
foldr f [] = id;
foldr f (x : xs) = f x . foldr f xs;

one_natural :: Natural;
one_natural = Nat (1 :: Integer);

sgn_integer :: Integer -> Integer;
sgn_integer k =
  (if k == (0 :: Integer) then (0 :: Integer)
    else (if k < (0 :: Integer) then (-1 :: Integer) else (1 :: Integer)));

abs_integer :: Integer -> Integer;
abs_integer k = (if k < (0 :: Integer) then negate k else k);

divmod_integer :: Integer -> Integer -> (Integer, Integer);
divmod_integer k l =
  (if k == (0 :: Integer) then ((0 :: Integer), (0 :: Integer))
    else (if l == (0 :: Integer) then ((0 :: Integer), k)
           else ((apsnd . (\ a b -> a * b)) . sgn_integer) l
                  (if sgn_integer k == sgn_integer l then divMod (abs k) (abs l)
                    else let {
                           (r, s) = divMod (abs k) (abs l);
                         } in (if s == (0 :: Integer)
                                then (negate r, (0 :: Integer))
                                else (negate r - (1 :: Integer),
                                       abs_integer l - s)))));

div_integer :: Integer -> Integer -> Integer;
div_integer k l = fst (divmod_integer k l);

div_natural :: Natural -> Natural -> Natural;
div_natural m n =
  Nat (div_integer (integer_of_natural m) (integer_of_natural n));

log :: Natural -> Natural -> Natural;
log b i =
  (if less_eq_natural b one_natural || less_natural i b then one_natural
    else plus_natural one_natural (log b (div_natural i b)));

times_natural :: Natural -> Natural -> Natural;
times_natural m n = Nat (integer_of_natural m * integer_of_natural n);

mod_integer :: Integer -> Integer -> Integer;
mod_integer k l = snd (divmod_integer k l);

mod_natural :: Natural -> Natural -> Natural;
mod_natural m n =
  Nat (mod_integer (integer_of_natural m) (integer_of_natural n));

max :: forall a. (Ord a) => a -> a -> a;
max a b = (if less_eq a b then b else a);

natural_of_integer :: Integer -> Natural;
natural_of_integer k = Nat (max (0 :: Integer) k);

minus_natural :: Natural -> Natural -> Natural;
minus_natural m n =
  Nat (max (0 :: Integer) (integer_of_natural m - integer_of_natural n));

minus_shift :: Natural -> Natural -> Natural -> Natural;
minus_shift r k l =
  (if less_natural k l then minus_natural (plus_natural r k) l
    else minus_natural k l);

next :: (Natural, Natural) -> (Natural, (Natural, Natural));
next (v, w) =
  let {
    k = div_natural v (natural_of_integer (53668 :: Integer));
    va = minus_shift (natural_of_integer (2147483563 :: Integer))
           (times_natural
             (mod_natural v (natural_of_integer (53668 :: Integer)))
             (natural_of_integer (40014 :: Integer)))
           (times_natural k (natural_of_integer (12211 :: Integer)));
    l = div_natural w (natural_of_integer (52774 :: Integer));
    wa = minus_shift (natural_of_integer (2147483399 :: Integer))
           (times_natural
             (mod_natural w (natural_of_integer (52774 :: Integer)))
             (natural_of_integer (40692 :: Integer)))
           (times_natural l (natural_of_integer (3791 :: Integer)));
    z = plus_natural
          (minus_shift (natural_of_integer (2147483562 :: Integer)) va
            (plus_natural wa one_natural))
          one_natural;
  } in (z, (va, wa));

pick :: forall a. [(Natural, a)] -> Natural -> a;
pick (x : xs) i =
  (if less_natural i (fst x) then snd x else pick xs (minus_natural i (fst x)));

scomp :: forall a b c d. (a -> (b, c)) -> (b -> c -> d) -> a -> d;
scomp f g = (\ x -> let {
                      (a, b) = f x;
                    } in g a b);

equal_natural :: Natural -> Natural -> Bool;
equal_natural m n = integer_of_natural m == integer_of_natural n;

iterate :: forall a b. Natural -> (a -> b -> (a, b)) -> a -> b -> (a, b);
iterate k f x =
  (if equal_natural k zero_natural then (\ a -> (x, a))
    else scomp (f x) (iterate (minus_natural k one_natural) f));

range :: Natural -> (Natural, Natural) -> (Natural, (Natural, Natural));
range k =
  scomp (iterate (log (natural_of_integer (2147483561 :: Integer)) k)
          (\ l ->
            scomp next
              (\ v ->
                (\ a ->
                  (plus_natural v
                     (times_natural l
                       (natural_of_integer (2147483561 :: Integer))),
                    a))))
          one_natural)
    (\ v -> (\ a -> (mod_natural v k, a)));

listsum :: forall a. (Monoid_add a) => [a] -> a;
listsum xs = foldr plus xs zero;

select_weight ::
  forall a. [(Natural, a)] -> (Natural, Natural) -> (a, (Natural, Natural));
select_weight xs =
  scomp (range (listsum (map fst xs))) (\ k -> (\ a -> (pick xs k, a)));

valapp ::
  forall a b. (a -> b, () -> Term) -> (a, () -> Term) -> (b, () -> Term);
valapp (f, tf) (x, tx) = (f x, (\ _ -> App (tf ()) (tx ())));

eq_int :: Int -> Int -> Bool;
eq_int x y = equal_int x y;

evalExp :: Exp -> Int;
evalExp (Plus e1 e2) = plus_int (evalExp e1) (evalExp e2);
evalExp (Times e1 e2) = times_int (evalExp e1) (evalExp e2);
evalExp (Cond b e1 e2) = (if evalBexp b then evalExp e1 else evalExp e2);
evalExp (Val i) = i;

evalBexp :: Bexp -> Bool;
evalBexp (Equal e1 e2) = eq_int (evalExp e1) (evalExp e2);
evalBexp (Greater e1 e2) = less_int (evalExp e2) (evalExp e1);

one_nat :: Nat;
one_nat = Suc Zero_nat;

sum ::
  forall a.
    (Integer -> Narrowing_cons a) ->
      (Integer -> Narrowing_cons a) -> Integer -> Narrowing_cons a;
sum a b d =
  let {
    (Narrowing_cons (Narrowing_sum_of_products ssa) ca) = a d;
    (Narrowing_cons (Narrowing_sum_of_products ssb) cb) = b d;
  } in Narrowing_cons (Narrowing_sum_of_products (ssa ++ ssb)) (ca ++ cb);

beyond :: Natural -> Natural -> Natural;
beyond k l = (if less_natural k l then l else zero_natural);

cons :: forall a. a -> Integer -> Narrowing_cons a;
cons a d = Narrowing_cons (Narrowing_sum_of_products [[]]) [(\ _ -> a)];

plus_nat :: Nat -> Nat -> Nat;
plus_nat (Suc m) n = plus_nat m (Suc n);
plus_nat Zero_nat n = n;

collapse :: forall a b. (a -> (a -> (b, a), a)) -> a -> (b, a);
collapse f = scomp f id;

int_of_integer :: Integer -> Int;
int_of_integer k =
  (if k < (0 :: Integer) then uminus_int (int_of_integer (negate k))
    else (if k == (0 :: Integer) then Zero_int
           else let {
                  (l, j) = divmod_integer k (2 :: Integer);
                  la = times_int (Pos (Bit0 One)) (int_of_integer l);
                } in (if j == (0 :: Integer) then la
                       else plus_int la (Pos One))));

nat_of_integer :: Integer -> Nat;
nat_of_integer k =
  (if k <= (0 :: Integer) then Zero_nat
    else let {
           (l, j) = divmod_integer k (2 :: Integer);
           la = nat_of_integer l;
           lb = plus_nat la la;
         } in (if j == (0 :: Integer) then lb else plus_nat lb one_nat));

nat_of_natural :: Natural -> Nat;
nat_of_natural = nat_of_integer . integer_of_natural;

rec_Exp ::
  forall a b.
    (Exp -> Exp -> a -> a -> a) ->
      (Exp -> Exp -> a -> a -> a) ->
        (Bexp -> Exp -> Exp -> b -> a -> a -> a) ->
          (Int -> a) ->
            (Exp -> Exp -> a -> a -> b) ->
              (Exp -> Exp -> a -> a -> b) -> Exp -> a;
rec_Exp f11 f12 f13 f14 f21 f22 (Plus x111 x112) =
  f11 x111 x112 (rec_Exp f11 f12 f13 f14 f21 f22 x111)
    (rec_Exp f11 f12 f13 f14 f21 f22 x112);
rec_Exp f11 f12 f13 f14 f21 f22 (Times x121 x122) =
  f12 x121 x122 (rec_Exp f11 f12 f13 f14 f21 f22 x121)
    (rec_Exp f11 f12 f13 f14 f21 f22 x122);
rec_Exp f11 f12 f13 f14 f21 f22 (Cond x131 x132 x133) =
  f13 x131 x132 x133 (rec_Bexp f11 f12 f13 f14 f21 f22 x131)
    (rec_Exp f11 f12 f13 f14 f21 f22 x132)
    (rec_Exp f11 f12 f13 f14 f21 f22 x133);
rec_Exp f11 f12 f13 f14 f21 f22 (Val x14) = f14 x14;

rec_Bexp ::
  forall a b.
    (Exp -> Exp -> a -> a -> a) ->
      (Exp -> Exp -> a -> a -> a) ->
        (Bexp -> Exp -> Exp -> b -> a -> a -> a) ->
          (Int -> a) ->
            (Exp -> Exp -> a -> a -> b) ->
              (Exp -> Exp -> a -> a -> b) -> Bexp -> b;
rec_Bexp f11 f12 f13 f14 f21 f22 (Equal x211 x212) =
  f21 x211 x212 (rec_Exp f11 f12 f13 f14 f21 f22 x211)
    (rec_Exp f11 f12 f13 f14 f21 f22 x212);
rec_Bexp f11 f12 f13 f14 f21 f22 (Greater x221 x222) =
  f22 x221 x222 (rec_Exp f11 f12 f13 f14 f21 f22 x221)
    (rec_Exp f11 f12 f13 f14 f21 f22 x222);

of_nat_aux :: forall a. (Semiring_1 a) => (a -> a) -> Nat -> a -> a;
of_nat_aux inc Zero_nat i = i;
of_nat_aux inc (Suc n) i = of_nat_aux inc n (inc i);

of_nat :: forall a. (Semiring_1 a) => Nat -> a;
of_nat n = of_nat_aux (\ i -> plus i one) n zero;

size_Exp :: Exp -> Nat;
size_Exp (Plus x111 x112) =
  plus_nat (plus_nat (size_Exp x111) (size_Exp x112)) (Suc Zero_nat);
size_Exp (Times x121 x122) =
  plus_nat (plus_nat (size_Exp x121) (size_Exp x122)) (Suc Zero_nat);
size_Exp (Cond x131 x132 x133) =
  plus_nat
    (plus_nat (plus_nat (size_Bexp x131) (size_Exp x132)) (size_Exp x133))
    (Suc Zero_nat);
size_Exp (Val x14) = Zero_nat;

size_Bexp :: Bexp -> Nat;
size_Bexp (Equal x211 x212) =
  plus_nat (plus_nat (size_Exp x211) (size_Exp x212)) (Suc Zero_nat);
size_Bexp (Greater x221 x222) =
  plus_nat (plus_nat (size_Exp x221) (size_Exp x222)) (Suc Zero_nat);

term_of_num :: Num -> Term;
term_of_num (Bit1 a) =
  App (Const "Num.num.Bit1"
        (Typerep "fun" [Typerep "Num.num" [], Typerep "Num.num" []]))
    (term_of_num a);
term_of_num (Bit0 a) =
  App (Const "Num.num.Bit0"
        (Typerep "fun" [Typerep "Num.num" [], Typerep "Num.num" []]))
    (term_of_num a);
term_of_num One = Const "Num.num.One" (Typerep "Num.num" []);

term_of_int :: Int -> Term;
term_of_int (Neg a) =
  App (Const "Int.Neg"
        (Typerep "fun" [Typerep "Num.num" [], Typerep "Int.int" []]))
    (term_of_num a);
term_of_int (Pos a) =
  App (Const "Int.Pos"
        (Typerep "fun" [Typerep "Num.num" [], Typerep "Int.int" []]))
    (term_of_num a);
term_of_int Zero_int =
  Const "Int.zero_int_inst.zero_int" (Typerep "Int.int" []);

random_int ::
  Natural -> (Natural, Natural) -> ((Int, () -> Term), (Natural, Natural));
random_int i =
  scomp (range
          (plus_natural (times_natural (natural_of_integer (2 :: Integer)) i)
            one_natural))
    (\ k ->
      (\ a ->
        (let {
           j = (if less_eq_natural i k
                 then of_nat (nat_of_natural (minus_natural k i))
                 else uminus_int (of_nat (nat_of_natural (minus_natural i k))));
         } in (j, (\ _ -> term_of_int j)),
          a)));

random_aux_Exp ::
  Natural ->
    Natural -> (Natural, Natural) -> ((Exp, () -> Term), (Natural, Natural));
random_aux_Exp i j s =
  collapse
    (select_weight
      [(i, scomp (random_aux_Exp (minus_natural i one_natural) j)
             (\ x ->
               scomp (random_aux_Exp (minus_natural i one_natural) j)
                 (\ y ->
                   (\ a ->
                     (valapp
                        (valapp
                          (Plus,
                            (\ _ ->
                              Const "MutualRecursion.Exp.Plus"
                                (Typerep "fun"
                                  [Typerep "MutualRecursion.Exp" [],
                                    Typerep "fun"
                                      [Typerep "MutualRecursion.Exp" [],
Typerep "MutualRecursion.Exp" []]])))
                          x)
                        y,
                       a))))),
        (i, scomp (random_aux_Exp (minus_natural i one_natural) j)
              (\ x ->
                scomp (random_aux_Exp (minus_natural i one_natural) j)
                  (\ y ->
                    (\ a ->
                      (valapp
                         (valapp
                           (Times,
                             (\ _ ->
                               Const "MutualRecursion.Exp.Times"
                                 (Typerep "fun"
                                   [Typerep "MutualRecursion.Exp" [],
                                     Typerep "fun"
                                       [Typerep "MutualRecursion.Exp" [],
 Typerep "MutualRecursion.Exp" []]])))
                           x)
                         y,
                        a))))),
        (beyond one_natural i,
          scomp (random_aux_Bexp (minus_natural i one_natural) j)
            (\ x ->
              scomp (random_aux_Exp (minus_natural i one_natural) j)
                (\ y ->
                  scomp (random_aux_Exp (minus_natural i one_natural) j)
                    (\ z ->
                      (\ a ->
                        (valapp
                           (valapp
                             (valapp
                               (Cond,
                                 (\ _ ->
                                   Const "MutualRecursion.Exp.Cond"
                                     (Typerep "fun"
                                       [Typerep "MutualRecursion.Bexp" [],
 Typerep "fun"
   [Typerep "MutualRecursion.Exp" [],
     Typerep "fun"
       [Typerep "MutualRecursion.Exp" [], Typerep "MutualRecursion.Exp" []]]])))
                               x)
                             y)
                           z,
                          a)))))),
        (one_natural,
          scomp (random_int j)
            (\ x ->
              (\ a ->
                (valapp
                   (Val, (\ _ ->
                           Const "MutualRecursion.Exp.Val"
                             (Typerep "fun"
                               [Typerep "Int.int" [],
                                 Typerep "MutualRecursion.Exp" []])))
                   x,
                  a))))])
    s;

random_aux_Bexp ::
  Natural ->
    Natural -> (Natural, Natural) -> ((Bexp, () -> Term), (Natural, Natural));
random_aux_Bexp i j s =
  collapse
    (select_weight
      [(i, scomp (random_aux_Exp (minus_natural i one_natural) j)
             (\ x ->
               scomp (random_aux_Exp (minus_natural i one_natural) j)
                 (\ y ->
                   (\ a ->
                     (valapp
                        (valapp
                          (Equal,
                            (\ _ ->
                              Const "MutualRecursion.Bexp.Equal"
                                (Typerep "fun"
                                  [Typerep "MutualRecursion.Exp" [],
                                    Typerep "fun"
                                      [Typerep "MutualRecursion.Exp" [],
Typerep "MutualRecursion.Bexp" []]])))
                          x)
                        y,
                       a))))),
        (i, scomp (random_aux_Exp (minus_natural i one_natural) j)
              (\ x ->
                scomp (random_aux_Exp (minus_natural i one_natural) j)
                  (\ y ->
                    (\ a ->
                      (valapp
                         (valapp
                           (Greater,
                             (\ _ ->
                               Const "MutualRecursion.Bexp.Greater"
                                 (Typerep "fun"
                                   [Typerep "MutualRecursion.Exp" [],
                                     Typerep "fun"
                                       [Typerep "MutualRecursion.Exp" [],
 Typerep "MutualRecursion.Bexp" []]])))
                           x)
                         y,
                        a)))))])
    s;

non_empty :: Narrowing_type -> Bool;
non_empty (Narrowing_sum_of_products ps) = not (null ps);

drawn_from :: forall a. [a] -> Narrowing_cons a;
drawn_from xs =
  Narrowing_cons (Narrowing_sum_of_products (map (\ _ -> []) xs))
    (map (\ x _ -> x) xs);

around_zero :: Int -> [Int];
around_zero i =
  (if less_int i Zero_int then []
    else (if equal_int i Zero_int then [Zero_int]
           else around_zero (minus_int i (Pos One)) ++ [i, uminus_int i]));

size_Expa :: Exp -> Nat;
size_Expa (Plus x111 x112) =
  plus_nat (plus_nat (size_Expa x111) (size_Expa x112)) (Suc Zero_nat);
size_Expa (Times x121 x122) =
  plus_nat (plus_nat (size_Expa x121) (size_Expa x122)) (Suc Zero_nat);
size_Expa (Cond x131 x132 x133) =
  plus_nat
    (plus_nat (plus_nat (size_Bexpa x131) (size_Expa x132)) (size_Expa x133))
    (Suc Zero_nat);
size_Expa (Val x14) = Zero_nat;

size_Bexpa :: Bexp -> Nat;
size_Bexpa (Equal x211 x212) =
  plus_nat (plus_nat (size_Expa x211) (size_Expa x212)) (Suc Zero_nat);
size_Bexpa (Greater x221 x222) =
  plus_nat (plus_nat (size_Expa x221) (size_Expa x222)) (Suc Zero_nat);

equal_Exp :: Exp -> Exp -> Bool;
equal_Exp (Cond x31 x32 x33) (Val x4) = False;
equal_Exp (Val x4) (Cond x31 x32 x33) = False;
equal_Exp (Times x21 x22) (Val x4) = False;
equal_Exp (Val x4) (Times x21 x22) = False;
equal_Exp (Times x21 x22) (Cond x31 x32 x33) = False;
equal_Exp (Cond x31 x32 x33) (Times x21 x22) = False;
equal_Exp (Plus x11 x12) (Val x4) = False;
equal_Exp (Val x4) (Plus x11 x12) = False;
equal_Exp (Plus x11 x12) (Cond x31 x32 x33) = False;
equal_Exp (Cond x31 x32 x33) (Plus x11 x12) = False;
equal_Exp (Plus x11 x12) (Times x21 x22) = False;
equal_Exp (Times x21 x22) (Plus x11 x12) = False;
equal_Exp (Val x4) (Val y4) = equal_int x4 y4;
equal_Exp (Cond x31 x32 x33) (Cond y31 y32 y33) =
  equal_Bexp x31 y31 && equal_Exp x32 y32 && equal_Exp x33 y33;
equal_Exp (Times x21 x22) (Times y21 y22) =
  equal_Exp x21 y21 && equal_Exp x22 y22;
equal_Exp (Plus x11 x12) (Plus y11 y12) =
  equal_Exp x11 y11 && equal_Exp x12 y12;

equal_Bexp :: Bexp -> Bexp -> Bool;
equal_Bexp (Equal x11 x12) (Greater x21 x22) = False;
equal_Bexp (Greater x21 x22) (Equal x11 x12) = False;
equal_Bexp (Greater x21 x22) (Greater y21 y22) =
  equal_Exp x21 y21 && equal_Exp x22 y22;
equal_Bexp (Equal x11 x12) (Equal y11 y12) =
  equal_Exp x11 y11 && equal_Exp x12 y12;

one_integer :: Integer;
one_integer = (1 :: Integer);

random_Exp ::
  Natural -> (Natural, Natural) -> ((Exp, () -> Term), (Natural, Natural));
random_Exp i = random_aux_Exp i i;

full_exhaustive_int ::
  ((Int, () -> Term) -> Maybe (Bool, [Term])) ->
    Int -> Int -> Maybe (Bool, [Term]);
full_exhaustive_int f d i =
  (if less_int d i then Nothing
    else (case f (i, (\ _ -> term_of_int i)) of {
           Nothing -> full_exhaustive_int f d (plus_int i (Pos One));
           Just a -> Just a;
         }));

random_Bexp ::
  Natural -> (Natural, Natural) -> ((Bexp, () -> Term), (Natural, Natural));
random_Bexp i = random_aux_Bexp (max one_natural i) i;

term_of_Exp :: Exp -> Term;
term_of_Exp (Val a) =
  App (Const "MutualRecursion.Exp.Val"
        (Typerep "fun"
          [Typerep "Int.int" [], Typerep "MutualRecursion.Exp" []]))
    (term_of_int a);
term_of_Exp (Cond a b c) =
  App (App (App (Const "MutualRecursion.Exp.Cond"
                  (Typerep "fun"
                    [Typerep "MutualRecursion.Bexp" [],
                      Typerep "fun"
                        [Typerep "MutualRecursion.Exp" [],
                          Typerep "fun"
                            [Typerep "MutualRecursion.Exp" [],
                              Typerep "MutualRecursion.Exp" []]]]))
             (term_of_Bexp a))
        (term_of_Exp b))
    (term_of_Exp c);
term_of_Exp (Times a b) =
  App (App (Const "MutualRecursion.Exp.Times"
             (Typerep "fun"
               [Typerep "MutualRecursion.Exp" [],
                 Typerep "fun"
                   [Typerep "MutualRecursion.Exp" [],
                     Typerep "MutualRecursion.Exp" []]]))
        (term_of_Exp a))
    (term_of_Exp b);
term_of_Exp (Plus a b) =
  App (App (Const "MutualRecursion.Exp.Plus"
             (Typerep "fun"
               [Typerep "MutualRecursion.Exp" [],
                 Typerep "fun"
                   [Typerep "MutualRecursion.Exp" [],
                     Typerep "MutualRecursion.Exp" []]]))
        (term_of_Exp a))
    (term_of_Exp b);

term_of_Bexp :: Bexp -> Term;
term_of_Bexp (Greater a b) =
  App (App (Const "MutualRecursion.Bexp.Greater"
             (Typerep "fun"
               [Typerep "MutualRecursion.Exp" [],
                 Typerep "fun"
                   [Typerep "MutualRecursion.Exp" [],
                     Typerep "MutualRecursion.Bexp" []]]))
        (term_of_Exp a))
    (term_of_Exp b);
term_of_Bexp (Equal a b) =
  App (App (Const "MutualRecursion.Bexp.Equal"
             (Typerep "fun"
               [Typerep "MutualRecursion.Exp" [],
                 Typerep "fun"
                   [Typerep "MutualRecursion.Exp" [],
                     Typerep "MutualRecursion.Bexp" []]]))
        (term_of_Exp a))
    (term_of_Exp b);

typerep_Exp :: Itself Exp -> Typerepa;
typerep_Exp t = Typerep "MutualRecursion.Exp" [];

typerep_Bexp :: Itself Bexp -> Typerepa;
typerep_Bexp t = Typerep "MutualRecursion.Bexp" [];

partial_term_of_int :: Itself Int -> Narrowing_term -> Term;
partial_term_of_int ty (Narrowing_constructor i []) =
  (if mod_integer i (2 :: Integer) == (0 :: Integer)
    then term_of_int (div_int (uminus_int (int_of_integer i)) (Pos (Bit0 One)))
    else term_of_int
           (div_int (plus_int (int_of_integer i) (Pos One)) (Pos (Bit0 One))));
partial_term_of_int ty (Narrowing_variable p t) =
  Free "_" (Typerep "Int.int" []);

full_exhaustive_inta ::
  ((Int, () -> Term) -> Maybe (Bool, [Term])) ->
    Natural -> Maybe (Bool, [Term]);
full_exhaustive_inta f d =
  full_exhaustive_int f (int_of_integer (integer_of_natural d))
    (uminus_int (int_of_integer (integer_of_natural d)));

full_exhaustive_Exp ::
  ((Exp, () -> Term) -> Maybe (Bool, [Term])) ->
    Natural -> Maybe (Bool, [Term]);
full_exhaustive_Exp f i =
  (if less_natural zero_natural i
    then (case full_exhaustive_Exp
                 (\ (uu, uua) ->
                   full_exhaustive_Exp
                     (\ (uub, uuc) ->
                       f (Plus uu uub,
                           (\ _ ->
                             App (App (Const "MutualRecursion.Exp.Plus"
(Typerep "fun"
  [Typerep "MutualRecursion.Exp" [],
    Typerep "fun"
      [Typerep "MutualRecursion.Exp" [], Typerep "MutualRecursion.Exp" []]]))
                                   (uua ()))
                               (uuc ()))))
                     (minus_natural i one_natural))
                 (minus_natural i one_natural)
           of {
           Nothing ->
             (case full_exhaustive_Exp
                     (\ (uu, uua) ->
                       full_exhaustive_Exp
                         (\ (uub, uuc) ->
                           f (Times uu uub,
                               (\ _ ->
                                 App (App (Const "MutualRecursion.Exp.Times"
    (Typerep "fun"
      [Typerep "MutualRecursion.Exp" [],
        Typerep "fun"
          [Typerep "MutualRecursion.Exp" [],
            Typerep "MutualRecursion.Exp" []]]))
                                       (uua ()))
                                   (uuc ()))))
                         (minus_natural i one_natural))
                     (minus_natural i one_natural)
               of {
               Nothing ->
                 (case full_exhaustive_Bexp
                         (\ (uu, uua) ->
                           full_exhaustive_Exp
                             (\ (uub, uuc) ->
                               full_exhaustive_Exp
                                 (\ (uud, uue) ->
                                   f (Cond uu uub uud,
                                       (\ _ ->
 App (App (App (Const "MutualRecursion.Exp.Cond"
                 (Typerep "fun"
                   [Typerep "MutualRecursion.Bexp" [],
                     Typerep "fun"
                       [Typerep "MutualRecursion.Exp" [],
                         Typerep "fun"
                           [Typerep "MutualRecursion.Exp" [],
                             Typerep "MutualRecursion.Exp" []]]]))
            (uua ()))
       (uuc ()))
   (uue ()))))
                                 (minus_natural i one_natural))
                             (minus_natural i one_natural))
                         (minus_natural i one_natural)
                   of {
                   Nothing ->
                     full_exhaustive_inta
                       (\ (uu, uua) ->
                         f (Val uu,
                             (\ _ ->
                               App (Const "MutualRecursion.Exp.Val"
                                     (Typerep "fun"
                                       [Typerep "Int.int" [],
 Typerep "MutualRecursion.Exp" []]))
                                 (uua ()))))
                       (minus_natural i one_natural);
                   Just a -> Just a;
                 });
               Just a -> Just a;
             });
           Just a -> Just a;
         })
    else Nothing);

full_exhaustive_Bexp ::
  ((Bexp, () -> Term) -> Maybe (Bool, [Term])) ->
    Natural -> Maybe (Bool, [Term]);
full_exhaustive_Bexp f i =
  (if less_natural zero_natural i
    then (case full_exhaustive_Exp
                 (\ (uu, uua) ->
                   full_exhaustive_Exp
                     (\ (uub, uuc) ->
                       f (Equal uu uub,
                           (\ _ ->
                             App (App (Const "MutualRecursion.Bexp.Equal"
(Typerep "fun"
  [Typerep "MutualRecursion.Exp" [],
    Typerep "fun"
      [Typerep "MutualRecursion.Exp" [], Typerep "MutualRecursion.Bexp" []]]))
                                   (uua ()))
                               (uuc ()))))
                     (minus_natural i one_natural))
                 (minus_natural i one_natural)
           of {
           Nothing ->
             full_exhaustive_Exp
               (\ (uu, uua) ->
                 full_exhaustive_Exp
                   (\ (uub, uuc) ->
                     f (Greater uu uub,
                         (\ _ ->
                           App (App (Const "MutualRecursion.Bexp.Greater"
                                      (Typerep "fun"
[Typerep "MutualRecursion.Exp" [],
  Typerep "fun"
    [Typerep "MutualRecursion.Exp" [], Typerep "MutualRecursion.Bexp" []]]))
                                 (uua ()))
                             (uuc ()))))
                   (minus_natural i one_natural))
               (minus_natural i one_natural);
           Just a -> Just a;
         })
    else Nothing);

partial_term_of_Exp :: Itself Exp -> Narrowing_term -> Term;
partial_term_of_Exp ty (Narrowing_constructor (3 :: Integer) [a]) =
  App (Const "MutualRecursion.Exp.Val"
        (Typerep "fun"
          [Typerep "Int.int" [], Typerep "MutualRecursion.Exp" []]))
    (partial_term_of_int Type a);
partial_term_of_Exp ty (Narrowing_constructor (2 :: Integer) [c, b, a]) =
  App (App (App (Const "MutualRecursion.Exp.Cond"
                  (Typerep "fun"
                    [Typerep "MutualRecursion.Bexp" [],
                      Typerep "fun"
                        [Typerep "MutualRecursion.Exp" [],
                          Typerep "fun"
                            [Typerep "MutualRecursion.Exp" [],
                              Typerep "MutualRecursion.Exp" []]]]))
             (partial_term_of_Bexp Type a))
        (partial_term_of_Exp Type b))
    (partial_term_of_Exp Type c);
partial_term_of_Exp ty (Narrowing_constructor (1 :: Integer) [b, a]) =
  App (App (Const "MutualRecursion.Exp.Times"
             (Typerep "fun"
               [Typerep "MutualRecursion.Exp" [],
                 Typerep "fun"
                   [Typerep "MutualRecursion.Exp" [],
                     Typerep "MutualRecursion.Exp" []]]))
        (partial_term_of_Exp Type a))
    (partial_term_of_Exp Type b);
partial_term_of_Exp ty (Narrowing_constructor (0 :: Integer) [b, a]) =
  App (App (Const "MutualRecursion.Exp.Plus"
             (Typerep "fun"
               [Typerep "MutualRecursion.Exp" [],
                 Typerep "fun"
                   [Typerep "MutualRecursion.Exp" [],
                     Typerep "MutualRecursion.Exp" []]]))
        (partial_term_of_Exp Type a))
    (partial_term_of_Exp Type b);
partial_term_of_Exp ty (Narrowing_variable p tt) =
  Free "_" (Typerep "MutualRecursion.Exp" []);

partial_term_of_Bexp :: Itself Bexp -> Narrowing_term -> Term;
partial_term_of_Bexp ty (Narrowing_constructor (1 :: Integer) [b, a]) =
  App (App (Const "MutualRecursion.Bexp.Greater"
             (Typerep "fun"
               [Typerep "MutualRecursion.Exp" [],
                 Typerep "fun"
                   [Typerep "MutualRecursion.Exp" [],
                     Typerep "MutualRecursion.Bexp" []]]))
        (partial_term_of_Exp Type a))
    (partial_term_of_Exp Type b);
partial_term_of_Bexp ty (Narrowing_constructor (0 :: Integer) [b, a]) =
  App (App (Const "MutualRecursion.Bexp.Equal"
             (Typerep "fun"
               [Typerep "MutualRecursion.Exp" [],
                 Typerep "fun"
                   [Typerep "MutualRecursion.Exp" [],
                     Typerep "MutualRecursion.Bexp" []]]))
        (partial_term_of_Exp Type a))
    (partial_term_of_Exp Type b);
partial_term_of_Bexp ty (Narrowing_variable p tt) =
  Free "_" (Typerep "MutualRecursion.Bexp" []);

typerep_Exp_pre_Exp ::
  forall a b. (Typerep a, Typerep b) => Itself (Exp_pre_Exp a b) -> Typerepa;
typerep_Exp_pre_Exp t =
  Typerep "MutualRecursion.Exp.Exp_pre_Exp"
    [(typerep :: Itself a -> Typerepa) Type,
      (typerep :: Itself b -> Typerepa) Type];

typerep_Bexp_pre_Bexp ::
  forall a. (Typerep a) => Itself (Bexp_pre_Bexp a) -> Typerepa;
typerep_Bexp_pre_Bexp t =
  Typerep "MutualRecursion.Bexp.Bexp_pre_Bexp"
    [(typerep :: Itself a -> Typerepa) Type];

typerep_Exp_Bexp_IITN_Exp_Bexp :: Itself Exp_Bexp_IITN_Exp_Bexp -> Typerepa;
typerep_Exp_Bexp_IITN_Exp_Bexp t =
  Typerep "MutualRecursion.Exp_Bexp.Exp_Bexp_IITN_Exp_Bexp" [];

typerep_Exp_Bexp_sbdT_Exp_Bexp :: Itself Exp_Bexp_sbdT_Exp_Bexp -> Typerepa;
typerep_Exp_Bexp_sbdT_Exp_Bexp t =
  Typerep "MutualRecursion.Exp_Bexp.Exp_Bexp_sbdT_Exp_Bexp" [];

}
