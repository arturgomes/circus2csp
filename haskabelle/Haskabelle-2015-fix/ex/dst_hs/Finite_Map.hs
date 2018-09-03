{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Finite_Map(Num(..), plus_num, times_num, Int(..), times_int, Times(..),
              one_int, One(..), uminus_int, bitM, dup, minus_int, sub, plus_int,
              equal_num, equal_int, less_num, less_eq_num, less_int, sgn_int,
              abs_int, apsnd, Orda(..), Plus(..), Numeral, numeral, Minus(..),
              Zero(..), Monoid_add, Semiring_1, Div(..), Semiring_numeral_div,
              divmod_step, divmod, less_eq_int, divmod_abs, divmod_int, div_int,
              mod_int, Natural(..), integer_of_natural, plus_natural,
              zero_natural, Eqa(..), Ord, Typerepa(..), Term(..), Itself(..),
              Typerep(..), Term_of(..), Random(..), Narrowing_type(..),
              Narrowing_term(..), Partial_term_of(..), Full_exhaustive(..),
              Narrowing_cons(..), Narrowing(..), Nat(..), Set(..), Nibble(..),
              Char(..), FiniteMap(..), FiniteMap_pre_FiniteMap,
              FiniteMap_IITN_FiniteMap, ball, fold, foldl, foldr,
              less_eq_natural, less_natural, one_natural, sgn_integer,
              abs_integer, divmod_integer, div_integer, div_natural, log,
              removeAll, membera, inserta, insert, member, times_natural,
              mod_integer, mod_natural, max, natural_of_integer, minus_natural,
              minus_shift, next, pick, scomp, equal_natural, iterate, range,
              findMin, findMax, unbox2, sizeFM, mkBranch, single_R10,
              sIZE_RATIO, single_L8, double_R6, double_L4, mkBalBranch, emptyFM,
              unitFM, addToFM_C, add0, mapFM, lookupFM, elemFM, foldFM, eltsFM,
              isJust, keysFM, addToFM, mkVBalBranch, splitLT, splitGT, plusFM,
              deleteMin, deleteMax, glueBal, glueVBal, minusFM, filterFM,
              fmToList, addListToFM_C, addListToFM, listToFM, plusFM_C,
              delFromFM, eq_int, isEmptyFM, listsum, select_weight, mapMaybeFM,
              valapp, intersectFM_C, intersectFM, delListFromFM, one_nat, sum,
              bot_set, sup_set, set2_FiniteMap, set1_FiniteMap, pred_FiniteMap,
              cons, plus_nat, collapse, int_of_integer, nat_of_integer,
              nat_of_natural, of_nat_aux, of_nat, lookupWithDefaultFM,
              non_empty, term_of_num, term_of_int, random_int,
              random_aux_FiniteMap, drawn_from, around_zero, map_FiniteMap,
              rec_FiniteMap, rel_FiniteMap, size_FiniteMap, one_integer,
              full_exhaustive_int, size_FiniteMapa, equal_FiniteMap,
              partial_term_of_int, random_FiniteMap, term_of_FiniteMap,
              typerep_FiniteMap, full_exhaustive_inta,
              full_exhaustive_FiniteMap, partial_term_of_FiniteMap,
              typerep_FiniteMap_pre_FiniteMap, typerep_FiniteMap_IITN_FiniteMap)
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

class Orda a where {
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

class (Orda a) => Preorder a where {
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

instance Orda Int where {
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

instance Orda Integer where {
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

instance Semigroup_add Natural where {
};

instance Monoid_add Natural where {
};

class Eqa a where {
  eq :: a -> a -> Bool;
  not_eq :: a -> a -> Bool;
};

class (Linorder a, Eqa a) => Ord a where {
};

data Typerepa = Typerep String [Typerepa];

data Term = Const String Typerepa | App Term Term | Abs String Typerepa Term
  | Free String Typerepa;

data Itself a = Type;

class Typerep a where {
  typerep :: Itself a -> Typerepa;
};

class (Typerep a) => Term_of a where {
  term_of :: a -> Term;
};

class (Typerep a) => Random a where {
  random ::
    Natural -> (Natural, Natural) -> ((a, () -> Term), (Natural, Natural));
};

newtype Narrowing_type = Narrowing_sum_of_products [[Narrowing_type]];

data Narrowing_term = Narrowing_variable [Integer] Narrowing_type
  | Narrowing_constructor Integer [Narrowing_term];

class (Typerep a) => Partial_term_of a where {
  partial_term_of :: Itself a -> Narrowing_term -> Term;
};

class (Term_of a) => Full_exhaustive a where {
  full_exhaustive ::
    ((a, () -> Term) -> Maybe (Bool, [Term])) ->
      Natural -> Maybe (Bool, [Term]);
};

data Narrowing_cons a = Narrowing_cons Narrowing_type [[Narrowing_term] -> a];

class Narrowing a where {
  narrowing :: Integer -> Narrowing_cons a;
};

data Nat = Zero_nat | Suc Nat;

data Set a = Set [a] | Coset [a];

data Nibble = Nibble0 | Nibble1 | Nibble2 | Nibble3 | Nibble4 | Nibble5
  | Nibble6 | Nibble7 | Nibble8 | Nibble9 | NibbleA | NibbleB | NibbleC
  | NibbleD | NibbleE | NibbleF;

data Char = Char Nibble Nibble;

data FiniteMap a b = EmptyFM | Branch a b Int (FiniteMap a b) (FiniteMap a b);

data FiniteMap_pre_FiniteMap a b c;

data FiniteMap_IITN_FiniteMap a b;

ball :: forall a. Set a -> (a -> Bool) -> Bool;
ball (Set xs) p = all p xs;

fold :: forall a b. (a -> b -> b) -> [a] -> b -> b;
fold f (x : xs) s = fold f xs (f x s);
fold f [] s = s;

foldl :: forall a b. (a -> b -> a) -> a -> [b] -> a;
foldl f a [] = a;
foldl f a (x : xs) = foldl f (f a x) xs;

foldr :: forall a b. (a -> b -> b) -> [a] -> b -> b;
foldr f [] = id;
foldr f (x : xs) = f x . foldr f xs;

less_eq_natural :: Natural -> Natural -> Bool;
less_eq_natural m n = integer_of_natural m <= integer_of_natural n;

less_natural :: Natural -> Natural -> Bool;
less_natural m n = integer_of_natural m < integer_of_natural n;

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

removeAll :: forall a. (Eq a) => a -> [a] -> [a];
removeAll x [] = [];
removeAll x (y : xs) = (if x == y then removeAll x xs else y : removeAll x xs);

membera :: forall a. (Eq a) => [a] -> a -> Bool;
membera [] y = False;
membera (x : xs) y = x == y || membera xs y;

inserta :: forall a. (Eq a) => a -> [a] -> [a];
inserta x xs = (if membera xs x then xs else x : xs);

insert :: forall a. (Eq a) => a -> Set a -> Set a;
insert x (Coset xs) = Coset (removeAll x xs);
insert x (Set xs) = Set (inserta x xs);

member :: forall a. (Eq a) => a -> Set a -> Bool;
member x (Coset xs) = not (membera xs x);
member x (Set xs) = membera xs x;

times_natural :: Natural -> Natural -> Natural;
times_natural m n = Nat (integer_of_natural m * integer_of_natural n);

mod_integer :: Integer -> Integer -> Integer;
mod_integer k l = snd (divmod_integer k l);

mod_natural :: Natural -> Natural -> Natural;
mod_natural m n =
  Nat (mod_integer (integer_of_natural m) (integer_of_natural n));

max :: forall a. (Orda a) => a -> a -> a;
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

findMin :: forall a b. FiniteMap a b -> (a, b);
findMin (Branch key elt uu EmptyFM uv) = (key, elt);
findMin (Branch key elt uw (Branch v va vb vc vd) ux) =
  findMin (Branch v va vb vc vd);

findMax :: forall a b. FiniteMap a b -> (a, b);
findMax (Branch key elt uu uv EmptyFM) = (key, elt);
findMax (Branch key elt uw ux (Branch v va vb vc vd)) =
  findMax (Branch v va vb vc vd);

unbox2 :: forall a. a -> a;
unbox2 x = x;

sizeFM :: forall a b. FiniteMap a b -> Int;
sizeFM EmptyFM = Zero_int;
sizeFM (Branch uu uv size15 uw ux) = size15;

mkBranch ::
  forall a b.
    (Ord a) => Int -> a -> b -> FiniteMap a b -> FiniteMap a b -> FiniteMap a b;
mkBranch which key elt fm_l fm_r =
  let {
    unbox = unbox2;
    _ = (case fm_l of {
          EmptyFM -> True;
          Branch _ _ _ _ _ ->
            let {
              biggest_left_key = fst (findMax fm_l);
            } in less biggest_left_key key;
        });
    _ = (case fm_r of {
          EmptyFM -> True;
          Branch _ _ _ _ _ -> let {
                                a = fst (findMin fm_r);
                              } in less key a;
        });
    _ = True;
    left_size = sizeFM fm_l;
    right_size = sizeFM fm_r;
    result =
      Branch key elt
        (unbox (plus_int (plus_int (Pos One) left_size) right_size)) fm_l fm_r;
  } in result;

single_R10 ::
  forall a b.
    (Ord b) => (a, b) -> FiniteMap b a -> FiniteMap b a -> FiniteMap b a;
single_R10 (elt, key) (Branch key_l elt_l uu fm_ll fm_lr) fm_r =
  mkBranch (Pos (Bit0 (Bit0 (Bit0 One)))) key_l elt_l fm_ll
    (mkBranch (Pos (Bit1 (Bit0 (Bit0 One)))) key elt fm_lr fm_r);

sIZE_RATIO :: Int;
sIZE_RATIO = Pos (Bit1 (Bit0 One));

single_L8 ::
  forall a b.
    (Ord b) => (a, b) -> FiniteMap b a -> FiniteMap b a -> FiniteMap b a;
single_L8 (elt, key) fm_l (Branch key_r elt_r uu fm_rl fm_rr) =
  mkBranch (Pos (Bit1 One)) key_r elt_r
    (mkBranch (Pos (Bit0 (Bit0 One))) key elt fm_l fm_rl) fm_rr;

double_R6 ::
  forall a b.
    (Ord b) => (a, b) -> FiniteMap b a -> FiniteMap b a -> FiniteMap b a;
double_R6 (elt, key)
  (Branch key_l elt_l uu fm_ll (Branch key_lr elt_lr uv fm_lrl fm_lrr)) fm_r =
  mkBranch (Pos (Bit0 (Bit1 (Bit0 One)))) key_lr elt_lr
    (mkBranch (Pos (Bit1 (Bit1 (Bit0 One)))) key_l elt_l fm_ll fm_lrl)
    (mkBranch (Pos (Bit0 (Bit0 (Bit1 One)))) key elt fm_lrr fm_r);

double_L4 ::
  forall a b.
    (Ord b) => (a, b) -> FiniteMap b a -> FiniteMap b a -> FiniteMap b a;
double_L4 (elt, key) fm_l
  (Branch key_r elt_r uu (Branch key_rl elt_rl uv fm_rll fm_rlr) fm_rr) =
  mkBranch (Pos (Bit1 (Bit0 One))) key_rl elt_rl
    (mkBranch (Pos (Bit0 (Bit1 One))) key elt fm_l fm_rll)
    (mkBranch (Pos (Bit1 (Bit1 One))) key_r elt_r fm_rlr fm_rr);

mkBalBranch ::
  forall a b.
    (Ord a) => a -> b -> FiniteMap a b -> FiniteMap a b -> FiniteMap a b;
mkBalBranch key elt fm_L fm_R =
  let {
    double_L = double_L4 (elt, key);
    double_R = double_R6 (elt, key);
    single_L = single_L8 (elt, key);
    single_R = single_R10 (elt, key);
    size_l = sizeFM fm_L;
    size_r = sizeFM fm_R;
  } in (if less_int (plus_int size_l size_r) (Pos (Bit0 One))
         then mkBranch (Pos One) key elt fm_L fm_R
         else (if less_int (times_int sIZE_RATIO size_l) size_r
                then let {
                       (Branch _ _ _ fm_rl fm_rr) = fm_R;
                     } in (if less_int (sizeFM fm_rl)
                                (times_int (Pos (Bit0 One)) (sizeFM fm_rr))
                            then single_L fm_L fm_R else double_L fm_L fm_R)
                else (if less_int (times_int sIZE_RATIO size_r) size_l
                       then let {
                              (Branch _ _ _ fm_ll fm_lr) = fm_L;
                            } in (if less_int (sizeFM fm_lr)
                                       (times_int (Pos (Bit0 One))
 (sizeFM fm_ll))
                                   then single_R fm_L fm_R
                                   else double_R fm_L fm_R)
                       else mkBranch (Pos (Bit0 One)) key elt fm_L fm_R)));

emptyFM :: forall a b. FiniteMap a b;
emptyFM = EmptyFM;

unitFM :: forall a b. a -> b -> FiniteMap a b;
unitFM key elt = Branch key elt (Pos One) emptyFM emptyFM;

addToFM_C ::
  forall a b.
    (Ord b) => (a -> a -> a) -> FiniteMap b a -> b -> a -> FiniteMap b a;
addToFM_C combiner EmptyFM key elt = unitFM key elt;
addToFM_C combiner (Branch key elt size12 fm_l fm_r) new_key new_elt =
  (if less new_key key
    then mkBalBranch key elt (addToFM_C combiner fm_l new_key new_elt) fm_r
    else (if less key new_key
           then mkBalBranch key elt fm_l
                  (addToFM_C combiner fm_r new_key new_elt)
           else Branch new_key (combiner elt new_elt) size12 fm_l fm_r));

add0 ::
  forall a b.
    (Ord b) => (a -> a -> a) -> FiniteMap b a -> (b, a) -> FiniteMap b a;
add0 combiner fmap (key, elt) = addToFM_C combiner fmap key elt;

mapFM :: forall a b c. (a -> b -> c) -> FiniteMap a b -> FiniteMap a c;
mapFM f EmptyFM = emptyFM;
mapFM f (Branch key elt size14 fm_l fm_r) =
  Branch key (f key elt) size14 (mapFM f fm_l) (mapFM f fm_r);

lookupFM :: forall a b. (Ord a) => FiniteMap a b -> a -> Maybe b;
lookupFM EmptyFM key = Nothing;
lookupFM (Branch key elt uu fm_l fm_r) key_to_find =
  (if less key_to_find key then lookupFM fm_l key_to_find
    else (if less key key_to_find then lookupFM fm_r key_to_find
           else Just elt));

elemFM :: forall a b. (Ord a) => a -> FiniteMap a b -> Bool;
elemFM key fm = (case lookupFM fm key of {
                  Nothing -> False;
                  Just _ -> True;
                });

foldFM :: forall a b c. (a -> b -> c -> c) -> c -> FiniteMap a b -> c;
foldFM k z EmptyFM = z;
foldFM k z (Branch key elt uu fm_l fm_r) =
  foldFM k (k key elt (foldFM k z fm_r)) fm_l;

eltsFM :: forall a b. FiniteMap a b -> [b];
eltsFM fm = foldFM (\ _ -> (\ a b -> a : b)) [] fm;

isJust :: forall a. Maybe a -> Bool;
isJust (Just uu) = True;
isJust Nothing = False;

keysFM :: forall a b. FiniteMap a b -> [a];
keysFM fm = foldFM (\ key _ -> (\ a -> key : a)) [] fm;

addToFM :: forall a b. (Ord a) => FiniteMap a b -> a -> b -> FiniteMap a b;
addToFM fm key elt = addToFM_C (\ _ new -> new) fm key elt;

mkVBalBranch ::
  forall a b.
    (Ord a) => a -> b -> FiniteMap a b -> FiniteMap a b -> FiniteMap a b;
mkVBalBranch key elt EmptyFM fm_r = addToFM fm_r key elt;
mkVBalBranch key elt (Branch v va vb vc vd) EmptyFM =
  addToFM (Branch v va vb vc vd) key elt;
mkVBalBranch key elt (Branch key_l elt_l a0 fm_ll fm_lr)
  (Branch key_r elt_r a1 fm_rl fm_rr) =
  let {
    fm_l = Branch key_l elt_l a0 fm_ll fm_lr;
    fm_r = Branch key_r elt_r a1 fm_rl fm_rr;
    size_l = sizeFM fm_l;
    size_r = sizeFM fm_r;
  } in (if less_int (times_int sIZE_RATIO size_l) size_r
         then mkBalBranch key_r elt_r (mkVBalBranch key elt fm_l fm_rl) fm_rr
         else (if less_int (times_int sIZE_RATIO size_r) size_l
                then mkBalBranch key_l elt_l fm_ll
                       (mkVBalBranch key elt fm_lr fm_r)
                else mkBranch (Pos (Bit1 (Bit0 (Bit1 One)))) key elt fm_l
                       fm_r));

splitLT :: forall a b. (Ord a) => FiniteMap a b -> a -> FiniteMap a b;
splitLT EmptyFM split_key = emptyFM;
splitLT (Branch key elt uu fm_l fm_r) split_key =
  (if less split_key key then splitLT fm_l split_key
    else (if less key split_key
           then mkVBalBranch key elt fm_l (splitLT fm_r split_key) else fm_l));

splitGT :: forall a b. (Ord a) => FiniteMap a b -> a -> FiniteMap a b;
splitGT EmptyFM split_key = emptyFM;
splitGT (Branch key elt uu fm_l fm_r) split_key =
  (if less key split_key then splitGT fm_r split_key
    else (if less split_key key
           then mkVBalBranch key elt (splitGT fm_l split_key) fm_r else fm_r));

plusFM ::
  forall a b. (Ord a) => FiniteMap a b -> FiniteMap a b -> FiniteMap a b;
plusFM EmptyFM fm2 = fm2;
plusFM (Branch v va vb vc vd) EmptyFM = Branch v va vb vc vd;
plusFM (Branch v va vb vc vd) (Branch split_key elt1 uu left right) =
  let {
    lts = splitLT (Branch v va vb vc vd) split_key;
    gts = splitGT (Branch v va vb vc vd) split_key;
  } in mkVBalBranch split_key elt1 (plusFM lts left) (plusFM gts right);

deleteMin :: forall a b. (Ord a) => FiniteMap a b -> FiniteMap a b;
deleteMin (Branch key elt uu EmptyFM fm_r) = fm_r;
deleteMin (Branch key elt uv (Branch v va vb vc vd) fm_r) =
  mkBalBranch key elt (deleteMin (Branch v va vb vc vd)) fm_r;

deleteMax :: forall a b. (Ord a) => FiniteMap a b -> FiniteMap a b;
deleteMax (Branch key elt uu fm_l EmptyFM) = fm_l;
deleteMax (Branch key elt uv fm_l (Branch v va vb vc vd)) =
  mkBalBranch key elt fm_l (deleteMax (Branch v va vb vc vd));

glueBal ::
  forall a b. (Ord a) => FiniteMap a b -> FiniteMap a b -> FiniteMap a b;
glueBal EmptyFM fm2 = fm2;
glueBal (Branch v va vb vc vd) EmptyFM = Branch v va vb vc vd;
glueBal (Branch v va vb vc vd) (Branch ve vf vg vh vi) =
  let {
    (mid_key1, mid_elt1) = findMax (Branch v va vb vc vd);
    (mid_key2, mid_elt2) = findMin (Branch ve vf vg vh vi);
  } in (if less_int (sizeFM (Branch v va vb vc vd))
             (sizeFM (Branch ve vf vg vh vi))
         then mkBalBranch mid_key2 mid_elt2 (Branch v va vb vc vd)
                (deleteMin (Branch ve vf vg vh vi))
         else mkBalBranch mid_key1 mid_elt1 (deleteMax (Branch v va vb vc vd))
                (Branch ve vf vg vh vi));

glueVBal ::
  forall a b. (Ord a) => FiniteMap a b -> FiniteMap a b -> FiniteMap a b;
glueVBal EmptyFM fm2 = fm2;
glueVBal (Branch v va vb vc vd) EmptyFM = Branch v va vb vc vd;
glueVBal (Branch key_l elt_l a2 fm_ll fm_lr) (Branch key_r elt_r a3 fm_rl fm_rr)
  = let {
      fm_l = Branch key_l elt_l a2 fm_ll fm_lr;
      fm_r = Branch key_r elt_r a3 fm_rl fm_rr;
      size_l = sizeFM fm_l;
      size_r = sizeFM fm_r;
    } in (if less_int (times_int sIZE_RATIO size_l) size_r
           then mkBalBranch key_r elt_r (glueVBal fm_l fm_rl) fm_rr
           else (if less_int (times_int sIZE_RATIO size_r) size_l
                  then mkBalBranch key_l elt_l fm_ll (glueVBal fm_lr fm_r)
                  else glueBal fm_l fm_r));

minusFM ::
  forall a b. (Ord a) => FiniteMap a b -> FiniteMap a b -> FiniteMap a b;
minusFM EmptyFM fm2 = emptyFM;
minusFM (Branch v va vb vc vd) EmptyFM = Branch v va vb vc vd;
minusFM (Branch v va vb vc vd) (Branch split_key elt uu left right) =
  let {
    lts = splitLT (Branch v va vb vc vd) split_key;
    gts = splitGT (Branch v va vb vc vd) split_key;
  } in glueVBal (minusFM lts left) (minusFM gts right);

filterFM ::
  forall a b. (Ord a) => (a -> b -> Bool) -> FiniteMap a b -> FiniteMap a b;
filterFM p EmptyFM = emptyFM;
filterFM p (Branch key elt uu fm_l fm_r) =
  (if p key elt then mkVBalBranch key elt (filterFM p fm_l) (filterFM p fm_r)
    else glueVBal (filterFM p fm_l) (filterFM p fm_r));

fmToList :: forall a b. FiniteMap a b -> [(a, b)];
fmToList fm = foldFM (\ key elt -> (\ a -> (key, elt) : a)) [] fm;

addListToFM_C ::
  forall a b.
    (Ord b) => (a -> a -> a) -> FiniteMap b a -> [(b, a)] -> FiniteMap b a;
addListToFM_C combiner fm key_elt_pairs =
  let {
    add = add0 combiner;
  } in foldl add fm key_elt_pairs;

addListToFM ::
  forall a b. (Ord a) => FiniteMap a b -> [(a, b)] -> FiniteMap a b;
addListToFM fm key_elt_pairs = addListToFM_C (\ _ new -> new) fm key_elt_pairs;

listToFM :: forall a b. (Ord a) => [(a, b)] -> FiniteMap a b;
listToFM = addListToFM emptyFM;

plusFM_C ::
  forall a b.
    (Ord b) => (a -> a -> a) -> FiniteMap b a -> FiniteMap b a -> FiniteMap b a;
plusFM_C combiner EmptyFM fm2 = fm2;
plusFM_C combiner (Branch v va vb vc vd) EmptyFM = Branch v va vb vc vd;
plusFM_C combiner (Branch v va vb vc vd) (Branch split_key elt2 uu left right) =
  let {
    lts = splitLT (Branch v va vb vc vd) split_key;
    gts = splitGT (Branch v va vb vc vd) split_key;
    new_elt =
      (case lookupFM (Branch v va vb vc vd) split_key of {
        Nothing -> elt2;
        Just elt1 -> combiner elt1 elt2;
      });
  } in mkVBalBranch split_key new_elt (plusFM_C combiner lts left)
         (plusFM_C combiner gts right);

delFromFM :: forall a b. (Ord a) => FiniteMap a b -> a -> FiniteMap a b;
delFromFM EmptyFM del_key = emptyFM;
delFromFM (Branch key elt size13 fm_l fm_r) del_key =
  (if less key del_key then mkBalBranch key elt fm_l (delFromFM fm_r del_key)
    else (if less del_key key
           then mkBalBranch key elt (delFromFM fm_l del_key) fm_r
           else glueBal fm_l fm_r));

eq_int :: Int -> Int -> Bool;
eq_int x y = equal_int x y;

isEmptyFM :: forall a b. FiniteMap a b -> Bool;
isEmptyFM fm = eq_int (sizeFM fm) Zero_int;

listsum :: forall a. (Monoid_add a) => [a] -> a;
listsum xs = foldr plus xs zero;

select_weight ::
  forall a. [(Natural, a)] -> (Natural, Natural) -> (a, (Natural, Natural));
select_weight xs =
  scomp (range (listsum (map fst xs))) (\ k -> (\ a -> (pick xs k, a)));

mapMaybeFM ::
  forall a b c.
    (Ord a) => (a -> b -> Maybe c) -> FiniteMap a b -> FiniteMap a c;
mapMaybeFM f EmptyFM = emptyFM;
mapMaybeFM f (Branch key elt uu fm_l fm_r) =
  (case f key elt of {
    Nothing -> glueVBal (mapMaybeFM f fm_l) (mapMaybeFM f fm_r);
    Just elta -> mkVBalBranch key elta (mapMaybeFM f fm_l) (mapMaybeFM f fm_r);
  });

valapp ::
  forall a b. (a -> b, () -> Term) -> (a, () -> Term) -> (b, () -> Term);
valapp (f, tf) (x, tx) = (f x, (\ _ -> App (tf ()) (tx ())));

intersectFM_C ::
  forall a b c d.
    (Ord d) => (a -> b -> c) -> FiniteMap d a -> FiniteMap d b -> FiniteMap d c;
intersectFM_C combiner fm1 EmptyFM = emptyFM;
intersectFM_C combiner EmptyFM (Branch v va vb vc vd) = emptyFM;
intersectFM_C combiner (Branch v va vb vc vd)
  (Branch split_key elt2 uu left right) =
  let {
    lts = splitLT (Branch v va vb vc vd) split_key;
    gts = splitGT (Branch v va vb vc vd) split_key;
    maybe_elt1 = lookupFM (Branch v va vb vc vd) split_key;
    elt1 = let {
             (Just x) = maybe_elt1;
           } in x;
  } in (if isJust maybe_elt1
         then mkVBalBranch split_key (combiner elt1 elt2)
                (intersectFM_C combiner lts left)
                (intersectFM_C combiner gts right)
         else glueVBal (intersectFM_C combiner lts left)
                (intersectFM_C combiner gts right));

intersectFM ::
  forall a b. (Ord a) => FiniteMap a b -> FiniteMap a b -> FiniteMap a b;
intersectFM fm1 fm2 = intersectFM_C (\ _ right -> right) fm1 fm2;

delListFromFM :: forall a b. (Ord a) => FiniteMap a b -> [a] -> FiniteMap a b;
delListFromFM fm keys = foldl delFromFM fm keys;

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

bot_set :: forall a. Set a;
bot_set = Set [];

sup_set :: forall a. (Eq a) => Set a -> Set a -> Set a;
sup_set (Coset xs) a = Coset (filter (\ x -> not (member x a)) xs);
sup_set (Set xs) a = fold insert xs a;

set2_FiniteMap :: forall a b. (Eq b) => FiniteMap a b -> Set b;
set2_FiniteMap EmptyFM = bot_set;
set2_FiniteMap (Branch x21 x22 x23 x24 x25) =
  insert x22 (sup_set (set2_FiniteMap x24) (set2_FiniteMap x25));

set1_FiniteMap :: forall a b. (Eq a) => FiniteMap a b -> Set a;
set1_FiniteMap EmptyFM = bot_set;
set1_FiniteMap (Branch x21 x22 x23 x24 x25) =
  insert x21 (sup_set (set1_FiniteMap x24) (set1_FiniteMap x25));

pred_FiniteMap ::
  forall a b.
    (Eq a, Eq b) => (a -> Bool) -> (b -> Bool) -> FiniteMap a b -> Bool;
pred_FiniteMap p1 p2 =
  (\ x -> ball (set1_FiniteMap x) p1 && ball (set2_FiniteMap x) p2);

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

of_nat_aux :: forall a. (Semiring_1 a) => (a -> a) -> Nat -> a -> a;
of_nat_aux inc Zero_nat i = i;
of_nat_aux inc (Suc n) i = of_nat_aux inc n (inc i);

of_nat :: forall a. (Semiring_1 a) => Nat -> a;
of_nat n = of_nat_aux (\ i -> plus i one) n zero;

lookupWithDefaultFM :: forall a b. (Ord a) => FiniteMap a b -> b -> a -> b;
lookupWithDefaultFM fm deflt key =
  (case lookupFM fm key of {
    Nothing -> deflt;
    Just elt -> elt;
  });

non_empty :: Narrowing_type -> Bool;
non_empty (Narrowing_sum_of_products ps) = not (null ps);

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

random_aux_FiniteMap ::
  forall a b.
    (Random a,
      Random b) => Natural ->
                     Natural ->
                       (Natural, Natural) ->
                         ((FiniteMap a b, () -> Term), (Natural, Natural));
random_aux_FiniteMap i j s =
  collapse
    (select_weight
      [(i, scomp (random j)
             (\ x ->
               scomp (random j)
                 (\ y ->
                   scomp (random_int j)
                     (\ z ->
                       scomp (random_aux_FiniteMap (minus_natural i one_natural)
                               j)
                         (\ aa ->
                           scomp (random_aux_FiniteMap
                                   (minus_natural i one_natural) j)
                             (\ ab ->
                               (\ a ->
                                 (valapp
                                    (valapp
                                      (valapp
(valapp
  (valapp
    (Branch,
      (\ _ ->
        Const "Finite_Map.FiniteMap.Branch"
          (Typerep "fun"
            [(typerep :: Itself a -> Typerepa) Type,
              Typerep "fun"
                [(typerep :: Itself b -> Typerepa) Type,
                  Typerep "fun"
                    [Typerep "Int.int" [],
                      Typerep "fun"
                        [Typerep "Finite_Map.FiniteMap"
                           [(typerep :: Itself a -> Typerepa) Type,
                             (typerep :: Itself b -> Typerepa) Type],
                          Typerep "fun"
                            [Typerep "Finite_Map.FiniteMap"
                               [(typerep :: Itself a -> Typerepa) Type,
                                 (typerep :: Itself b -> Typerepa) Type],
                              Typerep "Finite_Map.FiniteMap"
                                [(typerep :: Itself a -> Typerepa) Type,
                                  (typerep :: Itself b -> Typerepa)
                                    Type]]]]]])))
    x)
  y)
z)
                                      aa)
                                    ab,
                                   a)))))))),
        (one_natural,
          (\ a ->
            ((EmptyFM,
               (\ _ ->
                 Const "Finite_Map.FiniteMap.EmptyFM"
                   (Typerep "Finite_Map.FiniteMap"
                     [(typerep :: Itself a -> Typerepa) Type,
                       (typerep :: Itself b -> Typerepa) Type]))),
              a)))])
    s;

drawn_from :: forall a. [a] -> Narrowing_cons a;
drawn_from xs =
  Narrowing_cons (Narrowing_sum_of_products (map (\ _ -> []) xs))
    (map (\ x _ -> x) xs);

around_zero :: Int -> [Int];
around_zero i =
  (if less_int i Zero_int then []
    else (if equal_int i Zero_int then [Zero_int]
           else around_zero (minus_int i (Pos One)) ++ [i, uminus_int i]));

map_FiniteMap ::
  forall a b c d. (a -> b) -> (c -> d) -> FiniteMap a c -> FiniteMap b d;
map_FiniteMap f1 f2 EmptyFM = EmptyFM;
map_FiniteMap f1 f2 (Branch x21 x22 x23 x24 x25) =
  Branch (f1 x21) (f2 x22) x23 (map_FiniteMap f1 f2 x24)
    (map_FiniteMap f1 f2 x25);

rec_FiniteMap ::
  forall a b c.
    a -> (b -> c -> Int -> FiniteMap b c -> FiniteMap b c -> a -> a -> a) ->
           FiniteMap b c -> a;
rec_FiniteMap f1 f2 EmptyFM = f1;
rec_FiniteMap f1 f2 (Branch x21 x22 x23 x24 x25) =
  f2 x21 x22 x23 x24 x25 (rec_FiniteMap f1 f2 x24) (rec_FiniteMap f1 f2 x25);

rel_FiniteMap ::
  forall a b c d.
    (a -> b -> Bool) ->
      (c -> d -> Bool) -> FiniteMap a c -> FiniteMap b d -> Bool;
rel_FiniteMap r1 r2 EmptyFM (Branch y21 y22 y23 y24 y25) = False;
rel_FiniteMap r1 r2 (Branch y21 y22 y23 y24 y25) EmptyFM = False;
rel_FiniteMap r1 r2 EmptyFM EmptyFM = True;
rel_FiniteMap r1 r2 (Branch x21 x22 x23 x24 x25) (Branch y21 y22 y23 y24 y25) =
  r1 x21 y21 &&
    r2 x22 y22 &&
      equal_int x23 y23 &&
        rel_FiniteMap r1 r2 x24 y24 && rel_FiniteMap r1 r2 x25 y25;

size_FiniteMap :: forall a b. (a -> Nat) -> (b -> Nat) -> FiniteMap a b -> Nat;
size_FiniteMap xa x EmptyFM = Zero_nat;
size_FiniteMap xa x (Branch x21 x22 x23 x24 x25) =
  plus_nat
    (plus_nat (plus_nat (plus_nat (xa x21) (x x22)) (size_FiniteMap xa x x24))
      (size_FiniteMap xa x x25))
    (Suc Zero_nat);

one_integer :: Integer;
one_integer = (1 :: Integer);

full_exhaustive_int ::
  ((Int, () -> Term) -> Maybe (Bool, [Term])) ->
    Int -> Int -> Maybe (Bool, [Term]);
full_exhaustive_int f d i =
  (if less_int d i then Nothing
    else (case f (i, (\ _ -> term_of_int i)) of {
           Nothing -> full_exhaustive_int f d (plus_int i (Pos One));
           Just a -> Just a;
         }));

size_FiniteMapa :: forall a b. FiniteMap a b -> Nat;
size_FiniteMapa EmptyFM = Zero_nat;
size_FiniteMapa (Branch x21 x22 x23 x24 x25) =
  plus_nat (plus_nat (size_FiniteMapa x24) (size_FiniteMapa x25))
    (Suc Zero_nat);

equal_FiniteMap ::
  forall a b. (Eq a, Eq b) => FiniteMap a b -> FiniteMap a b -> Bool;
equal_FiniteMap EmptyFM (Branch x21 x22 x23 x24 x25) = False;
equal_FiniteMap (Branch x21 x22 x23 x24 x25) EmptyFM = False;
equal_FiniteMap (Branch x21 x22 x23 x24 x25) (Branch y21 y22 y23 y24 y25) =
  x21 == y21 &&
    x22 == y22 &&
      equal_int x23 y23 && equal_FiniteMap x24 y24 && equal_FiniteMap x25 y25;
equal_FiniteMap EmptyFM EmptyFM = True;

partial_term_of_int :: Itself Int -> Narrowing_term -> Term;
partial_term_of_int ty (Narrowing_constructor i []) =
  (if mod_integer i (2 :: Integer) == (0 :: Integer)
    then term_of_int (div_int (uminus_int (int_of_integer i)) (Pos (Bit0 One)))
    else term_of_int
           (div_int (plus_int (int_of_integer i) (Pos One)) (Pos (Bit0 One))));
partial_term_of_int ty (Narrowing_variable p t) =
  Free "_" (Typerep "Int.int" []);

random_FiniteMap ::
  forall a b.
    (Random a,
      Random b) => Natural ->
                     (Natural, Natural) ->
                       ((FiniteMap a b, () -> Term), (Natural, Natural));
random_FiniteMap i = random_aux_FiniteMap i i;

term_of_FiniteMap ::
  forall a b. (Term_of a, Term_of b) => FiniteMap a b -> Term;
term_of_FiniteMap (Branch a b c d e) =
  App (App (App (App (App (Const "Finite_Map.FiniteMap.Branch"
                            (Typerep "fun"
                              [(typerep :: Itself a -> Typerepa) Type,
                                Typerep "fun"
                                  [(typerep :: Itself b -> Typerepa) Type,
                                    Typerep "fun"
                                      [Typerep "Int.int" [],
Typerep "fun"
  [Typerep "Finite_Map.FiniteMap"
     [(typerep :: Itself a -> Typerepa) Type,
       (typerep :: Itself b -> Typerepa) Type],
    Typerep "fun"
      [Typerep "Finite_Map.FiniteMap"
         [(typerep :: Itself a -> Typerepa) Type,
           (typerep :: Itself b -> Typerepa) Type],
        Typerep "Finite_Map.FiniteMap"
          [(typerep :: Itself a -> Typerepa) Type,
            (typerep :: Itself b -> Typerepa) Type]]]]]]))
                       (term_of a))
                  (term_of b))
             (term_of_int c))
        (term_of_FiniteMap d))
    (term_of_FiniteMap e);
term_of_FiniteMap EmptyFM =
  Const "Finite_Map.FiniteMap.EmptyFM"
    (Typerep "Finite_Map.FiniteMap"
      [(typerep :: Itself a -> Typerepa) Type,
        (typerep :: Itself b -> Typerepa) Type]);

typerep_FiniteMap ::
  forall a b. (Typerep a, Typerep b) => Itself (FiniteMap a b) -> Typerepa;
typerep_FiniteMap t =
  Typerep "Finite_Map.FiniteMap"
    [(typerep :: Itself a -> Typerepa) Type,
      (typerep :: Itself b -> Typerepa) Type];

full_exhaustive_inta ::
  ((Int, () -> Term) -> Maybe (Bool, [Term])) ->
    Natural -> Maybe (Bool, [Term]);
full_exhaustive_inta f d =
  full_exhaustive_int f (int_of_integer (integer_of_natural d))
    (uminus_int (int_of_integer (integer_of_natural d)));

full_exhaustive_FiniteMap ::
  forall a b.
    (Full_exhaustive a,
      Full_exhaustive b) => ((FiniteMap a b, () -> Term) ->
                              Maybe (Bool, [Term])) ->
                              Natural -> Maybe (Bool, [Term]);
full_exhaustive_FiniteMap f i =
  (if less_natural zero_natural i
    then (case f (EmptyFM,
                   (\ _ ->
                     Const "Finite_Map.FiniteMap.EmptyFM"
                       (Typerep "Finite_Map.FiniteMap"
                         [(typerep :: Itself a -> Typerepa) Type,
                           (typerep :: Itself b -> Typerepa) Type])))
           of {
           Nothing ->
             full_exhaustive
               (\ (uu, uua) ->
                 full_exhaustive
                   (\ (uub, uuc) ->
                     full_exhaustive_inta
                       (\ (uud, uue) ->
                         full_exhaustive_FiniteMap
                           (\ (uuf, uug) ->
                             full_exhaustive_FiniteMap
                               (\ (uuh, uui) ->
                                 f (Branch uu uub uud uuf uuh,
                                     (\ _ ->
                                       App
 (App (App (App (App (Const "Finite_Map.FiniteMap.Branch"
                       (Typerep "fun"
                         [(typerep :: Itself a -> Typerepa) Type,
                           Typerep "fun"
                             [(typerep :: Itself b -> Typerepa) Type,
                               Typerep "fun"
                                 [Typerep "Int.int" [],
                                   Typerep "fun"
                                     [Typerep "Finite_Map.FiniteMap"
[(typerep :: Itself a -> Typerepa) Type,
  (typerep :: Itself b -> Typerepa) Type],
                                       Typerep "fun"
 [Typerep "Finite_Map.FiniteMap"
    [(typerep :: Itself a -> Typerepa) Type,
      (typerep :: Itself b -> Typerepa) Type],
   Typerep "Finite_Map.FiniteMap"
     [(typerep :: Itself a -> Typerepa) Type,
       (typerep :: Itself b -> Typerepa) Type]]]]]]))
                  (uua ()))
             (uuc ()))
        (uue ()))
   (uug ()))
 (uui ()))))
                               (minus_natural i one_natural))
                           (minus_natural i one_natural))
                       (minus_natural i one_natural))
                   (minus_natural i one_natural))
               (minus_natural i one_natural);
           Just a -> Just a;
         })
    else Nothing);

partial_term_of_FiniteMap ::
  forall a b.
    (Partial_term_of a,
      Partial_term_of b) => Itself (FiniteMap a b) -> Narrowing_term -> Term;
partial_term_of_FiniteMap ty
  (Narrowing_constructor (1 :: Integer) [e, d, c, b, a]) =
  App (App (App (App (App (Const "Finite_Map.FiniteMap.Branch"
                            (Typerep "fun"
                              [(typerep :: Itself a -> Typerepa) Type,
                                Typerep "fun"
                                  [(typerep :: Itself b -> Typerepa) Type,
                                    Typerep "fun"
                                      [Typerep "Int.int" [],
Typerep "fun"
  [Typerep "Finite_Map.FiniteMap"
     [(typerep :: Itself a -> Typerepa) Type,
       (typerep :: Itself b -> Typerepa) Type],
    Typerep "fun"
      [Typerep "Finite_Map.FiniteMap"
         [(typerep :: Itself a -> Typerepa) Type,
           (typerep :: Itself b -> Typerepa) Type],
        Typerep "Finite_Map.FiniteMap"
          [(typerep :: Itself a -> Typerepa) Type,
            (typerep :: Itself b -> Typerepa) Type]]]]]]))
                       ((partial_term_of :: Itself a -> Narrowing_term -> Term)
                         Type a))
                  ((partial_term_of :: Itself b -> Narrowing_term -> Term) Type
                    b))
             (partial_term_of_int Type c))
        ((partial_term_of_FiniteMap ::
           Itself (FiniteMap a b) -> Narrowing_term -> Term)
          Type d))
    ((partial_term_of_FiniteMap ::
       Itself (FiniteMap a b) -> Narrowing_term -> Term)
      Type e);
partial_term_of_FiniteMap ty (Narrowing_constructor (0 :: Integer) []) =
  Const "Finite_Map.FiniteMap.EmptyFM"
    (Typerep "Finite_Map.FiniteMap"
      [(typerep :: Itself a -> Typerepa) Type,
        (typerep :: Itself b -> Typerepa) Type]);
partial_term_of_FiniteMap ty (Narrowing_variable p tt) =
  Free "_"
    (Typerep "Finite_Map.FiniteMap"
      [(typerep :: Itself a -> Typerepa) Type,
        (typerep :: Itself b -> Typerepa) Type]);

typerep_FiniteMap_pre_FiniteMap ::
  forall a b c.
    (Typerep a, Typerep b,
      Typerep c) => Itself (FiniteMap_pre_FiniteMap a b c) -> Typerepa;
typerep_FiniteMap_pre_FiniteMap t =
  Typerep "Finite_Map.FiniteMap.FiniteMap_pre_FiniteMap"
    [(typerep :: Itself a -> Typerepa) Type,
      (typerep :: Itself b -> Typerepa) Type,
      (typerep :: Itself c -> Typerepa) Type];

typerep_FiniteMap_IITN_FiniteMap ::
  forall a b.
    (Typerep a, Typerep b) => Itself (FiniteMap_IITN_FiniteMap a b) -> Typerepa;
typerep_FiniteMap_IITN_FiniteMap t =
  Typerep "Finite_Map.FiniteMap.FiniteMap_IITN_FiniteMap"
    [(typerep :: Itself a -> Typerepa) Type,
      (typerep :: Itself b -> Typerepa) Type];

}
