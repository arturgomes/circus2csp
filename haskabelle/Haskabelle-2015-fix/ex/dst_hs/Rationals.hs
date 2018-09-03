{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Rationals(Num(..), plus_num, times_num, Int(..), times_int, Times(..),
             one_int, One(..), equal_num, equal_int, not_eq_int, eq_int,
             Eqa(..), uminus_int, bitM, dup, minus_int, sub, plus_int, less_num,
             less_eq_num, less_int, sgn_inta, abs_inta, apsnda, Ord(..),
             Plus(..), Numeral, numeral, Minus(..), Zero(..), Monoid_add,
             Semiring_1, Div(..), Semiring_numeral_div, divmod_step, divmoda,
             less_eq_int, divmod_abs, divmod_int, div_inta, mod_inta, one_inta,
             Onea(..), plus_inta, Plusa(..), zero_int, Zeroa(..), times_inta,
             Timesa(..), Semiring_1a, Nibble(..), equal_nibble, Char(..),
             equal_char, Typerepa(..), Itself(..), typerep_char, Typerep(..),
             Terma(..), term_of_nibble, Nat(..), minus_nata, equal_nat,
             less_nata, less_eq_nata, divmod_nat, div_nat, enum_nibble,
             mod_nata, plus_nat, one_nat, nat_of_num, nth, nibble_of_nat,
             nat_of_char, case_char, term_of_char, Term_of(..),
             Narrowing_type(..), Narrowing_term(..), Partial_term_of(..),
             partial_term_of_nibble, partial_term_of_char, Rat(..), one_rat,
             one_Rat, sgn_int, abs_int, less_eq_rat, less_eq_Rat, less_rat,
             less_Rat, Orda(..), Nata(..), minus_nat, less_nat, less_eq_nat,
             eq_nat, divmod, mod_nat, gcd_nat, of_nat_aux, of_nat, nat_aux, nat,
             gcd_int, divmod_0, apsnd, divmod_inta, div_int, fract_norm,
             plus_rat, plus_Rat, times_rat, times_Rat, minus_rat, minus_Rat,
             neg_rat, neg_Rat, zero_rat, zero_Rat, Minusa(..), Uminus(..),
             Ring_1, Typerepb(..), equal_Typerep, typerep_Typerep, term_of_list,
             term_of_Typerep, partial_term_of_list, partial_term_of_Typerep,
             Natural(..), integer_of_natural, plus_natural, zero_natural,
             Diva(..), Inverse(..), Field_char_0, Set(..), Term(..),
             Nibblea(..), Chara(..), Itselfa(..), Nat_IITN_Nat, Rat_IITN_Rat,
             Term_pre_Term, Term_IITN_Term, Chara_IITN_Chara, Itself_pre_Itself,
             Nibble_pre_Nibble, Narrowing_cons(..), Itself_IITN_Itself,
             Nibble_IITN_Nibble, Typerep_IITN_Typerep, ball, foldr,
             less_eq_natural, less_natural, one_natural, sgn_integer,
             abs_integer, divmod_integer, div_integer, div_natural, log,
             times_natural, mod_integer, mod_natural, max, natural_of_integer,
             minus_natural, minus_shift, next, pick, scompa, equal_natural,
             iterate, range, leta, maxaa, maxa, minaa, mina, scomp, split,
             eq_rat, of_int, of_rat, abs_rat, collect, inf_rat, mod_int,
             sgn_rat, sup_rat, size_list, listsum, select_weight, divide_rat,
             rec_Nat, rec_Rat, bot_set, set_Itself, pred_Itself, valapp,
             size_Nat, size_Rat, rec_Term, sum, size_Term, collapse,
             random_aux_Nat, term_of_num, term_of_int, of_nat_auxa, of_nata,
             nat_of_integer, nat_of_natural, random_int, random_aux_Rat, cons,
             rec_Chara, size_Chara, random_aux_Nibble, random_Nibble,
             random_aux_Chara, int_of_integer, map_Itself, rec_Itself,
             rel_Itself, rec_Nibble, random_aux_Itself, size_Itself,
             size_Nibble, rec_Typerep, non_empty, size_Typerep, drawn_from,
             diva_int, moda_int, around_zero, size_Nata, size_Rata, equal_Nat,
             equal_Rat, size_Terma, equal_Term, random_Nat, random_Rat,
             size_Charaa, equal_Nibble, equal_Chara, size_Itselfa, size_Nibblea,
             term_of_Nat, term_of_Rat, typerep_Nat, typerep_Rat, equal_Itself,
             random_Chara, size_Typerepa, term_of_Term, typerep_Term,
             one_integer, full_exhaustive_int, random_Itself, term_of_Nibble,
             term_of_Chara, typerep_Chara, term_of_Itself, typerep_Itself,
             typerep_Nibble, partial_term_of_int, narrowing_Itself,
             narrowing_Nibble, full_exhaustive_Nat, full_exhaustive_inta,
             full_exhaustive_Rat, partial_term_of_Nat, partial_term_of_Rat,
             partial_term_of_Term, full_exhaustive_Nibble,
             full_exhaustive_Chara, partial_term_of_Nibble,
             partial_term_of_Chara, typerep_Nat_IITN_Nat, typerep_Rat_IITN_Rat,
             full_exhaustive_Itself, partial_term_of_Itself,
             typerep_Term_pre_Term, typerep_Term_IITN_Term,
             typerep_Chara_IITN_Chara, typerep_Itself_pre_Itself,
             typerep_Nibble_pre_Nibble, typerep_Itself_IITN_Itself,
             typerep_Nibble_IITN_Nibble, typerep_Typerep_IITN_Typerep)
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

not_eq_int :: Int -> Int -> Bool;
not_eq_int x y = not (equal_int x y);

eq_int :: Int -> Int -> Bool;
eq_int x y = equal_int x y;

class Eqa a where {
  eq :: a -> a -> Bool;
  not_eq :: a -> a -> Bool;
};

instance Eqa Int where {
  eq = eq_int;
  not_eq = not_eq_int;
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

sgn_inta :: Int -> Int;
sgn_inta i =
  (if equal_int i Zero_int then Zero_int
    else (if less_int Zero_int i then Pos One else Neg One));

abs_inta :: Int -> Int;
abs_inta i = (if less_int i Zero_int then uminus_int i else i);

apsnda :: forall a b c. (a -> b) -> (c, a) -> (c, b);
apsnda f (x, y) = (x, f y);

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

divmoda :: forall a. (Semiring_numeral_div a) => Num -> Num -> (a, a);
divmoda (Bit1 m) (Bit0 n) =
  let {
    (q, r) = divmoda m n;
  } in (q, plus (times (numeral (Bit0 One)) r) one);
divmoda (Bit0 m) (Bit0 n) =
  let {
    (q, r) = divmoda m n;
  } in (q, times (numeral (Bit0 One)) r);
divmoda m n =
  (if less_num m n then (zero, numeral m)
    else divmod_step n (divmoda m (Bit0 n)));

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
  div = div_inta;
  mod = mod_inta;
};

instance Semiring_div Int where {
};

instance Semiring_div_parity Int where {
};

instance Semiring_numeral_div Int where {
};

divmod_abs :: Int -> Int -> (Int, Int);
divmod_abs Zero_int j = (Zero_int, Zero_int);
divmod_abs j Zero_int = (Zero_int, abs_inta j);
divmod_abs (Pos k) (Neg l) = divmoda k l;
divmod_abs (Neg k) (Pos l) = divmoda k l;
divmod_abs (Neg k) (Neg l) = divmoda k l;
divmod_abs (Pos k) (Pos l) = divmoda k l;

divmod_int :: Int -> Int -> (Int, Int);
divmod_int k l =
  (if equal_int k Zero_int then (Zero_int, Zero_int)
    else (if equal_int l Zero_int then (Zero_int, k)
           else apsnda (times_int (sgn_inta l))
                  (if equal_int (sgn_inta k) (sgn_inta l) then divmod_abs k l
                    else let {
                           (r, s) = divmod_abs k l;
                         } in (if equal_int s Zero_int
                                then (uminus_int r, Zero_int)
                                else (minus_int (uminus_int r) (Pos One),
                                       minus_int (abs_inta l) s)))));

div_inta :: Int -> Int -> Int;
div_inta a b = fst (divmod_int a b);

mod_inta :: Int -> Int -> Int;
mod_inta a b = snd (divmod_int a b);

one_inta :: Int;
one_inta = Pos One;

class Onea a where {
  onea :: a;
};

instance Onea Int where {
  onea = one_inta;
};

plus_inta :: Int -> Int -> Int;
plus_inta a b = plus_int a b;

class Plusa a where {
  plusa :: a -> a -> a;
};

instance Plusa Int where {
  plusa = plus_inta;
};

zero_int :: Int;
zero_int = Pos One;

class Zeroa a where {
  zeroa :: a;
};

instance Zeroa Int where {
  zeroa = zero_int;
};

times_inta :: Int -> Int -> Int;
times_inta a b = times_int a b;

class Timesa a where {
  timesa :: a -> a -> a;
};

class (Onea a, Timesa a) => Powera a where {
};

instance Timesa Int where {
  timesa = times_inta;
};

instance Powera Int where {
};

class (Plusa a) => Semigroup_adda a where {
};

class (Semigroup_adda a) => Ab_semigroup_adda a where {
};

class (Timesa a) => Semigroup_multa a where {
};

class (Ab_semigroup_adda a, Semigroup_multa a) => Semiringa a where {
};

instance Semigroup_adda Int where {
};

instance Ab_semigroup_adda Int where {
};

instance Semigroup_multa Int where {
};

instance Semiringa Int where {
};

class (Timesa a, Zeroa a) => Mult_zeroa a where {
};

instance Mult_zeroa Int where {
};

class (Semigroup_adda a, Zeroa a) => Monoid_adda a where {
};

instance Monoid_adda Int where {
};

class (Ab_semigroup_adda a, Monoid_adda a) => Comm_monoid_adda a where {
};

class (Comm_monoid_adda a, Mult_zeroa a, Semiringa a) => Semiring_0a a where {
};

instance Comm_monoid_adda Int where {
};

instance Semiring_0a Int where {
};

class (Onea a, Zeroa a) => Zero_neq_onea a where {
};

class (Powera a, Semigroup_multa a) => Monoid_multa a where {
};

class (Monoid_multa a, Semiring_0a a, Zero_neq_onea a) => Semiring_1a a where {
};

instance Zero_neq_onea Int where {
};

instance Monoid_multa Int where {
};

instance Semiring_1a Int where {
};

data Nibble = Nibble0 | Nibble1 | Nibble2 | Nibble3 | Nibble4 | Nibble5
  | Nibble6 | Nibble7 | Nibble8 | Nibble9 | NibbleA | NibbleB | NibbleC
  | NibbleD | NibbleE | NibbleF;

equal_nibble :: Nibble -> Nibble -> Bool;
equal_nibble NibbleE NibbleF = False;
equal_nibble NibbleF NibbleE = False;
equal_nibble NibbleD NibbleF = False;
equal_nibble NibbleF NibbleD = False;
equal_nibble NibbleD NibbleE = False;
equal_nibble NibbleE NibbleD = False;
equal_nibble NibbleC NibbleF = False;
equal_nibble NibbleF NibbleC = False;
equal_nibble NibbleC NibbleE = False;
equal_nibble NibbleE NibbleC = False;
equal_nibble NibbleC NibbleD = False;
equal_nibble NibbleD NibbleC = False;
equal_nibble NibbleB NibbleF = False;
equal_nibble NibbleF NibbleB = False;
equal_nibble NibbleB NibbleE = False;
equal_nibble NibbleE NibbleB = False;
equal_nibble NibbleB NibbleD = False;
equal_nibble NibbleD NibbleB = False;
equal_nibble NibbleB NibbleC = False;
equal_nibble NibbleC NibbleB = False;
equal_nibble NibbleA NibbleF = False;
equal_nibble NibbleF NibbleA = False;
equal_nibble NibbleA NibbleE = False;
equal_nibble NibbleE NibbleA = False;
equal_nibble NibbleA NibbleD = False;
equal_nibble NibbleD NibbleA = False;
equal_nibble NibbleA NibbleC = False;
equal_nibble NibbleC NibbleA = False;
equal_nibble NibbleA NibbleB = False;
equal_nibble NibbleB NibbleA = False;
equal_nibble Nibble9 NibbleF = False;
equal_nibble NibbleF Nibble9 = False;
equal_nibble Nibble9 NibbleE = False;
equal_nibble NibbleE Nibble9 = False;
equal_nibble Nibble9 NibbleD = False;
equal_nibble NibbleD Nibble9 = False;
equal_nibble Nibble9 NibbleC = False;
equal_nibble NibbleC Nibble9 = False;
equal_nibble Nibble9 NibbleB = False;
equal_nibble NibbleB Nibble9 = False;
equal_nibble Nibble9 NibbleA = False;
equal_nibble NibbleA Nibble9 = False;
equal_nibble Nibble8 NibbleF = False;
equal_nibble NibbleF Nibble8 = False;
equal_nibble Nibble8 NibbleE = False;
equal_nibble NibbleE Nibble8 = False;
equal_nibble Nibble8 NibbleD = False;
equal_nibble NibbleD Nibble8 = False;
equal_nibble Nibble8 NibbleC = False;
equal_nibble NibbleC Nibble8 = False;
equal_nibble Nibble8 NibbleB = False;
equal_nibble NibbleB Nibble8 = False;
equal_nibble Nibble8 NibbleA = False;
equal_nibble NibbleA Nibble8 = False;
equal_nibble Nibble8 Nibble9 = False;
equal_nibble Nibble9 Nibble8 = False;
equal_nibble Nibble7 NibbleF = False;
equal_nibble NibbleF Nibble7 = False;
equal_nibble Nibble7 NibbleE = False;
equal_nibble NibbleE Nibble7 = False;
equal_nibble Nibble7 NibbleD = False;
equal_nibble NibbleD Nibble7 = False;
equal_nibble Nibble7 NibbleC = False;
equal_nibble NibbleC Nibble7 = False;
equal_nibble Nibble7 NibbleB = False;
equal_nibble NibbleB Nibble7 = False;
equal_nibble Nibble7 NibbleA = False;
equal_nibble NibbleA Nibble7 = False;
equal_nibble Nibble7 Nibble9 = False;
equal_nibble Nibble9 Nibble7 = False;
equal_nibble Nibble7 Nibble8 = False;
equal_nibble Nibble8 Nibble7 = False;
equal_nibble Nibble6 NibbleF = False;
equal_nibble NibbleF Nibble6 = False;
equal_nibble Nibble6 NibbleE = False;
equal_nibble NibbleE Nibble6 = False;
equal_nibble Nibble6 NibbleD = False;
equal_nibble NibbleD Nibble6 = False;
equal_nibble Nibble6 NibbleC = False;
equal_nibble NibbleC Nibble6 = False;
equal_nibble Nibble6 NibbleB = False;
equal_nibble NibbleB Nibble6 = False;
equal_nibble Nibble6 NibbleA = False;
equal_nibble NibbleA Nibble6 = False;
equal_nibble Nibble6 Nibble9 = False;
equal_nibble Nibble9 Nibble6 = False;
equal_nibble Nibble6 Nibble8 = False;
equal_nibble Nibble8 Nibble6 = False;
equal_nibble Nibble6 Nibble7 = False;
equal_nibble Nibble7 Nibble6 = False;
equal_nibble Nibble5 NibbleF = False;
equal_nibble NibbleF Nibble5 = False;
equal_nibble Nibble5 NibbleE = False;
equal_nibble NibbleE Nibble5 = False;
equal_nibble Nibble5 NibbleD = False;
equal_nibble NibbleD Nibble5 = False;
equal_nibble Nibble5 NibbleC = False;
equal_nibble NibbleC Nibble5 = False;
equal_nibble Nibble5 NibbleB = False;
equal_nibble NibbleB Nibble5 = False;
equal_nibble Nibble5 NibbleA = False;
equal_nibble NibbleA Nibble5 = False;
equal_nibble Nibble5 Nibble9 = False;
equal_nibble Nibble9 Nibble5 = False;
equal_nibble Nibble5 Nibble8 = False;
equal_nibble Nibble8 Nibble5 = False;
equal_nibble Nibble5 Nibble7 = False;
equal_nibble Nibble7 Nibble5 = False;
equal_nibble Nibble5 Nibble6 = False;
equal_nibble Nibble6 Nibble5 = False;
equal_nibble Nibble4 NibbleF = False;
equal_nibble NibbleF Nibble4 = False;
equal_nibble Nibble4 NibbleE = False;
equal_nibble NibbleE Nibble4 = False;
equal_nibble Nibble4 NibbleD = False;
equal_nibble NibbleD Nibble4 = False;
equal_nibble Nibble4 NibbleC = False;
equal_nibble NibbleC Nibble4 = False;
equal_nibble Nibble4 NibbleB = False;
equal_nibble NibbleB Nibble4 = False;
equal_nibble Nibble4 NibbleA = False;
equal_nibble NibbleA Nibble4 = False;
equal_nibble Nibble4 Nibble9 = False;
equal_nibble Nibble9 Nibble4 = False;
equal_nibble Nibble4 Nibble8 = False;
equal_nibble Nibble8 Nibble4 = False;
equal_nibble Nibble4 Nibble7 = False;
equal_nibble Nibble7 Nibble4 = False;
equal_nibble Nibble4 Nibble6 = False;
equal_nibble Nibble6 Nibble4 = False;
equal_nibble Nibble4 Nibble5 = False;
equal_nibble Nibble5 Nibble4 = False;
equal_nibble Nibble3 NibbleF = False;
equal_nibble NibbleF Nibble3 = False;
equal_nibble Nibble3 NibbleE = False;
equal_nibble NibbleE Nibble3 = False;
equal_nibble Nibble3 NibbleD = False;
equal_nibble NibbleD Nibble3 = False;
equal_nibble Nibble3 NibbleC = False;
equal_nibble NibbleC Nibble3 = False;
equal_nibble Nibble3 NibbleB = False;
equal_nibble NibbleB Nibble3 = False;
equal_nibble Nibble3 NibbleA = False;
equal_nibble NibbleA Nibble3 = False;
equal_nibble Nibble3 Nibble9 = False;
equal_nibble Nibble9 Nibble3 = False;
equal_nibble Nibble3 Nibble8 = False;
equal_nibble Nibble8 Nibble3 = False;
equal_nibble Nibble3 Nibble7 = False;
equal_nibble Nibble7 Nibble3 = False;
equal_nibble Nibble3 Nibble6 = False;
equal_nibble Nibble6 Nibble3 = False;
equal_nibble Nibble3 Nibble5 = False;
equal_nibble Nibble5 Nibble3 = False;
equal_nibble Nibble3 Nibble4 = False;
equal_nibble Nibble4 Nibble3 = False;
equal_nibble Nibble2 NibbleF = False;
equal_nibble NibbleF Nibble2 = False;
equal_nibble Nibble2 NibbleE = False;
equal_nibble NibbleE Nibble2 = False;
equal_nibble Nibble2 NibbleD = False;
equal_nibble NibbleD Nibble2 = False;
equal_nibble Nibble2 NibbleC = False;
equal_nibble NibbleC Nibble2 = False;
equal_nibble Nibble2 NibbleB = False;
equal_nibble NibbleB Nibble2 = False;
equal_nibble Nibble2 NibbleA = False;
equal_nibble NibbleA Nibble2 = False;
equal_nibble Nibble2 Nibble9 = False;
equal_nibble Nibble9 Nibble2 = False;
equal_nibble Nibble2 Nibble8 = False;
equal_nibble Nibble8 Nibble2 = False;
equal_nibble Nibble2 Nibble7 = False;
equal_nibble Nibble7 Nibble2 = False;
equal_nibble Nibble2 Nibble6 = False;
equal_nibble Nibble6 Nibble2 = False;
equal_nibble Nibble2 Nibble5 = False;
equal_nibble Nibble5 Nibble2 = False;
equal_nibble Nibble2 Nibble4 = False;
equal_nibble Nibble4 Nibble2 = False;
equal_nibble Nibble2 Nibble3 = False;
equal_nibble Nibble3 Nibble2 = False;
equal_nibble Nibble1 NibbleF = False;
equal_nibble NibbleF Nibble1 = False;
equal_nibble Nibble1 NibbleE = False;
equal_nibble NibbleE Nibble1 = False;
equal_nibble Nibble1 NibbleD = False;
equal_nibble NibbleD Nibble1 = False;
equal_nibble Nibble1 NibbleC = False;
equal_nibble NibbleC Nibble1 = False;
equal_nibble Nibble1 NibbleB = False;
equal_nibble NibbleB Nibble1 = False;
equal_nibble Nibble1 NibbleA = False;
equal_nibble NibbleA Nibble1 = False;
equal_nibble Nibble1 Nibble9 = False;
equal_nibble Nibble9 Nibble1 = False;
equal_nibble Nibble1 Nibble8 = False;
equal_nibble Nibble8 Nibble1 = False;
equal_nibble Nibble1 Nibble7 = False;
equal_nibble Nibble7 Nibble1 = False;
equal_nibble Nibble1 Nibble6 = False;
equal_nibble Nibble6 Nibble1 = False;
equal_nibble Nibble1 Nibble5 = False;
equal_nibble Nibble5 Nibble1 = False;
equal_nibble Nibble1 Nibble4 = False;
equal_nibble Nibble4 Nibble1 = False;
equal_nibble Nibble1 Nibble3 = False;
equal_nibble Nibble3 Nibble1 = False;
equal_nibble Nibble1 Nibble2 = False;
equal_nibble Nibble2 Nibble1 = False;
equal_nibble Nibble0 NibbleF = False;
equal_nibble NibbleF Nibble0 = False;
equal_nibble Nibble0 NibbleE = False;
equal_nibble NibbleE Nibble0 = False;
equal_nibble Nibble0 NibbleD = False;
equal_nibble NibbleD Nibble0 = False;
equal_nibble Nibble0 NibbleC = False;
equal_nibble NibbleC Nibble0 = False;
equal_nibble Nibble0 NibbleB = False;
equal_nibble NibbleB Nibble0 = False;
equal_nibble Nibble0 NibbleA = False;
equal_nibble NibbleA Nibble0 = False;
equal_nibble Nibble0 Nibble9 = False;
equal_nibble Nibble9 Nibble0 = False;
equal_nibble Nibble0 Nibble8 = False;
equal_nibble Nibble8 Nibble0 = False;
equal_nibble Nibble0 Nibble7 = False;
equal_nibble Nibble7 Nibble0 = False;
equal_nibble Nibble0 Nibble6 = False;
equal_nibble Nibble6 Nibble0 = False;
equal_nibble Nibble0 Nibble5 = False;
equal_nibble Nibble5 Nibble0 = False;
equal_nibble Nibble0 Nibble4 = False;
equal_nibble Nibble4 Nibble0 = False;
equal_nibble Nibble0 Nibble3 = False;
equal_nibble Nibble3 Nibble0 = False;
equal_nibble Nibble0 Nibble2 = False;
equal_nibble Nibble2 Nibble0 = False;
equal_nibble Nibble0 Nibble1 = False;
equal_nibble Nibble1 Nibble0 = False;
equal_nibble NibbleF NibbleF = True;
equal_nibble NibbleE NibbleE = True;
equal_nibble NibbleD NibbleD = True;
equal_nibble NibbleC NibbleC = True;
equal_nibble NibbleB NibbleB = True;
equal_nibble NibbleA NibbleA = True;
equal_nibble Nibble9 Nibble9 = True;
equal_nibble Nibble8 Nibble8 = True;
equal_nibble Nibble7 Nibble7 = True;
equal_nibble Nibble6 Nibble6 = True;
equal_nibble Nibble5 Nibble5 = True;
equal_nibble Nibble4 Nibble4 = True;
equal_nibble Nibble3 Nibble3 = True;
equal_nibble Nibble2 Nibble2 = True;
equal_nibble Nibble1 Nibble1 = True;
equal_nibble Nibble0 Nibble0 = True;

data Char = Char Nibble Nibble;

equal_char :: Char -> Char -> Bool;
equal_char (Char x1 x2) (Char y1 y2) = equal_nibble x1 y1 && equal_nibble x2 y2;

instance Eq Char where {
  a == b = equal_char a b;
};

data Typerepa = Typerep String [Typerepa];

data Itself a = Type;

typerep_char :: Itself Char -> Typerepa;
typerep_char t = Typerep "String.char" [];

class Typerep a where {
  typerep :: Itself a -> Typerepa;
};

instance Typerep Char where {
  typerep = typerep_char;
};

data Terma = Consta String Typerepa | Appa Terma Terma
  | Abs String Typerepa Terma | Free String Typerepa;

term_of_nibble :: Nibble -> Terma;
term_of_nibble NibbleF =
  Consta "String.nibble.NibbleF" (Typerep "String.nibble" []);
term_of_nibble NibbleE =
  Consta "String.nibble.NibbleE" (Typerep "String.nibble" []);
term_of_nibble NibbleD =
  Consta "String.nibble.NibbleD" (Typerep "String.nibble" []);
term_of_nibble NibbleC =
  Consta "String.nibble.NibbleC" (Typerep "String.nibble" []);
term_of_nibble NibbleB =
  Consta "String.nibble.NibbleB" (Typerep "String.nibble" []);
term_of_nibble NibbleA =
  Consta "String.nibble.NibbleA" (Typerep "String.nibble" []);
term_of_nibble Nibble9 =
  Consta "String.nibble.Nibble9" (Typerep "String.nibble" []);
term_of_nibble Nibble8 =
  Consta "String.nibble.Nibble8" (Typerep "String.nibble" []);
term_of_nibble Nibble7 =
  Consta "String.nibble.Nibble7" (Typerep "String.nibble" []);
term_of_nibble Nibble6 =
  Consta "String.nibble.Nibble6" (Typerep "String.nibble" []);
term_of_nibble Nibble5 =
  Consta "String.nibble.Nibble5" (Typerep "String.nibble" []);
term_of_nibble Nibble4 =
  Consta "String.nibble.Nibble4" (Typerep "String.nibble" []);
term_of_nibble Nibble3 =
  Consta "String.nibble.Nibble3" (Typerep "String.nibble" []);
term_of_nibble Nibble2 =
  Consta "String.nibble.Nibble2" (Typerep "String.nibble" []);
term_of_nibble Nibble1 =
  Consta "String.nibble.Nibble1" (Typerep "String.nibble" []);
term_of_nibble Nibble0 =
  Consta "String.nibble.Nibble0" (Typerep "String.nibble" []);

data Nat = Zero_nat | Suc Nat;

minus_nata :: Nat -> Nat -> Nat;
minus_nata (Suc m) (Suc n) = minus_nata m n;
minus_nata Zero_nat n = Zero_nat;
minus_nata m Zero_nat = m;

equal_nat :: Nat -> Nat -> Bool;
equal_nat Zero_nat (Suc x2) = False;
equal_nat (Suc x2) Zero_nat = False;
equal_nat (Suc x2) (Suc y2) = equal_nat x2 y2;
equal_nat Zero_nat Zero_nat = True;

less_nata :: Nat -> Nat -> Bool;
less_nata m (Suc n) = less_eq_nata m n;
less_nata n Zero_nat = False;

less_eq_nata :: Nat -> Nat -> Bool;
less_eq_nata (Suc m) n = less_nata m n;
less_eq_nata Zero_nat n = True;

divmod_nat :: Nat -> Nat -> (Nat, Nat);
divmod_nat m n =
  (if equal_nat n Zero_nat || less_nata m n then (Zero_nat, m)
    else let {
           a = divmod_nat (minus_nata m n) n;
           (q, aa) = a;
         } in (Suc q, aa));

div_nat :: Nat -> Nat -> Nat;
div_nat m n = fst (divmod_nat m n);

enum_nibble :: [Nibble];
enum_nibble =
  [Nibble0, Nibble1, Nibble2, Nibble3, Nibble4, Nibble5, Nibble6, Nibble7,
    Nibble8, Nibble9, NibbleA, NibbleB, NibbleC, NibbleD, NibbleE, NibbleF];

mod_nata :: Nat -> Nat -> Nat;
mod_nata m n = snd (divmod_nat m n);

plus_nat :: Nat -> Nat -> Nat;
plus_nat (Suc m) n = plus_nat m (Suc n);
plus_nat Zero_nat n = n;

one_nat :: Nat;
one_nat = Suc Zero_nat;

nat_of_num :: Num -> Nat;
nat_of_num (Bit1 n) = let {
                        m = nat_of_num n;
                      } in Suc (plus_nat m m);
nat_of_num (Bit0 n) = let {
                        m = nat_of_num n;
                      } in plus_nat m m;
nat_of_num One = one_nat;

nth :: forall a. [a] -> Nat -> a;
nth (x : xs) (Suc n) = nth xs n;
nth (x : xs) Zero_nat = x;

nibble_of_nat :: Nat -> Nibble;
nibble_of_nat n =
  nth enum_nibble (mod_nata n (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 One))))));

nat_of_char :: Char -> Nat;
nat_of_char (Char NibbleF NibbleF) =
  nat_of_num (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 One)))))));
nat_of_char (Char NibbleF NibbleE) =
  nat_of_num (Bit0 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 One)))))));
nat_of_char (Char NibbleF NibbleD) =
  nat_of_num (Bit1 (Bit0 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 One)))))));
nat_of_char (Char NibbleF NibbleC) =
  nat_of_num (Bit0 (Bit0 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 One)))))));
nat_of_char (Char NibbleF NibbleB) =
  nat_of_num (Bit1 (Bit1 (Bit0 (Bit1 (Bit1 (Bit1 (Bit1 One)))))));
nat_of_char (Char NibbleF NibbleA) =
  nat_of_num (Bit0 (Bit1 (Bit0 (Bit1 (Bit1 (Bit1 (Bit1 One)))))));
nat_of_char (Char NibbleF Nibble9) =
  nat_of_num (Bit1 (Bit0 (Bit0 (Bit1 (Bit1 (Bit1 (Bit1 One)))))));
nat_of_char (Char NibbleF Nibble8) =
  nat_of_num (Bit0 (Bit0 (Bit0 (Bit1 (Bit1 (Bit1 (Bit1 One)))))));
nat_of_char (Char NibbleF Nibble7) =
  nat_of_num (Bit1 (Bit1 (Bit1 (Bit0 (Bit1 (Bit1 (Bit1 One)))))));
nat_of_char (Char NibbleF Nibble6) =
  nat_of_num (Bit0 (Bit1 (Bit1 (Bit0 (Bit1 (Bit1 (Bit1 One)))))));
nat_of_char (Char NibbleF Nibble5) =
  nat_of_num (Bit1 (Bit0 (Bit1 (Bit0 (Bit1 (Bit1 (Bit1 One)))))));
nat_of_char (Char NibbleF Nibble4) =
  nat_of_num (Bit0 (Bit0 (Bit1 (Bit0 (Bit1 (Bit1 (Bit1 One)))))));
nat_of_char (Char NibbleF Nibble3) =
  nat_of_num (Bit1 (Bit1 (Bit0 (Bit0 (Bit1 (Bit1 (Bit1 One)))))));
nat_of_char (Char NibbleF Nibble2) =
  nat_of_num (Bit0 (Bit1 (Bit0 (Bit0 (Bit1 (Bit1 (Bit1 One)))))));
nat_of_char (Char NibbleF Nibble1) =
  nat_of_num (Bit1 (Bit0 (Bit0 (Bit0 (Bit1 (Bit1 (Bit1 One)))))));
nat_of_char (Char NibbleF Nibble0) =
  nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit1 (Bit1 (Bit1 One)))))));
nat_of_char (Char NibbleE NibbleF) =
  nat_of_num (Bit1 (Bit1 (Bit1 (Bit1 (Bit0 (Bit1 (Bit1 One)))))));
nat_of_char (Char NibbleE NibbleE) =
  nat_of_num (Bit0 (Bit1 (Bit1 (Bit1 (Bit0 (Bit1 (Bit1 One)))))));
nat_of_char (Char NibbleE NibbleD) =
  nat_of_num (Bit1 (Bit0 (Bit1 (Bit1 (Bit0 (Bit1 (Bit1 One)))))));
nat_of_char (Char NibbleE NibbleC) =
  nat_of_num (Bit0 (Bit0 (Bit1 (Bit1 (Bit0 (Bit1 (Bit1 One)))))));
nat_of_char (Char NibbleE NibbleB) =
  nat_of_num (Bit1 (Bit1 (Bit0 (Bit1 (Bit0 (Bit1 (Bit1 One)))))));
nat_of_char (Char NibbleE NibbleA) =
  nat_of_num (Bit0 (Bit1 (Bit0 (Bit1 (Bit0 (Bit1 (Bit1 One)))))));
nat_of_char (Char NibbleE Nibble9) =
  nat_of_num (Bit1 (Bit0 (Bit0 (Bit1 (Bit0 (Bit1 (Bit1 One)))))));
nat_of_char (Char NibbleE Nibble8) =
  nat_of_num (Bit0 (Bit0 (Bit0 (Bit1 (Bit0 (Bit1 (Bit1 One)))))));
nat_of_char (Char NibbleE Nibble7) =
  nat_of_num (Bit1 (Bit1 (Bit1 (Bit0 (Bit0 (Bit1 (Bit1 One)))))));
nat_of_char (Char NibbleE Nibble6) =
  nat_of_num (Bit0 (Bit1 (Bit1 (Bit0 (Bit0 (Bit1 (Bit1 One)))))));
nat_of_char (Char NibbleE Nibble5) =
  nat_of_num (Bit1 (Bit0 (Bit1 (Bit0 (Bit0 (Bit1 (Bit1 One)))))));
nat_of_char (Char NibbleE Nibble4) =
  nat_of_num (Bit0 (Bit0 (Bit1 (Bit0 (Bit0 (Bit1 (Bit1 One)))))));
nat_of_char (Char NibbleE Nibble3) =
  nat_of_num (Bit1 (Bit1 (Bit0 (Bit0 (Bit0 (Bit1 (Bit1 One)))))));
nat_of_char (Char NibbleE Nibble2) =
  nat_of_num (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 (Bit1 (Bit1 One)))))));
nat_of_char (Char NibbleE Nibble1) =
  nat_of_num (Bit1 (Bit0 (Bit0 (Bit0 (Bit0 (Bit1 (Bit1 One)))))));
nat_of_char (Char NibbleE Nibble0) =
  nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit1 (Bit1 One)))))));
nat_of_char (Char NibbleD NibbleF) =
  nat_of_num (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit0 (Bit1 One)))))));
nat_of_char (Char NibbleD NibbleE) =
  nat_of_num (Bit0 (Bit1 (Bit1 (Bit1 (Bit1 (Bit0 (Bit1 One)))))));
nat_of_char (Char NibbleD NibbleD) =
  nat_of_num (Bit1 (Bit0 (Bit1 (Bit1 (Bit1 (Bit0 (Bit1 One)))))));
nat_of_char (Char NibbleD NibbleC) =
  nat_of_num (Bit0 (Bit0 (Bit1 (Bit1 (Bit1 (Bit0 (Bit1 One)))))));
nat_of_char (Char NibbleD NibbleB) =
  nat_of_num (Bit1 (Bit1 (Bit0 (Bit1 (Bit1 (Bit0 (Bit1 One)))))));
nat_of_char (Char NibbleD NibbleA) =
  nat_of_num (Bit0 (Bit1 (Bit0 (Bit1 (Bit1 (Bit0 (Bit1 One)))))));
nat_of_char (Char NibbleD Nibble9) =
  nat_of_num (Bit1 (Bit0 (Bit0 (Bit1 (Bit1 (Bit0 (Bit1 One)))))));
nat_of_char (Char NibbleD Nibble8) =
  nat_of_num (Bit0 (Bit0 (Bit0 (Bit1 (Bit1 (Bit0 (Bit1 One)))))));
nat_of_char (Char NibbleD Nibble7) =
  nat_of_num (Bit1 (Bit1 (Bit1 (Bit0 (Bit1 (Bit0 (Bit1 One)))))));
nat_of_char (Char NibbleD Nibble6) =
  nat_of_num (Bit0 (Bit1 (Bit1 (Bit0 (Bit1 (Bit0 (Bit1 One)))))));
nat_of_char (Char NibbleD Nibble5) =
  nat_of_num (Bit1 (Bit0 (Bit1 (Bit0 (Bit1 (Bit0 (Bit1 One)))))));
nat_of_char (Char NibbleD Nibble4) =
  nat_of_num (Bit0 (Bit0 (Bit1 (Bit0 (Bit1 (Bit0 (Bit1 One)))))));
nat_of_char (Char NibbleD Nibble3) =
  nat_of_num (Bit1 (Bit1 (Bit0 (Bit0 (Bit1 (Bit0 (Bit1 One)))))));
nat_of_char (Char NibbleD Nibble2) =
  nat_of_num (Bit0 (Bit1 (Bit0 (Bit0 (Bit1 (Bit0 (Bit1 One)))))));
nat_of_char (Char NibbleD Nibble1) =
  nat_of_num (Bit1 (Bit0 (Bit0 (Bit0 (Bit1 (Bit0 (Bit1 One)))))));
nat_of_char (Char NibbleD Nibble0) =
  nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit1 (Bit0 (Bit1 One)))))));
nat_of_char (Char NibbleC NibbleF) =
  nat_of_num (Bit1 (Bit1 (Bit1 (Bit1 (Bit0 (Bit0 (Bit1 One)))))));
nat_of_char (Char NibbleC NibbleE) =
  nat_of_num (Bit0 (Bit1 (Bit1 (Bit1 (Bit0 (Bit0 (Bit1 One)))))));
nat_of_char (Char NibbleC NibbleD) =
  nat_of_num (Bit1 (Bit0 (Bit1 (Bit1 (Bit0 (Bit0 (Bit1 One)))))));
nat_of_char (Char NibbleC NibbleC) =
  nat_of_num (Bit0 (Bit0 (Bit1 (Bit1 (Bit0 (Bit0 (Bit1 One)))))));
nat_of_char (Char NibbleC NibbleB) =
  nat_of_num (Bit1 (Bit1 (Bit0 (Bit1 (Bit0 (Bit0 (Bit1 One)))))));
nat_of_char (Char NibbleC NibbleA) =
  nat_of_num (Bit0 (Bit1 (Bit0 (Bit1 (Bit0 (Bit0 (Bit1 One)))))));
nat_of_char (Char NibbleC Nibble9) =
  nat_of_num (Bit1 (Bit0 (Bit0 (Bit1 (Bit0 (Bit0 (Bit1 One)))))));
nat_of_char (Char NibbleC Nibble8) =
  nat_of_num (Bit0 (Bit0 (Bit0 (Bit1 (Bit0 (Bit0 (Bit1 One)))))));
nat_of_char (Char NibbleC Nibble7) =
  nat_of_num (Bit1 (Bit1 (Bit1 (Bit0 (Bit0 (Bit0 (Bit1 One)))))));
nat_of_char (Char NibbleC Nibble6) =
  nat_of_num (Bit0 (Bit1 (Bit1 (Bit0 (Bit0 (Bit0 (Bit1 One)))))));
nat_of_char (Char NibbleC Nibble5) =
  nat_of_num (Bit1 (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 (Bit1 One)))))));
nat_of_char (Char NibbleC Nibble4) =
  nat_of_num (Bit0 (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 (Bit1 One)))))));
nat_of_char (Char NibbleC Nibble3) =
  nat_of_num (Bit1 (Bit1 (Bit0 (Bit0 (Bit0 (Bit0 (Bit1 One)))))));
nat_of_char (Char NibbleC Nibble2) =
  nat_of_num (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 (Bit0 (Bit1 One)))))));
nat_of_char (Char NibbleC Nibble1) =
  nat_of_num (Bit1 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit1 One)))))));
nat_of_char (Char NibbleC Nibble0) =
  nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit1 One)))))));
nat_of_char (Char NibbleB NibbleF) =
  nat_of_num (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit0 One)))))));
nat_of_char (Char NibbleB NibbleE) =
  nat_of_num (Bit0 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit0 One)))))));
nat_of_char (Char NibbleB NibbleD) =
  nat_of_num (Bit1 (Bit0 (Bit1 (Bit1 (Bit1 (Bit1 (Bit0 One)))))));
nat_of_char (Char NibbleB NibbleC) =
  nat_of_num (Bit0 (Bit0 (Bit1 (Bit1 (Bit1 (Bit1 (Bit0 One)))))));
nat_of_char (Char NibbleB NibbleB) =
  nat_of_num (Bit1 (Bit1 (Bit0 (Bit1 (Bit1 (Bit1 (Bit0 One)))))));
nat_of_char (Char NibbleB NibbleA) =
  nat_of_num (Bit0 (Bit1 (Bit0 (Bit1 (Bit1 (Bit1 (Bit0 One)))))));
nat_of_char (Char NibbleB Nibble9) =
  nat_of_num (Bit1 (Bit0 (Bit0 (Bit1 (Bit1 (Bit1 (Bit0 One)))))));
nat_of_char (Char NibbleB Nibble8) =
  nat_of_num (Bit0 (Bit0 (Bit0 (Bit1 (Bit1 (Bit1 (Bit0 One)))))));
nat_of_char (Char NibbleB Nibble7) =
  nat_of_num (Bit1 (Bit1 (Bit1 (Bit0 (Bit1 (Bit1 (Bit0 One)))))));
nat_of_char (Char NibbleB Nibble6) =
  nat_of_num (Bit0 (Bit1 (Bit1 (Bit0 (Bit1 (Bit1 (Bit0 One)))))));
nat_of_char (Char NibbleB Nibble5) =
  nat_of_num (Bit1 (Bit0 (Bit1 (Bit0 (Bit1 (Bit1 (Bit0 One)))))));
nat_of_char (Char NibbleB Nibble4) =
  nat_of_num (Bit0 (Bit0 (Bit1 (Bit0 (Bit1 (Bit1 (Bit0 One)))))));
nat_of_char (Char NibbleB Nibble3) =
  nat_of_num (Bit1 (Bit1 (Bit0 (Bit0 (Bit1 (Bit1 (Bit0 One)))))));
nat_of_char (Char NibbleB Nibble2) =
  nat_of_num (Bit0 (Bit1 (Bit0 (Bit0 (Bit1 (Bit1 (Bit0 One)))))));
nat_of_char (Char NibbleB Nibble1) =
  nat_of_num (Bit1 (Bit0 (Bit0 (Bit0 (Bit1 (Bit1 (Bit0 One)))))));
nat_of_char (Char NibbleB Nibble0) =
  nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit1 (Bit1 (Bit0 One)))))));
nat_of_char (Char NibbleA NibbleF) =
  nat_of_num (Bit1 (Bit1 (Bit1 (Bit1 (Bit0 (Bit1 (Bit0 One)))))));
nat_of_char (Char NibbleA NibbleE) =
  nat_of_num (Bit0 (Bit1 (Bit1 (Bit1 (Bit0 (Bit1 (Bit0 One)))))));
nat_of_char (Char NibbleA NibbleD) =
  nat_of_num (Bit1 (Bit0 (Bit1 (Bit1 (Bit0 (Bit1 (Bit0 One)))))));
nat_of_char (Char NibbleA NibbleC) =
  nat_of_num (Bit0 (Bit0 (Bit1 (Bit1 (Bit0 (Bit1 (Bit0 One)))))));
nat_of_char (Char NibbleA NibbleB) =
  nat_of_num (Bit1 (Bit1 (Bit0 (Bit1 (Bit0 (Bit1 (Bit0 One)))))));
nat_of_char (Char NibbleA NibbleA) =
  nat_of_num (Bit0 (Bit1 (Bit0 (Bit1 (Bit0 (Bit1 (Bit0 One)))))));
nat_of_char (Char NibbleA Nibble9) =
  nat_of_num (Bit1 (Bit0 (Bit0 (Bit1 (Bit0 (Bit1 (Bit0 One)))))));
nat_of_char (Char NibbleA Nibble8) =
  nat_of_num (Bit0 (Bit0 (Bit0 (Bit1 (Bit0 (Bit1 (Bit0 One)))))));
nat_of_char (Char NibbleA Nibble7) =
  nat_of_num (Bit1 (Bit1 (Bit1 (Bit0 (Bit0 (Bit1 (Bit0 One)))))));
nat_of_char (Char NibbleA Nibble6) =
  nat_of_num (Bit0 (Bit1 (Bit1 (Bit0 (Bit0 (Bit1 (Bit0 One)))))));
nat_of_char (Char NibbleA Nibble5) =
  nat_of_num (Bit1 (Bit0 (Bit1 (Bit0 (Bit0 (Bit1 (Bit0 One)))))));
nat_of_char (Char NibbleA Nibble4) =
  nat_of_num (Bit0 (Bit0 (Bit1 (Bit0 (Bit0 (Bit1 (Bit0 One)))))));
nat_of_char (Char NibbleA Nibble3) =
  nat_of_num (Bit1 (Bit1 (Bit0 (Bit0 (Bit0 (Bit1 (Bit0 One)))))));
nat_of_char (Char NibbleA Nibble2) =
  nat_of_num (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 (Bit1 (Bit0 One)))))));
nat_of_char (Char NibbleA Nibble1) =
  nat_of_num (Bit1 (Bit0 (Bit0 (Bit0 (Bit0 (Bit1 (Bit0 One)))))));
nat_of_char (Char NibbleA Nibble0) =
  nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit1 (Bit0 One)))))));
nat_of_char (Char Nibble9 NibbleF) =
  nat_of_num (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit0 (Bit0 One)))))));
nat_of_char (Char Nibble9 NibbleE) =
  nat_of_num (Bit0 (Bit1 (Bit1 (Bit1 (Bit1 (Bit0 (Bit0 One)))))));
nat_of_char (Char Nibble9 NibbleD) =
  nat_of_num (Bit1 (Bit0 (Bit1 (Bit1 (Bit1 (Bit0 (Bit0 One)))))));
nat_of_char (Char Nibble9 NibbleC) =
  nat_of_num (Bit0 (Bit0 (Bit1 (Bit1 (Bit1 (Bit0 (Bit0 One)))))));
nat_of_char (Char Nibble9 NibbleB) =
  nat_of_num (Bit1 (Bit1 (Bit0 (Bit1 (Bit1 (Bit0 (Bit0 One)))))));
nat_of_char (Char Nibble9 NibbleA) =
  nat_of_num (Bit0 (Bit1 (Bit0 (Bit1 (Bit1 (Bit0 (Bit0 One)))))));
nat_of_char (Char Nibble9 Nibble9) =
  nat_of_num (Bit1 (Bit0 (Bit0 (Bit1 (Bit1 (Bit0 (Bit0 One)))))));
nat_of_char (Char Nibble9 Nibble8) =
  nat_of_num (Bit0 (Bit0 (Bit0 (Bit1 (Bit1 (Bit0 (Bit0 One)))))));
nat_of_char (Char Nibble9 Nibble7) =
  nat_of_num (Bit1 (Bit1 (Bit1 (Bit0 (Bit1 (Bit0 (Bit0 One)))))));
nat_of_char (Char Nibble9 Nibble6) =
  nat_of_num (Bit0 (Bit1 (Bit1 (Bit0 (Bit1 (Bit0 (Bit0 One)))))));
nat_of_char (Char Nibble9 Nibble5) =
  nat_of_num (Bit1 (Bit0 (Bit1 (Bit0 (Bit1 (Bit0 (Bit0 One)))))));
nat_of_char (Char Nibble9 Nibble4) =
  nat_of_num (Bit0 (Bit0 (Bit1 (Bit0 (Bit1 (Bit0 (Bit0 One)))))));
nat_of_char (Char Nibble9 Nibble3) =
  nat_of_num (Bit1 (Bit1 (Bit0 (Bit0 (Bit1 (Bit0 (Bit0 One)))))));
nat_of_char (Char Nibble9 Nibble2) =
  nat_of_num (Bit0 (Bit1 (Bit0 (Bit0 (Bit1 (Bit0 (Bit0 One)))))));
nat_of_char (Char Nibble9 Nibble1) =
  nat_of_num (Bit1 (Bit0 (Bit0 (Bit0 (Bit1 (Bit0 (Bit0 One)))))));
nat_of_char (Char Nibble9 Nibble0) =
  nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit1 (Bit0 (Bit0 One)))))));
nat_of_char (Char Nibble8 NibbleF) =
  nat_of_num (Bit1 (Bit1 (Bit1 (Bit1 (Bit0 (Bit0 (Bit0 One)))))));
nat_of_char (Char Nibble8 NibbleE) =
  nat_of_num (Bit0 (Bit1 (Bit1 (Bit1 (Bit0 (Bit0 (Bit0 One)))))));
nat_of_char (Char Nibble8 NibbleD) =
  nat_of_num (Bit1 (Bit0 (Bit1 (Bit1 (Bit0 (Bit0 (Bit0 One)))))));
nat_of_char (Char Nibble8 NibbleC) =
  nat_of_num (Bit0 (Bit0 (Bit1 (Bit1 (Bit0 (Bit0 (Bit0 One)))))));
nat_of_char (Char Nibble8 NibbleB) =
  nat_of_num (Bit1 (Bit1 (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 One)))))));
nat_of_char (Char Nibble8 NibbleA) =
  nat_of_num (Bit0 (Bit1 (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 One)))))));
nat_of_char (Char Nibble8 Nibble9) =
  nat_of_num (Bit1 (Bit0 (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 One)))))));
nat_of_char (Char Nibble8 Nibble8) =
  nat_of_num (Bit0 (Bit0 (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 One)))))));
nat_of_char (Char Nibble8 Nibble7) =
  nat_of_num (Bit1 (Bit1 (Bit1 (Bit0 (Bit0 (Bit0 (Bit0 One)))))));
nat_of_char (Char Nibble8 Nibble6) =
  nat_of_num (Bit0 (Bit1 (Bit1 (Bit0 (Bit0 (Bit0 (Bit0 One)))))));
nat_of_char (Char Nibble8 Nibble5) =
  nat_of_num (Bit1 (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 (Bit0 One)))))));
nat_of_char (Char Nibble8 Nibble4) =
  nat_of_num (Bit0 (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 (Bit0 One)))))));
nat_of_char (Char Nibble8 Nibble3) =
  nat_of_num (Bit1 (Bit1 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One)))))));
nat_of_char (Char Nibble8 Nibble2) =
  nat_of_num (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One)))))));
nat_of_char (Char Nibble8 Nibble1) =
  nat_of_num (Bit1 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One)))))));
nat_of_char (Char Nibble8 Nibble0) =
  nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One)))))));
nat_of_char (Char Nibble7 NibbleF) =
  nat_of_num (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 One))))));
nat_of_char (Char Nibble7 NibbleE) =
  nat_of_num (Bit0 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 One))))));
nat_of_char (Char Nibble7 NibbleD) =
  nat_of_num (Bit1 (Bit0 (Bit1 (Bit1 (Bit1 (Bit1 One))))));
nat_of_char (Char Nibble7 NibbleC) =
  nat_of_num (Bit0 (Bit0 (Bit1 (Bit1 (Bit1 (Bit1 One))))));
nat_of_char (Char Nibble7 NibbleB) =
  nat_of_num (Bit1 (Bit1 (Bit0 (Bit1 (Bit1 (Bit1 One))))));
nat_of_char (Char Nibble7 NibbleA) =
  nat_of_num (Bit0 (Bit1 (Bit0 (Bit1 (Bit1 (Bit1 One))))));
nat_of_char (Char Nibble7 Nibble9) =
  nat_of_num (Bit1 (Bit0 (Bit0 (Bit1 (Bit1 (Bit1 One))))));
nat_of_char (Char Nibble7 Nibble8) =
  nat_of_num (Bit0 (Bit0 (Bit0 (Bit1 (Bit1 (Bit1 One))))));
nat_of_char (Char Nibble7 Nibble7) =
  nat_of_num (Bit1 (Bit1 (Bit1 (Bit0 (Bit1 (Bit1 One))))));
nat_of_char (Char Nibble7 Nibble6) =
  nat_of_num (Bit0 (Bit1 (Bit1 (Bit0 (Bit1 (Bit1 One))))));
nat_of_char (Char Nibble7 Nibble5) =
  nat_of_num (Bit1 (Bit0 (Bit1 (Bit0 (Bit1 (Bit1 One))))));
nat_of_char (Char Nibble7 Nibble4) =
  nat_of_num (Bit0 (Bit0 (Bit1 (Bit0 (Bit1 (Bit1 One))))));
nat_of_char (Char Nibble7 Nibble3) =
  nat_of_num (Bit1 (Bit1 (Bit0 (Bit0 (Bit1 (Bit1 One))))));
nat_of_char (Char Nibble7 Nibble2) =
  nat_of_num (Bit0 (Bit1 (Bit0 (Bit0 (Bit1 (Bit1 One))))));
nat_of_char (Char Nibble7 Nibble1) =
  nat_of_num (Bit1 (Bit0 (Bit0 (Bit0 (Bit1 (Bit1 One))))));
nat_of_char (Char Nibble7 Nibble0) =
  nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit1 (Bit1 One))))));
nat_of_char (Char Nibble6 NibbleF) =
  nat_of_num (Bit1 (Bit1 (Bit1 (Bit1 (Bit0 (Bit1 One))))));
nat_of_char (Char Nibble6 NibbleE) =
  nat_of_num (Bit0 (Bit1 (Bit1 (Bit1 (Bit0 (Bit1 One))))));
nat_of_char (Char Nibble6 NibbleD) =
  nat_of_num (Bit1 (Bit0 (Bit1 (Bit1 (Bit0 (Bit1 One))))));
nat_of_char (Char Nibble6 NibbleC) =
  nat_of_num (Bit0 (Bit0 (Bit1 (Bit1 (Bit0 (Bit1 One))))));
nat_of_char (Char Nibble6 NibbleB) =
  nat_of_num (Bit1 (Bit1 (Bit0 (Bit1 (Bit0 (Bit1 One))))));
nat_of_char (Char Nibble6 NibbleA) =
  nat_of_num (Bit0 (Bit1 (Bit0 (Bit1 (Bit0 (Bit1 One))))));
nat_of_char (Char Nibble6 Nibble9) =
  nat_of_num (Bit1 (Bit0 (Bit0 (Bit1 (Bit0 (Bit1 One))))));
nat_of_char (Char Nibble6 Nibble8) =
  nat_of_num (Bit0 (Bit0 (Bit0 (Bit1 (Bit0 (Bit1 One))))));
nat_of_char (Char Nibble6 Nibble7) =
  nat_of_num (Bit1 (Bit1 (Bit1 (Bit0 (Bit0 (Bit1 One))))));
nat_of_char (Char Nibble6 Nibble6) =
  nat_of_num (Bit0 (Bit1 (Bit1 (Bit0 (Bit0 (Bit1 One))))));
nat_of_char (Char Nibble6 Nibble5) =
  nat_of_num (Bit1 (Bit0 (Bit1 (Bit0 (Bit0 (Bit1 One))))));
nat_of_char (Char Nibble6 Nibble4) =
  nat_of_num (Bit0 (Bit0 (Bit1 (Bit0 (Bit0 (Bit1 One))))));
nat_of_char (Char Nibble6 Nibble3) =
  nat_of_num (Bit1 (Bit1 (Bit0 (Bit0 (Bit0 (Bit1 One))))));
nat_of_char (Char Nibble6 Nibble2) =
  nat_of_num (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 (Bit1 One))))));
nat_of_char (Char Nibble6 Nibble1) =
  nat_of_num (Bit1 (Bit0 (Bit0 (Bit0 (Bit0 (Bit1 One))))));
nat_of_char (Char Nibble6 Nibble0) =
  nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit1 One))))));
nat_of_char (Char Nibble5 NibbleF) =
  nat_of_num (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit0 One))))));
nat_of_char (Char Nibble5 NibbleE) =
  nat_of_num (Bit0 (Bit1 (Bit1 (Bit1 (Bit1 (Bit0 One))))));
nat_of_char (Char Nibble5 NibbleD) =
  nat_of_num (Bit1 (Bit0 (Bit1 (Bit1 (Bit1 (Bit0 One))))));
nat_of_char (Char Nibble5 NibbleC) =
  nat_of_num (Bit0 (Bit0 (Bit1 (Bit1 (Bit1 (Bit0 One))))));
nat_of_char (Char Nibble5 NibbleB) =
  nat_of_num (Bit1 (Bit1 (Bit0 (Bit1 (Bit1 (Bit0 One))))));
nat_of_char (Char Nibble5 NibbleA) =
  nat_of_num (Bit0 (Bit1 (Bit0 (Bit1 (Bit1 (Bit0 One))))));
nat_of_char (Char Nibble5 Nibble9) =
  nat_of_num (Bit1 (Bit0 (Bit0 (Bit1 (Bit1 (Bit0 One))))));
nat_of_char (Char Nibble5 Nibble8) =
  nat_of_num (Bit0 (Bit0 (Bit0 (Bit1 (Bit1 (Bit0 One))))));
nat_of_char (Char Nibble5 Nibble7) =
  nat_of_num (Bit1 (Bit1 (Bit1 (Bit0 (Bit1 (Bit0 One))))));
nat_of_char (Char Nibble5 Nibble6) =
  nat_of_num (Bit0 (Bit1 (Bit1 (Bit0 (Bit1 (Bit0 One))))));
nat_of_char (Char Nibble5 Nibble5) =
  nat_of_num (Bit1 (Bit0 (Bit1 (Bit0 (Bit1 (Bit0 One))))));
nat_of_char (Char Nibble5 Nibble4) =
  nat_of_num (Bit0 (Bit0 (Bit1 (Bit0 (Bit1 (Bit0 One))))));
nat_of_char (Char Nibble5 Nibble3) =
  nat_of_num (Bit1 (Bit1 (Bit0 (Bit0 (Bit1 (Bit0 One))))));
nat_of_char (Char Nibble5 Nibble2) =
  nat_of_num (Bit0 (Bit1 (Bit0 (Bit0 (Bit1 (Bit0 One))))));
nat_of_char (Char Nibble5 Nibble1) =
  nat_of_num (Bit1 (Bit0 (Bit0 (Bit0 (Bit1 (Bit0 One))))));
nat_of_char (Char Nibble5 Nibble0) =
  nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit1 (Bit0 One))))));
nat_of_char (Char Nibble4 NibbleF) =
  nat_of_num (Bit1 (Bit1 (Bit1 (Bit1 (Bit0 (Bit0 One))))));
nat_of_char (Char Nibble4 NibbleE) =
  nat_of_num (Bit0 (Bit1 (Bit1 (Bit1 (Bit0 (Bit0 One))))));
nat_of_char (Char Nibble4 NibbleD) =
  nat_of_num (Bit1 (Bit0 (Bit1 (Bit1 (Bit0 (Bit0 One))))));
nat_of_char (Char Nibble4 NibbleC) =
  nat_of_num (Bit0 (Bit0 (Bit1 (Bit1 (Bit0 (Bit0 One))))));
nat_of_char (Char Nibble4 NibbleB) =
  nat_of_num (Bit1 (Bit1 (Bit0 (Bit1 (Bit0 (Bit0 One))))));
nat_of_char (Char Nibble4 NibbleA) =
  nat_of_num (Bit0 (Bit1 (Bit0 (Bit1 (Bit0 (Bit0 One))))));
nat_of_char (Char Nibble4 Nibble9) =
  nat_of_num (Bit1 (Bit0 (Bit0 (Bit1 (Bit0 (Bit0 One))))));
nat_of_char (Char Nibble4 Nibble8) =
  nat_of_num (Bit0 (Bit0 (Bit0 (Bit1 (Bit0 (Bit0 One))))));
nat_of_char (Char Nibble4 Nibble7) =
  nat_of_num (Bit1 (Bit1 (Bit1 (Bit0 (Bit0 (Bit0 One))))));
nat_of_char (Char Nibble4 Nibble6) =
  nat_of_num (Bit0 (Bit1 (Bit1 (Bit0 (Bit0 (Bit0 One))))));
nat_of_char (Char Nibble4 Nibble5) =
  nat_of_num (Bit1 (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 One))))));
nat_of_char (Char Nibble4 Nibble4) =
  nat_of_num (Bit0 (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 One))))));
nat_of_char (Char Nibble4 Nibble3) =
  nat_of_num (Bit1 (Bit1 (Bit0 (Bit0 (Bit0 (Bit0 One))))));
nat_of_char (Char Nibble4 Nibble2) =
  nat_of_num (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 (Bit0 One))))));
nat_of_char (Char Nibble4 Nibble1) =
  nat_of_num (Bit1 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One))))));
nat_of_char (Char Nibble4 Nibble0) =
  nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One))))));
nat_of_char (Char Nibble3 NibbleF) =
  nat_of_num (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 One)))));
nat_of_char (Char Nibble3 NibbleE) =
  nat_of_num (Bit0 (Bit1 (Bit1 (Bit1 (Bit1 One)))));
nat_of_char (Char Nibble3 NibbleD) =
  nat_of_num (Bit1 (Bit0 (Bit1 (Bit1 (Bit1 One)))));
nat_of_char (Char Nibble3 NibbleC) =
  nat_of_num (Bit0 (Bit0 (Bit1 (Bit1 (Bit1 One)))));
nat_of_char (Char Nibble3 NibbleB) =
  nat_of_num (Bit1 (Bit1 (Bit0 (Bit1 (Bit1 One)))));
nat_of_char (Char Nibble3 NibbleA) =
  nat_of_num (Bit0 (Bit1 (Bit0 (Bit1 (Bit1 One)))));
nat_of_char (Char Nibble3 Nibble9) =
  nat_of_num (Bit1 (Bit0 (Bit0 (Bit1 (Bit1 One)))));
nat_of_char (Char Nibble3 Nibble8) =
  nat_of_num (Bit0 (Bit0 (Bit0 (Bit1 (Bit1 One)))));
nat_of_char (Char Nibble3 Nibble7) =
  nat_of_num (Bit1 (Bit1 (Bit1 (Bit0 (Bit1 One)))));
nat_of_char (Char Nibble3 Nibble6) =
  nat_of_num (Bit0 (Bit1 (Bit1 (Bit0 (Bit1 One)))));
nat_of_char (Char Nibble3 Nibble5) =
  nat_of_num (Bit1 (Bit0 (Bit1 (Bit0 (Bit1 One)))));
nat_of_char (Char Nibble3 Nibble4) =
  nat_of_num (Bit0 (Bit0 (Bit1 (Bit0 (Bit1 One)))));
nat_of_char (Char Nibble3 Nibble3) =
  nat_of_num (Bit1 (Bit1 (Bit0 (Bit0 (Bit1 One)))));
nat_of_char (Char Nibble3 Nibble2) =
  nat_of_num (Bit0 (Bit1 (Bit0 (Bit0 (Bit1 One)))));
nat_of_char (Char Nibble3 Nibble1) =
  nat_of_num (Bit1 (Bit0 (Bit0 (Bit0 (Bit1 One)))));
nat_of_char (Char Nibble3 Nibble0) =
  nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit1 One)))));
nat_of_char (Char Nibble2 NibbleF) =
  nat_of_num (Bit1 (Bit1 (Bit1 (Bit1 (Bit0 One)))));
nat_of_char (Char Nibble2 NibbleE) =
  nat_of_num (Bit0 (Bit1 (Bit1 (Bit1 (Bit0 One)))));
nat_of_char (Char Nibble2 NibbleD) =
  nat_of_num (Bit1 (Bit0 (Bit1 (Bit1 (Bit0 One)))));
nat_of_char (Char Nibble2 NibbleC) =
  nat_of_num (Bit0 (Bit0 (Bit1 (Bit1 (Bit0 One)))));
nat_of_char (Char Nibble2 NibbleB) =
  nat_of_num (Bit1 (Bit1 (Bit0 (Bit1 (Bit0 One)))));
nat_of_char (Char Nibble2 NibbleA) =
  nat_of_num (Bit0 (Bit1 (Bit0 (Bit1 (Bit0 One)))));
nat_of_char (Char Nibble2 Nibble9) =
  nat_of_num (Bit1 (Bit0 (Bit0 (Bit1 (Bit0 One)))));
nat_of_char (Char Nibble2 Nibble8) =
  nat_of_num (Bit0 (Bit0 (Bit0 (Bit1 (Bit0 One)))));
nat_of_char (Char Nibble2 Nibble7) =
  nat_of_num (Bit1 (Bit1 (Bit1 (Bit0 (Bit0 One)))));
nat_of_char (Char Nibble2 Nibble6) =
  nat_of_num (Bit0 (Bit1 (Bit1 (Bit0 (Bit0 One)))));
nat_of_char (Char Nibble2 Nibble5) =
  nat_of_num (Bit1 (Bit0 (Bit1 (Bit0 (Bit0 One)))));
nat_of_char (Char Nibble2 Nibble4) =
  nat_of_num (Bit0 (Bit0 (Bit1 (Bit0 (Bit0 One)))));
nat_of_char (Char Nibble2 Nibble3) =
  nat_of_num (Bit1 (Bit1 (Bit0 (Bit0 (Bit0 One)))));
nat_of_char (Char Nibble2 Nibble2) =
  nat_of_num (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 One)))));
nat_of_char (Char Nibble2 Nibble1) =
  nat_of_num (Bit1 (Bit0 (Bit0 (Bit0 (Bit0 One)))));
nat_of_char (Char Nibble2 Nibble0) =
  nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One)))));
nat_of_char (Char Nibble1 NibbleF) = nat_of_num (Bit1 (Bit1 (Bit1 (Bit1 One))));
nat_of_char (Char Nibble1 NibbleE) = nat_of_num (Bit0 (Bit1 (Bit1 (Bit1 One))));
nat_of_char (Char Nibble1 NibbleD) = nat_of_num (Bit1 (Bit0 (Bit1 (Bit1 One))));
nat_of_char (Char Nibble1 NibbleC) = nat_of_num (Bit0 (Bit0 (Bit1 (Bit1 One))));
nat_of_char (Char Nibble1 NibbleB) = nat_of_num (Bit1 (Bit1 (Bit0 (Bit1 One))));
nat_of_char (Char Nibble1 NibbleA) = nat_of_num (Bit0 (Bit1 (Bit0 (Bit1 One))));
nat_of_char (Char Nibble1 Nibble9) = nat_of_num (Bit1 (Bit0 (Bit0 (Bit1 One))));
nat_of_char (Char Nibble1 Nibble8) = nat_of_num (Bit0 (Bit0 (Bit0 (Bit1 One))));
nat_of_char (Char Nibble1 Nibble7) = nat_of_num (Bit1 (Bit1 (Bit1 (Bit0 One))));
nat_of_char (Char Nibble1 Nibble6) = nat_of_num (Bit0 (Bit1 (Bit1 (Bit0 One))));
nat_of_char (Char Nibble1 Nibble5) = nat_of_num (Bit1 (Bit0 (Bit1 (Bit0 One))));
nat_of_char (Char Nibble1 Nibble4) = nat_of_num (Bit0 (Bit0 (Bit1 (Bit0 One))));
nat_of_char (Char Nibble1 Nibble3) = nat_of_num (Bit1 (Bit1 (Bit0 (Bit0 One))));
nat_of_char (Char Nibble1 Nibble2) = nat_of_num (Bit0 (Bit1 (Bit0 (Bit0 One))));
nat_of_char (Char Nibble1 Nibble1) = nat_of_num (Bit1 (Bit0 (Bit0 (Bit0 One))));
nat_of_char (Char Nibble1 Nibble0) = nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 One))));
nat_of_char (Char Nibble0 NibbleF) = nat_of_num (Bit1 (Bit1 (Bit1 One)));
nat_of_char (Char Nibble0 NibbleE) = nat_of_num (Bit0 (Bit1 (Bit1 One)));
nat_of_char (Char Nibble0 NibbleD) = nat_of_num (Bit1 (Bit0 (Bit1 One)));
nat_of_char (Char Nibble0 NibbleC) = nat_of_num (Bit0 (Bit0 (Bit1 One)));
nat_of_char (Char Nibble0 NibbleB) = nat_of_num (Bit1 (Bit1 (Bit0 One)));
nat_of_char (Char Nibble0 NibbleA) = nat_of_num (Bit0 (Bit1 (Bit0 One)));
nat_of_char (Char Nibble0 Nibble9) = nat_of_num (Bit1 (Bit0 (Bit0 One)));
nat_of_char (Char Nibble0 Nibble8) = nat_of_num (Bit0 (Bit0 (Bit0 One)));
nat_of_char (Char Nibble0 Nibble7) = nat_of_num (Bit1 (Bit1 One));
nat_of_char (Char Nibble0 Nibble6) = nat_of_num (Bit0 (Bit1 One));
nat_of_char (Char Nibble0 Nibble5) = nat_of_num (Bit1 (Bit0 One));
nat_of_char (Char Nibble0 Nibble4) = nat_of_num (Bit0 (Bit0 One));
nat_of_char (Char Nibble0 Nibble3) = nat_of_num (Bit1 One);
nat_of_char (Char Nibble0 Nibble2) = nat_of_num (Bit0 One);
nat_of_char (Char Nibble0 Nibble1) = one_nat;
nat_of_char (Char Nibble0 Nibble0) = Zero_nat;

case_char :: forall a. (Nibble -> Nibble -> a) -> Char -> a;
case_char f c =
  let {
    n = nat_of_char c;
  } in f (nibble_of_nat
           (div_nat n (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 One)))))))
         (nibble_of_nat n);

term_of_char :: Char -> Terma;
term_of_char c =
  case_char
    (\ x y ->
      Appa (Appa (Consta "String.char.Char"
                   (Typerep "fun"
                     [Typerep "String.nibble" [],
                       Typerep "fun"
                         [Typerep "String.nibble" [],
                           Typerep "String.char" []]]))
             (term_of_nibble x))
        (term_of_nibble y))
    c;

class (Typerep a) => Term_of a where {
  term_of :: a -> Terma;
};

instance Term_of Char where {
  term_of = term_of_char;
};

newtype Narrowing_type = Narrowing_sum_of_products [[Narrowing_type]];

data Narrowing_term = Narrowing_variable [Integer] Narrowing_type
  | Narrowing_constructor Integer [Narrowing_term];

class (Typerep a) => Partial_term_of a where {
  partial_term_of :: Itself a -> Narrowing_term -> Terma;
};

partial_term_of_nibble :: Itself Nibble -> Narrowing_term -> Terma;
partial_term_of_nibble ty (Narrowing_constructor (15 :: Integer) []) =
  Consta "String.nibble.NibbleF" (Typerep "String.nibble" []);
partial_term_of_nibble ty (Narrowing_constructor (14 :: Integer) []) =
  Consta "String.nibble.NibbleE" (Typerep "String.nibble" []);
partial_term_of_nibble ty (Narrowing_constructor (13 :: Integer) []) =
  Consta "String.nibble.NibbleD" (Typerep "String.nibble" []);
partial_term_of_nibble ty (Narrowing_constructor (12 :: Integer) []) =
  Consta "String.nibble.NibbleC" (Typerep "String.nibble" []);
partial_term_of_nibble ty (Narrowing_constructor (11 :: Integer) []) =
  Consta "String.nibble.NibbleB" (Typerep "String.nibble" []);
partial_term_of_nibble ty (Narrowing_constructor (10 :: Integer) []) =
  Consta "String.nibble.NibbleA" (Typerep "String.nibble" []);
partial_term_of_nibble ty (Narrowing_constructor (9 :: Integer) []) =
  Consta "String.nibble.Nibble9" (Typerep "String.nibble" []);
partial_term_of_nibble ty (Narrowing_constructor (8 :: Integer) []) =
  Consta "String.nibble.Nibble8" (Typerep "String.nibble" []);
partial_term_of_nibble ty (Narrowing_constructor (7 :: Integer) []) =
  Consta "String.nibble.Nibble7" (Typerep "String.nibble" []);
partial_term_of_nibble ty (Narrowing_constructor (6 :: Integer) []) =
  Consta "String.nibble.Nibble6" (Typerep "String.nibble" []);
partial_term_of_nibble ty (Narrowing_constructor (5 :: Integer) []) =
  Consta "String.nibble.Nibble5" (Typerep "String.nibble" []);
partial_term_of_nibble ty (Narrowing_constructor (4 :: Integer) []) =
  Consta "String.nibble.Nibble4" (Typerep "String.nibble" []);
partial_term_of_nibble ty (Narrowing_constructor (3 :: Integer) []) =
  Consta "String.nibble.Nibble3" (Typerep "String.nibble" []);
partial_term_of_nibble ty (Narrowing_constructor (2 :: Integer) []) =
  Consta "String.nibble.Nibble2" (Typerep "String.nibble" []);
partial_term_of_nibble ty (Narrowing_constructor (1 :: Integer) []) =
  Consta "String.nibble.Nibble1" (Typerep "String.nibble" []);
partial_term_of_nibble ty (Narrowing_constructor (0 :: Integer) []) =
  Consta "String.nibble.Nibble0" (Typerep "String.nibble" []);
partial_term_of_nibble ty (Narrowing_variable p tt) =
  Free "_" (Typerep "String.nibble" []);

partial_term_of_char :: Itself Char -> Narrowing_term -> Terma;
partial_term_of_char ty (Narrowing_constructor (0 :: Integer) [b, a]) =
  Appa (Appa (Consta "String.char.Char"
               (Typerep "fun"
                 [Typerep "String.nibble" [],
                   Typerep "fun"
                     [Typerep "String.nibble" [], Typerep "String.char" []]]))
         (partial_term_of_nibble Type a))
    (partial_term_of_nibble Type b);
partial_term_of_char ty (Narrowing_variable p tt) =
  Free "_" (Typerep "String.char" []);

instance Partial_term_of Char where {
  partial_term_of = partial_term_of_char;
};

data Rat = Fract Int Int;

one_rat :: Rat;
one_rat = Fract (Pos One) (Pos One);

one_Rat :: Rat;
one_Rat = one_rat;

instance Onea Rat where {
  onea = one_Rat;
};

sgn_int :: Int -> Int;
sgn_int i =
  (if eq_int i Zero_int then Zero_int
    else (if less_int Zero_int i then Pos One else Neg One));

abs_int :: Int -> Int;
abs_int i = (if less_int i Zero_int then uminus_int i else i);

less_eq_rat :: Rat -> Rat -> Bool;
less_eq_rat (Fract a b) (Fract c d) =
  (if eq_int b Zero_int
    then less_eq_int Zero_int (times_int (sgn_int c) (sgn_int d))
    else (if eq_int d Zero_int
           then less_eq_int (times_int (sgn_int a) (sgn_int b)) Zero_int
           else less_eq_int (times_int (times_int a (abs_int d)) (sgn_int b))
                  (times_int (times_int c (abs_int b)) (sgn_int d))));

less_eq_Rat :: Rat -> Rat -> Bool;
less_eq_Rat = less_eq_rat;

less_rat :: Rat -> Rat -> Bool;
less_rat (Fract a b) (Fract c d) =
  (if eq_int b Zero_int
    then less_int Zero_int (times_int (sgn_int c) (sgn_int d))
    else (if eq_int d Zero_int
           then less_int (times_int (sgn_int a) (sgn_int b)) Zero_int
           else less_int (times_int (times_int a (abs_int d)) (sgn_int b))
                  (times_int (times_int c (abs_int b)) (sgn_int d))));

less_Rat :: Rat -> Rat -> Bool;
less_Rat = less_rat;

class Orda a where {
  less_eqa :: a -> a -> Bool;
  lessa :: a -> a -> Bool;
};

instance Orda Rat where {
  less_eqa = less_eq_Rat;
  lessa = less_Rat;
};

data Nata = Zero | Suca Nata;

minus_nat :: Nata -> Nata -> Nata;
minus_nat (Suca m) (Suca n) = minus_nat m n;
minus_nat Zero n = Zero;
minus_nat (Suca v) Zero = Suca v;

less_nat :: Nata -> Nata -> Bool;
less_nat m (Suca n) = less_eq_nat m n;
less_nat n Zero = False;

less_eq_nat :: Nata -> Nata -> Bool;
less_eq_nat (Suca m) n = less_nat m n;
less_eq_nat Zero n = True;

eq_nat :: Nata -> Nata -> Bool;
eq_nat (Suca nat) Zero = False;
eq_nat Zero (Suca nat) = False;
eq_nat (Suca nat2) (Suca nat) = eq_nat nat2 nat;
eq_nat Zero Zero = True;

divmod :: Nata -> Nata -> (Nata, Nata);
divmod m n =
  (if eq_nat n Zero || less_nat m n then (Zero, m)
    else let {
           a = divmod (minus_nat m n) n;
           (q, aa) = a;
         } in (Suca q, aa));

mod_nat :: Nata -> Nata -> Nata;
mod_nat m n = snd (divmod m n);

gcd_nat :: Nata -> Nata -> Nata;
gcd_nat x y = (if eq_nat y Zero then x else gcd_nat y (mod_nat x y));

of_nat_aux :: forall a. (Semiring_1a a) => (a -> a) -> Nata -> a -> a;
of_nat_aux inc Zero i = i;
of_nat_aux inc (Suca n) i = of_nat_aux inc n (inc i);

of_nat :: forall a. (Semiring_1a a) => Nata -> a;
of_nat n = of_nat_aux (\ i -> plusa i onea) n zeroa;

nat_aux :: Int -> Nata -> Nata;
nat_aux i n =
  (if less_eq_int i Zero_int then n
    else nat_aux (minus_int i (Pos One)) (Suca n));

nat :: Int -> Nata;
nat i = nat_aux i Zero;

gcd_int :: Int -> Int -> Int;
gcd_int x y = of_nat (gcd_nat (nat (abs_int x)) (nat (abs_int y)));

divmod_0 ::
  forall a b.
    (Minus a, Zero a, Ord a, Eqa a, One b, Plus b, Zero b) => a -> a -> (b, a);
divmod_0 k l =
  (if eq l zero || less k l then (zero, k)
    else let {
           a = divmod_0 (minus k l) l;
           (q, aa) = a;
         } in (plus q one, aa));

apsnd :: forall a b c. (a -> b) -> (c, a) -> (c, b);
apsnd f (x, y) = (x, f y);

divmod_inta :: Int -> Int -> (Int, Int);
divmod_inta k l =
  let {
    divmod = divmod_0;
  } in (if eq_int k Zero_int then (Zero_int, Zero_int)
         else (if eq_int l Zero_int then (Zero_int, k)
                else apsnd (times_int (sgn_int l))
                       (if eq_int (sgn_int k) (sgn_int l)
                         then divmod (abs_inta k) (abs_inta l)
                         else let {
                                (r, s) = divmod (abs_inta k) (abs_inta l);
                              } in (if eq_int s Zero_int
                                     then (uminus_int r, Zero_int)
                                     else (minus_int (uminus_int r) (Pos One),
    minus_int (abs_int l) s)))));

div_int :: Int -> Int -> Int;
div_int a b = fst (divmod_inta a b);

fract_norm :: Int -> Int -> Rat;
fract_norm a b =
  (if eq_int a Zero_int || eq_int b Zero_int then Fract Zero_int (Pos One)
    else let {
           c = gcd_int a b;
         } in (if less_int Zero_int b then Fract (div_int a c) (div_int b c)
                else Fract (uminus_int (div_int a c))
                       (uminus_int (div_int b c))));

plus_rat :: Rat -> Rat -> Rat;
plus_rat (Fract a b) (Fract c d) =
  (if eq_int b Zero_int then Fract c d
    else (if eq_int d Zero_int then Fract a b
           else fract_norm (plus_int (times_int a d) (times_int c b))
                  (times_int b d)));

plus_Rat :: Rat -> Rat -> Rat;
plus_Rat = plus_rat;

instance Plusa Rat where {
  plusa = plus_Rat;
};

times_rat :: Rat -> Rat -> Rat;
times_rat (Fract a b) (Fract c d) = fract_norm (times_int a c) (times_int b d);

times_Rat :: Rat -> Rat -> Rat;
times_Rat = times_rat;

minus_rat :: Rat -> Rat -> Rat;
minus_rat (Fract a b) (Fract c d) =
  (if eq_int b Zero_int then Fract (uminus_int c) d
    else (if eq_int d Zero_int then Fract a b
           else fract_norm (minus_int (times_int a d) (times_int c b))
                  (times_int b d)));

minus_Rat :: Rat -> Rat -> Rat;
minus_Rat = minus_rat;

neg_rat :: Rat -> Rat;
neg_rat (Fract a b) = Fract (uminus_int a) b;

neg_Rat :: Rat -> Rat;
neg_Rat = neg_rat;

zero_rat :: Rat;
zero_rat = Fract Zero_int (Pos One);

zero_Rat :: Rat;
zero_Rat = zero_rat;

class Minusa a where {
  minusa :: a -> a -> a;
};

class Uminus a where {
  neg :: a -> a;
};

class (Semigroup_adda a) => Cancel_semigroup_adda a where {
};

class (Ab_semigroup_adda a,
        Cancel_semigroup_adda a) => Cancel_ab_semigroup_adda a where {
};

class (Cancel_ab_semigroup_adda a,
        Comm_monoid_adda a) => Cancel_comm_monoid_adda a where {
};

class (Cancel_comm_monoid_adda a, Semiring_0a a) => Semiring_0_cancela a where {
};

class (Minusa a, Monoid_adda a, Uminus a) => Group_add a where {
};

class (Cancel_comm_monoid_adda a, Group_add a) => Ab_group_add a where {
};

class (Ab_group_add a, Semiring_0_cancela a) => Ring a where {
};

instance Semigroup_adda Rat where {
};

instance Cancel_semigroup_adda Rat where {
};

instance Ab_semigroup_adda Rat where {
};

instance Cancel_ab_semigroup_adda Rat where {
};

instance Zeroa Rat where {
  zeroa = zero_Rat;
};

instance Monoid_adda Rat where {
};

instance Comm_monoid_adda Rat where {
};

instance Cancel_comm_monoid_adda Rat where {
};

instance Timesa Rat where {
  timesa = times_Rat;
};

instance Mult_zeroa Rat where {
};

instance Semigroup_multa Rat where {
};

instance Semiringa Rat where {
};

instance Semiring_0a Rat where {
};

instance Semiring_0_cancela Rat where {
};

instance Uminus Rat where {
  neg = neg_Rat;
};

instance Minusa Rat where {
  minusa = minus_Rat;
};

instance Group_add Rat where {
};

instance Ab_group_add Rat where {
};

instance Ring Rat where {
};

instance Powera Rat where {
};

class (Semiring_0_cancela a, Semiring_1a a) => Semiring_1_cancela a where {
};

class (Ring a, Semiring_1_cancela a) => Ring_1 a where {
};

instance Zero_neq_onea Rat where {
};

instance Monoid_multa Rat where {
};

instance Semiring_1a Rat where {
};

instance Semiring_1_cancela Rat where {
};

instance Ring_1 Rat where {
};

data Typerepb = Typerepa [Char] [Typerepb];

instance Eq Typerepb where {
  a == b = equal_Typerep a b;
};

equal_Typerep :: Typerepb -> Typerepb -> Bool;
equal_Typerep (Typerepa x1 x2) (Typerepa y1 y2) = x1 == y1 && x2 == y2;

typerep_Typerep :: Itself Typerepb -> Typerepa;
typerep_Typerep t = Typerep "Rationals.Typerep" [];

instance Typerep Typerepb where {
  typerep = typerep_Typerep;
};

term_of_list :: forall a. (Term_of a) => [a] -> Terma;
term_of_list (a : b) =
  Appa (Appa (Consta "List.list.Cons"
               (Typerep "fun"
                 [(typerep :: Itself a -> Typerepa) Type,
                   Typerep "fun"
                     [Typerep "List.list"
                        [(typerep :: Itself a -> Typerepa) Type],
                       Typerep "List.list"
                         [(typerep :: Itself a -> Typerepa) Type]]]))
         (term_of a))
    (term_of_list b);
term_of_list [] =
  Consta "List.list.Nil"
    (Typerep "List.list" [(typerep :: Itself a -> Typerepa) Type]);

instance Term_of Typerepb where {
  term_of = term_of_Typerep;
};

term_of_Typerep :: Typerepb -> Terma;
term_of_Typerep (Typerepa a b) =
  Appa (Appa (Consta "Rationals.Typerep.Typerep"
               (Typerep "fun"
                 [Typerep "List.list" [Typerep "String.char" []],
                   Typerep "fun"
                     [Typerep "List.list" [Typerep "Rationals.Typerep" []],
                       Typerep "Rationals.Typerep" []]]))
         (term_of_list a))
    (term_of_list b);

partial_term_of_list ::
  forall a. (Partial_term_of a) => Itself [a] -> Narrowing_term -> Terma;
partial_term_of_list ty (Narrowing_constructor (1 :: Integer) [b, a]) =
  Appa (Appa (Consta "List.list.Cons"
               (Typerep "fun"
                 [(typerep :: Itself a -> Typerepa) Type,
                   Typerep "fun"
                     [Typerep "List.list"
                        [(typerep :: Itself a -> Typerepa) Type],
                       Typerep "List.list"
                         [(typerep :: Itself a -> Typerepa) Type]]]))
         ((partial_term_of :: Itself a -> Narrowing_term -> Terma) Type a))
    ((partial_term_of_list :: Itself [a] -> Narrowing_term -> Terma) Type b);
partial_term_of_list ty (Narrowing_constructor (0 :: Integer) []) =
  Consta "List.list.Nil"
    (Typerep "List.list" [(typerep :: Itself a -> Typerepa) Type]);
partial_term_of_list ty (Narrowing_variable p tt) =
  Free "_" (Typerep "List.list" [(typerep :: Itself a -> Typerepa) Type]);

instance Partial_term_of Typerepb where {
  partial_term_of = partial_term_of_Typerep;
};

partial_term_of_Typerep :: Itself Typerepb -> Narrowing_term -> Terma;
partial_term_of_Typerep ty (Narrowing_constructor (0 :: Integer) [b, a]) =
  Appa (Appa (Consta "Rationals.Typerep.Typerep"
               (Typerep "fun"
                 [Typerep "List.list" [Typerep "String.char" []],
                   Typerep "fun"
                     [Typerep "List.list" [Typerep "Rationals.Typerep" []],
                       Typerep "Rationals.Typerep" []]]))
         ((partial_term_of_list :: Itself [Char] -> Narrowing_term -> Terma)
           Type a))
    ((partial_term_of_list :: Itself [Typerepb] -> Narrowing_term -> Terma) Type
      b);
partial_term_of_Typerep ty (Narrowing_variable p tt) =
  Free "_" (Typerep "Rationals.Typerep" []);

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

instance Semigroup_add Natural where {
};

instance Monoid_add Natural where {
};

class (Timesa a) => Dvda a where {
};

class (Dvda a) => Diva a where {
  diva :: a -> a -> a;
  moda :: a -> a -> a;
};

class (Semigroup_multa a) => Ab_semigroup_multa a where {
};

class (Ab_semigroup_multa a, Semiringa a) => Comm_semiringa a where {
};

class (Comm_semiringa a, Semiring_0a a) => Comm_semiring_0a a where {
};

class (Comm_semiring_0a a,
        Semiring_0_cancela a) => Comm_semiring_0_cancela a where {
};

class (Ab_semigroup_multa a, Monoid_multa a) => Comm_monoid_multa a where {
};

class (Comm_monoid_multa a, Comm_semiring_0a a, Dvda a,
        Semiring_1a a) => Comm_semiring_1a a where {
};

class (Comm_semiring_0_cancela a, Comm_semiring_1a a,
        Semiring_1_cancela a) => Comm_semiring_1_cancela a where {
};

class (Comm_semiring_0_cancela a, Ring a) => Comm_ring a where {
};

class (Comm_ring a, Comm_semiring_1_cancela a,
        Ring_1 a) => Comm_ring_1 a where {
};

class (Timesa a, Zeroa a) => No_zero_divisors a where {
};

class (No_zero_divisors a, Ring a) => Ring_no_zero_divisors a where {
};

class (Ring_1 a, Ring_no_zero_divisors a) => Ring_1_no_zero_divisors a where {
};

class (Comm_ring_1 a, Ring_1_no_zero_divisors a) => Idom a where {
};

class Inverse a where {
  inverse :: a -> a;
  divide :: a -> a -> a;
};

class (Inverse a, Ring_1_no_zero_divisors a) => Division_ring a where {
};

class (Division_ring a, Idom a) => Field a where {
};

class (Semiring_1a a) => Semiring_char_0a a where {
};

class (Ring_1 a, Semiring_char_0a a) => Ring_char_0 a where {
};

class (Field a, Ring_char_0 a) => Field_char_0 a where {
};

data Set a = Set [a] | Coset [a];

data Term = Const [Char] Typerepb | App Term Term;

data Nibblea = Nibble0a | Nibble1a | Nibble2a | Nibble3a | Nibble4a | Nibble5a
  | Nibble6a | Nibble7a | Nibble8a | Nibble9a | NibbleAa | NibbleBa | NibbleCa
  | NibbleDa | NibbleEa | NibbleFa;

data Chara = Chara Nibblea Nibblea;

data Itselfa a = Typea;

data Nat_IITN_Nat;

data Rat_IITN_Rat;

data Term_pre_Term a;

data Term_IITN_Term;

data Chara_IITN_Chara;

data Itself_pre_Itself a b;

data Nibble_pre_Nibble;

data Narrowing_cons a = Narrowing_cons Narrowing_type [[Narrowing_term] -> a];

data Itself_IITN_Itself a;

data Nibble_IITN_Nibble;

data Typerep_IITN_Typerep;

ball :: forall a. Set a -> (a -> Bool) -> Bool;
ball (Set xs) p = all p xs;

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
           else ((apsnda . (\ a b -> a * b)) . sgn_integer) l
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

scompa :: forall a b c d. (a -> (b, c)) -> (b -> c -> d) -> a -> d;
scompa f g = (\ x -> let {
                       (a, b) = f x;
                     } in g a b);

equal_natural :: Natural -> Natural -> Bool;
equal_natural m n = integer_of_natural m == integer_of_natural n;

iterate :: forall a b. Natural -> (a -> b -> (a, b)) -> a -> b -> (a, b);
iterate k f x =
  (if equal_natural k zero_natural then (\ a -> (x, a))
    else scompa (f x) (iterate (minus_natural k one_natural) f));

range :: Natural -> (Natural, Natural) -> (Natural, (Natural, Natural));
range k =
  scompa
    (iterate (log (natural_of_integer (2147483561 :: Integer)) k)
      (\ l ->
        scompa next
          (\ v ->
            (\ a ->
              (plus_natural v
                 (times_natural l (natural_of_integer (2147483561 :: Integer))),
                a))))
      one_natural)
    (\ v -> (\ a -> (mod_natural v k, a)));

leta :: forall a b. a -> (a -> b) -> b;
leta s f = f s;

maxaa :: forall a. (a -> a -> Bool) -> a -> a -> a;
maxaa less_eq3 a b = (if less_eq3 a b then b else a);

maxa :: forall a. (Orda a) => a -> a -> a;
maxa = maxaa less_eqa;

minaa :: forall a. (a -> a -> Bool) -> a -> a -> a;
minaa less_eq4 a b = (if less_eq4 a b then a else b);

mina :: forall a. (Orda a) => a -> a -> a;
mina = minaa less_eqa;

scomp :: forall a b c d. (a -> (b, c)) -> (b -> c -> d) -> a -> d;
scomp f g = (\ x -> let {
                      a = f x;
                      (aa, b) = a;
                    } in g aa b);

split :: forall a b c. (a -> b -> c) -> (a, b) -> c;
split f (a, b) = f a b;

eq_rat :: Rat -> Rat -> Bool;
eq_rat (Fract a b) (Fract c d) =
  (if eq_int b Zero_int then eq_int c Zero_int || eq_int d Zero_int
    else (if eq_int d Zero_int then eq_int a Zero_int || eq_int b Zero_int
           else eq_int (times_int a d) (times_int b c)));

of_int :: forall a. (Ring_1 a) => Int -> a;
of_int k =
  (if eq_int k Zero_int then zeroa
    else (if less_int k Zero_int then neg (of_int (uminus_int k))
           else let {
                  (l, m) = divmod_inta k (Pos (Bit0 One));
                  la = of_int l;
                } in (if eq_int m Zero_int then plusa la la
                       else plusa (plusa la la) onea)));

of_rat :: forall a. (Field_char_0 a) => Rat -> a;
of_rat (Fract a b) =
  (if not (eq_int b Zero_int) then divide (of_int a) (of_int b) else zeroa);

abs_rat :: Rat -> Rat;
abs_rat (Fract a b) = Fract (abs_int a) (abs_int b);

collect :: forall a. (a -> Bool) -> a -> Bool;
collect p = p;

inf_rat :: Rat -> Rat -> Rat;
inf_rat = mina;

mod_int :: Int -> Int -> Int;
mod_int a b = snd (divmod_inta a b);

sgn_rat :: Rat -> Rat;
sgn_rat (Fract a b) = of_int (times_int (sgn_int a) (sgn_int b));

sup_rat :: Rat -> Rat -> Rat;
sup_rat = maxa;

size_list :: forall a. (a -> Nat) -> [a] -> Nat;
size_list x [] = Zero_nat;
size_list x (x21 : x22) =
  plus_nat (plus_nat (x x21) (size_list x x22)) (Suc Zero_nat);

listsum :: forall a. (Monoid_add a) => [a] -> a;
listsum xs = foldr plus xs zero;

select_weight ::
  forall a. [(Natural, a)] -> (Natural, Natural) -> (a, (Natural, Natural));
select_weight xs =
  scompa (range (listsum (map fst xs))) (\ k -> (\ a -> (pick xs k, a)));

divide_rat :: Rat -> Rat -> Rat;
divide_rat (Fract a b) (Fract c d) = fract_norm (times_int a d) (times_int b c);

rec_Nat :: forall a. a -> (Nata -> a -> a) -> Nata -> a;
rec_Nat f1 f2 Zero = f1;
rec_Nat f1 f2 (Suca x2) = f2 x2 (rec_Nat f1 f2 x2);

rec_Rat :: forall a. (Int -> Int -> a) -> Rat -> a;
rec_Rat f (Fract x1 x2) = f x1 x2;

bot_set :: forall a. Set a;
bot_set = Set [];

set_Itself :: forall a. Itselfa a -> Set a;
set_Itself Typea = bot_set;

pred_Itself :: forall a. (a -> Bool) -> Itselfa a -> Bool;
pred_Itself p = (\ x -> ball (set_Itself x) p);

valapp ::
  forall a b. (a -> b, () -> Terma) -> (a, () -> Terma) -> (b, () -> Terma);
valapp (f, tf) (x, tx) = (f x, (\ _ -> Appa (tf ()) (tx ())));

size_Nat :: Nata -> Nat;
size_Nat Zero = Zero_nat;
size_Nat (Suca x2) = plus_nat (size_Nat x2) (Suc Zero_nat);

size_Rat :: Rat -> Nat;
size_Rat (Fract x1 x2) = Zero_nat;

rec_Term ::
  forall a.
    ([Char] -> Typerepb -> a) -> (Term -> Term -> a -> a -> a) -> Term -> a;
rec_Term f1 f2 (Const x11 x12) = f1 x11 x12;
rec_Term f1 f2 (App x21 x22) =
  f2 x21 x22 (rec_Term f1 f2 x21) (rec_Term f1 f2 x22);

sum ::
  forall a.
    (Integer -> Narrowing_cons a) ->
      (Integer -> Narrowing_cons a) -> Integer -> Narrowing_cons a;
sum a b d =
  let {
    (Narrowing_cons (Narrowing_sum_of_products ssa) ca) = a d;
    (Narrowing_cons (Narrowing_sum_of_products ssb) cb) = b d;
  } in Narrowing_cons (Narrowing_sum_of_products (ssa ++ ssb)) (ca ++ cb);

size_Term :: Term -> Nat;
size_Term (Const x11 x12) = Zero_nat;
size_Term (App x21 x22) =
  plus_nat (plus_nat (size_Term x21) (size_Term x22)) (Suc Zero_nat);

collapse :: forall a b. (a -> (a -> (b, a), a)) -> a -> (b, a);
collapse f = scompa f id;

random_aux_Nat ::
  Natural ->
    Natural -> (Natural, Natural) -> ((Nata, () -> Terma), (Natural, Natural));
random_aux_Nat i j s =
  collapse
    (select_weight
      [(i, scompa (random_aux_Nat (minus_natural i one_natural) j)
             (\ x ->
               (\ a ->
                 (valapp
                    (Suca,
                      (\ _ ->
                        Consta "Rationals.Nat.Suc"
                          (Typerep "fun"
                            [Typerep "Rationals.Nat" [],
                              Typerep "Rationals.Nat" []])))
                    x,
                   a)))),
        (one_natural,
          (\ a ->
            ((Zero,
               (\ _ ->
                 Consta "Rationals.Nat.Zero" (Typerep "Rationals.Nat" []))),
              a)))])
    s;

term_of_num :: Num -> Terma;
term_of_num (Bit1 a) =
  Appa (Consta "Num.num.Bit1"
         (Typerep "fun" [Typerep "Num.num" [], Typerep "Num.num" []]))
    (term_of_num a);
term_of_num (Bit0 a) =
  Appa (Consta "Num.num.Bit0"
         (Typerep "fun" [Typerep "Num.num" [], Typerep "Num.num" []]))
    (term_of_num a);
term_of_num One = Consta "Num.num.One" (Typerep "Num.num" []);

term_of_int :: Int -> Terma;
term_of_int (Neg a) =
  Appa (Consta "Int.Neg"
         (Typerep "fun" [Typerep "Num.num" [], Typerep "Int.int" []]))
    (term_of_num a);
term_of_int (Pos a) =
  Appa (Consta "Int.Pos"
         (Typerep "fun" [Typerep "Num.num" [], Typerep "Int.int" []]))
    (term_of_num a);
term_of_int Zero_int =
  Consta "Int.zero_int_inst.zero_int" (Typerep "Int.int" []);

of_nat_auxa :: forall a. (Semiring_1 a) => (a -> a) -> Nat -> a -> a;
of_nat_auxa inc Zero_nat i = i;
of_nat_auxa inc (Suc n) i = of_nat_auxa inc n (inc i);

of_nata :: forall a. (Semiring_1 a) => Nat -> a;
of_nata n = of_nat_auxa (\ i -> plus i one) n zero;

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

random_int ::
  Natural -> (Natural, Natural) -> ((Int, () -> Terma), (Natural, Natural));
random_int i =
  scompa
    (range
      (plus_natural (times_natural (natural_of_integer (2 :: Integer)) i)
        one_natural))
    (\ k ->
      (\ a ->
        (let {
           j = (if less_eq_natural i k
                 then of_nata (nat_of_natural (minus_natural k i))
                 else uminus_int
                        (of_nata (nat_of_natural (minus_natural i k))));
         } in (j, (\ _ -> term_of_int j)),
          a)));

random_aux_Rat ::
  Natural ->
    Natural -> (Natural, Natural) -> ((Rat, () -> Terma), (Natural, Natural));
random_aux_Rat i j s =
  collapse
    (select_weight
      [(one_natural,
         scompa (random_int j)
           (\ x ->
             scompa (random_int j)
               (\ y ->
                 (\ a ->
                   (valapp
                      (valapp
                        (Fract,
                          (\ _ ->
                            Consta "Rationals.Rat.Fract"
                              (Typerep "fun"
                                [Typerep "Int.int" [],
                                  Typerep "fun"
                                    [Typerep "Int.int" [],
                                      Typerep "Rationals.Rat" []]])))
                        x)
                      y,
                     a)))))])
    s;

cons :: forall a. a -> Integer -> Narrowing_cons a;
cons a d = Narrowing_cons (Narrowing_sum_of_products [[]]) [(\ _ -> a)];

rec_Chara :: forall a. (Nibblea -> Nibblea -> a) -> Chara -> a;
rec_Chara f (Chara x1 x2) = f x1 x2;

size_Chara :: Chara -> Nat;
size_Chara (Chara x1 x2) = Zero_nat;

random_aux_Nibble ::
  Natural ->
    Natural ->
      (Natural, Natural) -> ((Nibblea, () -> Terma), (Natural, Natural));
random_aux_Nibble i j s =
  collapse
    (select_weight
      [(one_natural,
         (\ a ->
           ((Nibble0a,
              (\ _ ->
                Consta "Rationals.Nibble.Nibble0"
                  (Typerep "Rationals.Nibble" []))),
             a))),
        (one_natural,
          (\ a ->
            ((Nibble1a,
               (\ _ ->
                 Consta "Rationals.Nibble.Nibble1"
                   (Typerep "Rationals.Nibble" []))),
              a))),
        (one_natural,
          (\ a ->
            ((Nibble2a,
               (\ _ ->
                 Consta "Rationals.Nibble.Nibble2"
                   (Typerep "Rationals.Nibble" []))),
              a))),
        (one_natural,
          (\ a ->
            ((Nibble3a,
               (\ _ ->
                 Consta "Rationals.Nibble.Nibble3"
                   (Typerep "Rationals.Nibble" []))),
              a))),
        (one_natural,
          (\ a ->
            ((Nibble4a,
               (\ _ ->
                 Consta "Rationals.Nibble.Nibble4"
                   (Typerep "Rationals.Nibble" []))),
              a))),
        (one_natural,
          (\ a ->
            ((Nibble5a,
               (\ _ ->
                 Consta "Rationals.Nibble.Nibble5"
                   (Typerep "Rationals.Nibble" []))),
              a))),
        (one_natural,
          (\ a ->
            ((Nibble6a,
               (\ _ ->
                 Consta "Rationals.Nibble.Nibble6"
                   (Typerep "Rationals.Nibble" []))),
              a))),
        (one_natural,
          (\ a ->
            ((Nibble7a,
               (\ _ ->
                 Consta "Rationals.Nibble.Nibble7"
                   (Typerep "Rationals.Nibble" []))),
              a))),
        (one_natural,
          (\ a ->
            ((Nibble8a,
               (\ _ ->
                 Consta "Rationals.Nibble.Nibble8"
                   (Typerep "Rationals.Nibble" []))),
              a))),
        (one_natural,
          (\ a ->
            ((Nibble9a,
               (\ _ ->
                 Consta "Rationals.Nibble.Nibble9"
                   (Typerep "Rationals.Nibble" []))),
              a))),
        (one_natural,
          (\ a ->
            ((NibbleAa,
               (\ _ ->
                 Consta "Rationals.Nibble.NibbleA"
                   (Typerep "Rationals.Nibble" []))),
              a))),
        (one_natural,
          (\ a ->
            ((NibbleBa,
               (\ _ ->
                 Consta "Rationals.Nibble.NibbleB"
                   (Typerep "Rationals.Nibble" []))),
              a))),
        (one_natural,
          (\ a ->
            ((NibbleCa,
               (\ _ ->
                 Consta "Rationals.Nibble.NibbleC"
                   (Typerep "Rationals.Nibble" []))),
              a))),
        (one_natural,
          (\ a ->
            ((NibbleDa,
               (\ _ ->
                 Consta "Rationals.Nibble.NibbleD"
                   (Typerep "Rationals.Nibble" []))),
              a))),
        (one_natural,
          (\ a ->
            ((NibbleEa,
               (\ _ ->
                 Consta "Rationals.Nibble.NibbleE"
                   (Typerep "Rationals.Nibble" []))),
              a))),
        (one_natural,
          (\ a ->
            ((NibbleFa,
               (\ _ ->
                 Consta "Rationals.Nibble.NibbleF"
                   (Typerep "Rationals.Nibble" []))),
              a)))])
    s;

random_Nibble ::
  Natural -> (Natural, Natural) -> ((Nibblea, () -> Terma), (Natural, Natural));
random_Nibble i = random_aux_Nibble i i;

random_aux_Chara ::
  Natural ->
    Natural -> (Natural, Natural) -> ((Chara, () -> Terma), (Natural, Natural));
random_aux_Chara i j s =
  collapse
    (select_weight
      [(one_natural,
         scompa (random_Nibble j)
           (\ x ->
             scompa (random_Nibble j)
               (\ y ->
                 (\ a ->
                   (valapp
                      (valapp
                        (Chara,
                          (\ _ ->
                            Consta "Rationals.Chara.Chara"
                              (Typerep "fun"
                                [Typerep "Rationals.Nibble" [],
                                  Typerep "fun"
                                    [Typerep "Rationals.Nibble" [],
                                      Typerep "Rationals.Chara" []]])))
                        x)
                      y,
                     a)))))])
    s;

int_of_integer :: Integer -> Int;
int_of_integer k =
  (if k < (0 :: Integer) then uminus_int (int_of_integer (negate k))
    else (if k == (0 :: Integer) then Zero_int
           else let {
                  (l, j) = divmod_integer k (2 :: Integer);
                  la = times_int (Pos (Bit0 One)) (int_of_integer l);
                } in (if j == (0 :: Integer) then la
                       else plus_int la (Pos One))));

map_Itself :: forall a b. (a -> b) -> Itselfa a -> Itselfa b;
map_Itself f Typea = Typea;

rec_Itself :: forall a b. a -> Itselfa b -> a;
rec_Itself f Typea = f;

rel_Itself :: forall a b. (a -> b -> Bool) -> Itselfa a -> Itselfa b -> Bool;
rel_Itself r Typea Typea = True;

rec_Nibble ::
  forall a.
    a -> a -> a -> a -> a -> a -> a -> a ->
 a -> a -> a -> a -> a -> a -> a -> a -> Nibblea -> a;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble0a = f1;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble1a = f2;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble2a = f3;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble3a = f4;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble4a = f5;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble5a = f6;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble6a = f7;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble7a = f8;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble8a = f9;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble9a =
  f10;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 NibbleAa =
  f11;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 NibbleBa =
  f12;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 NibbleCa =
  f13;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 NibbleDa =
  f14;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 NibbleEa =
  f15;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 NibbleFa =
  f16;

random_aux_Itself ::
  forall a.
    (Typerep a) => Natural ->
                     Natural ->
                       (Natural, Natural) ->
                         ((Itselfa a, () -> Terma), (Natural, Natural));
random_aux_Itself i j s =
  collapse
    (select_weight
      [(one_natural,
         (\ a ->
           ((Typea,
              (\ _ ->
                Consta "Rationals.Itself.Type"
                  (Typerep "Rationals.Itself"
                    [(typerep :: Itself a -> Typerepa) Type]))),
             a)))])
    s;

size_Itself :: forall a. (a -> Nat) -> Itselfa a -> Nat;
size_Itself x Typea = Zero_nat;

size_Nibble :: Nibblea -> Nat;
size_Nibble Nibble0a = Zero_nat;
size_Nibble Nibble1a = Zero_nat;
size_Nibble Nibble2a = Zero_nat;
size_Nibble Nibble3a = Zero_nat;
size_Nibble Nibble4a = Zero_nat;
size_Nibble Nibble5a = Zero_nat;
size_Nibble Nibble6a = Zero_nat;
size_Nibble Nibble7a = Zero_nat;
size_Nibble Nibble8a = Zero_nat;
size_Nibble Nibble9a = Zero_nat;
size_Nibble NibbleAa = Zero_nat;
size_Nibble NibbleBa = Zero_nat;
size_Nibble NibbleCa = Zero_nat;
size_Nibble NibbleDa = Zero_nat;
size_Nibble NibbleEa = Zero_nat;
size_Nibble NibbleFa = Zero_nat;

rec_Typerep :: forall a. ([Char] -> [(Typerepb, a)] -> a) -> Typerepb -> a;
rec_Typerep f (Typerepa x1 x2) =
  f x1 (map (\ typerep -> (typerep, rec_Typerep f typerep)) x2);

non_empty :: Narrowing_type -> Bool;
non_empty (Narrowing_sum_of_products ps) = not (null ps);

size_Typerep :: Typerepb -> Nat;
size_Typerep (Typerepa x1 x2) =
  plus_nat (size_list size_Typerep x2) (Suc Zero_nat);

drawn_from :: forall a. [a] -> Narrowing_cons a;
drawn_from xs =
  Narrowing_cons (Narrowing_sum_of_products (map (\ _ -> []) xs))
    (map (\ x _ -> x) xs);

diva_int :: Int -> Int -> Int;
diva_int = div_int;

moda_int :: Int -> Int -> Int;
moda_int = mod_int;

around_zero :: Int -> [Int];
around_zero i =
  (if less_int i Zero_int then []
    else (if equal_int i Zero_int then [Zero_int]
           else around_zero (minus_int i (Pos One)) ++ [i, uminus_int i]));

size_Nata :: Nata -> Nat;
size_Nata Zero = Zero_nat;
size_Nata (Suca x2) = plus_nat (size_Nata x2) (Suc Zero_nat);

size_Rata :: Rat -> Nat;
size_Rata (Fract x1 x2) = Zero_nat;

equal_Nat :: Nata -> Nata -> Bool;
equal_Nat Zero (Suca x2) = False;
equal_Nat (Suca x2) Zero = False;
equal_Nat (Suca x2) (Suca y2) = equal_Nat x2 y2;
equal_Nat Zero Zero = True;

equal_Rat :: Rat -> Rat -> Bool;
equal_Rat (Fract x1 x2) (Fract y1 y2) = equal_int x1 y1 && equal_int x2 y2;

size_Terma :: Term -> Nat;
size_Terma (Const x11 x12) = Zero_nat;
size_Terma (App x21 x22) =
  plus_nat (plus_nat (size_Terma x21) (size_Terma x22)) (Suc Zero_nat);

equal_Term :: Term -> Term -> Bool;
equal_Term (Const x11 x12) (App x21 x22) = False;
equal_Term (App x21 x22) (Const x11 x12) = False;
equal_Term (App x21 x22) (App y21 y22) =
  equal_Term x21 y21 && equal_Term x22 y22;
equal_Term (Const x11 x12) (Const y11 y12) =
  x11 == y11 && equal_Typerep x12 y12;

random_Nat ::
  Natural -> (Natural, Natural) -> ((Nata, () -> Terma), (Natural, Natural));
random_Nat i = random_aux_Nat i i;

random_Rat ::
  Natural -> (Natural, Natural) -> ((Rat, () -> Terma), (Natural, Natural));
random_Rat i = random_aux_Rat i i;

size_Charaa :: Chara -> Nat;
size_Charaa (Chara x1 x2) = Zero_nat;

equal_Nibble :: Nibblea -> Nibblea -> Bool;
equal_Nibble NibbleEa NibbleFa = False;
equal_Nibble NibbleFa NibbleEa = False;
equal_Nibble NibbleDa NibbleFa = False;
equal_Nibble NibbleFa NibbleDa = False;
equal_Nibble NibbleDa NibbleEa = False;
equal_Nibble NibbleEa NibbleDa = False;
equal_Nibble NibbleCa NibbleFa = False;
equal_Nibble NibbleFa NibbleCa = False;
equal_Nibble NibbleCa NibbleEa = False;
equal_Nibble NibbleEa NibbleCa = False;
equal_Nibble NibbleCa NibbleDa = False;
equal_Nibble NibbleDa NibbleCa = False;
equal_Nibble NibbleBa NibbleFa = False;
equal_Nibble NibbleFa NibbleBa = False;
equal_Nibble NibbleBa NibbleEa = False;
equal_Nibble NibbleEa NibbleBa = False;
equal_Nibble NibbleBa NibbleDa = False;
equal_Nibble NibbleDa NibbleBa = False;
equal_Nibble NibbleBa NibbleCa = False;
equal_Nibble NibbleCa NibbleBa = False;
equal_Nibble NibbleAa NibbleFa = False;
equal_Nibble NibbleFa NibbleAa = False;
equal_Nibble NibbleAa NibbleEa = False;
equal_Nibble NibbleEa NibbleAa = False;
equal_Nibble NibbleAa NibbleDa = False;
equal_Nibble NibbleDa NibbleAa = False;
equal_Nibble NibbleAa NibbleCa = False;
equal_Nibble NibbleCa NibbleAa = False;
equal_Nibble NibbleAa NibbleBa = False;
equal_Nibble NibbleBa NibbleAa = False;
equal_Nibble Nibble9a NibbleFa = False;
equal_Nibble NibbleFa Nibble9a = False;
equal_Nibble Nibble9a NibbleEa = False;
equal_Nibble NibbleEa Nibble9a = False;
equal_Nibble Nibble9a NibbleDa = False;
equal_Nibble NibbleDa Nibble9a = False;
equal_Nibble Nibble9a NibbleCa = False;
equal_Nibble NibbleCa Nibble9a = False;
equal_Nibble Nibble9a NibbleBa = False;
equal_Nibble NibbleBa Nibble9a = False;
equal_Nibble Nibble9a NibbleAa = False;
equal_Nibble NibbleAa Nibble9a = False;
equal_Nibble Nibble8a NibbleFa = False;
equal_Nibble NibbleFa Nibble8a = False;
equal_Nibble Nibble8a NibbleEa = False;
equal_Nibble NibbleEa Nibble8a = False;
equal_Nibble Nibble8a NibbleDa = False;
equal_Nibble NibbleDa Nibble8a = False;
equal_Nibble Nibble8a NibbleCa = False;
equal_Nibble NibbleCa Nibble8a = False;
equal_Nibble Nibble8a NibbleBa = False;
equal_Nibble NibbleBa Nibble8a = False;
equal_Nibble Nibble8a NibbleAa = False;
equal_Nibble NibbleAa Nibble8a = False;
equal_Nibble Nibble8a Nibble9a = False;
equal_Nibble Nibble9a Nibble8a = False;
equal_Nibble Nibble7a NibbleFa = False;
equal_Nibble NibbleFa Nibble7a = False;
equal_Nibble Nibble7a NibbleEa = False;
equal_Nibble NibbleEa Nibble7a = False;
equal_Nibble Nibble7a NibbleDa = False;
equal_Nibble NibbleDa Nibble7a = False;
equal_Nibble Nibble7a NibbleCa = False;
equal_Nibble NibbleCa Nibble7a = False;
equal_Nibble Nibble7a NibbleBa = False;
equal_Nibble NibbleBa Nibble7a = False;
equal_Nibble Nibble7a NibbleAa = False;
equal_Nibble NibbleAa Nibble7a = False;
equal_Nibble Nibble7a Nibble9a = False;
equal_Nibble Nibble9a Nibble7a = False;
equal_Nibble Nibble7a Nibble8a = False;
equal_Nibble Nibble8a Nibble7a = False;
equal_Nibble Nibble6a NibbleFa = False;
equal_Nibble NibbleFa Nibble6a = False;
equal_Nibble Nibble6a NibbleEa = False;
equal_Nibble NibbleEa Nibble6a = False;
equal_Nibble Nibble6a NibbleDa = False;
equal_Nibble NibbleDa Nibble6a = False;
equal_Nibble Nibble6a NibbleCa = False;
equal_Nibble NibbleCa Nibble6a = False;
equal_Nibble Nibble6a NibbleBa = False;
equal_Nibble NibbleBa Nibble6a = False;
equal_Nibble Nibble6a NibbleAa = False;
equal_Nibble NibbleAa Nibble6a = False;
equal_Nibble Nibble6a Nibble9a = False;
equal_Nibble Nibble9a Nibble6a = False;
equal_Nibble Nibble6a Nibble8a = False;
equal_Nibble Nibble8a Nibble6a = False;
equal_Nibble Nibble6a Nibble7a = False;
equal_Nibble Nibble7a Nibble6a = False;
equal_Nibble Nibble5a NibbleFa = False;
equal_Nibble NibbleFa Nibble5a = False;
equal_Nibble Nibble5a NibbleEa = False;
equal_Nibble NibbleEa Nibble5a = False;
equal_Nibble Nibble5a NibbleDa = False;
equal_Nibble NibbleDa Nibble5a = False;
equal_Nibble Nibble5a NibbleCa = False;
equal_Nibble NibbleCa Nibble5a = False;
equal_Nibble Nibble5a NibbleBa = False;
equal_Nibble NibbleBa Nibble5a = False;
equal_Nibble Nibble5a NibbleAa = False;
equal_Nibble NibbleAa Nibble5a = False;
equal_Nibble Nibble5a Nibble9a = False;
equal_Nibble Nibble9a Nibble5a = False;
equal_Nibble Nibble5a Nibble8a = False;
equal_Nibble Nibble8a Nibble5a = False;
equal_Nibble Nibble5a Nibble7a = False;
equal_Nibble Nibble7a Nibble5a = False;
equal_Nibble Nibble5a Nibble6a = False;
equal_Nibble Nibble6a Nibble5a = False;
equal_Nibble Nibble4a NibbleFa = False;
equal_Nibble NibbleFa Nibble4a = False;
equal_Nibble Nibble4a NibbleEa = False;
equal_Nibble NibbleEa Nibble4a = False;
equal_Nibble Nibble4a NibbleDa = False;
equal_Nibble NibbleDa Nibble4a = False;
equal_Nibble Nibble4a NibbleCa = False;
equal_Nibble NibbleCa Nibble4a = False;
equal_Nibble Nibble4a NibbleBa = False;
equal_Nibble NibbleBa Nibble4a = False;
equal_Nibble Nibble4a NibbleAa = False;
equal_Nibble NibbleAa Nibble4a = False;
equal_Nibble Nibble4a Nibble9a = False;
equal_Nibble Nibble9a Nibble4a = False;
equal_Nibble Nibble4a Nibble8a = False;
equal_Nibble Nibble8a Nibble4a = False;
equal_Nibble Nibble4a Nibble7a = False;
equal_Nibble Nibble7a Nibble4a = False;
equal_Nibble Nibble4a Nibble6a = False;
equal_Nibble Nibble6a Nibble4a = False;
equal_Nibble Nibble4a Nibble5a = False;
equal_Nibble Nibble5a Nibble4a = False;
equal_Nibble Nibble3a NibbleFa = False;
equal_Nibble NibbleFa Nibble3a = False;
equal_Nibble Nibble3a NibbleEa = False;
equal_Nibble NibbleEa Nibble3a = False;
equal_Nibble Nibble3a NibbleDa = False;
equal_Nibble NibbleDa Nibble3a = False;
equal_Nibble Nibble3a NibbleCa = False;
equal_Nibble NibbleCa Nibble3a = False;
equal_Nibble Nibble3a NibbleBa = False;
equal_Nibble NibbleBa Nibble3a = False;
equal_Nibble Nibble3a NibbleAa = False;
equal_Nibble NibbleAa Nibble3a = False;
equal_Nibble Nibble3a Nibble9a = False;
equal_Nibble Nibble9a Nibble3a = False;
equal_Nibble Nibble3a Nibble8a = False;
equal_Nibble Nibble8a Nibble3a = False;
equal_Nibble Nibble3a Nibble7a = False;
equal_Nibble Nibble7a Nibble3a = False;
equal_Nibble Nibble3a Nibble6a = False;
equal_Nibble Nibble6a Nibble3a = False;
equal_Nibble Nibble3a Nibble5a = False;
equal_Nibble Nibble5a Nibble3a = False;
equal_Nibble Nibble3a Nibble4a = False;
equal_Nibble Nibble4a Nibble3a = False;
equal_Nibble Nibble2a NibbleFa = False;
equal_Nibble NibbleFa Nibble2a = False;
equal_Nibble Nibble2a NibbleEa = False;
equal_Nibble NibbleEa Nibble2a = False;
equal_Nibble Nibble2a NibbleDa = False;
equal_Nibble NibbleDa Nibble2a = False;
equal_Nibble Nibble2a NibbleCa = False;
equal_Nibble NibbleCa Nibble2a = False;
equal_Nibble Nibble2a NibbleBa = False;
equal_Nibble NibbleBa Nibble2a = False;
equal_Nibble Nibble2a NibbleAa = False;
equal_Nibble NibbleAa Nibble2a = False;
equal_Nibble Nibble2a Nibble9a = False;
equal_Nibble Nibble9a Nibble2a = False;
equal_Nibble Nibble2a Nibble8a = False;
equal_Nibble Nibble8a Nibble2a = False;
equal_Nibble Nibble2a Nibble7a = False;
equal_Nibble Nibble7a Nibble2a = False;
equal_Nibble Nibble2a Nibble6a = False;
equal_Nibble Nibble6a Nibble2a = False;
equal_Nibble Nibble2a Nibble5a = False;
equal_Nibble Nibble5a Nibble2a = False;
equal_Nibble Nibble2a Nibble4a = False;
equal_Nibble Nibble4a Nibble2a = False;
equal_Nibble Nibble2a Nibble3a = False;
equal_Nibble Nibble3a Nibble2a = False;
equal_Nibble Nibble1a NibbleFa = False;
equal_Nibble NibbleFa Nibble1a = False;
equal_Nibble Nibble1a NibbleEa = False;
equal_Nibble NibbleEa Nibble1a = False;
equal_Nibble Nibble1a NibbleDa = False;
equal_Nibble NibbleDa Nibble1a = False;
equal_Nibble Nibble1a NibbleCa = False;
equal_Nibble NibbleCa Nibble1a = False;
equal_Nibble Nibble1a NibbleBa = False;
equal_Nibble NibbleBa Nibble1a = False;
equal_Nibble Nibble1a NibbleAa = False;
equal_Nibble NibbleAa Nibble1a = False;
equal_Nibble Nibble1a Nibble9a = False;
equal_Nibble Nibble9a Nibble1a = False;
equal_Nibble Nibble1a Nibble8a = False;
equal_Nibble Nibble8a Nibble1a = False;
equal_Nibble Nibble1a Nibble7a = False;
equal_Nibble Nibble7a Nibble1a = False;
equal_Nibble Nibble1a Nibble6a = False;
equal_Nibble Nibble6a Nibble1a = False;
equal_Nibble Nibble1a Nibble5a = False;
equal_Nibble Nibble5a Nibble1a = False;
equal_Nibble Nibble1a Nibble4a = False;
equal_Nibble Nibble4a Nibble1a = False;
equal_Nibble Nibble1a Nibble3a = False;
equal_Nibble Nibble3a Nibble1a = False;
equal_Nibble Nibble1a Nibble2a = False;
equal_Nibble Nibble2a Nibble1a = False;
equal_Nibble Nibble0a NibbleFa = False;
equal_Nibble NibbleFa Nibble0a = False;
equal_Nibble Nibble0a NibbleEa = False;
equal_Nibble NibbleEa Nibble0a = False;
equal_Nibble Nibble0a NibbleDa = False;
equal_Nibble NibbleDa Nibble0a = False;
equal_Nibble Nibble0a NibbleCa = False;
equal_Nibble NibbleCa Nibble0a = False;
equal_Nibble Nibble0a NibbleBa = False;
equal_Nibble NibbleBa Nibble0a = False;
equal_Nibble Nibble0a NibbleAa = False;
equal_Nibble NibbleAa Nibble0a = False;
equal_Nibble Nibble0a Nibble9a = False;
equal_Nibble Nibble9a Nibble0a = False;
equal_Nibble Nibble0a Nibble8a = False;
equal_Nibble Nibble8a Nibble0a = False;
equal_Nibble Nibble0a Nibble7a = False;
equal_Nibble Nibble7a Nibble0a = False;
equal_Nibble Nibble0a Nibble6a = False;
equal_Nibble Nibble6a Nibble0a = False;
equal_Nibble Nibble0a Nibble5a = False;
equal_Nibble Nibble5a Nibble0a = False;
equal_Nibble Nibble0a Nibble4a = False;
equal_Nibble Nibble4a Nibble0a = False;
equal_Nibble Nibble0a Nibble3a = False;
equal_Nibble Nibble3a Nibble0a = False;
equal_Nibble Nibble0a Nibble2a = False;
equal_Nibble Nibble2a Nibble0a = False;
equal_Nibble Nibble0a Nibble1a = False;
equal_Nibble Nibble1a Nibble0a = False;
equal_Nibble NibbleFa NibbleFa = True;
equal_Nibble NibbleEa NibbleEa = True;
equal_Nibble NibbleDa NibbleDa = True;
equal_Nibble NibbleCa NibbleCa = True;
equal_Nibble NibbleBa NibbleBa = True;
equal_Nibble NibbleAa NibbleAa = True;
equal_Nibble Nibble9a Nibble9a = True;
equal_Nibble Nibble8a Nibble8a = True;
equal_Nibble Nibble7a Nibble7a = True;
equal_Nibble Nibble6a Nibble6a = True;
equal_Nibble Nibble5a Nibble5a = True;
equal_Nibble Nibble4a Nibble4a = True;
equal_Nibble Nibble3a Nibble3a = True;
equal_Nibble Nibble2a Nibble2a = True;
equal_Nibble Nibble1a Nibble1a = True;
equal_Nibble Nibble0a Nibble0a = True;

equal_Chara :: Chara -> Chara -> Bool;
equal_Chara (Chara x1 x2) (Chara y1 y2) =
  equal_Nibble x1 y1 && equal_Nibble x2 y2;

size_Itselfa :: forall a. Itselfa a -> Nat;
size_Itselfa Typea = Zero_nat;

size_Nibblea :: Nibblea -> Nat;
size_Nibblea Nibble0a = Zero_nat;
size_Nibblea Nibble1a = Zero_nat;
size_Nibblea Nibble2a = Zero_nat;
size_Nibblea Nibble3a = Zero_nat;
size_Nibblea Nibble4a = Zero_nat;
size_Nibblea Nibble5a = Zero_nat;
size_Nibblea Nibble6a = Zero_nat;
size_Nibblea Nibble7a = Zero_nat;
size_Nibblea Nibble8a = Zero_nat;
size_Nibblea Nibble9a = Zero_nat;
size_Nibblea NibbleAa = Zero_nat;
size_Nibblea NibbleBa = Zero_nat;
size_Nibblea NibbleCa = Zero_nat;
size_Nibblea NibbleDa = Zero_nat;
size_Nibblea NibbleEa = Zero_nat;
size_Nibblea NibbleFa = Zero_nat;

term_of_Nat :: Nata -> Terma;
term_of_Nat (Suca a) =
  Appa (Consta "Rationals.Nat.Suc"
         (Typerep "fun"
           [Typerep "Rationals.Nat" [], Typerep "Rationals.Nat" []]))
    (term_of_Nat a);
term_of_Nat Zero = Consta "Rationals.Nat.Zero" (Typerep "Rationals.Nat" []);

term_of_Rat :: Rat -> Terma;
term_of_Rat (Fract a b) =
  Appa (Appa (Consta "Rationals.Rat.Fract"
               (Typerep "fun"
                 [Typerep "Int.int" [],
                   Typerep "fun"
                     [Typerep "Int.int" [], Typerep "Rationals.Rat" []]]))
         (term_of_int a))
    (term_of_int b);

typerep_Nat :: Itself Nata -> Typerepa;
typerep_Nat t = Typerep "Rationals.Nat" [];

typerep_Rat :: Itself Rat -> Typerepa;
typerep_Rat t = Typerep "Rationals.Rat" [];

equal_Itself :: forall a. Itselfa a -> Itselfa a -> Bool;
equal_Itself Typea Typea = True;

random_Chara ::
  Natural -> (Natural, Natural) -> ((Chara, () -> Terma), (Natural, Natural));
random_Chara i = random_aux_Chara i i;

size_Typerepa :: Typerepb -> Nat;
size_Typerepa (Typerepa x1 x2) =
  plus_nat (size_list size_Typerepa x2) (Suc Zero_nat);

term_of_Term :: Term -> Terma;
term_of_Term (App a b) =
  Appa (Appa (Consta "Rationals.Term.App"
               (Typerep "fun"
                 [Typerep "Rationals.Term" [],
                   Typerep "fun"
                     [Typerep "Rationals.Term" [],
                       Typerep "Rationals.Term" []]]))
         (term_of_Term a))
    (term_of_Term b);
term_of_Term (Const a b) =
  Appa (Appa (Consta "Rationals.Term.Const"
               (Typerep "fun"
                 [Typerep "List.list" [Typerep "String.char" []],
                   Typerep "fun"
                     [Typerep "Rationals.Typerep" [],
                       Typerep "Rationals.Term" []]]))
         (term_of_list a))
    (term_of_Typerep b);

typerep_Term :: Itself Term -> Typerepa;
typerep_Term t = Typerep "Rationals.Term" [];

one_integer :: Integer;
one_integer = (1 :: Integer);

full_exhaustive_int ::
  ((Int, () -> Terma) -> Maybe (Bool, [Terma])) ->
    Int -> Int -> Maybe (Bool, [Terma]);
full_exhaustive_int f d i =
  (if less_int d i then Nothing
    else (case f (i, (\ _ -> term_of_int i)) of {
           Nothing -> full_exhaustive_int f d (plus_int i (Pos One));
           Just a -> Just a;
         }));

random_Itself ::
  forall a.
    (Typerep a) => Natural ->
                     (Natural, Natural) ->
                       ((Itselfa a, () -> Terma), (Natural, Natural));
random_Itself i = random_aux_Itself i i;

term_of_Nibble :: Nibblea -> Terma;
term_of_Nibble NibbleFa =
  Consta "Rationals.Nibble.NibbleF" (Typerep "Rationals.Nibble" []);
term_of_Nibble NibbleEa =
  Consta "Rationals.Nibble.NibbleE" (Typerep "Rationals.Nibble" []);
term_of_Nibble NibbleDa =
  Consta "Rationals.Nibble.NibbleD" (Typerep "Rationals.Nibble" []);
term_of_Nibble NibbleCa =
  Consta "Rationals.Nibble.NibbleC" (Typerep "Rationals.Nibble" []);
term_of_Nibble NibbleBa =
  Consta "Rationals.Nibble.NibbleB" (Typerep "Rationals.Nibble" []);
term_of_Nibble NibbleAa =
  Consta "Rationals.Nibble.NibbleA" (Typerep "Rationals.Nibble" []);
term_of_Nibble Nibble9a =
  Consta "Rationals.Nibble.Nibble9" (Typerep "Rationals.Nibble" []);
term_of_Nibble Nibble8a =
  Consta "Rationals.Nibble.Nibble8" (Typerep "Rationals.Nibble" []);
term_of_Nibble Nibble7a =
  Consta "Rationals.Nibble.Nibble7" (Typerep "Rationals.Nibble" []);
term_of_Nibble Nibble6a =
  Consta "Rationals.Nibble.Nibble6" (Typerep "Rationals.Nibble" []);
term_of_Nibble Nibble5a =
  Consta "Rationals.Nibble.Nibble5" (Typerep "Rationals.Nibble" []);
term_of_Nibble Nibble4a =
  Consta "Rationals.Nibble.Nibble4" (Typerep "Rationals.Nibble" []);
term_of_Nibble Nibble3a =
  Consta "Rationals.Nibble.Nibble3" (Typerep "Rationals.Nibble" []);
term_of_Nibble Nibble2a =
  Consta "Rationals.Nibble.Nibble2" (Typerep "Rationals.Nibble" []);
term_of_Nibble Nibble1a =
  Consta "Rationals.Nibble.Nibble1" (Typerep "Rationals.Nibble" []);
term_of_Nibble Nibble0a =
  Consta "Rationals.Nibble.Nibble0" (Typerep "Rationals.Nibble" []);

term_of_Chara :: Chara -> Terma;
term_of_Chara (Chara a b) =
  Appa (Appa (Consta "Rationals.Chara.Chara"
               (Typerep "fun"
                 [Typerep "Rationals.Nibble" [],
                   Typerep "fun"
                     [Typerep "Rationals.Nibble" [],
                       Typerep "Rationals.Chara" []]]))
         (term_of_Nibble a))
    (term_of_Nibble b);

typerep_Chara :: Itself Chara -> Typerepa;
typerep_Chara t = Typerep "Rationals.Chara" [];

term_of_Itself :: forall a. (Typerep a) => Itselfa a -> Terma;
term_of_Itself Typea =
  Consta "Rationals.Itself.Type"
    (Typerep "Rationals.Itself" [(typerep :: Itself a -> Typerepa) Type]);

typerep_Itself :: forall a. (Typerep a) => Itself (Itselfa a) -> Typerepa;
typerep_Itself t =
  Typerep "Rationals.Itself" [(typerep :: Itself a -> Typerepa) Type];

typerep_Nibble :: Itself Nibblea -> Typerepa;
typerep_Nibble t = Typerep "Rationals.Nibble" [];

partial_term_of_int :: Itself Int -> Narrowing_term -> Terma;
partial_term_of_int ty (Narrowing_constructor i []) =
  (if mod_integer i (2 :: Integer) == (0 :: Integer)
    then term_of_int (div_inta (uminus_int (int_of_integer i)) (Pos (Bit0 One)))
    else term_of_int
           (div_inta (plus_int (int_of_integer i) (Pos One)) (Pos (Bit0 One))));
partial_term_of_int ty (Narrowing_variable p t) =
  Free "_" (Typerep "Int.int" []);

narrowing_Itself ::
  forall a. (Typerep a) => Integer -> Narrowing_cons (Itselfa a);
narrowing_Itself = cons Typea;

narrowing_Nibble :: Integer -> Narrowing_cons Nibblea;
narrowing_Nibble =
  sum (cons Nibble0a)
    (sum (cons Nibble1a)
      (sum (cons Nibble2a)
        (sum (cons Nibble3a)
          (sum (cons Nibble4a)
            (sum (cons Nibble5a)
              (sum (cons Nibble6a)
                (sum (cons Nibble7a)
                  (sum (cons Nibble8a)
                    (sum (cons Nibble9a)
                      (sum (cons NibbleAa)
                        (sum (cons NibbleBa)
                          (sum (cons NibbleCa)
                            (sum (cons NibbleDa)
                              (sum (cons NibbleEa)
                                (cons NibbleFa)))))))))))))));

full_exhaustive_Nat ::
  ((Nata, () -> Terma) -> Maybe (Bool, [Terma])) ->
    Natural -> Maybe (Bool, [Terma]);
full_exhaustive_Nat f i =
  (if less_natural zero_natural i
    then (case f (Zero,
                   (\ _ ->
                     Consta "Rationals.Nat.Zero" (Typerep "Rationals.Nat" [])))
           of {
           Nothing ->
             full_exhaustive_Nat
               (\ (uu, uua) ->
                 f (Suca uu,
                     (\ _ ->
                       Appa (Consta "Rationals.Nat.Suc"
                              (Typerep "fun"
                                [Typerep "Rationals.Nat" [],
                                  Typerep "Rationals.Nat" []]))
                         (uua ()))))
               (minus_natural i one_natural);
           Just a -> Just a;
         })
    else Nothing);

full_exhaustive_inta ::
  ((Int, () -> Terma) -> Maybe (Bool, [Terma])) ->
    Natural -> Maybe (Bool, [Terma]);
full_exhaustive_inta f d =
  full_exhaustive_int f (int_of_integer (integer_of_natural d))
    (uminus_int (int_of_integer (integer_of_natural d)));

full_exhaustive_Rat ::
  ((Rat, () -> Terma) -> Maybe (Bool, [Terma])) ->
    Natural -> Maybe (Bool, [Terma]);
full_exhaustive_Rat f i =
  (if less_natural zero_natural i
    then full_exhaustive_inta
           (\ (uu, uua) ->
             full_exhaustive_inta
               (\ (uub, uuc) ->
                 f (Fract uu uub,
                     (\ _ ->
                       Appa (Appa (Consta "Rationals.Rat.Fract"
                                    (Typerep "fun"
                                      [Typerep "Int.int" [],
Typerep "fun" [Typerep "Int.int" [], Typerep "Rationals.Rat" []]]))
                              (uua ()))
                         (uuc ()))))
               (minus_natural i one_natural))
           (minus_natural i one_natural)
    else Nothing);

partial_term_of_Nat :: Itself Nata -> Narrowing_term -> Terma;
partial_term_of_Nat ty (Narrowing_constructor (1 :: Integer) [a]) =
  Appa (Consta "Rationals.Nat.Suc"
         (Typerep "fun"
           [Typerep "Rationals.Nat" [], Typerep "Rationals.Nat" []]))
    (partial_term_of_Nat Type a);
partial_term_of_Nat ty (Narrowing_constructor (0 :: Integer) []) =
  Consta "Rationals.Nat.Zero" (Typerep "Rationals.Nat" []);
partial_term_of_Nat ty (Narrowing_variable p tt) =
  Free "_" (Typerep "Rationals.Nat" []);

partial_term_of_Rat :: Itself Rat -> Narrowing_term -> Terma;
partial_term_of_Rat ty (Narrowing_constructor (0 :: Integer) [b, a]) =
  Appa (Appa (Consta "Rationals.Rat.Fract"
               (Typerep "fun"
                 [Typerep "Int.int" [],
                   Typerep "fun"
                     [Typerep "Int.int" [], Typerep "Rationals.Rat" []]]))
         (partial_term_of_int Type a))
    (partial_term_of_int Type b);
partial_term_of_Rat ty (Narrowing_variable p tt) =
  Free "_" (Typerep "Rationals.Rat" []);

partial_term_of_Term :: Itself Term -> Narrowing_term -> Terma;
partial_term_of_Term ty (Narrowing_constructor (1 :: Integer) [b, a]) =
  Appa (Appa (Consta "Rationals.Term.App"
               (Typerep "fun"
                 [Typerep "Rationals.Term" [],
                   Typerep "fun"
                     [Typerep "Rationals.Term" [],
                       Typerep "Rationals.Term" []]]))
         (partial_term_of_Term Type a))
    (partial_term_of_Term Type b);
partial_term_of_Term ty (Narrowing_constructor (0 :: Integer) [b, a]) =
  Appa (Appa (Consta "Rationals.Term.Const"
               (Typerep "fun"
                 [Typerep "List.list" [Typerep "String.char" []],
                   Typerep "fun"
                     [Typerep "Rationals.Typerep" [],
                       Typerep "Rationals.Term" []]]))
         ((partial_term_of_list :: Itself [Char] -> Narrowing_term -> Terma)
           Type a))
    (partial_term_of_Typerep Type b);
partial_term_of_Term ty (Narrowing_variable p tt) =
  Free "_" (Typerep "Rationals.Term" []);

full_exhaustive_Nibble ::
  ((Nibblea, () -> Terma) -> Maybe (Bool, [Terma])) ->
    Natural -> Maybe (Bool, [Terma]);
full_exhaustive_Nibble f i =
  (if less_natural zero_natural i
    then (case f (Nibble0a,
                   (\ _ ->
                     Consta "Rationals.Nibble.Nibble0"
                       (Typerep "Rationals.Nibble" [])))
           of {
           Nothing ->
             (case f (Nibble1a,
                       (\ _ ->
                         Consta "Rationals.Nibble.Nibble1"
                           (Typerep "Rationals.Nibble" [])))
               of {
               Nothing ->
                 (case f (Nibble2a,
                           (\ _ ->
                             Consta "Rationals.Nibble.Nibble2"
                               (Typerep "Rationals.Nibble" [])))
                   of {
                   Nothing ->
                     (case f (Nibble3a,
                               (\ _ ->
                                 Consta "Rationals.Nibble.Nibble3"
                                   (Typerep "Rationals.Nibble" [])))
                       of {
                       Nothing ->
                         (case f (Nibble4a,
                                   (\ _ ->
                                     Consta "Rationals.Nibble.Nibble4"
                                       (Typerep "Rationals.Nibble" [])))
                           of {
                           Nothing ->
                             (case f (Nibble5a,
                                       (\ _ ->
 Consta "Rationals.Nibble.Nibble5" (Typerep "Rationals.Nibble" [])))
                               of {
                               Nothing ->
                                 (case f
 (Nibble6a,
   (\ _ -> Consta "Rationals.Nibble.Nibble6" (Typerep "Rationals.Nibble" [])))
                                   of {
                                   Nothing ->
                                     (case f
     (Nibble7a,
       (\ _ ->
         Consta "Rationals.Nibble.Nibble7" (Typerep "Rationals.Nibble" [])))
                                       of {
                                       Nothing ->
 (case f (Nibble8a,
           (\ _ ->
             Consta "Rationals.Nibble.Nibble8" (Typerep "Rationals.Nibble" [])))
   of {
   Nothing ->
     (case f (Nibble9a,
               (\ _ ->
                 Consta "Rationals.Nibble.Nibble9"
                   (Typerep "Rationals.Nibble" [])))
       of {
       Nothing ->
         (case f (NibbleAa,
                   (\ _ ->
                     Consta "Rationals.Nibble.NibbleA"
                       (Typerep "Rationals.Nibble" [])))
           of {
           Nothing ->
             (case f (NibbleBa,
                       (\ _ ->
                         Consta "Rationals.Nibble.NibbleB"
                           (Typerep "Rationals.Nibble" [])))
               of {
               Nothing ->
                 (case f (NibbleCa,
                           (\ _ ->
                             Consta "Rationals.Nibble.NibbleC"
                               (Typerep "Rationals.Nibble" [])))
                   of {
                   Nothing ->
                     (case f (NibbleDa,
                               (\ _ ->
                                 Consta "Rationals.Nibble.NibbleD"
                                   (Typerep "Rationals.Nibble" [])))
                       of {
                       Nothing ->
                         (case f (NibbleEa,
                                   (\ _ ->
                                     Consta "Rationals.Nibble.NibbleE"
                                       (Typerep "Rationals.Nibble" [])))
                           of {
                           Nothing ->
                             f (NibbleFa,
                                 (\ _ ->
                                   Consta "Rationals.Nibble.NibbleF"
                                     (Typerep "Rationals.Nibble" [])));
                           Just a -> Just a;
                         });
                       Just a -> Just a;
                     });
                   Just a -> Just a;
                 });
               Just a -> Just a;
             });
           Just a -> Just a;
         });
       Just a -> Just a;
     });
   Just a -> Just a;
 });
                                       Just a -> Just a;
                                     });
                                   Just a -> Just a;
                                 });
                               Just a -> Just a;
                             });
                           Just a -> Just a;
                         });
                       Just a -> Just a;
                     });
                   Just a -> Just a;
                 });
               Just a -> Just a;
             });
           Just a -> Just a;
         })
    else Nothing);

full_exhaustive_Chara ::
  ((Chara, () -> Terma) -> Maybe (Bool, [Terma])) ->
    Natural -> Maybe (Bool, [Terma]);
full_exhaustive_Chara f i =
  (if less_natural zero_natural i
    then full_exhaustive_Nibble
           (\ (uu, uua) ->
             full_exhaustive_Nibble
               (\ (uub, uuc) ->
                 f (Chara uu uub,
                     (\ _ ->
                       Appa (Appa (Consta "Rationals.Chara.Chara"
                                    (Typerep "fun"
                                      [Typerep "Rationals.Nibble" [],
Typerep "fun" [Typerep "Rationals.Nibble" [], Typerep "Rationals.Chara" []]]))
                              (uua ()))
                         (uuc ()))))
               (minus_natural i one_natural))
           (minus_natural i one_natural)
    else Nothing);

partial_term_of_Nibble :: Itself Nibblea -> Narrowing_term -> Terma;
partial_term_of_Nibble ty (Narrowing_constructor (15 :: Integer) []) =
  Consta "Rationals.Nibble.NibbleF" (Typerep "Rationals.Nibble" []);
partial_term_of_Nibble ty (Narrowing_constructor (14 :: Integer) []) =
  Consta "Rationals.Nibble.NibbleE" (Typerep "Rationals.Nibble" []);
partial_term_of_Nibble ty (Narrowing_constructor (13 :: Integer) []) =
  Consta "Rationals.Nibble.NibbleD" (Typerep "Rationals.Nibble" []);
partial_term_of_Nibble ty (Narrowing_constructor (12 :: Integer) []) =
  Consta "Rationals.Nibble.NibbleC" (Typerep "Rationals.Nibble" []);
partial_term_of_Nibble ty (Narrowing_constructor (11 :: Integer) []) =
  Consta "Rationals.Nibble.NibbleB" (Typerep "Rationals.Nibble" []);
partial_term_of_Nibble ty (Narrowing_constructor (10 :: Integer) []) =
  Consta "Rationals.Nibble.NibbleA" (Typerep "Rationals.Nibble" []);
partial_term_of_Nibble ty (Narrowing_constructor (9 :: Integer) []) =
  Consta "Rationals.Nibble.Nibble9" (Typerep "Rationals.Nibble" []);
partial_term_of_Nibble ty (Narrowing_constructor (8 :: Integer) []) =
  Consta "Rationals.Nibble.Nibble8" (Typerep "Rationals.Nibble" []);
partial_term_of_Nibble ty (Narrowing_constructor (7 :: Integer) []) =
  Consta "Rationals.Nibble.Nibble7" (Typerep "Rationals.Nibble" []);
partial_term_of_Nibble ty (Narrowing_constructor (6 :: Integer) []) =
  Consta "Rationals.Nibble.Nibble6" (Typerep "Rationals.Nibble" []);
partial_term_of_Nibble ty (Narrowing_constructor (5 :: Integer) []) =
  Consta "Rationals.Nibble.Nibble5" (Typerep "Rationals.Nibble" []);
partial_term_of_Nibble ty (Narrowing_constructor (4 :: Integer) []) =
  Consta "Rationals.Nibble.Nibble4" (Typerep "Rationals.Nibble" []);
partial_term_of_Nibble ty (Narrowing_constructor (3 :: Integer) []) =
  Consta "Rationals.Nibble.Nibble3" (Typerep "Rationals.Nibble" []);
partial_term_of_Nibble ty (Narrowing_constructor (2 :: Integer) []) =
  Consta "Rationals.Nibble.Nibble2" (Typerep "Rationals.Nibble" []);
partial_term_of_Nibble ty (Narrowing_constructor (1 :: Integer) []) =
  Consta "Rationals.Nibble.Nibble1" (Typerep "Rationals.Nibble" []);
partial_term_of_Nibble ty (Narrowing_constructor (0 :: Integer) []) =
  Consta "Rationals.Nibble.Nibble0" (Typerep "Rationals.Nibble" []);
partial_term_of_Nibble ty (Narrowing_variable p tt) =
  Free "_" (Typerep "Rationals.Nibble" []);

partial_term_of_Chara :: Itself Chara -> Narrowing_term -> Terma;
partial_term_of_Chara ty (Narrowing_constructor (0 :: Integer) [b, a]) =
  Appa (Appa (Consta "Rationals.Chara.Chara"
               (Typerep "fun"
                 [Typerep "Rationals.Nibble" [],
                   Typerep "fun"
                     [Typerep "Rationals.Nibble" [],
                       Typerep "Rationals.Chara" []]]))
         (partial_term_of_Nibble Type a))
    (partial_term_of_Nibble Type b);
partial_term_of_Chara ty (Narrowing_variable p tt) =
  Free "_" (Typerep "Rationals.Chara" []);

typerep_Nat_IITN_Nat :: Itself Nat_IITN_Nat -> Typerepa;
typerep_Nat_IITN_Nat t = Typerep "Rationals.Nat.Nat_IITN_Nat" [];

typerep_Rat_IITN_Rat :: Itself Rat_IITN_Rat -> Typerepa;
typerep_Rat_IITN_Rat t = Typerep "Rationals.Rat.Rat_IITN_Rat" [];

full_exhaustive_Itself ::
  forall a.
    (Typerep a) => ((Itselfa a, () -> Terma) -> Maybe (Bool, [Terma])) ->
                     Natural -> Maybe (Bool, [Terma]);
full_exhaustive_Itself f i =
  (if less_natural zero_natural i
    then f (Typea,
             (\ _ ->
               Consta "Rationals.Itself.Type"
                 (Typerep "Rationals.Itself"
                   [(typerep :: Itself a -> Typerepa) Type])))
    else Nothing);

partial_term_of_Itself ::
  forall a. (Typerep a) => Itself (Itselfa a) -> Narrowing_term -> Terma;
partial_term_of_Itself ty (Narrowing_constructor (0 :: Integer) []) =
  Consta "Rationals.Itself.Type"
    (Typerep "Rationals.Itself" [(typerep :: Itself a -> Typerepa) Type]);
partial_term_of_Itself ty (Narrowing_variable p tt) =
  Free "_"
    (Typerep "Rationals.Itself" [(typerep :: Itself a -> Typerepa) Type]);

typerep_Term_pre_Term ::
  forall a. (Typerep a) => Itself (Term_pre_Term a) -> Typerepa;
typerep_Term_pre_Term t =
  Typerep "Rationals.Term.Term_pre_Term"
    [(typerep :: Itself a -> Typerepa) Type];

typerep_Term_IITN_Term :: Itself Term_IITN_Term -> Typerepa;
typerep_Term_IITN_Term t = Typerep "Rationals.Term.Term_IITN_Term" [];

typerep_Chara_IITN_Chara :: Itself Chara_IITN_Chara -> Typerepa;
typerep_Chara_IITN_Chara t = Typerep "Rationals.Chara.Chara_IITN_Chara" [];

typerep_Itself_pre_Itself ::
  forall a b.
    (Typerep a, Typerep b) => Itself (Itself_pre_Itself a b) -> Typerepa;
typerep_Itself_pre_Itself t =
  Typerep "Rationals.Itself.Itself_pre_Itself"
    [(typerep :: Itself a -> Typerepa) Type,
      (typerep :: Itself b -> Typerepa) Type];

typerep_Nibble_pre_Nibble :: Itself Nibble_pre_Nibble -> Typerepa;
typerep_Nibble_pre_Nibble t = Typerep "Rationals.Nibble.Nibble_pre_Nibble" [];

typerep_Itself_IITN_Itself ::
  forall a. (Typerep a) => Itself (Itself_IITN_Itself a) -> Typerepa;
typerep_Itself_IITN_Itself t =
  Typerep "Rationals.Itself.Itself_IITN_Itself"
    [(typerep :: Itself a -> Typerepa) Type];

typerep_Nibble_IITN_Nibble :: Itself Nibble_IITN_Nibble -> Typerepa;
typerep_Nibble_IITN_Nibble t = Typerep "Rationals.Nibble.Nibble_IITN_Nibble" [];

typerep_Typerep_IITN_Typerep :: Itself Typerep_IITN_Typerep -> Typerepa;
typerep_Typerep_IITN_Typerep t =
  Typerep "Rationals.Typerep.Typerep_IITN_Typerep" [];

}
