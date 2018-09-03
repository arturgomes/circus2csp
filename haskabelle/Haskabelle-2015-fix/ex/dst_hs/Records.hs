{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Records(Typerepa(..), Itself(..), Typerep(..), Nibble(..), Char(..),
           typerep_fun, Num(..), plus_num, times_num, Int(..), times_int,
           Times(..), one_int, One(..), uminus_int, bitM, dup, minus_int, sub,
           plus_int, equal_num, equal_int, less_num, less_eq_num, less_int,
           sgn_int, abs_int, apsnd, Ord(..), Plus(..), Numeral, numeral,
           Minus(..), Zero(..), Monoid_add, Semiring_1, Div(..),
           Semiring_numeral_div, divmod_step, divmod, less_eq_int, divmod_abs,
           divmod_int, div_int, mod_int, equal_nibble, equal_char, typerep_char,
           Term(..), term_of_nibble, Nat(..), minus_nat, equal_nat, less_nat,
           less_eq_nat, divmod_nat, div_nat, enum_nibble, mod_nat, plus_nat,
           one_nat, nat_of_num, nth, nibble_of_nat, nat_of_char, case_char,
           term_of_char, Term_of(..), enum_char, scomp, gen_length, size_list,
           of_nat_aux, of_nat, Natural(..), one_integer, natural_of_nat,
           integer_of_natural, sgn_integer, abs_integer, divmod_integer,
           nat_of_integer, nat_of_natural, times_natural, plus_natural,
           one_natural, mod_integer, mod_natural, max, natural_of_integer,
           minus_natural, equal_natural, zero_natural, iterate, div_integer,
           div_natural, less_natural, minus_shift, next, less_eq_natural, log,
           range, select, random_char, Random(..), Narrowing_type(..),
           Narrowing_term(..), Partial_term_of(..), partial_term_of_nibble,
           partial_term_of_char, Full_exhaustive(..), full_exhaustive_nibble,
           times_nat, nat_of_nibble, char_of_nat, typerep_nibble,
           full_exhaustive_char, Narrowing_cons(..), Narrowing(..), Set(..),
           Identity(..), MyRecord(..), MyRecord_pre_MyRecord,
           Identity_IITN_Identity, MyRecord_IITN_MyRecord, ball, foldr,
           removeAll, member, inserta, insert, pick, this, constr,
           update_common2, update_common1, update, aField1, bField1, bField2,
           common1, common2, pattern, update_this, collapse, valapp, listsum,
           select_weight, random_aux_list, bot_set, set_Identity, pred_Identity,
           update_aField1, update_bField1, update_bField2, sum, cons,
           int_of_integer, random_aux_Identity, random_bool, term_of_num,
           term_of_int, random_int, random_list, random_aux_MyRecord,
           map_Identity, rec_Identity, rel_Identity, rec_MyRecord, non_empty,
           size_Identity, size_MyRecord, drawn_from, around_zero, term_of_bool,
           term_of_list, narrowing_bool, size_Identitya, size_MyRecorda,
           full_exhaustive_int, equal_Identity, equal_MyRecord, random_Identity,
           random_MyRecord, narrowing_nibble, term_of_Identity,
           term_of_MyRecord, typerep_Identity, typerep_MyRecord,
           partial_term_of_int, full_exhaustive_bool, partial_term_of_bool,
           full_exhaustive_list, partial_term_of_list, full_exhaustive_Identity,
           full_exhaustive_inta, full_exhaustive_MyRecord,
           partial_term_of_Identity, partial_term_of_MyRecord,
           typerep_MyRecord_pre_MyRecord, typerep_Identity_IITN_Identity,
           typerep_MyRecord_IITN_MyRecord)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;

data Typerepa = Typerep String [Typerepa];

data Itself a = Type;

class Typerep a where {
  typerep :: Itself a -> Typerepa;
};

data Nibble = Nibble0 | Nibble1 | Nibble2 | Nibble3 | Nibble4 | Nibble5
  | Nibble6 | Nibble7 | Nibble8 | Nibble9 | NibbleA | NibbleB | NibbleC
  | NibbleD | NibbleE | NibbleF;

data Char = Char Nibble Nibble;

typerep_fun ::
  forall a b. (Typerep a, Typerep b) => Itself (a -> b) -> Typerepa;
typerep_fun t =
  Typerep "fun"
    [(typerep :: Itself a -> Typerepa) Type,
      (typerep :: Itself b -> Typerepa) Type];

instance (Typerep a, Typerep b) => Typerep (a -> b) where {
  typerep = typerep_fun;
};

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

equal_char :: Char -> Char -> Bool;
equal_char (Char x1 x2) (Char y1 y2) = equal_nibble x1 y1 && equal_nibble x2 y2;

instance Eq Char where {
  a == b = equal_char a b;
};

typerep_char :: Itself Char -> Typerepa;
typerep_char t = Typerep "String.char" [];

instance Typerep Char where {
  typerep = typerep_char;
};

data Term = Const String Typerepa | App Term Term | Abs String Typerepa Term
  | Free String Typerepa;

term_of_nibble :: Nibble -> Term;
term_of_nibble NibbleF =
  Const "String.nibble.NibbleF" (Typerep "String.nibble" []);
term_of_nibble NibbleE =
  Const "String.nibble.NibbleE" (Typerep "String.nibble" []);
term_of_nibble NibbleD =
  Const "String.nibble.NibbleD" (Typerep "String.nibble" []);
term_of_nibble NibbleC =
  Const "String.nibble.NibbleC" (Typerep "String.nibble" []);
term_of_nibble NibbleB =
  Const "String.nibble.NibbleB" (Typerep "String.nibble" []);
term_of_nibble NibbleA =
  Const "String.nibble.NibbleA" (Typerep "String.nibble" []);
term_of_nibble Nibble9 =
  Const "String.nibble.Nibble9" (Typerep "String.nibble" []);
term_of_nibble Nibble8 =
  Const "String.nibble.Nibble8" (Typerep "String.nibble" []);
term_of_nibble Nibble7 =
  Const "String.nibble.Nibble7" (Typerep "String.nibble" []);
term_of_nibble Nibble6 =
  Const "String.nibble.Nibble6" (Typerep "String.nibble" []);
term_of_nibble Nibble5 =
  Const "String.nibble.Nibble5" (Typerep "String.nibble" []);
term_of_nibble Nibble4 =
  Const "String.nibble.Nibble4" (Typerep "String.nibble" []);
term_of_nibble Nibble3 =
  Const "String.nibble.Nibble3" (Typerep "String.nibble" []);
term_of_nibble Nibble2 =
  Const "String.nibble.Nibble2" (Typerep "String.nibble" []);
term_of_nibble Nibble1 =
  Const "String.nibble.Nibble1" (Typerep "String.nibble" []);
term_of_nibble Nibble0 =
  Const "String.nibble.Nibble0" (Typerep "String.nibble" []);

data Nat = Zero_nat | Suc Nat;

minus_nat :: Nat -> Nat -> Nat;
minus_nat (Suc m) (Suc n) = minus_nat m n;
minus_nat Zero_nat n = Zero_nat;
minus_nat m Zero_nat = m;

equal_nat :: Nat -> Nat -> Bool;
equal_nat Zero_nat (Suc x2) = False;
equal_nat (Suc x2) Zero_nat = False;
equal_nat (Suc x2) (Suc y2) = equal_nat x2 y2;
equal_nat Zero_nat Zero_nat = True;

less_nat :: Nat -> Nat -> Bool;
less_nat m (Suc n) = less_eq_nat m n;
less_nat n Zero_nat = False;

less_eq_nat :: Nat -> Nat -> Bool;
less_eq_nat (Suc m) n = less_nat m n;
less_eq_nat Zero_nat n = True;

divmod_nat :: Nat -> Nat -> (Nat, Nat);
divmod_nat m n =
  (if equal_nat n Zero_nat || less_nat m n then (Zero_nat, m)
    else let {
           a = divmod_nat (minus_nat m n) n;
           (q, aa) = a;
         } in (Suc q, aa));

div_nat :: Nat -> Nat -> Nat;
div_nat m n = fst (divmod_nat m n);

enum_nibble :: [Nibble];
enum_nibble =
  [Nibble0, Nibble1, Nibble2, Nibble3, Nibble4, Nibble5, Nibble6, Nibble7,
    Nibble8, Nibble9, NibbleA, NibbleB, NibbleC, NibbleD, NibbleE, NibbleF];

mod_nat :: Nat -> Nat -> Nat;
mod_nat m n = snd (divmod_nat m n);

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
  nth enum_nibble (mod_nat n (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 One))))));

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

term_of_char :: Char -> Term;
term_of_char c =
  case_char
    (\ x y ->
      App (App (Const "String.char.Char"
                 (Typerep "fun"
                   [Typerep "String.nibble" [],
                     Typerep "fun"
                       [Typerep "String.nibble" [], Typerep "String.char" []]]))
            (term_of_nibble x))
        (term_of_nibble y))
    c;

class (Typerep a) => Term_of a where {
  term_of :: a -> Term;
};

instance Term_of Char where {
  term_of = term_of_char;
};

enum_char :: [Char];
enum_char =
  [Char Nibble0 Nibble0, Char Nibble0 Nibble1, Char Nibble0 Nibble2,
    Char Nibble0 Nibble3, Char Nibble0 Nibble4, Char Nibble0 Nibble5,
    Char Nibble0 Nibble6, Char Nibble0 Nibble7, Char Nibble0 Nibble8,
    Char Nibble0 Nibble9, Char Nibble0 NibbleA, Char Nibble0 NibbleB,
    Char Nibble0 NibbleC, Char Nibble0 NibbleD, Char Nibble0 NibbleE,
    Char Nibble0 NibbleF, Char Nibble1 Nibble0, Char Nibble1 Nibble1,
    Char Nibble1 Nibble2, Char Nibble1 Nibble3, Char Nibble1 Nibble4,
    Char Nibble1 Nibble5, Char Nibble1 Nibble6, Char Nibble1 Nibble7,
    Char Nibble1 Nibble8, Char Nibble1 Nibble9, Char Nibble1 NibbleA,
    Char Nibble1 NibbleB, Char Nibble1 NibbleC, Char Nibble1 NibbleD,
    Char Nibble1 NibbleE, Char Nibble1 NibbleF, Char Nibble2 Nibble0,
    Char Nibble2 Nibble1, Char Nibble2 Nibble2, Char Nibble2 Nibble3,
    Char Nibble2 Nibble4, Char Nibble2 Nibble5, Char Nibble2 Nibble6,
    Char Nibble2 Nibble7, Char Nibble2 Nibble8, Char Nibble2 Nibble9,
    Char Nibble2 NibbleA, Char Nibble2 NibbleB, Char Nibble2 NibbleC,
    Char Nibble2 NibbleD, Char Nibble2 NibbleE, Char Nibble2 NibbleF,
    Char Nibble3 Nibble0, Char Nibble3 Nibble1, Char Nibble3 Nibble2,
    Char Nibble3 Nibble3, Char Nibble3 Nibble4, Char Nibble3 Nibble5,
    Char Nibble3 Nibble6, Char Nibble3 Nibble7, Char Nibble3 Nibble8,
    Char Nibble3 Nibble9, Char Nibble3 NibbleA, Char Nibble3 NibbleB,
    Char Nibble3 NibbleC, Char Nibble3 NibbleD, Char Nibble3 NibbleE,
    Char Nibble3 NibbleF, Char Nibble4 Nibble0, Char Nibble4 Nibble1,
    Char Nibble4 Nibble2, Char Nibble4 Nibble3, Char Nibble4 Nibble4,
    Char Nibble4 Nibble5, Char Nibble4 Nibble6, Char Nibble4 Nibble7,
    Char Nibble4 Nibble8, Char Nibble4 Nibble9, Char Nibble4 NibbleA,
    Char Nibble4 NibbleB, Char Nibble4 NibbleC, Char Nibble4 NibbleD,
    Char Nibble4 NibbleE, Char Nibble4 NibbleF, Char Nibble5 Nibble0,
    Char Nibble5 Nibble1, Char Nibble5 Nibble2, Char Nibble5 Nibble3,
    Char Nibble5 Nibble4, Char Nibble5 Nibble5, Char Nibble5 Nibble6,
    Char Nibble5 Nibble7, Char Nibble5 Nibble8, Char Nibble5 Nibble9,
    Char Nibble5 NibbleA, Char Nibble5 NibbleB, Char Nibble5 NibbleC,
    Char Nibble5 NibbleD, Char Nibble5 NibbleE, Char Nibble5 NibbleF,
    Char Nibble6 Nibble0, Char Nibble6 Nibble1, Char Nibble6 Nibble2,
    Char Nibble6 Nibble3, Char Nibble6 Nibble4, Char Nibble6 Nibble5,
    Char Nibble6 Nibble6, Char Nibble6 Nibble7, Char Nibble6 Nibble8,
    Char Nibble6 Nibble9, Char Nibble6 NibbleA, Char Nibble6 NibbleB,
    Char Nibble6 NibbleC, Char Nibble6 NibbleD, Char Nibble6 NibbleE,
    Char Nibble6 NibbleF, Char Nibble7 Nibble0, Char Nibble7 Nibble1,
    Char Nibble7 Nibble2, Char Nibble7 Nibble3, Char Nibble7 Nibble4,
    Char Nibble7 Nibble5, Char Nibble7 Nibble6, Char Nibble7 Nibble7,
    Char Nibble7 Nibble8, Char Nibble7 Nibble9, Char Nibble7 NibbleA,
    Char Nibble7 NibbleB, Char Nibble7 NibbleC, Char Nibble7 NibbleD,
    Char Nibble7 NibbleE, Char Nibble7 NibbleF, Char Nibble8 Nibble0,
    Char Nibble8 Nibble1, Char Nibble8 Nibble2, Char Nibble8 Nibble3,
    Char Nibble8 Nibble4, Char Nibble8 Nibble5, Char Nibble8 Nibble6,
    Char Nibble8 Nibble7, Char Nibble8 Nibble8, Char Nibble8 Nibble9,
    Char Nibble8 NibbleA, Char Nibble8 NibbleB, Char Nibble8 NibbleC,
    Char Nibble8 NibbleD, Char Nibble8 NibbleE, Char Nibble8 NibbleF,
    Char Nibble9 Nibble0, Char Nibble9 Nibble1, Char Nibble9 Nibble2,
    Char Nibble9 Nibble3, Char Nibble9 Nibble4, Char Nibble9 Nibble5,
    Char Nibble9 Nibble6, Char Nibble9 Nibble7, Char Nibble9 Nibble8,
    Char Nibble9 Nibble9, Char Nibble9 NibbleA, Char Nibble9 NibbleB,
    Char Nibble9 NibbleC, Char Nibble9 NibbleD, Char Nibble9 NibbleE,
    Char Nibble9 NibbleF, Char NibbleA Nibble0, Char NibbleA Nibble1,
    Char NibbleA Nibble2, Char NibbleA Nibble3, Char NibbleA Nibble4,
    Char NibbleA Nibble5, Char NibbleA Nibble6, Char NibbleA Nibble7,
    Char NibbleA Nibble8, Char NibbleA Nibble9, Char NibbleA NibbleA,
    Char NibbleA NibbleB, Char NibbleA NibbleC, Char NibbleA NibbleD,
    Char NibbleA NibbleE, Char NibbleA NibbleF, Char NibbleB Nibble0,
    Char NibbleB Nibble1, Char NibbleB Nibble2, Char NibbleB Nibble3,
    Char NibbleB Nibble4, Char NibbleB Nibble5, Char NibbleB Nibble6,
    Char NibbleB Nibble7, Char NibbleB Nibble8, Char NibbleB Nibble9,
    Char NibbleB NibbleA, Char NibbleB NibbleB, Char NibbleB NibbleC,
    Char NibbleB NibbleD, Char NibbleB NibbleE, Char NibbleB NibbleF,
    Char NibbleC Nibble0, Char NibbleC Nibble1, Char NibbleC Nibble2,
    Char NibbleC Nibble3, Char NibbleC Nibble4, Char NibbleC Nibble5,
    Char NibbleC Nibble6, Char NibbleC Nibble7, Char NibbleC Nibble8,
    Char NibbleC Nibble9, Char NibbleC NibbleA, Char NibbleC NibbleB,
    Char NibbleC NibbleC, Char NibbleC NibbleD, Char NibbleC NibbleE,
    Char NibbleC NibbleF, Char NibbleD Nibble0, Char NibbleD Nibble1,
    Char NibbleD Nibble2, Char NibbleD Nibble3, Char NibbleD Nibble4,
    Char NibbleD Nibble5, Char NibbleD Nibble6, Char NibbleD Nibble7,
    Char NibbleD Nibble8, Char NibbleD Nibble9, Char NibbleD NibbleA,
    Char NibbleD NibbleB, Char NibbleD NibbleC, Char NibbleD NibbleD,
    Char NibbleD NibbleE, Char NibbleD NibbleF, Char NibbleE Nibble0,
    Char NibbleE Nibble1, Char NibbleE Nibble2, Char NibbleE Nibble3,
    Char NibbleE Nibble4, Char NibbleE Nibble5, Char NibbleE Nibble6,
    Char NibbleE Nibble7, Char NibbleE Nibble8, Char NibbleE Nibble9,
    Char NibbleE NibbleA, Char NibbleE NibbleB, Char NibbleE NibbleC,
    Char NibbleE NibbleD, Char NibbleE NibbleE, Char NibbleE NibbleF,
    Char NibbleF Nibble0, Char NibbleF Nibble1, Char NibbleF Nibble2,
    Char NibbleF Nibble3, Char NibbleF Nibble4, Char NibbleF Nibble5,
    Char NibbleF Nibble6, Char NibbleF Nibble7, Char NibbleF Nibble8,
    Char NibbleF Nibble9, Char NibbleF NibbleA, Char NibbleF NibbleB,
    Char NibbleF NibbleC, Char NibbleF NibbleD, Char NibbleF NibbleE,
    Char NibbleF NibbleF];

scomp :: forall a b c d. (a -> (b, c)) -> (b -> c -> d) -> a -> d;
scomp f g = (\ x -> let {
                      (a, b) = f x;
                    } in g a b);

gen_length :: forall a. Nat -> [a] -> Nat;
gen_length n (x : xs) = gen_length (Suc n) xs;
gen_length n [] = n;

size_list :: forall a. [a] -> Nat;
size_list = gen_length Zero_nat;

of_nat_aux :: forall a. (Semiring_1 a) => (a -> a) -> Nat -> a -> a;
of_nat_aux inc Zero_nat i = i;
of_nat_aux inc (Suc n) i = of_nat_aux inc n (inc i);

of_nat :: forall a. (Semiring_1 a) => Nat -> a;
of_nat n = of_nat_aux (\ i -> plus i one) n zero;

newtype Natural = Nat Integer;

one_integer :: Integer;
one_integer = (1 :: Integer);

instance Times Integer where {
  times = (\ a b -> a * b);
};

instance Semigroup_mult Integer where {
};

instance One Integer where {
  one = one_integer;
};

instance Power Integer where {
};

instance Monoid_mult Integer where {
};

instance Plus Integer where {
  plus = (\ a b -> a + b);
};

instance Semigroup_add Integer where {
};

instance Ab_semigroup_add Integer where {
};

instance Semiring Integer where {
};

instance Numeral Integer where {
};

instance Semiring_numeral Integer where {
};

instance Zero Integer where {
  zero = (0 :: Integer);
};

instance Zero_neq_one Integer where {
};

instance Monoid_add Integer where {
};

instance Comm_monoid_add Integer where {
};

instance Mult_zero Integer where {
};

instance Semiring_0 Integer where {
};

instance Semiring_1 Integer where {
};

natural_of_nat :: Nat -> Natural;
natural_of_nat n = Nat (of_nat n);

integer_of_natural :: Natural -> Integer;
integer_of_natural (Nat x) = x;

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

times_natural :: Natural -> Natural -> Natural;
times_natural m n = Nat (integer_of_natural m * integer_of_natural n);

plus_natural :: Natural -> Natural -> Natural;
plus_natural m n = Nat (integer_of_natural m + integer_of_natural n);

one_natural :: Natural;
one_natural = Nat (1 :: Integer);

mod_integer :: Integer -> Integer -> Integer;
mod_integer k l = snd (divmod_integer k l);

mod_natural :: Natural -> Natural -> Natural;
mod_natural m n =
  Nat (mod_integer (integer_of_natural m) (integer_of_natural n));

max :: forall a. (Ord a) => a -> a -> a;
max a b = (if less_eq a b then b else a);

instance Ord Integer where {
  less_eq = (\ a b -> a <= b);
  less = (\ a b -> a < b);
};

natural_of_integer :: Integer -> Natural;
natural_of_integer k = Nat (max (0 :: Integer) k);

minus_natural :: Natural -> Natural -> Natural;
minus_natural m n =
  Nat (max (0 :: Integer) (integer_of_natural m - integer_of_natural n));

equal_natural :: Natural -> Natural -> Bool;
equal_natural m n = integer_of_natural m == integer_of_natural n;

zero_natural :: Natural;
zero_natural = Nat (0 :: Integer);

iterate :: forall a b. Natural -> (a -> b -> (a, b)) -> a -> b -> (a, b);
iterate k f x =
  (if equal_natural k zero_natural then (\ a -> (x, a))
    else scomp (f x) (iterate (minus_natural k one_natural) f));

div_integer :: Integer -> Integer -> Integer;
div_integer k l = fst (divmod_integer k l);

div_natural :: Natural -> Natural -> Natural;
div_natural m n =
  Nat (div_integer (integer_of_natural m) (integer_of_natural n));

less_natural :: Natural -> Natural -> Bool;
less_natural m n = integer_of_natural m < integer_of_natural n;

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

less_eq_natural :: Natural -> Natural -> Bool;
less_eq_natural m n = integer_of_natural m <= integer_of_natural n;

log :: Natural -> Natural -> Natural;
log b i =
  (if less_eq_natural b one_natural || less_natural i b then one_natural
    else plus_natural one_natural (log b (div_natural i b)));

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

select :: forall a. [a] -> (Natural, Natural) -> (a, (Natural, Natural));
select xs =
  scomp (range (natural_of_nat (size_list xs)))
    (\ k -> (\ a -> (nth xs (nat_of_natural k), a)));

random_char ::
  Natural -> (Natural, Natural) -> ((Char, () -> Term), (Natural, Natural));
random_char uu =
  scomp (select enum_char) (\ c -> (\ a -> ((c, (\ _ -> term_of_char c)), a)));

class (Typerep a) => Random a where {
  random ::
    Natural -> (Natural, Natural) -> ((a, () -> Term), (Natural, Natural));
};

instance Random Char where {
  random = random_char;
};

newtype Narrowing_type = Narrowing_sum_of_products [[Narrowing_type]];

data Narrowing_term = Narrowing_variable [Integer] Narrowing_type
  | Narrowing_constructor Integer [Narrowing_term];

class (Typerep a) => Partial_term_of a where {
  partial_term_of :: Itself a -> Narrowing_term -> Term;
};

partial_term_of_nibble :: Itself Nibble -> Narrowing_term -> Term;
partial_term_of_nibble ty (Narrowing_constructor (15 :: Integer) []) =
  Const "String.nibble.NibbleF" (Typerep "String.nibble" []);
partial_term_of_nibble ty (Narrowing_constructor (14 :: Integer) []) =
  Const "String.nibble.NibbleE" (Typerep "String.nibble" []);
partial_term_of_nibble ty (Narrowing_constructor (13 :: Integer) []) =
  Const "String.nibble.NibbleD" (Typerep "String.nibble" []);
partial_term_of_nibble ty (Narrowing_constructor (12 :: Integer) []) =
  Const "String.nibble.NibbleC" (Typerep "String.nibble" []);
partial_term_of_nibble ty (Narrowing_constructor (11 :: Integer) []) =
  Const "String.nibble.NibbleB" (Typerep "String.nibble" []);
partial_term_of_nibble ty (Narrowing_constructor (10 :: Integer) []) =
  Const "String.nibble.NibbleA" (Typerep "String.nibble" []);
partial_term_of_nibble ty (Narrowing_constructor (9 :: Integer) []) =
  Const "String.nibble.Nibble9" (Typerep "String.nibble" []);
partial_term_of_nibble ty (Narrowing_constructor (8 :: Integer) []) =
  Const "String.nibble.Nibble8" (Typerep "String.nibble" []);
partial_term_of_nibble ty (Narrowing_constructor (7 :: Integer) []) =
  Const "String.nibble.Nibble7" (Typerep "String.nibble" []);
partial_term_of_nibble ty (Narrowing_constructor (6 :: Integer) []) =
  Const "String.nibble.Nibble6" (Typerep "String.nibble" []);
partial_term_of_nibble ty (Narrowing_constructor (5 :: Integer) []) =
  Const "String.nibble.Nibble5" (Typerep "String.nibble" []);
partial_term_of_nibble ty (Narrowing_constructor (4 :: Integer) []) =
  Const "String.nibble.Nibble4" (Typerep "String.nibble" []);
partial_term_of_nibble ty (Narrowing_constructor (3 :: Integer) []) =
  Const "String.nibble.Nibble3" (Typerep "String.nibble" []);
partial_term_of_nibble ty (Narrowing_constructor (2 :: Integer) []) =
  Const "String.nibble.Nibble2" (Typerep "String.nibble" []);
partial_term_of_nibble ty (Narrowing_constructor (1 :: Integer) []) =
  Const "String.nibble.Nibble1" (Typerep "String.nibble" []);
partial_term_of_nibble ty (Narrowing_constructor (0 :: Integer) []) =
  Const "String.nibble.Nibble0" (Typerep "String.nibble" []);
partial_term_of_nibble ty (Narrowing_variable p tt) =
  Free "_" (Typerep "String.nibble" []);

partial_term_of_char :: Itself Char -> Narrowing_term -> Term;
partial_term_of_char ty (Narrowing_constructor (0 :: Integer) [b, a]) =
  App (App (Const "String.char.Char"
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

class (Term_of a) => Full_exhaustive a where {
  full_exhaustive ::
    ((a, () -> Term) -> Maybe (Bool, [Term])) ->
      Natural -> Maybe (Bool, [Term]);
};

full_exhaustive_nibble ::
  ((Nibble, () -> Term) -> Maybe (Bool, [Term])) ->
    Natural -> Maybe (Bool, [Term]);
full_exhaustive_nibble f i =
  (if less_natural zero_natural i
    then (case f (Nibble0,
                   (\ _ ->
                     Const "String.nibble.Nibble0"
                       (Typerep "String.nibble" [])))
           of {
           Nothing ->
             (case f (Nibble1,
                       (\ _ ->
                         Const "String.nibble.Nibble1"
                           (Typerep "String.nibble" [])))
               of {
               Nothing ->
                 (case f (Nibble2,
                           (\ _ ->
                             Const "String.nibble.Nibble2"
                               (Typerep "String.nibble" [])))
                   of {
                   Nothing ->
                     (case f (Nibble3,
                               (\ _ ->
                                 Const "String.nibble.Nibble3"
                                   (Typerep "String.nibble" [])))
                       of {
                       Nothing ->
                         (case f (Nibble4,
                                   (\ _ ->
                                     Const "String.nibble.Nibble4"
                                       (Typerep "String.nibble" [])))
                           of {
                           Nothing ->
                             (case f (Nibble5,
                                       (\ _ ->
 Const "String.nibble.Nibble5" (Typerep "String.nibble" [])))
                               of {
                               Nothing ->
                                 (case f
 (Nibble6, (\ _ -> Const "String.nibble.Nibble6" (Typerep "String.nibble" [])))
                                   of {
                                   Nothing ->
                                     (case f
     (Nibble7,
       (\ _ -> Const "String.nibble.Nibble7" (Typerep "String.nibble" [])))
                                       of {
                                       Nothing ->
 (case f (Nibble8,
           (\ _ -> Const "String.nibble.Nibble8" (Typerep "String.nibble" [])))
   of {
   Nothing ->
     (case f (Nibble9,
               (\ _ ->
                 Const "String.nibble.Nibble9" (Typerep "String.nibble" [])))
       of {
       Nothing ->
         (case f (NibbleA,
                   (\ _ ->
                     Const "String.nibble.NibbleA"
                       (Typerep "String.nibble" [])))
           of {
           Nothing ->
             (case f (NibbleB,
                       (\ _ ->
                         Const "String.nibble.NibbleB"
                           (Typerep "String.nibble" [])))
               of {
               Nothing ->
                 (case f (NibbleC,
                           (\ _ ->
                             Const "String.nibble.NibbleC"
                               (Typerep "String.nibble" [])))
                   of {
                   Nothing ->
                     (case f (NibbleD,
                               (\ _ ->
                                 Const "String.nibble.NibbleD"
                                   (Typerep "String.nibble" [])))
                       of {
                       Nothing ->
                         (case f (NibbleE,
                                   (\ _ ->
                                     Const "String.nibble.NibbleE"
                                       (Typerep "String.nibble" [])))
                           of {
                           Nothing ->
                             f (NibbleF,
                                 (\ _ ->
                                   Const "String.nibble.NibbleF"
                                     (Typerep "String.nibble" [])));
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

times_nat :: Nat -> Nat -> Nat;
times_nat Zero_nat n = Zero_nat;
times_nat (Suc m) n = plus_nat n (times_nat m n);

nat_of_nibble :: Nibble -> Nat;
nat_of_nibble Nibble0 = Zero_nat;
nat_of_nibble Nibble1 = one_nat;
nat_of_nibble Nibble2 = nat_of_num (Bit0 One);
nat_of_nibble Nibble3 = nat_of_num (Bit1 One);
nat_of_nibble Nibble4 = nat_of_num (Bit0 (Bit0 One));
nat_of_nibble Nibble5 = nat_of_num (Bit1 (Bit0 One));
nat_of_nibble Nibble6 = nat_of_num (Bit0 (Bit1 One));
nat_of_nibble Nibble7 = nat_of_num (Bit1 (Bit1 One));
nat_of_nibble Nibble8 = nat_of_num (Bit0 (Bit0 (Bit0 One)));
nat_of_nibble Nibble9 = nat_of_num (Bit1 (Bit0 (Bit0 One)));
nat_of_nibble NibbleA = nat_of_num (Bit0 (Bit1 (Bit0 One)));
nat_of_nibble NibbleB = nat_of_num (Bit1 (Bit1 (Bit0 One)));
nat_of_nibble NibbleC = nat_of_num (Bit0 (Bit0 (Bit1 One)));
nat_of_nibble NibbleD = nat_of_num (Bit1 (Bit0 (Bit1 One)));
nat_of_nibble NibbleE = nat_of_num (Bit0 (Bit1 (Bit1 One)));
nat_of_nibble NibbleF = nat_of_num (Bit1 (Bit1 (Bit1 One)));

char_of_nat :: Nat -> Char;
char_of_nat n =
  nth enum_char
    (mod_nat n
      (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One))))))))));

typerep_nibble :: Itself Nibble -> Typerepa;
typerep_nibble t = Typerep "String.nibble" [];

instance Typerep Nibble where {
  typerep = typerep_nibble;
};

full_exhaustive_char ::
  ((Char, () -> Term) -> Maybe (Bool, [Term])) ->
    Natural -> Maybe (Bool, [Term]);
full_exhaustive_char f i =
  (if less_natural zero_natural i
    then full_exhaustive_nibble
           (\ (a, b) ->
             full_exhaustive_nibble
               (\ (c, d) ->
                 f (char_of_nat
                      (plus_nat
                        (times_nat (nat_of_nibble a)
                          (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 One))))))
                        (nat_of_nibble c)),
                     (\ _ ->
                       App (App (Const "String.char.Char"
                                  ((typerep_fun ::
                                     Itself (Nibble -> Nibble -> Char) ->
                                       Typerepa)
                                    Type))
                             (b ()))
                         (d ()))))
               (minus_natural i one_natural))
           (minus_natural i one_natural)
    else Nothing);

instance Full_exhaustive Char where {
  full_exhaustive = full_exhaustive_char;
};

instance Plus Natural where {
  plus = plus_natural;
};

instance Zero Natural where {
  zero = zero_natural;
};

instance Semigroup_add Natural where {
};

instance Monoid_add Natural where {
};

data Narrowing_cons a = Narrowing_cons Narrowing_type [[Narrowing_term] -> a];

class Narrowing a where {
  narrowing :: Integer -> Narrowing_cons a;
};

data Set a = Set [a] | Coset [a];

newtype Identity a = Id a;

data MyRecord = A [Char] Bool Int | B Bool Int Bool Int | C Bool Int [Char];

data MyRecord_pre_MyRecord;

data Identity_IITN_Identity a;

data MyRecord_IITN_MyRecord;

ball :: forall a. Set a -> (a -> Bool) -> Bool;
ball (Set xs) p = all p xs;

foldr :: forall a b. (a -> b -> b) -> [a] -> b -> b;
foldr f [] = id;
foldr f (x : xs) = f x . foldr f xs;

removeAll :: forall a. (Eq a) => a -> [a] -> [a];
removeAll x [] = [];
removeAll x (y : xs) = (if x == y then removeAll x xs else y : removeAll x xs);

member :: forall a. (Eq a) => [a] -> a -> Bool;
member [] y = False;
member (x : xs) y = x == y || member xs y;

inserta :: forall a. (Eq a) => a -> [a] -> [a];
inserta x xs = (if member xs x then xs else x : xs);

insert :: forall a. (Eq a) => a -> Set a -> Set a;
insert x (Coset xs) = Coset (removeAll x xs);
insert x (Set xs) = Set (inserta x xs);

pick :: forall a. [(Natural, a)] -> Natural -> a;
pick (x : xs) i =
  (if less_natural i (fst x) then snd x else pick xs (minus_natural i (fst x)));

this :: forall a. Identity a -> a;
this (Id x) = x;

constr :: MyRecord;
constr =
  A [Char Nibble6 Nibble6, Char Nibble6 NibbleF, Char Nibble6 NibbleF] True
    (error "undefined");

update_common2 :: Int -> MyRecord -> MyRecord;
update_common2 x (B f1 f2 f3 uu) = B f1 f2 f3 x;
update_common2 x (A f1 f2 uv) = A f1 f2 x;

update_common1 :: Bool -> MyRecord -> MyRecord;
update_common1 x (B f1 f2 uu f4) = B f1 f2 x f4;
update_common1 x (A f1 uv f3) = A f1 x f3;

update :: MyRecord -> MyRecord;
update x = (update_common1 False . update_common2 (Pos One)) x;

aField1 :: MyRecord -> [Char];
aField1 (A x uu uv) = x;

bField1 :: MyRecord -> Bool;
bField1 (B x uu uv uw) = x;

bField2 :: MyRecord -> Int;
bField2 (B uu x uv uw) = x;

common1 :: MyRecord -> Bool;
common1 (B uu uv x uw) = x;
common1 (A ux x uy) = x;

common2 :: MyRecord -> Int;
common2 (B uu uv uw x) = x;
common2 (A ux uy x) = x;

pattern :: MyRecord -> Int;
pattern (A uu uv val) = val;
pattern (B uw val ux uy) = val;
pattern (C uz val va) = val;

update_this :: forall a. a -> Identity a -> Identity a;
update_this x (Id uu) = Id x;

collapse :: forall a b. (a -> (a -> (b, a), a)) -> a -> (b, a);
collapse f = scomp f id;

valapp ::
  forall a b. (a -> b, () -> Term) -> (a, () -> Term) -> (b, () -> Term);
valapp (f, tf) (x, tx) = (f x, (\ _ -> App (tf ()) (tx ())));

listsum :: forall a. (Monoid_add a) => [a] -> a;
listsum xs = foldr plus xs zero;

select_weight ::
  forall a. [(Natural, a)] -> (Natural, Natural) -> (a, (Natural, Natural));
select_weight xs =
  scomp (range (listsum (map fst xs))) (\ k -> (\ a -> (pick xs k, a)));

random_aux_list ::
  forall a.
    (Random a) => Natural ->
                    Natural ->
                      (Natural, Natural) ->
                        (([a], () -> Term), (Natural, Natural));
random_aux_list i j s =
  collapse
    (select_weight
      [(i, scomp (random j)
             (\ x ->
               scomp (random_aux_list (minus_natural i one_natural) j)
                 (\ y ->
                   (\ a ->
                     (valapp
                        (valapp
                          ((\ aa b -> aa : b),
                            (\ _ ->
                              Const "List.list.Cons"
                                (Typerep "fun"
                                  [(typerep :: Itself a -> Typerepa) Type,
                                    Typerep "fun"
                                      [Typerep "List.list"
 [(typerep :: Itself a -> Typerepa) Type],
Typerep "List.list" [(typerep :: Itself a -> Typerepa) Type]]])))
                          x)
                        y,
                       a))))),
        (one_natural,
          (\ a ->
            (([], (\ _ ->
                    Const "List.list.Nil"
                      (Typerep "List.list"
                        [(typerep :: Itself a -> Typerepa) Type]))),
              a)))])
    s;

bot_set :: forall a. Set a;
bot_set = Set [];

set_Identity :: forall a. (Eq a) => Identity a -> Set a;
set_Identity (Id x) = insert x bot_set;

pred_Identity :: forall a. (Eq a) => (a -> Bool) -> Identity a -> Bool;
pred_Identity p = (\ x -> ball (set_Identity x) p);

update_aField1 :: [Char] -> MyRecord -> MyRecord;
update_aField1 x (A uu f2 f3) = A x f2 f3;

update_bField1 :: Bool -> MyRecord -> MyRecord;
update_bField1 x (B uu f2 f3 f4) = B x f2 f3 f4;

update_bField2 :: Int -> MyRecord -> MyRecord;
update_bField2 x (B f1 uu f3 f4) = B f1 x f3 f4;

sum ::
  forall a.
    (Integer -> Narrowing_cons a) ->
      (Integer -> Narrowing_cons a) -> Integer -> Narrowing_cons a;
sum a b d =
  let {
    (Narrowing_cons (Narrowing_sum_of_products ssa) ca) = a d;
    (Narrowing_cons (Narrowing_sum_of_products ssb) cb) = b d;
  } in Narrowing_cons (Narrowing_sum_of_products (ssa ++ ssb)) (ca ++ cb);

cons :: forall a. a -> Integer -> Narrowing_cons a;
cons a d = Narrowing_cons (Narrowing_sum_of_products [[]]) [(\ _ -> a)];

int_of_integer :: Integer -> Int;
int_of_integer k =
  (if k < (0 :: Integer) then uminus_int (int_of_integer (negate k))
    else (if k == (0 :: Integer) then Zero_int
           else let {
                  (l, j) = divmod_integer k (2 :: Integer);
                  la = times_int (Pos (Bit0 One)) (int_of_integer l);
                } in (if j == (0 :: Integer) then la
                       else plus_int la (Pos One))));

random_aux_Identity ::
  forall a.
    (Random a) => Natural ->
                    Natural ->
                      (Natural, Natural) ->
                        ((Identity a, () -> Term), (Natural, Natural));
random_aux_Identity i j s =
  collapse
    (select_weight
      [(one_natural,
         scomp (random j)
           (\ x ->
             (\ a ->
               (valapp
                  (Id, (\ _ ->
                         Const "Records.Identity.Id"
                           (Typerep "fun"
                             [(typerep :: Itself a -> Typerepa) Type,
                               Typerep "Records.Identity"
                                 [(typerep :: Itself a -> Typerepa) Type]])))
                  x,
                 a))))])
    s;

random_bool ::
  Natural -> (Natural, Natural) -> ((Bool, () -> Term), (Natural, Natural));
random_bool i =
  scomp (range (natural_of_integer (2 :: Integer)))
    (\ k ->
      (\ a ->
        ((if equal_natural k zero_natural
           then (False, (\ _ -> Const "HOL.False" (Typerep "HOL.bool" [])))
           else (True, (\ _ -> Const "HOL.True" (Typerep "HOL.bool" [])))),
          a)));

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

random_list ::
  forall a.
    (Random a) => Natural ->
                    (Natural, Natural) ->
                      (([a], () -> Term), (Natural, Natural));
random_list i = random_aux_list i i;

random_aux_MyRecord ::
  Natural ->
    Natural ->
      (Natural, Natural) -> ((MyRecord, () -> Term), (Natural, Natural));
random_aux_MyRecord i j s =
  collapse
    (select_weight
      [(one_natural,
         scomp (random_list j)
           (\ x ->
             scomp (random_bool j)
               (\ y ->
                 scomp (random_int j)
                   (\ z ->
                     (\ a ->
                       (valapp
                          (valapp
                            (valapp
                              (A, (\ _ ->
                                    Const "Records.MyRecord.A"
                                      (Typerep "fun"
[Typerep "List.list" [Typerep "String.char" []],
  Typerep "fun"
    [Typerep "HOL.bool" [],
      Typerep "fun" [Typerep "Int.int" [], Typerep "Records.MyRecord" []]]])))
                              x)
                            y)
                          z,
                         a)))))),
        (one_natural,
          scomp (random_bool j)
            (\ x ->
              scomp (random_int j)
                (\ y ->
                  scomp (random_bool j)
                    (\ z ->
                      scomp (random_int j)
                        (\ aa ->
                          (\ a ->
                            (valapp
                               (valapp
                                 (valapp
                                   (valapp
                                     (B, (\ _ ->
   Const "Records.MyRecord.B"
     (Typerep "fun"
       [Typerep "HOL.bool" [],
         Typerep "fun"
           [Typerep "Int.int" [],
             Typerep "fun"
               [Typerep "HOL.bool" [],
                 Typerep "fun"
                   [Typerep "Int.int" [], Typerep "Records.MyRecord" []]]]])))
                                     x)
                                   y)
                                 z)
                               aa,
                              a))))))),
        (one_natural,
          scomp (random_bool j)
            (\ x ->
              scomp (random_int j)
                (\ y ->
                  scomp (random_list j)
                    (\ z ->
                      (\ a ->
                        (valapp
                           (valapp
                             (valapp
                               (C, (\ _ ->
                                     Const "Records.MyRecord.C"
                                       (Typerep "fun"
 [Typerep "HOL.bool" [],
   Typerep "fun"
     [Typerep "Int.int" [],
       Typerep "fun"
         [Typerep "List.list" [Typerep "String.char" []],
           Typerep "Records.MyRecord" []]]])))
                               x)
                             y)
                           z,
                          a))))))])
    s;

map_Identity :: forall a b. (a -> b) -> Identity a -> Identity b;
map_Identity f (Id x) = Id (f x);

rec_Identity :: forall a b. (a -> b) -> Identity a -> b;
rec_Identity f (Id x) = f x;

rel_Identity ::
  forall a b. (a -> b -> Bool) -> Identity a -> Identity b -> Bool;
rel_Identity r (Id x) (Id y) = r x y;

rec_MyRecord ::
  forall a.
    ([Char] -> Bool -> Int -> a) ->
      (Bool -> Int -> Bool -> Int -> a) ->
        (Bool -> Int -> [Char] -> a) -> MyRecord -> a;
rec_MyRecord f1 f2 f3 (A x11 x12 x13) = f1 x11 x12 x13;
rec_MyRecord f1 f2 f3 (B x21 x22 x23 x24) = f2 x21 x22 x23 x24;
rec_MyRecord f1 f2 f3 (C x31 x32 x33) = f3 x31 x32 x33;

non_empty :: Narrowing_type -> Bool;
non_empty (Narrowing_sum_of_products ps) = not (null ps);

size_Identity :: forall a. (a -> Nat) -> Identity a -> Nat;
size_Identity xa (Id x) = plus_nat (xa x) (Suc Zero_nat);

size_MyRecord :: MyRecord -> Nat;
size_MyRecord (A x11 x12 x13) = Zero_nat;
size_MyRecord (B x21 x22 x23 x24) = Zero_nat;
size_MyRecord (C x31 x32 x33) = Zero_nat;

drawn_from :: forall a. [a] -> Narrowing_cons a;
drawn_from xs =
  Narrowing_cons (Narrowing_sum_of_products (map (\ _ -> []) xs))
    (map (\ x _ -> x) xs);

around_zero :: Int -> [Int];
around_zero i =
  (if less_int i Zero_int then []
    else (if equal_int i Zero_int then [Zero_int]
           else around_zero (minus_int i (Pos One)) ++ [i, uminus_int i]));

term_of_bool :: Bool -> Term;
term_of_bool False = Const "HOL.False" (Typerep "HOL.bool" []);
term_of_bool True = Const "HOL.True" (Typerep "HOL.bool" []);

term_of_list :: forall a. (Term_of a) => [a] -> Term;
term_of_list (a : b) =
  App (App (Const "List.list.Cons"
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
  Const "List.list.Nil"
    (Typerep "List.list" [(typerep :: Itself a -> Typerepa) Type]);

narrowing_bool :: Integer -> Narrowing_cons Bool;
narrowing_bool = sum (cons True) (cons False);

size_Identitya :: forall a. Identity a -> Nat;
size_Identitya (Id x) = Suc Zero_nat;

size_MyRecorda :: MyRecord -> Nat;
size_MyRecorda (A x11 x12 x13) = Zero_nat;
size_MyRecorda (B x21 x22 x23 x24) = Zero_nat;
size_MyRecorda (C x31 x32 x33) = Zero_nat;

full_exhaustive_int ::
  ((Int, () -> Term) -> Maybe (Bool, [Term])) ->
    Int -> Int -> Maybe (Bool, [Term]);
full_exhaustive_int f d i =
  (if less_int d i then Nothing
    else (case f (i, (\ _ -> term_of_int i)) of {
           Nothing -> full_exhaustive_int f d (plus_int i (Pos One));
           Just a -> Just a;
         }));

equal_Identity :: forall a. (Eq a) => Identity a -> Identity a -> Bool;
equal_Identity (Id x) (Id ya) = x == ya;

equal_MyRecord :: MyRecord -> MyRecord -> Bool;
equal_MyRecord (B x21 x22 x23 x24) (C x31 x32 x33) = False;
equal_MyRecord (C x31 x32 x33) (B x21 x22 x23 x24) = False;
equal_MyRecord (A x11 x12 x13) (C x31 x32 x33) = False;
equal_MyRecord (C x31 x32 x33) (A x11 x12 x13) = False;
equal_MyRecord (A x11 x12 x13) (B x21 x22 x23 x24) = False;
equal_MyRecord (B x21 x22 x23 x24) (A x11 x12 x13) = False;
equal_MyRecord (C x31 x32 x33) (C y31 y32 y33) =
  x31 == y31 && equal_int x32 y32 && x33 == y33;
equal_MyRecord (B x21 x22 x23 x24) (B y21 y22 y23 y24) =
  x21 == y21 && equal_int x22 y22 && x23 == y23 && equal_int x24 y24;
equal_MyRecord (A x11 x12 x13) (A y11 y12 y13) =
  x11 == y11 && x12 == y12 && equal_int x13 y13;

random_Identity ::
  forall a.
    (Random a) => Natural ->
                    (Natural, Natural) ->
                      ((Identity a, () -> Term), (Natural, Natural));
random_Identity i = random_aux_Identity i i;

random_MyRecord ::
  Natural -> (Natural, Natural) -> ((MyRecord, () -> Term), (Natural, Natural));
random_MyRecord i = random_aux_MyRecord i i;

narrowing_nibble :: Integer -> Narrowing_cons Nibble;
narrowing_nibble =
  sum (cons Nibble0)
    (sum (cons Nibble1)
      (sum (cons Nibble2)
        (sum (cons Nibble3)
          (sum (cons Nibble4)
            (sum (cons Nibble5)
              (sum (cons Nibble6)
                (sum (cons Nibble7)
                  (sum (cons Nibble8)
                    (sum (cons Nibble9)
                      (sum (cons NibbleA)
                        (sum (cons NibbleB)
                          (sum (cons NibbleC)
                            (sum (cons NibbleD)
                              (sum (cons NibbleE) (cons NibbleF)))))))))))))));

term_of_Identity :: forall a. (Term_of a) => Identity a -> Term;
term_of_Identity (Id a) =
  App (Const "Records.Identity.Id"
        (Typerep "fun"
          [(typerep :: Itself a -> Typerepa) Type,
            Typerep "Records.Identity"
              [(typerep :: Itself a -> Typerepa) Type]]))
    (term_of a);

term_of_MyRecord :: MyRecord -> Term;
term_of_MyRecord (C a b c) =
  App (App (App (Const "Records.MyRecord.C"
                  (Typerep "fun"
                    [Typerep "HOL.bool" [],
                      Typerep "fun"
                        [Typerep "Int.int" [],
                          Typerep "fun"
                            [Typerep "List.list" [Typerep "String.char" []],
                              Typerep "Records.MyRecord" []]]]))
             (term_of_bool a))
        (term_of_int b))
    (term_of_list c);
term_of_MyRecord (B a b c d) =
  App (App (App (App (Const "Records.MyRecord.B"
                       (Typerep "fun"
                         [Typerep "HOL.bool" [],
                           Typerep "fun"
                             [Typerep "Int.int" [],
                               Typerep "fun"
                                 [Typerep "HOL.bool" [],
                                   Typerep "fun"
                                     [Typerep "Int.int" [],
                                       Typerep "Records.MyRecord" []]]]]))
                  (term_of_bool a))
             (term_of_int b))
        (term_of_bool c))
    (term_of_int d);
term_of_MyRecord (A a b c) =
  App (App (App (Const "Records.MyRecord.A"
                  (Typerep "fun"
                    [Typerep "List.list" [Typerep "String.char" []],
                      Typerep "fun"
                        [Typerep "HOL.bool" [],
                          Typerep "fun"
                            [Typerep "Int.int" [],
                              Typerep "Records.MyRecord" []]]]))
             (term_of_list a))
        (term_of_bool b))
    (term_of_int c);

typerep_Identity :: forall a. (Typerep a) => Itself (Identity a) -> Typerepa;
typerep_Identity t =
  Typerep "Records.Identity" [(typerep :: Itself a -> Typerepa) Type];

typerep_MyRecord :: Itself MyRecord -> Typerepa;
typerep_MyRecord t = Typerep "Records.MyRecord" [];

partial_term_of_int :: Itself Int -> Narrowing_term -> Term;
partial_term_of_int ty (Narrowing_constructor i []) =
  (if mod_integer i (2 :: Integer) == (0 :: Integer)
    then term_of_int (div_int (uminus_int (int_of_integer i)) (Pos (Bit0 One)))
    else term_of_int
           (div_int (plus_int (int_of_integer i) (Pos One)) (Pos (Bit0 One))));
partial_term_of_int ty (Narrowing_variable p t) =
  Free "_" (Typerep "Int.int" []);

full_exhaustive_bool ::
  ((Bool, () -> Term) -> Maybe (Bool, [Term])) ->
    Natural -> Maybe (Bool, [Term]);
full_exhaustive_bool f i =
  (if less_natural zero_natural i
    then (case f (True, (\ _ -> Const "HOL.True" (Typerep "HOL.bool" []))) of {
           Nothing ->
             f (False, (\ _ -> Const "HOL.False" (Typerep "HOL.bool" [])));
           Just a -> Just a;
         })
    else Nothing);

partial_term_of_bool :: Itself Bool -> Narrowing_term -> Term;
partial_term_of_bool ty (Narrowing_constructor (1 :: Integer) []) =
  Const "HOL.False" (Typerep "HOL.bool" []);
partial_term_of_bool ty (Narrowing_constructor (0 :: Integer) []) =
  Const "HOL.True" (Typerep "HOL.bool" []);
partial_term_of_bool ty (Narrowing_variable p tt) =
  Free "_" (Typerep "HOL.bool" []);

full_exhaustive_list ::
  forall a.
    (Full_exhaustive a) => (([a], () -> Term) -> Maybe (Bool, [Term])) ->
                             Natural -> Maybe (Bool, [Term]);
full_exhaustive_list f i =
  (if less_natural zero_natural i
    then (case f ([], (\ _ ->
                        Const "List.list.Nil"
                          (Typerep "List.list"
                            [(typerep :: Itself a -> Typerepa) Type])))
           of {
           Nothing ->
             full_exhaustive
               (\ (uu, uua) ->
                 full_exhaustive_list
                   (\ (uub, uuc) ->
                     f (uu : uub,
                         (\ _ ->
                           App (App (Const "List.list.Cons"
                                      (Typerep "fun"
[(typerep :: Itself a -> Typerepa) Type,
  Typerep "fun"
    [Typerep "List.list" [(typerep :: Itself a -> Typerepa) Type],
      Typerep "List.list" [(typerep :: Itself a -> Typerepa) Type]]]))
                                 (uua ()))
                             (uuc ()))))
                   (minus_natural i one_natural))
               (minus_natural i one_natural);
           Just a -> Just a;
         })
    else Nothing);

partial_term_of_list ::
  forall a. (Partial_term_of a) => Itself [a] -> Narrowing_term -> Term;
partial_term_of_list ty (Narrowing_constructor (1 :: Integer) [b, a]) =
  App (App (Const "List.list.Cons"
             (Typerep "fun"
               [(typerep :: Itself a -> Typerepa) Type,
                 Typerep "fun"
                   [Typerep "List.list"
                      [(typerep :: Itself a -> Typerepa) Type],
                     Typerep "List.list"
                       [(typerep :: Itself a -> Typerepa) Type]]]))
        ((partial_term_of :: Itself a -> Narrowing_term -> Term) Type a))
    ((partial_term_of_list :: Itself [a] -> Narrowing_term -> Term) Type b);
partial_term_of_list ty (Narrowing_constructor (0 :: Integer) []) =
  Const "List.list.Nil"
    (Typerep "List.list" [(typerep :: Itself a -> Typerepa) Type]);
partial_term_of_list ty (Narrowing_variable p tt) =
  Free "_" (Typerep "List.list" [(typerep :: Itself a -> Typerepa) Type]);

full_exhaustive_Identity ::
  forall a.
    (Full_exhaustive a) => ((Identity a, () -> Term) -> Maybe (Bool, [Term])) ->
                             Natural -> Maybe (Bool, [Term]);
full_exhaustive_Identity f i =
  (if less_natural zero_natural i
    then full_exhaustive
           (\ (uu, uua) ->
             f (Id uu,
                 (\ _ ->
                   App (Const "Records.Identity.Id"
                         (Typerep "fun"
                           [(typerep :: Itself a -> Typerepa) Type,
                             Typerep "Records.Identity"
                               [(typerep :: Itself a -> Typerepa) Type]]))
                     (uua ()))))
           (minus_natural i one_natural)
    else Nothing);

full_exhaustive_inta ::
  ((Int, () -> Term) -> Maybe (Bool, [Term])) ->
    Natural -> Maybe (Bool, [Term]);
full_exhaustive_inta f d =
  full_exhaustive_int f (int_of_integer (integer_of_natural d))
    (uminus_int (int_of_integer (integer_of_natural d)));

full_exhaustive_MyRecord ::
  ((MyRecord, () -> Term) -> Maybe (Bool, [Term])) ->
    Natural -> Maybe (Bool, [Term]);
full_exhaustive_MyRecord f i =
  (if less_natural zero_natural i
    then (case full_exhaustive_list
                 (\ (uu, uua) ->
                   full_exhaustive_bool
                     (\ (uub, uuc) ->
                       full_exhaustive_inta
                         (\ (uud, uue) ->
                           f (A uu uub uud,
                               (\ _ ->
                                 App (App (App
    (Const "Records.MyRecord.A"
      (Typerep "fun"
        [Typerep "List.list" [Typerep "String.char" []],
          Typerep "fun"
            [Typerep "HOL.bool" [],
              Typerep "fun"
                [Typerep "Int.int" [], Typerep "Records.MyRecord" []]]]))
    (uua ()))
                                       (uuc ()))
                                   (uue ()))))
                         (minus_natural i one_natural))
                     (minus_natural i one_natural))
                 (minus_natural i one_natural)
           of {
           Nothing ->
             (case full_exhaustive_bool
                     (\ (uu, uua) ->
                       full_exhaustive_inta
                         (\ (uub, uuc) ->
                           full_exhaustive_bool
                             (\ (uud, uue) ->
                               full_exhaustive_inta
                                 (\ (uuf, uug) ->
                                   f (B uu uub uud uuf,
                                       (\ _ ->
 App (App (App (App (Const "Records.MyRecord.B"
                      (Typerep "fun"
                        [Typerep "HOL.bool" [],
                          Typerep "fun"
                            [Typerep "Int.int" [],
                              Typerep "fun"
                                [Typerep "HOL.bool" [],
                                  Typerep "fun"
                                    [Typerep "Int.int" [],
                                      Typerep "Records.MyRecord" []]]]]))
                 (uua ()))
            (uuc ()))
       (uue ()))
   (uug ()))))
                                 (minus_natural i one_natural))
                             (minus_natural i one_natural))
                         (minus_natural i one_natural))
                     (minus_natural i one_natural)
               of {
               Nothing ->
                 full_exhaustive_bool
                   (\ (uu, uua) ->
                     full_exhaustive_inta
                       (\ (uub, uuc) ->
                         full_exhaustive_list
                           (\ (uud, uue) ->
                             f (C uu uub uud,
                                 (\ _ ->
                                   App (App
 (App (Const "Records.MyRecord.C"
        (Typerep "fun"
          [Typerep "HOL.bool" [],
            Typerep "fun"
              [Typerep "Int.int" [],
                Typerep "fun"
                  [Typerep "List.list" [Typerep "String.char" []],
                    Typerep "Records.MyRecord" []]]]))
   (uua ()))
 (uuc ()))
                                     (uue ()))))
                           (minus_natural i one_natural))
                       (minus_natural i one_natural))
                   (minus_natural i one_natural);
               Just a -> Just a;
             });
           Just a -> Just a;
         })
    else Nothing);

partial_term_of_Identity ::
  forall a.
    (Partial_term_of a) => Itself (Identity a) -> Narrowing_term -> Term;
partial_term_of_Identity ty (Narrowing_constructor (0 :: Integer) [a]) =
  App (Const "Records.Identity.Id"
        (Typerep "fun"
          [(typerep :: Itself a -> Typerepa) Type,
            Typerep "Records.Identity"
              [(typerep :: Itself a -> Typerepa) Type]]))
    ((partial_term_of :: Itself a -> Narrowing_term -> Term) Type a);
partial_term_of_Identity ty (Narrowing_variable p tt) =
  Free "_"
    (Typerep "Records.Identity" [(typerep :: Itself a -> Typerepa) Type]);

partial_term_of_MyRecord :: Itself MyRecord -> Narrowing_term -> Term;
partial_term_of_MyRecord ty (Narrowing_constructor (2 :: Integer) [c, b, a]) =
  App (App (App (Const "Records.MyRecord.C"
                  (Typerep "fun"
                    [Typerep "HOL.bool" [],
                      Typerep "fun"
                        [Typerep "Int.int" [],
                          Typerep "fun"
                            [Typerep "List.list" [Typerep "String.char" []],
                              Typerep "Records.MyRecord" []]]]))
             (partial_term_of_bool Type a))
        (partial_term_of_int Type b))
    ((partial_term_of_list :: Itself [Char] -> Narrowing_term -> Term) Type c);
partial_term_of_MyRecord ty (Narrowing_constructor (1 :: Integer) [d, c, b, a])
  = App (App (App (App (Const "Records.MyRecord.B"
                         (Typerep "fun"
                           [Typerep "HOL.bool" [],
                             Typerep "fun"
                               [Typerep "Int.int" [],
                                 Typerep "fun"
                                   [Typerep "HOL.bool" [],
                                     Typerep "fun"
                                       [Typerep "Int.int" [],
 Typerep "Records.MyRecord" []]]]]))
                    (partial_term_of_bool Type a))
               (partial_term_of_int Type b))
          (partial_term_of_bool Type c))
      (partial_term_of_int Type d);
partial_term_of_MyRecord ty (Narrowing_constructor (0 :: Integer) [c, b, a]) =
  App (App (App (Const "Records.MyRecord.A"
                  (Typerep "fun"
                    [Typerep "List.list" [Typerep "String.char" []],
                      Typerep "fun"
                        [Typerep "HOL.bool" [],
                          Typerep "fun"
                            [Typerep "Int.int" [],
                              Typerep "Records.MyRecord" []]]]))
             ((partial_term_of_list :: Itself [Char] -> Narrowing_term -> Term)
               Type a))
        (partial_term_of_bool Type b))
    (partial_term_of_int Type c);
partial_term_of_MyRecord ty (Narrowing_variable p tt) =
  Free "_" (Typerep "Records.MyRecord" []);

typerep_MyRecord_pre_MyRecord :: Itself MyRecord_pre_MyRecord -> Typerepa;
typerep_MyRecord_pre_MyRecord t =
  Typerep "Records.MyRecord.MyRecord_pre_MyRecord" [];

typerep_Identity_IITN_Identity ::
  forall a. (Typerep a) => Itself (Identity_IITN_Identity a) -> Typerepa;
typerep_Identity_IITN_Identity t =
  Typerep "Records.Identity.Identity_IITN_Identity"
    [(typerep :: Itself a -> Typerepa) Type];

typerep_MyRecord_IITN_MyRecord :: Itself MyRecord_IITN_MyRecord -> Typerepa;
typerep_MyRecord_IITN_MyRecord t =
  Typerep "Records.MyRecord.MyRecord_IITN_MyRecord" [];

}
