{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Float(Num(..), Int(..), one_inta, One(..), plus_num, times_num, times_int,
         Timesa(..), one_int, Onea(..), uminus_int, bitM, dup, minus_int, sub,
         plus_int, equal_num, equal_int, less_num, less_eq_num, less_int,
         sgn_inta, abs_inta, apsnda, Ord(..), Plusa(..), Numeral, numeral,
         Minusa(..), Zeroa(..), Monoid_adda, Semiring_1a, Diva(..),
         Semiring_numeral_div, divmod_step, divmodb, less_eq_int, divmod_abs,
         divmod_int, div_inta, mod_inta, times_inta, Times(..), Power, Rat(..),
         Reala(..), neg_rat, neg_real, neg_Reala, Neg(..), one_real, one_Reala,
         eq_int, positive, div_mod, divmod, mod_nat, gcd_nat, abs_int, gcd_int,
         sgn_int, apsnd, divmoda, div_int, fract_norm, plus_rat, plus_real,
         plus_Reala, Plus(..), times_rat, times_real, times_Reala, minus_rat,
         minus_real, minus_Reala, zero_real, zero_Reala, Minus(..), Zero(..),
         Ring_1, Natural(..), integer_of_natural, plus_natural, zero_natural,
         Div(..), Typerepa(..), Itself(..), Typerep(..), Nat(..), Set(..),
         Nibble(..), Chara(..), Nibblea(..), Char(..), Floata(..), Itselfa(..),
         Term(..), Rat_IITN_Rat, Chara_IITN_Chara, Reala_IITN_Reala,
         Itself_pre_Itself, Nibble_pre_Nibble, Floata_IITN_Floata,
         Itself_IITN_Itself, Nibble_IITN_Nibble, Narrowing_type(..),
         Narrowing_term(..), Narrowing_cons(..), ball, leta, inverse_rat,
         inverse_real, minus_nat, power, pow2, foldr, less_eq_natural,
         less_natural, one_natural, sgn_integer, abs_integer, divmod_integer,
         div_integer, div_natural, log, scale, split, times_natural,
         mod_integer, mod_natural, max, natural_of_integer, minus_natural,
         minus_shift, next, pick, bitlen, foldla, times_float, plus_float,
         neg_float, minus_float, mod_int, even_int, normfloat, rapprox_posrat,
         lapprox_posrat, zero_float, rapprox_rat, float_divr, ceiling_fl,
         lb_mod, of_int, lapprox_rat, float_divl, floor_fl, ub_mod, scomp,
         equal_natural, iterate, range, eq_float, less_rat, mantissa, of_float,
         round_up, float_abs, abs_float, less_real, one_float, float_nprt,
         float_pprt, float_size, less_float, round_down, rec_Rat, less_eq_rat,
         bot_set, set_Itself, pred_Itself, size_Rat, less_eq_real,
         less_eq_float, term_of_num, term_of_int, of_nat_aux, of_nat, plus_nat,
         one_nat, nat_of_integer, nat_of_natural, random_int, collapse, valapp,
         listsum, select_weight, random_aux_Rat, rec_Chara, rec_Reala,
         size_Chara, size_Reala, random_aux_Nibble, random_Nibble,
         random_aux_Chara, random_Rat, random_aux_Reala, rec_Floata, map_Itself,
         rec_Itself, rel_Itself, rec_Nibble, random_aux_Floata,
         random_aux_Itself, size_Floata, size_Itself, size_Nibble, sum, cons,
         int_of_integer, diva_int, moda_int, plus_inta, zero_int, size_Rata,
         equal_Rat, non_empty, drawn_from, size_Charaa, size_Realaa,
         around_zero, equal_Nibble, equal_Chara, equal_Reala, size_Floataa,
         size_Itselfa, size_Nibblea, term_of_Rat, typerep_Rat, equal_Floata,
         equal_Itself, random_Chara, random_Reala, random_Floata, random_Itself,
         term_of_Nibble, term_of_Chara, term_of_Reala, typerep_Chara,
         typerep_Reala, term_of_Floata, term_of_Itself, typerep_Floata,
         typerep_Itself, typerep_Nibble, one_integer, full_exhaustive_int,
         narrowing_Itself, narrowing_Nibble, partial_term_of_int,
         full_exhaustive_inta, full_exhaustive_Rat, partial_term_of_Rat,
         full_exhaustive_Nibble, full_exhaustive_Chara, full_exhaustive_Reala,
         partial_term_of_Nibble, partial_term_of_Chara, partial_term_of_Reala,
         typerep_Rat_IITN_Rat, full_exhaustive_Floata, full_exhaustive_Itself,
         partial_term_of_Floata, partial_term_of_Itself,
         typerep_Chara_IITN_Chara, typerep_Reala_IITN_Reala,
         typerep_Itself_pre_Itself, typerep_Nibble_pre_Nibble,
         typerep_Floata_IITN_Floata, typerep_Itself_IITN_Itself,
         typerep_Nibble_IITN_Nibble)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;

data Num = One | Bit0 Num | Bit1 Num;

data Int = Zero_int | Pos Num | Neg Num;

one_inta :: Int;
one_inta = Pos One;

class One a where {
  one :: a;
};

instance One Int where {
  one = one_inta;
};

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

times_int :: Int -> Int -> Int;
times_int (Neg m) (Neg n) = Pos (times_num m n);
times_int (Neg m) (Pos n) = Neg (times_num m n);
times_int (Pos m) (Neg n) = Neg (times_num m n);
times_int (Pos m) (Pos n) = Pos (times_num m n);
times_int Zero_int l = Zero_int;
times_int k Zero_int = Zero_int;

class Timesa a where {
  timesa :: a -> a -> a;
};

class (Timesa a) => Dvda a where {
};

instance Timesa Int where {
  timesa = times_int;
};

instance Dvda Int where {
};

one_int :: Int;
one_int = Pos One;

class Onea a where {
  onea :: a;
};

instance Onea Int where {
  onea = one_int;
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

class Plusa a where {
  plusa :: a -> a -> a;
};

class (Plusa a) => Semigroup_adda a where {
};

class (Onea a, Semigroup_adda a) => Numeral a where {
};

numeral :: forall a. (Numeral a) => Num -> a;
numeral (Bit1 n) = let {
                     m = numeral n;
                   } in plusa (plusa m m) onea;
numeral (Bit0 n) = let {
                     m = numeral n;
                   } in plusa m m;
numeral One = onea;

class Minusa a where {
  minusa :: a -> a -> a;
};

class (Semigroup_adda a) => Cancel_semigroup_adda a where {
};

class (Semigroup_adda a) => Ab_semigroup_adda a where {
};

class (Ab_semigroup_adda a, Cancel_semigroup_adda a,
        Minusa a) => Cancel_ab_semigroup_adda a where {
};

class Zeroa a where {
  zeroa :: a;
};

class (Semigroup_adda a, Zeroa a) => Monoid_adda a where {
};

class (Ab_semigroup_adda a, Monoid_adda a) => Comm_monoid_adda a where {
};

class (Cancel_ab_semigroup_adda a,
        Comm_monoid_adda a) => Cancel_comm_monoid_adda a where {
};

class (Timesa a, Zeroa a) => Mult_zeroa a where {
};

class (Timesa a) => Semigroup_multa a where {
};

class (Ab_semigroup_adda a, Semigroup_multa a) => Semiringa a where {
};

class (Comm_monoid_adda a, Mult_zeroa a, Semiringa a) => Semiring_0a a where {
};

class (Cancel_comm_monoid_adda a, Semiring_0a a) => Semiring_0_cancela a where {
};

class (Semigroup_multa a) => Ab_semigroup_mult a where {
};

class (Ab_semigroup_mult a, Semiringa a) => Comm_semiring a where {
};

class (Comm_semiring a, Semiring_0a a) => Comm_semiring_0 a where {
};

class (Comm_semiring_0 a,
        Semiring_0_cancela a) => Comm_semiring_0_cancel a where {
};

class (Onea a, Timesa a) => Powera a where {
};

class (Semigroup_multa a, Powera a) => Monoid_multa a where {
};

class (Monoid_multa a, Numeral a, Semiringa a) => Semiring_numeral a where {
};

class (Onea a, Zeroa a) => Zero_neq_onea a where {
};

class (Semiring_numeral a, Semiring_0a a,
        Zero_neq_onea a) => Semiring_1a a where {
};

class (Semiring_0_cancela a, Semiring_1a a) => Semiring_1_cancela a where {
};

class (Ab_semigroup_mult a, Monoid_multa a,
        Dvda a) => Comm_monoid_mult a where {
};

class (Comm_monoid_mult a, Comm_semiring_0 a,
        Semiring_1a a) => Comm_semiring_1 a where {
};

class (Comm_semiring_0_cancel a, Comm_semiring_1 a,
        Semiring_1_cancela a) => Comm_semiring_1_cancel a where {
};

class (Comm_semiring_1_cancel a) => Comm_semiring_1_diff_distrib a where {
};

class (Comm_semiring_1_diff_distrib a) => Semiring_parity a where {
};

class (Semiring_0a a) => Semiring_no_zero_divisors a where {
};

class (Comm_semiring_1_diff_distrib a,
        Semiring_no_zero_divisors a) => Semidom a where {
};

class (Dvda a) => Diva a where {
  div :: a -> a -> a;
  mod :: a -> a -> a;
};

class (Diva a, Semidom a) => Semiring_div a where {
};

class (Semiring_div a, Semiring_parity a) => Semiring_div_parity a where {
};

class (Ord a) => Preorder a where {
};

class (Preorder a) => Order a where {
};

class (Ab_semigroup_adda a, Order a) => Ordered_ab_semigroup_add a where {
};

class (Comm_monoid_adda a, Ordered_ab_semigroup_add a,
        Semiringa a) => Ordered_semiring a where {
};

class (Ordered_semiring a,
        Semiring_0_cancela a) => Ordered_cancel_semiring a where {
};

class (Comm_semiring_0 a, Ordered_semiring a) => Ordered_comm_semiring a where {
};

class (Comm_semiring_0_cancel a, Ordered_cancel_semiring a,
        Ordered_comm_semiring a) => Ordered_cancel_comm_semiring a where {
};

class (Cancel_ab_semigroup_adda a,
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

class (Comm_monoid_adda a,
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

class (Semiring_1a a) => Semiring_char_0 a where {
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
    then (plusa (timesa (numeral (Bit0 One)) q) onea, minusa r (numeral l))
    else (timesa (numeral (Bit0 One)) q, r));

divmodb :: forall a. (Semiring_numeral_div a) => Num -> Num -> (a, a);
divmodb (Bit1 m) (Bit0 n) =
  let {
    (q, r) = divmodb m n;
  } in (q, plusa (timesa (numeral (Bit0 One)) r) onea);
divmodb (Bit0 m) (Bit0 n) =
  let {
    (q, r) = divmodb m n;
  } in (q, timesa (numeral (Bit0 One)) r);
divmodb m n =
  (if less_num m n then (zeroa, numeral m)
    else divmod_step n (divmodb m (Bit0 n)));

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

instance Plusa Int where {
  plusa = plus_int;
};

instance Semigroup_adda Int where {
};

instance Cancel_semigroup_adda Int where {
};

instance Ab_semigroup_adda Int where {
};

instance Minusa Int where {
  minusa = minus_int;
};

instance Cancel_ab_semigroup_adda Int where {
};

instance Zeroa Int where {
  zeroa = Zero_int;
};

instance Monoid_adda Int where {
};

instance Comm_monoid_adda Int where {
};

instance Cancel_comm_monoid_adda Int where {
};

instance Mult_zeroa Int where {
};

instance Semigroup_multa Int where {
};

instance Semiringa Int where {
};

instance Semiring_0a Int where {
};

instance Semiring_0_cancela Int where {
};

instance Ab_semigroup_mult Int where {
};

instance Comm_semiring Int where {
};

instance Comm_semiring_0 Int where {
};

instance Comm_semiring_0_cancel Int where {
};

instance Powera Int where {
};

instance Monoid_multa Int where {
};

instance Numeral Int where {
};

instance Semiring_numeral Int where {
};

instance Zero_neq_onea Int where {
};

instance Semiring_1a Int where {
};

instance Semiring_1_cancela Int where {
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

instance Diva Int where {
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
divmod_abs (Pos k) (Neg l) = divmodb k l;
divmod_abs (Neg k) (Pos l) = divmodb k l;
divmod_abs (Neg k) (Neg l) = divmodb k l;
divmod_abs (Pos k) (Pos l) = divmodb k l;

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

times_inta :: Int -> Int -> Int;
times_inta a b = times_int a b;

class Times a where {
  times :: a -> a -> a;
};

class (One a, Times a) => Power a where {
};

instance Times Int where {
  times = times_inta;
};

instance Power Int where {
};

data Rat = Fract Int Int;

newtype Reala = Ratreal Rat;

neg_rat :: Rat -> Rat;
neg_rat (Fract a b) = Fract (uminus_int a) b;

neg_real :: Reala -> Reala;
neg_real (Ratreal x) = Ratreal (neg_rat x);

neg_Reala :: Reala -> Reala;
neg_Reala = neg_real;

class Neg a where {
  neg :: a -> a;
};

instance Neg Reala where {
  neg = neg_Reala;
};

one_real :: Reala;
one_real = Ratreal (Fract (Pos One) (Pos One));

one_Reala :: Reala;
one_Reala = one_real;

instance One Reala where {
  one = one_Reala;
};

eq_int :: Int -> Int -> Bool;
eq_int x y = equal_int x y;

positive :: Int -> Int;
positive k = (if less_int k Zero_int then Zero_int else k);

div_mod :: Int -> Int -> (Int, Int);
div_mod m n =
  (if eq_int n Zero_int || less_int m n then (Zero_int, m)
    else let {
           a = div_mod (minus_int m n) n;
           (q, aa) = a;
         } in (plus_int q (Pos One), aa));

divmod :: Int -> Int -> (Int, Int);
divmod n m = (if eq_int m Zero_int then (Zero_int, n) else div_mod n m);

mod_nat :: Int -> Int -> Int;
mod_nat m n = snd (divmod m n);

gcd_nat :: Int -> Int -> Int;
gcd_nat x y = (if eq_int y Zero_int then x else gcd_nat y (mod_nat x y));

abs_int :: Int -> Int;
abs_int i = (if less_int i Zero_int then uminus_int i else i);

gcd_int :: Int -> Int -> Int;
gcd_int x y = id (gcd_nat (positive (abs_int x)) (positive (abs_int y)));

sgn_int :: Int -> Int;
sgn_int i =
  (if eq_int i Zero_int then Zero_int
    else (if less_int Zero_int i then Pos One else Neg One));

apsnd :: forall a b c. (a -> b) -> (c, a) -> (c, b);
apsnd f (x, y) = (x, f y);

divmoda :: Int -> Int -> (Int, Int);
divmoda k l =
  (if eq_int k Zero_int then (Zero_int, Zero_int)
    else (if eq_int l Zero_int then (Zero_int, k)
           else apsnd (times_int (sgn_int l))
                  (if eq_int (sgn_int k) (sgn_int l)
                    then div_mod (abs_inta k) (abs_inta l)
                    else let {
                           (r, s) = div_mod (abs_inta k) (abs_inta l);
                         } in (if eq_int s Zero_int
                                then (uminus_int r, Zero_int)
                                else (minus_int (uminus_int r) (Pos One),
                                       minus_int (abs_int l) s)))));

div_int :: Int -> Int -> Int;
div_int a b = fst (divmoda a b);

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

plus_real :: Reala -> Reala -> Reala;
plus_real (Ratreal x) (Ratreal y) = Ratreal (plus_rat x y);

plus_Reala :: Reala -> Reala -> Reala;
plus_Reala = plus_real;

class Plus a where {
  plus :: a -> a -> a;
};

instance Plus Reala where {
  plus = plus_Reala;
};

times_rat :: Rat -> Rat -> Rat;
times_rat (Fract a b) (Fract c d) = fract_norm (times_int a c) (times_int b d);

times_real :: Reala -> Reala -> Reala;
times_real (Ratreal x) (Ratreal y) = Ratreal (times_rat x y);

times_Reala :: Reala -> Reala -> Reala;
times_Reala = times_real;

minus_rat :: Rat -> Rat -> Rat;
minus_rat (Fract a b) (Fract c d) =
  (if eq_int b Zero_int then Fract (uminus_int c) d
    else (if eq_int d Zero_int then Fract a b
           else fract_norm (minus_int (times_int a d) (times_int c b))
                  (times_int b d)));

minus_real :: Reala -> Reala -> Reala;
minus_real (Ratreal x) (Ratreal y) = Ratreal (minus_rat x y);

minus_Reala :: Reala -> Reala -> Reala;
minus_Reala = minus_real;

zero_real :: Reala;
zero_real = Ratreal (Fract Zero_int (Pos One));

zero_Reala :: Reala;
zero_Reala = zero_real;

class Minus a where {
  minus :: a -> a -> a;
};

class Zero a where {
  zero :: a;
};

class (Plus a) => Semigroup_add a where {
};

class (Semigroup_add a) => Cancel_semigroup_add a where {
};

class (Semigroup_add a) => Ab_semigroup_add a where {
};

class (Ab_semigroup_add a,
        Cancel_semigroup_add a) => Cancel_ab_semigroup_add a where {
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

class (Minus a, Monoid_add a, Neg a) => Group_add a where {
};

class (Cancel_comm_monoid_add a, Group_add a) => Ab_group_add a where {
};

class (Ab_group_add a, Semiring_0_cancel a) => Ring a where {
};

instance Semigroup_add Reala where {
};

instance Cancel_semigroup_add Reala where {
};

instance Ab_semigroup_add Reala where {
};

instance Cancel_ab_semigroup_add Reala where {
};

instance Zero Reala where {
  zero = zero_Reala;
};

instance Monoid_add Reala where {
};

instance Comm_monoid_add Reala where {
};

instance Cancel_comm_monoid_add Reala where {
};

instance Times Reala where {
  times = times_Reala;
};

instance Mult_zero Reala where {
};

instance Semigroup_mult Reala where {
};

instance Semiring Reala where {
};

instance Semiring_0 Reala where {
};

instance Semiring_0_cancel Reala where {
};

instance Minus Reala where {
  minus = minus_Reala;
};

instance Group_add Reala where {
};

instance Ab_group_add Reala where {
};

instance Ring Reala where {
};

instance Power Reala where {
};

class (One a, Zero a) => Zero_neq_one a where {
};

class (Power a, Semigroup_mult a) => Monoid_mult a where {
};

class (Monoid_mult a, Semiring_0 a, Zero_neq_one a) => Semiring_1 a where {
};

class (Semiring_0_cancel a, Semiring_1 a) => Semiring_1_cancel a where {
};

class (Ring a, Semiring_1_cancel a) => Ring_1 a where {
};

instance Zero_neq_one Reala where {
};

instance Monoid_mult Reala where {
};

instance Semiring_1 Reala where {
};

instance Semiring_1_cancel Reala where {
};

instance Ring_1 Reala where {
};

instance Ord Integer where {
  less_eq = (\ a b -> a <= b);
  less = (\ a b -> a < b);
};

newtype Natural = Nat Integer;

integer_of_natural :: Natural -> Integer;
integer_of_natural (Nat x) = x;

plus_natural :: Natural -> Natural -> Natural;
plus_natural m n = Nat (integer_of_natural m + integer_of_natural n);

instance Plusa Natural where {
  plusa = plus_natural;
};

zero_natural :: Natural;
zero_natural = Nat (0 :: Integer);

instance Zeroa Natural where {
  zeroa = zero_natural;
};

instance Semigroup_adda Natural where {
};

instance Monoid_adda Natural where {
};

class (Times a) => Dvd a where {
};

class (Dvd a) => Div a where {
  diva :: a -> a -> a;
  moda :: a -> a -> a;
};

data Typerepa = Typerep String [Typerepa];

data Itself a = Type;

class Typerep a where {
  typerep :: Itself a -> Typerepa;
};

data Nat = Zero_nat | Suc Nat;

data Set a = Set [a] | Coset [a];

data Nibble = Nibble0 | Nibble1 | Nibble2 | Nibble3 | Nibble4 | Nibble5
  | Nibble6 | Nibble7 | Nibble8 | Nibble9 | NibbleA | NibbleB | NibbleC
  | NibbleD | NibbleE | NibbleF;

data Chara = Chara Nibble Nibble;

data Nibblea = Nibble0a | Nibble1a | Nibble2a | Nibble3a | Nibble4a | Nibble5a
  | Nibble6a | Nibble7a | Nibble8a | Nibble9a | NibbleAa | NibbleBa | NibbleCa
  | NibbleDa | NibbleEa | NibbleFa;

data Char = Char Nibblea Nibblea;

data Floata = Floata Int Int;

data Itselfa a = Typea;

data Term = Const String Typerepa | App Term Term | Abs String Typerepa Term
  | Free String Typerepa;

data Rat_IITN_Rat;

data Chara_IITN_Chara;

data Reala_IITN_Reala;

data Itself_pre_Itself a b;

data Nibble_pre_Nibble;

data Floata_IITN_Floata;

data Itself_IITN_Itself a;

data Nibble_IITN_Nibble;

newtype Narrowing_type = Narrowing_sum_of_products [[Narrowing_type]];

data Narrowing_term = Narrowing_variable [Integer] Narrowing_type
  | Narrowing_constructor Integer [Narrowing_term];

data Narrowing_cons a = Narrowing_cons Narrowing_type [[Narrowing_term] -> a];

ball :: forall a. Set a -> (a -> Bool) -> Bool;
ball (Set xs) p = all p xs;

leta :: forall a b. a -> (a -> b) -> b;
leta s f = f s;

inverse_rat :: Rat -> Rat;
inverse_rat (Fract a b) =
  (if eq_int b Zero_int then Fract (Pos One) Zero_int
    else (if less_int a Zero_int then Fract (uminus_int b) (uminus_int a)
           else Fract b a));

inverse_real :: Reala -> Reala;
inverse_real (Ratreal x) = Ratreal (inverse_rat x);

minus_nat :: Int -> Int -> Int;
minus_nat n m = positive (minus_int (id n) (id m));

power :: forall a. (Power a) => a -> Int -> a;
power a n =
  (if eq_int n Zero_int then one
    else times a (power a (minus_nat n (Pos One))));

pow2 :: Int -> Reala;
pow2 a =
  (if less_eq_int Zero_int a
    then power (Ratreal (Fract (Pos (Bit0 One)) (Pos One))) (positive a)
    else inverse_real
           (power (Ratreal (Fract (Pos (Bit0 One)) (Pos One)))
             (positive (uminus_int a))));

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

scale :: Floata -> Int;
scale (Floata a b) = b;

split :: forall a b c. (a -> b -> c) -> (a, b) -> c;
split f (a, b) = f a b;

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

bitlen :: Int -> Int;
bitlen x =
  (if eq_int x Zero_int then Zero_int
    else (if eq_int x (Neg One) then Pos One
           else plus_int (Pos One) (bitlen (div_int x (Pos (Bit0 One))))));

foldla :: forall a b. (a -> b -> a) -> a -> [b] -> a;
foldla f a [] = a;
foldla f a (x : xs) = foldla f (f a x) xs;

times_float :: Floata -> Floata -> Floata;
times_float (Floata a_m a_e) (Floata b_m b_e) =
  Floata (times_int a_m b_m) (plus_int a_e b_e);

plus_float :: Floata -> Floata -> Floata;
plus_float (Floata a_m a_e) (Floata b_m b_e) =
  (if less_eq_int a_e b_e
    then Floata
           (plus_int a_m
             (times_int b_m
               (power (Pos (Bit0 One)) (positive (minus_int b_e a_e)))))
           a_e
    else Floata
           (plus_int
             (times_int a_m
               (power (Pos (Bit0 One)) (positive (minus_int a_e b_e))))
             b_m)
           b_e);

neg_float :: Floata -> Floata;
neg_float (Floata m e) = Floata (uminus_int m) e;

minus_float :: Floata -> Floata -> Floata;
minus_float z w = plus_float z (neg_float w);

mod_int :: Int -> Int -> Int;
mod_int a b = snd (divmoda a b);

even_int :: Int -> Bool;
even_int x = eq_int (mod_int x (Pos (Bit0 One))) Zero_int;

normfloat :: Floata -> Floata;
normfloat (Floata a b) =
  (if not (eq_int a Zero_int) && even_int a
    then normfloat (Floata (div_int a (Pos (Bit0 One))) (plus_int b (Pos One)))
    else (if eq_int a Zero_int then Floata Zero_int Zero_int else Floata a b));

rapprox_posrat :: Int -> Int -> Int -> Floata;
rapprox_posrat prec x y =
  let {
    l = positive (minus_int (plus_int (id prec) (bitlen y)) (bitlen x));
    xa = times_int x (power (Pos (Bit0 One)) l);
    d = div_int xa y;
    m = mod_int xa y;
  } in normfloat
         (Floata (plus_int d (if eq_int m Zero_int then Zero_int else Pos One))
           (uminus_int (id l)));

lapprox_posrat :: Int -> Int -> Int -> Floata;
lapprox_posrat prec x y =
  let {
    l = positive (minus_int (plus_int (id prec) (bitlen y)) (bitlen x));
    d = div_int (times_int x (power (Pos (Bit0 One)) l)) y;
  } in normfloat (Floata d (uminus_int (id l)));

zero_float :: Floata;
zero_float = Floata Zero_int Zero_int;

rapprox_rat :: Int -> Int -> Int -> Floata;
rapprox_rat prec x y =
  (if eq_int y Zero_int then zero_float
    else (if less_eq_int Zero_int x
           then (if less_int Zero_int y then rapprox_posrat prec x y
                  else neg_float (lapprox_posrat prec x (uminus_int y)))
           else (if less_int Zero_int y
                  then neg_float (lapprox_posrat prec (uminus_int x) y)
                  else rapprox_posrat prec (uminus_int x) (uminus_int y))));

float_divr :: Int -> Floata -> Floata -> Floata;
float_divr prec (Floata m1 s1) (Floata m2 s2) =
  let {
    r = rapprox_rat prec m1 m2;
    f = Floata (Pos One) (minus_int s1 s2);
  } in times_float f r;

ceiling_fl :: Floata -> Floata;
ceiling_fl (Floata m e) =
  (if less_eq_int Zero_int e then Floata m e
    else Floata
           (plus_int
             (div_int m (power (Pos (Bit0 One)) (positive (uminus_int e))))
             (Pos One))
           Zero_int);

lb_mod :: Int -> Floata -> Floata -> Floata -> Floata;
lb_mod prec x ub lb =
  minus_float x (times_float (ceiling_fl (float_divr prec x lb)) ub);

of_int :: forall a. (Ring_1 a) => Int -> a;
of_int k =
  (if eq_int k Zero_int then zero
    else (if less_int k Zero_int then neg (of_int (uminus_int k))
           else let {
                  (l, m) = divmoda k (Pos (Bit0 One));
                  la = of_int l;
                } in (if eq_int m Zero_int then plus la la
                       else plus (plus la la) one)));

lapprox_rat :: Int -> Int -> Int -> Floata;
lapprox_rat prec x y =
  (if eq_int y Zero_int then zero_float
    else (if less_eq_int Zero_int x
           then (if less_int Zero_int y then lapprox_posrat prec x y
                  else neg_float (rapprox_posrat prec x (uminus_int y)))
           else (if less_int Zero_int y
                  then neg_float (rapprox_posrat prec (uminus_int x) y)
                  else lapprox_posrat prec (uminus_int x) (uminus_int y))));

float_divl :: Int -> Floata -> Floata -> Floata;
float_divl prec (Floata m1 s1) (Floata m2 s2) =
  let {
    l = lapprox_rat prec m1 m2;
    f = Floata (Pos One) (minus_int s1 s2);
  } in times_float f l;

floor_fl :: Floata -> Floata;
floor_fl (Floata m e) =
  (if less_eq_int Zero_int e then Floata m e
    else Floata (div_int m (power (Pos (Bit0 One)) (positive (uminus_int e))))
           Zero_int);

ub_mod :: Int -> Floata -> Floata -> Floata -> Floata;
ub_mod prec x ub lb =
  minus_float x (times_float (floor_fl (float_divl prec x ub)) lb);

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

eq_float :: Floata -> Floata -> Bool;
eq_float (Floata int1a int2a) (Floata int1 int2) =
  eq_int int1a int1 && eq_int int2a int2;

less_rat :: Rat -> Rat -> Bool;
less_rat (Fract a b) (Fract c d) =
  (if eq_int b Zero_int
    then less_int Zero_int (times_int (sgn_int c) (sgn_int d))
    else (if eq_int d Zero_int
           then less_int (times_int (sgn_int a) (sgn_int b)) Zero_int
           else less_int (times_int (times_int a (abs_int d)) (sgn_int b))
                  (times_int c (times_int (abs_int b) (sgn_int d)))));

mantissa :: Floata -> Int;
mantissa (Floata a b) = a;

of_float :: Floata -> Reala;
of_float (Floata a b) = times_real (of_int a) (pow2 b);

round_up :: Int -> Floata -> Floata;
round_up prec (Floata m e) =
  let {
    d = minus_int (bitlen m) (id prec);
  } in (if less_int Zero_int d
         then let {
                p = power (Pos (Bit0 One)) (positive d);
                n = div_int m p;
                r = mod_int m p;
              } in Floata
                     (plus_int n
                       (if eq_int r Zero_int then Zero_int else Pos One))
                     (plus_int e d)
         else Floata m e);

float_abs :: Floata -> Floata;
float_abs (Floata m e) = Floata (abs_int m) e;

abs_float :: Floata -> Floata;
abs_float x = float_abs x;

less_real :: Reala -> Reala -> Bool;
less_real (Ratreal x) (Ratreal y) = less_rat x y;

one_float :: Floata;
one_float = Floata (Pos One) Zero_int;

float_nprt :: Floata -> Floata;
float_nprt (Floata a e) =
  (if less_eq_int Zero_int a then zero_float else Floata a e);

float_pprt :: Floata -> Floata;
float_pprt (Floata a e) =
  (if less_eq_int Zero_int a then Floata a e else zero_float);

float_size :: Floata -> Int;
float_size (Floata int1 int2) = Zero_int;

less_float :: Floata -> Floata -> Bool;
less_float z w = less_real (of_float z) (of_float w);

round_down :: Int -> Floata -> Floata;
round_down prec (Floata m e) =
  let {
    d = minus_int (bitlen m) (id prec);
  } in (if less_int Zero_int d
         then let {
                p = power (Pos (Bit0 One)) (positive d);
                n = div_int m p;
              } in Floata n (plus_int e d)
         else Floata m e);

rec_Rat :: forall a. (Int -> Int -> a) -> Rat -> a;
rec_Rat f (Fract x1 x2) = f x1 x2;

less_eq_rat :: Rat -> Rat -> Bool;
less_eq_rat (Fract a b) (Fract c d) =
  (if eq_int b Zero_int
    then less_eq_int Zero_int (times_int (sgn_int c) (sgn_int d))
    else (if eq_int d Zero_int
           then less_eq_int (times_int (sgn_int a) (sgn_int b)) Zero_int
           else less_eq_int (times_int (times_int a (abs_int d)) (sgn_int b))
                  (times_int (times_int c (abs_int b)) (sgn_int d))));

bot_set :: forall a. Set a;
bot_set = Set [];

set_Itself :: forall a. Itselfa a -> Set a;
set_Itself Typea = bot_set;

pred_Itself :: forall a. (a -> Bool) -> Itselfa a -> Bool;
pred_Itself p = (\ x -> ball (set_Itself x) p);

size_Rat :: Rat -> Nat;
size_Rat (Fract x1 x2) = Zero_nat;

less_eq_real :: Reala -> Reala -> Bool;
less_eq_real (Ratreal x) (Ratreal y) = less_eq_rat x y;

less_eq_float :: Floata -> Floata -> Bool;
less_eq_float z w = less_eq_real (of_float z) (of_float w);

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

of_nat_aux :: forall a. (Semiring_1a a) => (a -> a) -> Nat -> a -> a;
of_nat_aux inc Zero_nat i = i;
of_nat_aux inc (Suc n) i = of_nat_aux inc n (inc i);

of_nat :: forall a. (Semiring_1a a) => Nat -> a;
of_nat n = of_nat_aux (\ i -> plusa i onea) n zeroa;

plus_nat :: Nat -> Nat -> Nat;
plus_nat (Suc m) n = plus_nat m (Suc n);
plus_nat Zero_nat n = n;

one_nat :: Nat;
one_nat = Suc Zero_nat;

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

collapse :: forall a b. (a -> (a -> (b, a), a)) -> a -> (b, a);
collapse f = scomp f id;

valapp ::
  forall a b. (a -> b, () -> Term) -> (a, () -> Term) -> (b, () -> Term);
valapp (f, tf) (x, tx) = (f x, (\ _ -> App (tf ()) (tx ())));

listsum :: forall a. (Monoid_adda a) => [a] -> a;
listsum xs = foldr plusa xs zeroa;

select_weight ::
  forall a. [(Natural, a)] -> (Natural, Natural) -> (a, (Natural, Natural));
select_weight xs =
  scomp (range (listsum (map fst xs))) (\ k -> (\ a -> (pick xs k, a)));

random_aux_Rat ::
  Natural ->
    Natural -> (Natural, Natural) -> ((Rat, () -> Term), (Natural, Natural));
random_aux_Rat i j s =
  collapse
    (select_weight
      [(one_natural,
         scomp (random_int j)
           (\ x ->
             scomp (random_int j)
               (\ y ->
                 (\ a ->
                   (valapp
                      (valapp
                        (Fract,
                          (\ _ ->
                            Const "Float.Rat.Fract"
                              (Typerep "fun"
                                [Typerep "Int.int" [],
                                  Typerep "fun"
                                    [Typerep "Int.int" [],
                                      Typerep "Float.Rat" []]])))
                        x)
                      y,
                     a)))))])
    s;

rec_Chara :: forall a. (Nibble -> Nibble -> a) -> Chara -> a;
rec_Chara f (Chara x1 x2) = f x1 x2;

rec_Reala :: forall a. (Rat -> a) -> Reala -> a;
rec_Reala f (Ratreal x) = f x;

size_Chara :: Chara -> Nat;
size_Chara (Chara x1 x2) = Zero_nat;

size_Reala :: Reala -> Nat;
size_Reala (Ratreal x) = Zero_nat;

random_aux_Nibble ::
  Natural ->
    Natural -> (Natural, Natural) -> ((Nibble, () -> Term), (Natural, Natural));
random_aux_Nibble i j s =
  collapse
    (select_weight
      [(one_natural,
         (\ a ->
           ((Nibble0,
              (\ _ ->
                Const "Float.Nibble.Nibble0" (Typerep "Float.Nibble" []))),
             a))),
        (one_natural,
          (\ a ->
            ((Nibble1,
               (\ _ ->
                 Const "Float.Nibble.Nibble1" (Typerep "Float.Nibble" []))),
              a))),
        (one_natural,
          (\ a ->
            ((Nibble2,
               (\ _ ->
                 Const "Float.Nibble.Nibble2" (Typerep "Float.Nibble" []))),
              a))),
        (one_natural,
          (\ a ->
            ((Nibble3,
               (\ _ ->
                 Const "Float.Nibble.Nibble3" (Typerep "Float.Nibble" []))),
              a))),
        (one_natural,
          (\ a ->
            ((Nibble4,
               (\ _ ->
                 Const "Float.Nibble.Nibble4" (Typerep "Float.Nibble" []))),
              a))),
        (one_natural,
          (\ a ->
            ((Nibble5,
               (\ _ ->
                 Const "Float.Nibble.Nibble5" (Typerep "Float.Nibble" []))),
              a))),
        (one_natural,
          (\ a ->
            ((Nibble6,
               (\ _ ->
                 Const "Float.Nibble.Nibble6" (Typerep "Float.Nibble" []))),
              a))),
        (one_natural,
          (\ a ->
            ((Nibble7,
               (\ _ ->
                 Const "Float.Nibble.Nibble7" (Typerep "Float.Nibble" []))),
              a))),
        (one_natural,
          (\ a ->
            ((Nibble8,
               (\ _ ->
                 Const "Float.Nibble.Nibble8" (Typerep "Float.Nibble" []))),
              a))),
        (one_natural,
          (\ a ->
            ((Nibble9,
               (\ _ ->
                 Const "Float.Nibble.Nibble9" (Typerep "Float.Nibble" []))),
              a))),
        (one_natural,
          (\ a ->
            ((NibbleA,
               (\ _ ->
                 Const "Float.Nibble.NibbleA" (Typerep "Float.Nibble" []))),
              a))),
        (one_natural,
          (\ a ->
            ((NibbleB,
               (\ _ ->
                 Const "Float.Nibble.NibbleB" (Typerep "Float.Nibble" []))),
              a))),
        (one_natural,
          (\ a ->
            ((NibbleC,
               (\ _ ->
                 Const "Float.Nibble.NibbleC" (Typerep "Float.Nibble" []))),
              a))),
        (one_natural,
          (\ a ->
            ((NibbleD,
               (\ _ ->
                 Const "Float.Nibble.NibbleD" (Typerep "Float.Nibble" []))),
              a))),
        (one_natural,
          (\ a ->
            ((NibbleE,
               (\ _ ->
                 Const "Float.Nibble.NibbleE" (Typerep "Float.Nibble" []))),
              a))),
        (one_natural,
          (\ a ->
            ((NibbleF,
               (\ _ ->
                 Const "Float.Nibble.NibbleF" (Typerep "Float.Nibble" []))),
              a)))])
    s;

random_Nibble ::
  Natural -> (Natural, Natural) -> ((Nibble, () -> Term), (Natural, Natural));
random_Nibble i = random_aux_Nibble i i;

random_aux_Chara ::
  Natural ->
    Natural -> (Natural, Natural) -> ((Chara, () -> Term), (Natural, Natural));
random_aux_Chara i j s =
  collapse
    (select_weight
      [(one_natural,
         scomp (random_Nibble j)
           (\ x ->
             scomp (random_Nibble j)
               (\ y ->
                 (\ a ->
                   (valapp
                      (valapp
                        (Chara,
                          (\ _ ->
                            Const "Float.Chara.Chara"
                              (Typerep "fun"
                                [Typerep "Float.Nibble" [],
                                  Typerep "fun"
                                    [Typerep "Float.Nibble" [],
                                      Typerep "Float.Chara" []]])))
                        x)
                      y,
                     a)))))])
    s;

random_Rat ::
  Natural -> (Natural, Natural) -> ((Rat, () -> Term), (Natural, Natural));
random_Rat i = random_aux_Rat i i;

random_aux_Reala ::
  Natural ->
    Natural -> (Natural, Natural) -> ((Reala, () -> Term), (Natural, Natural));
random_aux_Reala i j s =
  collapse
    (select_weight
      [(one_natural,
         scomp (random_Rat j)
           (\ x ->
             (\ a ->
               (valapp
                  (Ratreal,
                    (\ _ ->
                      Const "Float.Reala.Ratreal"
                        (Typerep "fun"
                          [Typerep "Float.Rat" [], Typerep "Float.Reala" []])))
                  x,
                 a))))])
    s;

rec_Floata :: forall a. (Int -> Int -> a) -> Floata -> a;
rec_Floata f (Floata x1 x2) = f x1 x2;

map_Itself :: forall a b. (a -> b) -> Itselfa a -> Itselfa b;
map_Itself f Typea = Typea;

rec_Itself :: forall a b. a -> Itselfa b -> a;
rec_Itself f Typea = f;

rel_Itself :: forall a b. (a -> b -> Bool) -> Itselfa a -> Itselfa b -> Bool;
rel_Itself r Typea Typea = True;

rec_Nibble ::
  forall a.
    a -> a -> a -> a -> a -> a -> a -> a ->
 a -> a -> a -> a -> a -> a -> a -> a -> Nibble -> a;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble0 = f1;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble1 = f2;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble2 = f3;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble3 = f4;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble4 = f5;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble5 = f6;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble6 = f7;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble7 = f8;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble8 = f9;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble9 = f10;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 NibbleA = f11;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 NibbleB = f12;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 NibbleC = f13;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 NibbleD = f14;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 NibbleE = f15;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 NibbleF = f16;

random_aux_Floata ::
  Natural ->
    Natural -> (Natural, Natural) -> ((Floata, () -> Term), (Natural, Natural));
random_aux_Floata i j s =
  collapse
    (select_weight
      [(one_natural,
         scomp (random_int j)
           (\ x ->
             scomp (random_int j)
               (\ y ->
                 (\ a ->
                   (valapp
                      (valapp
                        (Floata,
                          (\ _ ->
                            Const "Float.Floata.Floata"
                              (Typerep "fun"
                                [Typerep "Int.int" [],
                                  Typerep "fun"
                                    [Typerep "Int.int" [],
                                      Typerep "Float.Floata" []]])))
                        x)
                      y,
                     a)))))])
    s;

random_aux_Itself ::
  forall a.
    (Typerep a) => Natural ->
                     Natural ->
                       (Natural, Natural) ->
                         ((Itselfa a, () -> Term), (Natural, Natural));
random_aux_Itself i j s =
  collapse
    (select_weight
      [(one_natural,
         (\ a ->
           ((Typea,
              (\ _ ->
                Const "Float.Itself.Type"
                  (Typerep "Float.Itself"
                    [(typerep :: Itself a -> Typerepa) Type]))),
             a)))])
    s;

size_Floata :: Floata -> Nat;
size_Floata (Floata x1 x2) = Zero_nat;

size_Itself :: forall a. (a -> Nat) -> Itselfa a -> Nat;
size_Itself x Typea = Zero_nat;

size_Nibble :: Nibble -> Nat;
size_Nibble Nibble0 = Zero_nat;
size_Nibble Nibble1 = Zero_nat;
size_Nibble Nibble2 = Zero_nat;
size_Nibble Nibble3 = Zero_nat;
size_Nibble Nibble4 = Zero_nat;
size_Nibble Nibble5 = Zero_nat;
size_Nibble Nibble6 = Zero_nat;
size_Nibble Nibble7 = Zero_nat;
size_Nibble Nibble8 = Zero_nat;
size_Nibble Nibble9 = Zero_nat;
size_Nibble NibbleA = Zero_nat;
size_Nibble NibbleB = Zero_nat;
size_Nibble NibbleC = Zero_nat;
size_Nibble NibbleD = Zero_nat;
size_Nibble NibbleE = Zero_nat;
size_Nibble NibbleF = Zero_nat;

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

diva_int :: Int -> Int -> Int;
diva_int = div_int;

moda_int :: Int -> Int -> Int;
moda_int = mod_int;

plus_inta :: Int -> Int -> Int;
plus_inta a b = plus_int a b;

zero_int :: Int;
zero_int = Zero_int;

size_Rata :: Rat -> Nat;
size_Rata (Fract x1 x2) = Zero_nat;

equal_Rat :: Rat -> Rat -> Bool;
equal_Rat (Fract x1 x2) (Fract y1 y2) = equal_int x1 y1 && equal_int x2 y2;

non_empty :: Narrowing_type -> Bool;
non_empty (Narrowing_sum_of_products ps) = not (null ps);

drawn_from :: forall a. [a] -> Narrowing_cons a;
drawn_from xs =
  Narrowing_cons (Narrowing_sum_of_products (map (\ _ -> []) xs))
    (map (\ x _ -> x) xs);

size_Charaa :: Chara -> Nat;
size_Charaa (Chara x1 x2) = Zero_nat;

size_Realaa :: Reala -> Nat;
size_Realaa (Ratreal x) = Zero_nat;

around_zero :: Int -> [Int];
around_zero i =
  (if less_int i Zero_int then []
    else (if equal_int i Zero_int then [Zero_int]
           else around_zero (minus_int i (Pos One)) ++ [i, uminus_int i]));

equal_Nibble :: Nibble -> Nibble -> Bool;
equal_Nibble NibbleE NibbleF = False;
equal_Nibble NibbleF NibbleE = False;
equal_Nibble NibbleD NibbleF = False;
equal_Nibble NibbleF NibbleD = False;
equal_Nibble NibbleD NibbleE = False;
equal_Nibble NibbleE NibbleD = False;
equal_Nibble NibbleC NibbleF = False;
equal_Nibble NibbleF NibbleC = False;
equal_Nibble NibbleC NibbleE = False;
equal_Nibble NibbleE NibbleC = False;
equal_Nibble NibbleC NibbleD = False;
equal_Nibble NibbleD NibbleC = False;
equal_Nibble NibbleB NibbleF = False;
equal_Nibble NibbleF NibbleB = False;
equal_Nibble NibbleB NibbleE = False;
equal_Nibble NibbleE NibbleB = False;
equal_Nibble NibbleB NibbleD = False;
equal_Nibble NibbleD NibbleB = False;
equal_Nibble NibbleB NibbleC = False;
equal_Nibble NibbleC NibbleB = False;
equal_Nibble NibbleA NibbleF = False;
equal_Nibble NibbleF NibbleA = False;
equal_Nibble NibbleA NibbleE = False;
equal_Nibble NibbleE NibbleA = False;
equal_Nibble NibbleA NibbleD = False;
equal_Nibble NibbleD NibbleA = False;
equal_Nibble NibbleA NibbleC = False;
equal_Nibble NibbleC NibbleA = False;
equal_Nibble NibbleA NibbleB = False;
equal_Nibble NibbleB NibbleA = False;
equal_Nibble Nibble9 NibbleF = False;
equal_Nibble NibbleF Nibble9 = False;
equal_Nibble Nibble9 NibbleE = False;
equal_Nibble NibbleE Nibble9 = False;
equal_Nibble Nibble9 NibbleD = False;
equal_Nibble NibbleD Nibble9 = False;
equal_Nibble Nibble9 NibbleC = False;
equal_Nibble NibbleC Nibble9 = False;
equal_Nibble Nibble9 NibbleB = False;
equal_Nibble NibbleB Nibble9 = False;
equal_Nibble Nibble9 NibbleA = False;
equal_Nibble NibbleA Nibble9 = False;
equal_Nibble Nibble8 NibbleF = False;
equal_Nibble NibbleF Nibble8 = False;
equal_Nibble Nibble8 NibbleE = False;
equal_Nibble NibbleE Nibble8 = False;
equal_Nibble Nibble8 NibbleD = False;
equal_Nibble NibbleD Nibble8 = False;
equal_Nibble Nibble8 NibbleC = False;
equal_Nibble NibbleC Nibble8 = False;
equal_Nibble Nibble8 NibbleB = False;
equal_Nibble NibbleB Nibble8 = False;
equal_Nibble Nibble8 NibbleA = False;
equal_Nibble NibbleA Nibble8 = False;
equal_Nibble Nibble8 Nibble9 = False;
equal_Nibble Nibble9 Nibble8 = False;
equal_Nibble Nibble7 NibbleF = False;
equal_Nibble NibbleF Nibble7 = False;
equal_Nibble Nibble7 NibbleE = False;
equal_Nibble NibbleE Nibble7 = False;
equal_Nibble Nibble7 NibbleD = False;
equal_Nibble NibbleD Nibble7 = False;
equal_Nibble Nibble7 NibbleC = False;
equal_Nibble NibbleC Nibble7 = False;
equal_Nibble Nibble7 NibbleB = False;
equal_Nibble NibbleB Nibble7 = False;
equal_Nibble Nibble7 NibbleA = False;
equal_Nibble NibbleA Nibble7 = False;
equal_Nibble Nibble7 Nibble9 = False;
equal_Nibble Nibble9 Nibble7 = False;
equal_Nibble Nibble7 Nibble8 = False;
equal_Nibble Nibble8 Nibble7 = False;
equal_Nibble Nibble6 NibbleF = False;
equal_Nibble NibbleF Nibble6 = False;
equal_Nibble Nibble6 NibbleE = False;
equal_Nibble NibbleE Nibble6 = False;
equal_Nibble Nibble6 NibbleD = False;
equal_Nibble NibbleD Nibble6 = False;
equal_Nibble Nibble6 NibbleC = False;
equal_Nibble NibbleC Nibble6 = False;
equal_Nibble Nibble6 NibbleB = False;
equal_Nibble NibbleB Nibble6 = False;
equal_Nibble Nibble6 NibbleA = False;
equal_Nibble NibbleA Nibble6 = False;
equal_Nibble Nibble6 Nibble9 = False;
equal_Nibble Nibble9 Nibble6 = False;
equal_Nibble Nibble6 Nibble8 = False;
equal_Nibble Nibble8 Nibble6 = False;
equal_Nibble Nibble6 Nibble7 = False;
equal_Nibble Nibble7 Nibble6 = False;
equal_Nibble Nibble5 NibbleF = False;
equal_Nibble NibbleF Nibble5 = False;
equal_Nibble Nibble5 NibbleE = False;
equal_Nibble NibbleE Nibble5 = False;
equal_Nibble Nibble5 NibbleD = False;
equal_Nibble NibbleD Nibble5 = False;
equal_Nibble Nibble5 NibbleC = False;
equal_Nibble NibbleC Nibble5 = False;
equal_Nibble Nibble5 NibbleB = False;
equal_Nibble NibbleB Nibble5 = False;
equal_Nibble Nibble5 NibbleA = False;
equal_Nibble NibbleA Nibble5 = False;
equal_Nibble Nibble5 Nibble9 = False;
equal_Nibble Nibble9 Nibble5 = False;
equal_Nibble Nibble5 Nibble8 = False;
equal_Nibble Nibble8 Nibble5 = False;
equal_Nibble Nibble5 Nibble7 = False;
equal_Nibble Nibble7 Nibble5 = False;
equal_Nibble Nibble5 Nibble6 = False;
equal_Nibble Nibble6 Nibble5 = False;
equal_Nibble Nibble4 NibbleF = False;
equal_Nibble NibbleF Nibble4 = False;
equal_Nibble Nibble4 NibbleE = False;
equal_Nibble NibbleE Nibble4 = False;
equal_Nibble Nibble4 NibbleD = False;
equal_Nibble NibbleD Nibble4 = False;
equal_Nibble Nibble4 NibbleC = False;
equal_Nibble NibbleC Nibble4 = False;
equal_Nibble Nibble4 NibbleB = False;
equal_Nibble NibbleB Nibble4 = False;
equal_Nibble Nibble4 NibbleA = False;
equal_Nibble NibbleA Nibble4 = False;
equal_Nibble Nibble4 Nibble9 = False;
equal_Nibble Nibble9 Nibble4 = False;
equal_Nibble Nibble4 Nibble8 = False;
equal_Nibble Nibble8 Nibble4 = False;
equal_Nibble Nibble4 Nibble7 = False;
equal_Nibble Nibble7 Nibble4 = False;
equal_Nibble Nibble4 Nibble6 = False;
equal_Nibble Nibble6 Nibble4 = False;
equal_Nibble Nibble4 Nibble5 = False;
equal_Nibble Nibble5 Nibble4 = False;
equal_Nibble Nibble3 NibbleF = False;
equal_Nibble NibbleF Nibble3 = False;
equal_Nibble Nibble3 NibbleE = False;
equal_Nibble NibbleE Nibble3 = False;
equal_Nibble Nibble3 NibbleD = False;
equal_Nibble NibbleD Nibble3 = False;
equal_Nibble Nibble3 NibbleC = False;
equal_Nibble NibbleC Nibble3 = False;
equal_Nibble Nibble3 NibbleB = False;
equal_Nibble NibbleB Nibble3 = False;
equal_Nibble Nibble3 NibbleA = False;
equal_Nibble NibbleA Nibble3 = False;
equal_Nibble Nibble3 Nibble9 = False;
equal_Nibble Nibble9 Nibble3 = False;
equal_Nibble Nibble3 Nibble8 = False;
equal_Nibble Nibble8 Nibble3 = False;
equal_Nibble Nibble3 Nibble7 = False;
equal_Nibble Nibble7 Nibble3 = False;
equal_Nibble Nibble3 Nibble6 = False;
equal_Nibble Nibble6 Nibble3 = False;
equal_Nibble Nibble3 Nibble5 = False;
equal_Nibble Nibble5 Nibble3 = False;
equal_Nibble Nibble3 Nibble4 = False;
equal_Nibble Nibble4 Nibble3 = False;
equal_Nibble Nibble2 NibbleF = False;
equal_Nibble NibbleF Nibble2 = False;
equal_Nibble Nibble2 NibbleE = False;
equal_Nibble NibbleE Nibble2 = False;
equal_Nibble Nibble2 NibbleD = False;
equal_Nibble NibbleD Nibble2 = False;
equal_Nibble Nibble2 NibbleC = False;
equal_Nibble NibbleC Nibble2 = False;
equal_Nibble Nibble2 NibbleB = False;
equal_Nibble NibbleB Nibble2 = False;
equal_Nibble Nibble2 NibbleA = False;
equal_Nibble NibbleA Nibble2 = False;
equal_Nibble Nibble2 Nibble9 = False;
equal_Nibble Nibble9 Nibble2 = False;
equal_Nibble Nibble2 Nibble8 = False;
equal_Nibble Nibble8 Nibble2 = False;
equal_Nibble Nibble2 Nibble7 = False;
equal_Nibble Nibble7 Nibble2 = False;
equal_Nibble Nibble2 Nibble6 = False;
equal_Nibble Nibble6 Nibble2 = False;
equal_Nibble Nibble2 Nibble5 = False;
equal_Nibble Nibble5 Nibble2 = False;
equal_Nibble Nibble2 Nibble4 = False;
equal_Nibble Nibble4 Nibble2 = False;
equal_Nibble Nibble2 Nibble3 = False;
equal_Nibble Nibble3 Nibble2 = False;
equal_Nibble Nibble1 NibbleF = False;
equal_Nibble NibbleF Nibble1 = False;
equal_Nibble Nibble1 NibbleE = False;
equal_Nibble NibbleE Nibble1 = False;
equal_Nibble Nibble1 NibbleD = False;
equal_Nibble NibbleD Nibble1 = False;
equal_Nibble Nibble1 NibbleC = False;
equal_Nibble NibbleC Nibble1 = False;
equal_Nibble Nibble1 NibbleB = False;
equal_Nibble NibbleB Nibble1 = False;
equal_Nibble Nibble1 NibbleA = False;
equal_Nibble NibbleA Nibble1 = False;
equal_Nibble Nibble1 Nibble9 = False;
equal_Nibble Nibble9 Nibble1 = False;
equal_Nibble Nibble1 Nibble8 = False;
equal_Nibble Nibble8 Nibble1 = False;
equal_Nibble Nibble1 Nibble7 = False;
equal_Nibble Nibble7 Nibble1 = False;
equal_Nibble Nibble1 Nibble6 = False;
equal_Nibble Nibble6 Nibble1 = False;
equal_Nibble Nibble1 Nibble5 = False;
equal_Nibble Nibble5 Nibble1 = False;
equal_Nibble Nibble1 Nibble4 = False;
equal_Nibble Nibble4 Nibble1 = False;
equal_Nibble Nibble1 Nibble3 = False;
equal_Nibble Nibble3 Nibble1 = False;
equal_Nibble Nibble1 Nibble2 = False;
equal_Nibble Nibble2 Nibble1 = False;
equal_Nibble Nibble0 NibbleF = False;
equal_Nibble NibbleF Nibble0 = False;
equal_Nibble Nibble0 NibbleE = False;
equal_Nibble NibbleE Nibble0 = False;
equal_Nibble Nibble0 NibbleD = False;
equal_Nibble NibbleD Nibble0 = False;
equal_Nibble Nibble0 NibbleC = False;
equal_Nibble NibbleC Nibble0 = False;
equal_Nibble Nibble0 NibbleB = False;
equal_Nibble NibbleB Nibble0 = False;
equal_Nibble Nibble0 NibbleA = False;
equal_Nibble NibbleA Nibble0 = False;
equal_Nibble Nibble0 Nibble9 = False;
equal_Nibble Nibble9 Nibble0 = False;
equal_Nibble Nibble0 Nibble8 = False;
equal_Nibble Nibble8 Nibble0 = False;
equal_Nibble Nibble0 Nibble7 = False;
equal_Nibble Nibble7 Nibble0 = False;
equal_Nibble Nibble0 Nibble6 = False;
equal_Nibble Nibble6 Nibble0 = False;
equal_Nibble Nibble0 Nibble5 = False;
equal_Nibble Nibble5 Nibble0 = False;
equal_Nibble Nibble0 Nibble4 = False;
equal_Nibble Nibble4 Nibble0 = False;
equal_Nibble Nibble0 Nibble3 = False;
equal_Nibble Nibble3 Nibble0 = False;
equal_Nibble Nibble0 Nibble2 = False;
equal_Nibble Nibble2 Nibble0 = False;
equal_Nibble Nibble0 Nibble1 = False;
equal_Nibble Nibble1 Nibble0 = False;
equal_Nibble NibbleF NibbleF = True;
equal_Nibble NibbleE NibbleE = True;
equal_Nibble NibbleD NibbleD = True;
equal_Nibble NibbleC NibbleC = True;
equal_Nibble NibbleB NibbleB = True;
equal_Nibble NibbleA NibbleA = True;
equal_Nibble Nibble9 Nibble9 = True;
equal_Nibble Nibble8 Nibble8 = True;
equal_Nibble Nibble7 Nibble7 = True;
equal_Nibble Nibble6 Nibble6 = True;
equal_Nibble Nibble5 Nibble5 = True;
equal_Nibble Nibble4 Nibble4 = True;
equal_Nibble Nibble3 Nibble3 = True;
equal_Nibble Nibble2 Nibble2 = True;
equal_Nibble Nibble1 Nibble1 = True;
equal_Nibble Nibble0 Nibble0 = True;

equal_Chara :: Chara -> Chara -> Bool;
equal_Chara (Chara x1 x2) (Chara y1 y2) =
  equal_Nibble x1 y1 && equal_Nibble x2 y2;

equal_Reala :: Reala -> Reala -> Bool;
equal_Reala (Ratreal x) (Ratreal ya) = equal_Rat x ya;

size_Floataa :: Floata -> Nat;
size_Floataa (Floata x1 x2) = Zero_nat;

size_Itselfa :: forall a. Itselfa a -> Nat;
size_Itselfa Typea = Zero_nat;

size_Nibblea :: Nibble -> Nat;
size_Nibblea Nibble0 = Zero_nat;
size_Nibblea Nibble1 = Zero_nat;
size_Nibblea Nibble2 = Zero_nat;
size_Nibblea Nibble3 = Zero_nat;
size_Nibblea Nibble4 = Zero_nat;
size_Nibblea Nibble5 = Zero_nat;
size_Nibblea Nibble6 = Zero_nat;
size_Nibblea Nibble7 = Zero_nat;
size_Nibblea Nibble8 = Zero_nat;
size_Nibblea Nibble9 = Zero_nat;
size_Nibblea NibbleA = Zero_nat;
size_Nibblea NibbleB = Zero_nat;
size_Nibblea NibbleC = Zero_nat;
size_Nibblea NibbleD = Zero_nat;
size_Nibblea NibbleE = Zero_nat;
size_Nibblea NibbleF = Zero_nat;

term_of_Rat :: Rat -> Term;
term_of_Rat (Fract a b) =
  App (App (Const "Float.Rat.Fract"
             (Typerep "fun"
               [Typerep "Int.int" [],
                 Typerep "fun" [Typerep "Int.int" [], Typerep "Float.Rat" []]]))
        (term_of_int a))
    (term_of_int b);

typerep_Rat :: Itself Rat -> Typerepa;
typerep_Rat t = Typerep "Float.Rat" [];

equal_Floata :: Floata -> Floata -> Bool;
equal_Floata (Floata x1 x2) (Floata y1 y2) = equal_int x1 y1 && equal_int x2 y2;

equal_Itself :: forall a. Itselfa a -> Itselfa a -> Bool;
equal_Itself Typea Typea = True;

random_Chara ::
  Natural -> (Natural, Natural) -> ((Chara, () -> Term), (Natural, Natural));
random_Chara i = random_aux_Chara i i;

random_Reala ::
  Natural -> (Natural, Natural) -> ((Reala, () -> Term), (Natural, Natural));
random_Reala i = random_aux_Reala i i;

random_Floata ::
  Natural -> (Natural, Natural) -> ((Floata, () -> Term), (Natural, Natural));
random_Floata i = random_aux_Floata i i;

random_Itself ::
  forall a.
    (Typerep a) => Natural ->
                     (Natural, Natural) ->
                       ((Itselfa a, () -> Term), (Natural, Natural));
random_Itself i = random_aux_Itself i i;

term_of_Nibble :: Nibble -> Term;
term_of_Nibble NibbleF =
  Const "Float.Nibble.NibbleF" (Typerep "Float.Nibble" []);
term_of_Nibble NibbleE =
  Const "Float.Nibble.NibbleE" (Typerep "Float.Nibble" []);
term_of_Nibble NibbleD =
  Const "Float.Nibble.NibbleD" (Typerep "Float.Nibble" []);
term_of_Nibble NibbleC =
  Const "Float.Nibble.NibbleC" (Typerep "Float.Nibble" []);
term_of_Nibble NibbleB =
  Const "Float.Nibble.NibbleB" (Typerep "Float.Nibble" []);
term_of_Nibble NibbleA =
  Const "Float.Nibble.NibbleA" (Typerep "Float.Nibble" []);
term_of_Nibble Nibble9 =
  Const "Float.Nibble.Nibble9" (Typerep "Float.Nibble" []);
term_of_Nibble Nibble8 =
  Const "Float.Nibble.Nibble8" (Typerep "Float.Nibble" []);
term_of_Nibble Nibble7 =
  Const "Float.Nibble.Nibble7" (Typerep "Float.Nibble" []);
term_of_Nibble Nibble6 =
  Const "Float.Nibble.Nibble6" (Typerep "Float.Nibble" []);
term_of_Nibble Nibble5 =
  Const "Float.Nibble.Nibble5" (Typerep "Float.Nibble" []);
term_of_Nibble Nibble4 =
  Const "Float.Nibble.Nibble4" (Typerep "Float.Nibble" []);
term_of_Nibble Nibble3 =
  Const "Float.Nibble.Nibble3" (Typerep "Float.Nibble" []);
term_of_Nibble Nibble2 =
  Const "Float.Nibble.Nibble2" (Typerep "Float.Nibble" []);
term_of_Nibble Nibble1 =
  Const "Float.Nibble.Nibble1" (Typerep "Float.Nibble" []);
term_of_Nibble Nibble0 =
  Const "Float.Nibble.Nibble0" (Typerep "Float.Nibble" []);

term_of_Chara :: Chara -> Term;
term_of_Chara (Chara a b) =
  App (App (Const "Float.Chara.Chara"
             (Typerep "fun"
               [Typerep "Float.Nibble" [],
                 Typerep "fun"
                   [Typerep "Float.Nibble" [], Typerep "Float.Chara" []]]))
        (term_of_Nibble a))
    (term_of_Nibble b);

term_of_Reala :: Reala -> Term;
term_of_Reala (Ratreal a) =
  App (Const "Float.Reala.Ratreal"
        (Typerep "fun" [Typerep "Float.Rat" [], Typerep "Float.Reala" []]))
    (term_of_Rat a);

typerep_Chara :: Itself Chara -> Typerepa;
typerep_Chara t = Typerep "Float.Chara" [];

typerep_Reala :: Itself Reala -> Typerepa;
typerep_Reala t = Typerep "Float.Reala" [];

term_of_Floata :: Floata -> Term;
term_of_Floata (Floata a b) =
  App (App (Const "Float.Floata.Floata"
             (Typerep "fun"
               [Typerep "Int.int" [],
                 Typerep "fun"
                   [Typerep "Int.int" [], Typerep "Float.Floata" []]]))
        (term_of_int a))
    (term_of_int b);

term_of_Itself :: forall a. (Typerep a) => Itselfa a -> Term;
term_of_Itself Typea =
  Const "Float.Itself.Type"
    (Typerep "Float.Itself" [(typerep :: Itself a -> Typerepa) Type]);

typerep_Floata :: Itself Floata -> Typerepa;
typerep_Floata t = Typerep "Float.Floata" [];

typerep_Itself :: forall a. (Typerep a) => Itself (Itselfa a) -> Typerepa;
typerep_Itself t =
  Typerep "Float.Itself" [(typerep :: Itself a -> Typerepa) Type];

typerep_Nibble :: Itself Nibble -> Typerepa;
typerep_Nibble t = Typerep "Float.Nibble" [];

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

narrowing_Itself ::
  forall a. (Typerep a) => Integer -> Narrowing_cons (Itselfa a);
narrowing_Itself = cons Typea;

narrowing_Nibble :: Integer -> Narrowing_cons Nibble;
narrowing_Nibble =
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

partial_term_of_int :: Itself Int -> Narrowing_term -> Term;
partial_term_of_int ty (Narrowing_constructor i []) =
  (if mod_integer i (2 :: Integer) == (0 :: Integer)
    then term_of_int (div_inta (uminus_int (int_of_integer i)) (Pos (Bit0 One)))
    else term_of_int
           (div_inta (plus_int (int_of_integer i) (Pos One)) (Pos (Bit0 One))));
partial_term_of_int ty (Narrowing_variable p t) =
  Free "_" (Typerep "Int.int" []);

full_exhaustive_inta ::
  ((Int, () -> Term) -> Maybe (Bool, [Term])) ->
    Natural -> Maybe (Bool, [Term]);
full_exhaustive_inta f d =
  full_exhaustive_int f (int_of_integer (integer_of_natural d))
    (uminus_int (int_of_integer (integer_of_natural d)));

full_exhaustive_Rat ::
  ((Rat, () -> Term) -> Maybe (Bool, [Term])) ->
    Natural -> Maybe (Bool, [Term]);
full_exhaustive_Rat f i =
  (if less_natural zero_natural i
    then full_exhaustive_inta
           (\ (uu, uua) ->
             full_exhaustive_inta
               (\ (uub, uuc) ->
                 f (Fract uu uub,
                     (\ _ ->
                       App (App (Const "Float.Rat.Fract"
                                  (Typerep "fun"
                                    [Typerep "Int.int" [],
                                      Typerep "fun"
[Typerep "Int.int" [], Typerep "Float.Rat" []]]))
                             (uua ()))
                         (uuc ()))))
               (minus_natural i one_natural))
           (minus_natural i one_natural)
    else Nothing);

partial_term_of_Rat :: Itself Rat -> Narrowing_term -> Term;
partial_term_of_Rat ty (Narrowing_constructor (0 :: Integer) [b, a]) =
  App (App (Const "Float.Rat.Fract"
             (Typerep "fun"
               [Typerep "Int.int" [],
                 Typerep "fun" [Typerep "Int.int" [], Typerep "Float.Rat" []]]))
        (partial_term_of_int Type a))
    (partial_term_of_int Type b);
partial_term_of_Rat ty (Narrowing_variable p tt) =
  Free "_" (Typerep "Float.Rat" []);

full_exhaustive_Nibble ::
  ((Nibble, () -> Term) -> Maybe (Bool, [Term])) ->
    Natural -> Maybe (Bool, [Term]);
full_exhaustive_Nibble f i =
  (if less_natural zero_natural i
    then (case f (Nibble0,
                   (\ _ ->
                     Const "Float.Nibble.Nibble0" (Typerep "Float.Nibble" [])))
           of {
           Nothing ->
             (case f (Nibble1,
                       (\ _ ->
                         Const "Float.Nibble.Nibble1"
                           (Typerep "Float.Nibble" [])))
               of {
               Nothing ->
                 (case f (Nibble2,
                           (\ _ ->
                             Const "Float.Nibble.Nibble2"
                               (Typerep "Float.Nibble" [])))
                   of {
                   Nothing ->
                     (case f (Nibble3,
                               (\ _ ->
                                 Const "Float.Nibble.Nibble3"
                                   (Typerep "Float.Nibble" [])))
                       of {
                       Nothing ->
                         (case f (Nibble4,
                                   (\ _ ->
                                     Const "Float.Nibble.Nibble4"
                                       (Typerep "Float.Nibble" [])))
                           of {
                           Nothing ->
                             (case f (Nibble5,
                                       (\ _ ->
 Const "Float.Nibble.Nibble5" (Typerep "Float.Nibble" [])))
                               of {
                               Nothing ->
                                 (case f
 (Nibble6, (\ _ -> Const "Float.Nibble.Nibble6" (Typerep "Float.Nibble" [])))
                                   of {
                                   Nothing ->
                                     (case f
     (Nibble7,
       (\ _ -> Const "Float.Nibble.Nibble7" (Typerep "Float.Nibble" [])))
                                       of {
                                       Nothing ->
 (case f (Nibble8,
           (\ _ -> Const "Float.Nibble.Nibble8" (Typerep "Float.Nibble" [])))
   of {
   Nothing ->
     (case f (Nibble9,
               (\ _ ->
                 Const "Float.Nibble.Nibble9" (Typerep "Float.Nibble" [])))
       of {
       Nothing ->
         (case f (NibbleA,
                   (\ _ ->
                     Const "Float.Nibble.NibbleA" (Typerep "Float.Nibble" [])))
           of {
           Nothing ->
             (case f (NibbleB,
                       (\ _ ->
                         Const "Float.Nibble.NibbleB"
                           (Typerep "Float.Nibble" [])))
               of {
               Nothing ->
                 (case f (NibbleC,
                           (\ _ ->
                             Const "Float.Nibble.NibbleC"
                               (Typerep "Float.Nibble" [])))
                   of {
                   Nothing ->
                     (case f (NibbleD,
                               (\ _ ->
                                 Const "Float.Nibble.NibbleD"
                                   (Typerep "Float.Nibble" [])))
                       of {
                       Nothing ->
                         (case f (NibbleE,
                                   (\ _ ->
                                     Const "Float.Nibble.NibbleE"
                                       (Typerep "Float.Nibble" [])))
                           of {
                           Nothing ->
                             f (NibbleF,
                                 (\ _ ->
                                   Const "Float.Nibble.NibbleF"
                                     (Typerep "Float.Nibble" [])));
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
  ((Chara, () -> Term) -> Maybe (Bool, [Term])) ->
    Natural -> Maybe (Bool, [Term]);
full_exhaustive_Chara f i =
  (if less_natural zero_natural i
    then full_exhaustive_Nibble
           (\ (uu, uua) ->
             full_exhaustive_Nibble
               (\ (uub, uuc) ->
                 f (Chara uu uub,
                     (\ _ ->
                       App (App (Const "Float.Chara.Chara"
                                  (Typerep "fun"
                                    [Typerep "Float.Nibble" [],
                                      Typerep "fun"
[Typerep "Float.Nibble" [], Typerep "Float.Chara" []]]))
                             (uua ()))
                         (uuc ()))))
               (minus_natural i one_natural))
           (minus_natural i one_natural)
    else Nothing);

full_exhaustive_Reala ::
  ((Reala, () -> Term) -> Maybe (Bool, [Term])) ->
    Natural -> Maybe (Bool, [Term]);
full_exhaustive_Reala f i =
  (if less_natural zero_natural i
    then full_exhaustive_Rat
           (\ (uu, uua) ->
             f (Ratreal uu,
                 (\ _ ->
                   App (Const "Float.Reala.Ratreal"
                         (Typerep "fun"
                           [Typerep "Float.Rat" [], Typerep "Float.Reala" []]))
                     (uua ()))))
           (minus_natural i one_natural)
    else Nothing);

partial_term_of_Nibble :: Itself Nibble -> Narrowing_term -> Term;
partial_term_of_Nibble ty (Narrowing_constructor (15 :: Integer) []) =
  Const "Float.Nibble.NibbleF" (Typerep "Float.Nibble" []);
partial_term_of_Nibble ty (Narrowing_constructor (14 :: Integer) []) =
  Const "Float.Nibble.NibbleE" (Typerep "Float.Nibble" []);
partial_term_of_Nibble ty (Narrowing_constructor (13 :: Integer) []) =
  Const "Float.Nibble.NibbleD" (Typerep "Float.Nibble" []);
partial_term_of_Nibble ty (Narrowing_constructor (12 :: Integer) []) =
  Const "Float.Nibble.NibbleC" (Typerep "Float.Nibble" []);
partial_term_of_Nibble ty (Narrowing_constructor (11 :: Integer) []) =
  Const "Float.Nibble.NibbleB" (Typerep "Float.Nibble" []);
partial_term_of_Nibble ty (Narrowing_constructor (10 :: Integer) []) =
  Const "Float.Nibble.NibbleA" (Typerep "Float.Nibble" []);
partial_term_of_Nibble ty (Narrowing_constructor (9 :: Integer) []) =
  Const "Float.Nibble.Nibble9" (Typerep "Float.Nibble" []);
partial_term_of_Nibble ty (Narrowing_constructor (8 :: Integer) []) =
  Const "Float.Nibble.Nibble8" (Typerep "Float.Nibble" []);
partial_term_of_Nibble ty (Narrowing_constructor (7 :: Integer) []) =
  Const "Float.Nibble.Nibble7" (Typerep "Float.Nibble" []);
partial_term_of_Nibble ty (Narrowing_constructor (6 :: Integer) []) =
  Const "Float.Nibble.Nibble6" (Typerep "Float.Nibble" []);
partial_term_of_Nibble ty (Narrowing_constructor (5 :: Integer) []) =
  Const "Float.Nibble.Nibble5" (Typerep "Float.Nibble" []);
partial_term_of_Nibble ty (Narrowing_constructor (4 :: Integer) []) =
  Const "Float.Nibble.Nibble4" (Typerep "Float.Nibble" []);
partial_term_of_Nibble ty (Narrowing_constructor (3 :: Integer) []) =
  Const "Float.Nibble.Nibble3" (Typerep "Float.Nibble" []);
partial_term_of_Nibble ty (Narrowing_constructor (2 :: Integer) []) =
  Const "Float.Nibble.Nibble2" (Typerep "Float.Nibble" []);
partial_term_of_Nibble ty (Narrowing_constructor (1 :: Integer) []) =
  Const "Float.Nibble.Nibble1" (Typerep "Float.Nibble" []);
partial_term_of_Nibble ty (Narrowing_constructor (0 :: Integer) []) =
  Const "Float.Nibble.Nibble0" (Typerep "Float.Nibble" []);
partial_term_of_Nibble ty (Narrowing_variable p tt) =
  Free "_" (Typerep "Float.Nibble" []);

partial_term_of_Chara :: Itself Chara -> Narrowing_term -> Term;
partial_term_of_Chara ty (Narrowing_constructor (0 :: Integer) [b, a]) =
  App (App (Const "Float.Chara.Chara"
             (Typerep "fun"
               [Typerep "Float.Nibble" [],
                 Typerep "fun"
                   [Typerep "Float.Nibble" [], Typerep "Float.Chara" []]]))
        (partial_term_of_Nibble Type a))
    (partial_term_of_Nibble Type b);
partial_term_of_Chara ty (Narrowing_variable p tt) =
  Free "_" (Typerep "Float.Chara" []);

partial_term_of_Reala :: Itself Reala -> Narrowing_term -> Term;
partial_term_of_Reala ty (Narrowing_constructor (0 :: Integer) [a]) =
  App (Const "Float.Reala.Ratreal"
        (Typerep "fun" [Typerep "Float.Rat" [], Typerep "Float.Reala" []]))
    (partial_term_of_Rat Type a);
partial_term_of_Reala ty (Narrowing_variable p tt) =
  Free "_" (Typerep "Float.Reala" []);

typerep_Rat_IITN_Rat :: Itself Rat_IITN_Rat -> Typerepa;
typerep_Rat_IITN_Rat t = Typerep "Float.Rat.Rat_IITN_Rat" [];

full_exhaustive_Floata ::
  ((Floata, () -> Term) -> Maybe (Bool, [Term])) ->
    Natural -> Maybe (Bool, [Term]);
full_exhaustive_Floata f i =
  (if less_natural zero_natural i
    then full_exhaustive_inta
           (\ (uu, uua) ->
             full_exhaustive_inta
               (\ (uub, uuc) ->
                 f (Floata uu uub,
                     (\ _ ->
                       App (App (Const "Float.Floata.Floata"
                                  (Typerep "fun"
                                    [Typerep "Int.int" [],
                                      Typerep "fun"
[Typerep "Int.int" [], Typerep "Float.Floata" []]]))
                             (uua ()))
                         (uuc ()))))
               (minus_natural i one_natural))
           (minus_natural i one_natural)
    else Nothing);

full_exhaustive_Itself ::
  forall a.
    (Typerep a) => ((Itselfa a, () -> Term) -> Maybe (Bool, [Term])) ->
                     Natural -> Maybe (Bool, [Term]);
full_exhaustive_Itself f i =
  (if less_natural zero_natural i
    then f (Typea,
             (\ _ ->
               Const "Float.Itself.Type"
                 (Typerep "Float.Itself"
                   [(typerep :: Itself a -> Typerepa) Type])))
    else Nothing);

partial_term_of_Floata :: Itself Floata -> Narrowing_term -> Term;
partial_term_of_Floata ty (Narrowing_constructor (0 :: Integer) [b, a]) =
  App (App (Const "Float.Floata.Floata"
             (Typerep "fun"
               [Typerep "Int.int" [],
                 Typerep "fun"
                   [Typerep "Int.int" [], Typerep "Float.Floata" []]]))
        (partial_term_of_int Type a))
    (partial_term_of_int Type b);
partial_term_of_Floata ty (Narrowing_variable p tt) =
  Free "_" (Typerep "Float.Floata" []);

partial_term_of_Itself ::
  forall a. (Typerep a) => Itself (Itselfa a) -> Narrowing_term -> Term;
partial_term_of_Itself ty (Narrowing_constructor (0 :: Integer) []) =
  Const "Float.Itself.Type"
    (Typerep "Float.Itself" [(typerep :: Itself a -> Typerepa) Type]);
partial_term_of_Itself ty (Narrowing_variable p tt) =
  Free "_" (Typerep "Float.Itself" [(typerep :: Itself a -> Typerepa) Type]);

typerep_Chara_IITN_Chara :: Itself Chara_IITN_Chara -> Typerepa;
typerep_Chara_IITN_Chara t = Typerep "Float.Chara.Chara_IITN_Chara" [];

typerep_Reala_IITN_Reala :: Itself Reala_IITN_Reala -> Typerepa;
typerep_Reala_IITN_Reala t = Typerep "Float.Reala.Reala_IITN_Reala" [];

typerep_Itself_pre_Itself ::
  forall a b.
    (Typerep a, Typerep b) => Itself (Itself_pre_Itself a b) -> Typerepa;
typerep_Itself_pre_Itself t =
  Typerep "Float.Itself.Itself_pre_Itself"
    [(typerep :: Itself a -> Typerepa) Type,
      (typerep :: Itself b -> Typerepa) Type];

typerep_Nibble_pre_Nibble :: Itself Nibble_pre_Nibble -> Typerepa;
typerep_Nibble_pre_Nibble t = Typerep "Float.Nibble.Nibble_pre_Nibble" [];

typerep_Floata_IITN_Floata :: Itself Floata_IITN_Floata -> Typerepa;
typerep_Floata_IITN_Floata t = Typerep "Float.Floata.Floata_IITN_Floata" [];

typerep_Itself_IITN_Itself ::
  forall a. (Typerep a) => Itself (Itself_IITN_Itself a) -> Typerepa;
typerep_Itself_IITN_Itself t =
  Typerep "Float.Itself.Itself_IITN_Itself"
    [(typerep :: Itself a -> Typerepa) Type];

typerep_Nibble_IITN_Nibble :: Itself Nibble_IITN_Nibble -> Typerepa;
typerep_Nibble_IITN_Nibble t = Typerep "Float.Nibble.Nibble_IITN_Nibble" [];

}
