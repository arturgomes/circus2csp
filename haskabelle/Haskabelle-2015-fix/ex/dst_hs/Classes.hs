{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Classes(Ord(..), Natural(..), integer_of_natural, plus_natural, Plus(..),
           zero_natural, Zero(..), Monoid_add, Times(..), Div(..), One(..),
           Numeral, Monoid(..), Group(..), Minus(..), Linord(..), Eqa(..),
           Linorder(..), Semiring_numeral_div, Order(..), Itself(..), Num(..),
           Int(..), Nat(..), Nata(..), Nibble(..), Char(..), Typerep(..),
           Term(..), Linord_IITN_Linord, Narrowing_type(..), Narrowing_term(..),
           Narrowing_cons(..), dup, uminus_int, plus_num, bitM, sub, plus_int,
           minus_int, foldr, less_eq_natural, less_natural, one_natural,
           sgn_integer, abs_integer, apsnd, divmod_integer, div_integer,
           div_natural, log, suba, times_natural, mod_integer, mod_natural, max,
           natural_of_integer, minus_natural, minus_shift, next, pick, summ,
           scomp, equal_natural, iterate, range, less_nat, less_eq_nat,
           plus_nat, equal_num, equal_int, eq_int, less_num, less_eq_num,
           less_int, pow_int, pow_nat, listsum, select_weight, sum, rec_Linord,
           collapse, random_aux_Linord, numeral, cons, size_Linord, less_eq_int,
           times_num, less_Nat, less_inta, plus_Nat, plus_inta, less_list,
           less_prod, inverse_int, less_eq_Nat, less_eq_inta, nothing_Nat,
           nothing_int, linord_Nat, linord_int, less_eq_list, less_eq_prod,
           size_Linorda, linord_list, linord_prod, equal_Linord, random_Linord,
           one_integer, divmod_step, divmod, term_of_Linord, typerep_Linord,
           narrowing_Linord, full_exhaustive_Linord, partial_term_of_Linord,
           typerep_Linord_IITN_Linord)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;

class Ord a where {
  less_eqa :: a -> a -> Bool;
  lessa :: a -> a -> Bool;
};

instance Ord Integer where {
  less_eqa = (\ a b -> a <= b);
  lessa = (\ a b -> a < b);
};

newtype Natural = Nat Integer;

integer_of_natural :: Natural -> Integer;
integer_of_natural (Nat x) = x;

plus_natural :: Natural -> Natural -> Natural;
plus_natural m n = Nat (integer_of_natural m + integer_of_natural n);

class Plus a where {
  plus :: a -> a -> a;
};

instance Plus Natural where {
  plus = plus_natural;
};

zero_natural :: Natural;
zero_natural = Nat (0 :: Integer);

class Zero a where {
  zero :: a;
};

instance Zero Natural where {
  zero = zero_natural;
};

class (Plus a) => Semigroup_add a where {
};

class (Semigroup_add a, Zero a) => Monoid_add a where {
};

instance Semigroup_add Natural where {
};

instance Monoid_add Natural where {
};

class Times a where {
  times :: a -> a -> a;
};

class (Times a) => Dvd a where {
};

class (Dvd a) => Div a where {
  div :: a -> a -> a;
  mod :: a -> a -> a;
};

class One a where {
  one :: a;
};

class (One a, Semigroup_add a) => Numeral a where {
};

class (One a, Times a) => Power a where {
};

class Monoid a where {
  nothing :: a;
  plusa :: a -> a -> a;
};

class (Monoid a) => Group a where {
  inverse :: a -> a;
};

class (Semigroup_add a) => Ab_semigroup_add a where {
};

class (Ab_semigroup_add a, Monoid_add a) => Comm_monoid_add a where {
};

class (Times a, Zero a) => Mult_zero a where {
};

class (Times a) => Semigroup_mult a where {
};

class (Ab_semigroup_add a, Semigroup_mult a) => Semiring a where {
};

class (Comm_monoid_add a, Mult_zero a, Semiring a) => Semiring_0 a where {
};

class (Semiring_0 a) => Semiring_no_zero_divisors a where {
};

class (Semigroup_add a) => Cancel_semigroup_add a where {
};

class Minus a where {
  minus :: a -> a -> a;
};

class (Ab_semigroup_add a, Cancel_semigroup_add a,
        Minus a) => Cancel_ab_semigroup_add a where {
};

class (Cancel_ab_semigroup_add a,
        Comm_monoid_add a) => Cancel_comm_monoid_add a where {
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

class (Comm_semiring_1_diff_distrib a,
        Semiring_no_zero_divisors a) => Semidom a where {
};

class (Ord a) => Preorder a where {
};

class (Preorder a) => Ordera a where {
};

data Linord = Less | Equal | Greater;

class Eqa a where {
  eq :: a -> a -> Bool;
  not_eq :: a -> a -> Bool;
};

class (Eqa a) => Linorder a where {
  linord :: a -> a -> Linord;
};

class (Ordera a) => Linordera a where {
};

class (Semiring_1 a) => Semiring_char_0 a where {
};

class (Div a, Semidom a) => Semiring_div a where {
};

class (Comm_semiring_1_diff_distrib a) => Semiring_parity a where {
};

class (Ab_semigroup_add a, Ordera a) => Ordered_ab_semigroup_add a where {
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

class (Ordered_ab_semigroup_add a,
        Linordera a) => Linordered_ab_semigroup_add a where {
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

class (Semiring_char_0 a, Linordered_comm_semiring_strict a,
        Semidom a) => Linordered_semidom a where {
};

class (Semiring_div a, Semiring_parity a) => Semiring_div_parity a where {
};

class (Semiring_div_parity a,
        Linordered_semidom a) => Semiring_numeral_div a where {
};

class Order a where {
  less_eq :: a -> a -> Bool;
  less :: a -> a -> Bool;
};

data Itself a = Type;

data Num = One | Bit0 Num | Bit1 Num;

data Int = Zero_int | Pos Num | Neg Num;

data Nat = Zero_nat | Suc Nat;

data Nata = Suca Nata | Zero;

data Nibble = Nibble0 | Nibble1 | Nibble2 | Nibble3 | Nibble4 | Nibble5
  | Nibble6 | Nibble7 | Nibble8 | Nibble9 | NibbleA | NibbleB | NibbleC
  | NibbleD | NibbleE | NibbleF;

data Char = Char Nibble Nibble;

data Typerep = Typerep String [Typerep];

data Term = Const String Typerep | App Term Term | Abs String Typerep Term
  | Free String Typerep;

data Linord_IITN_Linord;

newtype Narrowing_type = Narrowing_sum_of_products [[Narrowing_type]];

data Narrowing_term = Narrowing_variable [Integer] Narrowing_type
  | Narrowing_constructor Integer [Narrowing_term];

data Narrowing_cons a = Narrowing_cons Narrowing_type [[Narrowing_term] -> a];

dup :: Int -> Int;
dup (Neg n) = Neg (Bit0 n);
dup (Pos n) = Pos (Bit0 n);
dup Zero_int = Zero_int;

uminus_int :: Int -> Int;
uminus_int (Neg m) = Pos m;
uminus_int (Pos m) = Neg m;
uminus_int Zero_int = Zero_int;

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

bitM :: Num -> Num;
bitM One = One;
bitM (Bit0 n) = Bit1 (bitM n);
bitM (Bit1 n) = Bit1 (Bit0 n);

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

minus_int :: Int -> Int -> Int;
minus_int (Neg m) (Neg n) = sub n m;
minus_int (Neg m) (Pos n) = Neg (plus_num m n);
minus_int (Pos m) (Neg n) = Pos (plus_num m n);
minus_int (Pos m) (Pos n) = sub m n;
minus_int Zero_int l = uminus_int l;
minus_int k Zero_int = k;

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

apsnd :: forall a b c. (a -> b) -> (c, a) -> (c, b);
apsnd f (x, y) = (x, f y);

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

suba :: forall a. (Group a) => a -> a -> a;
suba a b = plusa a (inverse b);

times_natural :: Natural -> Natural -> Natural;
times_natural m n = Nat (integer_of_natural m * integer_of_natural n);

mod_integer :: Integer -> Integer -> Integer;
mod_integer k l = snd (divmod_integer k l);

mod_natural :: Natural -> Natural -> Natural;
mod_natural m n =
  Nat (mod_integer (integer_of_natural m) (integer_of_natural n));

max :: forall a. (Ord a) => a -> a -> a;
max a b = (if less_eqa a b then b else a);

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

summ :: forall a. (Monoid a) => [a] -> a;
summ [] = nothing;
summ (x : xs) = plusa x (summ xs);

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

less_nat :: Nata -> Nata -> Bool;
less_nat m (Suca n) = less_eq_nat m n;
less_nat n Zero = False;

less_eq_nat :: Nata -> Nata -> Bool;
less_eq_nat (Suca m) n = less_nat m n;
less_eq_nat Zero n = True;

plus_nat :: Nata -> Nata -> Nata;
plus_nat (Suca m) n = plus_nat m (Suca n);
plus_nat Zero n = n;

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

eq_int :: Int -> Int -> Bool;
eq_int x y = equal_int x y;

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

pow_int :: forall a. (Group a) => Int -> a -> a;
pow_int k x =
  (if eq_int k Zero_int then nothing
    else (if less_int k Zero_int then pow_int (uminus_int k) (inverse x)
           else plusa x (pow_int (minus_int k (Pos One)) x)));

pow_nat :: forall a. (Monoid a) => Nata -> a -> a;
pow_nat Zero uu = nothing;
pow_nat (Suca n) x = plusa x (pow_nat n x);

listsum :: forall a. (Monoid_add a) => [a] -> a;
listsum xs = foldr plus xs zero;

select_weight ::
  forall a. [(Natural, a)] -> (Natural, Natural) -> (a, (Natural, Natural));
select_weight xs =
  scomp (range (listsum (map fst xs))) (\ k -> (\ a -> (pick xs k, a)));

sum ::
  forall a.
    (Integer -> Narrowing_cons a) ->
      (Integer -> Narrowing_cons a) -> Integer -> Narrowing_cons a;
sum a b d =
  let {
    (Narrowing_cons (Narrowing_sum_of_products ssa) ca) = a d;
    (Narrowing_cons (Narrowing_sum_of_products ssb) cb) = b d;
  } in Narrowing_cons (Narrowing_sum_of_products (ssa ++ ssb)) (ca ++ cb);

rec_Linord :: forall a. a -> a -> a -> Linord -> a;
rec_Linord f1 f2 f3 Less = f1;
rec_Linord f1 f2 f3 Equal = f2;
rec_Linord f1 f2 f3 Greater = f3;

collapse :: forall a b. (a -> (a -> (b, a), a)) -> a -> (b, a);
collapse f = scomp f id;

random_aux_Linord ::
  Natural ->
    Natural -> (Natural, Natural) -> ((Linord, () -> Term), (Natural, Natural));
random_aux_Linord i j s =
  collapse
    (select_weight
      [(one_natural,
         (\ a ->
           ((Less,
              (\ _ ->
                Const "Classes.Linord.Less" (Typerep "Classes.Linord" []))),
             a))),
        (one_natural,
          (\ a ->
            ((Equal,
               (\ _ ->
                 Const "Classes.Linord.Equal" (Typerep "Classes.Linord" []))),
              a))),
        (one_natural,
          (\ a ->
            ((Greater,
               (\ _ ->
                 Const "Classes.Linord.Greater" (Typerep "Classes.Linord" []))),
              a)))])
    s;

numeral :: forall a. (Numeral a) => Num -> a;
numeral (Bit1 n) = let {
                     m = numeral n;
                   } in plus (plus m m) one;
numeral (Bit0 n) = let {
                     m = numeral n;
                   } in plus m m;
numeral One = one;

cons :: forall a. a -> Integer -> Narrowing_cons a;
cons a d = Narrowing_cons (Narrowing_sum_of_products [[]]) [(\ _ -> a)];

size_Linord :: Linord -> Nat;
size_Linord Less = Zero_nat;
size_Linord Equal = Zero_nat;
size_Linord Greater = Zero_nat;

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

times_num :: Num -> Num -> Num;
times_num (Bit1 m) (Bit1 n) =
  Bit1 (plus_num (plus_num m n) (Bit0 (times_num m n)));
times_num (Bit1 m) (Bit0 n) = Bit0 (times_num (Bit1 m) n);
times_num (Bit0 m) (Bit1 n) = Bit0 (times_num m (Bit1 n));
times_num (Bit0 m) (Bit0 n) = Bit0 (Bit0 (times_num m n));
times_num One n = n;
times_num m One = m;

less_Nat :: Nata -> Nata -> Bool;
less_Nat = less_nat;

less_inta :: Int -> Int -> Bool;
less_inta = less_int;

plus_Nat :: Nata -> Nata -> Nata;
plus_Nat = plus_nat;

plus_inta :: Int -> Int -> Int;
plus_inta = plus_int;

less_list :: forall a. (Order a) => [a] -> [a] -> Bool;
less_list (x : xs) (y : ys) = less x y || not (less y x) && less_list xs ys;
less_list xs [] = False;
less_list [] (x : xs) = True;

less_prod :: forall a b. (Order a, Order b) => (a, b) -> (a, b) -> Bool;
less_prod (x, y) (w, z) = less x w || not (less w x) && less y z;

inverse_int :: Int -> Int;
inverse_int = uminus_int;

less_eq_Nat :: Nata -> Nata -> Bool;
less_eq_Nat = less_eq_nat;

less_eq_inta :: Int -> Int -> Bool;
less_eq_inta = less_eq_int;

nothing_Nat :: Nata;
nothing_Nat = Zero;

nothing_int :: Int;
nothing_int = Zero_int;

linord_Nat :: Nata -> Nata -> Linord;
linord_Nat Zero (Suca uu) = Less;
linord_Nat Zero Zero = Equal;
linord_Nat (Suca uv) Zero = Greater;
linord_Nat (Suca m) (Suca n) = linord_Nat m n;

linord_int :: Int -> Int -> Linord;
linord_int k l =
  (if less_int k l then Less else (if less_int l k then Greater else Equal));

less_eq_list :: forall a. (Order a) => [a] -> [a] -> Bool;
less_eq_list (x : xs) (y : ys) =
  less x y || not (less y x) && less_eq_list xs ys;
less_eq_list [] xs = True;
less_eq_list (x : xs) [] = False;

less_eq_prod :: forall a b. (Order a, Order b) => (a, b) -> (a, b) -> Bool;
less_eq_prod (x, y) (w, z) = less x w || not (less w x) && less_eq y z;

size_Linorda :: Linord -> Nat;
size_Linorda Less = Zero_nat;
size_Linorda Equal = Zero_nat;
size_Linorda Greater = Zero_nat;

linord_list :: forall a. (Linorder a) => [a] -> [a] -> Linord;
linord_list [] [] = Equal;
linord_list (v : va) [] = Greater;
linord_list [] (v : va) = Less;
linord_list (x : xs) (y : ys) =
  (case linord x y of {
    Less -> Less;
    Equal -> linord_list xs ys;
    Greater -> Greater;
  });

linord_prod ::
  forall a b. (Linorder a, Linorder b) => (a, b) -> (a, b) -> Linord;
linord_prod (x, y) (w, z) =
  (case linord x w of {
    Less -> Less;
    Equal -> linord y z;
    Greater -> Greater;
  });

equal_Linord :: Linord -> Linord -> Bool;
equal_Linord Equal Greater = False;
equal_Linord Greater Equal = False;
equal_Linord Less Greater = False;
equal_Linord Greater Less = False;
equal_Linord Less Equal = False;
equal_Linord Equal Less = False;
equal_Linord Greater Greater = True;
equal_Linord Equal Equal = True;
equal_Linord Less Less = True;

random_Linord ::
  Natural -> (Natural, Natural) -> ((Linord, () -> Term), (Natural, Natural));
random_Linord i = random_aux_Linord i i;

one_integer :: Integer;
one_integer = (1 :: Integer);

divmod_step :: forall a. (Semiring_numeral_div a) => Num -> (a, a) -> (a, a);
divmod_step l (q, r) =
  (if less_eqa (numeral l) r
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

term_of_Linord :: Linord -> Term;
term_of_Linord Greater =
  Const "Classes.Linord.Greater" (Typerep "Classes.Linord" []);
term_of_Linord Equal =
  Const "Classes.Linord.Equal" (Typerep "Classes.Linord" []);
term_of_Linord Less = Const "Classes.Linord.Less" (Typerep "Classes.Linord" []);

typerep_Linord :: Itself Linord -> Typerep;
typerep_Linord t = Typerep "Classes.Linord" [];

narrowing_Linord :: Integer -> Narrowing_cons Linord;
narrowing_Linord = sum (cons Less) (sum (cons Equal) (cons Greater));

full_exhaustive_Linord ::
  ((Linord, () -> Term) -> Maybe (Bool, [Term])) ->
    Natural -> Maybe (Bool, [Term]);
full_exhaustive_Linord f i =
  (if less_natural zero_natural i
    then (case f (Less,
                   (\ _ ->
                     Const "Classes.Linord.Less" (Typerep "Classes.Linord" [])))
           of {
           Nothing ->
             (case f (Equal,
                       (\ _ ->
                         Const "Classes.Linord.Equal"
                           (Typerep "Classes.Linord" [])))
               of {
               Nothing ->
                 f (Greater,
                     (\ _ ->
                       Const "Classes.Linord.Greater"
                         (Typerep "Classes.Linord" [])));
               Just a -> Just a;
             });
           Just a -> Just a;
         })
    else Nothing);

partial_term_of_Linord :: Itself Linord -> Narrowing_term -> Term;
partial_term_of_Linord ty (Narrowing_constructor (2 :: Integer) []) =
  Const "Classes.Linord.Greater" (Typerep "Classes.Linord" []);
partial_term_of_Linord ty (Narrowing_constructor (1 :: Integer) []) =
  Const "Classes.Linord.Equal" (Typerep "Classes.Linord" []);
partial_term_of_Linord ty (Narrowing_constructor (0 :: Integer) []) =
  Const "Classes.Linord.Less" (Typerep "Classes.Linord" []);
partial_term_of_Linord ty (Narrowing_variable p tt) =
  Free "_" (Typerep "Classes.Linord" []);

typerep_Linord_IITN_Linord :: Itself Linord_IITN_Linord -> Typerep;
typerep_Linord_IITN_Linord t = Typerep "Classes.Linord.Linord_IITN_Linord" [];

}
