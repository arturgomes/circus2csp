{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Enumerations(Ord(..), Natural(..), integer_of_natural, plus_natural, Plus(..),
                zero_natural, Zero(..), Monoid_add, Times(..), Div(..), One(..),
                Numeral, Minus(..), Enuma(..), Typerepa(..), Term(..),
                Itself(..), Typerep(..), Term_of(..), Random(..),
                Semiring_numeral_div, Narrowing_type(..), Narrowing_term(..),
                Partial_term_of(..), Full_exhaustive(..), Eqa(..),
                Narrowing_cons(..), Narrowing(..), Nat(..), Num(..), Set(..),
                Nibble(..), Char(..), Nata(..), Sum(..), Nat_IITN_Nat,
                Sum_IITN_Sum, bitM, ball, foldr, less_eq_natural, less_natural,
                one_natural, sgn_integer, abs_integer, apsnd, divmod_integer,
                div_integer, div_natural, log, removeAll, member, inserta,
                insert, times_natural, mod_integer, mod_natural, max,
                natural_of_integer, minus_natural, minus_shift, next, pick,
                scomp, equal_natural, iterate, range, len, the, mapa, zipa,
                append, enuma, producta, enumb, list_all, eq_fun, map_of,
                concata, n_lists, listsum, select_weight, enum_fun, plus_nat,
                bot_set, set2_Sum, set1_Sum, pred_Sum, sublists, valapp,
                enum_bool, enum_unit, list_case, rec_Nat, map_Sum, rec_Sum,
                rel_Sum, enum_option, sum, plus_nata, size_Nat, size_Sum,
                numeral, less_num, less_eq_num, cons, plus_num, collapse,
                random_aux_Nat, random_aux_Sum, equal_num, times_num, non_empty,
                size_Nata, size_Suma, equal_Nat, equal_Sum, random_Nat,
                random_Sum, one_integer, divmod_step, divmod, term_of_Nat,
                term_of_Sum, typerep_Nat, typerep_Sum, full_exhaustive_Nat,
                full_exhaustive_Sum, partial_term_of_Nat, partial_term_of_Sum,
                typerep_Nat_IITN_Nat, typerep_Sum_IITN_Sum)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;

class Ord a where {
  less_eq :: a -> a -> Bool;
  less :: a -> a -> Bool;
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

class (Preorder a) => Order a where {
};

class Finite a where {
};

class (Finite a) => Enuma a where {
  enum :: [a];
};

class (Order a) => Linorder a where {
};

class (Semiring_1 a) => Semiring_char_0 a where {
};

class (Div a, Semidom a) => Semiring_div a where {
};

class (Comm_semiring_1_diff_distrib a) => Semiring_parity a where {
};

class (Ab_semigroup_add a, Order a) => Ordered_ab_semigroup_add a where {
};

class (Comm_monoid_add a, Ordered_ab_semigroup_add a,
        Semiring a) => Ordered_semiring a where {
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

class (Semiring_char_0 a, Linordered_comm_semiring_strict a,
        Semidom a) => Linordered_semidom a where {
};

class (Semiring_div a, Semiring_parity a) => Semiring_div_parity a where {
};

class (Semiring_div_parity a,
        Linordered_semidom a) => Semiring_numeral_div a where {
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

class Eqa a where {
  eq :: a -> a -> Bool;
  not_eq :: a -> a -> Bool;
};

data Narrowing_cons a = Narrowing_cons Narrowing_type [[Narrowing_term] -> a];

class Narrowing a where {
  narrowing :: Integer -> Narrowing_cons a;
};

data Nat = Zero_nat | Suc Nat;

data Num = One | Bit0 Num | Bit1 Num;

data Set a = Set [a] | Coset [a];

data Nibble = Nibble0 | Nibble1 | Nibble2 | Nibble3 | Nibble4 | Nibble5
  | Nibble6 | Nibble7 | Nibble8 | Nibble9 | NibbleA | NibbleB | NibbleC
  | NibbleD | NibbleE | NibbleF;

data Char = Char Nibble Nibble;

data Nata = Zero | Suca Nata;

data Sum a b = Inl a | Inr b;

data Nat_IITN_Nat;

data Sum_IITN_Sum a b;

bitM :: Num -> Num;
bitM One = One;
bitM (Bit0 n) = Bit1 (bitM n);
bitM (Bit1 n) = Bit1 (Bit0 n);

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

len :: forall a. [a] -> Nata;
len [] = Zero;
len (uu : xs) = Suca (len xs);

the :: forall a. Maybe a -> a;
the (Just x) = x;

mapa :: forall a b. (a -> b) -> [a] -> [b];
mapa f [] = [];
mapa f (x : xs) = f x : mapa f xs;

zipa :: forall a b. [a] -> [b] -> [(a, b)];
zipa xs [] = [];
zipa xs (y : ys) = (case xs of {
                     [] -> [];
                     z : zs -> (z, y) : zipa zs ys;
                   });

append :: forall a. [a] -> [a] -> [a];
append [] ys = ys;
append (x : xs) ys = x : append xs ys;

enuma :: forall a b. (Enuma a, Enuma b) => [Sum a b];
enuma = append (mapa Inl enum) (mapa Inr enum);

producta :: forall a b. [a] -> [b] -> [(a, b)];
producta [] uu = [];
producta (x : xs) ys = append (mapa (\ a -> (x, a)) ys) (producta xs ys);

enumb :: forall a b. (Enuma a, Enuma b) => [(a, b)];
enumb = producta enum enum;

list_all :: forall a. (a -> Bool) -> [a] -> Bool;
list_all p [] = True;
list_all p (x : xs) = p x && list_all p xs;

eq_fun :: forall a b. (Enuma a, Eqa b) => (a -> b) -> (a -> b) -> Bool;
eq_fun f g = list_all (\ x -> eq (f x) (g x)) enum;

map_of :: forall a b. (Eqa a) => [(a, b)] -> a -> Maybe b;
map_of ((l, v) : ps) k = (if eq l k then Just v else map_of ps k);
map_of [] k = Nothing;

concata :: forall a. [[a]] -> [a];
concata [] = [];
concata (x : xs) = append x (concata xs);

n_lists :: forall a. Nata -> [a] -> [[a]];
n_lists Zero xs = [[]];
n_lists (Suca n) xs =
  concata (mapa (\ ys -> mapa (\ y -> y : ys) xs) (n_lists n xs));

listsum :: forall a. (Monoid_add a) => [a] -> a;
listsum xs = foldr plus xs zero;

select_weight ::
  forall a. [(Natural, a)] -> (Natural, Natural) -> (a, (Natural, Natural));
select_weight xs =
  scomp (range (listsum (map fst xs))) (\ k -> (\ a -> (pick xs k, a)));

enum_fun :: forall a b. (Enuma a, Eqa a, Enuma b) => [a -> b];
enum_fun =
  let {
    enum_a = enum;
  } in mapa (\ ys -> the . map_of (zipa enum_a ys)) (n_lists (len enum_a) enum);

plus_nat :: Nata -> Nata -> Nata;
plus_nat (Suca m) n = plus_nat m (Suca n);
plus_nat Zero n = n;

bot_set :: forall a. Set a;
bot_set = Set [];

set2_Sum :: forall a b. (Eq b) => Sum a b -> Set b;
set2_Sum (Inl x1) = bot_set;
set2_Sum (Inr x2) = insert x2 bot_set;

set1_Sum :: forall a b. (Eq a) => Sum a b -> Set a;
set1_Sum (Inl x1) = insert x1 bot_set;
set1_Sum (Inr x2) = bot_set;

pred_Sum ::
  forall a b. (Eq a, Eq b) => (a -> Bool) -> (b -> Bool) -> Sum a b -> Bool;
pred_Sum p1 p2 = (\ x -> ball (set1_Sum x) p1 && ball (set2_Sum x) p2);

sublists :: forall a. [a] -> [[a]];
sublists [] = [[]];
sublists (x : xs) =
  let {
    xss = sublists xs;
  } in append (mapa (\ a -> x : a) xss) xss;

valapp ::
  forall a b. (a -> b, () -> Term) -> (a, () -> Term) -> (b, () -> Term);
valapp (f, tf) (x, tx) = (f x, (\ _ -> App (tf ()) (tx ())));

enum_bool :: [Bool];
enum_bool = [False, True];

enum_unit :: [()];
enum_unit = [()];

list_case :: forall a b. a -> (b -> [b] -> a) -> [b] -> a;
list_case f1 f2 (a : list) = f2 a list;
list_case f1 f2 [] = f1;

rec_Nat :: forall a. a -> (Nata -> a -> a) -> Nata -> a;
rec_Nat f1 f2 Zero = f1;
rec_Nat f1 f2 (Suca x2) = f2 x2 (rec_Nat f1 f2 x2);

map_Sum :: forall a b c d. (a -> b) -> (c -> d) -> Sum a c -> Sum b d;
map_Sum f1 f2 (Inl x1) = Inl (f1 x1);
map_Sum f1 f2 (Inr x2) = Inr (f2 x2);

rec_Sum :: forall a b c. (a -> b) -> (c -> b) -> Sum a c -> b;
rec_Sum f1 f2 (Inl x1) = f1 x1;
rec_Sum f1 f2 (Inr x2) = f2 x2;

rel_Sum ::
  forall a b c d.
    (a -> b -> Bool) -> (c -> d -> Bool) -> Sum a c -> Sum b d -> Bool;
rel_Sum r1 r2 (Inl x1) (Inr y2) = False;
rel_Sum r1 r2 (Inr y2) (Inl x1) = False;
rel_Sum r1 r2 (Inl x1) (Inl y1) = r1 x1 y1;
rel_Sum r1 r2 (Inr x2) (Inr y2) = r2 x2 y2;

enum_option :: forall a. (Enuma a) => [Maybe a];
enum_option = Nothing : mapa Just enum;

sum ::
  forall a.
    (Integer -> Narrowing_cons a) ->
      (Integer -> Narrowing_cons a) -> Integer -> Narrowing_cons a;
sum a b d =
  let {
    (Narrowing_cons (Narrowing_sum_of_products ssa) ca) = a d;
    (Narrowing_cons (Narrowing_sum_of_products ssb) cb) = b d;
  } in Narrowing_cons (Narrowing_sum_of_products (ssa ++ ssb)) (ca ++ cb);

plus_nata :: Nat -> Nat -> Nat;
plus_nata (Suc m) n = plus_nata m (Suc n);
plus_nata Zero_nat n = n;

size_Nat :: Nata -> Nat;
size_Nat Zero = Zero_nat;
size_Nat (Suca x2) = plus_nata (size_Nat x2) (Suc Zero_nat);

size_Sum :: forall a b. (a -> Nat) -> (b -> Nat) -> Sum a b -> Nat;
size_Sum xa x (Inl x1) = plus_nata (xa x1) (Suc Zero_nat);
size_Sum xa x (Inr x2) = plus_nata (x x2) (Suc Zero_nat);

numeral :: forall a. (Numeral a) => Num -> a;
numeral (Bit1 n) = let {
                     m = numeral n;
                   } in plus (plus m m) one;
numeral (Bit0 n) = let {
                     m = numeral n;
                   } in plus m m;
numeral One = one;

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

cons :: forall a. a -> Integer -> Narrowing_cons a;
cons a d = Narrowing_cons (Narrowing_sum_of_products [[]]) [(\ _ -> a)];

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

collapse :: forall a b. (a -> (a -> (b, a), a)) -> a -> (b, a);
collapse f = scomp f id;

random_aux_Nat ::
  Natural ->
    Natural -> (Natural, Natural) -> ((Nata, () -> Term), (Natural, Natural));
random_aux_Nat i j s =
  collapse
    (select_weight
      [(i, scomp (random_aux_Nat (minus_natural i one_natural) j)
             (\ x ->
               (\ a ->
                 (valapp
                    (Suca,
                      (\ _ ->
                        Const "Enumerations.Nat.Suc"
                          (Typerep "fun"
                            [Typerep "Enumerations.Nat" [],
                              Typerep "Enumerations.Nat" []])))
                    x,
                   a)))),
        (one_natural,
          (\ a ->
            ((Zero,
               (\ _ ->
                 Const "Enumerations.Nat.Zero"
                   (Typerep "Enumerations.Nat" []))),
              a)))])
    s;

random_aux_Sum ::
  forall a b.
    (Random a,
      Random b) => Natural ->
                     Natural ->
                       (Natural, Natural) ->
                         ((Sum a b, () -> Term), (Natural, Natural));
random_aux_Sum i j s =
  collapse
    (select_weight
      [(one_natural,
         scomp (random j)
           (\ x ->
             (\ a ->
               (valapp
                  (Inl, (\ _ ->
                          Const "Enumerations.Sum.Inl"
                            (Typerep "fun"
                              [(typerep :: Itself a -> Typerepa) Type,
                                Typerep "Enumerations.Sum"
                                  [(typerep :: Itself a -> Typerepa) Type,
                                    (typerep :: Itself b -> Typerepa) Type]])))
                  x,
                 a)))),
        (one_natural,
          scomp (random j)
            (\ x ->
              (\ a ->
                (valapp
                   (Inr, (\ _ ->
                           Const "Enumerations.Sum.Inr"
                             (Typerep "fun"
                               [(typerep :: Itself b -> Typerepa) Type,
                                 Typerep "Enumerations.Sum"
                                   [(typerep :: Itself a -> Typerepa) Type,
                                     (typerep :: Itself b -> Typerepa) Type]])))
                   x,
                  a))))])
    s;

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

times_num :: Num -> Num -> Num;
times_num (Bit1 m) (Bit1 n) =
  Bit1 (plus_num (plus_num m n) (Bit0 (times_num m n)));
times_num (Bit1 m) (Bit0 n) = Bit0 (times_num (Bit1 m) n);
times_num (Bit0 m) (Bit1 n) = Bit0 (times_num m (Bit1 n));
times_num (Bit0 m) (Bit0 n) = Bit0 (Bit0 (times_num m n));
times_num One n = n;
times_num m One = m;

non_empty :: Narrowing_type -> Bool;
non_empty (Narrowing_sum_of_products ps) = not (null ps);

size_Nata :: Nata -> Nat;
size_Nata Zero = Zero_nat;
size_Nata (Suca x2) = plus_nata (size_Nata x2) (Suc Zero_nat);

size_Suma :: forall a b. Sum a b -> Nat;
size_Suma (Inl x1) = Suc Zero_nat;
size_Suma (Inr x2) = Suc Zero_nat;

equal_Nat :: Nata -> Nata -> Bool;
equal_Nat Zero (Suca x2) = False;
equal_Nat (Suca x2) Zero = False;
equal_Nat (Suca x2) (Suca y2) = equal_Nat x2 y2;
equal_Nat Zero Zero = True;

equal_Sum :: forall a b. (Eq a, Eq b) => Sum a b -> Sum a b -> Bool;
equal_Sum (Inl x1) (Inr x2) = False;
equal_Sum (Inr x2) (Inl x1) = False;
equal_Sum (Inr x2) (Inr y2) = x2 == y2;
equal_Sum (Inl x1) (Inl y1) = x1 == y1;

random_Nat ::
  Natural -> (Natural, Natural) -> ((Nata, () -> Term), (Natural, Natural));
random_Nat i = random_aux_Nat i i;

random_Sum ::
  forall a b.
    (Random a,
      Random b) => Natural ->
                     (Natural, Natural) ->
                       ((Sum a b, () -> Term), (Natural, Natural));
random_Sum i = random_aux_Sum i i;

one_integer :: Integer;
one_integer = (1 :: Integer);

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

term_of_Nat :: Nata -> Term;
term_of_Nat (Suca a) =
  App (Const "Enumerations.Nat.Suc"
        (Typerep "fun"
          [Typerep "Enumerations.Nat" [], Typerep "Enumerations.Nat" []]))
    (term_of_Nat a);
term_of_Nat Zero =
  Const "Enumerations.Nat.Zero" (Typerep "Enumerations.Nat" []);

term_of_Sum :: forall a b. (Term_of a, Term_of b) => Sum a b -> Term;
term_of_Sum (Inr a) =
  App (Const "Enumerations.Sum.Inr"
        (Typerep "fun"
          [(typerep :: Itself b -> Typerepa) Type,
            Typerep "Enumerations.Sum"
              [(typerep :: Itself a -> Typerepa) Type,
                (typerep :: Itself b -> Typerepa) Type]]))
    (term_of a);
term_of_Sum (Inl a) =
  App (Const "Enumerations.Sum.Inl"
        (Typerep "fun"
          [(typerep :: Itself a -> Typerepa) Type,
            Typerep "Enumerations.Sum"
              [(typerep :: Itself a -> Typerepa) Type,
                (typerep :: Itself b -> Typerepa) Type]]))
    (term_of a);

typerep_Nat :: Itself Nata -> Typerepa;
typerep_Nat t = Typerep "Enumerations.Nat" [];

typerep_Sum ::
  forall a b. (Typerep a, Typerep b) => Itself (Sum a b) -> Typerepa;
typerep_Sum t =
  Typerep "Enumerations.Sum"
    [(typerep :: Itself a -> Typerepa) Type,
      (typerep :: Itself b -> Typerepa) Type];

full_exhaustive_Nat ::
  ((Nata, () -> Term) -> Maybe (Bool, [Term])) ->
    Natural -> Maybe (Bool, [Term]);
full_exhaustive_Nat f i =
  (if less_natural zero_natural i
    then (case f (Zero,
                   (\ _ ->
                     Const "Enumerations.Nat.Zero"
                       (Typerep "Enumerations.Nat" [])))
           of {
           Nothing ->
             full_exhaustive_Nat
               (\ (uu, uua) ->
                 f (Suca uu,
                     (\ _ ->
                       App (Const "Enumerations.Nat.Suc"
                             (Typerep "fun"
                               [Typerep "Enumerations.Nat" [],
                                 Typerep "Enumerations.Nat" []]))
                         (uua ()))))
               (minus_natural i one_natural);
           Just a -> Just a;
         })
    else Nothing);

full_exhaustive_Sum ::
  forall a b.
    (Full_exhaustive a,
      Full_exhaustive b) => ((Sum a b, () -> Term) -> Maybe (Bool, [Term])) ->
                              Natural -> Maybe (Bool, [Term]);
full_exhaustive_Sum f i =
  (if less_natural zero_natural i
    then (case full_exhaustive
                 (\ (uu, uua) ->
                   f (Inl uu,
                       (\ _ ->
                         App (Const "Enumerations.Sum.Inl"
                               (Typerep "fun"
                                 [(typerep :: Itself a -> Typerepa) Type,
                                   Typerep "Enumerations.Sum"
                                     [(typerep :: Itself a -> Typerepa) Type,
                                       (typerep :: Itself b -> Typerepa)
 Type]]))
                           (uua ()))))
                 (minus_natural i one_natural)
           of {
           Nothing ->
             full_exhaustive
               (\ (uu, uua) ->
                 f (Inr uu,
                     (\ _ ->
                       App (Const "Enumerations.Sum.Inr"
                             (Typerep "fun"
                               [(typerep :: Itself b -> Typerepa) Type,
                                 Typerep "Enumerations.Sum"
                                   [(typerep :: Itself a -> Typerepa) Type,
                                     (typerep :: Itself b -> Typerepa) Type]]))
                         (uua ()))))
               (minus_natural i one_natural);
           Just a -> Just a;
         })
    else Nothing);

partial_term_of_Nat :: Itself Nata -> Narrowing_term -> Term;
partial_term_of_Nat ty (Narrowing_constructor (1 :: Integer) [a]) =
  App (Const "Enumerations.Nat.Suc"
        (Typerep "fun"
          [Typerep "Enumerations.Nat" [], Typerep "Enumerations.Nat" []]))
    (partial_term_of_Nat Type a);
partial_term_of_Nat ty (Narrowing_constructor (0 :: Integer) []) =
  Const "Enumerations.Nat.Zero" (Typerep "Enumerations.Nat" []);
partial_term_of_Nat ty (Narrowing_variable p tt) =
  Free "_" (Typerep "Enumerations.Nat" []);

partial_term_of_Sum ::
  forall a b.
    (Partial_term_of a,
      Partial_term_of b) => Itself (Sum a b) -> Narrowing_term -> Term;
partial_term_of_Sum ty (Narrowing_constructor (1 :: Integer) [a]) =
  App (Const "Enumerations.Sum.Inr"
        (Typerep "fun"
          [(typerep :: Itself b -> Typerepa) Type,
            Typerep "Enumerations.Sum"
              [(typerep :: Itself a -> Typerepa) Type,
                (typerep :: Itself b -> Typerepa) Type]]))
    ((partial_term_of :: Itself b -> Narrowing_term -> Term) Type a);
partial_term_of_Sum ty (Narrowing_constructor (0 :: Integer) [a]) =
  App (Const "Enumerations.Sum.Inl"
        (Typerep "fun"
          [(typerep :: Itself a -> Typerepa) Type,
            Typerep "Enumerations.Sum"
              [(typerep :: Itself a -> Typerepa) Type,
                (typerep :: Itself b -> Typerepa) Type]]))
    ((partial_term_of :: Itself a -> Narrowing_term -> Term) Type a);
partial_term_of_Sum ty (Narrowing_variable p tt) =
  Free "_"
    (Typerep "Enumerations.Sum"
      [(typerep :: Itself a -> Typerepa) Type,
        (typerep :: Itself b -> Typerepa) Type]);

typerep_Nat_IITN_Nat :: Itself Nat_IITN_Nat -> Typerepa;
typerep_Nat_IITN_Nat t = Typerep "Enumerations.Nat.Nat_IITN_Nat" [];

typerep_Sum_IITN_Sum ::
  forall a b. (Typerep a, Typerep b) => Itself (Sum_IITN_Sum a b) -> Typerepa;
typerep_Sum_IITN_Sum t =
  Typerep "Enumerations.Sum.Sum_IITN_Sum"
    [(typerep :: Itself a -> Typerepa) Type,
      (typerep :: Itself b -> Typerepa) Type];

}
