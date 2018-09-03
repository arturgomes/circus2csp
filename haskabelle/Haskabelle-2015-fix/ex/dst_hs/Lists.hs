{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Lists(Ord(..), Natural(..), integer_of_natural, plus_natural, Plusa(..),
         zero_natural, Zeroa(..), Monoid_adda, Times(..), Div(..), Orda(..),
         One(..), Numeral, Minus(..), Linorder, Plus(..), Zero(..), Monoid_add,
         Finite_intvl_succ(..), Semiring_numeral_div, Eqa(..), Typerepa(..),
         Itself(..), Typerep(..), Nat(..), Num(..), Set(..), Nata(..), Inta(..),
         Nibble(..), Chara(..), Nibblea(..), Char(..), Itselfa(..), Term(..),
         Nat_IITN_Nat, Inta_pre_Inta, Inta_IITN_Inta, Chara_IITN_Chara,
         Itself_pre_Itself, Nibble_pre_Nibble, Itself_IITN_Itself,
         Nibble_IITN_Nibble, Narrowing_type(..), Narrowing_term(..),
         Narrowing_cons(..), hd, tl, bitM, ball, nth, foldla, rev, insert,
         empty, set, foldr, leta, mapa, insort, sort, zipa, less_eq_natural,
         less_natural, one_natural, sgn_integer, abs_integer, apsnd,
         divmod_integer, div_integer, div_natural, log, dropa, nulla, lasta,
         preda, split, succa, takea, times_natural, mod_integer, mod_natural,
         max, natural_of_integer, minus_natural, minus_shift, next, pick,
         append, foldra, member, rotate1, fun_pow, rotate, sorted, splice,
         scomp, equal_natural, iterate, range, butlast, concata, filtera,
         list_ex, listsum, membera, remdups, remove1, distinct, less_nat,
         less_eq_nat, list_all, list_rec, nat_case, plus_int, plus_nat,
         char_size, filtermap, list_all2, list_case, list_size, partition,
         removeAll, size_char, size_list, dropWhilea, list_inter, map_filter,
         nibble_rec, replicatea, takeWhilea, rec_Nat, itself_char, itself_list,
         list_update, nibble_case, nibble_size, option_case, bot_set,
         set_Itself, pred_Itself, size_nibble, plus_nata, size_Nat, rec_Inta,
         itself_nibble, length_unique, successor_int, size_Inta, collapse,
         valapp, listsuma, select_weight, random_aux_Nat, rec_Chara,
         random_aux_Inta, size_Chara, random_aux_Nibble, random_Nibble,
         random_aux_Chara, map_Itself, rec_Itself, rel_Itself, rec_Nibble,
         random_aux_Itself, size_Itself, size_Nibble, sum, numeral, less_num,
         less_eq_num, cons, plus_num, size_Nata, equal_num, times_num,
         equal_Nat, size_Intaa, non_empty, equal_Inta, random_Nat, size_Charaa,
         equal_Nibble, equal_Chara, random_Inta, size_Itselfa, size_Nibblea,
         term_of_Nat, typerep_Nat, equal_Itself, random_Chara, term_of_Inta,
         typerep_Inta, random_Itself, term_of_Nibble, term_of_Chara,
         typerep_Chara, term_of_Itself, typerep_Itself, typerep_Nibble,
         one_integer, divmod_step, divmod, narrowing_Itself, narrowing_Nibble,
         full_exhaustive_Nat, partial_term_of_Nat, full_exhaustive_Inta,
         partial_term_of_Inta, full_exhaustive_Nibble, full_exhaustive_Chara,
         partial_term_of_Nibble, partial_term_of_Chara, typerep_Nat_IITN_Nat,
         full_exhaustive_Itself, partial_term_of_Itself, typerep_Inta_pre_Inta,
         typerep_Inta_IITN_Inta, typerep_Chara_IITN_Chara,
         typerep_Itself_pre_Itself, typerep_Nibble_pre_Nibble,
         typerep_Itself_IITN_Itself, typerep_Nibble_IITN_Nibble)
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

class Plusa a where {
  plusa :: a -> a -> a;
};

instance Plusa Natural where {
  plusa = plus_natural;
};

zero_natural :: Natural;
zero_natural = Nat (0 :: Integer);

class Zeroa a where {
  zeroa :: a;
};

instance Zeroa Natural where {
  zeroa = zero_natural;
};

class (Plusa a) => Semigroup_adda a where {
};

class (Semigroup_adda a, Zeroa a) => Monoid_adda a where {
};

instance Semigroup_adda Natural where {
};

instance Monoid_adda Natural where {
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

class Orda a where {
  less_eq :: a -> a -> Bool;
  less :: a -> a -> Bool;
};

class (Orda a) => Preorder a where {
};

class (Preorder a) => Order a where {
};

class One a where {
  one :: a;
};

class (One a, Semigroup_adda a) => Numeral a where {
};

class (One a, Times a) => Power a where {
};

class (Semigroup_adda a) => Ab_semigroup_add a where {
};

class (Ab_semigroup_add a, Monoid_adda a) => Comm_monoid_add a where {
};

class (Times a, Zeroa a) => Mult_zero a where {
};

class (Times a) => Semigroup_mult a where {
};

class (Ab_semigroup_add a, Semigroup_mult a) => Semiring a where {
};

class (Comm_monoid_add a, Mult_zero a, Semiring a) => Semiring_0 a where {
};

class (Semiring_0 a) => Semiring_no_zero_divisors a where {
};

class (Semigroup_adda a) => Cancel_semigroup_add a where {
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

class (One a, Zeroa a) => Zero_neq_one a where {
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

class (Order a) => Linorder a where {
};

class (Ord a) => Preordera a where {
};

class (Preordera a) => Ordera a where {
};

class Plus a where {
  plus :: a -> a -> a;
};

class (Plus a) => Semigroup_add a where {
};

class Zero a where {
  zero :: a;
};

class (Semigroup_add a, Zero a) => Monoid_add a where {
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

class (Linorder a) => Finite_intvl_succ a where {
  successor :: a -> a;
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

class Eqa a where {
  eq :: a -> a -> Bool;
  not_eq :: a -> a -> Bool;
};

data Typerepa = Typerep String [Typerepa];

data Itself a = Type;

class Typerep a where {
  typerep :: Itself a -> Typerepa;
};

data Nat = Zero_nat | Suc Nat;

data Num = One | Bit0 Num | Bit1 Num;

data Set a = Set [a] | Coset [a];

data Nata = Suca Nata | Zero;

data Inta = Number_of_int Inta | Bit1a Inta | Bit0a Inta | Min | Pls;

data Nibble = NibbleF | NibbleE | NibbleD | NibbleC | NibbleB | NibbleA
  | Nibble9 | Nibble8 | Nibble7 | Nibble6 | Nibble5 | Nibble4 | Nibble3
  | Nibble2 | Nibble1 | Nibble0;

data Chara = Chara Nibble Nibble;

data Nibblea = Nibble0a | Nibble1a | Nibble2a | Nibble3a | Nibble4a | Nibble5a
  | Nibble6a | Nibble7a | Nibble8a | Nibble9a | NibbleAa | NibbleBa | NibbleCa
  | NibbleDa | NibbleEa | NibbleFa;

data Char = Char Nibblea Nibblea;

data Itselfa a = Typea;

data Term = Const String Typerepa | App Term Term | Abs String Typerepa Term
  | Free String Typerepa;

data Nat_IITN_Nat;

data Inta_pre_Inta a;

data Inta_IITN_Inta;

data Chara_IITN_Chara;

data Itself_pre_Itself a b;

data Nibble_pre_Nibble;

data Itself_IITN_Itself a;

data Nibble_IITN_Nibble;

newtype Narrowing_type = Narrowing_sum_of_products [[Narrowing_type]];

data Narrowing_term = Narrowing_variable [Integer] Narrowing_type
  | Narrowing_constructor Integer [Narrowing_term];

data Narrowing_cons a = Narrowing_cons Narrowing_type [[Narrowing_term] -> a];

hd :: forall a. [a] -> a;
hd (x : xs) = x;

tl :: forall a. [a] -> [a];
tl [] = [];
tl (x : xs) = xs;

bitM :: Num -> Num;
bitM One = One;
bitM (Bit0 n) = Bit1 (bitM n);
bitM (Bit1 n) = Bit1 (Bit0 n);

ball :: forall a. Set a -> (a -> Bool) -> Bool;
ball (Set xs) p = all p xs;

nth :: forall a. [a] -> Nata -> a;
nth (x : xs) n = (case n of {
                   Suca a -> nth xs a;
                   Zero -> x;
                 });

foldla :: forall a b. (a -> b -> a) -> a -> [b] -> a;
foldla f a [] = a;
foldla f a (x : xs) = foldla f (f a x) xs;

rev :: forall a. [a] -> [a];
rev xs = foldla (\ xsa x -> x : xsa) [] xs;

insert :: forall a. (Eqa a) => a -> (a -> Bool) -> a -> Bool;
insert y a x = eq y x || a x;

empty :: forall a. a -> Bool;
empty x = False;

set :: forall a. (Eqa a) => [a] -> a -> Bool;
set [] = empty;
set (x : xs) = insert x (set xs);

foldr :: forall a b. (a -> b -> b) -> [a] -> b -> b;
foldr f [] = id;
foldr f (x : xs) = f x . foldr f xs;

leta :: forall a b. a -> (a -> b) -> b;
leta s f = f s;

mapa :: forall a b. (a -> b) -> [a] -> [b];
mapa f [] = [];
mapa f (x : xs) = f x : mapa f xs;

insort :: forall a. (Linorder a) => a -> [a] -> [a];
insort x [] = [x];
insort x (y : ys) = (if less_eq x y then x : y : ys else y : insort x ys);

sort :: forall a. (Linorder a) => [a] -> [a];
sort [] = [];
sort (x : xs) = insort x (sort xs);

zipa :: forall a b. [a] -> [b] -> [(a, b)];
zipa xs [] = [];
zipa xs (y : ys) = (case xs of {
                     [] -> [];
                     z : zs -> (z, y) : zipa zs ys;
                   });

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

dropa :: forall a. Nata -> [a] -> [a];
dropa n [] = [];
dropa n (x : xs) = (case n of {
                     Suca m -> dropa m xs;
                     Zero -> x : xs;
                   });

nulla :: forall a. [a] -> Bool;
nulla [] = True;
nulla (x : xs) = False;

lasta :: forall a. [a] -> a;
lasta (x : xs) = (if nulla xs then x else lasta xs);

preda :: Inta -> Inta;
preda (Bit1a k) = Bit0a k;
preda (Bit0a k) = Bit1a (preda k);
preda Min = Bit0a Min;
preda Pls = Min;

split :: forall a b c. (a -> b -> c) -> (a, b) -> c;
split f (a, b) = f a b;

succa :: Inta -> Inta;
succa (Bit1a k) = Bit0a (succa k);
succa (Bit0a k) = Bit1a k;
succa Min = Pls;
succa Pls = Bit1a Pls;

takea :: forall a. Nata -> [a] -> [a];
takea n [] = [];
takea n (x : xs) = (case n of {
                     Suca m -> x : takea m xs;
                     Zero -> [];
                   });

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

append :: forall a. [a] -> [a] -> [a];
append [] ys = ys;
append (x : xs) ys = x : append xs ys;

foldra :: forall a b. (a -> b -> b) -> [a] -> b -> b;
foldra f [] a = a;
foldra f (x : xs) a = f x (foldra f xs a);

member :: forall a. (Eqa a) => a -> [a] -> Bool;
member x [] = False;
member x (y : ys) = eq x y || member x ys;

rotate1 :: forall a. [a] -> [a];
rotate1 xs = (case xs of {
               [] -> [];
               x : xsa -> append xsa [x];
             });

fun_pow :: forall a. Nata -> (a -> a) -> a -> a;
fun_pow Zero f = id;
fun_pow (Suca n) f = f . fun_pow n f;

rotate :: forall a. Nata -> [a] -> [a];
rotate n = fun_pow n rotate1;

sorted :: forall a. (Linorder a) => [a] -> Bool;
sorted [] = True;
sorted [x] = True;
sorted (x : y : zs) = less_eq x y && sorted (y : zs);

splice :: forall a. [a] -> [a] -> [a];
splice (x : xs) (y : ys) = x : y : splice xs ys;
splice xs [] = xs;

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

butlast :: forall a. [a] -> [a];
butlast [] = [];
butlast (x : xs) = (if nulla xs then [] else x : butlast xs);

concata :: forall a. [[a]] -> [a];
concata [] = [];
concata (x : xs) = append x (concata xs);

filtera :: forall a. (a -> Bool) -> [a] -> [a];
filtera p [] = [];
filtera p (x : xs) = (if p x then x : filtera p xs else filtera p xs);

list_ex :: forall a. (a -> Bool) -> [a] -> Bool;
list_ex p [] = False;
list_ex p (x : xs) = p x || list_ex p xs;

listsum :: forall a. (Monoid_add a) => [a] -> a;
listsum [] = zero;
listsum (x : xs) = plus x (foldla plus zero xs);

membera :: forall a. a -> (a -> Bool) -> Bool;
membera x s = s x;

remdups :: forall a. (Eqa a) => [a] -> [a];
remdups [] = [];
remdups (x : xs) = (if member x xs then remdups xs else x : remdups xs);

remove1 :: forall a. (Eqa a) => a -> [a] -> [a];
remove1 x [] = [];
remove1 x (y : xs) = (if eq x y then xs else y : remove1 x xs);

distinct :: forall a. (Eqa a) => [a] -> Bool;
distinct [] = True;
distinct (x : xs) = not (member x xs) && distinct xs;

less_nat :: Nata -> Nata -> Bool;
less_nat m (Suca n) = less_eq_nat m n;
less_nat n Zero = False;

less_eq_nat :: Nata -> Nata -> Bool;
less_eq_nat (Suca m) n = less_nat m n;
less_eq_nat Zero n = True;

list_all :: forall a. (a -> Bool) -> [a] -> Bool;
list_all p [] = True;
list_all p (x : xs) = p x && list_all p xs;

list_rec :: forall a b. a -> (b -> [b] -> a -> a) -> [b] -> a;
list_rec f1 f2 [] = f1;
list_rec f1 f2 (a : list) = f2 a list (list_rec f1 f2 list);

nat_case :: forall a. a -> (Nata -> a) -> Nata -> a;
nat_case f1 f2 (Suca nat0) = f2 nat0;
nat_case f1 f2 Zero = f1;

plus_int :: Inta -> Inta -> Inta;
plus_int (Number_of_int v) (Number_of_int w) = Number_of_int (plus_int v w);
plus_int (Bit1a k) (Bit1a l) = Bit0a (plus_int k (succa l));
plus_int (Bit1a k) (Bit0a l) = Bit1a (plus_int k l);
plus_int (Bit0a k) (Bit1a l) = Bit1a (plus_int k l);
plus_int (Bit0a k) (Bit0a l) = Bit0a (plus_int k l);
plus_int k Min = preda k;
plus_int k Pls = k;
plus_int Min (Number_of_int v) = preda (Number_of_int v);
plus_int Min (Bit1a v) = preda (Bit1a v);
plus_int Min (Bit0a v) = preda (Bit0a v);
plus_int Pls (Number_of_int v) = Number_of_int v;
plus_int Pls (Bit1a v) = Bit1a v;
plus_int Pls (Bit0a v) = Bit0a v;

plus_nat :: Nata -> Nata -> Nata;
plus_nat (Suca m) n = plus_nat m (Suca n);
plus_nat Zero n = n;

char_size :: Chara -> Nata;
char_size c = Zero;

filtermap :: forall a b. (a -> Maybe b) -> [a] -> [b];
filtermap f [] = [];
filtermap f (x : xs) =
  (case f x of {
    Nothing -> filtermap f xs;
    Just y -> y : filtermap f xs;
  });

list_all2 :: forall a b. (a -> b -> Bool) -> [a] -> [b] -> Bool;
list_all2 p (x : xs) (y : ys) = p x y && list_all2 p xs ys;
list_all2 p xs [] = nulla xs;
list_all2 p [] (v : va) = nulla (v : va);

list_case :: forall a b. a -> (b -> [b] -> a) -> [b] -> a;
list_case f1 f2 (a : list) = f2 a list;
list_case f1 f2 [] = f1;

list_size :: forall a. (a -> Nata) -> [a] -> Nata;
list_size fa [] = Zero;
list_size fa (a : list) =
  plus_nat (plus_nat (fa a) (list_size fa list)) (Suca Zero);

partition :: forall a. (a -> Bool) -> [a] -> ([a], [a]);
partition p [] = ([], []);
partition p (x : xs) =
  let {
    (yes, no) = partition p xs;
  } in (if p x then (x : yes, no) else (yes, x : no));

removeAll :: forall a. (Eqa a) => a -> [a] -> [a];
removeAll x [] = [];
removeAll x (y : xs) = (if eq x y then removeAll x xs else y : removeAll x xs);

size_char :: Chara -> Nata;
size_char c = Zero;

size_list :: forall a. [a] -> Nata;
size_list [] = Zero;
size_list (a : list) = plus_nat (size_list list) (Suca Zero);

dropWhilea :: forall a. (a -> Bool) -> [a] -> [a];
dropWhilea p [] = [];
dropWhilea p (x : xs) = (if p x then dropWhilea p xs else x : xs);

list_inter :: forall a. (Eqa a) => [a] -> [a] -> [a];
list_inter [] bs = [];
list_inter (a : asa) bs =
  (if member a bs then a : list_inter asa bs else list_inter asa bs);

map_filter :: forall a b. (a -> b) -> (a -> Bool) -> [a] -> [b];
map_filter f p [] = [];
map_filter f p (x : xs) =
  (if p x then f x : map_filter f p xs else map_filter f p xs);

nibble_rec ::
  forall a.
    a -> a -> a -> a -> a -> a -> a -> a ->
 a -> a -> a -> a -> a -> a -> a -> a -> Nibble -> a;
nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble0 = f1;
nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble1 = f2;
nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble2 = f3;
nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble3 = f4;
nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble4 = f5;
nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble5 = f6;
nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble6 = f7;
nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble7 = f8;
nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble8 = f9;
nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble9 = f10;
nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 NibbleA = f11;
nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 NibbleB = f12;
nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 NibbleC = f13;
nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 NibbleD = f14;
nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 NibbleE = f15;
nibble_rec f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 NibbleF = f16;

replicatea :: forall a. Nata -> a -> [a];
replicatea Zero x = [];
replicatea (Suca n) x = x : replicatea n x;

takeWhilea :: forall a. (a -> Bool) -> [a] -> [a];
takeWhilea p [] = [];
takeWhilea p (x : xs) = (if p x then x : takeWhilea p xs else []);

rec_Nat :: forall a. (Nata -> a -> a) -> a -> Nata -> a;
rec_Nat f1 f2 (Suca x1) = f1 x1 (rec_Nat f1 f2 x1);
rec_Nat f1 f2 Zero = f2;

itself_char :: Itselfa Chara;
itself_char = Typea;

itself_list :: forall a. Itselfa [a];
itself_list = Typea;

list_update :: forall a. [a] -> Nata -> a -> [a];
list_update [] i v = [];
list_update (x : xs) i v =
  (case i of {
    Suca j -> x : list_update xs j v;
    Zero -> v : xs;
  });

nibble_case ::
  forall a.
    a -> a -> a -> a -> a -> a -> a -> a ->
 a -> a -> a -> a -> a -> a -> a -> a -> Nibble -> a;
nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 NibbleF =
  f16;
nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 NibbleE =
  f15;
nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 NibbleD =
  f14;
nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 NibbleC =
  f13;
nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 NibbleB =
  f12;
nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 NibbleA =
  f11;
nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble9 =
  f10;
nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble8 = f9;
nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble7 = f8;
nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble6 = f7;
nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble5 = f6;
nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble4 = f5;
nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble3 = f4;
nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble2 = f3;
nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble1 = f2;
nibble_case f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble0 = f1;

nibble_size :: Nibble -> Nata;
nibble_size Nibble0 = Zero;
nibble_size Nibble1 = Zero;
nibble_size Nibble2 = Zero;
nibble_size Nibble3 = Zero;
nibble_size Nibble4 = Zero;
nibble_size Nibble5 = Zero;
nibble_size Nibble6 = Zero;
nibble_size Nibble7 = Zero;
nibble_size Nibble8 = Zero;
nibble_size Nibble9 = Zero;
nibble_size NibbleA = Zero;
nibble_size NibbleB = Zero;
nibble_size NibbleC = Zero;
nibble_size NibbleD = Zero;
nibble_size NibbleE = Zero;
nibble_size NibbleF = Zero;

option_case :: forall a b. a -> (b -> a) -> Maybe b -> a;
option_case f1 f2 (Just a) = f2 a;
option_case f1 f2 Nothing = f1;

bot_set :: forall a. Set a;
bot_set = Set [];

set_Itself :: forall a. Itselfa a -> Set a;
set_Itself Typea = bot_set;

pred_Itself :: forall a. (a -> Bool) -> Itselfa a -> Bool;
pred_Itself p = (\ x -> ball (set_Itself x) p);

size_nibble :: Nibble -> Nata;
size_nibble Nibble0 = Zero;
size_nibble Nibble1 = Zero;
size_nibble Nibble2 = Zero;
size_nibble Nibble3 = Zero;
size_nibble Nibble4 = Zero;
size_nibble Nibble5 = Zero;
size_nibble Nibble6 = Zero;
size_nibble Nibble7 = Zero;
size_nibble Nibble8 = Zero;
size_nibble Nibble9 = Zero;
size_nibble NibbleA = Zero;
size_nibble NibbleB = Zero;
size_nibble NibbleC = Zero;
size_nibble NibbleD = Zero;
size_nibble NibbleE = Zero;
size_nibble NibbleF = Zero;

plus_nata :: Nat -> Nat -> Nat;
plus_nata (Suc m) n = plus_nata m (Suc n);
plus_nata Zero_nat n = n;

size_Nat :: Nata -> Nat;
size_Nat (Suca x1) = plus_nata (size_Nat x1) (Suc Zero_nat);
size_Nat Zero = Zero_nat;

rec_Inta ::
  forall a.
    (Inta -> a -> a) ->
      (Inta -> a -> a) -> (Inta -> a -> a) -> a -> a -> Inta -> a;
rec_Inta f1 f2 f3 f4 f5 (Number_of_int x1) = f1 x1 (rec_Inta f1 f2 f3 f4 f5 x1);
rec_Inta f1 f2 f3 f4 f5 (Bit1a x2) = f2 x2 (rec_Inta f1 f2 f3 f4 f5 x2);
rec_Inta f1 f2 f3 f4 f5 (Bit0a x3) = f3 x3 (rec_Inta f1 f2 f3 f4 f5 x3);
rec_Inta f1 f2 f3 f4 f5 Min = f4;
rec_Inta f1 f2 f3 f4 f5 Pls = f5;

itself_nibble :: Itselfa Nibble;
itself_nibble = Typea;

length_unique :: forall a. (Eqa a) => [a] -> Nata;
length_unique [] = Zero;
length_unique (x : xs) =
  (if member x xs then length_unique xs else Suca (length_unique xs));

successor_int :: Inta -> Inta;
successor_int = (\ i -> plus_int i (Number_of_int (Bit1a Pls)));

size_Inta :: Inta -> Nat;
size_Inta (Number_of_int x1) = plus_nata (size_Inta x1) (Suc Zero_nat);
size_Inta (Bit1a x2) = plus_nata (size_Inta x2) (Suc Zero_nat);
size_Inta (Bit0a x3) = plus_nata (size_Inta x3) (Suc Zero_nat);
size_Inta Min = Zero_nat;
size_Inta Pls = Zero_nat;

collapse :: forall a b. (a -> (a -> (b, a), a)) -> a -> (b, a);
collapse f = scomp f id;

valapp ::
  forall a b. (a -> b, () -> Term) -> (a, () -> Term) -> (b, () -> Term);
valapp (f, tf) (x, tx) = (f x, (\ _ -> App (tf ()) (tx ())));

listsuma :: forall a. (Monoid_adda a) => [a] -> a;
listsuma xs = foldr plusa xs zeroa;

select_weight ::
  forall a. [(Natural, a)] -> (Natural, Natural) -> (a, (Natural, Natural));
select_weight xs =
  scomp (range (listsuma (map fst xs))) (\ k -> (\ a -> (pick xs k, a)));

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
                        Const "Lists.Nat.Suc"
                          (Typerep "fun"
                            [Typerep "Lists.Nat" [], Typerep "Lists.Nat" []])))
                    x,
                   a)))),
        (one_natural,
          (\ a ->
            ((Zero, (\ _ -> Const "Lists.Nat.Zero" (Typerep "Lists.Nat" []))),
              a)))])
    s;

rec_Chara :: forall a. (Nibble -> Nibble -> a) -> Chara -> a;
rec_Chara f (Chara x1 x2) = f x1 x2;

random_aux_Inta ::
  Natural ->
    Natural -> (Natural, Natural) -> ((Inta, () -> Term), (Natural, Natural));
random_aux_Inta i j s =
  collapse
    (select_weight
      [(i, scomp (random_aux_Inta (minus_natural i one_natural) j)
             (\ x ->
               (\ a ->
                 (valapp
                    (Number_of_int,
                      (\ _ ->
                        Const "Lists.Inta.Number_of_int"
                          (Typerep "fun"
                            [Typerep "Lists.Inta" [],
                              Typerep "Lists.Inta" []])))
                    x,
                   a)))),
        (i, scomp (random_aux_Inta (minus_natural i one_natural) j)
              (\ x ->
                (\ a ->
                  (valapp
                     (Bit1a,
                       (\ _ ->
                         Const "Lists.Inta.Bit1"
                           (Typerep "fun"
                             [Typerep "Lists.Inta" [],
                               Typerep "Lists.Inta" []])))
                     x,
                    a)))),
        (i, scomp (random_aux_Inta (minus_natural i one_natural) j)
              (\ x ->
                (\ a ->
                  (valapp
                     (Bit0a,
                       (\ _ ->
                         Const "Lists.Inta.Bit0"
                           (Typerep "fun"
                             [Typerep "Lists.Inta" [],
                               Typerep "Lists.Inta" []])))
                     x,
                    a)))),
        (one_natural,
          (\ a ->
            ((Min, (\ _ -> Const "Lists.Inta.Min" (Typerep "Lists.Inta" []))),
              a))),
        (one_natural,
          (\ a ->
            ((Pls, (\ _ -> Const "Lists.Inta.Pls" (Typerep "Lists.Inta" []))),
              a)))])
    s;

size_Chara :: Chara -> Nat;
size_Chara (Chara x1 x2) = Zero_nat;

random_aux_Nibble ::
  Natural ->
    Natural -> (Natural, Natural) -> ((Nibble, () -> Term), (Natural, Natural));
random_aux_Nibble i j s =
  collapse
    (select_weight
      [(one_natural,
         (\ a ->
           ((NibbleF,
              (\ _ ->
                Const "Lists.Nibble.NibbleF" (Typerep "Lists.Nibble" []))),
             a))),
        (one_natural,
          (\ a ->
            ((NibbleE,
               (\ _ ->
                 Const "Lists.Nibble.NibbleE" (Typerep "Lists.Nibble" []))),
              a))),
        (one_natural,
          (\ a ->
            ((NibbleD,
               (\ _ ->
                 Const "Lists.Nibble.NibbleD" (Typerep "Lists.Nibble" []))),
              a))),
        (one_natural,
          (\ a ->
            ((NibbleC,
               (\ _ ->
                 Const "Lists.Nibble.NibbleC" (Typerep "Lists.Nibble" []))),
              a))),
        (one_natural,
          (\ a ->
            ((NibbleB,
               (\ _ ->
                 Const "Lists.Nibble.NibbleB" (Typerep "Lists.Nibble" []))),
              a))),
        (one_natural,
          (\ a ->
            ((NibbleA,
               (\ _ ->
                 Const "Lists.Nibble.NibbleA" (Typerep "Lists.Nibble" []))),
              a))),
        (one_natural,
          (\ a ->
            ((Nibble9,
               (\ _ ->
                 Const "Lists.Nibble.Nibble9" (Typerep "Lists.Nibble" []))),
              a))),
        (one_natural,
          (\ a ->
            ((Nibble8,
               (\ _ ->
                 Const "Lists.Nibble.Nibble8" (Typerep "Lists.Nibble" []))),
              a))),
        (one_natural,
          (\ a ->
            ((Nibble7,
               (\ _ ->
                 Const "Lists.Nibble.Nibble7" (Typerep "Lists.Nibble" []))),
              a))),
        (one_natural,
          (\ a ->
            ((Nibble6,
               (\ _ ->
                 Const "Lists.Nibble.Nibble6" (Typerep "Lists.Nibble" []))),
              a))),
        (one_natural,
          (\ a ->
            ((Nibble5,
               (\ _ ->
                 Const "Lists.Nibble.Nibble5" (Typerep "Lists.Nibble" []))),
              a))),
        (one_natural,
          (\ a ->
            ((Nibble4,
               (\ _ ->
                 Const "Lists.Nibble.Nibble4" (Typerep "Lists.Nibble" []))),
              a))),
        (one_natural,
          (\ a ->
            ((Nibble3,
               (\ _ ->
                 Const "Lists.Nibble.Nibble3" (Typerep "Lists.Nibble" []))),
              a))),
        (one_natural,
          (\ a ->
            ((Nibble2,
               (\ _ ->
                 Const "Lists.Nibble.Nibble2" (Typerep "Lists.Nibble" []))),
              a))),
        (one_natural,
          (\ a ->
            ((Nibble1,
               (\ _ ->
                 Const "Lists.Nibble.Nibble1" (Typerep "Lists.Nibble" []))),
              a))),
        (one_natural,
          (\ a ->
            ((Nibble0,
               (\ _ ->
                 Const "Lists.Nibble.Nibble0" (Typerep "Lists.Nibble" []))),
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
                            Const "Lists.Chara.Chara"
                              (Typerep "fun"
                                [Typerep "Lists.Nibble" [],
                                  Typerep "fun"
                                    [Typerep "Lists.Nibble" [],
                                      Typerep "Lists.Chara" []]])))
                        x)
                      y,
                     a)))))])
    s;

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
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 NibbleF = f1;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 NibbleE = f2;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 NibbleD = f3;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 NibbleC = f4;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 NibbleB = f5;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 NibbleA = f6;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble9 = f7;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble8 = f8;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble7 = f9;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble6 = f10;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble5 = f11;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble4 = f12;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble3 = f13;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble2 = f14;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble1 = f15;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble0 = f16;

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
                Const "Lists.Itself.Type"
                  (Typerep "Lists.Itself"
                    [(typerep :: Itself a -> Typerepa) Type]))),
             a)))])
    s;

size_Itself :: forall a. (a -> Nat) -> Itselfa a -> Nat;
size_Itself x Typea = Zero_nat;

size_Nibble :: Nibble -> Nat;
size_Nibble NibbleF = Zero_nat;
size_Nibble NibbleE = Zero_nat;
size_Nibble NibbleD = Zero_nat;
size_Nibble NibbleC = Zero_nat;
size_Nibble NibbleB = Zero_nat;
size_Nibble NibbleA = Zero_nat;
size_Nibble Nibble9 = Zero_nat;
size_Nibble Nibble8 = Zero_nat;
size_Nibble Nibble7 = Zero_nat;
size_Nibble Nibble6 = Zero_nat;
size_Nibble Nibble5 = Zero_nat;
size_Nibble Nibble4 = Zero_nat;
size_Nibble Nibble3 = Zero_nat;
size_Nibble Nibble2 = Zero_nat;
size_Nibble Nibble1 = Zero_nat;
size_Nibble Nibble0 = Zero_nat;

sum ::
  forall a.
    (Integer -> Narrowing_cons a) ->
      (Integer -> Narrowing_cons a) -> Integer -> Narrowing_cons a;
sum a b d =
  let {
    (Narrowing_cons (Narrowing_sum_of_products ssa) ca) = a d;
    (Narrowing_cons (Narrowing_sum_of_products ssb) cb) = b d;
  } in Narrowing_cons (Narrowing_sum_of_products (ssa ++ ssb)) (ca ++ cb);

numeral :: forall a. (Numeral a) => Num -> a;
numeral (Bit1 n) = let {
                     m = numeral n;
                   } in plusa (plusa m m) one;
numeral (Bit0 n) = let {
                     m = numeral n;
                   } in plusa m m;
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

size_Nata :: Nata -> Nat;
size_Nata (Suca x1) = plus_nata (size_Nata x1) (Suc Zero_nat);
size_Nata Zero = Zero_nat;

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

equal_Nat :: Nata -> Nata -> Bool;
equal_Nat (Suca x1) Zero = False;
equal_Nat Zero (Suca x1) = False;
equal_Nat (Suca x1) (Suca y1) = equal_Nat x1 y1;
equal_Nat Zero Zero = True;

size_Intaa :: Inta -> Nat;
size_Intaa (Number_of_int x1) = plus_nata (size_Intaa x1) (Suc Zero_nat);
size_Intaa (Bit1a x2) = plus_nata (size_Intaa x2) (Suc Zero_nat);
size_Intaa (Bit0a x3) = plus_nata (size_Intaa x3) (Suc Zero_nat);
size_Intaa Min = Zero_nat;
size_Intaa Pls = Zero_nat;

non_empty :: Narrowing_type -> Bool;
non_empty (Narrowing_sum_of_products ps) = not (null ps);

equal_Inta :: Inta -> Inta -> Bool;
equal_Inta Min Pls = False;
equal_Inta Pls Min = False;
equal_Inta (Bit0a x3) Pls = False;
equal_Inta Pls (Bit0a x3) = False;
equal_Inta (Bit0a x3) Min = False;
equal_Inta Min (Bit0a x3) = False;
equal_Inta (Bit1a x2) Pls = False;
equal_Inta Pls (Bit1a x2) = False;
equal_Inta (Bit1a x2) Min = False;
equal_Inta Min (Bit1a x2) = False;
equal_Inta (Bit1a x2) (Bit0a x3) = False;
equal_Inta (Bit0a x3) (Bit1a x2) = False;
equal_Inta (Number_of_int x1) Pls = False;
equal_Inta Pls (Number_of_int x1) = False;
equal_Inta (Number_of_int x1) Min = False;
equal_Inta Min (Number_of_int x1) = False;
equal_Inta (Number_of_int x1) (Bit0a x3) = False;
equal_Inta (Bit0a x3) (Number_of_int x1) = False;
equal_Inta (Number_of_int x1) (Bit1a x2) = False;
equal_Inta (Bit1a x2) (Number_of_int x1) = False;
equal_Inta (Bit0a x3) (Bit0a y3) = equal_Inta x3 y3;
equal_Inta (Bit1a x2) (Bit1a y2) = equal_Inta x2 y2;
equal_Inta (Number_of_int x1) (Number_of_int y1) = equal_Inta x1 y1;
equal_Inta Pls Pls = True;
equal_Inta Min Min = True;

random_Nat ::
  Natural -> (Natural, Natural) -> ((Nata, () -> Term), (Natural, Natural));
random_Nat i = random_aux_Nat i i;

size_Charaa :: Chara -> Nat;
size_Charaa (Chara x1 x2) = Zero_nat;

equal_Nibble :: Nibble -> Nibble -> Bool;
equal_Nibble Nibble1 Nibble0 = False;
equal_Nibble Nibble0 Nibble1 = False;
equal_Nibble Nibble2 Nibble0 = False;
equal_Nibble Nibble0 Nibble2 = False;
equal_Nibble Nibble2 Nibble1 = False;
equal_Nibble Nibble1 Nibble2 = False;
equal_Nibble Nibble3 Nibble0 = False;
equal_Nibble Nibble0 Nibble3 = False;
equal_Nibble Nibble3 Nibble1 = False;
equal_Nibble Nibble1 Nibble3 = False;
equal_Nibble Nibble3 Nibble2 = False;
equal_Nibble Nibble2 Nibble3 = False;
equal_Nibble Nibble4 Nibble0 = False;
equal_Nibble Nibble0 Nibble4 = False;
equal_Nibble Nibble4 Nibble1 = False;
equal_Nibble Nibble1 Nibble4 = False;
equal_Nibble Nibble4 Nibble2 = False;
equal_Nibble Nibble2 Nibble4 = False;
equal_Nibble Nibble4 Nibble3 = False;
equal_Nibble Nibble3 Nibble4 = False;
equal_Nibble Nibble5 Nibble0 = False;
equal_Nibble Nibble0 Nibble5 = False;
equal_Nibble Nibble5 Nibble1 = False;
equal_Nibble Nibble1 Nibble5 = False;
equal_Nibble Nibble5 Nibble2 = False;
equal_Nibble Nibble2 Nibble5 = False;
equal_Nibble Nibble5 Nibble3 = False;
equal_Nibble Nibble3 Nibble5 = False;
equal_Nibble Nibble5 Nibble4 = False;
equal_Nibble Nibble4 Nibble5 = False;
equal_Nibble Nibble6 Nibble0 = False;
equal_Nibble Nibble0 Nibble6 = False;
equal_Nibble Nibble6 Nibble1 = False;
equal_Nibble Nibble1 Nibble6 = False;
equal_Nibble Nibble6 Nibble2 = False;
equal_Nibble Nibble2 Nibble6 = False;
equal_Nibble Nibble6 Nibble3 = False;
equal_Nibble Nibble3 Nibble6 = False;
equal_Nibble Nibble6 Nibble4 = False;
equal_Nibble Nibble4 Nibble6 = False;
equal_Nibble Nibble6 Nibble5 = False;
equal_Nibble Nibble5 Nibble6 = False;
equal_Nibble Nibble7 Nibble0 = False;
equal_Nibble Nibble0 Nibble7 = False;
equal_Nibble Nibble7 Nibble1 = False;
equal_Nibble Nibble1 Nibble7 = False;
equal_Nibble Nibble7 Nibble2 = False;
equal_Nibble Nibble2 Nibble7 = False;
equal_Nibble Nibble7 Nibble3 = False;
equal_Nibble Nibble3 Nibble7 = False;
equal_Nibble Nibble7 Nibble4 = False;
equal_Nibble Nibble4 Nibble7 = False;
equal_Nibble Nibble7 Nibble5 = False;
equal_Nibble Nibble5 Nibble7 = False;
equal_Nibble Nibble7 Nibble6 = False;
equal_Nibble Nibble6 Nibble7 = False;
equal_Nibble Nibble8 Nibble0 = False;
equal_Nibble Nibble0 Nibble8 = False;
equal_Nibble Nibble8 Nibble1 = False;
equal_Nibble Nibble1 Nibble8 = False;
equal_Nibble Nibble8 Nibble2 = False;
equal_Nibble Nibble2 Nibble8 = False;
equal_Nibble Nibble8 Nibble3 = False;
equal_Nibble Nibble3 Nibble8 = False;
equal_Nibble Nibble8 Nibble4 = False;
equal_Nibble Nibble4 Nibble8 = False;
equal_Nibble Nibble8 Nibble5 = False;
equal_Nibble Nibble5 Nibble8 = False;
equal_Nibble Nibble8 Nibble6 = False;
equal_Nibble Nibble6 Nibble8 = False;
equal_Nibble Nibble8 Nibble7 = False;
equal_Nibble Nibble7 Nibble8 = False;
equal_Nibble Nibble9 Nibble0 = False;
equal_Nibble Nibble0 Nibble9 = False;
equal_Nibble Nibble9 Nibble1 = False;
equal_Nibble Nibble1 Nibble9 = False;
equal_Nibble Nibble9 Nibble2 = False;
equal_Nibble Nibble2 Nibble9 = False;
equal_Nibble Nibble9 Nibble3 = False;
equal_Nibble Nibble3 Nibble9 = False;
equal_Nibble Nibble9 Nibble4 = False;
equal_Nibble Nibble4 Nibble9 = False;
equal_Nibble Nibble9 Nibble5 = False;
equal_Nibble Nibble5 Nibble9 = False;
equal_Nibble Nibble9 Nibble6 = False;
equal_Nibble Nibble6 Nibble9 = False;
equal_Nibble Nibble9 Nibble7 = False;
equal_Nibble Nibble7 Nibble9 = False;
equal_Nibble Nibble9 Nibble8 = False;
equal_Nibble Nibble8 Nibble9 = False;
equal_Nibble NibbleA Nibble0 = False;
equal_Nibble Nibble0 NibbleA = False;
equal_Nibble NibbleA Nibble1 = False;
equal_Nibble Nibble1 NibbleA = False;
equal_Nibble NibbleA Nibble2 = False;
equal_Nibble Nibble2 NibbleA = False;
equal_Nibble NibbleA Nibble3 = False;
equal_Nibble Nibble3 NibbleA = False;
equal_Nibble NibbleA Nibble4 = False;
equal_Nibble Nibble4 NibbleA = False;
equal_Nibble NibbleA Nibble5 = False;
equal_Nibble Nibble5 NibbleA = False;
equal_Nibble NibbleA Nibble6 = False;
equal_Nibble Nibble6 NibbleA = False;
equal_Nibble NibbleA Nibble7 = False;
equal_Nibble Nibble7 NibbleA = False;
equal_Nibble NibbleA Nibble8 = False;
equal_Nibble Nibble8 NibbleA = False;
equal_Nibble NibbleA Nibble9 = False;
equal_Nibble Nibble9 NibbleA = False;
equal_Nibble NibbleB Nibble0 = False;
equal_Nibble Nibble0 NibbleB = False;
equal_Nibble NibbleB Nibble1 = False;
equal_Nibble Nibble1 NibbleB = False;
equal_Nibble NibbleB Nibble2 = False;
equal_Nibble Nibble2 NibbleB = False;
equal_Nibble NibbleB Nibble3 = False;
equal_Nibble Nibble3 NibbleB = False;
equal_Nibble NibbleB Nibble4 = False;
equal_Nibble Nibble4 NibbleB = False;
equal_Nibble NibbleB Nibble5 = False;
equal_Nibble Nibble5 NibbleB = False;
equal_Nibble NibbleB Nibble6 = False;
equal_Nibble Nibble6 NibbleB = False;
equal_Nibble NibbleB Nibble7 = False;
equal_Nibble Nibble7 NibbleB = False;
equal_Nibble NibbleB Nibble8 = False;
equal_Nibble Nibble8 NibbleB = False;
equal_Nibble NibbleB Nibble9 = False;
equal_Nibble Nibble9 NibbleB = False;
equal_Nibble NibbleB NibbleA = False;
equal_Nibble NibbleA NibbleB = False;
equal_Nibble NibbleC Nibble0 = False;
equal_Nibble Nibble0 NibbleC = False;
equal_Nibble NibbleC Nibble1 = False;
equal_Nibble Nibble1 NibbleC = False;
equal_Nibble NibbleC Nibble2 = False;
equal_Nibble Nibble2 NibbleC = False;
equal_Nibble NibbleC Nibble3 = False;
equal_Nibble Nibble3 NibbleC = False;
equal_Nibble NibbleC Nibble4 = False;
equal_Nibble Nibble4 NibbleC = False;
equal_Nibble NibbleC Nibble5 = False;
equal_Nibble Nibble5 NibbleC = False;
equal_Nibble NibbleC Nibble6 = False;
equal_Nibble Nibble6 NibbleC = False;
equal_Nibble NibbleC Nibble7 = False;
equal_Nibble Nibble7 NibbleC = False;
equal_Nibble NibbleC Nibble8 = False;
equal_Nibble Nibble8 NibbleC = False;
equal_Nibble NibbleC Nibble9 = False;
equal_Nibble Nibble9 NibbleC = False;
equal_Nibble NibbleC NibbleA = False;
equal_Nibble NibbleA NibbleC = False;
equal_Nibble NibbleC NibbleB = False;
equal_Nibble NibbleB NibbleC = False;
equal_Nibble NibbleD Nibble0 = False;
equal_Nibble Nibble0 NibbleD = False;
equal_Nibble NibbleD Nibble1 = False;
equal_Nibble Nibble1 NibbleD = False;
equal_Nibble NibbleD Nibble2 = False;
equal_Nibble Nibble2 NibbleD = False;
equal_Nibble NibbleD Nibble3 = False;
equal_Nibble Nibble3 NibbleD = False;
equal_Nibble NibbleD Nibble4 = False;
equal_Nibble Nibble4 NibbleD = False;
equal_Nibble NibbleD Nibble5 = False;
equal_Nibble Nibble5 NibbleD = False;
equal_Nibble NibbleD Nibble6 = False;
equal_Nibble Nibble6 NibbleD = False;
equal_Nibble NibbleD Nibble7 = False;
equal_Nibble Nibble7 NibbleD = False;
equal_Nibble NibbleD Nibble8 = False;
equal_Nibble Nibble8 NibbleD = False;
equal_Nibble NibbleD Nibble9 = False;
equal_Nibble Nibble9 NibbleD = False;
equal_Nibble NibbleD NibbleA = False;
equal_Nibble NibbleA NibbleD = False;
equal_Nibble NibbleD NibbleB = False;
equal_Nibble NibbleB NibbleD = False;
equal_Nibble NibbleD NibbleC = False;
equal_Nibble NibbleC NibbleD = False;
equal_Nibble NibbleE Nibble0 = False;
equal_Nibble Nibble0 NibbleE = False;
equal_Nibble NibbleE Nibble1 = False;
equal_Nibble Nibble1 NibbleE = False;
equal_Nibble NibbleE Nibble2 = False;
equal_Nibble Nibble2 NibbleE = False;
equal_Nibble NibbleE Nibble3 = False;
equal_Nibble Nibble3 NibbleE = False;
equal_Nibble NibbleE Nibble4 = False;
equal_Nibble Nibble4 NibbleE = False;
equal_Nibble NibbleE Nibble5 = False;
equal_Nibble Nibble5 NibbleE = False;
equal_Nibble NibbleE Nibble6 = False;
equal_Nibble Nibble6 NibbleE = False;
equal_Nibble NibbleE Nibble7 = False;
equal_Nibble Nibble7 NibbleE = False;
equal_Nibble NibbleE Nibble8 = False;
equal_Nibble Nibble8 NibbleE = False;
equal_Nibble NibbleE Nibble9 = False;
equal_Nibble Nibble9 NibbleE = False;
equal_Nibble NibbleE NibbleA = False;
equal_Nibble NibbleA NibbleE = False;
equal_Nibble NibbleE NibbleB = False;
equal_Nibble NibbleB NibbleE = False;
equal_Nibble NibbleE NibbleC = False;
equal_Nibble NibbleC NibbleE = False;
equal_Nibble NibbleE NibbleD = False;
equal_Nibble NibbleD NibbleE = False;
equal_Nibble NibbleF Nibble0 = False;
equal_Nibble Nibble0 NibbleF = False;
equal_Nibble NibbleF Nibble1 = False;
equal_Nibble Nibble1 NibbleF = False;
equal_Nibble NibbleF Nibble2 = False;
equal_Nibble Nibble2 NibbleF = False;
equal_Nibble NibbleF Nibble3 = False;
equal_Nibble Nibble3 NibbleF = False;
equal_Nibble NibbleF Nibble4 = False;
equal_Nibble Nibble4 NibbleF = False;
equal_Nibble NibbleF Nibble5 = False;
equal_Nibble Nibble5 NibbleF = False;
equal_Nibble NibbleF Nibble6 = False;
equal_Nibble Nibble6 NibbleF = False;
equal_Nibble NibbleF Nibble7 = False;
equal_Nibble Nibble7 NibbleF = False;
equal_Nibble NibbleF Nibble8 = False;
equal_Nibble Nibble8 NibbleF = False;
equal_Nibble NibbleF Nibble9 = False;
equal_Nibble Nibble9 NibbleF = False;
equal_Nibble NibbleF NibbleA = False;
equal_Nibble NibbleA NibbleF = False;
equal_Nibble NibbleF NibbleB = False;
equal_Nibble NibbleB NibbleF = False;
equal_Nibble NibbleF NibbleC = False;
equal_Nibble NibbleC NibbleF = False;
equal_Nibble NibbleF NibbleD = False;
equal_Nibble NibbleD NibbleF = False;
equal_Nibble NibbleF NibbleE = False;
equal_Nibble NibbleE NibbleF = False;
equal_Nibble Nibble0 Nibble0 = True;
equal_Nibble Nibble1 Nibble1 = True;
equal_Nibble Nibble2 Nibble2 = True;
equal_Nibble Nibble3 Nibble3 = True;
equal_Nibble Nibble4 Nibble4 = True;
equal_Nibble Nibble5 Nibble5 = True;
equal_Nibble Nibble6 Nibble6 = True;
equal_Nibble Nibble7 Nibble7 = True;
equal_Nibble Nibble8 Nibble8 = True;
equal_Nibble Nibble9 Nibble9 = True;
equal_Nibble NibbleA NibbleA = True;
equal_Nibble NibbleB NibbleB = True;
equal_Nibble NibbleC NibbleC = True;
equal_Nibble NibbleD NibbleD = True;
equal_Nibble NibbleE NibbleE = True;
equal_Nibble NibbleF NibbleF = True;

equal_Chara :: Chara -> Chara -> Bool;
equal_Chara (Chara x1 x2) (Chara y1 y2) =
  equal_Nibble x1 y1 && equal_Nibble x2 y2;

random_Inta ::
  Natural -> (Natural, Natural) -> ((Inta, () -> Term), (Natural, Natural));
random_Inta i = random_aux_Inta i i;

size_Itselfa :: forall a. Itselfa a -> Nat;
size_Itselfa Typea = Zero_nat;

size_Nibblea :: Nibble -> Nat;
size_Nibblea NibbleF = Zero_nat;
size_Nibblea NibbleE = Zero_nat;
size_Nibblea NibbleD = Zero_nat;
size_Nibblea NibbleC = Zero_nat;
size_Nibblea NibbleB = Zero_nat;
size_Nibblea NibbleA = Zero_nat;
size_Nibblea Nibble9 = Zero_nat;
size_Nibblea Nibble8 = Zero_nat;
size_Nibblea Nibble7 = Zero_nat;
size_Nibblea Nibble6 = Zero_nat;
size_Nibblea Nibble5 = Zero_nat;
size_Nibblea Nibble4 = Zero_nat;
size_Nibblea Nibble3 = Zero_nat;
size_Nibblea Nibble2 = Zero_nat;
size_Nibblea Nibble1 = Zero_nat;
size_Nibblea Nibble0 = Zero_nat;

term_of_Nat :: Nata -> Term;
term_of_Nat Zero = Const "Lists.Nat.Zero" (Typerep "Lists.Nat" []);
term_of_Nat (Suca a) =
  App (Const "Lists.Nat.Suc"
        (Typerep "fun" [Typerep "Lists.Nat" [], Typerep "Lists.Nat" []]))
    (term_of_Nat a);

typerep_Nat :: Itself Nata -> Typerepa;
typerep_Nat t = Typerep "Lists.Nat" [];

equal_Itself :: forall a. Itselfa a -> Itselfa a -> Bool;
equal_Itself Typea Typea = True;

random_Chara ::
  Natural -> (Natural, Natural) -> ((Chara, () -> Term), (Natural, Natural));
random_Chara i = random_aux_Chara i i;

term_of_Inta :: Inta -> Term;
term_of_Inta Pls = Const "Lists.Inta.Pls" (Typerep "Lists.Inta" []);
term_of_Inta Min = Const "Lists.Inta.Min" (Typerep "Lists.Inta" []);
term_of_Inta (Bit0a a) =
  App (Const "Lists.Inta.Bit0"
        (Typerep "fun" [Typerep "Lists.Inta" [], Typerep "Lists.Inta" []]))
    (term_of_Inta a);
term_of_Inta (Bit1a a) =
  App (Const "Lists.Inta.Bit1"
        (Typerep "fun" [Typerep "Lists.Inta" [], Typerep "Lists.Inta" []]))
    (term_of_Inta a);
term_of_Inta (Number_of_int a) =
  App (Const "Lists.Inta.Number_of_int"
        (Typerep "fun" [Typerep "Lists.Inta" [], Typerep "Lists.Inta" []]))
    (term_of_Inta a);

typerep_Inta :: Itself Inta -> Typerepa;
typerep_Inta t = Typerep "Lists.Inta" [];

random_Itself ::
  forall a.
    (Typerep a) => Natural ->
                     (Natural, Natural) ->
                       ((Itselfa a, () -> Term), (Natural, Natural));
random_Itself i = random_aux_Itself i i;

term_of_Nibble :: Nibble -> Term;
term_of_Nibble Nibble0 =
  Const "Lists.Nibble.Nibble0" (Typerep "Lists.Nibble" []);
term_of_Nibble Nibble1 =
  Const "Lists.Nibble.Nibble1" (Typerep "Lists.Nibble" []);
term_of_Nibble Nibble2 =
  Const "Lists.Nibble.Nibble2" (Typerep "Lists.Nibble" []);
term_of_Nibble Nibble3 =
  Const "Lists.Nibble.Nibble3" (Typerep "Lists.Nibble" []);
term_of_Nibble Nibble4 =
  Const "Lists.Nibble.Nibble4" (Typerep "Lists.Nibble" []);
term_of_Nibble Nibble5 =
  Const "Lists.Nibble.Nibble5" (Typerep "Lists.Nibble" []);
term_of_Nibble Nibble6 =
  Const "Lists.Nibble.Nibble6" (Typerep "Lists.Nibble" []);
term_of_Nibble Nibble7 =
  Const "Lists.Nibble.Nibble7" (Typerep "Lists.Nibble" []);
term_of_Nibble Nibble8 =
  Const "Lists.Nibble.Nibble8" (Typerep "Lists.Nibble" []);
term_of_Nibble Nibble9 =
  Const "Lists.Nibble.Nibble9" (Typerep "Lists.Nibble" []);
term_of_Nibble NibbleA =
  Const "Lists.Nibble.NibbleA" (Typerep "Lists.Nibble" []);
term_of_Nibble NibbleB =
  Const "Lists.Nibble.NibbleB" (Typerep "Lists.Nibble" []);
term_of_Nibble NibbleC =
  Const "Lists.Nibble.NibbleC" (Typerep "Lists.Nibble" []);
term_of_Nibble NibbleD =
  Const "Lists.Nibble.NibbleD" (Typerep "Lists.Nibble" []);
term_of_Nibble NibbleE =
  Const "Lists.Nibble.NibbleE" (Typerep "Lists.Nibble" []);
term_of_Nibble NibbleF =
  Const "Lists.Nibble.NibbleF" (Typerep "Lists.Nibble" []);

term_of_Chara :: Chara -> Term;
term_of_Chara (Chara a b) =
  App (App (Const "Lists.Chara.Chara"
             (Typerep "fun"
               [Typerep "Lists.Nibble" [],
                 Typerep "fun"
                   [Typerep "Lists.Nibble" [], Typerep "Lists.Chara" []]]))
        (term_of_Nibble a))
    (term_of_Nibble b);

typerep_Chara :: Itself Chara -> Typerepa;
typerep_Chara t = Typerep "Lists.Chara" [];

term_of_Itself :: forall a. (Typerep a) => Itselfa a -> Term;
term_of_Itself Typea =
  Const "Lists.Itself.Type"
    (Typerep "Lists.Itself" [(typerep :: Itself a -> Typerepa) Type]);

typerep_Itself :: forall a. (Typerep a) => Itself (Itselfa a) -> Typerepa;
typerep_Itself t =
  Typerep "Lists.Itself" [(typerep :: Itself a -> Typerepa) Type];

typerep_Nibble :: Itself Nibble -> Typerepa;
typerep_Nibble t = Typerep "Lists.Nibble" [];

one_integer :: Integer;
one_integer = (1 :: Integer);

divmod_step :: forall a. (Semiring_numeral_div a) => Num -> (a, a) -> (a, a);
divmod_step l (q, r) =
  (if less_eqa (numeral l) r
    then (plusa (times (numeral (Bit0 One)) q) one, minus r (numeral l))
    else (times (numeral (Bit0 One)) q, r));

divmod :: forall a. (Semiring_numeral_div a) => Num -> Num -> (a, a);
divmod (Bit1 m) (Bit0 n) =
  let {
    (q, r) = divmod m n;
  } in (q, plusa (times (numeral (Bit0 One)) r) one);
divmod (Bit0 m) (Bit0 n) =
  let {
    (q, r) = divmod m n;
  } in (q, times (numeral (Bit0 One)) r);
divmod m n =
  (if less_num m n then (zeroa, numeral m)
    else divmod_step n (divmod m (Bit0 n)));

narrowing_Itself ::
  forall a. (Typerep a) => Integer -> Narrowing_cons (Itselfa a);
narrowing_Itself = cons Typea;

narrowing_Nibble :: Integer -> Narrowing_cons Nibble;
narrowing_Nibble =
  sum (cons NibbleF)
    (sum (cons NibbleE)
      (sum (cons NibbleD)
        (sum (cons NibbleC)
          (sum (cons NibbleB)
            (sum (cons NibbleA)
              (sum (cons Nibble9)
                (sum (cons Nibble8)
                  (sum (cons Nibble7)
                    (sum (cons Nibble6)
                      (sum (cons Nibble5)
                        (sum (cons Nibble4)
                          (sum (cons Nibble3)
                            (sum (cons Nibble2)
                              (sum (cons Nibble1) (cons Nibble0)))))))))))))));

full_exhaustive_Nat ::
  ((Nata, () -> Term) -> Maybe (Bool, [Term])) ->
    Natural -> Maybe (Bool, [Term]);
full_exhaustive_Nat f i =
  (if less_natural zero_natural i
    then (case full_exhaustive_Nat
                 (\ (uu, uua) ->
                   f (Suca uu,
                       (\ _ ->
                         App (Const "Lists.Nat.Suc"
                               (Typerep "fun"
                                 [Typerep "Lists.Nat" [],
                                   Typerep "Lists.Nat" []]))
                           (uua ()))))
                 (minus_natural i one_natural)
           of {
           Nothing ->
             f (Zero, (\ _ -> Const "Lists.Nat.Zero" (Typerep "Lists.Nat" [])));
           Just a -> Just a;
         })
    else Nothing);

partial_term_of_Nat :: Itself Nata -> Narrowing_term -> Term;
partial_term_of_Nat ty (Narrowing_constructor (1 :: Integer) []) =
  Const "Lists.Nat.Zero" (Typerep "Lists.Nat" []);
partial_term_of_Nat ty (Narrowing_constructor (0 :: Integer) [a]) =
  App (Const "Lists.Nat.Suc"
        (Typerep "fun" [Typerep "Lists.Nat" [], Typerep "Lists.Nat" []]))
    (partial_term_of_Nat Type a);
partial_term_of_Nat ty (Narrowing_variable p tt) =
  Free "_" (Typerep "Lists.Nat" []);

full_exhaustive_Inta ::
  ((Inta, () -> Term) -> Maybe (Bool, [Term])) ->
    Natural -> Maybe (Bool, [Term]);
full_exhaustive_Inta f i =
  (if less_natural zero_natural i
    then (case full_exhaustive_Inta
                 (\ (uu, uua) ->
                   f (Number_of_int uu,
                       (\ _ ->
                         App (Const "Lists.Inta.Number_of_int"
                               (Typerep "fun"
                                 [Typerep "Lists.Inta" [],
                                   Typerep "Lists.Inta" []]))
                           (uua ()))))
                 (minus_natural i one_natural)
           of {
           Nothing ->
             (case full_exhaustive_Inta
                     (\ (uu, uua) ->
                       f (Bit1a uu,
                           (\ _ ->
                             App (Const "Lists.Inta.Bit1"
                                   (Typerep "fun"
                                     [Typerep "Lists.Inta" [],
                                       Typerep "Lists.Inta" []]))
                               (uua ()))))
                     (minus_natural i one_natural)
               of {
               Nothing ->
                 (case full_exhaustive_Inta
                         (\ (uu, uua) ->
                           f (Bit0a uu,
                               (\ _ ->
                                 App (Const "Lists.Inta.Bit0"
                                       (Typerep "fun"
 [Typerep "Lists.Inta" [], Typerep "Lists.Inta" []]))
                                   (uua ()))))
                         (minus_natural i one_natural)
                   of {
                   Nothing ->
                     (case f (Min, (\ _ ->
                                     Const "Lists.Inta.Min"
                                       (Typerep "Lists.Inta" [])))
                       of {
                       Nothing ->
                         f (Pls, (\ _ ->
                                   Const "Lists.Inta.Pls"
                                     (Typerep "Lists.Inta" [])));
                       Just a -> Just a;
                     });
                   Just a -> Just a;
                 });
               Just a -> Just a;
             });
           Just a -> Just a;
         })
    else Nothing);

partial_term_of_Inta :: Itself Inta -> Narrowing_term -> Term;
partial_term_of_Inta ty (Narrowing_constructor (4 :: Integer) []) =
  Const "Lists.Inta.Pls" (Typerep "Lists.Inta" []);
partial_term_of_Inta ty (Narrowing_constructor (3 :: Integer) []) =
  Const "Lists.Inta.Min" (Typerep "Lists.Inta" []);
partial_term_of_Inta ty (Narrowing_constructor (2 :: Integer) [a]) =
  App (Const "Lists.Inta.Bit0"
        (Typerep "fun" [Typerep "Lists.Inta" [], Typerep "Lists.Inta" []]))
    (partial_term_of_Inta Type a);
partial_term_of_Inta ty (Narrowing_constructor (1 :: Integer) [a]) =
  App (Const "Lists.Inta.Bit1"
        (Typerep "fun" [Typerep "Lists.Inta" [], Typerep "Lists.Inta" []]))
    (partial_term_of_Inta Type a);
partial_term_of_Inta ty (Narrowing_constructor (0 :: Integer) [a]) =
  App (Const "Lists.Inta.Number_of_int"
        (Typerep "fun" [Typerep "Lists.Inta" [], Typerep "Lists.Inta" []]))
    (partial_term_of_Inta Type a);
partial_term_of_Inta ty (Narrowing_variable p tt) =
  Free "_" (Typerep "Lists.Inta" []);

full_exhaustive_Nibble ::
  ((Nibble, () -> Term) -> Maybe (Bool, [Term])) ->
    Natural -> Maybe (Bool, [Term]);
full_exhaustive_Nibble f i =
  (if less_natural zero_natural i
    then (case f (NibbleF,
                   (\ _ ->
                     Const "Lists.Nibble.NibbleF" (Typerep "Lists.Nibble" [])))
           of {
           Nothing ->
             (case f (NibbleE,
                       (\ _ ->
                         Const "Lists.Nibble.NibbleE"
                           (Typerep "Lists.Nibble" [])))
               of {
               Nothing ->
                 (case f (NibbleD,
                           (\ _ ->
                             Const "Lists.Nibble.NibbleD"
                               (Typerep "Lists.Nibble" [])))
                   of {
                   Nothing ->
                     (case f (NibbleC,
                               (\ _ ->
                                 Const "Lists.Nibble.NibbleC"
                                   (Typerep "Lists.Nibble" [])))
                       of {
                       Nothing ->
                         (case f (NibbleB,
                                   (\ _ ->
                                     Const "Lists.Nibble.NibbleB"
                                       (Typerep "Lists.Nibble" [])))
                           of {
                           Nothing ->
                             (case f (NibbleA,
                                       (\ _ ->
 Const "Lists.Nibble.NibbleA" (Typerep "Lists.Nibble" [])))
                               of {
                               Nothing ->
                                 (case f
 (Nibble9, (\ _ -> Const "Lists.Nibble.Nibble9" (Typerep "Lists.Nibble" [])))
                                   of {
                                   Nothing ->
                                     (case f
     (Nibble8,
       (\ _ -> Const "Lists.Nibble.Nibble8" (Typerep "Lists.Nibble" [])))
                                       of {
                                       Nothing ->
 (case f (Nibble7,
           (\ _ -> Const "Lists.Nibble.Nibble7" (Typerep "Lists.Nibble" [])))
   of {
   Nothing ->
     (case f (Nibble6,
               (\ _ ->
                 Const "Lists.Nibble.Nibble6" (Typerep "Lists.Nibble" [])))
       of {
       Nothing ->
         (case f (Nibble5,
                   (\ _ ->
                     Const "Lists.Nibble.Nibble5" (Typerep "Lists.Nibble" [])))
           of {
           Nothing ->
             (case f (Nibble4,
                       (\ _ ->
                         Const "Lists.Nibble.Nibble4"
                           (Typerep "Lists.Nibble" [])))
               of {
               Nothing ->
                 (case f (Nibble3,
                           (\ _ ->
                             Const "Lists.Nibble.Nibble3"
                               (Typerep "Lists.Nibble" [])))
                   of {
                   Nothing ->
                     (case f (Nibble2,
                               (\ _ ->
                                 Const "Lists.Nibble.Nibble2"
                                   (Typerep "Lists.Nibble" [])))
                       of {
                       Nothing ->
                         (case f (Nibble1,
                                   (\ _ ->
                                     Const "Lists.Nibble.Nibble1"
                                       (Typerep "Lists.Nibble" [])))
                           of {
                           Nothing ->
                             f (Nibble0,
                                 (\ _ ->
                                   Const "Lists.Nibble.Nibble0"
                                     (Typerep "Lists.Nibble" [])));
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
                       App (App (Const "Lists.Chara.Chara"
                                  (Typerep "fun"
                                    [Typerep "Lists.Nibble" [],
                                      Typerep "fun"
[Typerep "Lists.Nibble" [], Typerep "Lists.Chara" []]]))
                             (uua ()))
                         (uuc ()))))
               (minus_natural i one_natural))
           (minus_natural i one_natural)
    else Nothing);

partial_term_of_Nibble :: Itself Nibble -> Narrowing_term -> Term;
partial_term_of_Nibble ty (Narrowing_constructor (15 :: Integer) []) =
  Const "Lists.Nibble.Nibble0" (Typerep "Lists.Nibble" []);
partial_term_of_Nibble ty (Narrowing_constructor (14 :: Integer) []) =
  Const "Lists.Nibble.Nibble1" (Typerep "Lists.Nibble" []);
partial_term_of_Nibble ty (Narrowing_constructor (13 :: Integer) []) =
  Const "Lists.Nibble.Nibble2" (Typerep "Lists.Nibble" []);
partial_term_of_Nibble ty (Narrowing_constructor (12 :: Integer) []) =
  Const "Lists.Nibble.Nibble3" (Typerep "Lists.Nibble" []);
partial_term_of_Nibble ty (Narrowing_constructor (11 :: Integer) []) =
  Const "Lists.Nibble.Nibble4" (Typerep "Lists.Nibble" []);
partial_term_of_Nibble ty (Narrowing_constructor (10 :: Integer) []) =
  Const "Lists.Nibble.Nibble5" (Typerep "Lists.Nibble" []);
partial_term_of_Nibble ty (Narrowing_constructor (9 :: Integer) []) =
  Const "Lists.Nibble.Nibble6" (Typerep "Lists.Nibble" []);
partial_term_of_Nibble ty (Narrowing_constructor (8 :: Integer) []) =
  Const "Lists.Nibble.Nibble7" (Typerep "Lists.Nibble" []);
partial_term_of_Nibble ty (Narrowing_constructor (7 :: Integer) []) =
  Const "Lists.Nibble.Nibble8" (Typerep "Lists.Nibble" []);
partial_term_of_Nibble ty (Narrowing_constructor (6 :: Integer) []) =
  Const "Lists.Nibble.Nibble9" (Typerep "Lists.Nibble" []);
partial_term_of_Nibble ty (Narrowing_constructor (5 :: Integer) []) =
  Const "Lists.Nibble.NibbleA" (Typerep "Lists.Nibble" []);
partial_term_of_Nibble ty (Narrowing_constructor (4 :: Integer) []) =
  Const "Lists.Nibble.NibbleB" (Typerep "Lists.Nibble" []);
partial_term_of_Nibble ty (Narrowing_constructor (3 :: Integer) []) =
  Const "Lists.Nibble.NibbleC" (Typerep "Lists.Nibble" []);
partial_term_of_Nibble ty (Narrowing_constructor (2 :: Integer) []) =
  Const "Lists.Nibble.NibbleD" (Typerep "Lists.Nibble" []);
partial_term_of_Nibble ty (Narrowing_constructor (1 :: Integer) []) =
  Const "Lists.Nibble.NibbleE" (Typerep "Lists.Nibble" []);
partial_term_of_Nibble ty (Narrowing_constructor (0 :: Integer) []) =
  Const "Lists.Nibble.NibbleF" (Typerep "Lists.Nibble" []);
partial_term_of_Nibble ty (Narrowing_variable p tt) =
  Free "_" (Typerep "Lists.Nibble" []);

partial_term_of_Chara :: Itself Chara -> Narrowing_term -> Term;
partial_term_of_Chara ty (Narrowing_constructor (0 :: Integer) [b, a]) =
  App (App (Const "Lists.Chara.Chara"
             (Typerep "fun"
               [Typerep "Lists.Nibble" [],
                 Typerep "fun"
                   [Typerep "Lists.Nibble" [], Typerep "Lists.Chara" []]]))
        (partial_term_of_Nibble Type a))
    (partial_term_of_Nibble Type b);
partial_term_of_Chara ty (Narrowing_variable p tt) =
  Free "_" (Typerep "Lists.Chara" []);

typerep_Nat_IITN_Nat :: Itself Nat_IITN_Nat -> Typerepa;
typerep_Nat_IITN_Nat t = Typerep "Lists.Nat.Nat_IITN_Nat" [];

full_exhaustive_Itself ::
  forall a.
    (Typerep a) => ((Itselfa a, () -> Term) -> Maybe (Bool, [Term])) ->
                     Natural -> Maybe (Bool, [Term]);
full_exhaustive_Itself f i =
  (if less_natural zero_natural i
    then f (Typea,
             (\ _ ->
               Const "Lists.Itself.Type"
                 (Typerep "Lists.Itself"
                   [(typerep :: Itself a -> Typerepa) Type])))
    else Nothing);

partial_term_of_Itself ::
  forall a. (Typerep a) => Itself (Itselfa a) -> Narrowing_term -> Term;
partial_term_of_Itself ty (Narrowing_constructor (0 :: Integer) []) =
  Const "Lists.Itself.Type"
    (Typerep "Lists.Itself" [(typerep :: Itself a -> Typerepa) Type]);
partial_term_of_Itself ty (Narrowing_variable p tt) =
  Free "_" (Typerep "Lists.Itself" [(typerep :: Itself a -> Typerepa) Type]);

typerep_Inta_pre_Inta ::
  forall a. (Typerep a) => Itself (Inta_pre_Inta a) -> Typerepa;
typerep_Inta_pre_Inta t =
  Typerep "Lists.Inta.Inta_pre_Inta" [(typerep :: Itself a -> Typerepa) Type];

typerep_Inta_IITN_Inta :: Itself Inta_IITN_Inta -> Typerepa;
typerep_Inta_IITN_Inta t = Typerep "Lists.Inta.Inta_IITN_Inta" [];

typerep_Chara_IITN_Chara :: Itself Chara_IITN_Chara -> Typerepa;
typerep_Chara_IITN_Chara t = Typerep "Lists.Chara.Chara_IITN_Chara" [];

typerep_Itself_pre_Itself ::
  forall a b.
    (Typerep a, Typerep b) => Itself (Itself_pre_Itself a b) -> Typerepa;
typerep_Itself_pre_Itself t =
  Typerep "Lists.Itself.Itself_pre_Itself"
    [(typerep :: Itself a -> Typerepa) Type,
      (typerep :: Itself b -> Typerepa) Type];

typerep_Nibble_pre_Nibble :: Itself Nibble_pre_Nibble -> Typerepa;
typerep_Nibble_pre_Nibble t = Typerep "Lists.Nibble.Nibble_pre_Nibble" [];

typerep_Itself_IITN_Itself ::
  forall a. (Typerep a) => Itself (Itself_IITN_Itself a) -> Typerepa;
typerep_Itself_IITN_Itself t =
  Typerep "Lists.Itself.Itself_IITN_Itself"
    [(typerep :: Itself a -> Typerepa) Type];

typerep_Nibble_IITN_Nibble :: Itself Nibble_IITN_Nibble -> Typerepa;
typerep_Nibble_IITN_Nibble t = Typerep "Lists.Nibble.Nibble_IITN_Nibble" [];

}
