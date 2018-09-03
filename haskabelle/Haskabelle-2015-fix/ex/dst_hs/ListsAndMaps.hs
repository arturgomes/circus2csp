{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  ListsAndMaps(Ord(..), Natural(..), integer_of_natural, plus_natural, Plus(..),
                zero_natural, Zero(..), Monoid_add, Times(..), Div(..), One(..),
                Numeral, Minus(..), Orda(..), Linordera, Plusa(..), Zeroa(..),
                Monoid_adda, Semiring_numeral_div, Finite_intvl_succ(..),
                Eqa(..), Typerepa(..), Itself(..), Typerep(..), Nat(..),
                Num(..), Set(..), Nibble(..), Char(..), Nata(..), Inta(..),
                Nibblea(..), Chara(..), Itselfa(..), Term(..), Nat_IITN_Nat,
                Inta_pre_Inta, Inta_IITN_Inta, Chara_IITN_Chara,
                Narrowing_type(..), Narrowing_term(..), Narrowing_cons(..),
                Itself_pre_Itself, Nibble_pre_Nibble, Itself_IITN_Itself,
                Nibble_IITN_Nibble, bitM, ball, foldr, less_eq_natural,
                less_natural, one_natural, sgn_integer, abs_integer, apsnd,
                divmod_integer, div_integer, div_natural, log, times_natural,
                mod_integer, mod_natural, max, natural_of_integer,
                minus_natural, minus_shift, next, pick, scomp, equal_natural,
                iterate, range, hd, tl, nth, foldla, rev, eqop, leta, mapa,
                insort, sort, zipa, dropa, nulla, lasta, preda, split, succa,
                takea, append, foldra, map_of, member, rotate1, fun_pow, rotate,
                sorted, splice, butlast, concata, filtera, list_ex, listsum,
                map_add, remdups, remove1, listsuma, select_weight, char_rec,
                distinct, less_nat, less_eq_nat, list_all, list_rec, map_comp,
                map_upds, nat_case, plus_int, plus_nat, valapp, char_case,
                char_size, filtermap, list_all2, list_case, list_size,
                partition, size_char, size_list, dropWhilea, list_inter,
                map_filter, replicatea, takeWhilea, rec_Nat, itself_char,
                itself_list, list_update, option_case, bot_set, set_Itself,
                pred_Itself, sum, plus_nata, size_Nat, numeral, less_num,
                less_eq_num, cons, rec_Inta, itself_nibble, successor_int,
                plus_num, collapse, size_Inta, random_aux_Nat, rec_Chara,
                random_aux_Inta, equal_num, times_num, size_Chara,
                random_aux_Nibble, random_Nibble, random_aux_Chara, map_Itself,
                rec_Itself, rel_Itself, rec_Nibble, random_aux_Itself,
                non_empty, size_Itself, size_Nibble, size_Nata, equal_Nat,
                size_Intaa, equal_Inta, random_Nat, size_Charaa, one_integer,
                divmod_step, divmod, equal_Nibble, equal_Chara, random_Inta,
                size_Itselfa, size_Nibblea, term_of_Nat, typerep_Nat,
                equal_Itself, random_Chara, term_of_Inta, typerep_Inta,
                random_Itself, term_of_Nibble, term_of_Chara, typerep_Chara,
                term_of_Itself, typerep_Itself, typerep_Nibble,
                narrowing_Itself, narrowing_Nibble, full_exhaustive_Nat,
                partial_term_of_Nat, full_exhaustive_Inta, partial_term_of_Inta,
                full_exhaustive_Nibble, full_exhaustive_Chara,
                partial_term_of_Nibble, partial_term_of_Chara,
                typerep_Nat_IITN_Nat, full_exhaustive_Itself,
                partial_term_of_Itself, typerep_Inta_pre_Inta,
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

class Orda a where {
  less_eqa :: a -> a -> Bool;
  lessa :: a -> a -> Bool;
};

class (Orda a) => Ordera a where {
};

class (Order a) => Linorder a where {
};

class (Semiring_1 a) => Semiring_char_0 a where {
};

class (Div a, Semidom a) => Semiring_div a where {
};

class (Ordera a) => Linordera a where {
};

class (Comm_semiring_1_diff_distrib a) => Semiring_parity a where {
};

class (Ab_semigroup_add a, Order a) => Ordered_ab_semigroup_add a where {
};

class (Comm_monoid_add a, Ordered_ab_semigroup_add a,
        Semiring a) => Ordered_semiring a where {
};

class Plusa a where {
  plusa :: a -> a -> a;
};

class (Plusa a) => Semigroup_adda a where {
};

class Zeroa a where {
  zeroa :: a;
};

class (Semigroup_adda a, Zeroa a) => Monoid_adda a where {
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

class (Linordera a) => Finite_intvl_succ a where {
  successor :: a -> a;
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

data Nibble = Nibble0 | Nibble1 | Nibble2 | Nibble3 | Nibble4 | Nibble5
  | Nibble6 | Nibble7 | Nibble8 | Nibble9 | NibbleA | NibbleB | NibbleC
  | NibbleD | NibbleE | NibbleF;

data Char = Char Nibble Nibble;

data Nata = Suca Nata | Zero;

data Inta = Number_of_int Inta | Bit1a Inta | Bit0a Inta | Min | Pls;

data Nibblea = NibbleFa | NibbleEa | NibbleDa | NibbleCa | NibbleBa | NibbleAa
  | Nibble9a | Nibble8a | Nibble7a | Nibble6a | Nibble5a | Nibble4a | Nibble3a
  | Nibble2a | Nibble1a | Nibble0a;

data Chara = Chara Nibblea Nibblea;

data Itselfa a = Typea;

data Term = Const String Typerepa | App Term Term | Abs String Typerepa Term
  | Free String Typerepa;

data Nat_IITN_Nat;

data Inta_pre_Inta a;

data Inta_IITN_Inta;

data Chara_IITN_Chara;

newtype Narrowing_type = Narrowing_sum_of_products [[Narrowing_type]];

data Narrowing_term = Narrowing_variable [Integer] Narrowing_type
  | Narrowing_constructor Integer [Narrowing_term];

data Narrowing_cons a = Narrowing_cons Narrowing_type [[Narrowing_term] -> a];

data Itself_pre_Itself a b;

data Nibble_pre_Nibble;

data Itself_IITN_Itself a;

data Nibble_IITN_Nibble;

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

hd :: forall a. [a] -> a;
hd (x : xs) = x;

tl :: forall a. [a] -> [a];
tl (x : xs) = xs;
tl [] = [];

nth :: forall a. [a] -> Nata -> a;
nth (x : xs) n = (case n of {
                   Suca a -> nth xs a;
                   Zero -> x;
                 });

foldla :: forall a b. (a -> b -> a) -> a -> [b] -> a;
foldla f a (x : xs) = foldla f (f a x) xs;
foldla f a [] = a;

rev :: forall a. [a] -> [a];
rev xs = foldla (\ xsa x -> x : xsa) [] xs;

eqop :: forall a. (Eqa a) => a -> a -> Bool;
eqop a = eq a;

leta :: forall a b. a -> (a -> b) -> b;
leta s f = f s;

mapa :: forall a b. (a -> b) -> [a] -> [b];
mapa f (x : xs) = f x : mapa f xs;
mapa f [] = [];

insort :: forall a. (Linordera a) => a -> [a] -> [a];
insort x (y : ys) = (if less_eqa x y then x : y : ys else y : insort x ys);
insort x [] = [x];

sort :: forall a. (Linordera a) => [a] -> [a];
sort (x : xs) = insort x (sort xs);
sort [] = [];

zipa :: forall a b. [a] -> [b] -> [(a, b)];
zipa xs (y : ys) = (case xs of {
                     [] -> [];
                     z : zs -> (z, y) : zipa zs ys;
                   });
zipa xs [] = [];

dropa :: forall a. Nata -> [a] -> [a];
dropa n (x : xs) = (case n of {
                     Suca m -> dropa m xs;
                     Zero -> x : xs;
                   });
dropa n [] = [];

nulla :: forall a. [a] -> Bool;
nulla (x : xs) = False;
nulla [] = True;

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
takea n (x : xs) = (case n of {
                     Suca m -> x : takea m xs;
                     Zero -> [];
                   });
takea n [] = [];

append :: forall a. [a] -> [a] -> [a];
append (x : xs) ys = x : append xs ys;
append [] ys = ys;

foldra :: forall a b. (a -> b -> b) -> [a] -> b -> b;
foldra f (x : xs) a = f x (foldra f xs a);
foldra f [] a = a;

map_of :: forall a b. (Eqa a) => [(a, b)] -> a -> Maybe b;
map_of ((l, v) : ps) k = (if eqop l k then Just v else map_of ps k);
map_of [] k = Nothing;

member :: forall a. (Eqa a) => a -> [a] -> Bool;
member x (y : ys) = (if eqop y x then True else member x ys);
member x [] = False;

rotate1 :: forall a. [a] -> [a];
rotate1 xs = (case xs of {
               [] -> [];
               x : xsa -> append xsa [x];
             });

fun_pow :: forall a. Nata -> (a -> a) -> a -> a;
fun_pow (Suca n) f = f . fun_pow n f;
fun_pow Zero f = id;

rotate :: forall a. Nata -> [a] -> [a];
rotate n = fun_pow n rotate1;

sorted :: forall a. (Linordera a) => [a] -> Bool;
sorted (x : y : zs) = less_eqa x y && sorted (y : zs);
sorted [x] = True;
sorted [] = True;

splice :: forall a. [a] -> [a] -> [a];
splice (x : xs) (y : ys) = x : y : splice xs ys;
splice xs [] = xs;
splice [] (v : va) = v : va;

butlast :: forall a. [a] -> [a];
butlast (x : xs) = (if nulla xs then [] else x : butlast xs);
butlast [] = [];

concata :: forall a. [[a]] -> [a];
concata (x : xs) = append x (concata xs);
concata [] = [];

filtera :: forall a. (a -> Bool) -> [a] -> [a];
filtera p (x : xs) = (if p x then x : filtera p xs else filtera p xs);
filtera p [] = [];

list_ex :: forall a. (a -> Bool) -> [a] -> Bool;
list_ex p (x : xs) = p x || list_ex p xs;
list_ex p [] = False;

listsum :: forall a. (Monoid_adda a) => [a] -> a;
listsum (x : xs) = plusa x (foldla plusa zeroa xs);
listsum [] = zeroa;

map_add :: forall a b. (a -> Maybe b) -> (a -> Maybe b) -> a -> Maybe b;
map_add m1 m2 = (\ x -> (case m2 x of {
                          Nothing -> m1 x;
                          Just a -> Just a;
                        }));

remdups :: forall a. (Eqa a) => [a] -> [a];
remdups (x : xs) = (if member x xs then remdups xs else x : remdups xs);
remdups [] = [];

remove1 :: forall a. (Eqa a) => a -> [a] -> [a];
remove1 x (y : xs) = (if eqop x y then xs else y : remove1 x xs);
remove1 x [] = [];

listsuma :: forall a. (Monoid_add a) => [a] -> a;
listsuma xs = foldr plus xs zero;

select_weight ::
  forall a. [(Natural, a)] -> (Natural, Natural) -> (a, (Natural, Natural));
select_weight xs =
  scomp (range (listsuma (map fst xs))) (\ k -> (\ a -> (pick xs k, a)));

char_rec :: forall a. (Nibblea -> Nibblea -> a) -> Chara -> a;
char_rec f1 (Chara nibble1 nibble2) = f1 nibble1 nibble2;

distinct :: forall a. (Eqa a) => [a] -> Bool;
distinct (x : xs) = not (member x xs) && distinct xs;
distinct [] = True;

less_nat :: Nata -> Nata -> Bool;
less_nat m (Suca n) = less_eq_nat m n;
less_nat n Zero = False;

less_eq_nat :: Nata -> Nata -> Bool;
less_eq_nat (Suca m) n = less_nat m n;
less_eq_nat Zero n = True;

list_all :: forall a. (a -> Bool) -> [a] -> Bool;
list_all p (x : xs) = p x && list_all p xs;
list_all p [] = True;

list_rec :: forall a b. a -> (b -> [b] -> a -> a) -> [b] -> a;
list_rec f1 f2 (a : list) = f2 a list (list_rec f1 f2 list);
list_rec f1 f2 [] = f1;

map_comp :: forall a b c. (a -> Maybe b) -> (c -> Maybe a) -> c -> Maybe b;
map_comp f g = (\ k -> (case g k of {
                         Nothing -> Nothing;
                         Just a -> f a;
                       }));

map_upds :: forall a b. (Eqa a) => (a -> Maybe b) -> [a] -> [b] -> a -> Maybe b;
map_upds m xs ys = map_add m (map_of (rev (zipa xs ys)));

nat_case :: forall a. a -> (Nata -> a) -> Nata -> a;
nat_case f1 f2 Zero = f1;
nat_case f1 f2 (Suca nat0) = f2 nat0;

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

valapp ::
  forall a b. (a -> b, () -> Term) -> (a, () -> Term) -> (b, () -> Term);
valapp (f, tf) (x, tx) = (f x, (\ _ -> App (tf ()) (tx ())));

char_case :: forall a. (Nibblea -> Nibblea -> a) -> Chara -> a;
char_case f1 (Chara nibble1 nibble2) = f1 nibble1 nibble2;

char_size :: Chara -> Nata;
char_size (Chara nibble1 nibble2) = Zero;

filtermap :: forall a b. (a -> Maybe b) -> [a] -> [b];
filtermap f (x : xs) =
  (case f x of {
    Nothing -> filtermap f xs;
    Just y -> y : filtermap f xs;
  });
filtermap f [] = [];

list_all2 :: forall a b. (a -> b -> Bool) -> [a] -> [b] -> Bool;
list_all2 p (x : xs) (y : ys) = p x y && list_all2 p xs ys;
list_all2 p xs [] = nulla xs;
list_all2 p [] (v : va) = nulla (v : va);

list_case :: forall a b. a -> (b -> [b] -> a) -> [b] -> a;
list_case f1 f2 [] = f1;
list_case f1 f2 (a : list) = f2 a list;

list_size :: forall a. (a -> Nata) -> [a] -> Nata;
list_size fa (a : list) =
  plus_nat (plus_nat (fa a) (list_size fa list)) (Suca Zero);
list_size fa [] = Zero;

partition :: forall a. (a -> Bool) -> [a] -> ([a], [a]);
partition p (x : xs) =
  let {
    (yes, no) = partition p xs;
  } in (if p x then (x : yes, no) else (yes, x : no));
partition p [] = ([], []);

size_char :: Chara -> Nata;
size_char (Chara nibble1 nibble2) = Zero;

size_list :: forall a. [a] -> Nata;
size_list (a : list) = plus_nat (size_list list) (Suca Zero);
size_list [] = Zero;

dropWhilea :: forall a. (a -> Bool) -> [a] -> [a];
dropWhilea p (x : xs) = (if p x then dropWhilea p xs else x : xs);
dropWhilea p [] = [];

list_inter :: forall a. (Eqa a) => [a] -> [a] -> [a];
list_inter (a : asa) bs =
  (if member a bs then a : list_inter asa bs else list_inter asa bs);
list_inter [] bs = [];

map_filter :: forall a b. (a -> b) -> (a -> Bool) -> [a] -> [b];
map_filter f p (x : xs) =
  (if p x then f x : map_filter f p xs else map_filter f p xs);
map_filter f p [] = [];

replicatea :: forall a. Nata -> a -> [a];
replicatea (Suca n) x = x : replicatea n x;
replicatea Zero x = [];

takeWhilea :: forall a. (a -> Bool) -> [a] -> [a];
takeWhilea p (x : xs) = (if p x then x : takeWhilea p xs else []);
takeWhilea p [] = [];

rec_Nat :: forall a. (Nata -> a -> a) -> a -> Nata -> a;
rec_Nat f1 f2 (Suca x1) = f1 x1 (rec_Nat f1 f2 x1);
rec_Nat f1 f2 Zero = f2;

itself_char :: Itselfa Chara;
itself_char = Typea;

itself_list :: forall a. Itselfa [a];
itself_list = Typea;

list_update :: forall a. [a] -> Nata -> a -> [a];
list_update (x : xs) i v =
  (case i of {
    Suca j -> x : list_update xs j v;
    Zero -> v : xs;
  });
list_update [] i v = [];

option_case :: forall a b. a -> (b -> a) -> Maybe b -> a;
option_case f1 f2 Nothing = f1;
option_case f1 f2 (Just a) = f2 a;

bot_set :: forall a. Set a;
bot_set = Set [];

set_Itself :: forall a. Itselfa a -> Set a;
set_Itself Typea = bot_set;

pred_Itself :: forall a. (a -> Bool) -> Itselfa a -> Bool;
pred_Itself p = (\ x -> ball (set_Itself x) p);

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
size_Nat (Suca x1) = plus_nata (size_Nat x1) (Suc Zero_nat);
size_Nat Zero = Zero_nat;

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

rec_Inta ::
  forall a.
    (Inta -> a -> a) ->
      (Inta -> a -> a) -> (Inta -> a -> a) -> a -> a -> Inta -> a;
rec_Inta f1 f2 f3 f4 f5 (Number_of_int x1) = f1 x1 (rec_Inta f1 f2 f3 f4 f5 x1);
rec_Inta f1 f2 f3 f4 f5 (Bit1a x2) = f2 x2 (rec_Inta f1 f2 f3 f4 f5 x2);
rec_Inta f1 f2 f3 f4 f5 (Bit0a x3) = f3 x3 (rec_Inta f1 f2 f3 f4 f5 x3);
rec_Inta f1 f2 f3 f4 f5 Min = f4;
rec_Inta f1 f2 f3 f4 f5 Pls = f5;

itself_nibble :: Itselfa Nibblea;
itself_nibble = Typea;

successor_int :: Inta -> Inta;
successor_int = (\ i -> plus_int i (Number_of_int (Bit1a Pls)));

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

size_Inta :: Inta -> Nat;
size_Inta (Number_of_int x1) = plus_nata (size_Inta x1) (Suc Zero_nat);
size_Inta (Bit1a x2) = plus_nata (size_Inta x2) (Suc Zero_nat);
size_Inta (Bit0a x3) = plus_nata (size_Inta x3) (Suc Zero_nat);
size_Inta Min = Zero_nat;
size_Inta Pls = Zero_nat;

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
                        Const "ListsAndMaps.Nat.Suc"
                          (Typerep "fun"
                            [Typerep "ListsAndMaps.Nat" [],
                              Typerep "ListsAndMaps.Nat" []])))
                    x,
                   a)))),
        (one_natural,
          (\ a ->
            ((Zero,
               (\ _ ->
                 Const "ListsAndMaps.Nat.Zero"
                   (Typerep "ListsAndMaps.Nat" []))),
              a)))])
    s;

rec_Chara :: forall a. (Nibblea -> Nibblea -> a) -> Chara -> a;
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
                        Const "ListsAndMaps.Inta.Number_of_int"
                          (Typerep "fun"
                            [Typerep "ListsAndMaps.Inta" [],
                              Typerep "ListsAndMaps.Inta" []])))
                    x,
                   a)))),
        (i, scomp (random_aux_Inta (minus_natural i one_natural) j)
              (\ x ->
                (\ a ->
                  (valapp
                     (Bit1a,
                       (\ _ ->
                         Const "ListsAndMaps.Inta.Bit1"
                           (Typerep "fun"
                             [Typerep "ListsAndMaps.Inta" [],
                               Typerep "ListsAndMaps.Inta" []])))
                     x,
                    a)))),
        (i, scomp (random_aux_Inta (minus_natural i one_natural) j)
              (\ x ->
                (\ a ->
                  (valapp
                     (Bit0a,
                       (\ _ ->
                         Const "ListsAndMaps.Inta.Bit0"
                           (Typerep "fun"
                             [Typerep "ListsAndMaps.Inta" [],
                               Typerep "ListsAndMaps.Inta" []])))
                     x,
                    a)))),
        (one_natural,
          (\ a ->
            ((Min, (\ _ ->
                     Const "ListsAndMaps.Inta.Min"
                       (Typerep "ListsAndMaps.Inta" []))),
              a))),
        (one_natural,
          (\ a ->
            ((Pls, (\ _ ->
                     Const "ListsAndMaps.Inta.Pls"
                       (Typerep "ListsAndMaps.Inta" []))),
              a)))])
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

size_Chara :: Chara -> Nat;
size_Chara (Chara x1 x2) = Zero_nat;

random_aux_Nibble ::
  Natural ->
    Natural ->
      (Natural, Natural) -> ((Nibblea, () -> Term), (Natural, Natural));
random_aux_Nibble i j s =
  collapse
    (select_weight
      [(one_natural,
         (\ a ->
           ((NibbleFa,
              (\ _ ->
                Const "ListsAndMaps.Nibble.NibbleF"
                  (Typerep "ListsAndMaps.Nibble" []))),
             a))),
        (one_natural,
          (\ a ->
            ((NibbleEa,
               (\ _ ->
                 Const "ListsAndMaps.Nibble.NibbleE"
                   (Typerep "ListsAndMaps.Nibble" []))),
              a))),
        (one_natural,
          (\ a ->
            ((NibbleDa,
               (\ _ ->
                 Const "ListsAndMaps.Nibble.NibbleD"
                   (Typerep "ListsAndMaps.Nibble" []))),
              a))),
        (one_natural,
          (\ a ->
            ((NibbleCa,
               (\ _ ->
                 Const "ListsAndMaps.Nibble.NibbleC"
                   (Typerep "ListsAndMaps.Nibble" []))),
              a))),
        (one_natural,
          (\ a ->
            ((NibbleBa,
               (\ _ ->
                 Const "ListsAndMaps.Nibble.NibbleB"
                   (Typerep "ListsAndMaps.Nibble" []))),
              a))),
        (one_natural,
          (\ a ->
            ((NibbleAa,
               (\ _ ->
                 Const "ListsAndMaps.Nibble.NibbleA"
                   (Typerep "ListsAndMaps.Nibble" []))),
              a))),
        (one_natural,
          (\ a ->
            ((Nibble9a,
               (\ _ ->
                 Const "ListsAndMaps.Nibble.Nibble9"
                   (Typerep "ListsAndMaps.Nibble" []))),
              a))),
        (one_natural,
          (\ a ->
            ((Nibble8a,
               (\ _ ->
                 Const "ListsAndMaps.Nibble.Nibble8"
                   (Typerep "ListsAndMaps.Nibble" []))),
              a))),
        (one_natural,
          (\ a ->
            ((Nibble7a,
               (\ _ ->
                 Const "ListsAndMaps.Nibble.Nibble7"
                   (Typerep "ListsAndMaps.Nibble" []))),
              a))),
        (one_natural,
          (\ a ->
            ((Nibble6a,
               (\ _ ->
                 Const "ListsAndMaps.Nibble.Nibble6"
                   (Typerep "ListsAndMaps.Nibble" []))),
              a))),
        (one_natural,
          (\ a ->
            ((Nibble5a,
               (\ _ ->
                 Const "ListsAndMaps.Nibble.Nibble5"
                   (Typerep "ListsAndMaps.Nibble" []))),
              a))),
        (one_natural,
          (\ a ->
            ((Nibble4a,
               (\ _ ->
                 Const "ListsAndMaps.Nibble.Nibble4"
                   (Typerep "ListsAndMaps.Nibble" []))),
              a))),
        (one_natural,
          (\ a ->
            ((Nibble3a,
               (\ _ ->
                 Const "ListsAndMaps.Nibble.Nibble3"
                   (Typerep "ListsAndMaps.Nibble" []))),
              a))),
        (one_natural,
          (\ a ->
            ((Nibble2a,
               (\ _ ->
                 Const "ListsAndMaps.Nibble.Nibble2"
                   (Typerep "ListsAndMaps.Nibble" []))),
              a))),
        (one_natural,
          (\ a ->
            ((Nibble1a,
               (\ _ ->
                 Const "ListsAndMaps.Nibble.Nibble1"
                   (Typerep "ListsAndMaps.Nibble" []))),
              a))),
        (one_natural,
          (\ a ->
            ((Nibble0a,
               (\ _ ->
                 Const "ListsAndMaps.Nibble.Nibble0"
                   (Typerep "ListsAndMaps.Nibble" []))),
              a)))])
    s;

random_Nibble ::
  Natural -> (Natural, Natural) -> ((Nibblea, () -> Term), (Natural, Natural));
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
                            Const "ListsAndMaps.Chara.Chara"
                              (Typerep "fun"
                                [Typerep "ListsAndMaps.Nibble" [],
                                  Typerep "fun"
                                    [Typerep "ListsAndMaps.Nibble" [],
                                      Typerep "ListsAndMaps.Chara" []]])))
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
 a -> a -> a -> a -> a -> a -> a -> a -> Nibblea -> a;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 NibbleFa = f1;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 NibbleEa = f2;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 NibbleDa = f3;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 NibbleCa = f4;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 NibbleBa = f5;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 NibbleAa = f6;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble9a = f7;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble8a = f8;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble7a = f9;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble6a =
  f10;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble5a =
  f11;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble4a =
  f12;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble3a =
  f13;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble2a =
  f14;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble1a =
  f15;
rec_Nibble f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 Nibble0a =
  f16;

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
                Const "ListsAndMaps.Itself.Type"
                  (Typerep "ListsAndMaps.Itself"
                    [(typerep :: Itself a -> Typerepa) Type]))),
             a)))])
    s;

non_empty :: Narrowing_type -> Bool;
non_empty (Narrowing_sum_of_products ps) = not (null ps);

size_Itself :: forall a. (a -> Nat) -> Itselfa a -> Nat;
size_Itself x Typea = Zero_nat;

size_Nibble :: Nibblea -> Nat;
size_Nibble NibbleFa = Zero_nat;
size_Nibble NibbleEa = Zero_nat;
size_Nibble NibbleDa = Zero_nat;
size_Nibble NibbleCa = Zero_nat;
size_Nibble NibbleBa = Zero_nat;
size_Nibble NibbleAa = Zero_nat;
size_Nibble Nibble9a = Zero_nat;
size_Nibble Nibble8a = Zero_nat;
size_Nibble Nibble7a = Zero_nat;
size_Nibble Nibble6a = Zero_nat;
size_Nibble Nibble5a = Zero_nat;
size_Nibble Nibble4a = Zero_nat;
size_Nibble Nibble3a = Zero_nat;
size_Nibble Nibble2a = Zero_nat;
size_Nibble Nibble1a = Zero_nat;
size_Nibble Nibble0a = Zero_nat;

size_Nata :: Nata -> Nat;
size_Nata (Suca x1) = plus_nata (size_Nata x1) (Suc Zero_nat);
size_Nata Zero = Zero_nat;

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

equal_Nibble :: Nibblea -> Nibblea -> Bool;
equal_Nibble Nibble1a Nibble0a = False;
equal_Nibble Nibble0a Nibble1a = False;
equal_Nibble Nibble2a Nibble0a = False;
equal_Nibble Nibble0a Nibble2a = False;
equal_Nibble Nibble2a Nibble1a = False;
equal_Nibble Nibble1a Nibble2a = False;
equal_Nibble Nibble3a Nibble0a = False;
equal_Nibble Nibble0a Nibble3a = False;
equal_Nibble Nibble3a Nibble1a = False;
equal_Nibble Nibble1a Nibble3a = False;
equal_Nibble Nibble3a Nibble2a = False;
equal_Nibble Nibble2a Nibble3a = False;
equal_Nibble Nibble4a Nibble0a = False;
equal_Nibble Nibble0a Nibble4a = False;
equal_Nibble Nibble4a Nibble1a = False;
equal_Nibble Nibble1a Nibble4a = False;
equal_Nibble Nibble4a Nibble2a = False;
equal_Nibble Nibble2a Nibble4a = False;
equal_Nibble Nibble4a Nibble3a = False;
equal_Nibble Nibble3a Nibble4a = False;
equal_Nibble Nibble5a Nibble0a = False;
equal_Nibble Nibble0a Nibble5a = False;
equal_Nibble Nibble5a Nibble1a = False;
equal_Nibble Nibble1a Nibble5a = False;
equal_Nibble Nibble5a Nibble2a = False;
equal_Nibble Nibble2a Nibble5a = False;
equal_Nibble Nibble5a Nibble3a = False;
equal_Nibble Nibble3a Nibble5a = False;
equal_Nibble Nibble5a Nibble4a = False;
equal_Nibble Nibble4a Nibble5a = False;
equal_Nibble Nibble6a Nibble0a = False;
equal_Nibble Nibble0a Nibble6a = False;
equal_Nibble Nibble6a Nibble1a = False;
equal_Nibble Nibble1a Nibble6a = False;
equal_Nibble Nibble6a Nibble2a = False;
equal_Nibble Nibble2a Nibble6a = False;
equal_Nibble Nibble6a Nibble3a = False;
equal_Nibble Nibble3a Nibble6a = False;
equal_Nibble Nibble6a Nibble4a = False;
equal_Nibble Nibble4a Nibble6a = False;
equal_Nibble Nibble6a Nibble5a = False;
equal_Nibble Nibble5a Nibble6a = False;
equal_Nibble Nibble7a Nibble0a = False;
equal_Nibble Nibble0a Nibble7a = False;
equal_Nibble Nibble7a Nibble1a = False;
equal_Nibble Nibble1a Nibble7a = False;
equal_Nibble Nibble7a Nibble2a = False;
equal_Nibble Nibble2a Nibble7a = False;
equal_Nibble Nibble7a Nibble3a = False;
equal_Nibble Nibble3a Nibble7a = False;
equal_Nibble Nibble7a Nibble4a = False;
equal_Nibble Nibble4a Nibble7a = False;
equal_Nibble Nibble7a Nibble5a = False;
equal_Nibble Nibble5a Nibble7a = False;
equal_Nibble Nibble7a Nibble6a = False;
equal_Nibble Nibble6a Nibble7a = False;
equal_Nibble Nibble8a Nibble0a = False;
equal_Nibble Nibble0a Nibble8a = False;
equal_Nibble Nibble8a Nibble1a = False;
equal_Nibble Nibble1a Nibble8a = False;
equal_Nibble Nibble8a Nibble2a = False;
equal_Nibble Nibble2a Nibble8a = False;
equal_Nibble Nibble8a Nibble3a = False;
equal_Nibble Nibble3a Nibble8a = False;
equal_Nibble Nibble8a Nibble4a = False;
equal_Nibble Nibble4a Nibble8a = False;
equal_Nibble Nibble8a Nibble5a = False;
equal_Nibble Nibble5a Nibble8a = False;
equal_Nibble Nibble8a Nibble6a = False;
equal_Nibble Nibble6a Nibble8a = False;
equal_Nibble Nibble8a Nibble7a = False;
equal_Nibble Nibble7a Nibble8a = False;
equal_Nibble Nibble9a Nibble0a = False;
equal_Nibble Nibble0a Nibble9a = False;
equal_Nibble Nibble9a Nibble1a = False;
equal_Nibble Nibble1a Nibble9a = False;
equal_Nibble Nibble9a Nibble2a = False;
equal_Nibble Nibble2a Nibble9a = False;
equal_Nibble Nibble9a Nibble3a = False;
equal_Nibble Nibble3a Nibble9a = False;
equal_Nibble Nibble9a Nibble4a = False;
equal_Nibble Nibble4a Nibble9a = False;
equal_Nibble Nibble9a Nibble5a = False;
equal_Nibble Nibble5a Nibble9a = False;
equal_Nibble Nibble9a Nibble6a = False;
equal_Nibble Nibble6a Nibble9a = False;
equal_Nibble Nibble9a Nibble7a = False;
equal_Nibble Nibble7a Nibble9a = False;
equal_Nibble Nibble9a Nibble8a = False;
equal_Nibble Nibble8a Nibble9a = False;
equal_Nibble NibbleAa Nibble0a = False;
equal_Nibble Nibble0a NibbleAa = False;
equal_Nibble NibbleAa Nibble1a = False;
equal_Nibble Nibble1a NibbleAa = False;
equal_Nibble NibbleAa Nibble2a = False;
equal_Nibble Nibble2a NibbleAa = False;
equal_Nibble NibbleAa Nibble3a = False;
equal_Nibble Nibble3a NibbleAa = False;
equal_Nibble NibbleAa Nibble4a = False;
equal_Nibble Nibble4a NibbleAa = False;
equal_Nibble NibbleAa Nibble5a = False;
equal_Nibble Nibble5a NibbleAa = False;
equal_Nibble NibbleAa Nibble6a = False;
equal_Nibble Nibble6a NibbleAa = False;
equal_Nibble NibbleAa Nibble7a = False;
equal_Nibble Nibble7a NibbleAa = False;
equal_Nibble NibbleAa Nibble8a = False;
equal_Nibble Nibble8a NibbleAa = False;
equal_Nibble NibbleAa Nibble9a = False;
equal_Nibble Nibble9a NibbleAa = False;
equal_Nibble NibbleBa Nibble0a = False;
equal_Nibble Nibble0a NibbleBa = False;
equal_Nibble NibbleBa Nibble1a = False;
equal_Nibble Nibble1a NibbleBa = False;
equal_Nibble NibbleBa Nibble2a = False;
equal_Nibble Nibble2a NibbleBa = False;
equal_Nibble NibbleBa Nibble3a = False;
equal_Nibble Nibble3a NibbleBa = False;
equal_Nibble NibbleBa Nibble4a = False;
equal_Nibble Nibble4a NibbleBa = False;
equal_Nibble NibbleBa Nibble5a = False;
equal_Nibble Nibble5a NibbleBa = False;
equal_Nibble NibbleBa Nibble6a = False;
equal_Nibble Nibble6a NibbleBa = False;
equal_Nibble NibbleBa Nibble7a = False;
equal_Nibble Nibble7a NibbleBa = False;
equal_Nibble NibbleBa Nibble8a = False;
equal_Nibble Nibble8a NibbleBa = False;
equal_Nibble NibbleBa Nibble9a = False;
equal_Nibble Nibble9a NibbleBa = False;
equal_Nibble NibbleBa NibbleAa = False;
equal_Nibble NibbleAa NibbleBa = False;
equal_Nibble NibbleCa Nibble0a = False;
equal_Nibble Nibble0a NibbleCa = False;
equal_Nibble NibbleCa Nibble1a = False;
equal_Nibble Nibble1a NibbleCa = False;
equal_Nibble NibbleCa Nibble2a = False;
equal_Nibble Nibble2a NibbleCa = False;
equal_Nibble NibbleCa Nibble3a = False;
equal_Nibble Nibble3a NibbleCa = False;
equal_Nibble NibbleCa Nibble4a = False;
equal_Nibble Nibble4a NibbleCa = False;
equal_Nibble NibbleCa Nibble5a = False;
equal_Nibble Nibble5a NibbleCa = False;
equal_Nibble NibbleCa Nibble6a = False;
equal_Nibble Nibble6a NibbleCa = False;
equal_Nibble NibbleCa Nibble7a = False;
equal_Nibble Nibble7a NibbleCa = False;
equal_Nibble NibbleCa Nibble8a = False;
equal_Nibble Nibble8a NibbleCa = False;
equal_Nibble NibbleCa Nibble9a = False;
equal_Nibble Nibble9a NibbleCa = False;
equal_Nibble NibbleCa NibbleAa = False;
equal_Nibble NibbleAa NibbleCa = False;
equal_Nibble NibbleCa NibbleBa = False;
equal_Nibble NibbleBa NibbleCa = False;
equal_Nibble NibbleDa Nibble0a = False;
equal_Nibble Nibble0a NibbleDa = False;
equal_Nibble NibbleDa Nibble1a = False;
equal_Nibble Nibble1a NibbleDa = False;
equal_Nibble NibbleDa Nibble2a = False;
equal_Nibble Nibble2a NibbleDa = False;
equal_Nibble NibbleDa Nibble3a = False;
equal_Nibble Nibble3a NibbleDa = False;
equal_Nibble NibbleDa Nibble4a = False;
equal_Nibble Nibble4a NibbleDa = False;
equal_Nibble NibbleDa Nibble5a = False;
equal_Nibble Nibble5a NibbleDa = False;
equal_Nibble NibbleDa Nibble6a = False;
equal_Nibble Nibble6a NibbleDa = False;
equal_Nibble NibbleDa Nibble7a = False;
equal_Nibble Nibble7a NibbleDa = False;
equal_Nibble NibbleDa Nibble8a = False;
equal_Nibble Nibble8a NibbleDa = False;
equal_Nibble NibbleDa Nibble9a = False;
equal_Nibble Nibble9a NibbleDa = False;
equal_Nibble NibbleDa NibbleAa = False;
equal_Nibble NibbleAa NibbleDa = False;
equal_Nibble NibbleDa NibbleBa = False;
equal_Nibble NibbleBa NibbleDa = False;
equal_Nibble NibbleDa NibbleCa = False;
equal_Nibble NibbleCa NibbleDa = False;
equal_Nibble NibbleEa Nibble0a = False;
equal_Nibble Nibble0a NibbleEa = False;
equal_Nibble NibbleEa Nibble1a = False;
equal_Nibble Nibble1a NibbleEa = False;
equal_Nibble NibbleEa Nibble2a = False;
equal_Nibble Nibble2a NibbleEa = False;
equal_Nibble NibbleEa Nibble3a = False;
equal_Nibble Nibble3a NibbleEa = False;
equal_Nibble NibbleEa Nibble4a = False;
equal_Nibble Nibble4a NibbleEa = False;
equal_Nibble NibbleEa Nibble5a = False;
equal_Nibble Nibble5a NibbleEa = False;
equal_Nibble NibbleEa Nibble6a = False;
equal_Nibble Nibble6a NibbleEa = False;
equal_Nibble NibbleEa Nibble7a = False;
equal_Nibble Nibble7a NibbleEa = False;
equal_Nibble NibbleEa Nibble8a = False;
equal_Nibble Nibble8a NibbleEa = False;
equal_Nibble NibbleEa Nibble9a = False;
equal_Nibble Nibble9a NibbleEa = False;
equal_Nibble NibbleEa NibbleAa = False;
equal_Nibble NibbleAa NibbleEa = False;
equal_Nibble NibbleEa NibbleBa = False;
equal_Nibble NibbleBa NibbleEa = False;
equal_Nibble NibbleEa NibbleCa = False;
equal_Nibble NibbleCa NibbleEa = False;
equal_Nibble NibbleEa NibbleDa = False;
equal_Nibble NibbleDa NibbleEa = False;
equal_Nibble NibbleFa Nibble0a = False;
equal_Nibble Nibble0a NibbleFa = False;
equal_Nibble NibbleFa Nibble1a = False;
equal_Nibble Nibble1a NibbleFa = False;
equal_Nibble NibbleFa Nibble2a = False;
equal_Nibble Nibble2a NibbleFa = False;
equal_Nibble NibbleFa Nibble3a = False;
equal_Nibble Nibble3a NibbleFa = False;
equal_Nibble NibbleFa Nibble4a = False;
equal_Nibble Nibble4a NibbleFa = False;
equal_Nibble NibbleFa Nibble5a = False;
equal_Nibble Nibble5a NibbleFa = False;
equal_Nibble NibbleFa Nibble6a = False;
equal_Nibble Nibble6a NibbleFa = False;
equal_Nibble NibbleFa Nibble7a = False;
equal_Nibble Nibble7a NibbleFa = False;
equal_Nibble NibbleFa Nibble8a = False;
equal_Nibble Nibble8a NibbleFa = False;
equal_Nibble NibbleFa Nibble9a = False;
equal_Nibble Nibble9a NibbleFa = False;
equal_Nibble NibbleFa NibbleAa = False;
equal_Nibble NibbleAa NibbleFa = False;
equal_Nibble NibbleFa NibbleBa = False;
equal_Nibble NibbleBa NibbleFa = False;
equal_Nibble NibbleFa NibbleCa = False;
equal_Nibble NibbleCa NibbleFa = False;
equal_Nibble NibbleFa NibbleDa = False;
equal_Nibble NibbleDa NibbleFa = False;
equal_Nibble NibbleFa NibbleEa = False;
equal_Nibble NibbleEa NibbleFa = False;
equal_Nibble Nibble0a Nibble0a = True;
equal_Nibble Nibble1a Nibble1a = True;
equal_Nibble Nibble2a Nibble2a = True;
equal_Nibble Nibble3a Nibble3a = True;
equal_Nibble Nibble4a Nibble4a = True;
equal_Nibble Nibble5a Nibble5a = True;
equal_Nibble Nibble6a Nibble6a = True;
equal_Nibble Nibble7a Nibble7a = True;
equal_Nibble Nibble8a Nibble8a = True;
equal_Nibble Nibble9a Nibble9a = True;
equal_Nibble NibbleAa NibbleAa = True;
equal_Nibble NibbleBa NibbleBa = True;
equal_Nibble NibbleCa NibbleCa = True;
equal_Nibble NibbleDa NibbleDa = True;
equal_Nibble NibbleEa NibbleEa = True;
equal_Nibble NibbleFa NibbleFa = True;

equal_Chara :: Chara -> Chara -> Bool;
equal_Chara (Chara x1 x2) (Chara y1 y2) =
  equal_Nibble x1 y1 && equal_Nibble x2 y2;

random_Inta ::
  Natural -> (Natural, Natural) -> ((Inta, () -> Term), (Natural, Natural));
random_Inta i = random_aux_Inta i i;

size_Itselfa :: forall a. Itselfa a -> Nat;
size_Itselfa Typea = Zero_nat;

size_Nibblea :: Nibblea -> Nat;
size_Nibblea NibbleFa = Zero_nat;
size_Nibblea NibbleEa = Zero_nat;
size_Nibblea NibbleDa = Zero_nat;
size_Nibblea NibbleCa = Zero_nat;
size_Nibblea NibbleBa = Zero_nat;
size_Nibblea NibbleAa = Zero_nat;
size_Nibblea Nibble9a = Zero_nat;
size_Nibblea Nibble8a = Zero_nat;
size_Nibblea Nibble7a = Zero_nat;
size_Nibblea Nibble6a = Zero_nat;
size_Nibblea Nibble5a = Zero_nat;
size_Nibblea Nibble4a = Zero_nat;
size_Nibblea Nibble3a = Zero_nat;
size_Nibblea Nibble2a = Zero_nat;
size_Nibblea Nibble1a = Zero_nat;
size_Nibblea Nibble0a = Zero_nat;

term_of_Nat :: Nata -> Term;
term_of_Nat Zero =
  Const "ListsAndMaps.Nat.Zero" (Typerep "ListsAndMaps.Nat" []);
term_of_Nat (Suca a) =
  App (Const "ListsAndMaps.Nat.Suc"
        (Typerep "fun"
          [Typerep "ListsAndMaps.Nat" [], Typerep "ListsAndMaps.Nat" []]))
    (term_of_Nat a);

typerep_Nat :: Itself Nata -> Typerepa;
typerep_Nat t = Typerep "ListsAndMaps.Nat" [];

equal_Itself :: forall a. Itselfa a -> Itselfa a -> Bool;
equal_Itself Typea Typea = True;

random_Chara ::
  Natural -> (Natural, Natural) -> ((Chara, () -> Term), (Natural, Natural));
random_Chara i = random_aux_Chara i i;

term_of_Inta :: Inta -> Term;
term_of_Inta Pls =
  Const "ListsAndMaps.Inta.Pls" (Typerep "ListsAndMaps.Inta" []);
term_of_Inta Min =
  Const "ListsAndMaps.Inta.Min" (Typerep "ListsAndMaps.Inta" []);
term_of_Inta (Bit0a a) =
  App (Const "ListsAndMaps.Inta.Bit0"
        (Typerep "fun"
          [Typerep "ListsAndMaps.Inta" [], Typerep "ListsAndMaps.Inta" []]))
    (term_of_Inta a);
term_of_Inta (Bit1a a) =
  App (Const "ListsAndMaps.Inta.Bit1"
        (Typerep "fun"
          [Typerep "ListsAndMaps.Inta" [], Typerep "ListsAndMaps.Inta" []]))
    (term_of_Inta a);
term_of_Inta (Number_of_int a) =
  App (Const "ListsAndMaps.Inta.Number_of_int"
        (Typerep "fun"
          [Typerep "ListsAndMaps.Inta" [], Typerep "ListsAndMaps.Inta" []]))
    (term_of_Inta a);

typerep_Inta :: Itself Inta -> Typerepa;
typerep_Inta t = Typerep "ListsAndMaps.Inta" [];

random_Itself ::
  forall a.
    (Typerep a) => Natural ->
                     (Natural, Natural) ->
                       ((Itselfa a, () -> Term), (Natural, Natural));
random_Itself i = random_aux_Itself i i;

term_of_Nibble :: Nibblea -> Term;
term_of_Nibble Nibble0a =
  Const "ListsAndMaps.Nibble.Nibble0" (Typerep "ListsAndMaps.Nibble" []);
term_of_Nibble Nibble1a =
  Const "ListsAndMaps.Nibble.Nibble1" (Typerep "ListsAndMaps.Nibble" []);
term_of_Nibble Nibble2a =
  Const "ListsAndMaps.Nibble.Nibble2" (Typerep "ListsAndMaps.Nibble" []);
term_of_Nibble Nibble3a =
  Const "ListsAndMaps.Nibble.Nibble3" (Typerep "ListsAndMaps.Nibble" []);
term_of_Nibble Nibble4a =
  Const "ListsAndMaps.Nibble.Nibble4" (Typerep "ListsAndMaps.Nibble" []);
term_of_Nibble Nibble5a =
  Const "ListsAndMaps.Nibble.Nibble5" (Typerep "ListsAndMaps.Nibble" []);
term_of_Nibble Nibble6a =
  Const "ListsAndMaps.Nibble.Nibble6" (Typerep "ListsAndMaps.Nibble" []);
term_of_Nibble Nibble7a =
  Const "ListsAndMaps.Nibble.Nibble7" (Typerep "ListsAndMaps.Nibble" []);
term_of_Nibble Nibble8a =
  Const "ListsAndMaps.Nibble.Nibble8" (Typerep "ListsAndMaps.Nibble" []);
term_of_Nibble Nibble9a =
  Const "ListsAndMaps.Nibble.Nibble9" (Typerep "ListsAndMaps.Nibble" []);
term_of_Nibble NibbleAa =
  Const "ListsAndMaps.Nibble.NibbleA" (Typerep "ListsAndMaps.Nibble" []);
term_of_Nibble NibbleBa =
  Const "ListsAndMaps.Nibble.NibbleB" (Typerep "ListsAndMaps.Nibble" []);
term_of_Nibble NibbleCa =
  Const "ListsAndMaps.Nibble.NibbleC" (Typerep "ListsAndMaps.Nibble" []);
term_of_Nibble NibbleDa =
  Const "ListsAndMaps.Nibble.NibbleD" (Typerep "ListsAndMaps.Nibble" []);
term_of_Nibble NibbleEa =
  Const "ListsAndMaps.Nibble.NibbleE" (Typerep "ListsAndMaps.Nibble" []);
term_of_Nibble NibbleFa =
  Const "ListsAndMaps.Nibble.NibbleF" (Typerep "ListsAndMaps.Nibble" []);

term_of_Chara :: Chara -> Term;
term_of_Chara (Chara a b) =
  App (App (Const "ListsAndMaps.Chara.Chara"
             (Typerep "fun"
               [Typerep "ListsAndMaps.Nibble" [],
                 Typerep "fun"
                   [Typerep "ListsAndMaps.Nibble" [],
                     Typerep "ListsAndMaps.Chara" []]]))
        (term_of_Nibble a))
    (term_of_Nibble b);

typerep_Chara :: Itself Chara -> Typerepa;
typerep_Chara t = Typerep "ListsAndMaps.Chara" [];

term_of_Itself :: forall a. (Typerep a) => Itselfa a -> Term;
term_of_Itself Typea =
  Const "ListsAndMaps.Itself.Type"
    (Typerep "ListsAndMaps.Itself" [(typerep :: Itself a -> Typerepa) Type]);

typerep_Itself :: forall a. (Typerep a) => Itself (Itselfa a) -> Typerepa;
typerep_Itself t =
  Typerep "ListsAndMaps.Itself" [(typerep :: Itself a -> Typerepa) Type];

typerep_Nibble :: Itself Nibblea -> Typerepa;
typerep_Nibble t = Typerep "ListsAndMaps.Nibble" [];

narrowing_Itself ::
  forall a. (Typerep a) => Integer -> Narrowing_cons (Itselfa a);
narrowing_Itself = cons Typea;

narrowing_Nibble :: Integer -> Narrowing_cons Nibblea;
narrowing_Nibble =
  sum (cons NibbleFa)
    (sum (cons NibbleEa)
      (sum (cons NibbleDa)
        (sum (cons NibbleCa)
          (sum (cons NibbleBa)
            (sum (cons NibbleAa)
              (sum (cons Nibble9a)
                (sum (cons Nibble8a)
                  (sum (cons Nibble7a)
                    (sum (cons Nibble6a)
                      (sum (cons Nibble5a)
                        (sum (cons Nibble4a)
                          (sum (cons Nibble3a)
                            (sum (cons Nibble2a)
                              (sum (cons Nibble1a)
                                (cons Nibble0a)))))))))))))));

full_exhaustive_Nat ::
  ((Nata, () -> Term) -> Maybe (Bool, [Term])) ->
    Natural -> Maybe (Bool, [Term]);
full_exhaustive_Nat f i =
  (if less_natural zero_natural i
    then (case full_exhaustive_Nat
                 (\ (uu, uua) ->
                   f (Suca uu,
                       (\ _ ->
                         App (Const "ListsAndMaps.Nat.Suc"
                               (Typerep "fun"
                                 [Typerep "ListsAndMaps.Nat" [],
                                   Typerep "ListsAndMaps.Nat" []]))
                           (uua ()))))
                 (minus_natural i one_natural)
           of {
           Nothing ->
             f (Zero,
                 (\ _ ->
                   Const "ListsAndMaps.Nat.Zero"
                     (Typerep "ListsAndMaps.Nat" [])));
           Just a -> Just a;
         })
    else Nothing);

partial_term_of_Nat :: Itself Nata -> Narrowing_term -> Term;
partial_term_of_Nat ty (Narrowing_constructor (1 :: Integer) []) =
  Const "ListsAndMaps.Nat.Zero" (Typerep "ListsAndMaps.Nat" []);
partial_term_of_Nat ty (Narrowing_constructor (0 :: Integer) [a]) =
  App (Const "ListsAndMaps.Nat.Suc"
        (Typerep "fun"
          [Typerep "ListsAndMaps.Nat" [], Typerep "ListsAndMaps.Nat" []]))
    (partial_term_of_Nat Type a);
partial_term_of_Nat ty (Narrowing_variable p tt) =
  Free "_" (Typerep "ListsAndMaps.Nat" []);

full_exhaustive_Inta ::
  ((Inta, () -> Term) -> Maybe (Bool, [Term])) ->
    Natural -> Maybe (Bool, [Term]);
full_exhaustive_Inta f i =
  (if less_natural zero_natural i
    then (case full_exhaustive_Inta
                 (\ (uu, uua) ->
                   f (Number_of_int uu,
                       (\ _ ->
                         App (Const "ListsAndMaps.Inta.Number_of_int"
                               (Typerep "fun"
                                 [Typerep "ListsAndMaps.Inta" [],
                                   Typerep "ListsAndMaps.Inta" []]))
                           (uua ()))))
                 (minus_natural i one_natural)
           of {
           Nothing ->
             (case full_exhaustive_Inta
                     (\ (uu, uua) ->
                       f (Bit1a uu,
                           (\ _ ->
                             App (Const "ListsAndMaps.Inta.Bit1"
                                   (Typerep "fun"
                                     [Typerep "ListsAndMaps.Inta" [],
                                       Typerep "ListsAndMaps.Inta" []]))
                               (uua ()))))
                     (minus_natural i one_natural)
               of {
               Nothing ->
                 (case full_exhaustive_Inta
                         (\ (uu, uua) ->
                           f (Bit0a uu,
                               (\ _ ->
                                 App (Const "ListsAndMaps.Inta.Bit0"
                                       (Typerep "fun"
 [Typerep "ListsAndMaps.Inta" [], Typerep "ListsAndMaps.Inta" []]))
                                   (uua ()))))
                         (minus_natural i one_natural)
                   of {
                   Nothing ->
                     (case f (Min, (\ _ ->
                                     Const "ListsAndMaps.Inta.Min"
                                       (Typerep "ListsAndMaps.Inta" [])))
                       of {
                       Nothing ->
                         f (Pls, (\ _ ->
                                   Const "ListsAndMaps.Inta.Pls"
                                     (Typerep "ListsAndMaps.Inta" [])));
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
  Const "ListsAndMaps.Inta.Pls" (Typerep "ListsAndMaps.Inta" []);
partial_term_of_Inta ty (Narrowing_constructor (3 :: Integer) []) =
  Const "ListsAndMaps.Inta.Min" (Typerep "ListsAndMaps.Inta" []);
partial_term_of_Inta ty (Narrowing_constructor (2 :: Integer) [a]) =
  App (Const "ListsAndMaps.Inta.Bit0"
        (Typerep "fun"
          [Typerep "ListsAndMaps.Inta" [], Typerep "ListsAndMaps.Inta" []]))
    (partial_term_of_Inta Type a);
partial_term_of_Inta ty (Narrowing_constructor (1 :: Integer) [a]) =
  App (Const "ListsAndMaps.Inta.Bit1"
        (Typerep "fun"
          [Typerep "ListsAndMaps.Inta" [], Typerep "ListsAndMaps.Inta" []]))
    (partial_term_of_Inta Type a);
partial_term_of_Inta ty (Narrowing_constructor (0 :: Integer) [a]) =
  App (Const "ListsAndMaps.Inta.Number_of_int"
        (Typerep "fun"
          [Typerep "ListsAndMaps.Inta" [], Typerep "ListsAndMaps.Inta" []]))
    (partial_term_of_Inta Type a);
partial_term_of_Inta ty (Narrowing_variable p tt) =
  Free "_" (Typerep "ListsAndMaps.Inta" []);

full_exhaustive_Nibble ::
  ((Nibblea, () -> Term) -> Maybe (Bool, [Term])) ->
    Natural -> Maybe (Bool, [Term]);
full_exhaustive_Nibble f i =
  (if less_natural zero_natural i
    then (case f (NibbleFa,
                   (\ _ ->
                     Const "ListsAndMaps.Nibble.NibbleF"
                       (Typerep "ListsAndMaps.Nibble" [])))
           of {
           Nothing ->
             (case f (NibbleEa,
                       (\ _ ->
                         Const "ListsAndMaps.Nibble.NibbleE"
                           (Typerep "ListsAndMaps.Nibble" [])))
               of {
               Nothing ->
                 (case f (NibbleDa,
                           (\ _ ->
                             Const "ListsAndMaps.Nibble.NibbleD"
                               (Typerep "ListsAndMaps.Nibble" [])))
                   of {
                   Nothing ->
                     (case f (NibbleCa,
                               (\ _ ->
                                 Const "ListsAndMaps.Nibble.NibbleC"
                                   (Typerep "ListsAndMaps.Nibble" [])))
                       of {
                       Nothing ->
                         (case f (NibbleBa,
                                   (\ _ ->
                                     Const "ListsAndMaps.Nibble.NibbleB"
                                       (Typerep "ListsAndMaps.Nibble" [])))
                           of {
                           Nothing ->
                             (case f (NibbleAa,
                                       (\ _ ->
 Const "ListsAndMaps.Nibble.NibbleA" (Typerep "ListsAndMaps.Nibble" [])))
                               of {
                               Nothing ->
                                 (case f
 (Nibble9a,
   (\ _ ->
     Const "ListsAndMaps.Nibble.Nibble9" (Typerep "ListsAndMaps.Nibble" [])))
                                   of {
                                   Nothing ->
                                     (case f
     (Nibble8a,
       (\ _ ->
         Const "ListsAndMaps.Nibble.Nibble8"
           (Typerep "ListsAndMaps.Nibble" [])))
                                       of {
                                       Nothing ->
 (case f (Nibble7a,
           (\ _ ->
             Const "ListsAndMaps.Nibble.Nibble7"
               (Typerep "ListsAndMaps.Nibble" [])))
   of {
   Nothing ->
     (case f (Nibble6a,
               (\ _ ->
                 Const "ListsAndMaps.Nibble.Nibble6"
                   (Typerep "ListsAndMaps.Nibble" [])))
       of {
       Nothing ->
         (case f (Nibble5a,
                   (\ _ ->
                     Const "ListsAndMaps.Nibble.Nibble5"
                       (Typerep "ListsAndMaps.Nibble" [])))
           of {
           Nothing ->
             (case f (Nibble4a,
                       (\ _ ->
                         Const "ListsAndMaps.Nibble.Nibble4"
                           (Typerep "ListsAndMaps.Nibble" [])))
               of {
               Nothing ->
                 (case f (Nibble3a,
                           (\ _ ->
                             Const "ListsAndMaps.Nibble.Nibble3"
                               (Typerep "ListsAndMaps.Nibble" [])))
                   of {
                   Nothing ->
                     (case f (Nibble2a,
                               (\ _ ->
                                 Const "ListsAndMaps.Nibble.Nibble2"
                                   (Typerep "ListsAndMaps.Nibble" [])))
                       of {
                       Nothing ->
                         (case f (Nibble1a,
                                   (\ _ ->
                                     Const "ListsAndMaps.Nibble.Nibble1"
                                       (Typerep "ListsAndMaps.Nibble" [])))
                           of {
                           Nothing ->
                             f (Nibble0a,
                                 (\ _ ->
                                   Const "ListsAndMaps.Nibble.Nibble0"
                                     (Typerep "ListsAndMaps.Nibble" [])));
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
                       App (App (Const "ListsAndMaps.Chara.Chara"
                                  (Typerep "fun"
                                    [Typerep "ListsAndMaps.Nibble" [],
                                      Typerep "fun"
[Typerep "ListsAndMaps.Nibble" [], Typerep "ListsAndMaps.Chara" []]]))
                             (uua ()))
                         (uuc ()))))
               (minus_natural i one_natural))
           (minus_natural i one_natural)
    else Nothing);

partial_term_of_Nibble :: Itself Nibblea -> Narrowing_term -> Term;
partial_term_of_Nibble ty (Narrowing_constructor (15 :: Integer) []) =
  Const "ListsAndMaps.Nibble.Nibble0" (Typerep "ListsAndMaps.Nibble" []);
partial_term_of_Nibble ty (Narrowing_constructor (14 :: Integer) []) =
  Const "ListsAndMaps.Nibble.Nibble1" (Typerep "ListsAndMaps.Nibble" []);
partial_term_of_Nibble ty (Narrowing_constructor (13 :: Integer) []) =
  Const "ListsAndMaps.Nibble.Nibble2" (Typerep "ListsAndMaps.Nibble" []);
partial_term_of_Nibble ty (Narrowing_constructor (12 :: Integer) []) =
  Const "ListsAndMaps.Nibble.Nibble3" (Typerep "ListsAndMaps.Nibble" []);
partial_term_of_Nibble ty (Narrowing_constructor (11 :: Integer) []) =
  Const "ListsAndMaps.Nibble.Nibble4" (Typerep "ListsAndMaps.Nibble" []);
partial_term_of_Nibble ty (Narrowing_constructor (10 :: Integer) []) =
  Const "ListsAndMaps.Nibble.Nibble5" (Typerep "ListsAndMaps.Nibble" []);
partial_term_of_Nibble ty (Narrowing_constructor (9 :: Integer) []) =
  Const "ListsAndMaps.Nibble.Nibble6" (Typerep "ListsAndMaps.Nibble" []);
partial_term_of_Nibble ty (Narrowing_constructor (8 :: Integer) []) =
  Const "ListsAndMaps.Nibble.Nibble7" (Typerep "ListsAndMaps.Nibble" []);
partial_term_of_Nibble ty (Narrowing_constructor (7 :: Integer) []) =
  Const "ListsAndMaps.Nibble.Nibble8" (Typerep "ListsAndMaps.Nibble" []);
partial_term_of_Nibble ty (Narrowing_constructor (6 :: Integer) []) =
  Const "ListsAndMaps.Nibble.Nibble9" (Typerep "ListsAndMaps.Nibble" []);
partial_term_of_Nibble ty (Narrowing_constructor (5 :: Integer) []) =
  Const "ListsAndMaps.Nibble.NibbleA" (Typerep "ListsAndMaps.Nibble" []);
partial_term_of_Nibble ty (Narrowing_constructor (4 :: Integer) []) =
  Const "ListsAndMaps.Nibble.NibbleB" (Typerep "ListsAndMaps.Nibble" []);
partial_term_of_Nibble ty (Narrowing_constructor (3 :: Integer) []) =
  Const "ListsAndMaps.Nibble.NibbleC" (Typerep "ListsAndMaps.Nibble" []);
partial_term_of_Nibble ty (Narrowing_constructor (2 :: Integer) []) =
  Const "ListsAndMaps.Nibble.NibbleD" (Typerep "ListsAndMaps.Nibble" []);
partial_term_of_Nibble ty (Narrowing_constructor (1 :: Integer) []) =
  Const "ListsAndMaps.Nibble.NibbleE" (Typerep "ListsAndMaps.Nibble" []);
partial_term_of_Nibble ty (Narrowing_constructor (0 :: Integer) []) =
  Const "ListsAndMaps.Nibble.NibbleF" (Typerep "ListsAndMaps.Nibble" []);
partial_term_of_Nibble ty (Narrowing_variable p tt) =
  Free "_" (Typerep "ListsAndMaps.Nibble" []);

partial_term_of_Chara :: Itself Chara -> Narrowing_term -> Term;
partial_term_of_Chara ty (Narrowing_constructor (0 :: Integer) [b, a]) =
  App (App (Const "ListsAndMaps.Chara.Chara"
             (Typerep "fun"
               [Typerep "ListsAndMaps.Nibble" [],
                 Typerep "fun"
                   [Typerep "ListsAndMaps.Nibble" [],
                     Typerep "ListsAndMaps.Chara" []]]))
        (partial_term_of_Nibble Type a))
    (partial_term_of_Nibble Type b);
partial_term_of_Chara ty (Narrowing_variable p tt) =
  Free "_" (Typerep "ListsAndMaps.Chara" []);

typerep_Nat_IITN_Nat :: Itself Nat_IITN_Nat -> Typerepa;
typerep_Nat_IITN_Nat t = Typerep "ListsAndMaps.Nat.Nat_IITN_Nat" [];

full_exhaustive_Itself ::
  forall a.
    (Typerep a) => ((Itselfa a, () -> Term) -> Maybe (Bool, [Term])) ->
                     Natural -> Maybe (Bool, [Term]);
full_exhaustive_Itself f i =
  (if less_natural zero_natural i
    then f (Typea,
             (\ _ ->
               Const "ListsAndMaps.Itself.Type"
                 (Typerep "ListsAndMaps.Itself"
                   [(typerep :: Itself a -> Typerepa) Type])))
    else Nothing);

partial_term_of_Itself ::
  forall a. (Typerep a) => Itself (Itselfa a) -> Narrowing_term -> Term;
partial_term_of_Itself ty (Narrowing_constructor (0 :: Integer) []) =
  Const "ListsAndMaps.Itself.Type"
    (Typerep "ListsAndMaps.Itself" [(typerep :: Itself a -> Typerepa) Type]);
partial_term_of_Itself ty (Narrowing_variable p tt) =
  Free "_"
    (Typerep "ListsAndMaps.Itself" [(typerep :: Itself a -> Typerepa) Type]);

typerep_Inta_pre_Inta ::
  forall a. (Typerep a) => Itself (Inta_pre_Inta a) -> Typerepa;
typerep_Inta_pre_Inta t =
  Typerep "ListsAndMaps.Inta.Inta_pre_Inta"
    [(typerep :: Itself a -> Typerepa) Type];

typerep_Inta_IITN_Inta :: Itself Inta_IITN_Inta -> Typerepa;
typerep_Inta_IITN_Inta t = Typerep "ListsAndMaps.Inta.Inta_IITN_Inta" [];

typerep_Chara_IITN_Chara :: Itself Chara_IITN_Chara -> Typerepa;
typerep_Chara_IITN_Chara t = Typerep "ListsAndMaps.Chara.Chara_IITN_Chara" [];

typerep_Itself_pre_Itself ::
  forall a b.
    (Typerep a, Typerep b) => Itself (Itself_pre_Itself a b) -> Typerepa;
typerep_Itself_pre_Itself t =
  Typerep "ListsAndMaps.Itself.Itself_pre_Itself"
    [(typerep :: Itself a -> Typerepa) Type,
      (typerep :: Itself b -> Typerepa) Type];

typerep_Nibble_pre_Nibble :: Itself Nibble_pre_Nibble -> Typerepa;
typerep_Nibble_pre_Nibble t =
  Typerep "ListsAndMaps.Nibble.Nibble_pre_Nibble" [];

typerep_Itself_IITN_Itself ::
  forall a. (Typerep a) => Itself (Itself_IITN_Itself a) -> Typerepa;
typerep_Itself_IITN_Itself t =
  Typerep "ListsAndMaps.Itself.Itself_IITN_Itself"
    [(typerep :: Itself a -> Typerepa) Type];

typerep_Nibble_IITN_Nibble :: Itself Nibble_IITN_Nibble -> Typerepa;
typerep_Nibble_IITN_Nibble t =
  Typerep "ListsAndMaps.Nibble.Nibble_IITN_Nibble" [];

}
