{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Fset(Ord(..), Natural(..), integer_of_natural, plus_natural, Plus(..),
        zero_natural, Zero(..), Monoid_add, Times(..), Div(..), One(..),
        Numeral, Minus(..), Typerepa(..), Term(..), Itself(..), Typerep(..),
        Term_of(..), Random(..), Semiring_numeral_div, Narrowing_type(..),
        Narrowing_term(..), Partial_term_of(..), Full_exhaustive(..), Eqa(..),
        Narrowing_cons(..), Narrowing(..), Nat(..), Num(..), Set(..), Nata(..),
        Fset(..), Nibble(..), Char(..), Nat_IITN_Nat, Fset_IITN_Fset, bitM,
        ball, membera, length_unique, card, remdups, mapb, mapa, empty, filterb,
        filtera, list_ex, exists, member, inter, nulla, inserta, insert, foldla,
        union, foldr, less_eq_natural, less_natural, one_natural, sgn_integer,
        abs_integer, apsnd, divmod_integer, div_integer, div_natural, log,
        intera, remove_all, remove, uniona, times_natural, mod_integer,
        mod_natural, max, natural_of_integer, minus_natural, minus_shift, next,
        pick, list_all, foralla, subfset_eq, eq_fset, subfset, scomp,
        equal_natural, iterate, range, is_empty, set_Fset, pred_Fset, subtracta,
        gen_length, rec_Nat, plus_nat, size_Nat, map_Fset, rec_Fset, list_all2,
        rel_Fset, size_list, size_Fset, collapse, valapp, listsum,
        select_weight, random_aux_Nat, random_aux_list, random_list,
        random_aux_Fset, sum, numeral, less_num, less_eq_num, cons, plus_num,
        size_Nata, equal_num, times_num, equal_Nat, size_lista, size_Fseta,
        non_empty, equal_Fset, random_Nat, random_Fset, term_of_Nat,
        typerep_Nat, term_of_list, term_of_Fset, typerep_Fset, one_integer,
        divmod_step, divmod, full_exhaustive_Nat, partial_term_of_Nat,
        full_exhaustive_list, full_exhaustive_Fset, partial_term_of_list,
        partial_term_of_Fset, typerep_Nat_IITN_Nat, typerep_Fset_IITN_Fset)
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

data Set a = Seta [a] | Coset [a];

data Nata = Zero | Suca Nata;

newtype Fset a = Set [a];

data Nibble = Nibble0 | Nibble1 | Nibble2 | Nibble3 | Nibble4 | Nibble5
  | Nibble6 | Nibble7 | Nibble8 | Nibble9 | NibbleA | NibbleB | NibbleC
  | NibbleD | NibbleE | NibbleF;

data Char = Char Nibble Nibble;

data Nat_IITN_Nat;

data Fset_IITN_Fset a;

bitM :: Num -> Num;
bitM One = One;
bitM (Bit0 n) = Bit1 (bitM n);
bitM (Bit1 n) = Bit1 (Bit0 n);

ball :: forall a. Set a -> (a -> Bool) -> Bool;
ball (Seta xs) p = all p xs;

membera :: forall a. (Eqa a) => a -> [a] -> Bool;
membera x [] = False;
membera x (y : ys) = eq x y || membera x ys;

length_unique :: forall a. (Eqa a) => [a] -> Nata;
length_unique [] = Zero;
length_unique (x : xs) =
  (if membera x xs then length_unique xs else Suca (length_unique xs));

card :: forall a. (Eqa a) => Fset a -> Nata;
card (Set xs) = length_unique xs;

remdups :: forall a. (Eqa a) => [a] -> [a];
remdups [] = [];
remdups (x : xs) = (if membera x xs then remdups xs else x : remdups xs);

mapb :: forall a b. (a -> b) -> [a] -> [b];
mapb f [] = [];
mapb f (x : xs) = f x : mapb f xs;

mapa :: forall a b. (Eqa b) => (a -> b) -> Fset a -> Fset b;
mapa f (Set xs) = Set (remdups (mapb f xs));

empty :: forall a. Fset a;
empty = Set [];

filterb :: forall a. (a -> Bool) -> [a] -> [a];
filterb p [] = [];
filterb p (x : xs) = (if p x then x : filterb p xs else filterb p xs);

filtera :: forall a. (a -> Bool) -> Fset a -> Fset a;
filtera p (Set xs) = Set (filterb p xs);

list_ex :: forall a. (a -> Bool) -> [a] -> Bool;
list_ex p [] = False;
list_ex p (x : xs) = p x || list_ex p xs;

exists :: forall a. (a -> Bool) -> Fset a -> Bool;
exists p (Set xs) = list_ex p xs;

member :: forall a. (Eqa a) => Fset a -> a -> Bool;
member a y = exists (eq y) a;

inter :: forall a. (Eqa a) => Fset a -> Fset a -> Fset a;
inter a b = filtera (member a) b;

nulla :: forall a. [a] -> Bool;
nulla [] = True;
nulla (x : xs) = False;

inserta :: forall a. (Eqa a) => a -> [a] -> [a];
inserta x xs = (if membera x xs then xs else x : xs);

insert :: forall a. (Eqa a) => a -> Fset a -> Fset a;
insert x (Set xs) = Set (inserta x xs);

foldla :: forall a b. (a -> b -> a) -> a -> [b] -> a;
foldla f a [] = a;
foldla f a (x : xs) = foldla f (f a x) xs;

union :: forall a. (Eqa a) => Fset a -> Fset a -> Fset a;
union (Set xs) a = foldla (\ aa x -> insert x aa) a xs;

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

intera :: forall a. (Eqa a) => Fset (Fset a) -> Fset a;
intera (Set (a : asa)) = foldla inter a asa;

remove_all :: forall a. (Eqa a) => a -> [a] -> [a];
remove_all x xs = filterb (not . eq x) xs;

remove :: forall a. (Eqa a) => a -> Fset a -> Fset a;
remove x (Set xs) = Set (remove_all x xs);

uniona :: forall a. (Eqa a) => Fset (Fset a) -> Fset a;
uniona (Set asa) = foldla union empty asa;

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

list_all :: forall a. (a -> Bool) -> [a] -> Bool;
list_all p [] = True;
list_all p (x : xs) = p x && list_all p xs;

foralla :: forall a. (a -> Bool) -> Fset a -> Bool;
foralla p (Set xs) = list_all p xs;

subfset_eq :: forall a. (Eqa a) => Fset a -> Fset a -> Bool;
subfset_eq a b = foralla (member b) a;

eq_fset :: forall a. (Eqa a) => Fset a -> Fset a -> Bool;
eq_fset a b = subfset_eq a b && subfset_eq b a;

subfset :: forall a. (Eqa a) => Fset a -> Fset a -> Bool;
subfset a b = subfset_eq a b && not (subfset_eq b a);

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

is_empty :: forall a. Fset a -> Bool;
is_empty (Set xs) = nulla xs;

set_Fset :: forall a. Fset a -> Set a;
set_Fset (Set x) = Seta x;

pred_Fset :: forall a. (a -> Bool) -> Fset a -> Bool;
pred_Fset p = (\ x -> ball (set_Fset x) p);

subtracta :: forall a. (Eqa a) => Fset a -> Fset a -> Fset a;
subtracta (Set xs) a = foldla (\ aa x -> remove x aa) a xs;

gen_length :: forall a. Nat -> [a] -> Nat;
gen_length n (x : xs) = gen_length (Suc n) xs;
gen_length n [] = n;

rec_Nat :: forall a. a -> (Nata -> a -> a) -> Nata -> a;
rec_Nat f1 f2 Zero = f1;
rec_Nat f1 f2 (Suca x2) = f2 x2 (rec_Nat f1 f2 x2);

plus_nat :: Nat -> Nat -> Nat;
plus_nat (Suc m) n = plus_nat m (Suc n);
plus_nat Zero_nat n = n;

size_Nat :: Nata -> Nat;
size_Nat Zero = Zero_nat;
size_Nat (Suca x2) = plus_nat (size_Nat x2) (Suc Zero_nat);

map_Fset :: forall a b. (a -> b) -> Fset a -> Fset b;
map_Fset f (Set x) = Set (map f x);

rec_Fset :: forall a b. ([a] -> b) -> Fset a -> b;
rec_Fset f (Set x) = f x;

list_all2 :: forall a b. (a -> b -> Bool) -> [a] -> [b] -> Bool;
list_all2 p (x : xs) (y : ys) = p x y && list_all2 p xs ys;
list_all2 p xs [] = null xs;
list_all2 p [] ys = null ys;

rel_Fset :: forall a b. (a -> b -> Bool) -> Fset a -> Fset b -> Bool;
rel_Fset r (Set x) (Set y) = list_all2 r x y;

size_list :: forall a. (a -> Nat) -> [a] -> Nat;
size_list x [] = Zero_nat;
size_list x (x21 : x22) =
  plus_nat (plus_nat (x x21) (size_list x x22)) (Suc Zero_nat);

size_Fset :: forall a. (a -> Nat) -> Fset a -> Nat;
size_Fset xa (Set x) = plus_nat (size_list xa x) (Suc Zero_nat);

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
                        Const "Fset.Nat.Suc"
                          (Typerep "fun"
                            [Typerep "Fset.Nat" [], Typerep "Fset.Nat" []])))
                    x,
                   a)))),
        (one_natural,
          (\ a ->
            ((Zero, (\ _ -> Const "Fset.Nat.Zero" (Typerep "Fset.Nat" []))),
              a)))])
    s;

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

random_list ::
  forall a.
    (Random a) => Natural ->
                    (Natural, Natural) ->
                      (([a], () -> Term), (Natural, Natural));
random_list i = random_aux_list i i;

random_aux_Fset ::
  forall a.
    (Random a) => Natural ->
                    Natural ->
                      (Natural, Natural) ->
                        ((Fset a, () -> Term), (Natural, Natural));
random_aux_Fset i j s =
  collapse
    (select_weight
      [(one_natural,
         scomp (random_list j)
           (\ x ->
             (\ a ->
               (valapp
                  (Set, (\ _ ->
                          Const "Fset.Fset.Set"
                            (Typerep "fun"
                              [Typerep "List.list"
                                 [(typerep :: Itself a -> Typerepa) Type],
                                Typerep "Fset.Fset"
                                  [(typerep :: Itself a -> Typerepa) Type]])))
                  x,
                 a))))])
    s;

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

size_Nata :: Nata -> Nat;
size_Nata Zero = Zero_nat;
size_Nata (Suca x2) = plus_nat (size_Nata x2) (Suc Zero_nat);

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
equal_Nat Zero (Suca x2) = False;
equal_Nat (Suca x2) Zero = False;
equal_Nat (Suca x2) (Suca y2) = equal_Nat x2 y2;
equal_Nat Zero Zero = True;

size_lista :: forall a. [a] -> Nat;
size_lista = gen_length Zero_nat;

size_Fseta :: forall a. Fset a -> Nat;
size_Fseta (Set x) = plus_nat (size_lista x) (Suc Zero_nat);

non_empty :: Narrowing_type -> Bool;
non_empty (Narrowing_sum_of_products ps) = not (null ps);

equal_Fset :: forall a. (Eq a) => Fset a -> Fset a -> Bool;
equal_Fset (Set x) (Set ya) = x == ya;

random_Nat ::
  Natural -> (Natural, Natural) -> ((Nata, () -> Term), (Natural, Natural));
random_Nat i = random_aux_Nat i i;

random_Fset ::
  forall a.
    (Random a) => Natural ->
                    (Natural, Natural) ->
                      ((Fset a, () -> Term), (Natural, Natural));
random_Fset i = random_aux_Fset i i;

term_of_Nat :: Nata -> Term;
term_of_Nat (Suca a) =
  App (Const "Fset.Nat.Suc"
        (Typerep "fun" [Typerep "Fset.Nat" [], Typerep "Fset.Nat" []]))
    (term_of_Nat a);
term_of_Nat Zero = Const "Fset.Nat.Zero" (Typerep "Fset.Nat" []);

typerep_Nat :: Itself Nata -> Typerepa;
typerep_Nat t = Typerep "Fset.Nat" [];

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

term_of_Fset :: forall a. (Term_of a) => Fset a -> Term;
term_of_Fset (Set a) =
  App (Const "Fset.Fset.Set"
        (Typerep "fun"
          [Typerep "List.list" [(typerep :: Itself a -> Typerepa) Type],
            Typerep "Fset.Fset" [(typerep :: Itself a -> Typerepa) Type]]))
    (term_of_list a);

typerep_Fset :: forall a. (Typerep a) => Itself (Fset a) -> Typerepa;
typerep_Fset t = Typerep "Fset.Fset" [(typerep :: Itself a -> Typerepa) Type];

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

full_exhaustive_Nat ::
  ((Nata, () -> Term) -> Maybe (Bool, [Term])) ->
    Natural -> Maybe (Bool, [Term]);
full_exhaustive_Nat f i =
  (if less_natural zero_natural i
    then (case f (Zero, (\ _ -> Const "Fset.Nat.Zero" (Typerep "Fset.Nat" [])))
           of {
           Nothing ->
             full_exhaustive_Nat
               (\ (uu, uua) ->
                 f (Suca uu,
                     (\ _ ->
                       App (Const "Fset.Nat.Suc"
                             (Typerep "fun"
                               [Typerep "Fset.Nat" [], Typerep "Fset.Nat" []]))
                         (uua ()))))
               (minus_natural i one_natural);
           Just a -> Just a;
         })
    else Nothing);

partial_term_of_Nat :: Itself Nata -> Narrowing_term -> Term;
partial_term_of_Nat ty (Narrowing_constructor (1 :: Integer) [a]) =
  App (Const "Fset.Nat.Suc"
        (Typerep "fun" [Typerep "Fset.Nat" [], Typerep "Fset.Nat" []]))
    (partial_term_of_Nat Type a);
partial_term_of_Nat ty (Narrowing_constructor (0 :: Integer) []) =
  Const "Fset.Nat.Zero" (Typerep "Fset.Nat" []);
partial_term_of_Nat ty (Narrowing_variable p tt) =
  Free "_" (Typerep "Fset.Nat" []);

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

full_exhaustive_Fset ::
  forall a.
    (Full_exhaustive a) => ((Fset a, () -> Term) -> Maybe (Bool, [Term])) ->
                             Natural -> Maybe (Bool, [Term]);
full_exhaustive_Fset f i =
  (if less_natural zero_natural i
    then full_exhaustive_list
           (\ (uu, uua) ->
             f (Set uu,
                 (\ _ ->
                   App (Const "Fset.Fset.Set"
                         (Typerep "fun"
                           [Typerep "List.list"
                              [(typerep :: Itself a -> Typerepa) Type],
                             Typerep "Fset.Fset"
                               [(typerep :: Itself a -> Typerepa) Type]]))
                     (uua ()))))
           (minus_natural i one_natural)
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

partial_term_of_Fset ::
  forall a. (Partial_term_of a) => Itself (Fset a) -> Narrowing_term -> Term;
partial_term_of_Fset ty (Narrowing_constructor (0 :: Integer) [a]) =
  App (Const "Fset.Fset.Set"
        (Typerep "fun"
          [Typerep "List.list" [(typerep :: Itself a -> Typerepa) Type],
            Typerep "Fset.Fset" [(typerep :: Itself a -> Typerepa) Type]]))
    ((partial_term_of_list :: Itself [a] -> Narrowing_term -> Term) Type a);
partial_term_of_Fset ty (Narrowing_variable p tt) =
  Free "_" (Typerep "Fset.Fset" [(typerep :: Itself a -> Typerepa) Type]);

typerep_Nat_IITN_Nat :: Itself Nat_IITN_Nat -> Typerepa;
typerep_Nat_IITN_Nat t = Typerep "Fset.Nat.Nat_IITN_Nat" [];

typerep_Fset_IITN_Fset ::
  forall a. (Typerep a) => Itself (Fset_IITN_Fset a) -> Typerepa;
typerep_Fset_IITN_Fset t =
  Typerep "Fset.Fset.Fset_IITN_Fset" [(typerep :: Itself a -> Typerepa) Type];

}
