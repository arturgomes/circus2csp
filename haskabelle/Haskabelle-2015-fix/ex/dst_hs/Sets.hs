{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Sets(Ord(..), Natural(..), integer_of_natural, plus_natural, Plus(..),
        zero_natural, Zero(..), Monoid_add, Times(..), Div(..), One(..),
        Numeral, Minus(..), Typerepa(..), Term(..), Itself(..), Typerep(..),
        Term_of(..), Random(..), Semiring_numeral_div, Narrowing_type(..),
        Narrowing_term(..), Partial_term_of(..), Full_exhaustive(..),
        Narrowing_cons(..), Narrowing(..), Nat(..), Num(..), Set(..), Nata(..),
        Seta(..), Nibble(..), Char(..), Nat_IITN_Nat, Set_IITN_Set, bitM, ball,
        bex, balla, foldr, less_eq_natural, less_natural, one_natural,
        sgn_integer, abs_integer, apsnd, divmod_integer, div_integer,
        div_natural, log, removeAll, member, inserta, insert, eq_nat, membera,
        uniona, union, image, intersect, intera, inter, times_natural,
        mod_integer, mod_natural, max, natural_of_integer, minus_natural,
        minus_shift, next, pick, less_eq_set, eq_set, unionb, scomp,
        equal_natural, iterate, range, project, is_empty, less_set, bot_set,
        set_Set, pred_Set, minus_set, rec_Nat, map_Set, rec_Set, rel_Set,
        plus_nat, size_Nat, size_Set, collapse, valapp, listsum, select_weight,
        random_aux_Nat, random_aux_Set, sum, numeral, less_num, less_eq_num,
        cons, plus_num, size_Nata, size_Seta, equal_num, times_num, equal_Nat,
        equal_Set, non_empty, random_Nat, random_Set, term_of_Nat, term_of_Set,
        typerep_Nat, typerep_Set, one_integer, divmod_step, divmod,
        full_exhaustive_Nat, full_exhaustive_Set, partial_term_of_Nat,
        partial_term_of_Set, typerep_Nat_IITN_Nat, typerep_Set_IITN_Set)
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

data Narrowing_cons a = Narrowing_cons Narrowing_type [[Narrowing_term] -> a];

class Narrowing a where {
  narrowing :: Integer -> Narrowing_cons a;
};

data Nat = Zero_nat | Suc Nat;

data Num = One | Bit0 Num | Bit1 Num;

data Set a = Set [a] | Coset [a];

data Nata = Suca Nata | Zero;

data Seta a = Insert a (Seta a) | Empty;

data Nibble = Nibble0 | Nibble1 | Nibble2 | Nibble3 | Nibble4 | Nibble5
  | Nibble6 | Nibble7 | Nibble8 | Nibble9 | NibbleA | NibbleB | NibbleC
  | NibbleD | NibbleE | NibbleF;

data Char = Char Nibble Nibble;

data Nat_IITN_Nat;

data Set_IITN_Set a;

bitM :: Num -> Num;
bitM One = One;
bitM (Bit0 n) = Bit1 (bitM n);
bitM (Bit1 n) = Bit1 (Bit0 n);

ball :: forall a. Set a -> (a -> Bool) -> Bool;
ball (Set xs) p = all p xs;

bex :: forall a. Seta a -> (a -> Bool) -> Bool;
bex Empty p = False;
bex (Insert a aa) p = p a || bex aa p;

balla :: forall a. Seta a -> (a -> Bool) -> Bool;
balla Empty p = True;
balla (Insert a aa) p = p a && balla aa p;

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

eq_nat :: Nata -> Nata -> Bool;
eq_nat Zero Zero = True;
eq_nat (Suca m) (Suca n) = eq_nat m n;
eq_nat Zero (Suca a) = False;
eq_nat (Suca a) Zero = False;

membera :: Nata -> Seta Nata -> Bool;
membera a aa = bex aa (eq_nat a);

uniona :: Seta Nata -> Seta Nata -> Seta Nata;
uniona a Empty = a;
uniona Empty (Insert v va) = Insert v va;
uniona (Insert a aa) (Insert v va) =
  let {
    c = uniona aa (Insert v va);
  } in (if membera a (Insert v va) then c else Insert a c);

union :: forall a. Seta a -> (a -> Seta Nata) -> Seta Nata;
union Empty f = Empty;
union (Insert a aa) f = uniona (f a) (union aa f);

image :: forall a. (a -> Nata) -> Seta a -> Seta Nata;
image f a = union a (\ x -> Insert (f x) Empty);

intersect :: Seta Nata -> Seta Nata -> Seta Nata;
intersect a Empty = Empty;
intersect Empty (Insert v va) = Empty;
intersect (Insert a aa) (Insert v va) =
  let {
    c = intersect aa (Insert v va);
  } in (if membera a (Insert v va) then Insert a c else c);

intera :: forall a. Seta a -> (a -> Seta Nata) -> Seta Nata;
intera (Insert a Empty) f = f a;
intera (Insert a (Insert v va)) f = intersect (f a) (intera (Insert v va) f);

inter :: Seta (Seta Nata) -> Seta Nata;
inter a = intera a (\ x -> x);

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

less_eq_set :: Seta Nata -> Seta Nata -> Bool;
less_eq_set a b = balla a (\ x -> membera x b);

eq_set :: Seta Nata -> Seta Nata -> Bool;
eq_set a b = less_eq_set a b && less_eq_set b a;

unionb :: Seta (Seta Nata) -> Seta Nata;
unionb a = union a (\ x -> x);

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

project :: (Nata -> Bool) -> Seta Nata -> Seta Nata;
project p a = union a (\ aa -> (if p aa then Insert aa Empty else Empty));

is_empty :: forall a. Seta a -> Bool;
is_empty Empty = True;
is_empty (Insert a aa) = False;

less_set :: Seta Nata -> Seta Nata -> Bool;
less_set a b = less_eq_set a b && not (less_eq_set b a);

bot_set :: forall a. Set a;
bot_set = Set [];

set_Set :: forall a. (Eq a) => Seta a -> Set a;
set_Set (Insert x11 x12) = insert x11 (set_Set x12);
set_Set Empty = bot_set;

pred_Set :: forall a. (Eq a) => (a -> Bool) -> Seta a -> Bool;
pred_Set p = (\ x -> ball (set_Set x) p);

minus_set :: Seta Nata -> Seta Nata -> Seta Nata;
minus_set a Empty = a;
minus_set Empty (Insert v va) = Empty;
minus_set (Insert a aa) (Insert v va) =
  let {
    c = minus_set aa (Insert v va);
  } in (if membera a (Insert v va) then c else Insert a c);

rec_Nat :: forall a. (Nata -> a -> a) -> a -> Nata -> a;
rec_Nat f1 f2 (Suca x1) = f1 x1 (rec_Nat f1 f2 x1);
rec_Nat f1 f2 Zero = f2;

map_Set :: forall a b. (a -> b) -> Seta a -> Seta b;
map_Set f (Insert x11 x12) = Insert (f x11) (map_Set f x12);
map_Set f Empty = Empty;

rec_Set :: forall a b. (a -> Seta a -> b -> b) -> b -> Seta a -> b;
rec_Set f1 f2 (Insert x11 x12) = f1 x11 x12 (rec_Set f1 f2 x12);
rec_Set f1 f2 Empty = f2;

rel_Set :: forall a b. (a -> b -> Bool) -> Seta a -> Seta b -> Bool;
rel_Set r (Insert x11 x12) Empty = False;
rel_Set r Empty (Insert x11 x12) = False;
rel_Set r (Insert x11 x12) (Insert y11 y12) = r x11 y11 && rel_Set r x12 y12;
rel_Set r Empty Empty = True;

plus_nat :: Nat -> Nat -> Nat;
plus_nat (Suc m) n = plus_nat m (Suc n);
plus_nat Zero_nat n = n;

size_Nat :: Nata -> Nat;
size_Nat (Suca x1) = plus_nat (size_Nat x1) (Suc Zero_nat);
size_Nat Zero = Zero_nat;

size_Set :: forall a. (a -> Nat) -> Seta a -> Nat;
size_Set x (Insert x11 x12) =
  plus_nat (plus_nat (x x11) (size_Set x x12)) (Suc Zero_nat);
size_Set x Empty = Zero_nat;

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
                        Const "Sets.Nat.Suc"
                          (Typerep "fun"
                            [Typerep "Sets.Nat" [], Typerep "Sets.Nat" []])))
                    x,
                   a)))),
        (one_natural,
          (\ a ->
            ((Zero, (\ _ -> Const "Sets.Nat.Zero" (Typerep "Sets.Nat" []))),
              a)))])
    s;

random_aux_Set ::
  forall a.
    (Random a) => Natural ->
                    Natural ->
                      (Natural, Natural) ->
                        ((Seta a, () -> Term), (Natural, Natural));
random_aux_Set i j s =
  collapse
    (select_weight
      [(i, scomp (random j)
             (\ x ->
               scomp (random_aux_Set (minus_natural i one_natural) j)
                 (\ y ->
                   (\ a ->
                     (valapp
                        (valapp
                          (Insert,
                            (\ _ ->
                              Const "Sets.Set.Insert"
                                (Typerep "fun"
                                  [(typerep :: Itself a -> Typerepa) Type,
                                    Typerep "fun"
                                      [Typerep "Sets.Set"
 [(typerep :: Itself a -> Typerepa) Type],
Typerep "Sets.Set" [(typerep :: Itself a -> Typerepa) Type]]])))
                          x)
                        y,
                       a))))),
        (one_natural,
          (\ a ->
            ((Empty,
               (\ _ ->
                 Const "Sets.Set.Empty"
                   (Typerep "Sets.Set"
                     [(typerep :: Itself a -> Typerepa) Type]))),
              a)))])
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
size_Nata (Suca x1) = plus_nat (size_Nata x1) (Suc Zero_nat);
size_Nata Zero = Zero_nat;

size_Seta :: forall a. Seta a -> Nat;
size_Seta (Insert x11 x12) = plus_nat (size_Seta x12) (Suc Zero_nat);
size_Seta Empty = Zero_nat;

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

equal_Set :: forall a. (Eq a) => Seta a -> Seta a -> Bool;
equal_Set (Insert x11 x12) Empty = False;
equal_Set Empty (Insert x11 x12) = False;
equal_Set (Insert x11 x12) (Insert y11 y12) = x11 == y11 && equal_Set x12 y12;
equal_Set Empty Empty = True;

non_empty :: Narrowing_type -> Bool;
non_empty (Narrowing_sum_of_products ps) = not (null ps);

random_Nat ::
  Natural -> (Natural, Natural) -> ((Nata, () -> Term), (Natural, Natural));
random_Nat i = random_aux_Nat i i;

random_Set ::
  forall a.
    (Random a) => Natural ->
                    (Natural, Natural) ->
                      ((Seta a, () -> Term), (Natural, Natural));
random_Set i = random_aux_Set i i;

term_of_Nat :: Nata -> Term;
term_of_Nat Zero = Const "Sets.Nat.Zero" (Typerep "Sets.Nat" []);
term_of_Nat (Suca a) =
  App (Const "Sets.Nat.Suc"
        (Typerep "fun" [Typerep "Sets.Nat" [], Typerep "Sets.Nat" []]))
    (term_of_Nat a);

term_of_Set :: forall a. (Term_of a) => Seta a -> Term;
term_of_Set Empty =
  Const "Sets.Set.Empty"
    (Typerep "Sets.Set" [(typerep :: Itself a -> Typerepa) Type]);
term_of_Set (Insert a b) =
  App (App (Const "Sets.Set.Insert"
             (Typerep "fun"
               [(typerep :: Itself a -> Typerepa) Type,
                 Typerep "fun"
                   [Typerep "Sets.Set" [(typerep :: Itself a -> Typerepa) Type],
                     Typerep "Sets.Set"
                       [(typerep :: Itself a -> Typerepa) Type]]]))
        (term_of a))
    (term_of_Set b);

typerep_Nat :: Itself Nata -> Typerepa;
typerep_Nat t = Typerep "Sets.Nat" [];

typerep_Set :: forall a. (Typerep a) => Itself (Seta a) -> Typerepa;
typerep_Set t = Typerep "Sets.Set" [(typerep :: Itself a -> Typerepa) Type];

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
    then (case full_exhaustive_Nat
                 (\ (uu, uua) ->
                   f (Suca uu,
                       (\ _ ->
                         App (Const "Sets.Nat.Suc"
                               (Typerep "fun"
                                 [Typerep "Sets.Nat" [],
                                   Typerep "Sets.Nat" []]))
                           (uua ()))))
                 (minus_natural i one_natural)
           of {
           Nothing ->
             f (Zero, (\ _ -> Const "Sets.Nat.Zero" (Typerep "Sets.Nat" [])));
           Just a -> Just a;
         })
    else Nothing);

full_exhaustive_Set ::
  forall a.
    (Full_exhaustive a) => ((Seta a, () -> Term) -> Maybe (Bool, [Term])) ->
                             Natural -> Maybe (Bool, [Term]);
full_exhaustive_Set f i =
  (if less_natural zero_natural i
    then (case full_exhaustive
                 (\ (uu, uua) ->
                   full_exhaustive_Set
                     (\ (uub, uuc) ->
                       f (Insert uu uub,
                           (\ _ ->
                             App (App (Const "Sets.Set.Insert"
(Typerep "fun"
  [(typerep :: Itself a -> Typerepa) Type,
    Typerep "fun"
      [Typerep "Sets.Set" [(typerep :: Itself a -> Typerepa) Type],
        Typerep "Sets.Set" [(typerep :: Itself a -> Typerepa) Type]]]))
                                   (uua ()))
                               (uuc ()))))
                     (minus_natural i one_natural))
                 (minus_natural i one_natural)
           of {
           Nothing ->
             f (Empty,
                 (\ _ ->
                   Const "Sets.Set.Empty"
                     (Typerep "Sets.Set"
                       [(typerep :: Itself a -> Typerepa) Type])));
           Just a -> Just a;
         })
    else Nothing);

partial_term_of_Nat :: Itself Nata -> Narrowing_term -> Term;
partial_term_of_Nat ty (Narrowing_constructor (1 :: Integer) []) =
  Const "Sets.Nat.Zero" (Typerep "Sets.Nat" []);
partial_term_of_Nat ty (Narrowing_constructor (0 :: Integer) [a]) =
  App (Const "Sets.Nat.Suc"
        (Typerep "fun" [Typerep "Sets.Nat" [], Typerep "Sets.Nat" []]))
    (partial_term_of_Nat Type a);
partial_term_of_Nat ty (Narrowing_variable p tt) =
  Free "_" (Typerep "Sets.Nat" []);

partial_term_of_Set ::
  forall a. (Partial_term_of a) => Itself (Seta a) -> Narrowing_term -> Term;
partial_term_of_Set ty (Narrowing_constructor (1 :: Integer) []) =
  Const "Sets.Set.Empty"
    (Typerep "Sets.Set" [(typerep :: Itself a -> Typerepa) Type]);
partial_term_of_Set ty (Narrowing_constructor (0 :: Integer) [b, a]) =
  App (App (Const "Sets.Set.Insert"
             (Typerep "fun"
               [(typerep :: Itself a -> Typerepa) Type,
                 Typerep "fun"
                   [Typerep "Sets.Set" [(typerep :: Itself a -> Typerepa) Type],
                     Typerep "Sets.Set"
                       [(typerep :: Itself a -> Typerepa) Type]]]))
        ((partial_term_of :: Itself a -> Narrowing_term -> Term) Type a))
    ((partial_term_of_Set :: Itself (Seta a) -> Narrowing_term -> Term) Type b);
partial_term_of_Set ty (Narrowing_variable p tt) =
  Free "_" (Typerep "Sets.Set" [(typerep :: Itself a -> Typerepa) Type]);

typerep_Nat_IITN_Nat :: Itself Nat_IITN_Nat -> Typerepa;
typerep_Nat_IITN_Nat t = Typerep "Sets.Nat.Nat_IITN_Nat" [];

typerep_Set_IITN_Set ::
  forall a. (Typerep a) => Itself (Set_IITN_Set a) -> Typerepa;
typerep_Set_IITN_Set t =
  Typerep "Sets.Set.Set_IITN_Set" [(typerep :: Itself a -> Typerepa) Type];

}
