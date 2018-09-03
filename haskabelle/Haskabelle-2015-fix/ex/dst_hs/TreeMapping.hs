{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  TreeMapping(less_eq_bool, less_bool, bot_bool, Orda(..), Bot(..), Ord(..),
               Natural(..), integer_of_natural, plus_natural, Plus(..),
               zero_natural, Zero(..), Monoid_add, Times(..), Div(..), One(..),
               Numeral, Minus(..), Linordera, Typerepa(..), Term(..),
               Itself(..), Typerep(..), Term_of(..), Random(..),
               Semiring_numeral_div, Narrowing_type(..), Narrowing_term(..),
               Partial_term_of(..), Full_exhaustive(..), Eqa(..),
               Narrowing_cons(..), Narrowing(..), Nat(..), Num(..), Set(..),
               Nibble(..), Char(..), Tree(..), Map(..), Nata(..), Itselfa(..),
               Map_IITN_Map, Nat_IITN_Nat, Tree_pre_Tree, Tree_IITN_Tree,
               Itself_pre_Itself, Itself_IITN_Itself, bitM, ball, fold, foldr,
               less_eq_natural, less_natural, one_natural, sgn_integer,
               abs_integer, apsnd, divmod_integer, div_integer, div_natural,
               log, removeAll, membera, inserta, insert, member, times_natural,
               mod_integer, mod_natural, max, natural_of_integer, minus_natural,
               minus_shift, next, pick, scomp, equal_natural, iterate, range,
               nth, bot_fun, insertb, set, memberb, remdups, lookupb, is_none,
               filtera, append, keysa, keys, mapa, plus_nat, size_list, sizea,
               size, insort, sort, dropa, empty, takea, eq_nat, foldla, updatea,
               update, eq_tree, lookupa, replace, listsum, select_weight,
               less_nat, less_eq_nat, sup_set, bot_set, set2_Tree, set2_Map,
               set1_Tree, set1_Map, pred_Map, minus_nat, pred_Tree, valapp,
               map_Tree, map_Map, rec_Map, rel_Tree, rel_Map, rec_Nat,
               set_Itself, pred_Itself, sum, plus_nata, size_Tree, size_Map,
               size_Nat, numeral, less_num, less_eq_num, cons, rec_Tree,
               plus_num, collapse, random_aux_Tree, random_Tree, random_aux_Map,
               random_aux_Nat, equal_num, times_num, map_Itself, rec_Itself,
               rel_Itself, random_aux_Itself, non_empty, size_Itself,
               size_Treea, size_Mapa, size_Nata, equal_Tree, equal_Map,
               equal_Nat, random_Map, random_Nat, size_Itselfa, term_of_Tree,
               term_of_Map, term_of_Nat, typerep_Map, typerep_Nat, one_integer,
               divmod_step, divmod, equal_Itself, typerep_Tree, random_Itself,
               term_of_Itself, typerep_Itself, narrowing_Itself,
               full_exhaustive_Tree, full_exhaustive_Map, full_exhaustive_Nat,
               partial_term_of_Tree, partial_term_of_Map, partial_term_of_Nat,
               typerep_Map_IITN_Map, typerep_Nat_IITN_Nat,
               full_exhaustive_Itself, partial_term_of_Itself,
               typerep_Tree_pre_Tree, typerep_Tree_IITN_Tree,
               typerep_Itself_pre_Itself, typerep_Itself_IITN_Itself)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;

less_eq_bool :: Bool -> Bool -> Bool;
less_eq_bool True b = b;
less_eq_bool False b = True;

less_bool :: Bool -> Bool -> Bool;
less_bool True b = False;
less_bool False b = b;

bot_bool :: Bool;
bot_bool = False;

class Orda a where {
  less_eqa :: a -> a -> Bool;
  lessa :: a -> a -> Bool;
};

class (Orda a) => Preordera a where {
};

class (Preordera a) => Bot a where {
  bot :: a;
};

instance Orda Bool where {
  less_eqa = less_eq_bool;
  lessa = less_bool;
};

instance Preordera Bool where {
};

instance Bot Bool where {
  bot = bot_bool;
};

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

class (Preordera a) => Ordera a where {
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

data Tree a b = Empty | Branch b a (Tree a b) (Tree a b);

newtype Map a b = Tree (Tree a b);

data Nata = Zero | Suca Nata;

data Itselfa a = Typea;

data Map_IITN_Map a b;

data Nat_IITN_Nat;

data Tree_pre_Tree a b c;

data Tree_IITN_Tree a b;

data Itself_pre_Itself a b;

data Itself_IITN_Itself a;

bitM :: Num -> Num;
bitM One = One;
bitM (Bit0 n) = Bit1 (bitM n);
bitM (Bit1 n) = Bit1 (Bit0 n);

ball :: forall a. Set a -> (a -> Bool) -> Bool;
ball (Set xs) p = all p xs;

fold :: forall a b. (a -> b -> b) -> [a] -> b -> b;
fold f (x : xs) s = fold f xs (f x s);
fold f [] s = s;

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

nth :: forall a. [a] -> Nata -> a;
nth (x : xs) (Suca n) = nth xs n;
nth (x : xs) Zero = x;

bot_fun :: forall a b. (Bot b) => a -> b;
bot_fun = (\ _ -> bot);

insertb :: forall a. (Eqa a) => a -> (a -> Bool) -> a -> Bool;
insertb y a x = eq y x || a x;

set :: forall a. (Eqa a) => [a] -> a -> Bool;
set [] = bot_fun;
set (x : xs) = insertb x (set xs);

memberb :: forall a. (Eqa a) => a -> [a] -> Bool;
memberb x [] = False;
memberb x (y : ys) = eq x y || memberb x ys;

remdups :: forall a. (Eqa a) => [a] -> [a];
remdups [] = [];
remdups (x : xs) = (if memberb x xs then remdups xs else x : remdups xs);

lookupb :: forall a b. (Eqa a, Linordera a) => Tree a b -> a -> Maybe b;
lookupb Empty = (\ _ -> Nothing);
lookupb (Branch v k l r) =
  (\ ka ->
    (if eq ka k then Just v
      else (if less_eqa ka k then lookupb l ka else lookupb r ka)));

is_none :: forall a. Maybe a -> Bool;
is_none (Just x) = False;
is_none Nothing = True;

filtera :: forall a. (a -> Bool) -> [a] -> [a];
filtera p [] = [];
filtera p (x : xs) = (if p x then x : filtera p xs else filtera p xs);

append :: forall a. [a] -> [a] -> [a];
append [] ys = ys;
append (x : xs) ys = x : append xs ys;

keysa :: forall a b. (Linordera a) => Tree a b -> [a];
keysa Empty = [];
keysa (Branch uu k l r) = k : append (keysa l) (keysa r);

keys :: forall a b. (Eqa a, Linordera a) => Map a b -> a -> Bool;
keys (Tree t) =
  set (filtera (\ k -> not (is_none (lookupb t k))) (remdups (keysa t)));

mapa :: forall a b. (a -> b) -> [a] -> [b];
mapa f [] = [];
mapa f (x : xs) = f x : mapa f xs;

plus_nat :: Nata -> Nata -> Nata;
plus_nat (Suca m) n = plus_nat m (Suca n);
plus_nat Zero n = n;

size_list :: forall a. [a] -> Nata;
size_list [] = Zero;
size_list (a : list) = plus_nat (size_list list) (Suca Zero);

sizea :: forall a b. (Eqa a, Linordera a) => Tree a b -> Nata;
sizea t =
  size_list
    (filtera (\ x -> not (is_none x)) (mapa (lookupb t) (remdups (keysa t))));

size :: forall a b. (Eqa a, Linordera a) => Map a b -> Nata;
size (Tree t) = sizea t;

insort :: forall a. (Linordera a) => a -> [a] -> [a];
insort x [] = [x];
insort x (y : ys) = (if less_eqa x y then x : y : ys else y : insort x ys);

sort :: forall a. (Linordera a) => [a] -> [a];
sort [] = [];
sort (x : xs) = insort x (sort xs);

dropa :: forall a. Nata -> [a] -> [a];
dropa n [] = [];
dropa n (x : xs) = (case n of {
                     Zero -> x : xs;
                     Suca m -> dropa m xs;
                   });

empty :: forall a b. (Linordera a) => Map a b;
empty = Tree Empty;

takea :: forall a. Nata -> [a] -> [a];
takea n [] = [];
takea n (x : xs) = (case n of {
                     Zero -> [];
                     Suca m -> x : takea m xs;
                   });

eq_nat :: Nata -> Nata -> Bool;
eq_nat (Suca nat) Zero = False;
eq_nat Zero (Suca nat) = False;
eq_nat (Suca nat0) (Suca nat) = eq_nat nat0 nat;
eq_nat Zero Zero = True;

foldla :: forall a b. (a -> b -> a) -> a -> [b] -> a;
foldla f a [] = a;
foldla f a (x : xs) = foldla f (f a x) xs;

updatea :: forall a b. (Eqa a, Linordera a) => a -> b -> Tree a b -> Tree a b;
updatea k v Empty = Branch v k Empty Empty;
updatea ka va (Branch v k l r) =
  (if eq ka k then Branch va k l r
    else (if less_eqa ka k then Branch v k (updatea ka va l) r
           else Branch v k l (updatea ka va r)));

update :: forall a b. (Eqa a, Linordera a) => a -> b -> Map a b -> Map a b;
update k v (Tree t) = Tree (updatea k v t);

eq_tree :: forall a b. (Eqa a, Eqa b) => Tree a b -> Tree a b -> Bool;
eq_tree (Branch b a tree1 tree2) Empty = False;
eq_tree Empty (Branch b a tree1 tree2) = False;
eq_tree (Branch ba aa tree1a tree2a) (Branch b a tree1 tree2) =
  eq ba b && eq aa a && eq_tree tree1a tree1 && eq_tree tree2a tree2;
eq_tree Empty Empty = True;

lookupa :: forall a b. (Eqa a, Linordera a) => Map a b -> a -> Maybe b;
lookupa (Tree t) = lookupb t;

replace :: forall a b. (Eqa a, Linordera a) => a -> b -> Map a b -> Map a b;
replace k v m = (if is_none (lookupa m k) then m else update k v m);

listsum :: forall a. (Monoid_add a) => [a] -> a;
listsum xs = foldr plus xs zero;

select_weight ::
  forall a. [(Natural, a)] -> (Natural, Natural) -> (a, (Natural, Natural));
select_weight xs =
  scomp (range (listsum (map fst xs))) (\ k -> (\ a -> (pick xs k, a)));

less_nat :: Nata -> Nata -> Bool;
less_nat m (Suca n) = less_eq_nat m n;
less_nat n Zero = False;

less_eq_nat :: Nata -> Nata -> Bool;
less_eq_nat (Suca m) n = less_nat m n;
less_eq_nat Zero n = True;

sup_set :: forall a. (Eq a) => Set a -> Set a -> Set a;
sup_set (Coset xs) a = Coset (filter (\ x -> not (member x a)) xs);
sup_set (Set xs) a = fold insert xs a;

bot_set :: forall a. Set a;
bot_set = Set [];

set2_Tree :: forall a b. (Eq b) => Tree a b -> Set b;
set2_Tree Empty = bot_set;
set2_Tree (Branch x21 x22 x23 x24) =
  insert x21 (sup_set (set2_Tree x23) (set2_Tree x24));

set2_Map :: forall a b. (Eq b) => Map a b -> Set b;
set2_Map (Tree x) = set2_Tree x;

set1_Tree :: forall a b. (Eq a) => Tree a b -> Set a;
set1_Tree Empty = bot_set;
set1_Tree (Branch x21 x22 x23 x24) =
  insert x22 (sup_set (set1_Tree x23) (set1_Tree x24));

set1_Map :: forall a b. (Eq a) => Map a b -> Set a;
set1_Map (Tree x) = set1_Tree x;

pred_Map ::
  forall a b. (Eq a, Eq b) => (a -> Bool) -> (b -> Bool) -> Map a b -> Bool;
pred_Map p1 p2 = (\ x -> ball (set1_Map x) p1 && ball (set2_Map x) p2);

minus_nat :: Nata -> Nata -> Nata;
minus_nat (Suca m) (Suca n) = minus_nat m n;
minus_nat Zero n = Zero;
minus_nat (Suca v) Zero = Suca v;

pred_Tree ::
  forall a b. (Eq a, Eq b) => (a -> Bool) -> (b -> Bool) -> Tree a b -> Bool;
pred_Tree p1 p2 = (\ x -> ball (set1_Tree x) p1 && ball (set2_Tree x) p2);

valapp ::
  forall a b. (a -> b, () -> Term) -> (a, () -> Term) -> (b, () -> Term);
valapp (f, tf) (x, tx) = (f x, (\ _ -> App (tf ()) (tx ())));

map_Tree :: forall a b c d. (a -> b) -> (c -> d) -> Tree a c -> Tree b d;
map_Tree f1 f2 Empty = Empty;
map_Tree f1 f2 (Branch x21 x22 x23 x24) =
  Branch (f2 x21) (f1 x22) (map_Tree f1 f2 x23) (map_Tree f1 f2 x24);

map_Map :: forall a b c d. (a -> b) -> (c -> d) -> Map a c -> Map b d;
map_Map f1 f2 (Tree x) = Tree (map_Tree f1 f2 x);

rec_Map :: forall a b c. (Tree a b -> c) -> Map a b -> c;
rec_Map f (Tree x) = f x;

rel_Tree ::
  forall a b c d.
    (a -> b -> Bool) -> (c -> d -> Bool) -> Tree a c -> Tree b d -> Bool;
rel_Tree r1 r2 Empty (Branch y21 y22 y23 y24) = False;
rel_Tree r1 r2 (Branch y21 y22 y23 y24) Empty = False;
rel_Tree r1 r2 Empty Empty = True;
rel_Tree r1 r2 (Branch x21 x22 x23 x24) (Branch y21 y22 y23 y24) =
  r2 x21 y21 && r1 x22 y22 && rel_Tree r1 r2 x23 y23 && rel_Tree r1 r2 x24 y24;

rel_Map ::
  forall a b c d.
    (a -> b -> Bool) -> (c -> d -> Bool) -> Map a c -> Map b d -> Bool;
rel_Map r1 r2 (Tree x) (Tree y) = rel_Tree r1 r2 x y;

rec_Nat :: forall a. a -> (Nata -> a -> a) -> Nata -> a;
rec_Nat f1 f2 Zero = f1;
rec_Nat f1 f2 (Suca x2) = f2 x2 (rec_Nat f1 f2 x2);

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

size_Tree :: forall a b. (a -> Nat) -> (b -> Nat) -> Tree a b -> Nat;
size_Tree xa x Empty = Zero_nat;
size_Tree xa x (Branch x21 x22 x23 x24) =
  plus_nata
    (plus_nata (plus_nata (plus_nata (x x21) (xa x22)) (size_Tree xa x x23))
      (size_Tree xa x x24))
    (Suc Zero_nat);

size_Map :: forall a b. (a -> Nat) -> (b -> Nat) -> Map a b -> Nat;
size_Map xb xa (Tree x) = plus_nata (size_Tree xb xa x) (Suc Zero_nat);

size_Nat :: Nata -> Nat;
size_Nat Zero = Zero_nat;
size_Nat (Suca x2) = plus_nata (size_Nat x2) (Suc Zero_nat);

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

rec_Tree ::
  forall a b c.
    a -> (b -> c -> Tree c b -> Tree c b -> a -> a -> a) -> Tree c b -> a;
rec_Tree f1 f2 Empty = f1;
rec_Tree f1 f2 (Branch x21 x22 x23 x24) =
  f2 x21 x22 x23 x24 (rec_Tree f1 f2 x23) (rec_Tree f1 f2 x24);

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

random_aux_Tree ::
  forall a b.
    (Random a,
      Random b) => Natural ->
                     Natural ->
                       (Natural, Natural) ->
                         ((Tree a b, () -> Term), (Natural, Natural));
random_aux_Tree i j s =
  collapse
    (select_weight
      [(i, scomp (random j)
             (\ x ->
               scomp (random j)
                 (\ y ->
                   scomp (random_aux_Tree (minus_natural i one_natural) j)
                     (\ z ->
                       scomp (random_aux_Tree (minus_natural i one_natural) j)
                         (\ aa ->
                           (\ a ->
                             (valapp
                                (valapp
                                  (valapp
                                    (valapp
                                      (Branch,
(\ _ ->
  Const "TreeMapping.Tree.Branch"
    (Typerep "fun"
      [(typerep :: Itself b -> Typerepa) Type,
        Typerep "fun"
          [(typerep :: Itself a -> Typerepa) Type,
            Typerep "fun"
              [Typerep "TreeMapping.Tree"
                 [(typerep :: Itself a -> Typerepa) Type,
                   (typerep :: Itself b -> Typerepa) Type],
                Typerep "fun"
                  [Typerep "TreeMapping.Tree"
                     [(typerep :: Itself a -> Typerepa) Type,
                       (typerep :: Itself b -> Typerepa) Type],
                    Typerep "TreeMapping.Tree"
                      [(typerep :: Itself a -> Typerepa) Type,
                        (typerep :: Itself b -> Typerepa) Type]]]]])))
                                      x)
                                    y)
                                  z)
                                aa,
                               a))))))),
        (one_natural,
          (\ a ->
            ((Empty,
               (\ _ ->
                 Const "TreeMapping.Tree.Empty"
                   (Typerep "TreeMapping.Tree"
                     [(typerep :: Itself a -> Typerepa) Type,
                       (typerep :: Itself b -> Typerepa) Type]))),
              a)))])
    s;

random_Tree ::
  forall a b.
    (Random a,
      Random b) => Natural ->
                     (Natural, Natural) ->
                       ((Tree a b, () -> Term), (Natural, Natural));
random_Tree i = random_aux_Tree i i;

random_aux_Map ::
  forall a b.
    (Random a,
      Random b) => Natural ->
                     Natural ->
                       (Natural, Natural) ->
                         ((Map a b, () -> Term), (Natural, Natural));
random_aux_Map i j s =
  collapse
    (select_weight
      [(one_natural,
         scomp (random_Tree j)
           (\ x ->
             (\ a ->
               (valapp
                  (Tree,
                    (\ _ ->
                      Const "TreeMapping.Map.Tree"
                        (Typerep "fun"
                          [Typerep "TreeMapping.Tree"
                             [(typerep :: Itself a -> Typerepa) Type,
                               (typerep :: Itself b -> Typerepa) Type],
                            Typerep "TreeMapping.Map"
                              [(typerep :: Itself a -> Typerepa) Type,
                                (typerep :: Itself b -> Typerepa) Type]])))
                  x,
                 a))))])
    s;

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
                        Const "TreeMapping.Nat.Suc"
                          (Typerep "fun"
                            [Typerep "TreeMapping.Nat" [],
                              Typerep "TreeMapping.Nat" []])))
                    x,
                   a)))),
        (one_natural,
          (\ a ->
            ((Zero,
               (\ _ ->
                 Const "TreeMapping.Nat.Zero" (Typerep "TreeMapping.Nat" []))),
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

map_Itself :: forall a b. (a -> b) -> Itselfa a -> Itselfa b;
map_Itself f Typea = Typea;

rec_Itself :: forall a b. a -> Itselfa b -> a;
rec_Itself f Typea = f;

rel_Itself :: forall a b. (a -> b -> Bool) -> Itselfa a -> Itselfa b -> Bool;
rel_Itself r Typea Typea = True;

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
                Const "TreeMapping.Itself.Type"
                  (Typerep "TreeMapping.Itself"
                    [(typerep :: Itself a -> Typerepa) Type]))),
             a)))])
    s;

non_empty :: Narrowing_type -> Bool;
non_empty (Narrowing_sum_of_products ps) = not (null ps);

size_Itself :: forall a. (a -> Nat) -> Itselfa a -> Nat;
size_Itself x Typea = Zero_nat;

size_Treea :: forall a b. Tree a b -> Nat;
size_Treea Empty = Zero_nat;
size_Treea (Branch x21 x22 x23 x24) =
  plus_nata (plus_nata (size_Treea x23) (size_Treea x24)) (Suc Zero_nat);

size_Mapa :: forall a b. Map a b -> Nat;
size_Mapa (Tree x) = plus_nata (size_Treea x) (Suc Zero_nat);

size_Nata :: Nata -> Nat;
size_Nata Zero = Zero_nat;
size_Nata (Suca x2) = plus_nata (size_Nata x2) (Suc Zero_nat);

equal_Tree :: forall a b. (Eq a, Eq b) => Tree a b -> Tree a b -> Bool;
equal_Tree Empty (Branch x21 x22 x23 x24) = False;
equal_Tree (Branch x21 x22 x23 x24) Empty = False;
equal_Tree (Branch x21 x22 x23 x24) (Branch y21 y22 y23 y24) =
  x21 == y21 && x22 == y22 && equal_Tree x23 y23 && equal_Tree x24 y24;
equal_Tree Empty Empty = True;

equal_Map :: forall a b. (Eq a, Eq b) => Map a b -> Map a b -> Bool;
equal_Map (Tree x) (Tree ya) = equal_Tree x ya;

equal_Nat :: Nata -> Nata -> Bool;
equal_Nat Zero (Suca x2) = False;
equal_Nat (Suca x2) Zero = False;
equal_Nat (Suca x2) (Suca y2) = equal_Nat x2 y2;
equal_Nat Zero Zero = True;

random_Map ::
  forall a b.
    (Random a,
      Random b) => Natural ->
                     (Natural, Natural) ->
                       ((Map a b, () -> Term), (Natural, Natural));
random_Map i = random_aux_Map i i;

random_Nat ::
  Natural -> (Natural, Natural) -> ((Nata, () -> Term), (Natural, Natural));
random_Nat i = random_aux_Nat i i;

size_Itselfa :: forall a. Itselfa a -> Nat;
size_Itselfa Typea = Zero_nat;

term_of_Tree :: forall a b. (Term_of a, Term_of b) => Tree a b -> Term;
term_of_Tree (Branch a b c d) =
  App (App (App (App (Const "TreeMapping.Tree.Branch"
                       (Typerep "fun"
                         [(typerep :: Itself b -> Typerepa) Type,
                           Typerep "fun"
                             [(typerep :: Itself a -> Typerepa) Type,
                               Typerep "fun"
                                 [Typerep "TreeMapping.Tree"
                                    [(typerep :: Itself a -> Typerepa) Type,
                                      (typerep :: Itself b -> Typerepa) Type],
                                   Typerep "fun"
                                     [Typerep "TreeMapping.Tree"
[(typerep :: Itself a -> Typerepa) Type,
  (typerep :: Itself b -> Typerepa) Type],
                                       Typerep "TreeMapping.Tree"
 [(typerep :: Itself a -> Typerepa) Type,
   (typerep :: Itself b -> Typerepa) Type]]]]]))
                  (term_of a))
             (term_of b))
        (term_of_Tree c))
    (term_of_Tree d);
term_of_Tree Empty =
  Const "TreeMapping.Tree.Empty"
    (Typerep "TreeMapping.Tree"
      [(typerep :: Itself a -> Typerepa) Type,
        (typerep :: Itself b -> Typerepa) Type]);

term_of_Map :: forall a b. (Term_of a, Term_of b) => Map a b -> Term;
term_of_Map (Tree a) =
  App (Const "TreeMapping.Map.Tree"
        (Typerep "fun"
          [Typerep "TreeMapping.Tree"
             [(typerep :: Itself a -> Typerepa) Type,
               (typerep :: Itself b -> Typerepa) Type],
            Typerep "TreeMapping.Map"
              [(typerep :: Itself a -> Typerepa) Type,
                (typerep :: Itself b -> Typerepa) Type]]))
    (term_of_Tree a);

term_of_Nat :: Nata -> Term;
term_of_Nat (Suca a) =
  App (Const "TreeMapping.Nat.Suc"
        (Typerep "fun"
          [Typerep "TreeMapping.Nat" [], Typerep "TreeMapping.Nat" []]))
    (term_of_Nat a);
term_of_Nat Zero = Const "TreeMapping.Nat.Zero" (Typerep "TreeMapping.Nat" []);

typerep_Map ::
  forall a b. (Typerep a, Typerep b) => Itself (Map a b) -> Typerepa;
typerep_Map t =
  Typerep "TreeMapping.Map"
    [(typerep :: Itself a -> Typerepa) Type,
      (typerep :: Itself b -> Typerepa) Type];

typerep_Nat :: Itself Nata -> Typerepa;
typerep_Nat t = Typerep "TreeMapping.Nat" [];

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

equal_Itself :: forall a. Itselfa a -> Itselfa a -> Bool;
equal_Itself Typea Typea = True;

typerep_Tree ::
  forall a b. (Typerep a, Typerep b) => Itself (Tree a b) -> Typerepa;
typerep_Tree t =
  Typerep "TreeMapping.Tree"
    [(typerep :: Itself a -> Typerepa) Type,
      (typerep :: Itself b -> Typerepa) Type];

random_Itself ::
  forall a.
    (Typerep a) => Natural ->
                     (Natural, Natural) ->
                       ((Itselfa a, () -> Term), (Natural, Natural));
random_Itself i = random_aux_Itself i i;

term_of_Itself :: forall a. (Typerep a) => Itselfa a -> Term;
term_of_Itself Typea =
  Const "TreeMapping.Itself.Type"
    (Typerep "TreeMapping.Itself" [(typerep :: Itself a -> Typerepa) Type]);

typerep_Itself :: forall a. (Typerep a) => Itself (Itselfa a) -> Typerepa;
typerep_Itself t =
  Typerep "TreeMapping.Itself" [(typerep :: Itself a -> Typerepa) Type];

narrowing_Itself ::
  forall a. (Typerep a) => Integer -> Narrowing_cons (Itselfa a);
narrowing_Itself = cons Typea;

full_exhaustive_Tree ::
  forall a b.
    (Full_exhaustive a,
      Full_exhaustive b) => ((Tree a b, () -> Term) -> Maybe (Bool, [Term])) ->
                              Natural -> Maybe (Bool, [Term]);
full_exhaustive_Tree f i =
  (if less_natural zero_natural i
    then (case f (Empty,
                   (\ _ ->
                     Const "TreeMapping.Tree.Empty"
                       (Typerep "TreeMapping.Tree"
                         [(typerep :: Itself a -> Typerepa) Type,
                           (typerep :: Itself b -> Typerepa) Type])))
           of {
           Nothing ->
             full_exhaustive
               (\ (uu, uua) ->
                 full_exhaustive
                   (\ (uub, uuc) ->
                     full_exhaustive_Tree
                       (\ (uud, uue) ->
                         full_exhaustive_Tree
                           (\ (uuf, uug) ->
                             f (Branch uu uub uud uuf,
                                 (\ _ ->
                                   App (App
 (App (App (Const "TreeMapping.Tree.Branch"
             (Typerep "fun"
               [(typerep :: Itself b -> Typerepa) Type,
                 Typerep "fun"
                   [(typerep :: Itself a -> Typerepa) Type,
                     Typerep "fun"
                       [Typerep "TreeMapping.Tree"
                          [(typerep :: Itself a -> Typerepa) Type,
                            (typerep :: Itself b -> Typerepa) Type],
                         Typerep "fun"
                           [Typerep "TreeMapping.Tree"
                              [(typerep :: Itself a -> Typerepa) Type,
                                (typerep :: Itself b -> Typerepa) Type],
                             Typerep "TreeMapping.Tree"
                               [(typerep :: Itself a -> Typerepa) Type,
                                 (typerep :: Itself b -> Typerepa) Type]]]]]))
        (uua ()))
   (uuc ()))
 (uue ()))
                                     (uug ()))))
                           (minus_natural i one_natural))
                       (minus_natural i one_natural))
                   (minus_natural i one_natural))
               (minus_natural i one_natural);
           Just a -> Just a;
         })
    else Nothing);

full_exhaustive_Map ::
  forall a b.
    (Full_exhaustive a,
      Full_exhaustive b) => ((Map a b, () -> Term) -> Maybe (Bool, [Term])) ->
                              Natural -> Maybe (Bool, [Term]);
full_exhaustive_Map f i =
  (if less_natural zero_natural i
    then full_exhaustive_Tree
           (\ (uu, uua) ->
             f (Tree uu,
                 (\ _ ->
                   App (Const "TreeMapping.Map.Tree"
                         (Typerep "fun"
                           [Typerep "TreeMapping.Tree"
                              [(typerep :: Itself a -> Typerepa) Type,
                                (typerep :: Itself b -> Typerepa) Type],
                             Typerep "TreeMapping.Map"
                               [(typerep :: Itself a -> Typerepa) Type,
                                 (typerep :: Itself b -> Typerepa) Type]]))
                     (uua ()))))
           (minus_natural i one_natural)
    else Nothing);

full_exhaustive_Nat ::
  ((Nata, () -> Term) -> Maybe (Bool, [Term])) ->
    Natural -> Maybe (Bool, [Term]);
full_exhaustive_Nat f i =
  (if less_natural zero_natural i
    then (case f (Zero,
                   (\ _ ->
                     Const "TreeMapping.Nat.Zero"
                       (Typerep "TreeMapping.Nat" [])))
           of {
           Nothing ->
             full_exhaustive_Nat
               (\ (uu, uua) ->
                 f (Suca uu,
                     (\ _ ->
                       App (Const "TreeMapping.Nat.Suc"
                             (Typerep "fun"
                               [Typerep "TreeMapping.Nat" [],
                                 Typerep "TreeMapping.Nat" []]))
                         (uua ()))))
               (minus_natural i one_natural);
           Just a -> Just a;
         })
    else Nothing);

partial_term_of_Tree ::
  forall a b.
    (Partial_term_of a,
      Partial_term_of b) => Itself (Tree a b) -> Narrowing_term -> Term;
partial_term_of_Tree ty (Narrowing_constructor (1 :: Integer) [d, c, b, a]) =
  App (App (App (App (Const "TreeMapping.Tree.Branch"
                       (Typerep "fun"
                         [(typerep :: Itself b -> Typerepa) Type,
                           Typerep "fun"
                             [(typerep :: Itself a -> Typerepa) Type,
                               Typerep "fun"
                                 [Typerep "TreeMapping.Tree"
                                    [(typerep :: Itself a -> Typerepa) Type,
                                      (typerep :: Itself b -> Typerepa) Type],
                                   Typerep "fun"
                                     [Typerep "TreeMapping.Tree"
[(typerep :: Itself a -> Typerepa) Type,
  (typerep :: Itself b -> Typerepa) Type],
                                       Typerep "TreeMapping.Tree"
 [(typerep :: Itself a -> Typerepa) Type,
   (typerep :: Itself b -> Typerepa) Type]]]]]))
                  ((partial_term_of :: Itself b -> Narrowing_term -> Term) Type
                    a))
             ((partial_term_of :: Itself a -> Narrowing_term -> Term) Type b))
        ((partial_term_of_Tree :: Itself (Tree a b) -> Narrowing_term -> Term)
          Type c))
    ((partial_term_of_Tree :: Itself (Tree a b) -> Narrowing_term -> Term) Type
      d);
partial_term_of_Tree ty (Narrowing_constructor (0 :: Integer) []) =
  Const "TreeMapping.Tree.Empty"
    (Typerep "TreeMapping.Tree"
      [(typerep :: Itself a -> Typerepa) Type,
        (typerep :: Itself b -> Typerepa) Type]);
partial_term_of_Tree ty (Narrowing_variable p tt) =
  Free "_"
    (Typerep "TreeMapping.Tree"
      [(typerep :: Itself a -> Typerepa) Type,
        (typerep :: Itself b -> Typerepa) Type]);

partial_term_of_Map ::
  forall a b.
    (Partial_term_of a,
      Partial_term_of b) => Itself (Map a b) -> Narrowing_term -> Term;
partial_term_of_Map ty (Narrowing_constructor (0 :: Integer) [a]) =
  App (Const "TreeMapping.Map.Tree"
        (Typerep "fun"
          [Typerep "TreeMapping.Tree"
             [(typerep :: Itself a -> Typerepa) Type,
               (typerep :: Itself b -> Typerepa) Type],
            Typerep "TreeMapping.Map"
              [(typerep :: Itself a -> Typerepa) Type,
                (typerep :: Itself b -> Typerepa) Type]]))
    ((partial_term_of_Tree :: Itself (Tree a b) -> Narrowing_term -> Term) Type
      a);
partial_term_of_Map ty (Narrowing_variable p tt) =
  Free "_"
    (Typerep "TreeMapping.Map"
      [(typerep :: Itself a -> Typerepa) Type,
        (typerep :: Itself b -> Typerepa) Type]);

partial_term_of_Nat :: Itself Nata -> Narrowing_term -> Term;
partial_term_of_Nat ty (Narrowing_constructor (1 :: Integer) [a]) =
  App (Const "TreeMapping.Nat.Suc"
        (Typerep "fun"
          [Typerep "TreeMapping.Nat" [], Typerep "TreeMapping.Nat" []]))
    (partial_term_of_Nat Type a);
partial_term_of_Nat ty (Narrowing_constructor (0 :: Integer) []) =
  Const "TreeMapping.Nat.Zero" (Typerep "TreeMapping.Nat" []);
partial_term_of_Nat ty (Narrowing_variable p tt) =
  Free "_" (Typerep "TreeMapping.Nat" []);

typerep_Map_IITN_Map ::
  forall a b. (Typerep a, Typerep b) => Itself (Map_IITN_Map a b) -> Typerepa;
typerep_Map_IITN_Map t =
  Typerep "TreeMapping.Map.Map_IITN_Map"
    [(typerep :: Itself a -> Typerepa) Type,
      (typerep :: Itself b -> Typerepa) Type];

typerep_Nat_IITN_Nat :: Itself Nat_IITN_Nat -> Typerepa;
typerep_Nat_IITN_Nat t = Typerep "TreeMapping.Nat.Nat_IITN_Nat" [];

full_exhaustive_Itself ::
  forall a.
    (Typerep a) => ((Itselfa a, () -> Term) -> Maybe (Bool, [Term])) ->
                     Natural -> Maybe (Bool, [Term]);
full_exhaustive_Itself f i =
  (if less_natural zero_natural i
    then f (Typea,
             (\ _ ->
               Const "TreeMapping.Itself.Type"
                 (Typerep "TreeMapping.Itself"
                   [(typerep :: Itself a -> Typerepa) Type])))
    else Nothing);

partial_term_of_Itself ::
  forall a. (Typerep a) => Itself (Itselfa a) -> Narrowing_term -> Term;
partial_term_of_Itself ty (Narrowing_constructor (0 :: Integer) []) =
  Const "TreeMapping.Itself.Type"
    (Typerep "TreeMapping.Itself" [(typerep :: Itself a -> Typerepa) Type]);
partial_term_of_Itself ty (Narrowing_variable p tt) =
  Free "_"
    (Typerep "TreeMapping.Itself" [(typerep :: Itself a -> Typerepa) Type]);

typerep_Tree_pre_Tree ::
  forall a b c.
    (Typerep a, Typerep b,
      Typerep c) => Itself (Tree_pre_Tree a b c) -> Typerepa;
typerep_Tree_pre_Tree t =
  Typerep "TreeMapping.Tree.Tree_pre_Tree"
    [(typerep :: Itself a -> Typerepa) Type,
      (typerep :: Itself b -> Typerepa) Type,
      (typerep :: Itself c -> Typerepa) Type];

typerep_Tree_IITN_Tree ::
  forall a b. (Typerep a, Typerep b) => Itself (Tree_IITN_Tree a b) -> Typerepa;
typerep_Tree_IITN_Tree t =
  Typerep "TreeMapping.Tree.Tree_IITN_Tree"
    [(typerep :: Itself a -> Typerepa) Type,
      (typerep :: Itself b -> Typerepa) Type];

typerep_Itself_pre_Itself ::
  forall a b.
    (Typerep a, Typerep b) => Itself (Itself_pre_Itself a b) -> Typerepa;
typerep_Itself_pre_Itself t =
  Typerep "TreeMapping.Itself.Itself_pre_Itself"
    [(typerep :: Itself a -> Typerepa) Type,
      (typerep :: Itself b -> Typerepa) Type];

typerep_Itself_IITN_Itself ::
  forall a. (Typerep a) => Itself (Itself_IITN_Itself a) -> Typerepa;
typerep_Itself_IITN_Itself t =
  Typerep "TreeMapping.Itself.Itself_IITN_Itself"
    [(typerep :: Itself a -> Typerepa) Type];

}
