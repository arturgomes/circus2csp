{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  AVL(Ord(..), Natural(..), integer_of_natural, plus_natural, Plus(..),
       zero_natural, Zero(..), Monoid_add, Times(..), Div(..), One(..), Numeral,
       Minus(..), Typerepa(..), Term(..), Itself(..), Typerep(..), Term_of(..),
       Random(..), Semiring_numeral_div, Narrowing_type(..), Narrowing_term(..),
       Partial_term_of(..), Full_exhaustive(..), Narrowing_cons(..),
       Narrowing(..), Nat(..), Set(..), Nata(..), Num(..), Seta(..), Tree(..),
       Nibble(..), Char(..), Tree_isub_0(..), Nat_IITN_Nat, Set_IITN_Set,
       Tree_pre_Tree, Tree_IITN_Tree, Tree_isub_0_pre_Tree_isub_0,
       Tree_isub_0_IITN_Tree_isub_0, ht, plus_nat, one_nat, less_eq_nat,
       less_nat, maxa, height, eq_nat, is_bal, erase, hinv, avl, bex, ball,
       mkta, bitM, balla, r_bal, l_bal, insrt, is_in, member, union, fold,
       set_of, is_ord, foldr, less_eq_natural, less_natural, one_natural,
       sgn_integer, abs_integer, apsnd, divmod_integer, div_integer,
       div_natural, log, removeAll, memberb, inserta, insert, membera,
       times_natural, mod_integer, mod_natural, max, natural_of_integer,
       minus_natural, minus_shift, next, pick, bot_set, set_Set, pred_Set,
       tree_rec, scomp, equal_natural, iterate, range, sup_set, set_Tree,
       pred_Tree, size_tree, tree_case, tree_size, rec_Nat, map_Set, rec_Set,
       rel_Set, plus_nata, size_Nat, size_Set, r_bal_isub_0, l_bal_isub_0,
       insrt_isub_0, is_in_isub_0, map_Tree, rec_Tree, equal_Nat, rel_Tree,
       size_Tree, collapse, valapp, listsum, select_weight, random_aux_Nat,
       random_aux_Set, random_Nat, random_aux_Tree, tree_isub_0_rec,
       set_Tree_isub_0, pred_Tree_isub_0, size_tree_isub_0, tree_isub_0_case,
       tree_isub_0_size, sum, numeral, less_num, less_eq_num, cons,
       random_aux_Tree_isub_0, size_Nata, size_Seta, plus_num, equal_Set,
       size_Treea, equal_num, times_num, equal_Tree, random_Set, non_empty,
       map_Tree_isub_0, rec_Tree_isub_0, rel_Tree_isub_0, size_Tree_isub_0,
       random_Tree, term_of_Nat, term_of_Set, typerep_Nat, typerep_Set,
       term_of_Tree, typerep_Tree, one_integer, divmod_step, divmod,
       size_Tree_isub_0a, equal_Tree_isub_0, random_Tree_isub_0,
       full_exhaustive_Nat, full_exhaustive_Set, partial_term_of_Nat,
       partial_term_of_Set, term_of_Tree_isub_0, typerep_Tree_isub_0,
       full_exhaustive_Tree, partial_term_of_Tree, typerep_Nat_IITN_Nat,
       typerep_Set_IITN_Set, typerep_Tree_pre_Tree, typerep_Tree_IITN_Tree,
       full_exhaustive_Tree_isub_0, partial_term_of_Tree_isub_0,
       typerep_Tree_isub_0_pre_Tree_isub_0,
       typerep_Tree_isub_0_IITN_Tree_isub_0)
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

data Nat = Suca Nat | Zero;

data Set a = Insert a (Set a) | Empty;

data Nata = Zero_nat | Suc Nata;

data Num = One | Bit0 Num | Bit1 Num;

data Seta a = Set [a] | Coset [a];

data Tree a = Mkt a (Tree a) (Tree a) Nat | Et;

data Nibble = Nibble0 | Nibble1 | Nibble2 | Nibble3 | Nibble4 | Nibble5
  | Nibble6 | Nibble7 | Nibble8 | Nibble9 | NibbleA | NibbleB | NibbleC
  | NibbleD | NibbleE | NibbleF;

data Char = Char Nibble Nibble;

data Tree_isub_0 a = MKT_isub_0 a (Tree_isub_0 a) (Tree_isub_0 a) | ET_isub_0;

data Nat_IITN_Nat;

data Set_IITN_Set a;

data Tree_pre_Tree a b;

data Tree_IITN_Tree a;

data Tree_isub_0_pre_Tree_isub_0 a b;

data Tree_isub_0_IITN_Tree_isub_0 a;

ht :: forall a. Tree a -> Nat;
ht (Mkt x l r h) = h;
ht Et = Zero;

plus_nat :: Nat -> Nat -> Nat;
plus_nat (Suca m) n = plus_nat m (Suca n);
plus_nat Zero n = n;

one_nat :: Nat;
one_nat = Suca Zero;

less_eq_nat :: Nat -> Nat -> Bool;
less_eq_nat (Suca m) n = less_nat m n;
less_eq_nat Zero n = True;

less_nat :: Nat -> Nat -> Bool;
less_nat m (Suca n) = less_eq_nat m n;
less_nat n Zero = False;

maxa :: Nat -> Nat -> Nat;
maxa a b = (if less_eq_nat a b then b else a);

height :: forall a. Tree_isub_0 a -> Nat;
height (MKT_isub_0 n l r) = plus_nat one_nat (maxa (height l) (height r));
height ET_isub_0 = Zero;

eq_nat :: Nat -> Nat -> Bool;
eq_nat Zero Zero = True;
eq_nat (Suca m) (Suca n) = eq_nat m n;
eq_nat Zero (Suca a) = False;
eq_nat (Suca a) Zero = False;

is_bal :: forall a. Tree_isub_0 a -> Bool;
is_bal (MKT_isub_0 n l r) =
  (eq_nat (height l) (height r) ||
    (eq_nat (height l) (plus_nat one_nat (height r)) ||
      eq_nat (height r) (plus_nat one_nat (height l)))) &&
    is_bal l && is_bal r;
is_bal ET_isub_0 = True;

erase :: forall a. Tree a -> Tree_isub_0 a;
erase (Mkt x l r h) = MKT_isub_0 x (erase l) (erase r);
erase Et = ET_isub_0;

hinv :: forall a. Tree a -> Bool;
hinv (Mkt x l r h) =
  eq_nat h (plus_nat one_nat (maxa (height (erase l)) (height (erase r)))) &&
    hinv l && hinv r;
hinv Et = True;

avl :: forall a. Tree a -> Bool;
avl t = is_bal (erase t) && hinv t;

bex :: forall a. Set a -> (a -> Bool) -> Bool;
bex Empty p = False;
bex (Insert a aa) p = p a || bex aa p;

ball :: forall a. Set a -> (a -> Bool) -> Bool;
ball Empty p = True;
ball (Insert a aa) p = p a && ball aa p;

mkta :: forall a. a -> Tree a -> Tree a -> Tree a;
mkta x l r = Mkt x l r (plus_nat (maxa (ht l) (ht r)) one_nat);

bitM :: Num -> Num;
bitM One = One;
bitM (Bit0 n) = Bit1 (bitM n);
bitM (Bit1 n) = Bit1 (Bit0 n);

balla :: forall a. Seta a -> (a -> Bool) -> Bool;
balla (Set xs) p = all p xs;

r_bal :: forall a. (a, (Tree a, Tree a)) -> Tree a;
r_bal (n, (l, Mkt rn rl rr h)) =
  (if less_nat (ht rr) (ht rl)
    then (case rl of {
           Mkt rln rll rlr _ -> mkta rln (mkta n l rll) (mkta rn rlr rr);
           Et -> Et;
         })
    else mkta rn (mkta n l rl) rr);

l_bal :: forall a. (a, (Tree a, Tree a)) -> Tree a;
l_bal (n, (Mkt ln ll lr h, r)) =
  (if less_nat (ht ll) (ht lr)
    then (case lr of {
           Mkt lrn lrl lrr _ -> mkta lrn (mkta ln ll lrl) (mkta n lrr r);
           Et -> Et;
         })
    else mkta ln ll (mkta n lr r));

insrt :: Nat -> Tree Nat -> Tree Nat;
insrt x (Mkt n l r h) =
  (if eq_nat x n then Mkt n l r h
    else (if less_nat x n
           then let {
                  la = insrt x l;
                  hl = ht la;
                  hr = ht r;
                } in (if eq_nat hl (plus_nat (Suca (Suca Zero)) hr)
                       then l_bal (n, (la, r))
                       else Mkt n la r (plus_nat one_nat (maxa hl hr)))
           else let {
                  ra = insrt x r;
                  hl = ht l;
                  hr = ht ra;
                } in (if eq_nat hr (plus_nat (Suca (Suca Zero)) hl)
                       then r_bal (n, (l, ra))
                       else Mkt n l ra (plus_nat one_nat (maxa hl hr)))));
insrt x Et = Mkt x Et Et one_nat;

is_in :: Nat -> Tree Nat -> Bool;
is_in k (Mkt n l r h) =
  (if eq_nat k n then True
    else (if less_nat k n then is_in k l else is_in k r));
is_in k Et = False;

member :: Nat -> Set Nat -> Bool;
member a aa = bex aa (eq_nat a);

union :: Set Nat -> Set Nat -> Set Nat;
union a Empty = a;
union Empty (Insert v va) = Insert v va;
union (Insert a aa) (Insert v va) =
  let {
    c = union aa (Insert v va);
  } in (if member a (Insert v va) then c else Insert a c);

fold :: forall a b. (a -> b -> b) -> [a] -> b -> b;
fold f (x : xs) s = fold f xs (f x s);
fold f [] s = s;

set_of :: Tree_isub_0 Nat -> Set Nat;
set_of (MKT_isub_0 n l r) = Insert n (union (set_of l) (set_of r));
set_of ET_isub_0 = Empty;

is_ord :: Tree_isub_0 Nat -> Bool;
is_ord (MKT_isub_0 n l r) =
  ball (set_of l) (\ na -> less_nat na n) &&
    ball (set_of r) (less_nat n) && is_ord l && is_ord r;
is_ord ET_isub_0 = True;

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

memberb :: forall a. (Eq a) => [a] -> a -> Bool;
memberb [] y = False;
memberb (x : xs) y = x == y || memberb xs y;

inserta :: forall a. (Eq a) => a -> [a] -> [a];
inserta x xs = (if memberb xs x then xs else x : xs);

insert :: forall a. (Eq a) => a -> Seta a -> Seta a;
insert x (Coset xs) = Coset (removeAll x xs);
insert x (Set xs) = Set (inserta x xs);

membera :: forall a. (Eq a) => a -> Seta a -> Bool;
membera x (Coset xs) = not (memberb xs x);
membera x (Set xs) = memberb xs x;

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

bot_set :: forall a. Seta a;
bot_set = Set [];

set_Set :: forall a. (Eq a) => Set a -> Seta a;
set_Set (Insert x11 x12) = insert x11 (set_Set x12);
set_Set Empty = bot_set;

pred_Set :: forall a. (Eq a) => (a -> Bool) -> Set a -> Bool;
pred_Set p = (\ x -> balla (set_Set x) p);

tree_rec ::
  forall a b. a -> (b -> Tree b -> Tree b -> Nat -> a -> a -> a) -> Tree b -> a;
tree_rec f1 f2 (Mkt a tree1 tree2 n) =
  f2 a tree1 tree2 n (tree_rec f1 f2 tree1) (tree_rec f1 f2 tree2);
tree_rec f1 f2 Et = f1;

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

sup_set :: forall a. (Eq a) => Seta a -> Seta a -> Seta a;
sup_set (Coset xs) a = Coset (filter (\ x -> not (membera x a)) xs);
sup_set (Set xs) a = fold insert xs a;

set_Tree :: forall a. (Eq a) => Tree a -> Seta a;
set_Tree (Mkt x11 x12 x13 x14) =
  insert x11 (sup_set (set_Tree x12) (set_Tree x13));
set_Tree Et = bot_set;

pred_Tree :: forall a. (Eq a) => (a -> Bool) -> Tree a -> Bool;
pred_Tree p = (\ x -> balla (set_Tree x) p);

size_tree :: forall a. Tree a -> Nat;
size_tree (Mkt a tree1 tree2 n) =
  plus_nat (plus_nat (size_tree tree1) (size_tree tree2)) (Suca Zero);
size_tree Et = Zero;

tree_case ::
  forall a b. a -> (b -> Tree b -> Tree b -> Nat -> a) -> Tree b -> a;
tree_case f1 f2 Et = f1;
tree_case f1 f2 (Mkt a tree1 tree2 n) = f2 a tree1 tree2 n;

tree_size :: forall a. (a -> Nat) -> Tree a -> Nat;
tree_size fa (Mkt a tree1 tree2 n) =
  plus_nat
    (plus_nat (plus_nat (fa a) (tree_size fa tree1)) (tree_size fa tree2))
    (Suca Zero);
tree_size fa Et = Zero;

rec_Nat :: forall a. (Nat -> a -> a) -> a -> Nat -> a;
rec_Nat f1 f2 (Suca x1) = f1 x1 (rec_Nat f1 f2 x1);
rec_Nat f1 f2 Zero = f2;

map_Set :: forall a b. (a -> b) -> Set a -> Set b;
map_Set f (Insert x11 x12) = Insert (f x11) (map_Set f x12);
map_Set f Empty = Empty;

rec_Set :: forall a b. (a -> Set a -> b -> b) -> b -> Set a -> b;
rec_Set f1 f2 (Insert x11 x12) = f1 x11 x12 (rec_Set f1 f2 x12);
rec_Set f1 f2 Empty = f2;

rel_Set :: forall a b. (a -> b -> Bool) -> Set a -> Set b -> Bool;
rel_Set r (Insert x11 x12) Empty = False;
rel_Set r Empty (Insert x11 x12) = False;
rel_Set r (Insert x11 x12) (Insert y11 y12) = r x11 y11 && rel_Set r x12 y12;
rel_Set r Empty Empty = True;

plus_nata :: Nata -> Nata -> Nata;
plus_nata (Suc m) n = plus_nata m (Suc n);
plus_nata Zero_nat n = n;

size_Nat :: Nat -> Nata;
size_Nat (Suca x1) = plus_nata (size_Nat x1) (Suc Zero_nat);
size_Nat Zero = Zero_nat;

size_Set :: forall a. (a -> Nata) -> Set a -> Nata;
size_Set x (Insert x11 x12) =
  plus_nata (plus_nata (x x11) (size_Set x x12)) (Suc Zero_nat);
size_Set x Empty = Zero_nat;

r_bal_isub_0 :: forall a. (a, (Tree_isub_0 a, Tree_isub_0 a)) -> Tree_isub_0 a;
r_bal_isub_0 (n, (l, MKT_isub_0 rn rl rr)) =
  (if less_nat (height rr) (height rl)
    then (case rl of {
           MKT_isub_0 rln rll rlr ->
             MKT_isub_0 rln (MKT_isub_0 n l rll) (MKT_isub_0 rn rlr rr);
           ET_isub_0 -> ET_isub_0;
         })
    else MKT_isub_0 rn (MKT_isub_0 n l rl) rr);

l_bal_isub_0 :: forall a. (a, (Tree_isub_0 a, Tree_isub_0 a)) -> Tree_isub_0 a;
l_bal_isub_0 (n, (MKT_isub_0 ln ll lr, r)) =
  (if less_nat (height ll) (height lr)
    then (case lr of {
           MKT_isub_0 lrn lrl lrr ->
             MKT_isub_0 lrn (MKT_isub_0 ln ll lrl) (MKT_isub_0 n lrr r);
           ET_isub_0 -> ET_isub_0;
         })
    else MKT_isub_0 ln ll (MKT_isub_0 n lr r));

insrt_isub_0 :: Nat -> Tree_isub_0 Nat -> Tree_isub_0 Nat;
insrt_isub_0 x (MKT_isub_0 n l r) =
  (if eq_nat x n then MKT_isub_0 n l r
    else (if less_nat x n
           then let {
                  la = insrt_isub_0 x l;
                } in (if eq_nat (height la)
                           (plus_nat (Suca (Suca Zero)) (height r))
                       then l_bal_isub_0 (n, (la, r)) else MKT_isub_0 n la r)
           else let {
                  ra = insrt_isub_0 x r;
                } in (if eq_nat (height ra)
                           (plus_nat (Suca (Suca Zero)) (height l))
                       then r_bal_isub_0 (n, (l, ra)) else MKT_isub_0 n l ra)));
insrt_isub_0 x ET_isub_0 = MKT_isub_0 x ET_isub_0 ET_isub_0;

is_in_isub_0 :: Nat -> Tree_isub_0 Nat -> Bool;
is_in_isub_0 k (MKT_isub_0 n l r) =
  (if eq_nat k n then True
    else (if less_nat k n then is_in_isub_0 k l else is_in_isub_0 k r));
is_in_isub_0 k ET_isub_0 = False;

map_Tree :: forall a b. (a -> b) -> Tree a -> Tree b;
map_Tree f (Mkt x11 x12 x13 x14) =
  Mkt (f x11) (map_Tree f x12) (map_Tree f x13) x14;
map_Tree f Et = Et;

rec_Tree ::
  forall a b. (a -> Tree a -> Tree a -> Nat -> b -> b -> b) -> b -> Tree a -> b;
rec_Tree f1 f2 (Mkt x11 x12 x13 x14) =
  f1 x11 x12 x13 x14 (rec_Tree f1 f2 x12) (rec_Tree f1 f2 x13);
rec_Tree f1 f2 Et = f2;

equal_Nat :: Nat -> Nat -> Bool;
equal_Nat (Suca x1) Zero = False;
equal_Nat Zero (Suca x1) = False;
equal_Nat (Suca x1) (Suca y1) = equal_Nat x1 y1;
equal_Nat Zero Zero = True;

rel_Tree :: forall a b. (a -> b -> Bool) -> Tree a -> Tree b -> Bool;
rel_Tree r (Mkt x11 x12 x13 x14) Et = False;
rel_Tree r Et (Mkt x11 x12 x13 x14) = False;
rel_Tree r (Mkt x11 x12 x13 x14) (Mkt y11 y12 y13 y14) =
  r x11 y11 && rel_Tree r x12 y12 && rel_Tree r x13 y13 && equal_Nat x14 y14;
rel_Tree r Et Et = True;

size_Tree :: forall a. (a -> Nata) -> Tree a -> Nata;
size_Tree x (Mkt x11 x12 x13 x14) =
  plus_nata (plus_nata (plus_nata (x x11) (size_Tree x x12)) (size_Tree x x13))
    (Suc Zero_nat);
size_Tree x Et = Zero_nat;

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
    Natural -> (Natural, Natural) -> ((Nat, () -> Term), (Natural, Natural));
random_aux_Nat i j s =
  collapse
    (select_weight
      [(i, scomp (random_aux_Nat (minus_natural i one_natural) j)
             (\ x ->
               (\ a ->
                 (valapp
                    (Suca,
                      (\ _ ->
                        Const "AVL.Nat.Suc"
                          (Typerep "fun"
                            [Typerep "AVL.Nat" [], Typerep "AVL.Nat" []])))
                    x,
                   a)))),
        (one_natural,
          (\ a ->
            ((Zero, (\ _ -> Const "AVL.Nat.Zero" (Typerep "AVL.Nat" []))),
              a)))])
    s;

random_aux_Set ::
  forall a.
    (Random a) => Natural ->
                    Natural ->
                      (Natural, Natural) ->
                        ((Set a, () -> Term), (Natural, Natural));
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
                              Const "AVL.Set.Insert"
                                (Typerep "fun"
                                  [(typerep :: Itself a -> Typerepa) Type,
                                    Typerep "fun"
                                      [Typerep "AVL.Set"
 [(typerep :: Itself a -> Typerepa) Type],
Typerep "AVL.Set" [(typerep :: Itself a -> Typerepa) Type]]])))
                          x)
                        y,
                       a))))),
        (one_natural,
          (\ a ->
            ((Empty,
               (\ _ ->
                 Const "AVL.Set.Empty"
                   (Typerep "AVL.Set"
                     [(typerep :: Itself a -> Typerepa) Type]))),
              a)))])
    s;

random_Nat ::
  Natural -> (Natural, Natural) -> ((Nat, () -> Term), (Natural, Natural));
random_Nat i = random_aux_Nat i i;

random_aux_Tree ::
  forall a.
    (Random a) => Natural ->
                    Natural ->
                      (Natural, Natural) ->
                        ((Tree a, () -> Term), (Natural, Natural));
random_aux_Tree i j s =
  collapse
    (select_weight
      [(i, scomp (random j)
             (\ x ->
               scomp (random_aux_Tree (minus_natural i one_natural) j)
                 (\ y ->
                   scomp (random_aux_Tree (minus_natural i one_natural) j)
                     (\ z ->
                       scomp (random_Nat j)
                         (\ aa ->
                           (\ a ->
                             (valapp
                                (valapp
                                  (valapp
                                    (valapp
                                      (Mkt,
(\ _ ->
  Const "AVL.Tree.Mkt"
    (Typerep "fun"
      [(typerep :: Itself a -> Typerepa) Type,
        Typerep "fun"
          [Typerep "AVL.Tree" [(typerep :: Itself a -> Typerepa) Type],
            Typerep "fun"
              [Typerep "AVL.Tree" [(typerep :: Itself a -> Typerepa) Type],
                Typerep "fun"
                  [Typerep "AVL.Nat" [],
                    Typerep "AVL.Tree"
                      [(typerep :: Itself a -> Typerepa) Type]]]]])))
                                      x)
                                    y)
                                  z)
                                aa,
                               a))))))),
        (one_natural,
          (\ a ->
            ((Et, (\ _ ->
                    Const "AVL.Tree.Et"
                      (Typerep "AVL.Tree"
                        [(typerep :: Itself a -> Typerepa) Type]))),
              a)))])
    s;

tree_isub_0_rec ::
  forall a b.
    a -> (b -> Tree_isub_0 b -> Tree_isub_0 b -> a -> a -> a) ->
           Tree_isub_0 b -> a;
tree_isub_0_rec f1 f2 (MKT_isub_0 a tree_isub_01 tree_isub_02) =
  f2 a tree_isub_01 tree_isub_02 (tree_isub_0_rec f1 f2 tree_isub_01)
    (tree_isub_0_rec f1 f2 tree_isub_02);
tree_isub_0_rec f1 f2 ET_isub_0 = f1;

set_Tree_isub_0 :: forall a. (Eq a) => Tree_isub_0 a -> Seta a;
set_Tree_isub_0 (MKT_isub_0 x11 x12 x13) =
  insert x11 (sup_set (set_Tree_isub_0 x12) (set_Tree_isub_0 x13));
set_Tree_isub_0 ET_isub_0 = bot_set;

pred_Tree_isub_0 :: forall a. (Eq a) => (a -> Bool) -> Tree_isub_0 a -> Bool;
pred_Tree_isub_0 p = (\ x -> balla (set_Tree_isub_0 x) p);

size_tree_isub_0 :: forall a. Tree_isub_0 a -> Nat;
size_tree_isub_0 (MKT_isub_0 a tree_isub_01 tree_isub_02) =
  plus_nat
    (plus_nat (size_tree_isub_0 tree_isub_01) (size_tree_isub_0 tree_isub_02))
    (Suca Zero);
size_tree_isub_0 ET_isub_0 = Zero;

tree_isub_0_case ::
  forall a b.
    a -> (b -> Tree_isub_0 b -> Tree_isub_0 b -> a) -> Tree_isub_0 b -> a;
tree_isub_0_case f1 f2 ET_isub_0 = f1;
tree_isub_0_case f1 f2 (MKT_isub_0 a tree_isub_01 tree_isub_02) =
  f2 a tree_isub_01 tree_isub_02;

tree_isub_0_size :: forall a. (a -> Nat) -> Tree_isub_0 a -> Nat;
tree_isub_0_size fa (MKT_isub_0 a tree_isub_01 tree_isub_02) =
  plus_nat
    (plus_nat (plus_nat (fa a) (tree_isub_0_size fa tree_isub_01))
      (tree_isub_0_size fa tree_isub_02))
    (Suca Zero);
tree_isub_0_size fa ET_isub_0 = Zero;

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

random_aux_Tree_isub_0 ::
  forall a.
    (Random a) => Natural ->
                    Natural ->
                      (Natural, Natural) ->
                        ((Tree_isub_0 a, () -> Term), (Natural, Natural));
random_aux_Tree_isub_0 i j s =
  collapse
    (select_weight
      [(i, scomp (random j)
             (\ x ->
               scomp (random_aux_Tree_isub_0 (minus_natural i one_natural) j)
                 (\ y ->
                   scomp (random_aux_Tree_isub_0 (minus_natural i one_natural)
                           j)
                     (\ z ->
                       (\ a ->
                         (valapp
                            (valapp
                              (valapp
                                (MKT_isub_0,
                                  (\ _ ->
                                    Const "AVL.Tree_isub_0.MKT_isub_0"
                                      (Typerep "fun"
[(typerep :: Itself a -> Typerepa) Type,
  Typerep "fun"
    [Typerep "AVL.Tree_isub_0" [(typerep :: Itself a -> Typerepa) Type],
      Typerep "fun"
        [Typerep "AVL.Tree_isub_0" [(typerep :: Itself a -> Typerepa) Type],
          Typerep "AVL.Tree_isub_0"
            [(typerep :: Itself a -> Typerepa) Type]]]])))
                                x)
                              y)
                            z,
                           a)))))),
        (one_natural,
          (\ a ->
            ((ET_isub_0,
               (\ _ ->
                 Const "AVL.Tree_isub_0.ET_isub_0"
                   (Typerep "AVL.Tree_isub_0"
                     [(typerep :: Itself a -> Typerepa) Type]))),
              a)))])
    s;

size_Nata :: Nat -> Nata;
size_Nata (Suca x1) = plus_nata (size_Nata x1) (Suc Zero_nat);
size_Nata Zero = Zero_nat;

size_Seta :: forall a. Set a -> Nata;
size_Seta (Insert x11 x12) = plus_nata (size_Seta x12) (Suc Zero_nat);
size_Seta Empty = Zero_nat;

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

equal_Set :: forall a. (Eq a) => Set a -> Set a -> Bool;
equal_Set (Insert x11 x12) Empty = False;
equal_Set Empty (Insert x11 x12) = False;
equal_Set (Insert x11 x12) (Insert y11 y12) = x11 == y11 && equal_Set x12 y12;
equal_Set Empty Empty = True;

size_Treea :: forall a. Tree a -> Nata;
size_Treea (Mkt x11 x12 x13 x14) =
  plus_nata (plus_nata (size_Treea x12) (size_Treea x13)) (Suc Zero_nat);
size_Treea Et = Zero_nat;

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

equal_Tree :: forall a. (Eq a) => Tree a -> Tree a -> Bool;
equal_Tree (Mkt x11 x12 x13 x14) Et = False;
equal_Tree Et (Mkt x11 x12 x13 x14) = False;
equal_Tree (Mkt x11 x12 x13 x14) (Mkt y11 y12 y13 y14) =
  x11 == y11 && equal_Tree x12 y12 && equal_Tree x13 y13 && equal_Nat x14 y14;
equal_Tree Et Et = True;

random_Set ::
  forall a.
    (Random a) => Natural ->
                    (Natural, Natural) ->
                      ((Set a, () -> Term), (Natural, Natural));
random_Set i = random_aux_Set i i;

non_empty :: Narrowing_type -> Bool;
non_empty (Narrowing_sum_of_products ps) = not (null ps);

map_Tree_isub_0 :: forall a b. (a -> b) -> Tree_isub_0 a -> Tree_isub_0 b;
map_Tree_isub_0 f (MKT_isub_0 x11 x12 x13) =
  MKT_isub_0 (f x11) (map_Tree_isub_0 f x12) (map_Tree_isub_0 f x13);
map_Tree_isub_0 f ET_isub_0 = ET_isub_0;

rec_Tree_isub_0 ::
  forall a b.
    (a -> Tree_isub_0 a -> Tree_isub_0 a -> b -> b -> b) ->
      b -> Tree_isub_0 a -> b;
rec_Tree_isub_0 f1 f2 (MKT_isub_0 x11 x12 x13) =
  f1 x11 x12 x13 (rec_Tree_isub_0 f1 f2 x12) (rec_Tree_isub_0 f1 f2 x13);
rec_Tree_isub_0 f1 f2 ET_isub_0 = f2;

rel_Tree_isub_0 ::
  forall a b. (a -> b -> Bool) -> Tree_isub_0 a -> Tree_isub_0 b -> Bool;
rel_Tree_isub_0 r (MKT_isub_0 x11 x12 x13) ET_isub_0 = False;
rel_Tree_isub_0 r ET_isub_0 (MKT_isub_0 x11 x12 x13) = False;
rel_Tree_isub_0 r (MKT_isub_0 x11 x12 x13) (MKT_isub_0 y11 y12 y13) =
  r x11 y11 && rel_Tree_isub_0 r x12 y12 && rel_Tree_isub_0 r x13 y13;
rel_Tree_isub_0 r ET_isub_0 ET_isub_0 = True;

size_Tree_isub_0 :: forall a. (a -> Nata) -> Tree_isub_0 a -> Nata;
size_Tree_isub_0 x (MKT_isub_0 x11 x12 x13) =
  plus_nata
    (plus_nata (plus_nata (x x11) (size_Tree_isub_0 x x12))
      (size_Tree_isub_0 x x13))
    (Suc Zero_nat);
size_Tree_isub_0 x ET_isub_0 = Zero_nat;

random_Tree ::
  forall a.
    (Random a) => Natural ->
                    (Natural, Natural) ->
                      ((Tree a, () -> Term), (Natural, Natural));
random_Tree i = random_aux_Tree i i;

term_of_Nat :: Nat -> Term;
term_of_Nat Zero = Const "AVL.Nat.Zero" (Typerep "AVL.Nat" []);
term_of_Nat (Suca a) =
  App (Const "AVL.Nat.Suc"
        (Typerep "fun" [Typerep "AVL.Nat" [], Typerep "AVL.Nat" []]))
    (term_of_Nat a);

term_of_Set :: forall a. (Term_of a) => Set a -> Term;
term_of_Set Empty =
  Const "AVL.Set.Empty"
    (Typerep "AVL.Set" [(typerep :: Itself a -> Typerepa) Type]);
term_of_Set (Insert a b) =
  App (App (Const "AVL.Set.Insert"
             (Typerep "fun"
               [(typerep :: Itself a -> Typerepa) Type,
                 Typerep "fun"
                   [Typerep "AVL.Set" [(typerep :: Itself a -> Typerepa) Type],
                     Typerep "AVL.Set"
                       [(typerep :: Itself a -> Typerepa) Type]]]))
        (term_of a))
    (term_of_Set b);

typerep_Nat :: Itself Nat -> Typerepa;
typerep_Nat t = Typerep "AVL.Nat" [];

typerep_Set :: forall a. (Typerep a) => Itself (Set a) -> Typerepa;
typerep_Set t = Typerep "AVL.Set" [(typerep :: Itself a -> Typerepa) Type];

term_of_Tree :: forall a. (Term_of a) => Tree a -> Term;
term_of_Tree Et =
  Const "AVL.Tree.Et"
    (Typerep "AVL.Tree" [(typerep :: Itself a -> Typerepa) Type]);
term_of_Tree (Mkt a b c d) =
  App (App (App (App (Const "AVL.Tree.Mkt"
                       (Typerep "fun"
                         [(typerep :: Itself a -> Typerepa) Type,
                           Typerep "fun"
                             [Typerep "AVL.Tree"
                                [(typerep :: Itself a -> Typerepa) Type],
                               Typerep "fun"
                                 [Typerep "AVL.Tree"
                                    [(typerep :: Itself a -> Typerepa) Type],
                                   Typerep "fun"
                                     [Typerep "AVL.Nat" [],
                                       Typerep "AVL.Tree"
 [(typerep :: Itself a -> Typerepa) Type]]]]]))
                  (term_of a))
             (term_of_Tree b))
        (term_of_Tree c))
    (term_of_Nat d);

typerep_Tree :: forall a. (Typerep a) => Itself (Tree a) -> Typerepa;
typerep_Tree t = Typerep "AVL.Tree" [(typerep :: Itself a -> Typerepa) Type];

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

size_Tree_isub_0a :: forall a. Tree_isub_0 a -> Nata;
size_Tree_isub_0a (MKT_isub_0 x11 x12 x13) =
  plus_nata (plus_nata (size_Tree_isub_0a x12) (size_Tree_isub_0a x13))
    (Suc Zero_nat);
size_Tree_isub_0a ET_isub_0 = Zero_nat;

equal_Tree_isub_0 :: forall a. (Eq a) => Tree_isub_0 a -> Tree_isub_0 a -> Bool;
equal_Tree_isub_0 (MKT_isub_0 x11 x12 x13) ET_isub_0 = False;
equal_Tree_isub_0 ET_isub_0 (MKT_isub_0 x11 x12 x13) = False;
equal_Tree_isub_0 (MKT_isub_0 x11 x12 x13) (MKT_isub_0 y11 y12 y13) =
  x11 == y11 && equal_Tree_isub_0 x12 y12 && equal_Tree_isub_0 x13 y13;
equal_Tree_isub_0 ET_isub_0 ET_isub_0 = True;

random_Tree_isub_0 ::
  forall a.
    (Random a) => Natural ->
                    (Natural, Natural) ->
                      ((Tree_isub_0 a, () -> Term), (Natural, Natural));
random_Tree_isub_0 i = random_aux_Tree_isub_0 i i;

full_exhaustive_Nat ::
  ((Nat, () -> Term) -> Maybe (Bool, [Term])) ->
    Natural -> Maybe (Bool, [Term]);
full_exhaustive_Nat f i =
  (if less_natural zero_natural i
    then (case full_exhaustive_Nat
                 (\ (uu, uua) ->
                   f (Suca uu,
                       (\ _ ->
                         App (Const "AVL.Nat.Suc"
                               (Typerep "fun"
                                 [Typerep "AVL.Nat" [], Typerep "AVL.Nat" []]))
                           (uua ()))))
                 (minus_natural i one_natural)
           of {
           Nothing ->
             f (Zero, (\ _ -> Const "AVL.Nat.Zero" (Typerep "AVL.Nat" [])));
           Just a -> Just a;
         })
    else Nothing);

full_exhaustive_Set ::
  forall a.
    (Full_exhaustive a) => ((Set a, () -> Term) -> Maybe (Bool, [Term])) ->
                             Natural -> Maybe (Bool, [Term]);
full_exhaustive_Set f i =
  (if less_natural zero_natural i
    then (case full_exhaustive
                 (\ (uu, uua) ->
                   full_exhaustive_Set
                     (\ (uub, uuc) ->
                       f (Insert uu uub,
                           (\ _ ->
                             App (App (Const "AVL.Set.Insert"
(Typerep "fun"
  [(typerep :: Itself a -> Typerepa) Type,
    Typerep "fun"
      [Typerep "AVL.Set" [(typerep :: Itself a -> Typerepa) Type],
        Typerep "AVL.Set" [(typerep :: Itself a -> Typerepa) Type]]]))
                                   (uua ()))
                               (uuc ()))))
                     (minus_natural i one_natural))
                 (minus_natural i one_natural)
           of {
           Nothing ->
             f (Empty,
                 (\ _ ->
                   Const "AVL.Set.Empty"
                     (Typerep "AVL.Set"
                       [(typerep :: Itself a -> Typerepa) Type])));
           Just a -> Just a;
         })
    else Nothing);

partial_term_of_Nat :: Itself Nat -> Narrowing_term -> Term;
partial_term_of_Nat ty (Narrowing_constructor (1 :: Integer) []) =
  Const "AVL.Nat.Zero" (Typerep "AVL.Nat" []);
partial_term_of_Nat ty (Narrowing_constructor (0 :: Integer) [a]) =
  App (Const "AVL.Nat.Suc"
        (Typerep "fun" [Typerep "AVL.Nat" [], Typerep "AVL.Nat" []]))
    (partial_term_of_Nat Type a);
partial_term_of_Nat ty (Narrowing_variable p tt) =
  Free "_" (Typerep "AVL.Nat" []);

partial_term_of_Set ::
  forall a. (Partial_term_of a) => Itself (Set a) -> Narrowing_term -> Term;
partial_term_of_Set ty (Narrowing_constructor (1 :: Integer) []) =
  Const "AVL.Set.Empty"
    (Typerep "AVL.Set" [(typerep :: Itself a -> Typerepa) Type]);
partial_term_of_Set ty (Narrowing_constructor (0 :: Integer) [b, a]) =
  App (App (Const "AVL.Set.Insert"
             (Typerep "fun"
               [(typerep :: Itself a -> Typerepa) Type,
                 Typerep "fun"
                   [Typerep "AVL.Set" [(typerep :: Itself a -> Typerepa) Type],
                     Typerep "AVL.Set"
                       [(typerep :: Itself a -> Typerepa) Type]]]))
        ((partial_term_of :: Itself a -> Narrowing_term -> Term) Type a))
    ((partial_term_of_Set :: Itself (Set a) -> Narrowing_term -> Term) Type b);
partial_term_of_Set ty (Narrowing_variable p tt) =
  Free "_" (Typerep "AVL.Set" [(typerep :: Itself a -> Typerepa) Type]);

term_of_Tree_isub_0 :: forall a. (Term_of a) => Tree_isub_0 a -> Term;
term_of_Tree_isub_0 ET_isub_0 =
  Const "AVL.Tree_isub_0.ET_isub_0"
    (Typerep "AVL.Tree_isub_0" [(typerep :: Itself a -> Typerepa) Type]);
term_of_Tree_isub_0 (MKT_isub_0 a b c) =
  App (App (App (Const "AVL.Tree_isub_0.MKT_isub_0"
                  (Typerep "fun"
                    [(typerep :: Itself a -> Typerepa) Type,
                      Typerep "fun"
                        [Typerep "AVL.Tree_isub_0"
                           [(typerep :: Itself a -> Typerepa) Type],
                          Typerep "fun"
                            [Typerep "AVL.Tree_isub_0"
                               [(typerep :: Itself a -> Typerepa) Type],
                              Typerep "AVL.Tree_isub_0"
                                [(typerep :: Itself a -> Typerepa) Type]]]]))
             (term_of a))
        (term_of_Tree_isub_0 b))
    (term_of_Tree_isub_0 c);

typerep_Tree_isub_0 ::
  forall a. (Typerep a) => Itself (Tree_isub_0 a) -> Typerepa;
typerep_Tree_isub_0 t =
  Typerep "AVL.Tree_isub_0" [(typerep :: Itself a -> Typerepa) Type];

full_exhaustive_Tree ::
  forall a.
    (Full_exhaustive a) => ((Tree a, () -> Term) -> Maybe (Bool, [Term])) ->
                             Natural -> Maybe (Bool, [Term]);
full_exhaustive_Tree f i =
  (if less_natural zero_natural i
    then (case full_exhaustive
                 (\ (uu, uua) ->
                   full_exhaustive_Tree
                     (\ (uub, uuc) ->
                       full_exhaustive_Tree
                         (\ (uud, uue) ->
                           full_exhaustive_Nat
                             (\ (uuf, uug) ->
                               f (Mkt uu uub uud uuf,
                                   (\ _ ->
                                     App (App
   (App (App (Const "AVL.Tree.Mkt"
               (Typerep "fun"
                 [(typerep :: Itself a -> Typerepa) Type,
                   Typerep "fun"
                     [Typerep "AVL.Tree"
                        [(typerep :: Itself a -> Typerepa) Type],
                       Typerep "fun"
                         [Typerep "AVL.Tree"
                            [(typerep :: Itself a -> Typerepa) Type],
                           Typerep "fun"
                             [Typerep "AVL.Nat" [],
                               Typerep "AVL.Tree"
                                 [(typerep :: Itself a -> Typerepa) Type]]]]]))
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
             f (Et, (\ _ ->
                      Const "AVL.Tree.Et"
                        (Typerep "AVL.Tree"
                          [(typerep :: Itself a -> Typerepa) Type])));
           Just a -> Just a;
         })
    else Nothing);

partial_term_of_Tree ::
  forall a. (Partial_term_of a) => Itself (Tree a) -> Narrowing_term -> Term;
partial_term_of_Tree ty (Narrowing_constructor (1 :: Integer) []) =
  Const "AVL.Tree.Et"
    (Typerep "AVL.Tree" [(typerep :: Itself a -> Typerepa) Type]);
partial_term_of_Tree ty (Narrowing_constructor (0 :: Integer) [d, c, b, a]) =
  App (App (App (App (Const "AVL.Tree.Mkt"
                       (Typerep "fun"
                         [(typerep :: Itself a -> Typerepa) Type,
                           Typerep "fun"
                             [Typerep "AVL.Tree"
                                [(typerep :: Itself a -> Typerepa) Type],
                               Typerep "fun"
                                 [Typerep "AVL.Tree"
                                    [(typerep :: Itself a -> Typerepa) Type],
                                   Typerep "fun"
                                     [Typerep "AVL.Nat" [],
                                       Typerep "AVL.Tree"
 [(typerep :: Itself a -> Typerepa) Type]]]]]))
                  ((partial_term_of :: Itself a -> Narrowing_term -> Term) Type
                    a))
             ((partial_term_of_Tree ::
                Itself (Tree a) -> Narrowing_term -> Term)
               Type b))
        ((partial_term_of_Tree :: Itself (Tree a) -> Narrowing_term -> Term)
          Type c))
    (partial_term_of_Nat Type d);
partial_term_of_Tree ty (Narrowing_variable p tt) =
  Free "_" (Typerep "AVL.Tree" [(typerep :: Itself a -> Typerepa) Type]);

typerep_Nat_IITN_Nat :: Itself Nat_IITN_Nat -> Typerepa;
typerep_Nat_IITN_Nat t = Typerep "AVL.Nat.Nat_IITN_Nat" [];

typerep_Set_IITN_Set ::
  forall a. (Typerep a) => Itself (Set_IITN_Set a) -> Typerepa;
typerep_Set_IITN_Set t =
  Typerep "AVL.Set.Set_IITN_Set" [(typerep :: Itself a -> Typerepa) Type];

typerep_Tree_pre_Tree ::
  forall a b. (Typerep a, Typerep b) => Itself (Tree_pre_Tree a b) -> Typerepa;
typerep_Tree_pre_Tree t =
  Typerep "AVL.Tree.Tree_pre_Tree"
    [(typerep :: Itself a -> Typerepa) Type,
      (typerep :: Itself b -> Typerepa) Type];

typerep_Tree_IITN_Tree ::
  forall a. (Typerep a) => Itself (Tree_IITN_Tree a) -> Typerepa;
typerep_Tree_IITN_Tree t =
  Typerep "AVL.Tree.Tree_IITN_Tree" [(typerep :: Itself a -> Typerepa) Type];

full_exhaustive_Tree_isub_0 ::
  forall a.
    (Full_exhaustive a) => ((Tree_isub_0 a, () -> Term) ->
                             Maybe (Bool, [Term])) ->
                             Natural -> Maybe (Bool, [Term]);
full_exhaustive_Tree_isub_0 f i =
  (if less_natural zero_natural i
    then (case full_exhaustive
                 (\ (uu, uua) ->
                   full_exhaustive_Tree_isub_0
                     (\ (uub, uuc) ->
                       full_exhaustive_Tree_isub_0
                         (\ (uud, uue) ->
                           f (MKT_isub_0 uu uub uud,
                               (\ _ ->
                                 App (App (App
    (Const "AVL.Tree_isub_0.MKT_isub_0"
      (Typerep "fun"
        [(typerep :: Itself a -> Typerepa) Type,
          Typerep "fun"
            [Typerep "AVL.Tree_isub_0" [(typerep :: Itself a -> Typerepa) Type],
              Typerep "fun"
                [Typerep "AVL.Tree_isub_0"
                   [(typerep :: Itself a -> Typerepa) Type],
                  Typerep "AVL.Tree_isub_0"
                    [(typerep :: Itself a -> Typerepa) Type]]]]))
    (uua ()))
                                       (uuc ()))
                                   (uue ()))))
                         (minus_natural i one_natural))
                     (minus_natural i one_natural))
                 (minus_natural i one_natural)
           of {
           Nothing ->
             f (ET_isub_0,
                 (\ _ ->
                   Const "AVL.Tree_isub_0.ET_isub_0"
                     (Typerep "AVL.Tree_isub_0"
                       [(typerep :: Itself a -> Typerepa) Type])));
           Just a -> Just a;
         })
    else Nothing);

partial_term_of_Tree_isub_0 ::
  forall a.
    (Partial_term_of a) => Itself (Tree_isub_0 a) -> Narrowing_term -> Term;
partial_term_of_Tree_isub_0 ty (Narrowing_constructor (1 :: Integer) []) =
  Const "AVL.Tree_isub_0.ET_isub_0"
    (Typerep "AVL.Tree_isub_0" [(typerep :: Itself a -> Typerepa) Type]);
partial_term_of_Tree_isub_0 ty (Narrowing_constructor (0 :: Integer) [c, b, a])
  = App (App (App (Const "AVL.Tree_isub_0.MKT_isub_0"
                    (Typerep "fun"
                      [(typerep :: Itself a -> Typerepa) Type,
                        Typerep "fun"
                          [Typerep "AVL.Tree_isub_0"
                             [(typerep :: Itself a -> Typerepa) Type],
                            Typerep "fun"
                              [Typerep "AVL.Tree_isub_0"
                                 [(typerep :: Itself a -> Typerepa) Type],
                                Typerep "AVL.Tree_isub_0"
                                  [(typerep :: Itself a -> Typerepa) Type]]]]))
               ((partial_term_of :: Itself a -> Narrowing_term -> Term) Type a))
          ((partial_term_of_Tree_isub_0 ::
             Itself (Tree_isub_0 a) -> Narrowing_term -> Term)
            Type b))
      ((partial_term_of_Tree_isub_0 ::
         Itself (Tree_isub_0 a) -> Narrowing_term -> Term)
        Type c);
partial_term_of_Tree_isub_0 ty (Narrowing_variable p tt) =
  Free "_" (Typerep "AVL.Tree_isub_0" [(typerep :: Itself a -> Typerepa) Type]);

typerep_Tree_isub_0_pre_Tree_isub_0 ::
  forall a b.
    (Typerep a,
      Typerep b) => Itself (Tree_isub_0_pre_Tree_isub_0 a b) -> Typerepa;
typerep_Tree_isub_0_pre_Tree_isub_0 t =
  Typerep "AVL.Tree_isub_0.Tree_isub_0_pre_Tree_isub_0"
    [(typerep :: Itself a -> Typerepa) Type,
      (typerep :: Itself b -> Typerepa) Type];

typerep_Tree_isub_0_IITN_Tree_isub_0 ::
  forall a. (Typerep a) => Itself (Tree_isub_0_IITN_Tree_isub_0 a) -> Typerepa;
typerep_Tree_isub_0_IITN_Tree_isub_0 t =
  Typerep "AVL.Tree_isub_0.Tree_isub_0_IITN_Tree_isub_0"
    [(typerep :: Itself a -> Typerepa) Type];

}
