{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Prelude(Num(..), Int(..), one_int, One(..), plus_num, uminus_int, bitM, dup,
           plus_int, sub, minus_int, Plus(..), Zero(..), times_num, times_int,
           Times(..), Semiring_1, Eqa(..), Nibble(..), Char(..), Print(..),
           Nat(..), plus_nat, one_nat, nat_of_num, nat, nth, foldr, curry,
           replicate, gen_length, size_list, of_nat_aux, of_nat, length, member,
           uncurry, separate, replicatea, the_default, less_num, less_eq_num,
           less_int, equal_num, equal_int, eq_int, eq_bool, eq_list, eq_prod,
           eq_unit, not_eq_int, not_eq_bool, not_eq_list, eq_option,
           not_eq_prod, not_eq_unit, print_list, not_eq_option)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;

data Num = One | Bit0 Num | Bit1 Num;

data Int = Zero_int | Pos Num | Neg Num;

one_int :: Int;
one_int = Pos One;

class One a where {
  one :: a;
};

instance One Int where {
  one = one_int;
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

plus_int :: Int -> Int -> Int;
plus_int (Neg m) (Neg n) = Neg (plus_num m n);
plus_int (Neg m) (Pos n) = sub n m;
plus_int (Pos m) (Neg n) = sub m n;
plus_int (Pos m) (Pos n) = Pos (plus_num m n);
plus_int Zero_int l = l;
plus_int k Zero_int = k;

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

minus_int :: Int -> Int -> Int;
minus_int (Neg m) (Neg n) = sub n m;
minus_int (Neg m) (Pos n) = Neg (plus_num m n);
minus_int (Pos m) (Neg n) = Pos (plus_num m n);
minus_int (Pos m) (Pos n) = sub m n;
minus_int Zero_int l = uminus_int l;
minus_int k Zero_int = k;

class Plus a where {
  plus :: a -> a -> a;
};

instance Plus Int where {
  plus = plus_int;
};

class Zero a where {
  zero :: a;
};

instance Zero Int where {
  zero = Zero_int;
};

class (Plus a) => Semigroup_add a where {
};

class (One a, Semigroup_add a) => Numeral a where {
};

instance Semigroup_add Int where {
};

instance Numeral Int where {
};

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

class Times a where {
  times :: a -> a -> a;
};

class (One a, Times a) => Power a where {
};

instance Times Int where {
  times = times_int;
};

instance Power Int where {
};

class (Semigroup_add a) => Ab_semigroup_add a where {
};

class (Times a) => Semigroup_mult a where {
};

class (Ab_semigroup_add a, Semigroup_mult a) => Semiring a where {
};

instance Ab_semigroup_add Int where {
};

instance Semigroup_mult Int where {
};

instance Semiring Int where {
};

class (Times a, Zero a) => Mult_zero a where {
};

instance Mult_zero Int where {
};

class (Semigroup_add a, Zero a) => Monoid_add a where {
};

class (Ab_semigroup_add a, Monoid_add a) => Comm_monoid_add a where {
};

class (Comm_monoid_add a, Mult_zero a, Semiring a) => Semiring_0 a where {
};

instance Monoid_add Int where {
};

instance Comm_monoid_add Int where {
};

instance Semiring_0 Int where {
};

class (Semigroup_mult a, Power a) => Monoid_mult a where {
};

class (Monoid_mult a, Numeral a, Semiring a) => Semiring_numeral a where {
};

class (One a, Zero a) => Zero_neq_one a where {
};

class (Semiring_numeral a, Semiring_0 a, Zero_neq_one a) => Semiring_1 a where {
};

instance Monoid_mult Int where {
};

instance Semiring_numeral Int where {
};

instance Zero_neq_one Int where {
};

instance Semiring_1 Int where {
};

class Eqa a where {
  eq :: a -> a -> Bool;
  not_eq :: a -> a -> Bool;
};

data Nibble = Nibble0 | Nibble1 | Nibble2 | Nibble3 | Nibble4 | Nibble5
  | Nibble6 | Nibble7 | Nibble8 | Nibble9 | NibbleA | NibbleB | NibbleC
  | NibbleD | NibbleE | NibbleF;

data Char = Char Nibble Nibble;

class Print a where {
  print :: a -> [Char];
};

data Nat = Zero_nat | Suc Nat;

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

nat :: Int -> Nat;
nat (Pos k) = nat_of_num k;
nat Zero_int = Zero_nat;
nat (Neg k) = Zero_nat;

nth :: forall a. [a] -> Nat -> a;
nth (x : xs) (Suc n) = nth xs n;
nth (x : xs) Zero_nat = x;

foldr :: forall a b. (a -> b -> b) -> [a] -> b -> b;
foldr f [] = id;
foldr f (x : xs) = f x . foldr f xs;

curry :: forall a b c. ((a, b) -> c) -> a -> b -> c;
curry f x y = f (x, y);

replicate :: forall a. Nat -> a -> [a];
replicate Zero_nat x = [];
replicate (Suc n) x = x : replicate n x;

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

length :: forall a. [a] -> Int;
length xs = of_nat (size_list xs);

member :: forall a. (Eqa a) => a -> [a] -> Bool;
member x ys = any (eq x) ys;

uncurry :: forall a b c. (a -> b -> c) -> (a, b) -> c;
uncurry = (\ a (b, c) -> a b c);

separate :: forall a. a -> [a] -> [a];
separate x [] = [];
separate x (y : ys) = (if null ys then [y] else y : x : separate x ys);

replicatea :: forall a. Int -> a -> [a];
replicatea k = replicate (nat k);

the_default :: forall a. a -> Maybe a -> a;
the_default x y = (case y of {
                    Nothing -> x;
                    Just z -> z;
                  });

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

eq_bool :: Bool -> Bool -> Bool;
eq_bool p q = p == q;

eq_list :: forall a. (Eq a, Eqa a) => [a] -> [a] -> Bool;
eq_list x y = x == y;

eq_prod :: forall a b. (Eq a, Eqa a, Eq b, Eqa b) => (a, b) -> (a, b) -> Bool;
eq_prod x y = x == y;

eq_unit :: () -> () -> Bool;
eq_unit u v = True;

not_eq_int :: Int -> Int -> Bool;
not_eq_int x y = not (equal_int x y);

not_eq_bool :: Bool -> Bool -> Bool;
not_eq_bool p q = not (p == q);

not_eq_list :: forall a. (Eq a, Eqa a) => [a] -> [a] -> Bool;
not_eq_list x y = not (x == y);

eq_option :: forall a. (Eq a, Eqa a) => Maybe a -> Maybe a -> Bool;
eq_option x y = x == y;

not_eq_prod ::
  forall a b. (Eq a, Eqa a, Eq b, Eqa b) => (a, b) -> (a, b) -> Bool;
not_eq_prod x y = not (x == y);

not_eq_unit :: () -> () -> Bool;
not_eq_unit u v = False;

print_list :: forall a. (Print a) => [a] -> [Char];
print_list xs =
  [Char Nibble5 NibbleB] ++
    concat
      (separate [Char Nibble2 NibbleC, Char Nibble2 Nibble0] (map print xs)) ++
      [Char Nibble5 NibbleD];

not_eq_option :: forall a. (Eq a, Eqa a) => Maybe a -> Maybe a -> Bool;
not_eq_option x y = not (x == y);

}
