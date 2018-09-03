{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Base(Num(..), Int(..), one_int, One(..), plus_num, uminus_int, bitM, dup,
        plus_int, sub, minus_int, Plus(..), Eqa(..), Nibble(..), Char(..), fold,
        maps, mapp0, member, fold_map, distincts, map_index, map_split,
        map_product)
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

class Eqa a where {
  eq :: a -> a -> Bool;
  not_eq :: a -> a -> Bool;
};

data Nibble = Nibble0 | Nibble1 | Nibble2 | Nibble3 | Nibble4 | Nibble5
  | Nibble6 | Nibble7 | Nibble8 | Nibble9 | NibbleA | NibbleB | NibbleC
  | NibbleD | NibbleE | NibbleF;

data Char = Char Nibble Nibble;

fold :: forall a b. (a -> b -> b) -> [a] -> b -> b;
fold f [] y = y;
fold f (x : xs) y = fold f xs (f x y);

maps :: forall a b. (a -> [b]) -> [a] -> [b];
maps f [] = [];
maps f (x : xs) = f x ++ maps f xs;

mapp0 :: forall a b c. (One a, Plus a) => ((a, b) -> c) -> a -> [b] -> [c];
mapp0 f uu [] = [];
mapp0 f i (x : xs) = let {
                       env1 = f;
                     } in f (i, x) : mapp0 env1 (plus i one) xs;

member :: forall a. (Eqa a) => [a] -> a -> Bool;
member [] y = False;
member (x : xs) y = eq x y || member xs y;

fold_map :: forall a b c. (a -> b -> (c, b)) -> [a] -> b -> ([c], b);
fold_map f [] y = ([], y);
fold_map f (x : xs) y =
  let {
    (xa, ya) = f x y;
    a = fold_map f xs ya;
    (xsa, aa) = a;
  } in (xa : xsa, aa);

distincts :: forall a. (Eqa a) => [a] -> [a];
distincts [] = [];
distincts (x : xs) = (if member xs x then distincts xs else x : distincts xs);

map_index :: forall a b. ((Int, a) -> b) -> [a] -> [b];
map_index f = let {
                mapp = mapp0 f;
              } in mapp Zero_int;

map_split :: forall a b c. (a -> (b, c)) -> [a] -> ([b], [c]);
map_split f [] = ([], []);
map_split f (x : xs) =
  let {
    (y, w) = f x;
    (ys, ws) = map_split f xs;
  } in (y : ys, w : ws);

map_product :: forall a b c. (a -> b -> c) -> [a] -> [b] -> [c];
map_product f uu [] = [];
map_product f [] (v : va) = [];
map_product f (x : xs) (v : va) =
  map (f x) (v : va) ++ map_product f xs (v : va);

}
