{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  ListComprehensions(Plus(..), One(..), Numeral, Eqa(..), Times(..), Num(..),
                      numeral, list, dot_product, list2, list3)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;

class Plus a where {
  plus :: a -> a -> a;
};

class (Plus a) => Semigroup_add a where {
};

class One a where {
  one :: a;
};

class (One a, Semigroup_add a) => Numeral a where {
};

class Eqa a where {
  eq :: a -> a -> Bool;
  not_eq :: a -> a -> Bool;
};

class Times a where {
  times :: a -> a -> a;
};

data Num = One | Bit0 Num | Bit1 Num;

numeral :: forall a. (Numeral a) => Num -> a;
numeral (Bit1 n) = let {
                     m = numeral n;
                   } in plus (plus m m) one;
numeral (Bit0 n) = let {
                     m = numeral n;
                   } in plus m m;
numeral One = one;

list :: forall a. (Numeral a) => [a];
list =
  [one, numeral (Bit0 One), numeral (Bit1 One), numeral (Bit0 (Bit0 One)),
    numeral (Bit1 (Bit0 One))];

dot_product :: forall a b c. (a -> b -> c) -> [a] -> [b] -> [c];
dot_product f l1 l2 = concatMap (\ x -> map (f x) l2) l1;

list2 :: forall a. (Numeral a) => [a];
list2 = dot_product plus list list;

list3 :: forall a. (Times a, Numeral a, Eqa a) => [a];
list3 =
  concatMap
    (\ x -> (if eq x one || eq x (numeral (Bit0 One)) then [times x x] else []))
    list;

}
