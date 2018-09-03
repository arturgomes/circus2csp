{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  LambdaFu(Plus(..), One(..), Numeral, Num(..), true, nil, false, nulla, pair,
            first, second, numeral, maybe_numbers, numbers)
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

data Num = One | Bit0 Num | Bit1 Num;

true :: forall a b. a -> b -> a;
true = (\ x _ -> x);

nil :: forall a b c. a -> b -> c -> b;
nil = (\ _ -> true);

false :: forall a b. a -> b -> b;
false = (\ _ y -> y);

nulla :: forall a b c d e. ((a -> b -> c -> d -> d) -> e) -> e;
nulla = (\ p -> p (\ _ _ -> false));

pair :: forall a b c. a -> b -> (a -> b -> c) -> c;
pair = (\ x y f -> f x y);

first :: forall a b c. ((a -> b -> a) -> c) -> c;
first = (\ p -> p true);

second :: forall a b c. ((a -> b -> b) -> c) -> c;
second = (\ p -> p false);

numeral :: forall a. (Numeral a) => Num -> a;
numeral (Bit1 n) = let {
                     m = numeral n;
                   } in plus (plus m m) one;
numeral (Bit0 n) = let {
                     m = numeral n;
                   } in plus m m;
numeral One = one;

maybe_numbers :: forall a. (Numeral a) => [Maybe a];
maybe_numbers =
  [Just one, Just (numeral (Bit1 One)), Just (numeral (Bit1 (Bit0 One))),
    Just (numeral (Bit1 (Bit1 One)))];

numbers :: forall a. (Numeral a) => [a];
numbers = map (\ (Just i) -> i) maybe_numbers;

}
