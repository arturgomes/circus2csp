{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Sections(Plus(..), One(..), Numeral, Num(..), numeral, bar, foo) where {

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

numeral :: forall a. (Numeral a) => Num -> a;
numeral (Bit1 n) = let {
                     m = numeral n;
                   } in plus (plus m m) one;
numeral (Bit0 n) = let {
                     m = numeral n;
                   } in plus m m;
numeral One = one;

bar :: forall a. (Numeral a) => [[a]] -> [[a]];
bar list = map (\ a -> [numeral (Bit1 (Bit1 (Bit1 (Bit0 One))))] ++ a) list;

foo :: forall a. (Numeral a) => [[a]] -> [[a]];
foo list =
  map (\ arg0 -> arg0 ++ [numeral (Bit0 (Bit1 (Bit0 (Bit1 (Bit0 One)))))]) list;

}
