{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Depend_DependB(One(..), bla) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;

class One a where {
  one :: a;
};

bla :: forall a. (One a) => a;
bla = one;

}
