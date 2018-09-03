{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Depend(One(..), Plus(..), alias, somefun) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;

class One a where {
  one :: a;
};

class Plus a where {
  plus :: a -> a -> a;
};

alias :: forall a. (One a) => a;
alias = one;

somefun :: forall a. (One a, Plus a) => [a] -> [a];
somefun = map (plus one);

}
