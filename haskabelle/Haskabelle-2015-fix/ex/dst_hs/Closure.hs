{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Closure(Plus(..), addToY2, addToX0, sum3, func) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;

class Plus a where {
  plus :: a -> a -> a;
};

addToY2 :: forall a. (Plus a) => a -> a -> a;
addToY2 y x = plus x y;

addToX0 :: forall a. (Plus a) => a -> a -> a;
addToX0 x y = plus x y;

sum3 :: forall a. (Plus a) => a -> a -> a;
sum3 y x = let {
             env4 = y;
             w = addToY2 env4 x;
           } in plus w x;

func :: forall a. (Plus a) => a -> a -> a;
func x y =
  let {
    addToX = addToX0 x;
    addToY = addToY2 y;
    sum = sum3 y;
    _ = addToY x;
  } in plus (sum x) (addToX y);

}
