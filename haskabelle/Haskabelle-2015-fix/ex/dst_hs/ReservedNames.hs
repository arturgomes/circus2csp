{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module ReservedNames(bar, foo, frob0, quux, knorks2, zurp) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;

bar :: forall a. a -> [a];
bar nat6 = let {
             set = [nat6];
           } in set;

foo :: forall a. a -> [a] -> [a];
foo nat4 set5 = nat4 : [nat4] ++ set5;

frob0 :: forall a. a -> [a] -> [a];
frob0 nat8 set9 = nat8 : set9;

quux :: forall a. a -> [a];
quux nat7 = let {
              frob = frob0;
            } in frob nat7 [];

knorks2 :: forall a. a -> [a] -> [a];
knorks2 x set10 = [x] ++ set10;

zurp :: forall a. a -> [a];
zurp x = let {
           knorks = knorks2;
         } in knorks x [];

}
