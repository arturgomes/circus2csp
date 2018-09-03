{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Adaptions(nor, append, rev, nand, implies, who_am_i_smile) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;

nor :: Bool -> Bool -> Bool;
nor p q = not (p || q);

append :: forall a. [a] -> [a] -> [a];
append [] ys = ys;
append (v : va) [] = v : va;
append (x : xs) (v : va) = x : append xs (v : va);

rev :: forall a. [a] -> [a];
rev [] = [];
rev (x : xs) = append (rev xs) [x];

nand :: Bool -> Bool -> Bool;
nand p q = not (p && q);

implies :: Bool -> Bool -> Bool;
implies False uu = True;
implies True True = True;
implies True False = False;

who_am_i_smile :: forall a b. (a -> b) -> Maybe a -> Maybe b;
who_am_i_smile f Nothing = Nothing;
who_am_i_smile f (Just x) = Just (f x);

}
