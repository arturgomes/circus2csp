{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Strings(Nat(..), Nibble(..), Char(..), digit10) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;

data Nat = Suc Nat | Zero;

data Nibble = Nibble0 | Nibble1 | Nibble2 | Nibble3 | Nibble4 | Nibble5
  | Nibble6 | Nibble7 | Nibble8 | Nibble9 | NibbleA | NibbleB | NibbleC
  | NibbleD | NibbleE | NibbleF;

data Char = Char Nibble Nibble;

digit10 :: Nat -> Char;
digit10 Zero = Char Nibble3 Nibble0;
digit10 (Suc Zero) = Char Nibble3 Nibble1;
digit10 (Suc (Suc Zero)) = Char Nibble3 Nibble2;
digit10 (Suc (Suc (Suc Zero))) = Char Nibble3 Nibble3;
digit10 (Suc (Suc (Suc (Suc Zero)))) = Char Nibble3 Nibble4;
digit10 (Suc (Suc (Suc (Suc (Suc Zero))))) = Char Nibble3 Nibble5;
digit10 (Suc (Suc (Suc (Suc (Suc (Suc Zero)))))) = Char Nibble3 Nibble6;
digit10 (Suc (Suc (Suc (Suc (Suc (Suc (Suc Zero))))))) = Char Nibble3 Nibble7;
digit10 (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc Zero)))))))) =
  Char Nibble3 Nibble8;
digit10 (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc Zero))))))))) =
  Char Nibble3 Nibble9;

}
