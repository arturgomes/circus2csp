{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Radix(Nat(..), fold, minus_nat, less_nat, less_eq_nat, eq_nat, divmod, rad0,
         radix, radix_10)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;

data Nat = Suc Nat | Zero;

fold :: forall a b. (a -> b -> b) -> [a] -> b -> b;
fold f (x : xs) s = fold f xs (f x s);
fold f [] s = s;

minus_nat :: Nat -> Nat -> Nat;
minus_nat (Suc m) (Suc n) = minus_nat m n;
minus_nat Zero n = Zero;
minus_nat (Suc v) Zero = Suc v;

less_nat :: Nat -> Nat -> Bool;
less_nat m (Suc n) = less_eq_nat m n;
less_nat n Zero = False;

less_eq_nat :: Nat -> Nat -> Bool;
less_eq_nat (Suc m) n = less_nat m n;
less_eq_nat Zero n = True;

eq_nat :: Nat -> Nat -> Bool;
eq_nat Zero Zero = True;
eq_nat (Suc m) (Suc n) = eq_nat m n;
eq_nat Zero (Suc a) = False;
eq_nat (Suc a) Zero = False;

divmod :: Nat -> Nat -> (Nat, Nat);
divmod m n =
  (if eq_nat n Zero || less_nat m n then (Zero, m)
    else let {
           a = divmod (minus_nat m n) n;
           (q, aa) = a;
         } in (Suc q, aa));

rad0 :: forall a. (Nat -> a) -> Nat -> Nat -> [a];
rad0 uu uv Zero = [];
rad0 ch r (Suc v) = let {
                      (m, d) = divmod (Suc v) r;
                    } in ch d : rad0 ch r m;

radix :: forall a. (Nat -> a) -> Nat -> Nat -> [a];
radix ch uu Zero = [ch Zero];
radix ch r (Suc v) = let {
                       rad = rad0;
                     } in reverse (rad ch r (Suc v));

radix_10 :: Nat -> [Nat];
radix_10 =
  radix id (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc Zero))))))))));

}
