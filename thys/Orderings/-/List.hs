{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module List(Interval, nth, upt, foldr, member, interval, all_interval) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import Data.Bits ((.&.), (.|.), (.^.));
import qualified Prelude;
import qualified Data.Bits;
import qualified Orderings;
import qualified Arith;

class (Orderings.Linorder a,
        Arith.Comm_semiring_1_cancel a) => Interval a where {
};

instance Interval Arith.Nat where {
};

nth :: forall a. [a] -> Arith.Nat -> a;
nth (x : xs) Arith.Zero_nat = x;
nth (x : xs) (Arith.Suc n) = nth xs n;

upt :: Arith.Nat -> Arith.Nat -> [Arith.Nat];
upt i j = (if Arith.less_nat i j then i : upt (Arith.Suc i) j else []);

foldr :: forall a b. (a -> b -> b) -> [a] -> b -> b;
foldr f [] = id;
foldr f (x : xs) = f x . foldr f xs;

member :: forall a. (Eq a) => [a] -> a -> Bool;
member [] y = False;
member (x : xs) y = x == y || member xs y;

interval :: forall a. (Eq a, Interval a) => a -> a -> [a];
interval a b =
  (if Orderings.less a b then a : interval (Arith.plus a Arith.one) b
    else (if a == b then [a] else []));

all_interval :: forall a. (Eq a, Interval a) => (a -> Bool) -> a -> a -> Bool;
all_interval p a b =
  (if Orderings.less a b then p a && all_interval p (Arith.plus a Arith.one) b
    else True) &&
    (if a == b then p a else True);

}
