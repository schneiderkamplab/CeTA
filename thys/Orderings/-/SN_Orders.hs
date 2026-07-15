{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module SN_Orders(Ordered_semiring_1) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import Data.Bits ((.&.), (.|.), (.^.));
import qualified Prelude;
import qualified Data.Bits;
import qualified Arith;
import qualified Orderings;

class (Orderings.Ord a) => Non_strict_order a where {
};

class (Arith.Ab_semigroup_add a, Arith.Monoid_add a,
        Non_strict_order a) => Ordered_ab_semigroup a where {
};

class (Arith.Semiring_0 a,
        Ordered_ab_semigroup a) => Ordered_semiring_0 a where {
};

class (Arith.Semiring_1 a, Ordered_semiring_0 a) => Ordered_semiring_1 a where {
};

}
