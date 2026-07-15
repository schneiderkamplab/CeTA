{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  SN_Orders(Non_strict_order, Ordered_ab_semigroup, Ordered_semiring_0,
             Ordered_semiring_1, Poly_carrier, Large_ordered_semiring_1)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import Data.Bits ((.&.), (.|.), (.^.));
import qualified Prelude;
import qualified Data.Bits;
import qualified Uint;
import qualified Array;
import qualified IArray;
import qualified Uint32;
import qualified Uint64;
import qualified Data_Bits;
import qualified Bit_Shifts;
import qualified Str_Literal;
import qualified Orderings;
import qualified Arith;

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

class (Arith.Comm_semiring_1 a, Ordered_semiring_1 a) => Poly_carrier a where {
};

class (Poly_carrier a) => Large_ordered_semiring_1 a where {
};

}
