{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Max_Polynomial_Aux(Ordered_semiring_1, Ordered_semigroup_mult_zero)
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

class (Arith.Ordered_semiring_0 a, Arith.Semiring_1 a,
        Arith.Zero_less_one a) => Ordered_semiring_1 a where {
};

class (Arith.Semigroup_mult a, Orderings.Order a,
        Arith.Mult_zero a) => Ordered_semigroup_mult_zero a where {
};

}
