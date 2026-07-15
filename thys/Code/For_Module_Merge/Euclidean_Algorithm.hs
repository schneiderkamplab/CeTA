{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Euclidean_Algorithm(Normalization_euclidean_semiring, gcd, lcm, gcda, lcma)
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
import qualified Set;
import qualified Arith;
import qualified Factorial_Ring;

class (Arith.Euclidean_semiring a,
        Factorial_Ring.Factorial_semiring a) => Normalization_euclidean_semiring a where {
};

gcd :: forall a. Set.Set a -> a;
gcd _ = error "Euclidean_Algorithm.normalization_euclidean_semiring_class.Gcd";

lcm :: forall a. Set.Set a -> a;
lcm _ = error "Euclidean_Algorithm.normalization_euclidean_semiring_class.Lcm";

gcda :: forall a. (Normalization_euclidean_semiring a, Eq a) => a -> a -> a;
gcda a b =
  (if b == Arith.zero then Arith.normalize a else gcda b (Arith.modulo a b));

lcma :: forall a. (Normalization_euclidean_semiring a, Eq a) => a -> a -> a;
lcma a b = Arith.normalize (Arith.divide (Arith.times a b) (gcda a b));

}
