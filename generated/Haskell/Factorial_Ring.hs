{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Factorial_Ring(Factorial_semiring, Factorial_semiring_gcd, Factorial_ring_gcd)
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
import qualified Arith;

class (Arith.Normalization_semidom a) => Factorial_semiring a where {
};

class (Factorial_semiring a,
        Arith.Semiring_Gcd a) => Factorial_semiring_gcd a where {
};

class (Factorial_semiring_gcd a, Arith.Ring_gcd a,
        Arith.Idom_divide a) => Factorial_ring_gcd a where {
};

}
