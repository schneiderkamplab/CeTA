{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Unique_Factorization(Ufd, Comm_monoid_gcd, Idom_gcd) where {

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
import qualified GCD;
import qualified Arith;

class (Arith.Idom a) => Ufd a where {
};

class (GCD.Gcda a, Arith.Comm_semiring_1 a) => Comm_monoid_gcd a where {
};

class (Arith.Idom a, Comm_monoid_gcd a) => Idom_gcd a where {
};

}
