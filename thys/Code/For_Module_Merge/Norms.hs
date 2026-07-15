{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Norms(Semiring_real_line, Semiring_1_real_line) where {

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

class (Arith.Ordered_semiring_0 a,
        Arith.Ordered_semiring_strict a) => Semiring_real_line a where {
};

class (Semiring_real_line a,
        Arith.Ordered_semiring_1 a) => Semiring_1_real_line a where {
};

}
