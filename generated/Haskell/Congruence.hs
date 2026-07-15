{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Congruence(Partial_object_ext(..), carrier) where {

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

data Partial_object_ext a b = Partial_object_ext (Arith.Set a) b;

carrier :: forall a b. Partial_object_ext a b -> Arith.Set a;
carrier (Partial_object_ext carrier more) = carrier;

}
