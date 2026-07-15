{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module NthRoot(sqrt) where {

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
import qualified Real_Unique_Impl;
import qualified Real;
import qualified Rat;

sqrt :: Real.Real -> Real.Real;
sqrt (Real.Real_of_u r) =
  (if Rat.equal_rat (Real_Unique_Impl.mau_coeff r) Rat.zero_rat
    then Real.Real_of_u (Real_Unique_Impl.mau_sqrt r)
    else (error :: forall a. String -> (() -> a) -> a)
           "cannot represent sqrt of irrational number"
           (\ _ -> sqrt (Real.Real_of_u r)));

}
