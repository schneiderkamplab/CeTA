{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Determinant(det) where {

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
import qualified Determinant_Impl;
import qualified Matrix;
import qualified Arith;

det :: forall a. (Eq a, Arith.Idom_divide a) => Matrix.Mat a -> a;
det a =
  Determinant_Impl.det_code Determinant_Impl.fst_sel_fun
    Determinant_Impl.trivial_mute_fun a;

}
