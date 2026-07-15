{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Misc_Polynomial(poly_inf) where {

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
import qualified Polynomial;
import qualified Transcendental;
import qualified Arith;

poly_inf ::
  forall a. (Transcendental.Real_normed_vector a) => Polynomial.Poly a -> a;
poly_inf p = Arith.sgn (Polynomial.coeff p (Polynomial.degree p));

}
