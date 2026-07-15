{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Ring_Hom_Matrix(real_of_int, Real_embedding(..), real_of_rat, real_of_real)
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
import qualified Rat;
import qualified Orderings;
import qualified Real;
import qualified Arith;

real_of_int :: Arith.Int -> Real.Real;
real_of_int x = Real.ratreal (Rat.of_int x);

class (Arith.Linordered_idom a) => Real_embedding a where {
  real_of :: a -> Real.Real;
};

instance Real_embedding Arith.Int where {
  real_of = real_of_int;
};

real_of_rat :: Rat.Rat -> Real.Real;
real_of_rat x = Real.ratreal x;

instance Real_embedding Rat.Rat where {
  real_of = real_of_rat;
};

real_of_real :: Real.Real -> Real.Real;
real_of_real x = x;

instance Real_embedding Real.Real where {
  real_of = real_of_real;
};

}
