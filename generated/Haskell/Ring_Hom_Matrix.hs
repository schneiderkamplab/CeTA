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
import qualified Quasi_Order;
import qualified Term_Rewriting;
import qualified Arith;

real_of_int :: Arith.Int -> Term_Rewriting.Real;
real_of_int x = Term_Rewriting.ratreal (Term_Rewriting.of_int x);

class (Arith.Linordered_idom a) => Real_embedding a where {
  real_of :: a -> Term_Rewriting.Real;
};

instance Real_embedding Arith.Int where {
  real_of = real_of_int;
};

real_of_rat :: Term_Rewriting.Rat -> Term_Rewriting.Real;
real_of_rat x = Term_Rewriting.ratreal x;

instance Real_embedding Term_Rewriting.Rat where {
  real_of = real_of_rat;
};

real_of_real :: Term_Rewriting.Real -> Term_Rewriting.Real;
real_of_real x = x;

instance Real_embedding Term_Rewriting.Real where {
  real_of = real_of_real;
};

}
