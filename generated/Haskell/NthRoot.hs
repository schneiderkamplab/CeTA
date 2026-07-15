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
import qualified Term_Rewriting;

sqrt :: Term_Rewriting.Real -> Term_Rewriting.Real;
sqrt (Term_Rewriting.Real_of_u r) =
  (if Term_Rewriting.equal_rat (Term_Rewriting.mau_coeff r)
        Term_Rewriting.zero_rat
    then Term_Rewriting.Real_of_u (Term_Rewriting.mau_sqrt r)
    else (error :: forall a. String -> (() -> a) -> a)
           "cannot represent sqrt of irrational number"
           (\ _ -> sqrt (Term_Rewriting.Real_of_u r)));

}
