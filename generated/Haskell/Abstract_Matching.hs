{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Abstract_Matching(subst_of_map) where {

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

subst_of_map :: forall a b. (a -> b) -> (a -> Maybe b) -> a -> b;
subst_of_map d sigma x = (case sigma x of {
                           Nothing -> d x;
                           Just t -> t;
                         });

}
