{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Utility(max_list, sorted_list_subset) where {

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
import qualified Orderings;
import qualified Arith;

max_list :: [Arith.Nat] -> Arith.Nat;
max_list [] = Arith.zero_nat;
max_list (x : xs) = Orderings.max x (max_list xs);

sorted_list_subset ::
  forall a. (Eq a, Orderings.Linorder a) => [a] -> [a] -> Maybe a;
sorted_list_subset (a : asa) (b : bs) =
  (if a == b then sorted_list_subset asa (b : bs)
    else (if Orderings.less b a then sorted_list_subset (a : asa) bs
           else Just a));
sorted_list_subset [] uu = Nothing;
sorted_list_subset (a : uv) [] = Just a;

}
