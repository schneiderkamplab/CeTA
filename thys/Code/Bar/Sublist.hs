{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Sublist(strict_prefix) where {

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

strict_prefix :: forall a. (Eq a) => [a] -> [a] -> Bool;
strict_prefix xs [] = False;
strict_prefix [] (x : xs) = True;
strict_prefix (x : xs) (y : ys) = x == y && strict_prefix xs ys;

}
