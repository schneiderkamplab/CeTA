{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Util(fun_of, enum_vectors, replace_impl) where {

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
import qualified HOL;
import qualified Arith;
import qualified Map;

fun_of :: forall a b. (Eq a) => [(a, b)] -> a -> b;
fun_of vec x = Arith.the (Map.map_of vec x);

enum_vectors :: forall a b. [a] -> [b] -> [[(b, a)]];
enum_vectors c [] = [[]];
enum_vectors c (x : xs) =
  let {
    a = enum_vectors c xs;
  } in concatMap (\ vec -> map (\ ca -> (x, ca) : vec) c) a;

replace_impl :: forall a. (Eq a) => a -> [a] -> [a] -> [a];
replace_impl a bs m =
  (if Arith.membera m a then bs ++ filter (\ b -> not (b == a)) m else m);

}
