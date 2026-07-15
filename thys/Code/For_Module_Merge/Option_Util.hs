{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Option_Util(fun_of_map, option_to_list) where {

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
import qualified Option;

fun_of_map :: forall a b. (a -> Maybe b) -> b -> a -> b;
fun_of_map m d a = (case m a of {
                     Nothing -> d;
                     Just b -> b;
                   });

option_to_list :: forall a. Maybe a -> [a];
option_to_list (Just a) = [a];
option_to_list Nothing = [];

}
