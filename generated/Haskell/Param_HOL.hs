{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Param_HOL(is_Inr, list_all_rec) where {

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
import qualified Sum_Type;

is_Inr :: forall a b. Sum_Type.Sum a b -> Bool;
is_Inr (Sum_Type.Inr uu) = True;
is_Inr (Sum_Type.Inl uv) = False;

list_all_rec :: forall a. (a -> Bool) -> [a] -> Bool;
list_all_rec p [] = True;
list_all_rec p (a : l) = p a && list_all_rec p l;

}
