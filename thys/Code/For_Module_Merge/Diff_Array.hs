{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Diff_Array(array_get, array_set, array_grow, array_length, array_shrink)
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
import qualified List;
import qualified Arith;

array_get :: forall a. Array.Array a -> Arith.Nat -> a;
array_get (Array.Array a) n = List.nth a n;

array_set :: forall a. Array.Array a -> Arith.Nat -> a -> Array.Array a;
array_set (Array.Array aa) n a = Array.Array (List.list_update aa n a);

array_grow :: forall a. Array.Array a -> Arith.Nat -> a -> Array.Array a;
array_grow (Array.Array a) inc x = Array.Array (a ++ List.replicate inc x);

array_length :: forall a. Array.Array a -> Arith.Nat;
array_length (Array.Array a) = List.size_list a;

array_shrink :: forall a. Array.Array a -> Arith.Nat -> Array.Array a;
array_shrink (Array.Array a) sz =
  (if Arith.less_nat (List.size_list a) sz then error "undefined"
    else Array.Array (List.take sz a));

}
