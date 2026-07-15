{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Term_Order(full_af, af_inter, empty_af) where {

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
import qualified Phantom_Type;
import qualified Set_Interval;
import qualified Set;
import qualified Collection_Order;
import qualified Set_Impl;
import qualified Collection_Eq;
import qualified List;
import qualified Arith;

full_af :: forall a. (a, Arith.Nat) -> Set.Set Arith.Nat;
full_af fn = Set_Interval.atLeastLessThan Arith.zero_nat (snd fn);

af_inter ::
  forall a.
    ((a, Arith.Nat) -> Set.Set Arith.Nat) ->
      ((a, Arith.Nat) -> Set.Set Arith.Nat) ->
        (a, Arith.Nat) -> Set.Set Arith.Nat;
af_inter pi mu f = Set.inf_set (pi f) (mu f);

empty_af :: forall a. (a, Arith.Nat) -> Set.Set Arith.Nat;
empty_af fn =
  Set_Impl.set_empty (Phantom_Type.of_phantom Set_Impl.set_impl_nat);

}
