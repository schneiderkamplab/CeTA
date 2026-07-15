{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Gabow_Skeleton(stat_stop, stat_start, find_max_nat, stat_newnode) where {

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

stat_stop :: () -> ();
stat_stop = (\ _ -> ());

stat_start :: () -> ();
stat_start = (\ _ -> ());

find_max_nat :: Arith.Nat -> (Arith.Nat -> Bool) -> Arith.Nat;
find_max_nat n uu =
  (if Arith.equal_nat n Arith.zero_nat then Arith.zero_nat
    else (if uu (Arith.minus_nat n Arith.one_nat)
           then Arith.minus_nat n Arith.one_nat
           else find_max_nat (Arith.minus_nat n Arith.one_nat) uu));

stat_newnode :: () -> ();
stat_newnode = (\ _ -> ());

}
