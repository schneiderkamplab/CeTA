{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Partitions(all_partitions_list) where {

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

insert_into_member_list ::
  forall a.
    (Arith.Cenum a, Arith.Ceq a, Arith.Ccompare a, Eq a,
      Arith.Set_impl a) => a -> [Arith.Set a] -> Arith.Set a -> [Arith.Set a];
insert_into_member_list new_el sets s =
  Arith.sup_set s (Arith.insert new_el Arith.bot_set) : Arith.remove1 s sets;

coarser_partitions_with_list ::
  forall a.
    (Arith.Cenum a, Arith.Ceq a, Arith.Ccompare a, Eq a,
      Arith.Set_impl a) => a -> [Arith.Set a] -> [[Arith.Set a]];
coarser_partitions_with_list new_el p =
  (Arith.insert new_el Arith.bot_set : p) :
    map (insert_into_member_list new_el p) p;

all_coarser_partitions_with_list ::
  forall a.
    (Arith.Cenum a, Arith.Ceq a, Arith.Ccompare a, Eq a,
      Arith.Set_impl a) => a -> [[Arith.Set a]] -> [[Arith.Set a]];
all_coarser_partitions_with_list elem ps =
  concatMap (coarser_partitions_with_list elem) ps;

all_partitions_list ::
  forall a.
    (Arith.Cenum a, Arith.Ceq a, Arith.Ccompare a, Eq a,
      Arith.Set_impl a) => [a] -> [[Arith.Set a]];
all_partitions_list [] = [[]];
all_partitions_list (e : x) =
  all_coarser_partitions_with_list e (all_partitions_list x);

}
