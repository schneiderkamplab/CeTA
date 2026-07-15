{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Multiset_Extension2(mul_ext, mulextp, smulextp) where {

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
import qualified Multiset;
import qualified DAList;
import qualified Arith;
import qualified Multiset_Extension2_Impl;

mul_ext :: forall a. (a -> a -> (Bool, Bool)) -> [a] -> [a] -> (Bool, Bool);
mul_ext = Multiset_Extension2_Impl.mul_ext_impl;

mulextp ::
  forall a.
    (a -> a -> (Bool, Bool)) ->
      Multiset.Multiset a -> Multiset.Multiset a -> (Bool, Bool);
mulextp f (Multiset.Bag xs) (Multiset.Bag ys) =
  mul_ext f
    (Multiset_Extension2_Impl.ass_list_to_single_list (DAList.impl_of xs))
    (Multiset_Extension2_Impl.ass_list_to_single_list (DAList.impl_of ys));

smulextp ::
  forall a.
    (a -> a -> (Bool, Bool)) ->
      Multiset.Multiset a -> Multiset.Multiset a -> Bool;
smulextp f (Multiset.Bag xs) (Multiset.Bag ys) =
  fst (mul_ext f
        (Multiset_Extension2_Impl.ass_list_to_single_list (DAList.impl_of xs))
        (Multiset_Extension2_Impl.ass_list_to_single_list (DAList.impl_of ys)));

}
