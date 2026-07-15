{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  DAList_Multiset(fold, join, count_of, subtract_entries, single_alist_entry)
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
import qualified AList;
import qualified Map;
import qualified DAList;
import qualified Arith;

fold_impl ::
  forall a b. (a -> Arith.Nat -> b -> b) -> b -> [(a, Arith.Nat)] -> b;
fold_impl fn e ((a, n) : ms) = fold_impl fn (fn a n e) ms;
fold_impl fn e [] = e;

fold ::
  forall a b. (a -> Arith.Nat -> b -> b) -> b -> DAList.Alist a Arith.Nat -> b;
fold f e al = fold_impl f e (DAList.impl_of al);

join_raw ::
  forall a b. (Eq a) => (a -> (b, b) -> b) -> [(a, b)] -> [(a, b)] -> [(a, b)];
join_raw f xs ys =
  Arith.foldr (\ (k, v) -> AList.map_default k v (\ va -> f k (va, v))) ys xs;

join ::
  forall a b.
    (Eq a) => (a -> (b, b) -> b) ->
                DAList.Alist a b -> DAList.Alist a b -> DAList.Alist a b;
join xc xd xe =
  DAList.Alist (join_raw xc (DAList.impl_of xd) (DAList.impl_of xe));

count_of :: forall a. (Eq a) => [(a, Arith.Nat)] -> a -> Arith.Nat;
count_of xs x = (case Map.map_of xs x of {
                  Nothing -> Arith.zero_nat;
                  Just n -> n;
                });

subtract_entries_raw ::
  forall a b. (Eq a, Arith.Minus b) => [(a, b)] -> [(a, b)] -> [(a, b)];
subtract_entries_raw xs ys =
  Arith.foldr (\ (k, v) -> AList.map_entry k (\ va -> Arith.minusa va v)) ys xs;

subtract_entries ::
  forall a b.
    (Eq a,
      Arith.Minus b) => DAList.Alist a b ->
                          DAList.Alist a b -> DAList.Alist a b;
subtract_entries xb xc =
  DAList.Alist (subtract_entries_raw (DAList.impl_of xb) (DAList.impl_of xc));

single_alist_entry :: forall a b. a -> b -> DAList.Alist a b;
single_alist_entry xb xc = DAList.Alist [(xb, xc)];

}
