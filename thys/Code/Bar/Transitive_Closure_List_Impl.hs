{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Transitive_Closure_List_Impl(memo_list_trancl, rtrancl_list_impl,
                                memo_list_rtrancl)
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
import qualified Transitive_Closure_Impl;
import qualified Arith;
import qualified Map;
import qualified HOL;

trancl_list_impl :: forall a. (Eq a) => [(a, a)] -> [a] -> [a];
trancl_list_impl =
  Transitive_Closure_Impl.trancl_impl
    (\ r asa ->
      Arith.remdups
        (Arith.map_filter
          (\ x ->
            (if (case x of {
                  (a, _) -> Arith.membera asa a;
                })
              then Just (snd x) else Nothing))
          r))
    (\ xs ys -> filter (\ x -> not (Arith.membera ys x)) xs ++ ys)
    (\ x xs -> Arith.membera xs x) [];

memo_list_trancl :: forall a. (Eq a) => [(a, a)] -> a -> [a];
memo_list_trancl r =
  let {
    tr = trancl_list_impl r;
    rm = map (\ a -> (a, tr [a])) ((Arith.remdups . map fst) r);
  } in (\ a -> (case Map.map_of rm a of {
                 Nothing -> [];
                 Just asa -> asa;
               }));

rtrancl_list_impl :: forall a. (Eq a) => [(a, a)] -> [a] -> [a];
rtrancl_list_impl =
  Transitive_Closure_Impl.rtrancl_impl
    (\ r asa ->
      Arith.remdups
        (Arith.map_filter
          (\ x ->
            (if (case x of {
                  (a, _) -> Arith.membera asa a;
                })
              then Just (snd x) else Nothing))
          r))
    (\ xs ys -> filter (\ x -> not (Arith.membera ys x)) xs ++ ys)
    (\ x xs -> Arith.membera xs x) [];

memo_list_rtrancl :: forall a. (Eq a) => [(a, a)] -> a -> [a];
memo_list_rtrancl r =
  let {
    tr = rtrancl_list_impl r;
    rm = map (\ a -> (a, tr [a])) ((Arith.remdups . map fst) r);
  } in (\ a -> (case Map.map_of rm a of {
                 Nothing -> [a];
                 Just asa -> asa;
               }));

}
