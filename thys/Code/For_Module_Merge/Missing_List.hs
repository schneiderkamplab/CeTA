{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Missing_List(min_list, list_diff, list_union, concat_lists, is_partition,
                remdups_sort, generate_lists, union_list_sorted,
                subtract_list_sorted)
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
import qualified Arith;
import qualified Option;
import qualified Set;
import qualified Collection_Order;
import qualified Cardinality;
import qualified Set_Impl;
import qualified Collection_Eq;
import qualified List;
import qualified HOL;
import qualified Orderings;

min_list :: forall a. (Orderings.Linorder a) => [a] -> a;
min_list [x] = x;
min_list (x : v : va) = Orderings.min x (min_list (v : va));

list_diff :: forall a. (Eq a) => [a] -> [a] -> [a];
list_diff [] ys = [];
list_diff (x : xs) ys = let {
                          zs = list_diff xs ys;
                        } in (if List.member ys x then zs else x : zs);

list_union :: forall a. (Eq a) => [a] -> [a] -> [a];
list_union [] ys = ys;
list_union (x : xs) ys = let {
                           zs = list_union xs ys;
                         } in (if List.member zs x then zs else x : zs);

concat_lists :: forall a. [[a]] -> [[a]];
concat_lists [] = [[]];
concat_lists (asa : xs) =
  concatMap (\ vec -> map (\ a -> a : vec) asa) (concat_lists xs);

is_partition_impl ::
  forall a.
    (Cardinality.Card_UNIV a, Collection_Eq.Ceq a,
      Collection_Order.Cproper_interval a,
      Set_Impl.Set_impl a) => [Set.Set a] -> Maybe (Set.Set a);
is_partition_impl [] = Just Set.bot_set;
is_partition_impl (asa : rest) =
  Option.bind (is_partition_impl rest)
    (\ alla ->
      (if Set.is_empty (Set.inf_set asa alla) then Just (Set.sup_set alla asa)
        else Nothing));

is_partition ::
  forall a.
    (Cardinality.Card_UNIV a, Collection_Eq.Ceq a,
      Collection_Order.Cproper_interval a,
      Set_Impl.Set_impl a) => [Set.Set a] -> Bool;
is_partition asa = not (Option.is_none (is_partition_impl asa));

remdups_sort :: forall a. (Eq a, Orderings.Linorder a) => [a] -> [a];
remdups_sort xs = List.remdups_adj (List.sort_key (\ x -> x) xs);

generate_lists :: forall a. Arith.Nat -> [a] -> [[a]];
generate_lists n xs =
  concat_lists (map (\ _ -> xs) (List.upt Arith.zero_nat n));

union_list_sorted :: forall a. (Eq a, Orderings.Ord a) => [a] -> [a] -> [a];
union_list_sorted (x : xs) (y : ys) =
  (if x == y then x : union_list_sorted xs ys
    else (if Orderings.less x y then x : union_list_sorted xs (y : ys)
           else y : union_list_sorted (x : xs) ys));
union_list_sorted [] ys = ys;
union_list_sorted (v : va) [] = v : va;

subtract_list_sorted ::
  forall a. (Eq a, Orderings.Linorder a) => [a] -> [a] -> [a];
subtract_list_sorted (x : xs) (y : ys) =
  (if x == y then subtract_list_sorted xs (y : ys)
    else (if Orderings.less x y then x : subtract_list_sorted xs (y : ys)
           else subtract_list_sorted (x : xs) ys));
subtract_list_sorted [] ys = [];
subtract_list_sorted (v : va) [] = v : va;

}
