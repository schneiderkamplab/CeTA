{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Dual_Multiset_Impl(dms_order_ext) where {

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
import qualified Product_Type;
import qualified List;
import qualified HOL;
import qualified Sum_Type;
import qualified Arith;

dms_decide_singletons ::
  Bool -> Arith.Nat -> [(Arith.Nat, (Bool, Bool))] -> Bool;
dms_decide_singletons stri n p =
  let {
    d = Arith.minus_nat (List.size_list p) Arith.one_nat;
  } in (if Arith.less_nat d (List.size_list p)
         then List.all_interval
                (\ i ->
                  (case List.nth p i of {
                    (j, (s, ns)) ->
                      s && not (List.member (List.drop (Arith.suc i) p)
                                 (j, (False, True))) ||
                        ns && not (List.member
                                    (map fst (List.drop (Arith.suc i) p)) j);
                  }))
                Arith.zero_nat d
         else True) &&
    (if stri
      then any (\ j -> not (List.member p (j, (False, True))))
             (List.upt Arith.zero_nat n)
      else True);

dms_select :: Bool -> [[(Arith.Nat, (Bool, Bool))]] -> Arith.Nat;
dms_select stri p =
  snd (List.hd
        (List.sort_key fst
          (filter (\ (l, _) -> Arith.less_nat Arith.one_nat l)
            (zip (map List.size_list p)
              (List.upt Arith.zero_nat (List.size_list p))))));

dms_solve_or_select ::
  Bool ->
    Arith.Nat -> [[(Arith.Nat, (Bool, Bool))]] -> Sum_Type.Sum Bool Arith.Nat;
dms_solve_or_select stri n p =
  (if all (\ jsns -> Arith.less_eq_nat (List.size_list jsns) Arith.one_nat) p
    then Sum_Type.Inl
           (if List.member p [] then False
             else dms_decide_singletons stri n (map List.hd p))
    else Sum_Type.Inr (dms_select stri p));

dms_simplify ::
  Bool ->
    [Arith.Nat] ->
      [[(Arith.Nat, (Bool, Bool))]] -> [[(Arith.Nat, (Bool, Bool))]];
dms_simplify stri is p =
  (if any (\ i -> null (List.nth p i)) is then [[]] else p);

dms_solve :: Bool -> Arith.Nat -> [[(Arith.Nat, (Bool, Bool))]] -> Bool;
dms_solve stri n p =
  (case dms_solve_or_select stri n p of {
    Sum_Type.Inl res -> res;
    Sum_Type.Inr k ->
      let {
        ksns = List.nth p k;
      } in dms_solve stri n
             (dms_simplify stri [k] (List.list_update p k [List.hd ksns])) ||
             dms_solve stri n
               (dms_simplify stri [k] (List.list_update p k (List.tl ksns)));
  });

dms_convert ::
  forall a.
    (a -> a -> (Bool, Bool)) -> [a] -> [a] -> [[(Arith.Nat, (Bool, Bool))]];
dms_convert f asa bs =
  let {
    jbs = zip (List.upt Arith.zero_nat (List.size_list bs)) bs;
  } in map (\ a -> map (\ (j, b) -> (j, f a b)) jbs) asa;

dms_preprocess ::
  [[(Arith.Nat, (Bool, Bool))]] -> [[(Arith.Nat, (Bool, Bool))]];
dms_preprocess p = map (filter (\ (_, (a, b)) -> a || b)) p;

dms_bool_ex_idx_impl ::
  Bool -> Arith.Nat -> [[(Arith.Nat, (Bool, Bool))]] -> Bool;
dms_bool_ex_idx_impl stri n p =
  dms_solve stri n
    (dms_simplify stri (List.upt Arith.zero_nat (List.size_list p))
      (dms_preprocess p));

dms_bool_ex_idx :: Bool -> Arith.Nat -> [[(Arith.Nat, (Bool, Bool))]] -> Bool;
dms_bool_ex_idx = dms_bool_ex_idx_impl;

dms_order_ext ::
  forall a. Arith.Nat -> (a -> a -> (Bool, Bool)) -> [a] -> [a] -> (Bool, Bool);
dms_order_ext n f asa bs =
  let {
    p = dms_convert f asa bs;
    lts = List.size_list bs;
    len = Arith.less_eq_nat lts n || Arith.equal_nat (List.size_list asa) lts;
  } in (len && dms_bool_ex_idx True lts p, len && dms_bool_ex_idx False lts p);

}
