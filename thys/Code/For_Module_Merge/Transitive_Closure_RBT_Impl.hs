{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Transitive_Closure_RBT_Impl(memo_rbt_rtrancl) where {

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
import qualified RBT_Map_Set_Extension;
import qualified Option;
import qualified HOL;
import qualified RBT;
import qualified Compare;

rtrancl_rbt_impl ::
  forall a. (Compare.Compare_order a) => [(a, a)] -> [a] -> RBT.Rbt a ();
rtrancl_rbt_impl =
  Transitive_Closure_Impl.rtrancl_impl
    (\ r ->
      let {
        rm = RBT_Map_Set_Extension.elem_list_to_rm fst r;
      } in (\ asa ->
             RBT.keys
               (RBT_Map_Set_Extension.rs_Union
                 (map (\ a ->
                        RBT_Map_Set_Extension.rBT_from_list
                          (map snd (RBT_Map_Set_Extension.rm_set_lookup rm a)))
                   asa))))
    RBT_Map_Set_Extension.rBT_list_union RBT_Map_Set_Extension.rBT_is_key
    RBT.empty;

memo_rbt_rtrancl ::
  forall a. (Compare.Compare_order a) => [(a, a)] -> a -> RBT.Rbt a ();
memo_rbt_rtrancl r =
  let {
    tr = rtrancl_rbt_impl r;
    rm = RBT.bulkload
           (map (\ a -> (a, tr [a]))
             (((RBT.keys . RBT_Map_Set_Extension.rBT_from_list) . map fst) r));
  } in (\ a -> (case RBT.lookup rm a of {
                 Nothing -> RBT_Map_Set_Extension.rBT_from_list [a];
                 Just asa -> asa;
               }));

}
