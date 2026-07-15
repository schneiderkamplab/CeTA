{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module RBTMapImpl(g_to_list_rm_basic_ops, g_list_to_map_rm_basic_ops) where {

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
import qualified RBT_add;
import qualified RBT_Impl;
import qualified Product_Type;
import qualified List;
import qualified Compare;
import qualified RBT;
import qualified Orderings;

iteratei_bmap_op_list_it_rm_basic_ops ::
  forall a b c.
    (Orderings.Linorder a) => RBT.Rbt a b ->
                                (c -> Bool) -> ((a, b) -> c -> c) -> c -> c;
iteratei_bmap_op_list_it_rm_basic_ops s = RBT_add.rm_iterateoi (RBT.impl_of s);

g_to_list_rm_basic_ops ::
  forall a b. (Orderings.Linorder a) => RBT.Rbt a b -> [(a, b)];
g_to_list_rm_basic_ops m =
  iteratei_bmap_op_list_it_rm_basic_ops m (\ _ -> True) (\ a b -> a : b) [];

g_list_to_map_rm_basic_ops ::
  forall a b. (Compare.Compare_order a) => [(a, b)] -> RBT.Rbt a b;
g_list_to_map_rm_basic_ops l =
  List.foldl (\ m (k, v) -> RBT.insert k v m) RBT.empty (reverse l);

}
