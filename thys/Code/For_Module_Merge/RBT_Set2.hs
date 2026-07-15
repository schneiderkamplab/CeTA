{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module RBT_Set2(fold, keys, fold1, minus, member, product, inter_list) where {

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
import qualified List;
import qualified RBT_Comparator_Impl;
import qualified Option;
import qualified Comparator;
import qualified RBT_ext;
import qualified RBT_Mapping2;
import qualified RBT_Impl;
import qualified Collection_Order;

fold ::
  forall a b.
    (Collection_Order.Ccompare a) => (a -> b -> b) ->
                                       RBT_Mapping2.Mapping_rbt a () -> b -> b;
fold x xc = RBT_Impl.fold (\ a _ -> x a) (RBT_Mapping2.impl_of xc);

keys ::
  forall a.
    (Collection_Order.Ccompare a) => RBT_Mapping2.Mapping_rbt a () -> [a];
keys xa = RBT_Impl.keys (RBT_Mapping2.impl_of xa);

fold1 ::
  forall a.
    (Collection_Order.Ccompare a) => (a -> a -> a) ->
                                       RBT_Mapping2.Mapping_rbt a () -> a;
fold1 x xc = RBT_ext.rBT_Impl_fold1 x (RBT_Mapping2.impl_of xc);

minus ::
  forall a.
    (Collection_Order.Ccompare a) => RBT_Mapping2.Mapping_rbt a () ->
                                       RBT_Mapping2.Mapping_rbt a () ->
 RBT_Mapping2.Mapping_rbt a ();
minus xb xc =
  RBT_Mapping2.Mapping_RBT
    (RBT_Comparator_Impl.rbt_comp_minus (Option.the Collection_Order.ccompare)
      (RBT_Mapping2.impl_of xb) (RBT_Mapping2.impl_of xc));

member ::
  forall a.
    (Collection_Order.Ccompare a) => RBT_Mapping2.Mapping_rbt a () -> a -> Bool;
member t x = RBT_Mapping2.lookup t x == Just ();

product ::
  forall a b.
    (Collection_Order.Ccompare a,
      Collection_Order.Ccompare b) => RBT_Mapping2.Mapping_rbt a () ->
RBT_Mapping2.Mapping_rbt b () -> RBT_Mapping2.Mapping_rbt (a, b) ();
product rbt1 rbt2 = RBT_Mapping2.product (\ _ _ _ _ -> ()) rbt1 rbt2;

inter_list ::
  forall a.
    (Collection_Order.Ccompare a) => RBT_Mapping2.Mapping_rbt a () ->
                                       [a] -> RBT_Mapping2.Mapping_rbt a ();
inter_list xb xc =
  RBT_Mapping2.Mapping_RBT
    (List.fold
      (\ k ->
        RBT_Comparator_Impl.rbt_comp_insert
          (Option.the Collection_Order.ccompare) k ())
      (filter
        (\ x ->
          not (Option.is_none
                (RBT_Comparator_Impl.rbt_comp_lookup
                  (Option.the Collection_Order.ccompare)
                  (RBT_Mapping2.impl_of xb) x)))
        xc)
      RBT_Impl.Empty);

}
