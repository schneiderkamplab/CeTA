{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  RBT_Mapping2(Mapping_rbt(..), impl_of, ex, alla, init, join, meet, empty,
                delete, filtera, insert, lookup, product, is_empty)
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
import qualified RBT_Comparator_Impl;
import qualified Option;
import qualified Comparator;
import qualified RBT_ext;
import qualified RBT_Impl;
import qualified Collection_Order;

newtype Mapping_rbt b a = Mapping_RBT (RBT_Impl.Rbt b a);

impl_of ::
  forall b a.
    (Collection_Order.Ccompare b) => Mapping_rbt b a -> RBT_Impl.Rbt b a;
impl_of (Mapping_RBT x) = x;

ex :: forall a b.
        (Collection_Order.Ccompare a) => (a -> b -> Bool) ->
   Mapping_rbt a b -> Bool;
ex xb xc = RBT_ext.rBT_Impl_rbt_ex xb (impl_of xc);

alla ::
  forall a b.
    (Collection_Order.Ccompare a) => (a -> b -> Bool) ->
                                       Mapping_rbt a b -> Bool;
alla xb xc = RBT_ext.rBT_Impl_rbt_all xb (impl_of xc);

init ::
  forall a b c.
    (Collection_Order.Ccompare a) => Mapping_rbt a b ->
                                       ([(c, RBT_Impl.Rbt a b)],
 RBT_Impl.Rbt a b);
init xa = RBT_ext.rbt_init (impl_of xa);

join ::
  forall a b.
    (Collection_Order.Ccompare a) => (a -> b -> b -> b) ->
                                       Mapping_rbt a b ->
 Mapping_rbt a b -> Mapping_rbt a b;
join xc xd xe =
  Mapping_RBT
    (RBT_Comparator_Impl.rbt_comp_union_with_key
      (Option.the Collection_Order.ccompare) xc (impl_of xd) (impl_of xe));

meet ::
  forall a b.
    (Collection_Order.Ccompare a) => (a -> b -> b -> b) ->
                                       Mapping_rbt a b ->
 Mapping_rbt a b -> Mapping_rbt a b;
meet xc xd xe =
  Mapping_RBT
    (RBT_Comparator_Impl.rbt_comp_inter_with_key
      (Option.the Collection_Order.ccompare) xc (impl_of xd) (impl_of xe));

empty :: forall a b. (Collection_Order.Ccompare a) => Mapping_rbt a b;
empty = Mapping_RBT RBT_Impl.Empty;

delete ::
  forall a b.
    (Collection_Order.Ccompare a) => a -> Mapping_rbt a b -> Mapping_rbt a b;
delete xb xc =
  Mapping_RBT
    (RBT_Comparator_Impl.rbt_comp_delete (Option.the Collection_Order.ccompare)
      xb (impl_of xc));

filtera ::
  forall a b.
    (Collection_Order.Ccompare a) => ((a, b) -> Bool) ->
                                       Mapping_rbt a b -> Mapping_rbt a b;
filtera xb xc =
  Mapping_RBT (RBT_Impl.rbtreeify (filter xb (RBT_Impl.entries (impl_of xc))));

insert ::
  forall a b.
    (Collection_Order.Ccompare a) => a -> b ->
    Mapping_rbt a b -> Mapping_rbt a b;
insert xc xd xe =
  Mapping_RBT
    (RBT_Comparator_Impl.rbt_comp_insert (Option.the Collection_Order.ccompare)
      xc xd (impl_of xe));

lookup ::
  forall a b. (Collection_Order.Ccompare a) => Mapping_rbt a b -> a -> Maybe b;
lookup xa =
  RBT_Comparator_Impl.rbt_comp_lookup (Option.the Collection_Order.ccompare)
    (impl_of xa);

product ::
  forall a d b e c.
    (Collection_Order.Ccompare a,
      Collection_Order.Ccompare b) => (a -> d -> b -> e -> c) ->
Mapping_rbt a d -> Mapping_rbt b e -> Mapping_rbt (a, b) c;
product xc xd xe =
  Mapping_RBT (RBT_ext.rbt_product xc (impl_of xd) (impl_of xe));

is_empty ::
  forall a b. (Collection_Order.Ccompare a) => Mapping_rbt a b -> Bool;
is_empty xa = (case impl_of xa of {
                RBT_Impl.Empty -> True;
                RBT_Impl.Branch _ _ _ _ _ -> False;
              });

}
