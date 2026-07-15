{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Mapping(Mapping(..), empty, delete, lookup, update, of_alist, tabulate,
           lookup_default)
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
import qualified Product_Type;
import qualified List;
import qualified Option;
import qualified AssocList;
import qualified Fun;
import qualified Comparator;
import qualified Phantom_Type;
import qualified Mapping_Impl;
import qualified Collection_Order;
import qualified RBT_Mapping2;
import qualified DAList;

data Mapping a b = Assoc_List_Mapping (DAList.Alist a b)
  | RBT_Mapping (RBT_Mapping2.Mapping_rbt a b) | Mapping (a -> Maybe b);

empty ::
  forall a b.
    (Collection_Order.Ccompare a, Mapping_Impl.Mapping_impl a) => Mapping a b;
empty =
  Mapping_Impl.mapping_empty
    (Phantom_Type.of_phantom
      (Mapping_Impl.mapping_impl ::
        Phantom_Type.Phantom a Mapping_Impl.Mapping_impla));

delete ::
  forall a b.
    (Collection_Order.Ccompare a, Eq a) => a -> Mapping a b -> Mapping a b;
delete k (RBT_Mapping t) =
  (case (Collection_Order.ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "delete RBT_Mapping: ccompare = None" (\ _ -> delete k (RBT_Mapping t));
    Just _ -> RBT_Mapping (RBT_Mapping2.delete k t);
  });
delete k (Assoc_List_Mapping al) = Assoc_List_Mapping (AssocList.delete k al);
delete k (Mapping m) = Mapping (Fun.fun_upd m k Nothing);

lookup ::
  forall a b.
    (Collection_Order.Ccompare a, Eq a) => Mapping a b -> a -> Maybe b;
lookup (RBT_Mapping t) = RBT_Mapping2.lookup t;
lookup (Assoc_List_Mapping al) = DAList.lookup al;

update ::
  forall a b.
    (Collection_Order.Ccompare a, Eq a) => a -> b -> Mapping a b -> Mapping a b;
update k v (RBT_Mapping t) =
  (case (Collection_Order.ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "update RBT_Mapping: ccompare = None"
        (\ _ -> update k v (RBT_Mapping t));
    Just _ -> RBT_Mapping (RBT_Mapping2.insert k v t);
  });
update k v (Assoc_List_Mapping al) = Assoc_List_Mapping (DAList.update k v al);
update k v (Mapping m) = Mapping (Fun.fun_upd m k (Just v));

of_alist ::
  forall a b.
    (Collection_Order.Ccompare a, Eq a,
      Mapping_Impl.Mapping_impl a) => [(a, b)] -> Mapping a b;
of_alist xs = List.foldr (\ (a, b) -> update a b) xs empty;

tabulate ::
  forall a b.
    (Collection_Order.Ccompare a, Eq a,
      Mapping_Impl.Mapping_impl a) => [a] -> (a -> b) -> Mapping a b;
tabulate xs f = List.fold (\ k -> update k (f k)) xs empty;

lookup_default ::
  forall a b. (Collection_Order.Ccompare b, Eq b) => a -> Mapping b a -> b -> a;
lookup_default d m k = (case lookup m k of {
                         Nothing -> d;
                         Just v -> v;
                       });

}
