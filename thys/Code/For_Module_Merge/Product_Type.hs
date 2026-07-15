{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Product_Type(apfst, apsnd, curry, product, map_prod, swap) where {

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
import qualified Option;
import qualified RBT_Set2;
import qualified List;
import qualified RBT_Mapping2;
import qualified DList_Set;
import qualified Comparator;
import qualified Set;
import qualified Collection_Order;
import qualified Set_Impl;
import qualified Collection_Eq;

apfst :: forall a b c. (a -> b) -> (a, c) -> (b, c);
apfst f (x, y) = (f x, y);

apsnd :: forall a b c. (a -> b) -> (c, a) -> (c, b);
apsnd f (x, y) = (x, f y);

curry :: forall a b c. ((a, b) -> c) -> a -> b -> c;
curry f a b = f (a, b);

product ::
  forall a b.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a, Set_Impl.Set_impl a,
      Collection_Eq.Ceq b, Collection_Order.Ccompare b,
      Set_Impl.Set_impl b) => Set.Set a -> Set.Set b -> Set.Set (a, b);
product (Set.RBT_set rbt1) (Set.RBT_set rbt2) =
  (case (Collection_Order.ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "product RBT_set RBT_set: ccompare1 = None"
        (\ _ -> product (Set.RBT_set rbt1) (Set.RBT_set rbt2));
    Just _ ->
      (case (Collection_Order.ccompare :: Maybe (b -> b -> Comparator.Order)) of
        {
        Nothing ->
          (error :: forall a. String -> (() -> a) -> a)
            "product RBT_set RBT_set: ccompare2 = None"
            (\ _ -> product (Set.RBT_set rbt1) (Set.RBT_set rbt2));
        Just _ -> Set.RBT_set (RBT_Set2.product rbt1 rbt2);
      });
  });
product a2 (Set.RBT_set rbt2) =
  (case (Collection_Order.ccompare :: Maybe (b -> b -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "product RBT_set: ccompare2 = None"
        (\ _ -> product a2 (Set.RBT_set rbt2));
    Just _ ->
      RBT_Set2.fold (\ y -> Set.sup_set (Set.image (\ x -> (x, y)) a2)) rbt2
        Set.bot_set;
  });
product (Set.RBT_set rbt1) b2 =
  (case (Collection_Order.ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "product RBT_set: ccompare1 = None"
        (\ _ -> product (Set.RBT_set rbt1) b2);
    Just _ ->
      RBT_Set2.fold (\ x -> Set.sup_set (Set.image (\ a -> (x, a)) b2)) rbt1
        Set.bot_set;
  });
product (Set.DList_set dxs) (Set.DList_set dys) =
  (case (Collection_Eq.ceq :: Maybe (a -> a -> Bool)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "product DList_set DList_set: ceq1 = None"
        (\ _ -> product (Set.DList_set dxs) (Set.DList_set dys));
    Just _ ->
      (case (Collection_Eq.ceq :: Maybe (b -> b -> Bool)) of {
        Nothing ->
          (error :: forall a. String -> (() -> a) -> a)
            "product DList_set DList_set: ceq2 = None"
            (\ _ -> product (Set.DList_set dxs) (Set.DList_set dys));
        Just _ -> Set.DList_set (DList_Set.product dxs dys);
      });
  });
product a1 (Set.DList_set dys) =
  (case (Collection_Eq.ceq :: Maybe (b -> b -> Bool)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "product DList_set2: ceq = None"
        (\ _ -> product a1 (Set.DList_set dys));
    Just _ ->
      DList_Set.fold (\ y -> Set.sup_set (Set.image (\ x -> (x, y)) a1)) dys
        Set.bot_set;
  });
product (Set.DList_set dxs) b1 =
  (case (Collection_Eq.ceq :: Maybe (a -> a -> Bool)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "product DList_set1: ceq = None"
        (\ _ -> product (Set.DList_set dxs) b1);
    Just _ ->
      DList_Set.fold (\ x -> Set.sup_set (Set.image (\ a -> (x, a)) b1)) dxs
        Set.bot_set;
  });
product (Set.Set_Monad xs) (Set.Set_Monad ys) =
  Set.Set_Monad
    (List.fold (\ x -> List.fold (\ y -> (\ a -> (x, y) : a)) ys) xs []);
product a b = Set.Collect_set (\ (x, y) -> Set.member x a && Set.member y b);

map_prod :: forall a b c d. (a -> b) -> (c -> d) -> (a, c) -> (b, d);
map_prod f g (a, b) = (f a, g b);

swap :: forall a b. (a, b) -> (b, a);
swap p = (snd p, fst p);

}
