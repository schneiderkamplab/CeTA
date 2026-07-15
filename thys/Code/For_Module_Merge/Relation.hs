{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Relation(image, relcomp, converse) where {

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
import qualified Option;
import qualified RBT_Set2;
import qualified List;
import qualified RBT_Mapping2;
import qualified DList_Set;
import qualified Comparator;
import qualified Set;
import qualified Set_Impl;
import qualified Collection_Order;
import qualified Collection_Eq;

image ::
  forall a b.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a, Collection_Eq.Ceq b,
      Collection_Order.Ccompare b,
      Set_Impl.Set_impl b) => Set.Set (a, b) -> Set.Set a -> Set.Set b;
image (Set.RBT_set rbt) c =
  (case (Collection_Order.ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "Image RBT_set: ccompare1 = None" (\ _ -> image (Set.RBT_set rbt) c);
    Just _ ->
      (case (Collection_Order.ccompare :: Maybe (b -> b -> Comparator.Order)) of
        {
        Nothing ->
          (error :: forall a. String -> (() -> a) -> a)
            "Image RBT_set: ccompare2 = None"
            (\ _ -> image (Set.RBT_set rbt) c);
        Just _ ->
          RBT_Set2.fold
            (\ (x, y) acc -> (if Set.member x c then Set.insert y acc else acc))
            rbt Set.bot_set;
      });
  });
image (Set.DList_set dxs) b =
  (case (Collection_Eq.ceq :: Maybe (a -> a -> Bool)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "Image DList_set: ceq1 = None" (\ _ -> image (Set.DList_set dxs) b);
    Just _ ->
      (case (Collection_Eq.ceq :: Maybe (b -> b -> Bool)) of {
        Nothing ->
          (error :: forall a. String -> (() -> a) -> a)
            "Image DList_set: ceq2 = None" (\ _ -> image (Set.DList_set dxs) b);
        Just _ ->
          DList_Set.fold
            (\ (x, y) acc -> (if Set.member x b then Set.insert y acc else acc))
            dxs Set.bot_set;
      });
  });
image (Set.Set_Monad rxs) a =
  Set.Set_Monad
    (List.fold (\ (x, y) rest -> (if Set.member x a then y : rest else rest))
      rxs []);
image x y = Set.image snd (Set.filtera (\ (xa, _) -> Set.member xa y) x);

relcomp ::
  forall a b c.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a, Set_Impl.Set_impl a,
      Collection_Eq.Ceq b, Collection_Order.Ccompare b, Collection_Eq.Ceq c,
      Collection_Order.Ccompare c,
      Set_Impl.Set_impl c) => Set.Set (a, b) ->
                                Set.Set (b, c) -> Set.Set (a, c);
relcomp (Set.RBT_set rbt1) (Set.RBT_set rbt2) =
  (case (Collection_Order.ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "relcomp RBT_set RBT_set: ccompare1 = None"
        (\ _ -> relcomp (Set.RBT_set rbt1) (Set.RBT_set rbt2));
    Just _ ->
      (case Collection_Order.ccompare of {
        Nothing ->
          (error :: forall a. String -> (() -> a) -> a)
            "relcomp RBT_set RBT_set: ccompare2 = None"
            (\ _ -> relcomp (Set.RBT_set rbt1) (Set.RBT_set rbt2));
        Just c_b ->
          (case (Collection_Order.ccompare ::
                  Maybe (c -> c -> Comparator.Order))
            of {
            Nothing ->
              (error :: forall a. String -> (() -> a) -> a)
                "relcomp RBT_set RBT_set: ccompare3 = None"
                (\ _ -> relcomp (Set.RBT_set rbt1) (Set.RBT_set rbt2));
            Just _ ->
              RBT_Set2.fold
                (\ (x, y) ->
                  RBT_Set2.fold
                    (\ (ya, z) a ->
                      (if not (Comparator.equal_order (c_b y ya) Comparator.Eqa)
                        then a else Set.insert (x, z) a))
                    rbt2)
                rbt1 Set.bot_set;
          });
      });
  });
relcomp (Set.RBT_set rbt3) (Set.DList_set dxs1) =
  (case (Collection_Order.ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "relcomp RBT_set DList_set: ccompare1 = None"
        (\ _ -> relcomp (Set.RBT_set rbt3) (Set.DList_set dxs1));
    Just _ ->
      (case (Collection_Order.ccompare :: Maybe (b -> b -> Comparator.Order)) of
        {
        Nothing ->
          (error :: forall a. String -> (() -> a) -> a)
            "relcomp RBT_set DList_set: ccompare2 = None"
            (\ _ -> relcomp (Set.RBT_set rbt3) (Set.DList_set dxs1));
        Just _ ->
          (case Collection_Eq.ceq of {
            Nothing ->
              (error :: forall a. String -> (() -> a) -> a)
                "relcomp RBT_set DList_set: ceq2 = None"
                (\ _ -> relcomp (Set.RBT_set rbt3) (Set.DList_set dxs1));
            Just eq ->
              (case (Collection_Eq.ceq :: Maybe (c -> c -> Bool)) of {
                Nothing ->
                  (error :: forall a. String -> (() -> a) -> a)
                    "relcomp RBT_set DList_set: ceq3 = None"
                    (\ _ -> relcomp (Set.RBT_set rbt3) (Set.DList_set dxs1));
                Just _ ->
                  RBT_Set2.fold
                    (\ (x, y) ->
                      DList_Set.fold
                        (\ (ya, z) a ->
                          (if eq y ya then Set.insert (x, z) a else a))
                        dxs1)
                    rbt3 Set.bot_set;
              });
          });
      });
  });
relcomp (Set.DList_set dxs2) (Set.RBT_set rbt4) =
  (case (Collection_Eq.ceq :: Maybe (a -> a -> Bool)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "relcomp DList_set RBT_set: ceq1 = None"
        (\ _ -> relcomp (Set.DList_set dxs2) (Set.RBT_set rbt4));
    Just _ ->
      (case (Collection_Order.ccompare :: Maybe (b -> b -> Comparator.Order)) of
        {
        Nothing ->
          (error :: forall a. String -> (() -> a) -> a)
            "relcomp DList_set RBT_set: ceq2 = None"
            (\ _ -> relcomp (Set.DList_set dxs2) (Set.RBT_set rbt4));
        Just _ ->
          (case Collection_Eq.ceq of {
            Nothing ->
              (error :: forall a. String -> (() -> a) -> a)
                "relcomp DList_set RBT_set: ccompare2 = None"
                (\ _ -> relcomp (Set.DList_set dxs2) (Set.RBT_set rbt4));
            Just eq ->
              (case (Collection_Order.ccompare ::
                      Maybe (c -> c -> Comparator.Order))
                of {
                Nothing ->
                  (error :: forall a. String -> (() -> a) -> a)
                    "relcomp DList_set RBT_set: ccompare3 = None"
                    (\ _ -> relcomp (Set.DList_set dxs2) (Set.RBT_set rbt4));
                Just _ ->
                  DList_Set.fold
                    (\ (x, y) ->
                      RBT_Set2.fold
                        (\ (ya, z) a ->
                          (if eq y ya then Set.insert (x, z) a else a))
                        rbt4)
                    dxs2 Set.bot_set;
              });
          });
      });
  });
relcomp (Set.DList_set dxs3) (Set.DList_set dxs4) =
  (case (Collection_Eq.ceq :: Maybe (a -> a -> Bool)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "relcomp DList_set DList_set: ceq1 = None"
        (\ _ -> relcomp (Set.DList_set dxs3) (Set.DList_set dxs4));
    Just _ ->
      (case Collection_Eq.ceq of {
        Nothing ->
          (error :: forall a. String -> (() -> a) -> a)
            "relcomp DList_set DList_set: ceq2 = None"
            (\ _ -> relcomp (Set.DList_set dxs3) (Set.DList_set dxs4));
        Just eq ->
          (case (Collection_Eq.ceq :: Maybe (c -> c -> Bool)) of {
            Nothing ->
              (error :: forall a. String -> (() -> a) -> a)
                "relcomp DList_set DList_set: ceq3 = None"
                (\ _ -> relcomp (Set.DList_set dxs3) (Set.DList_set dxs4));
            Just _ ->
              DList_Set.fold
                (\ (x, y) ->
                  DList_Set.fold
                    (\ (ya, z) a ->
                      (if eq y ya then Set.insert (x, z) a else a))
                    dxs4)
                dxs3 Set.bot_set;
          });
      });
  });
relcomp (Set.Set_Monad xs1) (Set.Set_Monad xs2) =
  (case Collection_Eq.ceq of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "relcomp Set_Monad Set_Monad: ceq = None"
        (\ _ -> relcomp (Set.Set_Monad xs1) (Set.Set_Monad xs2));
    Just eq ->
      List.fold
        (\ (x, y) ->
          List.fold
            (\ (ya, z) a -> (if eq y ya then Set.insert (x, z) a else a)) xs2)
        xs1 Set.bot_set;
  });
relcomp (Set.RBT_set rbt1) (Set.Set_Monad xs3) =
  (case (Collection_Order.ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "relcomp RBT_set Set_Monad: ccompare1 = None"
        (\ _ -> relcomp (Set.RBT_set rbt1) (Set.Set_Monad xs3));
    Just _ ->
      (case Collection_Order.ccompare of {
        Nothing ->
          (error :: forall a. String -> (() -> a) -> a)
            "relcomp RBT_set Set_Monad: ccompare2 = None"
            (\ _ -> relcomp (Set.RBT_set rbt1) (Set.Set_Monad xs3));
        Just c_b ->
          RBT_Set2.fold
            (\ (x, y) ->
              List.fold
                (\ (ya, z) a ->
                  (if not (Comparator.equal_order (c_b y ya) Comparator.Eqa)
                    then a else Set.insert (x, z) a))
                xs3)
            rbt1 Set.bot_set;
      });
  });
relcomp (Set.Set_Monad xs4) (Set.RBT_set rbt5) =
  (case (Collection_Order.ccompare :: Maybe (c -> c -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "relcomp Set_Monad RBT_set: ccompare1 = None"
        (\ _ -> relcomp (Set.Set_Monad xs4) (Set.RBT_set rbt5));
    Just _ ->
      (case Collection_Order.ccompare of {
        Nothing ->
          (error :: forall a. String -> (() -> a) -> a)
            "relcomp Set_Monad RBT_set: ccompare2 = None"
            (\ _ -> relcomp (Set.Set_Monad xs4) (Set.RBT_set rbt5));
        Just c_b ->
          List.fold
            (\ (x, y) ->
              RBT_Set2.fold
                (\ (ya, z) a ->
                  (if not (Comparator.equal_order (c_b y ya) Comparator.Eqa)
                    then a else Set.insert (x, z) a))
                rbt5)
            xs4 Set.bot_set;
      });
  });
relcomp (Set.DList_set dxs3) (Set.Set_Monad xs5) =
  (case (Collection_Eq.ceq :: Maybe (a -> a -> Bool)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "relcomp DList_set Set_Monad: ceq1 = None"
        (\ _ -> relcomp (Set.DList_set dxs3) (Set.Set_Monad xs5));
    Just _ ->
      (case Collection_Eq.ceq of {
        Nothing ->
          (error :: forall a. String -> (() -> a) -> a)
            "relcomp DList_set Set_Monad: ceq2 = None"
            (\ _ -> relcomp (Set.DList_set dxs3) (Set.Set_Monad xs5));
        Just eq ->
          DList_Set.fold
            (\ (x, y) ->
              List.fold
                (\ (ya, z) a -> (if eq y ya then Set.insert (x, z) a else a))
                xs5)
            dxs3 Set.bot_set;
      });
  });
relcomp (Set.Set_Monad xs6) (Set.DList_set dxs4) =
  (case Collection_Eq.ceq of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "relcomp Set_Monad DList_set: ceq1 = None"
        (\ _ -> relcomp (Set.Set_Monad xs6) (Set.DList_set dxs4));
    Just eq ->
      (case (Collection_Eq.ceq :: Maybe (c -> c -> Bool)) of {
        Nothing ->
          (error :: forall a. String -> (() -> a) -> a)
            "relcomp Set_Monad DList_set: ceq2 = None"
            (\ _ -> relcomp (Set.Set_Monad xs6) (Set.DList_set dxs4));
        Just _ ->
          List.fold
            (\ (x, y) ->
              DList_Set.fold
                (\ (ya, z) a -> (if eq y ya then Set.insert (x, z) a else a))
                dxs4)
            xs6 Set.bot_set;
      });
  });

converse ::
  forall a b.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a, Set_Impl.Set_impl a,
      Collection_Eq.Ceq b, Collection_Order.Ccompare b,
      Set_Impl.Set_impl b) => Set.Set (a, b) -> Set.Set (b, a);
converse r = Set.image (\ (x, y) -> (y, x)) r;

}
