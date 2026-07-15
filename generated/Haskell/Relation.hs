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
import qualified Comparator;
import qualified Arith;

image ::
  forall a b.
    (Arith.Ceq a, Arith.Ccompare a, Arith.Ceq b, Arith.Ccompare b,
      Arith.Set_impl b) => Arith.Set (a, b) -> Arith.Set a -> Arith.Set b;
image (Arith.RBT_set rbt) c =
  (case (Arith.ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "Image RBT_set: ccompare1 = None" (\ _ -> image (Arith.RBT_set rbt) c);
    Just _ ->
      (case (Arith.ccompare :: Maybe (b -> b -> Comparator.Order)) of {
        Nothing ->
          (error :: forall a. String -> (() -> a) -> a)
            "Image RBT_set: ccompare2 = None"
            (\ _ -> image (Arith.RBT_set rbt) c);
        Just _ ->
          Arith.foldb
            (\ (x, y) acc ->
              (if Arith.member x c then Arith.insert y acc else acc))
            rbt Arith.bot_set;
      });
  });
image (Arith.DList_set dxs) b =
  (case (Arith.ceq :: Maybe (a -> a -> Bool)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "Image DList_set: ceq1 = None" (\ _ -> image (Arith.DList_set dxs) b);
    Just _ ->
      (case (Arith.ceq :: Maybe (b -> b -> Bool)) of {
        Nothing ->
          (error :: forall a. String -> (() -> a) -> a)
            "Image DList_set: ceq2 = None"
            (\ _ -> image (Arith.DList_set dxs) b);
        Just _ ->
          Arith.foldc
            (\ (x, y) acc ->
              (if Arith.member x b then Arith.insert y acc else acc))
            dxs Arith.bot_set;
      });
  });
image (Arith.Set_Monad rxs) a =
  Arith.Set_Monad
    (Arith.fold (\ (x, y) rest -> (if Arith.member x a then y : rest else rest))
      rxs []);
image x y = Arith.image snd (Arith.filtera (\ (xa, _) -> Arith.member xa y) x);

relcomp ::
  forall a b c.
    (Arith.Ceq a, Arith.Ccompare a, Arith.Set_impl a, Arith.Ceq b,
      Arith.Ccompare b, Arith.Ceq c, Arith.Ccompare c,
      Arith.Set_impl c) => Arith.Set (a, b) ->
                             Arith.Set (b, c) -> Arith.Set (a, c);
relcomp (Arith.RBT_set rbt1) (Arith.RBT_set rbt2) =
  (case (Arith.ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "relcomp RBT_set RBT_set: ccompare1 = None"
        (\ _ -> relcomp (Arith.RBT_set rbt1) (Arith.RBT_set rbt2));
    Just _ ->
      (case Arith.ccompare of {
        Nothing ->
          (error :: forall a. String -> (() -> a) -> a)
            "relcomp RBT_set RBT_set: ccompare2 = None"
            (\ _ -> relcomp (Arith.RBT_set rbt1) (Arith.RBT_set rbt2));
        Just c_b ->
          (case (Arith.ccompare :: Maybe (c -> c -> Comparator.Order)) of {
            Nothing ->
              (error :: forall a. String -> (() -> a) -> a)
                "relcomp RBT_set RBT_set: ccompare3 = None"
                (\ _ -> relcomp (Arith.RBT_set rbt1) (Arith.RBT_set rbt2));
            Just _ ->
              Arith.foldb
                (\ (x, y) ->
                  Arith.foldb
                    (\ (ya, z) a ->
                      (if not (Comparator.equal_order (c_b y ya) Comparator.Eqa)
                        then a else Arith.insert (x, z) a))
                    rbt2)
                rbt1 Arith.bot_set;
          });
      });
  });
relcomp (Arith.RBT_set rbt3) (Arith.DList_set dxs1) =
  (case (Arith.ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "relcomp RBT_set DList_set: ccompare1 = None"
        (\ _ -> relcomp (Arith.RBT_set rbt3) (Arith.DList_set dxs1));
    Just _ ->
      (case (Arith.ccompare :: Maybe (b -> b -> Comparator.Order)) of {
        Nothing ->
          (error :: forall a. String -> (() -> a) -> a)
            "relcomp RBT_set DList_set: ccompare2 = None"
            (\ _ -> relcomp (Arith.RBT_set rbt3) (Arith.DList_set dxs1));
        Just _ ->
          (case Arith.ceq of {
            Nothing ->
              (error :: forall a. String -> (() -> a) -> a)
                "relcomp RBT_set DList_set: ceq2 = None"
                (\ _ -> relcomp (Arith.RBT_set rbt3) (Arith.DList_set dxs1));
            Just eq ->
              (case (Arith.ceq :: Maybe (c -> c -> Bool)) of {
                Nothing ->
                  (error :: forall a. String -> (() -> a) -> a)
                    "relcomp RBT_set DList_set: ceq3 = None"
                    (\ _ ->
                      relcomp (Arith.RBT_set rbt3) (Arith.DList_set dxs1));
                Just _ ->
                  Arith.foldb
                    (\ (x, y) ->
                      Arith.foldc
                        (\ (ya, z) a ->
                          (if eq y ya then Arith.insert (x, z) a else a))
                        dxs1)
                    rbt3 Arith.bot_set;
              });
          });
      });
  });
relcomp (Arith.DList_set dxs2) (Arith.RBT_set rbt4) =
  (case (Arith.ceq :: Maybe (a -> a -> Bool)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "relcomp DList_set RBT_set: ceq1 = None"
        (\ _ -> relcomp (Arith.DList_set dxs2) (Arith.RBT_set rbt4));
    Just _ ->
      (case (Arith.ccompare :: Maybe (b -> b -> Comparator.Order)) of {
        Nothing ->
          (error :: forall a. String -> (() -> a) -> a)
            "relcomp DList_set RBT_set: ceq2 = None"
            (\ _ -> relcomp (Arith.DList_set dxs2) (Arith.RBT_set rbt4));
        Just _ ->
          (case Arith.ceq of {
            Nothing ->
              (error :: forall a. String -> (() -> a) -> a)
                "relcomp DList_set RBT_set: ccompare2 = None"
                (\ _ -> relcomp (Arith.DList_set dxs2) (Arith.RBT_set rbt4));
            Just eq ->
              (case (Arith.ccompare :: Maybe (c -> c -> Comparator.Order)) of {
                Nothing ->
                  (error :: forall a. String -> (() -> a) -> a)
                    "relcomp DList_set RBT_set: ccompare3 = None"
                    (\ _ ->
                      relcomp (Arith.DList_set dxs2) (Arith.RBT_set rbt4));
                Just _ ->
                  Arith.foldc
                    (\ (x, y) ->
                      Arith.foldb
                        (\ (ya, z) a ->
                          (if eq y ya then Arith.insert (x, z) a else a))
                        rbt4)
                    dxs2 Arith.bot_set;
              });
          });
      });
  });
relcomp (Arith.DList_set dxs3) (Arith.DList_set dxs4) =
  (case (Arith.ceq :: Maybe (a -> a -> Bool)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "relcomp DList_set DList_set: ceq1 = None"
        (\ _ -> relcomp (Arith.DList_set dxs3) (Arith.DList_set dxs4));
    Just _ ->
      (case Arith.ceq of {
        Nothing ->
          (error :: forall a. String -> (() -> a) -> a)
            "relcomp DList_set DList_set: ceq2 = None"
            (\ _ -> relcomp (Arith.DList_set dxs3) (Arith.DList_set dxs4));
        Just eq ->
          (case (Arith.ceq :: Maybe (c -> c -> Bool)) of {
            Nothing ->
              (error :: forall a. String -> (() -> a) -> a)
                "relcomp DList_set DList_set: ceq3 = None"
                (\ _ -> relcomp (Arith.DList_set dxs3) (Arith.DList_set dxs4));
            Just _ ->
              Arith.foldc
                (\ (x, y) ->
                  Arith.foldc
                    (\ (ya, z) a ->
                      (if eq y ya then Arith.insert (x, z) a else a))
                    dxs4)
                dxs3 Arith.bot_set;
          });
      });
  });
relcomp (Arith.Set_Monad xs1) (Arith.Set_Monad xs2) =
  (case Arith.ceq of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "relcomp Set_Monad Set_Monad: ceq = None"
        (\ _ -> relcomp (Arith.Set_Monad xs1) (Arith.Set_Monad xs2));
    Just eq ->
      Arith.fold
        (\ (x, y) ->
          Arith.fold
            (\ (ya, z) a -> (if eq y ya then Arith.insert (x, z) a else a)) xs2)
        xs1 Arith.bot_set;
  });
relcomp (Arith.RBT_set rbt1) (Arith.Set_Monad xs3) =
  (case (Arith.ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "relcomp RBT_set Set_Monad: ccompare1 = None"
        (\ _ -> relcomp (Arith.RBT_set rbt1) (Arith.Set_Monad xs3));
    Just _ ->
      (case Arith.ccompare of {
        Nothing ->
          (error :: forall a. String -> (() -> a) -> a)
            "relcomp RBT_set Set_Monad: ccompare2 = None"
            (\ _ -> relcomp (Arith.RBT_set rbt1) (Arith.Set_Monad xs3));
        Just c_b ->
          Arith.foldb
            (\ (x, y) ->
              Arith.fold
                (\ (ya, z) a ->
                  (if not (Comparator.equal_order (c_b y ya) Comparator.Eqa)
                    then a else Arith.insert (x, z) a))
                xs3)
            rbt1 Arith.bot_set;
      });
  });
relcomp (Arith.Set_Monad xs4) (Arith.RBT_set rbt5) =
  (case (Arith.ccompare :: Maybe (c -> c -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "relcomp Set_Monad RBT_set: ccompare1 = None"
        (\ _ -> relcomp (Arith.Set_Monad xs4) (Arith.RBT_set rbt5));
    Just _ ->
      (case Arith.ccompare of {
        Nothing ->
          (error :: forall a. String -> (() -> a) -> a)
            "relcomp Set_Monad RBT_set: ccompare2 = None"
            (\ _ -> relcomp (Arith.Set_Monad xs4) (Arith.RBT_set rbt5));
        Just c_b ->
          Arith.fold
            (\ (x, y) ->
              Arith.foldb
                (\ (ya, z) a ->
                  (if not (Comparator.equal_order (c_b y ya) Comparator.Eqa)
                    then a else Arith.insert (x, z) a))
                rbt5)
            xs4 Arith.bot_set;
      });
  });
relcomp (Arith.DList_set dxs3) (Arith.Set_Monad xs5) =
  (case (Arith.ceq :: Maybe (a -> a -> Bool)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "relcomp DList_set Set_Monad: ceq1 = None"
        (\ _ -> relcomp (Arith.DList_set dxs3) (Arith.Set_Monad xs5));
    Just _ ->
      (case Arith.ceq of {
        Nothing ->
          (error :: forall a. String -> (() -> a) -> a)
            "relcomp DList_set Set_Monad: ceq2 = None"
            (\ _ -> relcomp (Arith.DList_set dxs3) (Arith.Set_Monad xs5));
        Just eq ->
          Arith.foldc
            (\ (x, y) ->
              Arith.fold
                (\ (ya, z) a -> (if eq y ya then Arith.insert (x, z) a else a))
                xs5)
            dxs3 Arith.bot_set;
      });
  });
relcomp (Arith.Set_Monad xs6) (Arith.DList_set dxs4) =
  (case Arith.ceq of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "relcomp Set_Monad DList_set: ceq1 = None"
        (\ _ -> relcomp (Arith.Set_Monad xs6) (Arith.DList_set dxs4));
    Just eq ->
      (case (Arith.ceq :: Maybe (c -> c -> Bool)) of {
        Nothing ->
          (error :: forall a. String -> (() -> a) -> a)
            "relcomp Set_Monad DList_set: ceq2 = None"
            (\ _ -> relcomp (Arith.Set_Monad xs6) (Arith.DList_set dxs4));
        Just _ ->
          Arith.fold
            (\ (x, y) ->
              Arith.foldc
                (\ (ya, z) a -> (if eq y ya then Arith.insert (x, z) a else a))
                dxs4)
            xs6 Arith.bot_set;
      });
  });

converse ::
  forall a b.
    (Arith.Ceq a, Arith.Ccompare a, Arith.Set_impl a, Arith.Ceq b,
      Arith.Ccompare b,
      Arith.Set_impl b) => Arith.Set (a, b) -> Arith.Set (b, a);
converse r = Arith.image (\ (x, y) -> (y, x)) r;

}
