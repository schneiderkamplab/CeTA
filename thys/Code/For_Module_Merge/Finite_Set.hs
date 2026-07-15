{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Finite_Set(finite, card) where {

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
import qualified Option;
import qualified RBT_Set2;
import qualified HOL;
import qualified RBT_Mapping2;
import qualified Phantom_Type;
import qualified DList_Set;
import qualified Comparator;
import qualified Set;
import qualified Arith;
import qualified Collection_Order;
import qualified Collection_Eq;
import qualified Cardinality;

finite ::
  forall a.
    (Cardinality.Finite_UNIV a, Collection_Eq.Ceq a,
      Collection_Order.Ccompare a) => Set.Set a -> Bool;
finite (Set.Collect_set p) =
  Phantom_Type.of_phantom
    (Cardinality.finite_UNIV :: Phantom_Type.Phantom a Bool) ||
    (error :: forall a. String -> (() -> a) -> a) "finite Collect_set"
      (\ _ -> finite (Set.Collect_set p));
finite (Set.Set_Monad xs) = True;
finite (Set.Complement a) =
  (if Phantom_Type.of_phantom
        (Cardinality.finite_UNIV :: Phantom_Type.Phantom a Bool)
    then True
    else (if finite a then False
           else (error :: forall a. String -> (() -> a) -> a)
                  "finite Complement: infinite set"
                  (\ _ -> finite (Set.Complement a))));
finite (Set.RBT_set rbt) =
  (case (Collection_Order.ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "finite RBT_set: ccompare = None" (\ _ -> finite (Set.RBT_set rbt));
    Just _ -> True;
  });
finite (Set.DList_set dxs) =
  (case (Collection_Eq.ceq :: Maybe (a -> a -> Bool)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "finite DList_set: ceq = None" (\ _ -> finite (Set.DList_set dxs));
    Just _ -> True;
  });

card ::
  forall a.
    (Cardinality.Card_UNIV a, Collection_Eq.Ceq a,
      Collection_Order.Ccompare a) => Set.Set a -> Arith.Nat;
card (Set.Complement a) =
  let {
    aa = card a;
    s = Phantom_Type.of_phantom
          (Cardinality.card_UNIV :: Phantom_Type.Phantom a Arith.Nat);
  } in (if Arith.less_nat Arith.zero_nat s then Arith.minus_nat s aa
         else (if finite a then Arith.zero_nat
                else (error :: forall a. String -> (() -> a) -> a)
                       "card Complement: infinite"
                       (\ _ -> card (Set.Complement a))));
card (Set.Set_Monad xs) =
  (case Collection_Eq.ceq of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a) "card Set_Monad: ceq = None"
        (\ _ -> card (Set.Set_Monad xs));
    Just eq -> List.size_list (DList_Set.list_remdups eq xs);
  });
card (Set.RBT_set rbt) =
  (case (Collection_Order.ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "card RBT_set: ccompare = None" (\ _ -> card (Set.RBT_set rbt));
    Just _ -> List.size_list (RBT_Set2.keys rbt);
  });
card (Set.DList_set dxs) =
  (case (Collection_Eq.ceq :: Maybe (a -> a -> Bool)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a) "card DList_set: ceq = None"
        (\ _ -> card (Set.DList_set dxs));
    Just _ -> DList_Set.length dxs;
  });

}
