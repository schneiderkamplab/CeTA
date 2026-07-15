{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Collection_Eq(Ceq(..), set_eq) where {

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
import qualified Equality_Instances;
import qualified RBT_ext;
import qualified Option;
import qualified RBT_Mapping2;
import qualified List_Fusion;
import qualified Comparator;
import qualified RBT_Impl;
import qualified Str;
import qualified Set;
import qualified Collection_Order;
import qualified Collection_Enum;
import qualified Arith;

ceq_int :: Maybe (Arith.Int -> Arith.Int -> Bool);
ceq_int = Just Arith.equal_int;

class Ceq a where {
  ceq :: Maybe (a -> a -> Bool);
};

instance Ceq Arith.Int where {
  ceq = ceq_int;
};

ceq_nat :: Maybe (Arith.Nat -> Arith.Nat -> Bool);
ceq_nat = Just Arith.equal_nat;

instance Ceq Arith.Nat where {
  ceq = ceq_nat;
};

set_eq ::
  forall a.
    (Collection_Enum.Cenum a, Ceq a,
      Collection_Order.Ccompare a) => Set.Set a -> Set.Set a -> Bool;
set_eq (Set.RBT_set rbt1) (Set.RBT_set rbt2) =
  (case Collection_Order.ccompare of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "set_eq RBT_set RBT_set: ccompare = None"
        (\ _ -> set_eq (Set.RBT_set rbt1) (Set.RBT_set rbt2));
    Just c ->
      (case ceq of {
        Nothing ->
          List_Fusion.list_all2_fusion
            (\ x y -> Comparator.equal_order (c x y) Comparator.Eqa)
            RBT_ext.rbt_keys_generator RBT_ext.rbt_keys_generator
            (RBT_Mapping2.init rbt1) (RBT_Mapping2.init rbt2);
        Just eq ->
          List_Fusion.list_all2_fusion eq RBT_ext.rbt_keys_generator
            RBT_ext.rbt_keys_generator (RBT_Mapping2.init rbt1)
            (RBT_Mapping2.init rbt2);
      });
  });
set_eq (Set.Complement a) (Set.Complement b) = set_eq a b;
set_eq a b = Set.less_eq_set a b && Set.less_eq_set b a;

ceq_set ::
  forall a.
    (Collection_Enum.Cenum a, Ceq a,
      Collection_Order.Ccompare a) => Maybe (Set.Set a -> Set.Set a -> Bool);
ceq_set = (case (ceq :: Maybe (a -> a -> Bool)) of {
            Nothing -> Nothing;
            Just _ -> Just set_eq;
          });

instance (Collection_Enum.Cenum a, Ceq a,
           Collection_Order.Ccompare a) => Ceq (Set.Set a) where {
  ceq = ceq_set;
};

ceq_list :: forall a. (Ceq a) => Maybe ([a] -> [a] -> Bool);
ceq_list = (case ceq of {
             Nothing -> Nothing;
             Just eq_a -> Just (Equality_Instances.equality_list eq_a);
           });

instance (Ceq a) => Ceq [a] where {
  ceq = ceq_list;
};

ceq_char :: Maybe (Str.Char -> Str.Char -> Bool);
ceq_char = Just Str.equal_char;

instance Ceq Str.Char where {
  ceq = ceq_char;
};

ceq_option :: forall a. (Ceq a) => Maybe (Maybe a -> Maybe a -> Bool);
ceq_option = (case ceq of {
               Nothing -> Nothing;
               Just eq_a -> Just (Equality_Instances.equality_option eq_a);
             });

instance (Ceq a) => Ceq (Maybe a) where {
  ceq = ceq_option;
};

ceq_prod :: forall a b. (Ceq a, Ceq b) => Maybe ((a, b) -> (a, b) -> Bool);
ceq_prod =
  (case ceq of {
    Nothing -> Nothing;
    Just eq_a ->
      (case ceq of {
        Nothing -> Nothing;
        Just eq_b -> Just (Equality_Instances.equality_prod eq_a eq_b);
      });
  });

instance (Ceq a, Ceq b) => Ceq (a, b) where {
  ceq = ceq_prod;
};

ceq_integer :: Maybe (Integer -> Integer -> Bool);
ceq_integer = Just (\ a b -> a == b);

instance Ceq Integer where {
  ceq = ceq_integer;
};

}
