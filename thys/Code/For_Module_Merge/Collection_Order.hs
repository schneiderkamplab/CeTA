{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Collection_Order(Ccompare(..), Cproper_interval(..)) where {

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
import qualified Compare_Instances;
import qualified Set_Linorder;
import qualified Lexicographic_Order;
import qualified RBT_ext;
import qualified Option;
import qualified Finite_Set;
import qualified List;
import qualified RBT_Mapping2;
import qualified List_Fusion;
import qualified RBT_Impl;
import qualified Str;
import qualified Set;
import qualified Cardinality;
import qualified Set_Impl;
import qualified Collection_Eq;
import qualified Comparator;
import qualified Arith;

ccompare_int :: Maybe (Arith.Int -> Arith.Int -> Comparator.Order);
ccompare_int = Just Compare_Instances.compare_int;

class Ccompare a where {
  ccompare :: Maybe (a -> a -> Comparator.Order);
};

instance Ccompare Arith.Int where {
  ccompare = ccompare_int;
};

ccompare_nat :: Maybe (Arith.Nat -> Arith.Nat -> Comparator.Order);
ccompare_nat = Just Compare_Instances.compare_nat;

instance Ccompare Arith.Nat where {
  ccompare = ccompare_nat;
};

cproper_interval_nat :: Maybe Arith.Nat -> Maybe Arith.Nat -> Bool;
cproper_interval_nat = Set_Linorder.proper_interval_nat;

class (Ccompare a) => Cproper_interval a where {
  cproper_interval :: Maybe a -> Maybe a -> Bool;
};

instance Cproper_interval Arith.Nat where {
  cproper_interval = cproper_interval_nat;
};

ccompare_set ::
  forall a.
    (Cardinality.Finite_UNIV a, Collection_Eq.Ceq a, Cproper_interval a,
      Set_Impl.Set_impl a) => Maybe (Set.Set a ->
                                      Set.Set a -> Comparator.Order);
ccompare_set =
  (case (ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing -> Nothing;
    Just _ -> Just (Comparator.comp_of_ords cless_eq_set cless_set);
  });

cless_set ::
  forall a.
    (Cardinality.Finite_UNIV a, Collection_Eq.Ceq a, Cproper_interval a,
      Set_Impl.Set_impl a) => Set.Set a -> Set.Set a -> Bool;
cless_set (Set.Complement (Set.RBT_set rbt1)) (Set.RBT_set rbt2) =
  (case ccompare of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "cless_set (Complement RBT_set) RBT_set: ccompare = None"
        (\ _ ->
          cless_set (Set.Complement (Set.RBT_set rbt1)) (Set.RBT_set rbt2));
    Just c ->
      (Finite_Set.finite :: Set.Set a -> Bool) (Set.top_set :: Set.Set a) &&
        Set_Linorder.compl_set_less_aux_fusion (Comparator.lt_of_comp c)
          cproper_interval RBT_ext.rbt_keys_generator RBT_ext.rbt_keys_generator
          Nothing (RBT_Mapping2.init rbt1) (RBT_Mapping2.init rbt2);
  });
cless_set (Set.RBT_set rbt1) (Set.Complement (Set.RBT_set rbt2)) =
  (case ccompare of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "cless_set RBT_set (Complement RBT_set): ccompare = None"
        (\ _ ->
          cless_set (Set.RBT_set rbt1) (Set.Complement (Set.RBT_set rbt2)));
    Just c ->
      (if (Finite_Set.finite :: Set.Set a -> Bool) (Set.top_set :: Set.Set a)
        then Set_Linorder.set_less_aux_Compl_fusion (Comparator.lt_of_comp c)
               cproper_interval RBT_ext.rbt_keys_generator
               RBT_ext.rbt_keys_generator Nothing (RBT_Mapping2.init rbt1)
               (RBT_Mapping2.init rbt2)
        else True);
  });
cless_set (Set.RBT_set rbta) (Set.RBT_set rbt) =
  (case ccompare of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "cless_set RBT_set RBT_set: ccompare = None"
        (\ _ -> cless_set (Set.RBT_set rbta) (Set.RBT_set rbt));
    Just c ->
      Lexicographic_Order.lexord_fusion (\ x y -> Comparator.lt_of_comp c y x)
        RBT_ext.rbt_keys_generator RBT_ext.rbt_keys_generator
        (RBT_Mapping2.init rbta) (RBT_Mapping2.init rbt);
  });
cless_set (Set.Complement a) (Set.Complement b) =
  (case (ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "cless_set Complement Complement: ccompare = None"
        (\ _ -> cless_set (Set.Complement a) (Set.Complement b));
    Just _ -> Comparator.lt_of_comp (Option.the ccompare_set) b a;
  });
cless_set (Set.Complement a) b =
  (case ccompare of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "cless_set Complement1: ccompare = None"
        (\ _ -> cless_set (Set.Complement a) b);
    Just c ->
      (if Finite_Set.finite a && Finite_Set.finite b
        then (Finite_Set.finite :: Set.Set a -> Bool)
               (Set.top_set :: Set.Set a) &&
               Set_Linorder.compl_set_less_aux (Comparator.lt_of_comp c)
                 cproper_interval Nothing (Set_Impl.csorted_list_of_set a)
                 (Set_Impl.csorted_list_of_set b)
        else (error :: forall a. String -> (() -> a) -> a)
               "cless_set Complement1: infinite set"
               (\ _ -> cless_set (Set.Complement a) b));
  });
cless_set a (Set.Complement b) =
  (case ccompare of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "cless_set Complement2: ccompare = None"
        (\ _ -> cless_set a (Set.Complement b));
    Just c ->
      (if Finite_Set.finite a && Finite_Set.finite b
        then (if (Finite_Set.finite :: Set.Set a -> Bool)
                   (Set.top_set :: Set.Set a)
               then Set_Linorder.set_less_aux_Compl (Comparator.lt_of_comp c)
                      cproper_interval Nothing (Set_Impl.csorted_list_of_set a)
                      (Set_Impl.csorted_list_of_set b)
               else True)
        else (error :: forall a. String -> (() -> a) -> a)
               "cless_set Complement2: infinite set"
               (\ _ -> cless_set a (Set.Complement b)));
  });
cless_set a b =
  (case ccompare of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a) "cless_set: ccompare = None"
        (\ _ -> cless_set a b);
    Just c ->
      (if Finite_Set.finite a && Finite_Set.finite b
        then List.lexordp (\ x y -> Comparator.lt_of_comp c y x)
               (Set_Impl.csorted_list_of_set a) (Set_Impl.csorted_list_of_set b)
        else (error :: forall a. String -> (() -> a) -> a)
               "cless_set: infinite set" (\ _ -> cless_set a b));
  });

cless_eq_set ::
  forall a.
    (Cardinality.Finite_UNIV a, Collection_Eq.Ceq a, Cproper_interval a,
      Set_Impl.Set_impl a) => Set.Set a -> Set.Set a -> Bool;
cless_eq_set (Set.Complement (Set.RBT_set rbt1)) (Set.RBT_set rbt2) =
  (case ccompare of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "cless_eq_set (Complement RBT_set) RBT_set: ccompare = None"
        (\ _ ->
          cless_eq_set (Set.Complement (Set.RBT_set rbt1)) (Set.RBT_set rbt2));
    Just c ->
      (Finite_Set.finite :: Set.Set a -> Bool) (Set.top_set :: Set.Set a) &&
        Set_Linorder.compl_set_less_eq_aux_fusion (Comparator.lt_of_comp c)
          cproper_interval RBT_ext.rbt_keys_generator RBT_ext.rbt_keys_generator
          Nothing (RBT_Mapping2.init rbt1) (RBT_Mapping2.init rbt2);
  });
cless_eq_set (Set.RBT_set rbt1) (Set.Complement (Set.RBT_set rbt2)) =
  (case ccompare of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "cless_eq_set RBT_set (Complement RBT_set): ccompare = None"
        (\ _ ->
          cless_eq_set (Set.RBT_set rbt1) (Set.Complement (Set.RBT_set rbt2)));
    Just c ->
      (if (Finite_Set.finite :: Set.Set a -> Bool) (Set.top_set :: Set.Set a)
        then Set_Linorder.set_less_eq_aux_Compl_fusion (Comparator.lt_of_comp c)
               cproper_interval RBT_ext.rbt_keys_generator
               RBT_ext.rbt_keys_generator Nothing (RBT_Mapping2.init rbt1)
               (RBT_Mapping2.init rbt2)
        else True);
  });
cless_eq_set (Set.RBT_set rbta) (Set.RBT_set rbt) =
  (case ccompare of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "cless_eq_set RBT_set RBT_set: ccompare = None"
        (\ _ -> cless_eq_set (Set.RBT_set rbta) (Set.RBT_set rbt));
    Just c ->
      Lexicographic_Order.lexord_eq_fusion
        (\ x y -> Comparator.lt_of_comp c y x) RBT_ext.rbt_keys_generator
        RBT_ext.rbt_keys_generator (RBT_Mapping2.init rbta)
        (RBT_Mapping2.init rbt);
  });
cless_eq_set (Set.Complement a) (Set.Complement b) =
  (case (ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "cless_eq_set Complement Complement: ccompare = None"
        (\ _ ->
          Comparator.le_of_comp (Option.the ccompare_set) (Set.Complement a)
            (Set.Complement b));
    Just _ -> cless_eq_set b a;
  });
cless_eq_set (Set.Complement a) b =
  (case ccompare of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "cless_eq_set Complement1: ccompare = None"
        (\ _ -> cless_eq_set (Set.Complement a) b);
    Just c ->
      (if Finite_Set.finite a && Finite_Set.finite b
        then (Finite_Set.finite :: Set.Set a -> Bool)
               (Set.top_set :: Set.Set a) &&
               Set_Linorder.compl_set_less_eq_aux (Comparator.lt_of_comp c)
                 cproper_interval Nothing (Set_Impl.csorted_list_of_set a)
                 (Set_Impl.csorted_list_of_set b)
        else (error :: forall a. String -> (() -> a) -> a)
               "cless_eq_set Complement1: infinite set"
               (\ _ -> cless_eq_set (Set.Complement a) b));
  });
cless_eq_set a (Set.Complement b) =
  (case ccompare of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "cless_eq_set Complement2: ccompare = None"
        (\ _ -> cless_eq_set a (Set.Complement b));
    Just c ->
      (if Finite_Set.finite a && Finite_Set.finite b
        then (if (Finite_Set.finite :: Set.Set a -> Bool)
                   (Set.top_set :: Set.Set a)
               then Set_Linorder.set_less_eq_aux_Compl (Comparator.lt_of_comp c)
                      cproper_interval Nothing (Set_Impl.csorted_list_of_set a)
                      (Set_Impl.csorted_list_of_set b)
               else True)
        else (error :: forall a. String -> (() -> a) -> a)
               "cless_eq_set Complement2: infinite set"
               (\ _ -> cless_eq_set a (Set.Complement b)));
  });
cless_eq_set a b =
  (case ccompare of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "cless_eq_set: ccompare = None" (\ _ -> cless_eq_set a b);
    Just c ->
      (if Finite_Set.finite a && Finite_Set.finite b
        then List.lexordp_eq (\ x y -> Comparator.lt_of_comp c y x)
               (Set_Impl.csorted_list_of_set a) (Set_Impl.csorted_list_of_set b)
        else (error :: forall a. String -> (() -> a) -> a)
               "cless_eq_set: infinite set" (\ _ -> cless_eq_set a b));
  });

instance (Cardinality.Finite_UNIV a, Collection_Eq.Ceq a, Cproper_interval a,
           Set_Impl.Set_impl a) => Ccompare (Set.Set a) where {
  ccompare = ccompare_set;
};

cproper_interval_set ::
  forall a.
    (Cardinality.Card_UNIV a, Collection_Eq.Ceq a, Cproper_interval a,
      Set_Impl.Set_impl a) => Maybe (Set.Set a) -> Maybe (Set.Set a) -> Bool;
cproper_interval_set (Just (Set.Complement (Set.RBT_set rbt1)))
  (Just (Set.RBT_set rbt2)) =
  (case ccompare of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "cproper_interval (Complement RBT_set) RBT_set: ccompare = None"
        (\ _ ->
          cproper_interval_set (Just (Set.Complement (Set.RBT_set rbt1)))
            (Just (Set.RBT_set rbt2)));
    Just c ->
      (Finite_Set.finite :: Set.Set a -> Bool) (Set.top_set :: Set.Set a) &&
        Set_Linorder.proper_interval_Compl_set_aux_fusion
          (Comparator.lt_of_comp c) cproper_interval RBT_ext.rbt_keys_generator
          RBT_ext.rbt_keys_generator Nothing (RBT_Mapping2.init rbt1)
          (RBT_Mapping2.init rbt2);
  });
cproper_interval_set (Just (Set.RBT_set rbt1))
  (Just (Set.Complement (Set.RBT_set rbt2))) =
  (case ccompare of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "cproper_interval RBT_set (Complement RBT_set): ccompare = None"
        (\ _ ->
          cproper_interval_set (Just (Set.RBT_set rbt1))
            (Just (Set.Complement (Set.RBT_set rbt2))));
    Just c ->
      (Finite_Set.finite :: Set.Set a -> Bool) (Set.top_set :: Set.Set a) &&
        Set_Linorder.proper_interval_set_Compl_aux_fusion
          (Comparator.lt_of_comp c) cproper_interval RBT_ext.rbt_keys_generator
          RBT_ext.rbt_keys_generator Nothing Arith.zero_nat
          (RBT_Mapping2.init rbt1) (RBT_Mapping2.init rbt2);
  });
cproper_interval_set (Just (Set.RBT_set rbt1)) (Just (Set.RBT_set rbt2)) =
  (case ccompare of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "cproper_interval RBT_set RBT_set: ccompare = None"
        (\ _ ->
          cproper_interval_set (Just (Set.RBT_set rbt1))
            (Just (Set.RBT_set rbt2)));
    Just c ->
      (Finite_Set.finite :: Set.Set a -> Bool) (Set.top_set :: Set.Set a) &&
        Set_Linorder.proper_interval_set_aux_fusion (Comparator.lt_of_comp c)
          cproper_interval RBT_ext.rbt_keys_generator RBT_ext.rbt_keys_generator
          (RBT_Mapping2.init rbt1) (RBT_Mapping2.init rbt2);
  });
cproper_interval_set (Just (Set.Complement a)) (Just (Set.Complement b)) =
  (case (ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "cproper_interval Complement Complement: ccompare = None"
        (\ _ ->
          cproper_interval_set (Just (Set.Complement a))
            (Just (Set.Complement b)));
    Just _ -> cproper_interval_set (Just b) (Just a);
  });
cproper_interval_set (Just (Set.Complement a)) (Just b) =
  (case ccompare of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "cproper_interval Complement1: ccompare = None"
        (\ _ -> cproper_interval_set (Just (Set.Complement a)) (Just b));
    Just c ->
      (Finite_Set.finite :: Set.Set a -> Bool) (Set.top_set :: Set.Set a) &&
        Set_Linorder.proper_interval_Compl_set_aux (Comparator.lt_of_comp c)
          cproper_interval Nothing (Set_Impl.csorted_list_of_set a)
          (Set_Impl.csorted_list_of_set b);
  });
cproper_interval_set (Just a) (Just (Set.Complement b)) =
  (case ccompare of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "cproper_interval Complement2: ccompare = None"
        (\ _ -> cproper_interval_set (Just a) (Just (Set.Complement b)));
    Just c ->
      (Finite_Set.finite :: Set.Set a -> Bool) (Set.top_set :: Set.Set a) &&
        Set_Linorder.proper_interval_set_Compl_aux (Comparator.lt_of_comp c)
          cproper_interval Nothing Arith.zero_nat
          (Set_Impl.csorted_list_of_set a) (Set_Impl.csorted_list_of_set b);
  });
cproper_interval_set (Just a) (Just b) =
  (case ccompare of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "cproper_interval: ccompare = None"
        (\ _ -> cproper_interval_set (Just a) (Just b));
    Just c ->
      (Finite_Set.finite :: Set.Set a -> Bool) (Set.top_set :: Set.Set a) &&
        Set_Linorder.proper_interval_set_aux (Comparator.lt_of_comp c)
          cproper_interval (Set_Impl.csorted_list_of_set a)
          (Set_Impl.csorted_list_of_set b);
  });

instance (Cardinality.Card_UNIV a, Collection_Eq.Ceq a, Cproper_interval a,
           Set_Impl.Set_impl a) => Cproper_interval (Set.Set a) where {
  cproper_interval = cproper_interval_set;
};

ccompare_list ::
  forall a. (Ccompare a) => Maybe ([a] -> [a] -> Comparator.Order);
ccompare_list =
  (case ccompare of {
    Nothing -> Nothing;
    Just comp_a -> Just (Compare_Instances.comparator_list comp_a);
  });

instance (Ccompare a) => Ccompare [a] where {
  ccompare = ccompare_list;
};

cproper_interval_list ::
  forall a. (Ccompare a) => Maybe [a] -> Maybe [a] -> Bool;
cproper_interval_list xso yso = error "undefined";

instance (Ccompare a) => Cproper_interval [a] where {
  cproper_interval = cproper_interval_list;
};

ccompare_char :: Maybe (Str.Char -> Str.Char -> Comparator.Order);
ccompare_char = Just Compare_Instances.compare_char;

instance Ccompare Str.Char where {
  ccompare = ccompare_char;
};

ccompare_option ::
  forall a. (Ccompare a) => Maybe (Maybe a -> Maybe a -> Comparator.Order);
ccompare_option =
  (case ccompare of {
    Nothing -> Nothing;
    Just comp_a -> Just (Compare_Instances.comparator_option comp_a);
  });

instance (Ccompare a) => Ccompare (Maybe a) where {
  ccompare = ccompare_option;
};

cproper_interval_option ::
  forall a. (Cproper_interval a) => Maybe (Maybe a) -> Maybe (Maybe a) -> Bool;
cproper_interval_option Nothing Nothing = True;
cproper_interval_option Nothing (Just x) = not (Option.is_none x);
cproper_interval_option (Just x) Nothing = cproper_interval x Nothing;
cproper_interval_option (Just x) (Just Nothing) = False;
cproper_interval_option (Just x) (Just (Just y)) = cproper_interval x (Just y);

instance (Cproper_interval a) => Cproper_interval (Maybe a) where {
  cproper_interval = cproper_interval_option;
};

ccompare_prod ::
  forall a b.
    (Ccompare a, Ccompare b) => Maybe ((a, b) -> (a, b) -> Comparator.Order);
ccompare_prod =
  (case ccompare of {
    Nothing -> Nothing;
    Just comp_a ->
      (case ccompare of {
        Nothing -> Nothing;
        Just comp_b -> Just (Compare_Instances.comparator_prod comp_a comp_b);
      });
  });

instance (Ccompare a, Ccompare b) => Ccompare (a, b) where {
  ccompare = ccompare_prod;
};

cproper_interval_prod ::
  forall a b.
    (Cproper_interval a,
      Cproper_interval b) => Maybe (a, b) -> Maybe (a, b) -> Bool;
cproper_interval_prod Nothing Nothing = True;
cproper_interval_prod Nothing (Just (y1, y2)) =
  cproper_interval Nothing (Just y1) || cproper_interval Nothing (Just y2);
cproper_interval_prod (Just (x1, x2)) Nothing =
  cproper_interval (Just x1) Nothing || cproper_interval (Just x2) Nothing;
cproper_interval_prod (Just (x1, x2)) (Just (y1, y2)) =
  cproper_interval (Just x1) (Just y1) ||
    (Comparator.lt_of_comp (Option.the ccompare) x1 y1 &&
       (cproper_interval (Just x2) Nothing ||
         cproper_interval Nothing (Just y2)) ||
      not (Comparator.lt_of_comp (Option.the ccompare) y1 x1) &&
        cproper_interval (Just x2) (Just y2));

instance (Cproper_interval a,
           Cproper_interval b) => Cproper_interval (a, b) where {
  cproper_interval = cproper_interval_prod;
};

ccompare_integer :: Maybe (Integer -> Integer -> Comparator.Order);
ccompare_integer = Just Compare_Instances.compare_integer;

instance Ccompare Integer where {
  ccompare = ccompare_integer;
};

}
