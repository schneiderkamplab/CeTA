{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Set_Impl(Set_impla(..), Set_impl(..), set_impl_nat, set_impl_set,
            set_impl_list, set_impl_prod, Comp_fun_idem, Semilattice_set,
            is_UNIV, max_sls, set_empty, set_aux, sup_cfi, set_fold1,
            set_fold_cfi, csorted_list_of_set, sorted_list_subset_fusion)
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
import qualified RBT_Set2;
import qualified Quasi_Order;
import qualified Lattices;
import qualified List;
import qualified DList_Set;
import qualified Orderings;
import qualified Set_Linorder;
import qualified RBT_ext;
import qualified Option;
import qualified Finite_Set;
import qualified HOL;
import qualified RBT_Mapping2;
import qualified List_Fusion;
import qualified Comparator;
import qualified RBT_Impl;
import qualified Collection_Eq;
import qualified Collection_Order;
import qualified Cardinality;
import qualified Set;
import qualified Phantom_Type;
import qualified Arith;

data Set_impla = Set_Choose | Set_Collect | Set_DList | Set_RBT | Set_Monad;

set_impl_int :: Phantom_Type.Phantom Arith.Int Set_impla;
set_impl_int = Phantom_Type.Phantom Set_RBT;

class Set_impl a where {
  set_impl :: Phantom_Type.Phantom a Set_impla;
};

instance Set_impl Arith.Int where {
  set_impl = set_impl_int;
};

set_impl_nat :: Phantom_Type.Phantom Arith.Nat Set_impla;
set_impl_nat = Phantom_Type.Phantom Set_RBT;

instance Set_impl Arith.Nat where {
  set_impl = set_impl_nat;
};

set_impl_set :: forall a. Phantom_Type.Phantom (Set.Set a) Set_impla;
set_impl_set = Phantom_Type.Phantom Set_Choose;

instance Set_impl (Set.Set a) where {
  set_impl = set_impl_set;
};

set_impl_list :: forall a. Phantom_Type.Phantom [a] Set_impla;
set_impl_list = Phantom_Type.Phantom Set_Choose;

instance Set_impl [a] where {
  set_impl = set_impl_list;
};

set_impl_option ::
  forall a. (Set_impl a) => Phantom_Type.Phantom (Maybe a) Set_impla;
set_impl_option =
  Phantom_Type.Phantom
    (Phantom_Type.of_phantom (set_impl :: Phantom_Type.Phantom a Set_impla));

instance (Set_impl a) => Set_impl (Maybe a) where {
  set_impl = set_impl_option;
};

set_impl_choose2 :: Set_impla -> Set_impla -> Set_impla;
set_impl_choose2 Set_Monad Set_Monad = Set_Monad;
set_impl_choose2 Set_RBT Set_RBT = Set_RBT;
set_impl_choose2 Set_DList Set_DList = Set_DList;
set_impl_choose2 Set_Collect Set_Collect = Set_Collect;
set_impl_choose2 x y = Set_Choose;

set_impl_prod ::
  forall a b. (Set_impl a, Set_impl b) => Phantom_Type.Phantom (a, b) Set_impla;
set_impl_prod =
  Phantom_Type.Phantom
    (set_impl_choose2
      (Phantom_Type.of_phantom (set_impl :: Phantom_Type.Phantom a Set_impla))
      (Phantom_Type.of_phantom (set_impl :: Phantom_Type.Phantom b Set_impla)));

instance (Set_impl a, Set_impl b) => Set_impl (a, b) where {
  set_impl = set_impl_prod;
};

set_impl_integer :: Phantom_Type.Phantom Integer Set_impla;
set_impl_integer = Phantom_Type.Phantom Set_RBT;

instance Set_impl Integer where {
  set_impl = set_impl_integer;
};

newtype Comp_fun_idem b a = Abs_comp_fun_idem (b -> a -> a);

newtype Semilattice_set a = Abs_semilattice_set (a -> a -> a);

is_UNIV ::
  forall a.
    (Cardinality.Card_UNIV a, Collection_Eq.Ceq a,
      Collection_Order.Cproper_interval a) => Set.Set a -> Bool;
is_UNIV (Set.RBT_set rbt) =
  (case (Collection_Order.ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "is_UNIV RBT_set: ccompare = None" (\ _ -> is_UNIV (Set.RBT_set rbt));
    Just _ ->
      Phantom_Type.of_phantom
        (Cardinality.finite_UNIV :: Phantom_Type.Phantom a Bool) &&
        Set_Linorder.exhaustive_fusion Collection_Order.cproper_interval
          RBT_ext.rbt_keys_generator (RBT_Mapping2.init rbt);
  });
is_UNIV a =
  let {
    aa = Phantom_Type.of_phantom
           (Cardinality.card_UNIV :: Phantom_Type.Phantom a Arith.Nat);
    b = Finite_Set.card a;
  } in (if Arith.less_nat Arith.zero_nat aa then Arith.equal_nat aa b
         else (if Arith.less_nat Arith.zero_nat b then False
                else (error :: forall a. String -> (() -> a) -> a)
                       "is_UNIV called on infinite type and set"
                       (\ _ -> is_UNIV a)));

max_sls :: forall a. (Orderings.Linorder a) => Semilattice_set a;
max_sls = Abs_semilattice_set Orderings.max;

set_empty_choose ::
  forall a. (Collection_Eq.Ceq a, Collection_Order.Ccompare a) => Set.Set a;
set_empty_choose =
  (case (Collection_Order.ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing -> (case (Collection_Eq.ceq :: Maybe (a -> a -> Bool)) of {
                 Nothing -> Set.Set_Monad [];
                 Just _ -> Set.DList_set DList_Set.empty;
               });
    Just _ -> Set.RBT_set RBT_Mapping2.empty;
  });

set_empty ::
  forall a.
    (Collection_Eq.Ceq a,
      Collection_Order.Ccompare a) => Set_impla -> Set.Set a;
set_empty Set_Collect = Set.Collect_set (\ _ -> False);
set_empty Set_DList = Set.DList_set DList_Set.empty;
set_empty Set_RBT = Set.RBT_set RBT_Mapping2.empty;
set_empty Set_Monad = Set.Set_Monad [];
set_empty Set_Choose = set_empty_choose;

set_aux ::
  forall a.
    (Collection_Eq.Ceq a,
      Collection_Order.Ccompare a) => Set_impla -> [a] -> Set.Set a;
set_aux Set_Monad = Set.Set_Monad;
set_aux Set_Choose =
  (case (Collection_Order.ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (case (Collection_Eq.ceq :: Maybe (a -> a -> Bool)) of {
        Nothing -> Set.Set_Monad;
        Just _ ->
          List.foldl (\ s x -> Set.insert x s) (Set.DList_set DList_Set.empty);
      });
    Just _ ->
      List.foldl (\ s x -> Set.insert x s) (Set.RBT_set RBT_Mapping2.empty);
  });
set_aux impl = List.foldl (\ s x -> Set.insert x s) (set_empty impl);

sup_cfi :: forall a. (Lattices.Lattice a) => Comp_fun_idem a a;
sup_cfi = Abs_comp_fun_idem Lattices.sup;

semilattice_set_apply :: forall a. Semilattice_set a -> a -> a -> a;
semilattice_set_apply (Abs_semilattice_set x) = x;

set_fold1 ::
  forall a.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a,
      Lattices.Lattice a) => Semilattice_set a -> Set.Set a -> a;
set_fold1 f (Set.RBT_set rbt) =
  (case (Collection_Order.ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "set_fold1 RBT_set: ccompare = None"
        (\ _ -> set_fold1 f (Set.RBT_set rbt));
    Just _ ->
      (if RBT_Mapping2.is_empty rbt
        then (error :: forall a. String -> (() -> a) -> a)
               "set_fold1 RBT_set: empty set"
               (\ _ -> set_fold1 f (Set.RBT_set rbt))
        else RBT_Set2.fold1 (semilattice_set_apply f) rbt);
  });
set_fold1 f (Set.DList_set dxs) =
  (case (Collection_Eq.ceq :: Maybe (a -> a -> Bool)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "set_fold1 DList_set: ceq = None"
        (\ _ -> set_fold1 f (Set.DList_set dxs));
    Just _ ->
      (if DList_Set.nulla dxs
        then (error :: forall a. String -> (() -> a) -> a)
               "set_fold1 DList_set: empty set"
               (\ _ -> set_fold1 f (Set.DList_set dxs))
        else DList_Set.fold (semilattice_set_apply f) (DList_Set.tl dxs)
               (DList_Set.hd dxs));
  });
set_fold1 f (Set.Set_Monad (x : xs)) = List.fold (semilattice_set_apply f) xs x;
set_fold1 f (Set.Collect_set p) =
  (error :: forall a. String -> (() -> a) -> a) "set_fold1: Collect_set"
    (\ _ -> set_fold1 f (Set.Collect_set p));
set_fold1 f (Set.Complement a) =
  (error :: forall a. String -> (() -> a) -> a) "set_fold1: Complement"
    (\ _ -> set_fold1 f (Set.Complement a));

comp_fun_idem_apply :: forall b a. Comp_fun_idem b a -> b -> a -> a;
comp_fun_idem_apply (Abs_comp_fun_idem x) = x;

set_fold_cfi ::
  forall a b.
    (Collection_Eq.Ceq a,
      Collection_Order.Ccompare a) => Comp_fun_idem a b -> b -> Set.Set a -> b;
set_fold_cfi f b (Set.RBT_set rbt) =
  (case (Collection_Order.ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "set_fold_cfi RBT_set: ccompare = None"
        (\ _ -> set_fold_cfi f b (Set.RBT_set rbt));
    Just _ -> RBT_Set2.fold (comp_fun_idem_apply f) rbt b;
  });
set_fold_cfi f b (Set.DList_set dxs) =
  (case (Collection_Eq.ceq :: Maybe (a -> a -> Bool)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "set_fold_cfi DList_set: ceq = None"
        (\ _ -> set_fold_cfi f b (Set.DList_set dxs));
    Just _ -> DList_Set.fold (comp_fun_idem_apply f) dxs b;
  });
set_fold_cfi f b (Set.Set_Monad xs) = List.fold (comp_fun_idem_apply f) xs b;
set_fold_cfi f b (Set.Collect_set p) =
  (error :: forall a. String -> (() -> a) -> a)
    "set_fold_cfi not supported on Collect_set"
    (\ _ -> set_fold_cfi f b (Set.Collect_set p));
set_fold_cfi f b (Set.Complement a) =
  (error :: forall a. String -> (() -> a) -> a)
    "set_fold_cfi not supported on Complement"
    (\ _ -> set_fold_cfi f b (Set.Complement a));

quicksort_acc :: forall a. (a -> a -> Bool) -> [a] -> [a] -> [a];
quicksort_acc less ac [] = ac;
quicksort_acc less ac [x] = x : ac;
quicksort_acc less ac (x : v : va) = quicksort_part less ac x [] [] [] (v : va);

quicksort_part ::
  forall a. (a -> a -> Bool) -> [a] -> a -> [a] -> [a] -> [a] -> [a] -> [a];
quicksort_part less ac x lts eqs gts [] =
  quicksort_acc less (eqs ++ x : quicksort_acc less ac gts) lts;
quicksort_part less ac x lts eqs gts (z : zs) =
  (if less x z then quicksort_part less ac x lts eqs (z : gts) zs
    else (if less z x then quicksort_part less ac x (z : lts) eqs gts zs
           else quicksort_part less ac x lts (z : eqs) gts zs));

quicksort :: forall a. (a -> a -> Bool) -> [a] -> [a];
quicksort less = quicksort_acc less [];

remdups_sorted :: forall a. (a -> a -> Bool) -> [a] -> [a];
remdups_sorted less [] = [];
remdups_sorted less [x] = [x];
remdups_sorted less (x : y : xs) =
  (if less x y then x : remdups_sorted less (y : xs)
    else remdups_sorted less (y : xs));

csorted_list_of_set ::
  forall a.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a) => Set.Set a -> [a];
csorted_list_of_set (Set.Set_Monad xs) =
  (case Collection_Order.ccompare of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "csorted_list_of_set Set_Monad: ccompare = None"
        (\ _ -> csorted_list_of_set (Set.Set_Monad xs));
    Just c ->
      remdups_sorted (Comparator.lt_of_comp c)
        (quicksort (Comparator.lt_of_comp c) xs);
  });
csorted_list_of_set (Set.DList_set dxs) =
  (case (Collection_Eq.ceq :: Maybe (a -> a -> Bool)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "csorted_list_of_set DList_set: ceq = None"
        (\ _ -> csorted_list_of_set (Set.DList_set dxs));
    Just _ ->
      (case Collection_Order.ccompare of {
        Nothing ->
          (error :: forall a. String -> (() -> a) -> a)
            "csorted_list_of_set DList_set: ccompare = None"
            (\ _ -> csorted_list_of_set (Set.DList_set dxs));
        Just c ->
          quicksort (Comparator.lt_of_comp c) (DList_Set.list_of_dlist dxs);
      });
  });
csorted_list_of_set (Set.RBT_set rbt) =
  (case (Collection_Order.ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "csorted_list_of_set RBT_set: ccompare = None"
        (\ _ -> csorted_list_of_set (Set.RBT_set rbt));
    Just _ -> RBT_Set2.keys rbt;
  });

sorted_list_subset_fusion ::
  forall a b c.
    (a -> a -> Bool) ->
      (a -> a -> Bool) ->
        List_Fusion.Generator a b ->
          List_Fusion.Generator a c -> b -> c -> Bool;
sorted_list_subset_fusion less eq g1 g2 s1 s2 =
  (if List_Fusion.has_next g1 s1
    then (case List_Fusion.next g1 s1 of {
           (x, s1a) ->
             List_Fusion.has_next g2 s2 &&
               (case List_Fusion.next g2 s2 of {
                 (y, s2a) ->
                   (if eq x y
                     then sorted_list_subset_fusion less eq g1 g2 s1a s2a
                     else less y x &&
                            sorted_list_subset_fusion less eq g1 g2 s1 s2a);
               });
         })
    else True);

}
