{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Set(Set(..), collect, member, less_eq_set, uminus_set, inf_set, sup_set, bex,
       ball, bot_set, insert, image, filtera, is_empty, top_set, minus_set)
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
import qualified RBT_ext;
import qualified List_Fusion;
import qualified RBT_Impl;
import qualified List;
import qualified Phantom_Type;
import qualified Cardinality;
import qualified Product_Type;
import qualified Closure_Set;
import qualified RBT_Set2;
import qualified Set_Impl;
import qualified Option;
import qualified Comparator;
import qualified RBT_Mapping2;
import qualified DList_Set;
import qualified Quasi_Order;
import qualified Orderings;
import qualified Lattices;
import qualified Collection_Order;
import qualified Collection_Enum;
import qualified Collection_Eq;

data Set a = Collect_set (a -> Bool) | DList_set (DList_Set.Set_dlist a)
  | RBT_set (RBT_Mapping2.Mapping_rbt a ()) | Set_Monad [a]
  | Complement (Set a);

collect :: forall a. (Collection_Enum.Cenum a) => (a -> Bool) -> Set a;
collect p = (case Collection_Enum.cEnum of {
              Nothing -> Collect_set p;
              Just (enum, _) -> Set_Monad (filter p enum);
            });

member ::
  forall a.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a) => a -> Set a -> Bool;
member x (Set_Monad xs) =
  (case Collection_Eq.ceq of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "member Set_Monad: ceq = None" (\ _ -> member x (Set_Monad xs));
    Just eq -> DList_Set.list_member eq xs x;
  });
member xa (Complement x) = not (member xa x);
member x (RBT_set rbt) = RBT_Set2.member rbt x;
member x (DList_set dxs) = DList_Set.member dxs x;
member x (Collect_set a) = a x;

less_eq_set ::
  forall a.
    (Collection_Enum.Cenum a, Collection_Eq.Ceq a,
      Collection_Order.Ccompare a) => Set a -> Set a -> Bool;
less_eq_set (RBT_set rbt1) (RBT_set rbt2) =
  (case Collection_Order.ccompare of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "subset RBT_set RBT_set: ccompare = None"
        (\ _ -> less_eq_set (RBT_set rbt1) (RBT_set rbt2));
    Just c ->
      (case Collection_Eq.ceq of {
        Nothing ->
          Set_Impl.sorted_list_subset_fusion (Comparator.lt_of_comp c)
            (\ x y -> Comparator.equal_order (c x y) Comparator.Eqa)
            RBT_ext.rbt_keys_generator RBT_ext.rbt_keys_generator
            (RBT_Mapping2.init rbt1) (RBT_Mapping2.init rbt2);
        Just eq ->
          Set_Impl.sorted_list_subset_fusion (Comparator.lt_of_comp c) eq
            RBT_ext.rbt_keys_generator RBT_ext.rbt_keys_generator
            (RBT_Mapping2.init rbt1) (RBT_Mapping2.init rbt2);
      });
  });
less_eq_set (Complement a1) (Complement a2) = less_eq_set a2 a1;
less_eq_set (Collect_set p) (Complement a) =
  less_eq_set a (collect (\ x -> not (p x)));
less_eq_set (RBT_set rbt) b =
  (case (Collection_Order.ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "subset RBT_set1: ccompare = None" (\ _ -> less_eq_set (RBT_set rbt) b);
    Just _ ->
      List_Fusion.list_all_fusion RBT_ext.rbt_keys_generator (\ x -> member x b)
        (RBT_Mapping2.init rbt);
  });
less_eq_set (DList_set dxs) c =
  (case (Collection_Eq.ceq :: Maybe (a -> a -> Bool)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "subset DList_set1: ceq = None" (\ _ -> less_eq_set (DList_set dxs) c);
    Just _ -> DList_Set.dlist_all (\ x -> member x c) dxs;
  });
less_eq_set (Set_Monad xs) c = all (\ x -> member x c) xs;

equal_set ::
  forall a.
    (Collection_Enum.Cenum a, Collection_Eq.Ceq a, Collection_Order.Ccompare a,
      Eq a) => Set a -> Set a -> Bool;
equal_set a b = less_eq_set a b && less_eq_set b a;

instance (Collection_Enum.Cenum a, Collection_Eq.Ceq a,
           Collection_Order.Ccompare a, Eq a) => Eq (Set a) where {
  a == b = equal_set a b;
};

uminus_set :: forall a. Set a -> Set a;
uminus_set (Complement b) = b;
uminus_set (Collect_set p) = Collect_set (\ x -> not (p x));
uminus_set a = Complement a;

inf_set ::
  forall a.
    (Collection_Eq.Ceq a,
      Collection_Order.Ccompare a) => Set a -> Set a -> Set a;
inf_set (RBT_set rbt1) (Set_Monad xs) =
  (case (Collection_Order.ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "inter RBT_set Set_Monad: ccompare = None"
        (\ _ -> inf_set (RBT_set rbt1) (Set_Monad xs));
    Just _ -> RBT_set (RBT_Set2.inter_list rbt1 xs);
  });
inf_set (Set_Monad xs) (RBT_set rbt1) =
  (case (Collection_Order.ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "inter Set_Monad RBT_set: ccompare = None"
        (\ _ -> inf_set (RBT_set rbt1) (Set_Monad xs));
    Just _ -> RBT_set (RBT_Set2.inter_list rbt1 xs);
  });
inf_set (Set_Monad xs) (DList_set dxs2) =
  (case Collection_Eq.ceq of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "inter Set_Monad DList_set: ceq = None"
        (\ _ -> inf_set (Set_Monad xs) (DList_set dxs2));
    Just eq -> DList_set (DList_Set.filtera (DList_Set.list_member eq xs) dxs2);
  });
inf_set (Set_Monad xs1) (Set_Monad xs2) =
  (case Collection_Eq.ceq of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "inter Set_Monad Set_Monad: ceq = None"
        (\ _ -> inf_set (Set_Monad xs1) (Set_Monad xs2));
    Just eq -> Set_Monad (filter (DList_Set.list_member eq xs2) xs1);
  });
inf_set (RBT_set rbt) (DList_set dxs) =
  (case (Collection_Order.ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "inter RBT_set DList_set: ccompare = None"
        (\ _ -> inf_set (RBT_set rbt) (DList_set dxs));
    Just _ ->
      (case (Collection_Eq.ceq :: Maybe (a -> a -> Bool)) of {
        Nothing ->
          (error :: forall a. String -> (() -> a) -> a)
            "inter RBT_set DList_set: ceq = None"
            (\ _ -> inf_set (RBT_set rbt) (DList_set dxs));
        Just _ ->
          RBT_set (RBT_Set2.inter_list rbt (DList_Set.list_of_dlist dxs));
      });
  });
inf_set (RBT_set rbt1) (RBT_set rbt2) =
  (case (Collection_Order.ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "inter RBT_set RBT_set: ccompare = None"
        (\ _ -> inf_set (RBT_set rbt1) (RBT_set rbt2));
    Just _ -> RBT_set (RBT_Mapping2.meet (\ _ _ -> id) rbt1 rbt2);
  });
inf_set (DList_set dxs1) (Set_Monad xs) =
  (case Collection_Eq.ceq of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "inter DList_set Set_Monad: ceq = None"
        (\ _ -> inf_set (DList_set dxs1) (Set_Monad xs));
    Just eq -> DList_set (DList_Set.filtera (DList_Set.list_member eq xs) dxs1);
  });
inf_set (DList_set dxs1) (DList_set dxs2) =
  (case (Collection_Eq.ceq :: Maybe (a -> a -> Bool)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "inter DList_set DList_set: ceq = None"
        (\ _ -> inf_set (DList_set dxs1) (DList_set dxs2));
    Just _ -> DList_set (DList_Set.filtera (DList_Set.member dxs2) dxs1);
  });
inf_set (DList_set dxs) (RBT_set rbt) =
  (case (Collection_Order.ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "inter DList_set RBT_set: ccompare = None"
        (\ _ -> inf_set (DList_set dxs) (RBT_set rbt));
    Just _ ->
      (case (Collection_Eq.ceq :: Maybe (a -> a -> Bool)) of {
        Nothing ->
          (error :: forall a. String -> (() -> a) -> a)
            "inter DList_set RBT_set: ceq = None"
            (\ _ -> inf_set (DList_set dxs) (RBT_set rbt));
        Just _ ->
          RBT_set (RBT_Set2.inter_list rbt (DList_Set.list_of_dlist dxs));
      });
  });
inf_set (Complement ba) (Complement b) = Complement (sup_set ba b);
inf_set g (RBT_set rbt2) =
  (case (Collection_Order.ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "inter RBT_set2: ccompare = None" (\ _ -> inf_set g (RBT_set rbt2));
    Just _ -> RBT_set (RBT_Mapping2.filtera ((\ x -> member x g) . fst) rbt2);
  });
inf_set (RBT_set rbt1) g =
  (case (Collection_Order.ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "inter RBT_set1: ccompare = None" (\ _ -> inf_set (RBT_set rbt1) g);
    Just _ -> RBT_set (RBT_Mapping2.filtera ((\ x -> member x g) . fst) rbt1);
  });
inf_set h (DList_set dxs2) =
  (case (Collection_Eq.ceq :: Maybe (a -> a -> Bool)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "inter DList_set2: ceq = None" (\ _ -> inf_set h (DList_set dxs2));
    Just _ -> DList_set (DList_Set.filtera (\ x -> member x h) dxs2);
  });
inf_set (DList_set dxs1) h =
  (case (Collection_Eq.ceq :: Maybe (a -> a -> Bool)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "inter DList_set1: ceq = None" (\ _ -> inf_set (DList_set dxs1) h);
    Just _ -> DList_set (DList_Set.filtera (\ x -> member x h) dxs1);
  });
inf_set i (Set_Monad xs) = Set_Monad (filter (\ x -> member x i) xs);
inf_set (Set_Monad xs) i = Set_Monad (filter (\ x -> member x i) xs);
inf_set j (Collect_set a) = Collect_set (\ x -> a x && member x j);
inf_set (Collect_set a) j = Collect_set (\ x -> a x && member x j);

sup_set ::
  forall a.
    (Collection_Eq.Ceq a,
      Collection_Order.Ccompare a) => Set a -> Set a -> Set a;
sup_set ba (Complement b) = Complement (inf_set (uminus_set ba) b);
sup_set (Complement ba) b = Complement (inf_set ba (uminus_set b));
sup_set (RBT_set rbt1) (RBT_set rbt2) =
  (case (Collection_Order.ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "union RBT_set RBT_set: ccompare = None"
        (\ _ -> sup_set (RBT_set rbt1) (RBT_set rbt2));
    Just _ -> RBT_set (RBT_Mapping2.join (\ _ _ -> id) rbt1 rbt2);
  });
sup_set (RBT_set rbt) (DList_set dxs) =
  (case (Collection_Order.ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "union RBT_set DList_set: ccompare = None"
        (\ _ -> sup_set (RBT_set rbt) (DList_set dxs));
    Just _ ->
      (case (Collection_Eq.ceq :: Maybe (a -> a -> Bool)) of {
        Nothing ->
          (error :: forall a. String -> (() -> a) -> a)
            "union RBT_set DList_set: ceq = None"
            (\ _ -> sup_set (RBT_set rbt) (DList_set dxs));
        Just _ ->
          RBT_set (DList_Set.fold (\ k -> RBT_Mapping2.insert k ()) dxs rbt);
      });
  });
sup_set (DList_set dxs) (RBT_set rbt) =
  (case (Collection_Order.ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "union DList_set RBT_set: ccompare = None"
        (\ _ -> sup_set (RBT_set rbt) (DList_set dxs));
    Just _ ->
      (case (Collection_Eq.ceq :: Maybe (a -> a -> Bool)) of {
        Nothing ->
          (error :: forall a. String -> (() -> a) -> a)
            "union DList_set RBT_set: ceq = None"
            (\ _ -> sup_set (RBT_set rbt) (DList_set dxs));
        Just _ ->
          RBT_set (DList_Set.fold (\ k -> RBT_Mapping2.insert k ()) dxs rbt);
      });
  });
sup_set (DList_set dxs1) (DList_set dxs2) =
  (case (Collection_Eq.ceq :: Maybe (a -> a -> Bool)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "union DList_set DList_set: ceq = None"
        (\ _ -> sup_set (DList_set dxs1) (DList_set dxs2));
    Just _ -> DList_set (DList_Set.union dxs1 dxs2);
  });
sup_set (Set_Monad zs) (RBT_set rbt2) =
  (case (Collection_Order.ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "union Set_Monad RBT_set: ccompare = None"
        (\ _ -> sup_set (Set_Monad zs) (RBT_set rbt2));
    Just _ -> RBT_set (List.fold (\ k -> RBT_Mapping2.insert k ()) zs rbt2);
  });
sup_set (RBT_set rbt1) (Set_Monad zs) =
  (case (Collection_Order.ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "union RBT_set Set_Monad: ccompare = None"
        (\ _ -> sup_set (RBT_set rbt1) (Set_Monad zs));
    Just _ -> RBT_set (List.fold (\ k -> RBT_Mapping2.insert k ()) zs rbt1);
  });
sup_set (Set_Monad ws) (DList_set dxs2) =
  (case (Collection_Eq.ceq :: Maybe (a -> a -> Bool)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "union Set_Monad DList_set: ceq = None"
        (\ _ -> sup_set (Set_Monad ws) (DList_set dxs2));
    Just _ -> DList_set (List.fold DList_Set.insert ws dxs2);
  });
sup_set (DList_set dxs1) (Set_Monad ws) =
  (case (Collection_Eq.ceq :: Maybe (a -> a -> Bool)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "union DList_set Set_Monad: ceq = None"
        (\ _ -> sup_set (DList_set dxs1) (Set_Monad ws));
    Just _ -> DList_set (List.fold DList_Set.insert ws dxs1);
  });
sup_set (Set_Monad xs) (Set_Monad ys) = Set_Monad (xs ++ ys);
sup_set b (Collect_set a) = Collect_set (\ x -> a x || member x b);
sup_set (Collect_set a) b = Collect_set (\ x -> a x || member x b);

instance (Collection_Eq.Ceq a,
           Collection_Order.Ccompare a) => Lattices.Inf (Set a) where {
  inf = inf_set;
};

instance (Collection_Eq.Ceq a,
           Collection_Order.Ccompare a) => Lattices.Sup (Set a) where {
  sup = sup_set;
};

less_set ::
  forall a.
    (Collection_Enum.Cenum a, Collection_Eq.Ceq a,
      Collection_Order.Ccompare a) => Set a -> Set a -> Bool;
less_set a b = less_eq_set a b && not (less_eq_set b a);

instance (Collection_Enum.Cenum a, Collection_Eq.Ceq a,
           Collection_Order.Ccompare a) => Orderings.Ord (Set a) where {
  less_eq = less_eq_set;
  less = less_set;
};

instance (Collection_Enum.Cenum a, Collection_Eq.Ceq a,
           Collection_Order.Ccompare a) => Quasi_Order.Quasi_order (Set
                             a) where {
};

instance (Collection_Enum.Cenum a, Collection_Eq.Ceq a,
           Collection_Order.Ccompare a) => Quasi_Order.Weak_order (Set
                            a) where {
};

instance (Collection_Enum.Cenum a, Collection_Eq.Ceq a,
           Collection_Order.Ccompare a) => Orderings.Preorder (Set a) where {
};

instance (Collection_Enum.Cenum a, Collection_Eq.Ceq a,
           Collection_Order.Ccompare a) => Orderings.Order (Set a) where {
};

instance (Collection_Enum.Cenum a, Collection_Eq.Ceq a,
           Collection_Order.Ccompare a) => Quasi_Order.Quasi_order_sup (Set
                                 a) where {
};

instance (Collection_Enum.Cenum a, Collection_Eq.Ceq a,
           Collection_Order.Ccompare a) => Quasi_Order.Quasi_semilattice_sup (Set
                                       a) where {
};

instance (Collection_Enum.Cenum a, Collection_Eq.Ceq a,
           Collection_Order.Ccompare a) => Lattices.Semilattice_sup (Set
                              a) where {
};

instance (Collection_Enum.Cenum a, Collection_Eq.Ceq a,
           Collection_Order.Ccompare a) => Lattices.Semilattice_inf (Set
                              a) where {
};

instance (Collection_Enum.Cenum a, Collection_Eq.Ceq a,
           Collection_Order.Ccompare a) => Lattices.Lattice (Set a) where {
};

bex ::
  forall a.
    (Collection_Eq.Ceq a,
      Collection_Order.Ccompare a) => Set a -> (a -> Bool) -> Bool;
bex (RBT_set rbt) p =
  (case (Collection_Order.ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "Bex RBT_set: ccompare = None" (\ _ -> bex (RBT_set rbt) p);
    Just _ -> RBT_Mapping2.ex (\ k _ -> p k) rbt;
  });
bex (DList_set dxs) p =
  (case (Collection_Eq.ceq :: Maybe (a -> a -> Bool)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a) "Bex DList_set: ceq = None"
        (\ _ -> bex (DList_set dxs) p);
    Just _ -> DList_Set.dlist_ex p dxs;
  });
bex (Set_Monad xs) p = any p xs;

ball ::
  forall a.
    (Collection_Eq.Ceq a,
      Collection_Order.Ccompare a) => Set a -> (a -> Bool) -> Bool;
ball (RBT_set rbt) p =
  (case (Collection_Order.ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "Ball RBT_set: ccompare = None" (\ _ -> ball (RBT_set rbt) p);
    Just _ -> RBT_Mapping2.alla (\ k _ -> p k) rbt;
  });
ball (DList_set dxs) p =
  (case (Collection_Eq.ceq :: Maybe (a -> a -> Bool)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a) "Ball DList_set: ceq = None"
        (\ _ -> ball (DList_set dxs) p);
    Just _ -> DList_Set.dlist_all p dxs;
  });
ball (Set_Monad xs) p = all p xs;

bot_set ::
  forall a.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a,
      Set_Impl.Set_impl a) => Set a;
bot_set =
  Set_Impl.set_empty
    (Phantom_Type.of_phantom
      (Set_Impl.set_impl :: Phantom_Type.Phantom a Set_Impl.Set_impla));

insert ::
  forall a.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a) => a -> Set a -> Set a;
insert xa (Complement x) = Complement (remove xa x);
insert x (RBT_set rbt) =
  (case (Collection_Order.ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "insert RBT_set: ccompare = None" (\ _ -> insert x (RBT_set rbt));
    Just _ -> RBT_set (RBT_Mapping2.insert x () rbt);
  });
insert x (DList_set dxs) =
  (case (Collection_Eq.ceq :: Maybe (a -> a -> Bool)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "insert DList_set: ceq = None" (\ _ -> insert x (DList_set dxs));
    Just _ -> DList_set (DList_Set.insert x dxs);
  });
insert x (Set_Monad xs) = Set_Monad (x : xs);
insert x (Collect_set a) =
  (case Collection_Eq.ceq of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "insert Collect_set: ceq = None" (\ _ -> insert x (Collect_set a));
    Just eq -> Collect_set (Closure_Set.fun_upd eq a x True);
  });

remove ::
  forall a.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a) => a -> Set a -> Set a;
remove x (Complement a) = Complement (insert x a);
remove x (RBT_set rbt) =
  (case (Collection_Order.ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "remove RBT_set: ccompare = None" (\ _ -> remove x (RBT_set rbt));
    Just _ -> RBT_set (RBT_Mapping2.delete x rbt);
  });
remove x (DList_set dxs) =
  (case (Collection_Eq.ceq :: Maybe (a -> a -> Bool)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "remove DList_set: ceq = None" (\ _ -> remove x (DList_set dxs));
    Just _ -> DList_set (DList_Set.remove x dxs);
  });
remove x (Collect_set a) =
  (case Collection_Eq.ceq of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a) "remove Collect: ceq = None"
        (\ _ -> remove x (Collect_set a));
    Just eq -> Collect_set (Closure_Set.fun_upd eq a x False);
  });

image ::
  forall a b.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a, Collection_Eq.Ceq b,
      Collection_Order.Ccompare b,
      Set_Impl.Set_impl b) => (a -> b) -> Set a -> Set b;
image h (RBT_set rbt) =
  (case (Collection_Order.ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "image RBT_set: ccompare = None" (\ _ -> image h (RBT_set rbt));
    Just _ -> RBT_Set2.fold (insert . h) rbt bot_set;
  });
image g (DList_set dxs) =
  (case (Collection_Eq.ceq :: Maybe (a -> a -> Bool)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "image DList_set: ceq = None" (\ _ -> image g (DList_set dxs));
    Just _ -> DList_Set.fold (insert . g) dxs bot_set;
  });
image f (Complement (Complement b)) = image f b;
image f (Collect_set a) =
  (error :: forall a. String -> (() -> a) -> a) "image Collect_set"
    (\ _ -> image f (Collect_set a));
image f (Set_Monad xs) = Set_Monad (map f xs);

filtera ::
  forall a.
    (Collection_Eq.Ceq a,
      Collection_Order.Ccompare a) => (a -> Bool) -> Set a -> Set a;
filtera p a = inf_set a (Collect_set p);

is_empty ::
  forall a.
    (Cardinality.Card_UNIV a, Collection_Eq.Ceq a,
      Collection_Order.Cproper_interval a) => Set a -> Bool;
is_empty (Complement a) = Set_Impl.is_UNIV a;
is_empty (RBT_set rbt) =
  (case (Collection_Order.ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "is_empty RBT_set: ccompare = None" (\ _ -> is_empty (RBT_set rbt));
    Just _ -> RBT_Mapping2.is_empty rbt;
  });
is_empty (DList_set dxs) =
  (case (Collection_Eq.ceq :: Maybe (a -> a -> Bool)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "is_empty DList_set: ceq = None" (\ _ -> is_empty (DList_set dxs));
    Just _ -> DList_Set.nulla dxs;
  });
is_empty (Set_Monad xs) = null xs;

top_set ::
  forall a.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a,
      Set_Impl.Set_impl a) => Set a;
top_set = uminus_set bot_set;

minus_set ::
  forall a.
    (Collection_Eq.Ceq a,
      Collection_Order.Ccompare a) => Set a -> Set a -> Set a;
minus_set (RBT_set rbt1) (RBT_set rbt2) =
  (case (Collection_Order.ccompare :: Maybe (a -> a -> Comparator.Order)) of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a)
        "minus RBT_set RBT_set: ccompare = None"
        (\ _ -> minus_set (RBT_set rbt1) (RBT_set rbt2));
    Just _ -> RBT_set (RBT_Set2.minus rbt1 rbt2);
  });
minus_set a b = inf_set a (uminus_set b);

}
