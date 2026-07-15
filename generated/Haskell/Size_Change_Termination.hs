{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Size_Change_Termination(Scg(..), check_SCT) where {

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
import qualified RBTSetImpl;
import qualified RTrancl2;
import qualified RBT;
import qualified HOL;
import qualified Arith;
import qualified Missing_List;
import qualified Product_Lexorder;
import qualified Comparator;
import qualified Compare;
import qualified Quasi_Order;

data Scg a b = Null | Scg a a [(b, b)] [(b, b)];

equal_scg :: forall a b. (Eq a, Eq b) => Scg a b -> Scg a b -> Bool;
equal_scg Null (Scg x21 x22 x23 x24) = False;
equal_scg (Scg x21 x22 x23 x24) Null = False;
equal_scg (Scg x21 x22 x23 x24) (Scg y21 y22 y23 y24) =
  x21 == y21 && x22 == y22 && x23 == y23 && x24 == y24;
equal_scg Null Null = True;

instance (Eq a, Eq b) => Eq (Scg a b) where {
  a == b = equal_scg a b;
};

comparator_scg ::
  forall a b.
    (a -> a -> Comparator.Order) ->
      (b -> b -> Comparator.Order) -> Scg a b -> Scg a b -> Comparator.Order;
comparator_scg comp_p_p comp_a_p Null Null = Comparator.Eqa;
comparator_scg comp_p_p comp_a_p Null (Scg y ya yb yc) = Comparator.Lt;
comparator_scg comp_p_p comp_a_p (Scg x xa xb xc) Null = Comparator.Gt;
comparator_scg comp_p_p comp_a_p (Scg x xa xb xc) (Scg y ya yb yc) =
  (case comp_p_p x y of {
    Comparator.Eqa ->
      (case comp_p_p xa ya of {
        Comparator.Eqa ->
          (case Arith.comparator_list (Arith.comparator_prod comp_a_p comp_a_p)
                  xb yb
            of {
            Comparator.Eqa ->
              Arith.comparator_list (Arith.comparator_prod comp_a_p comp_a_p) xc
                yc;
            Comparator.Lt -> Comparator.Lt;
            Comparator.Gt -> Comparator.Gt;
          });
        Comparator.Lt -> Comparator.Lt;
        Comparator.Gt -> Comparator.Gt;
      });
    Comparator.Lt -> Comparator.Lt;
    Comparator.Gt -> Comparator.Gt;
  });

compare_scg ::
  forall a b.
    (Compare.Compare a,
      Compare.Compare b) => Scg a b -> Scg a b -> Comparator.Order;
compare_scg = comparator_scg Compare.compare Compare.compare;

less_eq_scg ::
  forall a b.
    (Compare.Compare a, Compare.Compare b) => Scg a b -> Scg a b -> Bool;
less_eq_scg = Comparator.le_of_comp compare_scg;

less_scg ::
  forall a b.
    (Compare.Compare a, Compare.Compare b) => Scg a b -> Scg a b -> Bool;
less_scg = Comparator.lt_of_comp compare_scg;

instance (Compare.Compare a,
           Compare.Compare b) => Quasi_Order.Ord (Scg a b) where {
  less_eq = less_eq_scg;
  less = less_scg;
};

instance (Compare.Compare a,
           Compare.Compare b) => Compare.Compare (Scg a b) where {
  compare = compare_scg;
};

instance (Compare.Compare a,
           Compare.Compare b) => Quasi_Order.Quasi_order (Scg a b) where {
};

instance (Compare.Compare a,
           Compare.Compare b) => Quasi_Order.Weak_order (Scg a b) where {
};

instance (Compare.Compare a,
           Compare.Compare b) => Quasi_Order.Preorder (Scg a b) where {
};

instance (Compare.Compare a,
           Compare.Compare b) => Quasi_Order.Order (Scg a b) where {
};

instance (Compare.Compare a,
           Compare.Compare b) => Quasi_Order.Linorder (Scg a b) where {
};

instance (Compare.Compare a,
           Compare.Compare b) => Compare.Compare_order (Scg a b) where {
};

comp ::
  forall a. (Eq a, Quasi_Order.Linorder a) => [(a, a)] -> [(a, a)] -> [(a, a)];
comp esa es =
  Missing_List.remdups_sort
    (concatMap
      (\ (x, y) ->
        concatMap (\ (ya, z) -> (if y == ya then [(x, z)] else [])) es)
      esa);

subsumes :: forall a b. (Eq a, Eq b) => Scg a b -> Scg a b -> Bool;
subsumes (Scg pa qa stra wka) (Scg p q str wk) =
  pa == p &&
    qa == q && Arith.superset str stra && Arith.superset (str ++ wk) wka;
subsumes g Null = True;
subsumes Null (Scg v va vb vc) = False;

scg_comp ::
  forall a b.
    (Eq b,
      Quasi_Order.Linorder b) => (a -> a -> Bool) ->
                                   Scg a b -> Scg a b -> Scg a b;
scg_comp conn (Scg pa qa stra wka) (Scg p q str wk) =
  (if not (conn qa p) then Null
    else let {
           strs =
             Missing_List.remdups_sort
               (comp stra str ++ comp stra wk ++ comp wka str);
           a = Missing_List.subtract_list_sorted
                 (Missing_List.remdups_sort (comp wka wk)) strs;
         } in Scg pa q strs a);
scg_comp conn Null g = Null;
scg_comp conn (Scg v va vb vc) Null = Null;

in_situ :: forall a b. (Eq b) => Scg a b -> Bool;
in_situ Null = True;
in_situ (Scg p q str wk) = any (\ (a, b) -> a == b) str;

combine ::
  forall a b. (Eq b, Quasi_Order.Linorder b) => Scg a b -> Scg a b -> Scg a b;
combine (Scg pa qa stra wka) (Scg p q str wk) =
  Scg pa qa (Missing_List.union_list_sorted stra str)
    (Missing_List.union_list_sorted wka wk);
combine Null s = Null;
combine (Scg v va vb vc) Null = Null;

sagiv ::
  forall a b.
    (Eq a, Eq b, Quasi_Order.Linorder b) => (a -> a -> Bool) -> Scg a b -> Bool;
sagiv conn g =
  (if in_situ g then True
    else let {
           gg = scg_comp conn g g;
         } in (if subsumes gg g then False else sagiv conn (combine g gg)));

generate_scgs ::
  forall a b.
    (Eq a, Eq b,
      Quasi_Order.Linorder b) => (a -> a -> Bool) ->
                                   [Scg a b] -> Scg a b -> [Scg a b];
generate_scgs conn base g =
  filter (\ ga -> not (equal_scg ga Null)) (map (scg_comp conn g) base);

check_SCT ::
  forall a b.
    (Compare.Compare_order a, Eq a, Compare.Compare_order b,
      Eq b) => (a -> a -> Bool) -> [Scg a b] -> Bool;
check_SCT conn gs =
  RBTSetImpl.g_ball_dflt_basic_oops_rm_basic_ops
    (RTrancl2.mk_rtrancl_set (generate_scgs conn gs) gs) (sagiv conn);

}
