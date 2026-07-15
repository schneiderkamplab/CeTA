{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Labelings_Impl(compare_lab, showsl_lab) where {

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
import qualified Shows_Literal;
import qualified Quasi_Order;
import qualified Comparator;
import qualified Labelings;
import qualified Compare;
import qualified Orderings;

comparator_lab ::
  forall a b.
    (a -> a -> Comparator.Order) ->
      (b -> b -> Comparator.Order) ->
        Labelings.Lab a b -> Labelings.Lab a b -> Comparator.Order;
comparator_lab comp_f comp_l (Labelings.Lab x xa) (Labelings.Lab y ya) =
  (case comparator_lab comp_f comp_l x y of {
    Comparator.Eqa -> comp_l xa ya;
    Comparator.Lt -> Comparator.Lt;
    Comparator.Gt -> Comparator.Gt;
  });
comparator_lab comp_f comp_l (Labelings.Lab x xa) (Labelings.FunLab yb yc) =
  Comparator.Lt;
comparator_lab comp_f comp_l (Labelings.Lab x xa) (Labelings.UnLab yd) =
  Comparator.Lt;
comparator_lab comp_f comp_l (Labelings.Lab x xa) (Labelings.Sharp ye) =
  Comparator.Lt;
comparator_lab comp_f comp_l (Labelings.FunLab x xa) (Labelings.Lab y ya) =
  Comparator.Gt;
comparator_lab comp_f comp_l (Labelings.FunLab x xa) (Labelings.FunLab yb yc) =
  (case comparator_lab comp_f comp_l x yb of {
    Comparator.Eqa ->
      Compare_Instances.comparator_list (comparator_lab comp_f comp_l) xa yc;
    Comparator.Lt -> Comparator.Lt;
    Comparator.Gt -> Comparator.Gt;
  });
comparator_lab comp_f comp_l (Labelings.FunLab x xa) (Labelings.UnLab yd) =
  Comparator.Lt;
comparator_lab comp_f comp_l (Labelings.FunLab x xa) (Labelings.Sharp ye) =
  Comparator.Lt;
comparator_lab comp_f comp_l (Labelings.UnLab x) (Labelings.Lab y ya) =
  Comparator.Gt;
comparator_lab comp_f comp_l (Labelings.UnLab x) (Labelings.FunLab yb yc) =
  Comparator.Gt;
comparator_lab comp_f comp_l (Labelings.UnLab x) (Labelings.UnLab yd) =
  comp_f x yd;
comparator_lab comp_f comp_l (Labelings.UnLab x) (Labelings.Sharp ye) =
  Comparator.Lt;
comparator_lab comp_f comp_l (Labelings.Sharp x) (Labelings.Lab y ya) =
  Comparator.Gt;
comparator_lab comp_f comp_l (Labelings.Sharp x) (Labelings.FunLab yb yc) =
  Comparator.Gt;
comparator_lab comp_f comp_l (Labelings.Sharp x) (Labelings.UnLab yd) =
  Comparator.Gt;
comparator_lab comp_f comp_l (Labelings.Sharp x) (Labelings.Sharp ye) =
  comparator_lab comp_f comp_l x ye;

compare_lab ::
  forall a b.
    (Compare.Compare a,
      Compare.Compare b) => Labelings.Lab a b ->
                              Labelings.Lab a b -> Comparator.Order;
compare_lab = comparator_lab Compare.compare Compare.compare;

less_eq_lab ::
  forall a b.
    (Compare.Compare a,
      Compare.Compare b) => Labelings.Lab a b -> Labelings.Lab a b -> Bool;
less_eq_lab = Comparator.le_of_comp compare_lab;

less_lab ::
  forall a b.
    (Compare.Compare a,
      Compare.Compare b) => Labelings.Lab a b -> Labelings.Lab a b -> Bool;
less_lab = Comparator.lt_of_comp compare_lab;

instance (Compare.Compare a,
           Compare.Compare b) => Orderings.Ord (Labelings.Lab a b) where {
  less_eq = less_eq_lab;
  less = less_lab;
};

instance (Compare.Compare a,
           Compare.Compare b) => Compare.Compare (Labelings.Lab a b) where {
  compare = compare_lab;
};

instance (Compare.Compare a,
           Compare.Compare b) => Quasi_Order.Quasi_order (Labelings.Lab a
                   b) where {
};

instance (Compare.Compare a,
           Compare.Compare b) => Quasi_Order.Weak_order (Labelings.Lab a
                  b) where {
};

instance (Compare.Compare a,
           Compare.Compare b) => Orderings.Preorder (Labelings.Lab a b) where {
};

instance (Compare.Compare a,
           Compare.Compare b) => Orderings.Order (Labelings.Lab a b) where {
};

instance (Compare.Compare a,
           Compare.Compare b) => Orderings.Linorder (Labelings.Lab a b) where {
};

showsl_lab ::
  forall a b.
    (Shows_Literal.Showl a,
      Shows_Literal.Showl b) => Labelings.Lab a b -> String -> String;
showsl_lab (Labelings.UnLab f) = Shows_Literal.showsl f;
showsl_lab (Labelings.Lab f l) =
  ((showsl_lab f . Shows_Literal.showsl_lit "[") . Shows_Literal.showsl l) .
    Shows_Literal.showsl_lit "]";
showsl_lab (Labelings.Sharp f) = showsl_lab f . Shows_Literal.showsl_lit "#";
showsl_lab (Labelings.FunLab f l) =
  showsl_lab f . Shows_Literal.default_showsl_list id (map showsl_lab l);

showsl_list_lab ::
  forall a b.
    (Shows_Literal.Showl a,
      Shows_Literal.Showl b) => [Labelings.Lab a b] -> String -> String;
showsl_list_lab xs = Shows_Literal.default_showsl_list showsl_lab xs;

instance (Shows_Literal.Showl a,
           Shows_Literal.Showl b) => Shows_Literal.Showl (Labelings.Lab a
                   b) where {
  showsl = showsl_lab;
  showsl_list = showsl_list_lab;
};

instance (Compare.Compare a,
           Compare.Compare b) => Compare.Compare_order (Labelings.Lab a
                 b) where {
};

}
