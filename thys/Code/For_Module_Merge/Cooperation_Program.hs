{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Cooperation_Program(Sharp(..), equal_sharp, comparator_sharp, showsl_sharp,
                       showsl_list_sharp, natural, is_sharp, call_graph_impl,
                       flat_transition, sharp_transition, check_skip_transition)
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
import qualified Sorted_Algebra;
import qualified Sum_Type;
import qualified HOL;
import qualified Formula;
import qualified Term;
import qualified List;
import qualified LTS;
import qualified Shows_Literal;
import qualified Quasi_Order;
import qualified Comparator;
import qualified Compare;
import qualified Orderings;

data Sharp a = Flat a | Sharp a;

equal_sharp :: forall a. (Eq a) => Sharp a -> Sharp a -> Bool;
equal_sharp (Flat x1) (Sharp x2) = False;
equal_sharp (Sharp x2) (Flat x1) = False;
equal_sharp (Sharp x2) (Sharp y2) = x2 == y2;
equal_sharp (Flat x1) (Flat y1) = x1 == y1;

instance (Eq a) => Eq (Sharp a) where {
  a == b = equal_sharp a b;
};

comparator_sharp ::
  forall a.
    (a -> a -> Comparator.Order) -> Sharp a -> Sharp a -> Comparator.Order;
comparator_sharp comp_l (Flat x) (Flat y) = comp_l x y;
comparator_sharp comp_l (Flat x) (Sharp ya) = Comparator.Lt;
comparator_sharp comp_l (Sharp x) (Flat y) = Comparator.Gt;
comparator_sharp comp_l (Sharp x) (Sharp ya) = comp_l x ya;

compare_sharp ::
  forall a. (Compare.Compare a) => Sharp a -> Sharp a -> Comparator.Order;
compare_sharp = comparator_sharp Compare.compare;

less_eq_sharp :: forall a. (Compare.Compare a) => Sharp a -> Sharp a -> Bool;
less_eq_sharp = Comparator.le_of_comp compare_sharp;

less_sharp :: forall a. (Compare.Compare a) => Sharp a -> Sharp a -> Bool;
less_sharp = Comparator.lt_of_comp compare_sharp;

instance (Compare.Compare a) => Orderings.Ord (Sharp a) where {
  less_eq = less_eq_sharp;
  less = less_sharp;
};

instance (Compare.Compare a) => Compare.Compare (Sharp a) where {
  compare = compare_sharp;
};

instance (Compare.Compare a) => Quasi_Order.Quasi_order (Sharp a) where {
};

instance (Compare.Compare a) => Quasi_Order.Weak_order (Sharp a) where {
};

instance (Compare.Compare a) => Orderings.Preorder (Sharp a) where {
};

instance (Compare.Compare a) => Orderings.Order (Sharp a) where {
};

instance (Compare.Compare a) => Orderings.Linorder (Sharp a) where {
};

showsl_sharp ::
  forall a. (Shows_Literal.Showl a) => Sharp a -> String -> String;
showsl_sharp (Flat s) = Shows_Literal.showsl s;
showsl_sharp (Sharp s) = Shows_Literal.showsl_lit "#" . Shows_Literal.showsl s;

showsl_list_sharp ::
  forall a. (Shows_Literal.Showl a) => [Sharp a] -> String -> String;
showsl_list_sharp xs = Shows_Literal.default_showsl_list showsl_sharp xs;

instance (Shows_Literal.Showl a) => Shows_Literal.Showl (Sharp a) where {
  showsl = showsl_sharp;
  showsl_list = showsl_list_sharp;
};

instance (Compare.Compare a) => Compare.Compare_order (Sharp a) where {
};

natural :: forall a. Sharp a -> a;
natural (Sharp l) = l;
natural (Flat l) = l;

is_sharp :: forall a. Sharp a -> Bool;
is_sharp (Flat uu) = False;
is_sharp (Sharp uv) = True;

call_graph_impl ::
  forall a b c d e. (Eq d) => LTS.Lts_impl a b c d e -> [(d, d)];
call_graph_impl r =
  List.remdups
    (map (\ tau -> (LTS.source (snd tau), LTS.target (snd tau)))
      (LTS.transitions_impl r));

flat_transition ::
  forall a b c d.
    LTS.Transition_rule a b c d -> LTS.Transition_rule a b c (Sharp d);
flat_transition (LTS.Transition l r phi) = LTS.Transition (Flat l) (Flat r) phi;

sharp_transition ::
  forall a b c d.
    LTS.Transition_rule a b c d -> LTS.Transition_rule a b c (Sharp d);
sharp_transition (LTS.Transition l r phi) =
  LTS.Transition (Sharp l) (Sharp r) phi;

check_skip_transition ::
  forall a b c d e.
    (Eq a, Eq b, Shows_Literal.Showl b, Eq c, HOL.Default d,
      Shows_Literal.Showl d) => (Term.Term a (b, c) -> String -> String) ->
                                  (d -> Formula.Formula (Term.Term a (b, c)) ->
  Sum_Type.Sum (String -> String) ()) ->
                                    (Bool ->
                                      Term.Term a (b, c) ->
Formula.Formula (Term.Term a (b, c))) ->
                                      LTS.Transition_rule a b c e ->
Sum_Type.Sum (String -> String) ();
check_skip_transition showsl_atom logic_checker normalize_lit tau =
  (case tau of {
    LTS.Transition _ _ phi ->
      Formula.check_valid_formula showsl_atom logic_checker normalize_lit
        HOL.defaulta
        (Formula.map_formula (Sorted_Algebra.rename_vars_exp LTS.untrans_var)
          phi);
  });

}
