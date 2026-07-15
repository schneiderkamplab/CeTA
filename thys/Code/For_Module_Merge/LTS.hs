{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  LTS(Trans_var(..), comparator_trans_var, Transition_rule(..), Lts_impl(..),
       Lts_ext, transitions_impl, initiala, assertion_impl, assertion_of,
       lts_of, source, target, initial, untrans_var, assertion, transition_of,
       nodes_lts_impl, succ_transitions, transition_rule, check_lts_impl,
       del_transitions_impl, refine_transition_formulas, equal_transition_rule)
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
import qualified Comparator;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified Sum_Type;
import qualified Product_Type;
import qualified Map_Of;
import qualified List;
import qualified Mapping_Impl;
import qualified Container_Setup;
import qualified Collection_Order;
import qualified Set_Impl;
import qualified Collection_Eq;
import qualified Set;
import qualified Formula;
import qualified Term;
import qualified Shows_Literal;
import qualified Quasi_Order;
import qualified Compare;
import qualified Orderings;

data Trans_var a = Pre a | Post a | Intermediate a;

equal_trans_var :: forall a. (Eq a) => Trans_var a -> Trans_var a -> Bool;
equal_trans_var (Post x2) (Intermediate x3) = False;
equal_trans_var (Intermediate x3) (Post x2) = False;
equal_trans_var (Pre x1) (Intermediate x3) = False;
equal_trans_var (Intermediate x3) (Pre x1) = False;
equal_trans_var (Pre x1) (Post x2) = False;
equal_trans_var (Post x2) (Pre x1) = False;
equal_trans_var (Intermediate x3) (Intermediate y3) = x3 == y3;
equal_trans_var (Post x2) (Post y2) = x2 == y2;
equal_trans_var (Pre x1) (Pre y1) = x1 == y1;

instance (Eq a) => Eq (Trans_var a) where {
  a == b = equal_trans_var a b;
};

comparator_trans_var ::
  forall a.
    (a -> a -> Comparator.Order) ->
      Trans_var a -> Trans_var a -> Comparator.Order;
comparator_trans_var comp_v (Pre x) (Pre y) = comp_v x y;
comparator_trans_var comp_v (Pre x) (Post ya) = Comparator.Lt;
comparator_trans_var comp_v (Pre x) (Intermediate yb) = Comparator.Lt;
comparator_trans_var comp_v (Post x) (Pre y) = Comparator.Gt;
comparator_trans_var comp_v (Post x) (Post ya) = comp_v x ya;
comparator_trans_var comp_v (Post x) (Intermediate yb) = Comparator.Lt;
comparator_trans_var comp_v (Intermediate x) (Pre y) = Comparator.Gt;
comparator_trans_var comp_v (Intermediate x) (Post ya) = Comparator.Gt;
comparator_trans_var comp_v (Intermediate x) (Intermediate yb) = comp_v x yb;

compare_trans_var ::
  forall a.
    (Compare.Compare a) => Trans_var a -> Trans_var a -> Comparator.Order;
compare_trans_var = comparator_trans_var Compare.compare;

less_eq_trans_var ::
  forall a. (Compare.Compare a) => Trans_var a -> Trans_var a -> Bool;
less_eq_trans_var = Comparator.le_of_comp compare_trans_var;

less_trans_var ::
  forall a. (Compare.Compare a) => Trans_var a -> Trans_var a -> Bool;
less_trans_var = Comparator.lt_of_comp compare_trans_var;

instance (Compare.Compare a) => Orderings.Ord (Trans_var a) where {
  less_eq = less_eq_trans_var;
  less = less_trans_var;
};

instance (Compare.Compare a) => Quasi_Order.Quasi_order (Trans_var a) where {
};

instance (Compare.Compare a) => Quasi_Order.Weak_order (Trans_var a) where {
};

instance (Compare.Compare a) => Orderings.Preorder (Trans_var a) where {
};

instance (Compare.Compare a) => Orderings.Order (Trans_var a) where {
};

instance (Compare.Compare a) => Orderings.Linorder (Trans_var a) where {
};

showsl_trans_var ::
  forall a. (Shows_Literal.Showl a) => Trans_var a -> String -> String;
showsl_trans_var (Pre v) = Shows_Literal.showsl v;
showsl_trans_var (Post v) =
  Shows_Literal.showsl v . Shows_Literal.showsl_lit "\'";
showsl_trans_var (Intermediate v) =
  Shows_Literal.showsl v . Shows_Literal.showsl_lit "#";

showsl_list_trans_var ::
  forall a. (Shows_Literal.Showl a) => [Trans_var a] -> String -> String;
showsl_list_trans_var xs =
  Shows_Literal.default_showsl_list showsl_trans_var xs;

instance (Shows_Literal.Showl a) => Shows_Literal.Showl (Trans_var a) where {
  showsl = showsl_trans_var;
  showsl_list = showsl_list_trans_var;
};

data Transition_rule a b c d =
  Transition d d (Formula.Formula (Term.Term a (Trans_var b, c)));

data Lts_impl a b c d e =
  Lts_Impl [d] [(e, Transition_rule a b c d)]
    [(d, Formula.Formula (Term.Term a (b, c)))];

data Lts_ext a b c d e =
  Lts_ext (Set.Set d) (Set.Set (Transition_rule a b c d))
    (d -> Formula.Formula (Term.Term a (b, c))) e;

transitions_impl ::
  forall a b c d e. Lts_impl a b c d e -> [(e, Transition_rule a b c d)];
transitions_impl (Lts_Impl x1 x2 x3) = x2;

initiala :: forall a b c d e. Lts_impl a b c d e -> [d];
initiala (Lts_Impl x1 x2 x3) = x1;

assertion_impl ::
  forall a b c d e.
    Lts_impl a b c d e -> [(d, Formula.Formula (Term.Term a (b, c)))];
assertion_impl (Lts_Impl x1 x2 x3) = x3;

assertion_of ::
  forall a b c d e.
    (Collection_Order.Ccompare d, Eq d,
      Mapping_Impl.Mapping_impl d) => Lts_impl a b c d e ->
d -> Formula.Formula (Term.Term a (b, c));
assertion_of pi =
  Map_Of.map_of_default (Formula.Conjunction []) (assertion_impl pi);

lts_of ::
  forall a b c d e.
    (Collection_Order.Ccompare a, Eq a, Collection_Order.Ccompare b, Eq b,
      Collection_Order.Ccompare c, Eq c, Collection_Eq.Ceq d,
      Collection_Order.Ccompare d, Eq d, Mapping_Impl.Mapping_impl d,
      Set_Impl.Set_impl d, Collection_Eq.Ceq e, Collection_Order.Ccompare e,
      Set_Impl.Set_impl e) => Lts_impl a b c d e -> Lts_ext a b c d ();
lts_of pi =
  Lts_ext (List.set (initiala pi))
    (Set.image snd (List.set (transitions_impl pi))) (assertion_of pi) ();

source :: forall a b c d. Transition_rule a b c d -> d;
source (Transition l uu uv) = l;

target :: forall a b c d. Transition_rule a b c d -> d;
target (Transition uu r uv) = r;

initial :: forall a b c d e. Lts_ext a b c d e -> Set.Set d;
initial (Lts_ext initial transition_rules assertion more) = initial;

untrans_var :: forall a. Trans_var a -> a;
untrans_var (Pre x) = x;
untrans_var (Post x) = x;
untrans_var (Intermediate x) = x;

assertion ::
  forall a b c d e.
    Lts_ext a b c d e -> d -> Formula.Formula (Term.Term a (b, c));
assertion (Lts_ext initial transition_rules assertion more) = assertion;

transition_of ::
  forall a b c d e.
    (Collection_Order.Ccompare e, Eq e, Mapping_Impl.Mapping_impl e,
      Shows_Literal.Showl e) => Lts_impl a b c d e ->
                                  e -> Transition_rule a b c d;
transition_of pi =
  Map_Of.map_of_total
    (\ a ->
      ((Shows_Literal.showsl_lit "access to non-existing transition " .
         Shows_Literal.showsl a) .
        Shows_Literal.showsl_lit "\navailable transitions:\n") .
        Shows_Literal.showsl_list (map fst (transitions_impl pi)))
    (transitions_impl pi);

nodes_lts_impl :: forall a b c d e. (Eq d) => Lts_impl a b c d e -> [d];
nodes_lts_impl pi =
  List.remdups
    (map (source . snd) (transitions_impl pi) ++
      map (target . snd) (transitions_impl pi));

succ_transitions ::
  forall a b c d e.
    (Eq d) => Lts_impl a b c d e -> d -> [Transition_rule a b c d];
succ_transitions (Lts_Impl i ts lc) l =
  concatMap (\ (_, tau) -> (if source tau == l then [tau] else [])) ts;

diff_by_label ::
  forall a b.
    (Collection_Eq.Ceq a,
      Collection_Order.Ccompare a) => [(a, b)] -> Set.Set a -> [(a, b)];
diff_by_label pairs l = filter (\ v -> not (Set.member (fst v) l)) pairs;

transition_rule ::
  forall a b c d.
    (Collection_Eq.Ceq b, Collection_Order.Ccompare b,
      Eq b) => (a -> ([b], b)) -> Set.Set b -> Transition_rule a c b d -> Bool;
transition_rule type_of_fun bool_types (Transition l r phi) =
  Formula.formula (Formula.is_bool type_of_fun bool_types) phi;

check_lts_impl ::
  forall a b c d e.
    (Collection_Eq.Ceq b, Collection_Order.Ccompare b,
      Eq b) => (a -> ([b], b)) ->
                 Set.Set b ->
                   Lts_impl a c b d e -> Sum_Type.Sum (String -> String) ();
check_lts_impl type_of_fun bool_types pi =
  (case pi of {
    Lts_Impl _ ti lc ->
      Error_Monad.bind
        (Error_Monad.catch_error
          (Error_Monad.forallM
            (\ (_, t) ->
              Check_Monad.check (transition_rule type_of_fun bool_types t)
                (Shows_Literal.showsl_lit "ill-formed transition in LTS"))
            ti)
          (\ x -> Sum_Type.Inl (snd x)))
        (\ _ ->
          Error_Monad.catch_error
            (Error_Monad.forallM
              (\ (_, f) ->
                Check_Monad.check
                  (Formula.formula (Formula.is_bool type_of_fun bool_types) f)
                  (Shows_Literal.showsl_lit
                    "ill-formed location condition in LTS"))
              lc)
            (\ x -> Sum_Type.Inl (snd x)));
  });

update_transitions_impl ::
  forall a b c d e f.
    Lts_impl a b c d e -> [(f, Transition_rule a b c d)] -> Lts_impl a b c d f;
update_transitions_impl (Lts_Impl i tsa lc) ts = Lts_Impl i ts lc;

del_transitions_impl ::
  forall a b c d e.
    (Collection_Eq.Ceq e, Collection_Order.Ccompare e,
      Set_Impl.Set_impl e) => Lts_impl a b c d e -> [e] -> Lts_impl a b c d e;
del_transitions_impl p td =
  update_transitions_impl p (diff_by_label (transitions_impl p) (List.set td));

refine_transition_formula ::
  forall a b c d.
    Transition_rule a b c d ->
      Formula.Formula (Term.Term a (Trans_var b, c)) -> Transition_rule a b c d;
refine_transition_formula (Transition l r phi) psi =
  Transition l r (Formula.form_and phi psi);

refine_transition_formulas ::
  forall a b c d e.
    Lts_impl a b c d e ->
      (e -> Formula.Formula (Term.Term a (Trans_var b, c))) ->
        Lts_impl a b c d e;
refine_transition_formulas p f =
  Lts_Impl (initiala p)
    (map (\ (tr, tau) -> (tr, refine_transition_formula tau (f tr)))
      (transitions_impl p))
    (assertion_impl p);

equal_transition_rule ::
  forall a b c d.
    (Eq a, Eq b, Eq c,
      Eq d) => Transition_rule a b c d -> Transition_rule a b c d -> Bool;
equal_transition_rule (Transition x1 x2 x3) (Transition y1 y2 y3) =
  x1 == y1 && x2 == y2 && Formula.equal_formula x3 y3;

}
