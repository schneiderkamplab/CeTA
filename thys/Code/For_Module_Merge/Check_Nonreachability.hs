{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Check_Nonreachability(Nonreachability_proof(..), Nonjoinability_proof(..),
                         check_nonreachable, check_nonjoinable)
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
import qualified Exact_Tree_Automata_Completion_Impl;
import qualified Term_More;
import qualified Product_Type;
import qualified Gtcap_Impl;
import qualified Trs;
import qualified Error_Monad;
import qualified Container_Setup;
import qualified Check_Termination_Common;
import qualified Set_Impl;
import qualified Collection_Eq;
import qualified Trs_Impl;
import qualified Check_Monad;
import qualified Tcap_Impl;
import qualified Dependency_Pair_Problem_Spec;
import qualified Termination_Problem_Spec;
import qualified Ground_Context;
import qualified Sum_Type;
import qualified Shows_Literal;
import qualified Countable;
import qualified HOL;
import qualified Labelings_Impl;
import qualified Str;
import qualified Matching;
import qualified Mapping_Impl;
import qualified Collection_Order;
import qualified Option;
import qualified Rule_Map;
import qualified RBT;
import qualified Compare;
import qualified Compare_Order_Instances;
import qualified Product_Lexorder;
import qualified Compare_Instances;
import qualified Ordered_Completion_Impl;
import qualified Check_Equational_Proof;
import qualified Tree_Automata_Impl;
import qualified Term_Order_Impl;
import qualified Labelings;
import qualified Term;
import qualified Arith;

data Nonreachability_proof a b c d = Nonreachable_Tcap | Nonreachable_Gtcap
  | Nonreachable_ETAC [(Labelings.Lab a d, Arith.Nat)] (Labelings.Lab a d)
      (Labelings.Lab a d)
      (Tree_Automata_Impl.Tree_automaton (Term.Term (Labelings.Lab a d) b)
        (Labelings.Lab a d))
  | Nonreachable_Subst_Approx
      [(Term.Term (Labelings.Lab a d) b, Term.Term (Labelings.Lab a d) b)]
      (Nonreachability_proof a b c d)
  | Nonreachable_Reverse (Nonreachability_proof a b c d)
  | Nonreachable_FGCR (Labelings.Lab a d) (Labelings.Lab a d)
      (Labelings.Lab a d)
      [(Term.Term (Labelings.Lab a d) b, Term.Term (Labelings.Lab a d) b)]
      [(Term.Term (Labelings.Lab a d) b, Term.Term (Labelings.Lab a d) b)]
      (Ordered_Completion_Impl.Reduction_order_input (Labelings.Lab a d))
      (Ordered_Completion_Impl.Ordered_completion_proof (Labelings.Lab a d) b)
  | Nonreachable_Co_Rewrite_Pair
      (Term_Order_Impl.Rel_impl_type (Labelings.Lab a d) b c) c
  | Nonreachable_Equational_Disproof
      (Check_Equational_Proof.Equational_disproof a d b);

data Nonjoinability_proof a b c d = Nonjoinable_Tcap
  | Nonjoinable_Ground_NF (Nonreachability_proof a b c d);

req_list ::
  forall a b.
    a -> [(Term.Term b a, Term.Term b a)] ->
           b -> b -> b -> Term.Term b a ->
                            Term.Term b a -> [(Term.Term b a, Term.Term b a)];
req_list x r eq true false s t =
  (Term.Fun eq [Term.Var x, Term.Var x], Term.Fun true []) :
    (Term.Fun eq [s, t], Term.Fun false []) : r;

rule_map ::
  forall a b.
    (Compare.Compare_order a, Eq a,
      Eq b) => [(Term.Term a b, Term.Term a b)] ->
                 (a, Arith.Nat) -> [(Term.Term a b, Term.Term a b)];
rule_map r fn = (case RBT.lookup (Rule_Map.insert_rules () r RBT.empty) fn of {
                  Nothing -> [];
                  Just a -> map snd a;
                });

is_instance_rule ::
  forall a b.
    (Eq a, Collection_Order.Ccompare b, Eq b,
      Mapping_Impl.Mapping_impl b) => (Term.Term a b, Term.Term a b) ->
(Term.Term a b, Term.Term a b) -> Bool;
is_instance_rule ra r =
  (case Matching.match_list Term.Var [(fst r, fst ra), (snd r, snd ra)] of {
    Nothing -> False;
    Just _ -> True;
  });

check_non_reach_co_rewrite_pair ::
  forall a b.
    (Compare.Compare_order a, Shows_Literal.Showl a,
      Shows_Literal.Showl b) => Term_Order_Impl.Rel_impl_ext a b () ->
                                  [(Term.Term a b, Term.Term a b)] ->
                                    Term.Term a b ->
                                      Term.Term a b ->
Sum_Type.Sum (String -> String) ();
check_non_reach_co_rewrite_pair rp r s t =
  Error_Monad.catch_error
    (Error_Monad.bind (Term_Order_Impl.rel_impl_co_rewrite_pair rp)
      (\ _ ->
        Error_Monad.bind (Term_Order_Impl.rel_impl_ns rp r)
          (\ _ -> Term_Order_Impl.s rp (t, s))))
    (\ x ->
      Sum_Type.Inl
        ((Shows_Literal.showsl_lit
            "problem in disproving non-reachability via co-rewrite pairs" .
           Shows_Literal.showsl_literal "\n") .
          x));

check_subst_overapproximation ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Collection_Order.Ccompare b, Eq b,
      Mapping_Impl.Mapping_impl b,
      Shows_Literal.Showl b) => [(Term.Term a b, Term.Term a b)] ->
                                  [(Term.Term a b, Term.Term a b)] ->
                                    Sum_Type.Sum (String -> String) ();
check_subst_overapproximation ra r =
  Error_Monad.catch_error
    (Error_Monad.catch_error
      (Error_Monad.forallM
        (\ raa ->
          Error_Monad.catch_error
            (Error_Monad.existsM
              (\ rb -> Check_Monad.check (is_instance_rule raa rb) id) r)
            (\ _ ->
              Sum_Type.Inl
                ((Shows_Literal.showsl_lit "growing rule for " .
                   Trs_Impl.showsl_rule raa) .
                  Shows_Literal.showsl_lit " is missing\n")))
        ra)
      (\ x -> Sum_Type.Inl (snd x)))
    (\ x ->
      Sum_Type.Inl
        ((((Trs_Impl.showsl_trs r .
             Shows_Literal.showsl_lit "\nis not an overapproximation of\n") .
            Trs_Impl.showsl_trs ra) .
           Shows_Literal.showsl_literal "\n") .
          x));

check_nonreachable ::
  forall a b c d e.
    (Compare.Compare_order c, Countable.Countable c, HOL.Default c, Eq c,
      Shows_Literal.Showl c) => a -> (String -> String) ->
                                       Termination_Problem_Spec.Tp_ops_ext b
 (Labelings.Lab c [Arith.Nat]) [Str.Char] () ->
 Dependency_Pair_Problem_Spec.Dpp_ops_ext d (Labelings.Lab c [Arith.Nat])
   [Str.Char] () ->
   [(Term.Term (Labelings.Lab c [Arith.Nat]) [Str.Char],
      Term.Term (Labelings.Lab c [Arith.Nat]) [Str.Char])] ->
     Term.Term (Labelings.Lab c [Arith.Nat]) [Str.Char] ->
       Term.Term (Labelings.Lab c [Arith.Nat]) [Str.Char] ->
         Nonreachability_proof c [Str.Char] e [Arith.Nat] ->
           Sum_Type.Sum (String -> String) ();
check_nonreachable a ia i j r s t Nonreachable_Tcap =
  Check_Monad.check (not (Ground_Context.match (Tcap_Impl.tcapI r s) t))
    (Shows_Literal.showsl_lit "could not show nonreachability via tcap");
check_nonreachable a ia i j r s t Nonreachable_Gtcap =
  let {
    nlv = all (\ lr -> not (Term.is_Var (fst lr))) r;
    fs = Trs.funas_trs_list r;
  } in Check_Monad.check
         (not (Ground_Context.match (Tcap_Impl.tcapI r s) t) ||
           Gtcap_Impl.nonreachable_gtcapRM fs nlv (not (null r))
             (Gtcap_Impl.mk_gt_fun r) (rule_map r) s t)
         (Shows_Literal.showsl_lit
           "could not show nonreachability via generalized tcap");
check_nonreachable uu uv uw ux r s t (Nonreachable_ETAC f aa c a) =
  Exact_Tree_Automata_Completion_Impl.check_etac_nonreachable f aa c a r s t;
check_nonreachable a ia i j ra s t (Nonreachable_Subst_Approx r p) =
  Error_Monad.bind (check_subst_overapproximation ra r)
    (\ _ -> check_nonreachable a ia i j r s t p);
check_nonreachable a ia i j r s t (Nonreachable_Reverse p) =
  check_nonreachable a ia i j (map (\ (x, y) -> (y, x)) r) t s p;
check_nonreachable a ia i j ra s t (Nonreachable_FGCR eq tr fa e r ro ocp) =
  let {
    r_eq = req_list [Str.char_0x78] ra eq tr fa s t;
  } in Ordered_Completion_Impl.check_equational_disproof_oc (\ aa -> "" ++ aa)
         (Term.Fun tr [], Term.Fun fa []) r_eq e r ro ocp;
check_nonreachable a ia i j r s t (Nonreachable_Co_Rewrite_Pair grt rp) =
  Error_Monad.catch_error
    (check_non_reach_co_rewrite_pair (Term_Order_Impl.rel_impl_of grt rp) r s t)
    (\ x ->
      Sum_Type.Inl
        (((((Shows_Literal.showsl_lit "could not infer that " .
              Term_More.showsl_terma s) .
             Shows_Literal.showsl_lit " cannot reach ") .
            Term_More.showsl_terma t) .
           Shows_Literal.showsl_literal "\n") .
          x));
check_nonreachable a ia i j r s t (Nonreachable_Equational_Disproof v) =
  (if Term.ground s && Term.ground t
    then Check_Equational_Proof.check_equational_disproof False ia i j r (s, t)
           v
    else Sum_Type.Inl
           (((Term_More.showsl_terma s . Shows_Literal.showsl_lit " and ") .
              Term_More.showsl_terma t) .
             Shows_Literal.showsl_lit " must be both ground"));

check_nonjoinable ::
  forall a b c d e.
    (Compare.Compare_order c, Countable.Countable c, HOL.Default c, Eq c,
      Shows_Literal.Showl c) => a -> (String -> String) ->
                                       Termination_Problem_Spec.Tp_ops_ext b
 (Labelings.Lab c [Arith.Nat]) [Str.Char] () ->
 Dependency_Pair_Problem_Spec.Dpp_ops_ext d (Labelings.Lab c [Arith.Nat])
   [Str.Char] () ->
   [(Term.Term (Labelings.Lab c [Arith.Nat]) [Str.Char],
      Term.Term (Labelings.Lab c [Arith.Nat]) [Str.Char])] ->
     Term.Term (Labelings.Lab c [Arith.Nat]) [Str.Char] ->
       Term.Term (Labelings.Lab c [Arith.Nat]) [Str.Char] ->
         Nonjoinability_proof c [Str.Char] e [Arith.Nat] ->
           Sum_Type.Sum (String -> String) ();
check_nonjoinable a ia i j r s t Nonjoinable_Tcap =
  Check_Monad.check
    (not (Ground_Context.unifiable (Tcap_Impl.tcapI r s) (Tcap_Impl.tcapI r t)))
    (Shows_Literal.showsl_lit "could not show nonjoinability via tcap");
check_nonjoinable a ia i j r s t (Nonjoinable_Ground_NF p) =
  (if Trs_Impl.is_NF_trs r s && Term.ground s
    then check_nonreachable a ia i j r t s p
    else (if Trs_Impl.is_NF_trs r t && Term.ground t
           then check_nonreachable a ia i j r s t p
           else Sum_Type.Inl (Shows_Literal.showsl_lit "non NF")));

}
