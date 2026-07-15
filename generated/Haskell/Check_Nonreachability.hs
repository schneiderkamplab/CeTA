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
import qualified Gtcap_Impl;
import qualified Error_Monad;
import qualified Check_Termination_Common;
import qualified Check_Monad;
import qualified Tcap_Impl;
import qualified Dependency_Pair_Problem_Spec;
import qualified Termination_Problem_Spec;
import qualified Sum_Type;
import qualified Countable;
import qualified HOL;
import qualified Mapping;
import qualified Rule_Map;
import qualified RBT;
import qualified Compare;
import qualified Compare_Order_Instances;
import qualified Product_Lexorder;
import qualified Ordered_Completion_Impl;
import qualified Check_Equational_Proof;
import qualified Tree_Automata_Impl;
import qualified Labelings;
import qualified Term_Rewriting;
import qualified Arith;

data Nonreachability_proof a b c d = Nonreachable_Tcap | Nonreachable_Gtcap
  | Nonreachable_ETAC [(Labelings.Lab a d, Arith.Nat)] (Labelings.Lab a d)
      (Labelings.Lab a d)
      (Tree_Automata_Impl.Tree_automaton
        (Term_Rewriting.Term (Labelings.Lab a d) b) (Labelings.Lab a d))
  | Nonreachable_Subst_Approx
      [(Term_Rewriting.Term (Labelings.Lab a d) b,
         Term_Rewriting.Term (Labelings.Lab a d) b)]
      (Nonreachability_proof a b c d)
  | Nonreachable_Reverse (Nonreachability_proof a b c d)
  | Nonreachable_FGCR (Labelings.Lab a d) (Labelings.Lab a d)
      (Labelings.Lab a d)
      [(Term_Rewriting.Term (Labelings.Lab a d) b,
         Term_Rewriting.Term (Labelings.Lab a d) b)]
      [(Term_Rewriting.Term (Labelings.Lab a d) b,
         Term_Rewriting.Term (Labelings.Lab a d) b)]
      (Ordered_Completion_Impl.Reduction_order_input (Labelings.Lab a d))
      (Ordered_Completion_Impl.Ordered_completion_proof (Labelings.Lab a d) b)
  | Nonreachable_Co_Rewrite_Pair
      (Term_Rewriting.Rel_impl_type (Labelings.Lab a d) b c) c
  | Nonreachable_Equational_Disproof
      (Check_Equational_Proof.Equational_disproof a d b);

data Nonjoinability_proof a b c d = Nonjoinable_Tcap
  | Nonjoinable_Ground_NF (Nonreachability_proof a b c d);

req_list ::
  forall a b.
    a -> [(Term_Rewriting.Term b a, Term_Rewriting.Term b a)] ->
           b -> b -> b -> Term_Rewriting.Term b a ->
                            Term_Rewriting.Term b a ->
                              [(Term_Rewriting.Term b a,
                                 Term_Rewriting.Term b a)];
req_list x r eq true false s t =
  (Term_Rewriting.Fun eq [Term_Rewriting.Var x, Term_Rewriting.Var x],
    Term_Rewriting.Fun true []) :
    (Term_Rewriting.Fun eq [s, t], Term_Rewriting.Fun false []) : r;

rule_map ::
  forall a b.
    (Compare.Compare_order a, Eq a,
      Eq b) => [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
                 (a, Arith.Nat) ->
                   [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)];
rule_map r fn = (case RBT.lookup (Rule_Map.insert_rules () r RBT.empty) fn of {
                  Nothing -> [];
                  Just a -> map snd a;
                });

is_instance_rule ::
  forall a b.
    (Eq a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b) => (Term_Rewriting.Term a b,
                                   Term_Rewriting.Term a b) ->
                                   (Term_Rewriting.Term a b,
                                     Term_Rewriting.Term a b) ->
                                     Bool;
is_instance_rule ra r =
  (case Term_Rewriting.match_list Term_Rewriting.Var
          [(fst r, fst ra), (snd r, snd ra)]
    of {
    Nothing -> False;
    Just _ -> True;
  });

check_non_reach_co_rewrite_pair ::
  forall a b.
    (Compare.Compare_order a, Term_Rewriting.Showl a,
      Term_Rewriting.Showl b) => Term_Rewriting.Rel_impl_ext a b () ->
                                   [(Term_Rewriting.Term a b,
                                      Term_Rewriting.Term a b)] ->
                                     Term_Rewriting.Term a b ->
                                       Term_Rewriting.Term a b ->
 Sum_Type.Sum (String -> String) ();
check_non_reach_co_rewrite_pair rp r s t =
  Error_Monad.catch_error
    (Error_Monad.bind (Term_Rewriting.rel_impl_co_rewrite_pair rp)
      (\ _ ->
        Error_Monad.bind (Term_Rewriting.rel_impl_ns rp r)
          (\ _ -> Term_Rewriting.s rp (t, s))))
    (\ x ->
      Sum_Type.Inl
        ((Term_Rewriting.showsl_lit
            "problem in disproving non-reachability via co-rewrite pairs" .
           Term_Rewriting.showsl_literal "\n") .
          x));

check_subst_overapproximation ::
  forall a b.
    (Eq a, Term_Rewriting.Showl a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b,
      Term_Rewriting.Showl b) => [(Term_Rewriting.Term a b,
                                    Term_Rewriting.Term a b)] ->
                                   [(Term_Rewriting.Term a b,
                                      Term_Rewriting.Term a b)] ->
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
                ((Term_Rewriting.showsl_lit "growing rule for " .
                   Term_Rewriting.showsl_rule raa) .
                  Term_Rewriting.showsl_lit " is missing\n")))
        ra)
      (\ x -> Sum_Type.Inl (snd x)))
    (\ x ->
      Sum_Type.Inl
        ((((Term_Rewriting.showsl_trs r .
             Term_Rewriting.showsl_lit "\nis not an overapproximation of\n") .
            Term_Rewriting.showsl_trs ra) .
           Term_Rewriting.showsl_literal "\n") .
          x));

check_nonreachable ::
  forall a b c d e.
    (Compare.Compare_order c, Countable.Countable c, HOL.Default c, Eq c,
      Term_Rewriting.Showl c) => a -> (String -> String) ->
Termination_Problem_Spec.Tp_ops_ext b (Labelings.Lab c [Arith.Nat]) [Arith.Char]
  () ->
  Dependency_Pair_Problem_Spec.Dpp_ops_ext d (Labelings.Lab c [Arith.Nat])
    [Arith.Char] () ->
    [(Term_Rewriting.Term (Labelings.Lab c [Arith.Nat]) [Arith.Char],
       Term_Rewriting.Term (Labelings.Lab c [Arith.Nat]) [Arith.Char])] ->
      Term_Rewriting.Term (Labelings.Lab c [Arith.Nat]) [Arith.Char] ->
        Term_Rewriting.Term (Labelings.Lab c [Arith.Nat]) [Arith.Char] ->
          Nonreachability_proof c [Arith.Char] e [Arith.Nat] ->
            Sum_Type.Sum (String -> String) ();
check_nonreachable a ia i j r s t Nonreachable_Tcap =
  Check_Monad.check (not (Term_Rewriting.matcha (Tcap_Impl.tcapI r s) t))
    (Term_Rewriting.showsl_lit "could not show nonreachability via tcap");
check_nonreachable a ia i j r s t Nonreachable_Gtcap =
  let {
    nlv = all (\ lr -> not (Term_Rewriting.is_Var (fst lr))) r;
    fs = Term_Rewriting.funas_trs_list r;
  } in Check_Monad.check
         (not (Term_Rewriting.matcha (Tcap_Impl.tcapI r s) t) ||
           Gtcap_Impl.nonreachable_gtcapRM fs nlv (not (null r))
             (Gtcap_Impl.mk_gt_fun r) (rule_map r) s t)
         (Term_Rewriting.showsl_lit
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
    r_eq = req_list [Arith.char_0x78] ra eq tr fa s t;
  } in Ordered_Completion_Impl.check_equational_disproof_oc (\ aa -> "" ++ aa)
         (Term_Rewriting.Fun tr [], Term_Rewriting.Fun fa []) r_eq e r ro ocp;
check_nonreachable a ia i j r s t (Nonreachable_Co_Rewrite_Pair grt rp) =
  Error_Monad.catch_error
    (check_non_reach_co_rewrite_pair (Term_Rewriting.rel_impl_of grt rp) r s t)
    (\ x ->
      Sum_Type.Inl
        (((((Term_Rewriting.showsl_lit "could not infer that " .
              Term_Rewriting.showsl_terma s) .
             Term_Rewriting.showsl_lit " cannot reach ") .
            Term_Rewriting.showsl_terma t) .
           Term_Rewriting.showsl_literal "\n") .
          x));
check_nonreachable a ia i j r s t (Nonreachable_Equational_Disproof v) =
  (if Term_Rewriting.ground s && Term_Rewriting.ground t
    then Check_Equational_Proof.check_equational_disproof False ia i j r (s, t)
           v
    else Sum_Type.Inl
           (((Term_Rewriting.showsl_terma s .
               Term_Rewriting.showsl_lit " and ") .
              Term_Rewriting.showsl_terma t) .
             Term_Rewriting.showsl_lit " must be both ground"));

check_nonjoinable ::
  forall a b c d e.
    (Compare.Compare_order c, Countable.Countable c, HOL.Default c, Eq c,
      Term_Rewriting.Showl c) => a -> (String -> String) ->
Termination_Problem_Spec.Tp_ops_ext b (Labelings.Lab c [Arith.Nat]) [Arith.Char]
  () ->
  Dependency_Pair_Problem_Spec.Dpp_ops_ext d (Labelings.Lab c [Arith.Nat])
    [Arith.Char] () ->
    [(Term_Rewriting.Term (Labelings.Lab c [Arith.Nat]) [Arith.Char],
       Term_Rewriting.Term (Labelings.Lab c [Arith.Nat]) [Arith.Char])] ->
      Term_Rewriting.Term (Labelings.Lab c [Arith.Nat]) [Arith.Char] ->
        Term_Rewriting.Term (Labelings.Lab c [Arith.Nat]) [Arith.Char] ->
          Nonjoinability_proof c [Arith.Char] e [Arith.Nat] ->
            Sum_Type.Sum (String -> String) ();
check_nonjoinable a ia i j r s t Nonjoinable_Tcap =
  Check_Monad.check
    (not (Term_Rewriting.unifiable (Tcap_Impl.tcapI r s) (Tcap_Impl.tcapI r t)))
    (Term_Rewriting.showsl_lit "could not show nonjoinability via tcap");
check_nonjoinable a ia i j r s t (Nonjoinable_Ground_NF p) =
  (if Term_Rewriting.is_NF_trs r s && Term_Rewriting.ground s
    then check_nonreachable a ia i j r t s p
    else (if Term_Rewriting.is_NF_trs r t && Term_Rewriting.ground t
           then check_nonreachable a ia i j r s t p
           else Sum_Type.Inl (Term_Rewriting.showsl_lit "non NF")));

}
