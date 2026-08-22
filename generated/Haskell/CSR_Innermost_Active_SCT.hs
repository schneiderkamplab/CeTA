{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  CSR_Innermost_Active_SCT(check_innermost_csr_dp_termination_proof_active_sct,
                            check_innermost_csr_termination_proof_active_sct)
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
import qualified Reduction_Pair_Implementations;
import qualified Check_Termination;
import qualified Subterm_Criterion_Impl;
import qualified CSR_Innermost_Switch;
import qualified FOR_Preliminaries;
import qualified Termination_Problem_Spec;
import qualified CSR_Checker_Base;
import qualified Countable;
import qualified Mapping;
import qualified Compare_Order_Instances;
import qualified CSR_Innermost_DP_Checker;
import qualified Context_Sensitive_Impl;
import qualified CSR_Minimal_CSDP_Proofs;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified Dependency_Pair_Problem_Spec;
import qualified Labelings;
import qualified Sum_Type;
import qualified Compare;
import qualified Arith;
import qualified Term_Rewriting;

innermost_csr_sct_target_covered_check ::
  forall a b c.
    (Compare.Compare_order a, Eq a, Term_Rewriting.Showl a, Eq b,
      Eq c) => [((Labelings.Lab a b, Arith.Nat), [Arith.Nat])] ->
                 (Term_Rewriting.Term (Labelings.Lab a b) c,
                   Term_Rewriting.Term (Labelings.Lab a b) c) ->
                   Bool;
innermost_csr_sct_target_covered_check mu
  (u, Term_Rewriting.Fun (Labelings.Sharp g) vs) =
  CSR_Minimal_CSDP_Proofs.csr_sct_sharp_term u &&
    all (\ j ->
          not (Arith.member j
                (Context_Sensitive_Impl.mu_of mu (g, Arith.size_list vs))) ||
            Arith.membera (CSR_Innermost_DP_Checker.csr_dp_root_supt_list mu u)
              (Arith.nth vs j))
      (Arith.upt Arith.zero_nat (Arith.size_list vs));
innermost_csr_sct_target_covered_check mu (v, Term_Rewriting.Var vb) = False;
innermost_csr_sct_target_covered_check mu
  (v, Term_Rewriting.Fun (Labelings.Lab vd ve) vc) = False;
innermost_csr_sct_target_covered_check mu
  (v, Term_Rewriting.Fun (Labelings.FunLab vd ve) vc) = False;
innermost_csr_sct_target_covered_check mu
  (v, Term_Rewriting.Fun (Labelings.UnLab vd) vc) = False;

innermost_csr_sct_active_subterm_proc ::
  forall a b c.
    (Compare.Compare_order b, Eq b, Term_Rewriting.Showl b,
      Compare.Compare_order c, Eq c,
      Term_Rewriting.Showl c) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a
                                   (Labelings.Lab b c) [Arith.Char] () ->
                                   [((Labelings.Lab b c, Arith.Nat),
                                      [Arith.Nat])] ->
                                     [((Term_Rewriting.Term (Labelings.Lab b c)
  [Arith.Char],
 Term_Rewriting.Term (Labelings.Lab b c) [Arith.Char]),
([(Arith.Nat, Arith.Nat)], [(Arith.Nat, Arith.Nat)]))] ->
                                       a -> Sum_Type.Sum (String -> String) ();
innermost_csr_sct_active_subterm_proc j mu gs dpp =
  Error_Monad.bind
    (Term_Rewriting.check_wf_trs (Dependency_Pair_Problem_Spec.rules j dpp))
    (\ _ ->
      Error_Monad.bind
        (CSR_Minimal_CSDP_Proofs.csr_rules_sharp_fresh_check
          (Dependency_Pair_Problem_Spec.rules j dpp))
        (\ _ ->
          Error_Monad.bind
            (Check_Monad.check
              (all (innermost_csr_sct_target_covered_check mu)
                (Dependency_Pair_Problem_Spec.pairs j dpp))
              (Term_Rewriting.showsl_lit
                "innermost CSR SCT target arguments are not source-covered"))
            (\ _ ->
              CSR_Minimal_CSDP_Proofs.csr_sct_active_subterm_proc j mu gs
                dpp)));

check_innermost_csr_dp_termination_proof_active_sct ::
  forall a b c.
    (Compare.Compare_order b, Countable.Countable b, Eq b,
      Term_Rewriting.Showl b) => Termination_Problem_Spec.Tp_ops_ext a
                                   (Labelings.Lab b [Arith.Nat]) [Arith.Char]
                                   () ->
                                   Dependency_Pair_Problem_Spec.Dpp_ops_ext c
                                     (Labelings.Lab b [Arith.Nat]) [Arith.Char]
                                     () ->
                                     [((Labelings.Lab b [Arith.Nat], Arith.Nat),
[Arith.Nat])] ->
                                       (String -> String) ->
 c -> CSR_Checker_Base.Csr_dp_termination_proof b [Arith.Nat] [Arith.Char] ->
        Sum_Type.Sum (String -> String) ();
check_innermost_csr_dp_termination_proof_active_sct ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Dep_Graph_Proc edps) =
  FOR_Preliminaries.debug i "innermost CSR-DP dependency graph"
    (Error_Monad.bind
      (CSR_Innermost_DP_Checker.check_innermost_csr_dep_graph_proc j mu dpp
        edps)
      (\ _ ->
        check_innermost_csr_dp_graph_components_active_sct ia j mu i dpp edps));
check_innermost_csr_dp_termination_proof_active_sct ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Size_Change_Subterm_Proc graphs) =
  (if all (innermost_csr_sct_target_covered_check mu)
        (Dependency_Pair_Problem_Spec.pairs j dpp)
    then FOR_Preliminaries.debug i "innermost CSR active size-change"
           (innermost_csr_sct_active_subterm_proc j mu graphs dpp)
    else CSR_Innermost_DP_Checker.check_innermost_csr_dp_termination_proof ia j
           mu i dpp (CSR_Checker_Base.CSR_DP_Size_Change_Subterm_Proc graphs));
check_innermost_csr_dp_termination_proof_active_sct ia j mu i dpp
  CSR_Checker_Base.CSR_DP_P_is_Empty =
  CSR_Innermost_DP_Checker.check_innermost_csr_dp_termination_proof ia j mu i
    dpp CSR_Checker_Base.CSR_DP_P_is_Empty;
check_innermost_csr_dp_termination_proof_active_sct ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof v) =
  CSR_Innermost_DP_Checker.check_innermost_csr_dp_termination_proof ia j mu i
    dpp (CSR_Checker_Base.CSR_DP_Ordinary_Proof v);
check_innermost_csr_dp_termination_proof_active_sct ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Subterm_Criterion_Proc v va vb vc) =
  CSR_Innermost_DP_Checker.check_innermost_csr_dp_termination_proof ia j mu i
    dpp (CSR_Checker_Base.CSR_DP_Subterm_Criterion_Proc v va vb vc);
check_innermost_csr_dp_termination_proof_active_sct ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Gen_Subterm_Criterion_Proc v va vb) =
  CSR_Innermost_DP_Checker.check_innermost_csr_dp_termination_proof ia j mu i
    dpp (CSR_Checker_Base.CSR_DP_Gen_Subterm_Criterion_Proc v va vb);
check_innermost_csr_dp_termination_proof_active_sct ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Usable_Rules_Proc v va) =
  CSR_Innermost_DP_Checker.check_innermost_csr_dp_termination_proof ia j mu i
    dpp (CSR_Checker_Base.CSR_DP_Usable_Rules_Proc v va);
check_innermost_csr_dp_termination_proof_active_sct ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Instantiation_Proc v va vb) =
  CSR_Innermost_DP_Checker.check_innermost_csr_dp_termination_proof ia j mu i
    dpp (CSR_Checker_Base.CSR_DP_Instantiation_Proc v va vb);
check_innermost_csr_dp_termination_proof_active_sct ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Forward_Instantiation_Proc v va vb) =
  CSR_Innermost_DP_Checker.check_innermost_csr_dp_termination_proof ia j mu i
    dpp (CSR_Checker_Base.CSR_DP_Forward_Instantiation_Proc v va vb);
check_innermost_csr_dp_termination_proof_active_sct ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Redpair_UR_Proc v va vb vc) =
  CSR_Innermost_DP_Checker.check_innermost_csr_dp_termination_proof ia j mu i
    dpp (CSR_Checker_Base.CSR_DP_Redpair_UR_Proc v va vb vc);

check_innermost_csr_dp_graph_components_active_sct ::
  forall a b c.
    (Compare.Compare_order b, Countable.Countable b, Eq b,
      Term_Rewriting.Showl b) => Termination_Problem_Spec.Tp_ops_ext a
                                   (Labelings.Lab b [Arith.Nat]) [Arith.Char]
                                   () ->
                                   Dependency_Pair_Problem_Spec.Dpp_ops_ext c
                                     (Labelings.Lab b [Arith.Nat]) [Arith.Char]
                                     () ->
                                     [((Labelings.Lab b [Arith.Nat], Arith.Nat),
[Arith.Nat])] ->
                                       (String -> String) ->
 c -> [(Maybe (CSR_Checker_Base.Csr_dp_termination_proof b [Arith.Nat]
                [Arith.Char]),
         [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
            Term_Rewriting.Term (Labelings.Lab b [Arith.Nat])
              [Arith.Char])])] ->
        Sum_Type.Sum (String -> String) ();
check_innermost_csr_dp_graph_components_active_sct ia j mu i dpp [] =
  Sum_Type.Inr ();
check_innermost_csr_dp_graph_components_active_sct ia j mu i dpp
  ((Nothing, p) : rest) =
  check_innermost_csr_dp_graph_components_active_sct ia j mu
    (Term_Rewriting.add_index i Arith.one_nat) dpp rest;
check_innermost_csr_dp_graph_components_active_sct ia j mu i dpp
  ((Just prf, p) : rest) =
  Error_Monad.bind
    (check_innermost_csr_dp_termination_proof_active_sct ia j mu
      (Term_Rewriting.add_index i Arith.one_nat)
      (Dependency_Pair_Problem_Spec.intersect_pairs j dpp p) prf)
    (\ _ ->
      check_innermost_csr_dp_graph_components_active_sct ia j mu
        (Term_Rewriting.add_index i Arith.one_nat) dpp rest);

check_innermost_csr_termination_proof_active_sct ::
  forall a b c.
    (Compare.Compare_order b, Countable.Countable b, Eq b,
      Term_Rewriting.Showl b) => Termination_Problem_Spec.Tp_ops_ext a
                                   (Labelings.Lab b [Arith.Nat]) [Arith.Char]
                                   () ->
                                   Dependency_Pair_Problem_Spec.Dpp_ops_ext c
                                     (Labelings.Lab b [Arith.Nat]) [Arith.Char]
                                     () ->
                                     (String -> String) ->
                                       [((Labelings.Lab b [Arith.Nat],
   Arith.Nat),
  [Arith.Nat])] ->
 [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
    Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
   [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
      Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
     CSR_Checker_Base.Csr_dp_termination_proof b [Arith.Nat] [Arith.Char] ->
       Sum_Type.Sum (String -> String) ();
check_innermost_csr_termination_proof_active_sct ia j i mu r p prf =
  FOR_Preliminaries.debug i "innermost CSR dependency pairs"
    (Error_Monad.bind (CSR_Innermost_Switch.check_csr_orthogonal r)
      (\ _ ->
        Error_Monad.bind (CSR_Checker_Base.csr_sharp_mu_check mu)
          (\ _ ->
            Error_Monad.bind
              (CSR_Checker_Base.mu_csr_dependency_pairs_tt Labelings.Sharp j mu
                r p)
              (\ dpp ->
                check_innermost_csr_dp_termination_proof_active_sct ia j mu
                  (Term_Rewriting.add_index i Arith.one_nat) dpp prf))));

}
