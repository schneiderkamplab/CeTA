{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module CSR_Muterm_Innermost_Usable(check_muterm_expanded_innermost_proof)
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
import qualified CSR_Innermost_Active_SCT;
import qualified CSR_Innermost_DP_Checker;
import qualified CSR_Minimal_CSDP_Proofs;
import qualified FOR_Preliminaries;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified HOL;
import qualified Complex_Constant_Removal_Impl;
import qualified Dependency_Pair_Problem_Spec;
import qualified Reduction_Pair_Implementations;
import qualified Check_Termination_Common;
import qualified Termination_Problem_Spec;
import qualified CSR_Checker_Base;
import qualified Bounded_Increase_Impl;
import qualified Semantic_Labeling_Carrier;
import qualified Check_Termination;
import qualified Critical_Pairs_Impl;
import qualified Subterm_Criterion_Impl;
import qualified Sum_Type;
import qualified Compare;
import qualified Countable;
import qualified Labelings;
import qualified Compare_Order_Instances;
import qualified Term_Rewriting;
import qualified Arith;

check_muterm_expanded_innermost_proof ::
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
check_muterm_expanded_innermost_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Dep_Graph_Proc edps) =
  FOR_Preliminaries.debug i "expanded innermost MU-TERM dependency graph"
    (Error_Monad.bind
      (CSR_Innermost_DP_Checker.check_innermost_csr_dep_graph_proc j mu dpp
        edps)
      (\ _ -> check_muterm_expanded_innermost_components ia j mu i dpp edps));
check_muterm_expanded_innermost_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Instantiation_Proc st sts prf) =
  FOR_Preliminaries.debug i "expanded innermost MU-TERM instantiation"
    (Error_Monad.bind
      (CSR_Minimal_CSDP_Proofs.csr_instantiation_proc j mu st sts dpp)
      (\ dppa ->
        check_muterm_expanded_innermost_proof ia j mu
          (Term_Rewriting.add_index i Arith.one_nat) dppa prf));
check_muterm_expanded_innermost_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Redpair_UR_Proc redp pr u subprf))
  = FOR_Preliminaries.debug i
      "expanded innermost MU-TERM QCS usable-rule reduction pair"
      (Error_Monad.bind
        (Check_Monad.check
          (all (Arith.membera (Dependency_Pair_Problem_Spec.rules j dpp)) u)
          (Term_Rewriting.showsl_lit
            "expanded MU-TERM usable rules are not a subset of the active rules"))
        (\ _ ->
          Error_Monad.bind
            (Check_Monad.check
              (all (\ lr ->
                     CSR_Minimal_CSDP_Proofs.qcs_ur_closed_term_check
                       (Dependency_Pair_Problem_Spec.rules j dpp) u mu (snd lr))
                u)
              (Term_Rewriting.showsl_lit
                "expanded MU-TERM usable-rule RHS closure failed"))
            (\ _ ->
              Error_Monad.bind
                (Check_Monad.check
                  (all (\ dp ->
                         CSR_Minimal_CSDP_Proofs.qcs_ur_closed_dp_rhs_check
                           (Dependency_Pair_Problem_Spec.rules j dpp) u mu
                           (snd dp))
                    (Dependency_Pair_Problem_Spec.pairs j dpp))
                  (Term_Rewriting.showsl_lit
                    "expanded MU-TERM dependency-pair RHS closure failed"))
                (\ _ ->
                  Error_Monad.bind
                    (Check_Monad.check
                      (CSR_Minimal_CSDP_Proofs.qcs_csr_ur_closed_check
                        (Dependency_Pair_Problem_Spec.rules j dpp) u mu
                        (Dependency_Pair_Problem_Spec.pairs j dpp))
                      (Term_Rewriting.showsl_lit
                        "expanded MU-TERM QCS usable-rule closure failed"))
                    (\ _ ->
                      let {
                        dppU =
                          Dependency_Pair_Problem_Spec.mk j False False
                            (Dependency_Pair_Problem_Spec.pairs j dpp) [] [] []
                            u;
                      } in Check_Termination.check_dp_termination_proof ia j
                             False (Term_Rewriting.add_index i Arith.one_nat)
                             dppU
                             (Check_Termination.Redpair_Proc redp pr
                               subprf))))));
check_muterm_expanded_innermost_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof Check_Termination.P_is_Empty) =
  FOR_Preliminaries.debug i "expanded innermost ordinary DP proof"
    (CSR_Checker_Base.check_csr_dp_termination_proof ia j False i dpp
      (CSR_Checker_Base.CSR_DP_Ordinary_Proof Check_Termination.P_is_Empty));
check_muterm_expanded_innermost_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Subterm_Criterion_Proc v va vb vc))
  = FOR_Preliminaries.debug i "expanded innermost ordinary DP proof"
      (CSR_Checker_Base.check_csr_dp_termination_proof ia j False i dpp
        (CSR_Checker_Base.CSR_DP_Ordinary_Proof
          (Check_Termination.Subterm_Criterion_Proc v va vb vc)));
check_muterm_expanded_innermost_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Gen_Subterm_Criterion_Proc v va vb))
  = FOR_Preliminaries.debug i "expanded innermost ordinary DP proof"
      (CSR_Checker_Base.check_csr_dp_termination_proof ia j False i dpp
        (CSR_Checker_Base.CSR_DP_Ordinary_Proof
          (Check_Termination.Gen_Subterm_Criterion_Proc v va vb)));
check_muterm_expanded_innermost_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Redpair_Proc v va vb))
  = FOR_Preliminaries.debug i "expanded innermost ordinary DP proof"
      (CSR_Checker_Base.check_csr_dp_termination_proof ia j False i dpp
        (CSR_Checker_Base.CSR_DP_Ordinary_Proof
          (Check_Termination.Redpair_Proc v va vb)));
check_muterm_expanded_innermost_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Usable_Rules_Proc v va))
  = FOR_Preliminaries.debug i "expanded innermost ordinary DP proof"
      (CSR_Checker_Base.check_csr_dp_termination_proof ia j False i dpp
        (CSR_Checker_Base.CSR_DP_Ordinary_Proof
          (Check_Termination.Usable_Rules_Proc v va)));
check_muterm_expanded_innermost_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof (Check_Termination.Dep_Graph_Proc v))
  = FOR_Preliminaries.debug i "expanded innermost ordinary DP proof"
      (CSR_Checker_Base.check_csr_dp_termination_proof ia j False i dpp
        (CSR_Checker_Base.CSR_DP_Ordinary_Proof
          (Check_Termination.Dep_Graph_Proc v)));
check_muterm_expanded_innermost_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Mono_Redpair_Proc v va vb vc))
  = FOR_Preliminaries.debug i "expanded innermost ordinary DP proof"
      (CSR_Checker_Base.check_csr_dp_termination_proof ia j False i dpp
        (CSR_Checker_Base.CSR_DP_Ordinary_Proof
          (Check_Termination.Mono_Redpair_Proc v va vb vc)));
check_muterm_expanded_innermost_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Mono_URM_Redpair_Proc v va vb vc))
  = FOR_Preliminaries.debug i "expanded innermost ordinary DP proof"
      (CSR_Checker_Base.check_csr_dp_termination_proof ia j False i dpp
        (CSR_Checker_Base.CSR_DP_Ordinary_Proof
          (Check_Termination.Mono_URM_Redpair_Proc v va vb vc)));
check_muterm_expanded_innermost_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Mono_Redpair_UR_Proc v va vb vc vd))
  = FOR_Preliminaries.debug i "expanded innermost ordinary DP proof"
      (CSR_Checker_Base.check_csr_dp_termination_proof ia j False i dpp
        (CSR_Checker_Base.CSR_DP_Ordinary_Proof
          (Check_Termination.Mono_Redpair_UR_Proc v va vb vc vd)));
check_muterm_expanded_innermost_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Size_Change_Subterm_Proc v))
  = FOR_Preliminaries.debug i "expanded innermost ordinary DP proof"
      (CSR_Checker_Base.check_csr_dp_termination_proof ia j False i dpp
        (CSR_Checker_Base.CSR_DP_Ordinary_Proof
          (Check_Termination.Size_Change_Subterm_Proc v)));
check_muterm_expanded_innermost_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Size_Change_Redpair_Proc v va vb))
  = FOR_Preliminaries.debug i "expanded innermost ordinary DP proof"
      (CSR_Checker_Base.check_csr_dp_termination_proof ia j False i dpp
        (CSR_Checker_Base.CSR_DP_Ordinary_Proof
          (Check_Termination.Size_Change_Redpair_Proc v va vb)));
check_muterm_expanded_innermost_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Uncurry_Proc v va vb vc vd))
  = FOR_Preliminaries.debug i "expanded innermost ordinary DP proof"
      (CSR_Checker_Base.check_csr_dp_termination_proof ia j False i dpp
        (CSR_Checker_Base.CSR_DP_Ordinary_Proof
          (Check_Termination.Uncurry_Proc v va vb vc vd)));
check_muterm_expanded_innermost_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Fcc_Proc v va vb vc vd))
  = FOR_Preliminaries.debug i "expanded innermost ordinary DP proof"
      (CSR_Checker_Base.check_csr_dp_termination_proof ia j False i dpp
        (CSR_Checker_Base.CSR_DP_Ordinary_Proof
          (Check_Termination.Fcc_Proc v va vb vc vd)));
check_muterm_expanded_innermost_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Split_Proc v va vb vc))
  = FOR_Preliminaries.debug i "expanded innermost ordinary DP proof"
      (CSR_Checker_Base.check_csr_dp_termination_proof ia j False i dpp
        (CSR_Checker_Base.CSR_DP_Ordinary_Proof
          (Check_Termination.Split_Proc v va vb vc)));
check_muterm_expanded_innermost_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Semlab_Proc v va vb vc vd))
  = FOR_Preliminaries.debug i "expanded innermost ordinary DP proof"
      (CSR_Checker_Base.check_csr_dp_termination_proof ia j False i dpp
        (CSR_Checker_Base.CSR_DP_Ordinary_Proof
          (Check_Termination.Semlab_Proc v va vb vc vd)));
check_muterm_expanded_innermost_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Switch_Innermost_Proc v va))
  = FOR_Preliminaries.debug i "expanded innermost ordinary DP proof"
      (CSR_Checker_Base.check_csr_dp_termination_proof ia j False i dpp
        (CSR_Checker_Base.CSR_DP_Ordinary_Proof
          (Check_Termination.Switch_Innermost_Proc v va)));
check_muterm_expanded_innermost_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Rewriting_Proc v va vb vc vd ve vf))
  = FOR_Preliminaries.debug i "expanded innermost ordinary DP proof"
      (CSR_Checker_Base.check_csr_dp_termination_proof ia j False i dpp
        (CSR_Checker_Base.CSR_DP_Ordinary_Proof
          (Check_Termination.Rewriting_Proc v va vb vc vd ve vf)));
check_muterm_expanded_innermost_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Instantiation_Proc v va vb))
  = FOR_Preliminaries.debug i "expanded innermost ordinary DP proof"
      (CSR_Checker_Base.check_csr_dp_termination_proof ia j False i dpp
        (CSR_Checker_Base.CSR_DP_Ordinary_Proof
          (Check_Termination.Instantiation_Proc v va vb)));
check_muterm_expanded_innermost_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Forward_Instantiation_Proc v va vb vc))
  = FOR_Preliminaries.debug i "expanded innermost ordinary DP proof"
      (CSR_Checker_Base.check_csr_dp_termination_proof ia j False i dpp
        (CSR_Checker_Base.CSR_DP_Ordinary_Proof
          (Check_Termination.Forward_Instantiation_Proc v va vb vc)));
check_muterm_expanded_innermost_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Narrowing_Proc v va vb vc))
  = FOR_Preliminaries.debug i "expanded innermost ordinary DP proof"
      (CSR_Checker_Base.check_csr_dp_termination_proof ia j False i dpp
        (CSR_Checker_Base.CSR_DP_Ordinary_Proof
          (Check_Termination.Narrowing_Proc v va vb vc)));
check_muterm_expanded_innermost_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Assume_Finite v va))
  = FOR_Preliminaries.debug i "expanded innermost ordinary DP proof"
      (CSR_Checker_Base.check_csr_dp_termination_proof ia j False i dpp
        (CSR_Checker_Base.CSR_DP_Ordinary_Proof
          (Check_Termination.Assume_Finite v va)));
check_muterm_expanded_innermost_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Q_Reduction_Proc v va))
  = FOR_Preliminaries.debug i "expanded innermost ordinary DP proof"
      (CSR_Checker_Base.check_csr_dp_termination_proof ia j False i dpp
        (CSR_Checker_Base.CSR_DP_Ordinary_Proof
          (Check_Termination.Q_Reduction_Proc v va)));
check_muterm_expanded_innermost_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Complex_Constant_Removal_Proc v va))
  = FOR_Preliminaries.debug i "expanded innermost ordinary DP proof"
      (CSR_Checker_Base.check_csr_dp_termination_proof ia j False i dpp
        (CSR_Checker_Base.CSR_DP_Ordinary_Proof
          (Check_Termination.Complex_Constant_Removal_Proc v va)));
check_muterm_expanded_innermost_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.General_Redpair_Proc v va vb vc vd))
  = FOR_Preliminaries.debug i "expanded innermost ordinary DP proof"
      (CSR_Checker_Base.check_csr_dp_termination_proof ia j False i dpp
        (CSR_Checker_Base.CSR_DP_Ordinary_Proof
          (Check_Termination.General_Redpair_Proc v va vb vc vd)));
check_muterm_expanded_innermost_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof (Check_Termination.To_Trs_Proc v)) =
  FOR_Preliminaries.debug i "expanded innermost ordinary DP proof"
    (CSR_Checker_Base.check_csr_dp_termination_proof ia j False i dpp
      (CSR_Checker_Base.CSR_DP_Ordinary_Proof
        (Check_Termination.To_Trs_Proc v)));
check_muterm_expanded_innermost_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Zantema_To_SRS_Proc v))
  = FOR_Preliminaries.debug i "expanded innermost ordinary DP proof"
      (CSR_Checker_Base.check_csr_dp_termination_proof ia j False i dpp
        (CSR_Checker_Base.CSR_DP_Ordinary_Proof
          (Check_Termination.Zantema_To_SRS_Proc v)));
check_muterm_expanded_innermost_proof ia j mu i dpp
  CSR_Checker_Base.CSR_DP_P_is_Empty =
  CSR_Innermost_Active_SCT.check_innermost_csr_dp_termination_proof_active_sct
    ia j mu i dpp CSR_Checker_Base.CSR_DP_P_is_Empty;
check_muterm_expanded_innermost_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Subterm_Criterion_Proc v va vb vc) =
  CSR_Innermost_Active_SCT.check_innermost_csr_dp_termination_proof_active_sct
    ia j mu i dpp (CSR_Checker_Base.CSR_DP_Subterm_Criterion_Proc v va vb vc);
check_muterm_expanded_innermost_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Gen_Subterm_Criterion_Proc v va vb) =
  CSR_Innermost_Active_SCT.check_innermost_csr_dp_termination_proof_active_sct
    ia j mu i dpp (CSR_Checker_Base.CSR_DP_Gen_Subterm_Criterion_Proc v va vb);
check_muterm_expanded_innermost_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Usable_Rules_Proc v va) =
  CSR_Innermost_Active_SCT.check_innermost_csr_dp_termination_proof_active_sct
    ia j mu i dpp (CSR_Checker_Base.CSR_DP_Usable_Rules_Proc v va);
check_muterm_expanded_innermost_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Forward_Instantiation_Proc v va vb) =
  CSR_Innermost_Active_SCT.check_innermost_csr_dp_termination_proof_active_sct
    ia j mu i dpp (CSR_Checker_Base.CSR_DP_Forward_Instantiation_Proc v va vb);
check_muterm_expanded_innermost_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Redpair_UR_Proc v va vb vc) =
  CSR_Innermost_Active_SCT.check_innermost_csr_dp_termination_proof_active_sct
    ia j mu i dpp (CSR_Checker_Base.CSR_DP_Redpair_UR_Proc v va vb vc);
check_muterm_expanded_innermost_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Size_Change_Subterm_Proc v) =
  CSR_Innermost_Active_SCT.check_innermost_csr_dp_termination_proof_active_sct
    ia j mu i dpp (CSR_Checker_Base.CSR_DP_Size_Change_Subterm_Proc v);

check_muterm_expanded_innermost_components ::
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
check_muterm_expanded_innermost_components ia j mu i dpp [] = Sum_Type.Inr ();
check_muterm_expanded_innermost_components ia j mu i dpp ((Nothing, c) : rest) =
  check_muterm_expanded_innermost_components ia j mu
    (Term_Rewriting.add_index i Arith.one_nat) dpp rest;
check_muterm_expanded_innermost_components ia j mu i dpp ((Just prf, c) : rest)
  = Error_Monad.bind
      (check_muterm_expanded_innermost_proof ia j mu
        (Term_Rewriting.add_index i Arith.one_nat)
        (Dependency_Pair_Problem_Spec.intersect_pairs j dpp c) prf)
      (\ _ ->
        check_muterm_expanded_innermost_components ia j mu
          (Term_Rewriting.add_index i Arith.one_nat) dpp rest);

}
