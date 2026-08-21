{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  CSR_Conservative_Checker(Extended_csr_termination_proof(..),
                            check_extended_csr_termination_proof)
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
import qualified CSR_Mixed_Subterm_Proofs;
import qualified CSR_Checker;
import qualified Check_Termination;
import qualified Subterm_Criterion_Impl;
import qualified Compare_Order_Instances;
import qualified CSR_Improved_CSDP_Proofs;
import qualified CSR_Minimal_CSDP_Proofs;
import qualified CSR_Innermost_Switch;
import qualified FOR_Preliminaries;
import qualified Error_Monad;
import qualified Dependency_Pair_Problem_Spec;
import qualified Termination_Problem_Spec;
import qualified Sum_Type;
import qualified Countable;
import qualified Compare;
import qualified Arith;
import qualified Reduction_Pair_Implementations;
import qualified CSR_Checker_Base;
import qualified Labelings;
import qualified Term_Rewriting;

data Extended_csr_termination_proof a b c =
  Direct_CSR_Proof (CSR_Checker_Base.Csr_termination_proof a b c)
  | Orthogonality_Checked_CSR_Proof
      (CSR_Checker_Base.Csr_termination_proof a b c)
  | Improved_CSR_Dependency_Pairs (Labelings.Lab a b)
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      (CSR_Checker_Base.Csr_dp_termination_proof a b c)
  | CSR_Rule_Removal_Then_Improved
      (Reduction_Pair_Implementations.Redtriple_impl (Labelings.Lab a b))
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      (Labelings.Lab a b)
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      (CSR_Checker_Base.Csr_dp_termination_proof a b c)
  | Conservative_CSR_Dependency_Pairs (Labelings.Lab a b)
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      (CSR_Checker_Base.Csr_dp_termination_proof a b c);

unhiding_subterm_pair_check ::
  forall a b.
    (Eq a,
      Eq b) => a -> (Term_Rewriting.Term a b, Term_Rewriting.Term a b) -> Bool;
unhiding_subterm_pair_check u
  (Term_Rewriting.Fun v [s], Term_Rewriting.Fun w [t]) =
  v == u && w == u && Term_Rewriting.supt_impl s t;
unhiding_subterm_pair_check u (Term_Rewriting.Var vb, va) = False;
unhiding_subterm_pair_check u (Term_Rewriting.Fun vb [], va) = False;
unhiding_subterm_pair_check u (Term_Rewriting.Fun vb (vd : vf : vg), va) =
  False;
unhiding_subterm_pair_check u (v, Term_Rewriting.Var vb) = False;
unhiding_subterm_pair_check u (v, Term_Rewriting.Fun vb []) = False;
unhiding_subterm_pair_check u (v, Term_Rewriting.Fun vb (vd : vf : vg)) = False;

unhiding_subterm_pairs_check ::
  forall a b.
    (Eq a,
      Eq b) => a -> [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
                      Bool;
unhiding_subterm_pairs_check u p = all (unhiding_subterm_pair_check u) p;

check_improved_csr_dp_termination_proof ::
  forall a b c.
    (Compare.Compare_order b, Countable.Countable b, Eq b,
      Term_Rewriting.Showl b) => Termination_Problem_Spec.Tp_ops_ext a
                                   (Labelings.Lab b [Arith.Nat]) [Arith.Char]
                                   () ->
                                   Dependency_Pair_Problem_Spec.Dpp_ops_ext c
                                     (Labelings.Lab b [Arith.Nat]) [Arith.Char]
                                     () ->
                                     Labelings.Lab b [Arith.Nat] ->
                                       [((Labelings.Lab b [Arith.Nat],
   Arith.Nat),
  [Arith.Nat])] ->
 Bool ->
   (String -> String) ->
     c -> CSR_Checker_Base.Csr_dp_termination_proof b [Arith.Nat]
            [Arith.Char] ->
            Sum_Type.Sum (String -> String) ();
check_improved_csr_dp_termination_proof ia j u mu a i dpp
  (CSR_Checker_Base.CSR_DP_Usable_Rules_Proc us prf) =
  FOR_Preliminaries.debug i "improved QCS usable rules"
    (Error_Monad.bind
      (CSR_Minimal_CSDP_Proofs.csr_qcs_usable_rules_proc j mu us dpp)
      (\ dppa ->
        check_improved_csr_dp_termination_proof ia j u mu a
          (Term_Rewriting.add_index i Arith.one_nat) dppa prf));
check_improved_csr_dp_termination_proof ia j u mu a i dpp
  (CSR_Checker_Base.CSR_DP_Dep_Graph_Proc edpts) =
  FOR_Preliminaries.debug i "improved minimal CSR-DP dependency graph"
    (Error_Monad.bind (CSR_Checker.check_csr_dep_graph_proc j mu dpp edpts)
      (\ _ -> check_improved_csr_dp_graph_components ia j u mu a i dpp edpts));
check_improved_csr_dp_termination_proof ia j u mu a i dpp
  (CSR_Checker_Base.CSR_DP_Instantiation_Proc st sts prf) =
  FOR_Preliminaries.debug i "LPAR08 CS instantiation"
    (Error_Monad.bind
      (CSR_Minimal_CSDP_Proofs.csr_instantiation_proc j mu st sts dpp)
      (\ dppa ->
        check_improved_csr_dp_termination_proof ia j u mu a
          (Term_Rewriting.add_index i Arith.one_nat) dppa prf));
check_improved_csr_dp_termination_proof ia j u mu a i dpp
  (CSR_Checker_Base.CSR_DP_Forward_Instantiation_Proc st sts prf) =
  FOR_Preliminaries.debug i "CSR forward instantiation"
    (Error_Monad.bind
      (CSR_Minimal_CSDP_Proofs.csr_forward_instantiation_proc j mu st sts dpp)
      (\ dppa ->
        check_improved_csr_dp_termination_proof ia j u mu a
          (Term_Rewriting.add_index i Arith.one_nat) dppa prf));
check_improved_csr_dp_termination_proof ia j u mu a i dpp
  (CSR_Checker_Base.CSR_DP_Redpair_UR_Proc redp pr us prf) =
  FOR_Preliminaries.debug i "LPAR08 U3 reduction pair"
    (Error_Monad.bind
      (CSR_Minimal_CSDP_Proofs.csr_u3_redpair_proc j mu
        (Reduction_Pair_Implementations.get_rel_impl redp) pr us dpp)
      (\ dppa ->
        check_improved_csr_dp_termination_proof ia j u mu a
          (Term_Rewriting.add_index i Arith.one_nat) dppa prf));
check_improved_csr_dp_termination_proof ia j u mu a i dpp
  (CSR_Checker_Base.CSR_DP_Size_Change_Subterm_Proc graphs) =
  (if unhiding_subterm_pairs_check u (Dependency_Pair_Problem_Spec.pairs j dpp)
    then FOR_Preliminaries.debug i "LPAR08 unhiding subterm" (Sum_Type.Inr ())
    else CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu a i
           dpp (CSR_Checker_Base.CSR_DP_Size_Change_Subterm_Proc graphs));
check_improved_csr_dp_termination_proof ia j u mu a i dpp
  (CSR_Checker_Base.CSR_DP_Subterm_Criterion_Proc p rseq pr prf) =
  (if CSR_Mixed_Subterm_Proofs.csr_mixed_unhiding_present u
        (Dependency_Pair_Problem_Spec.pairs j dpp)
    then FOR_Preliminaries.debug i "LPAR08 mixed marked/unhiding subterm"
           (Error_Monad.bind
             (CSR_Mixed_Subterm_Proofs.csr_mixed_subterm_proc j u mu p rseq pr
               dpp)
             (\ dppa ->
               check_improved_csr_dp_termination_proof ia j u mu a
                 (Term_Rewriting.add_index i Arith.one_nat) dppa prf))
    else CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu a i
           dpp (CSR_Checker_Base.CSR_DP_Subterm_Criterion_Proc p rseq pr prf));
check_improved_csr_dp_termination_proof ia j u mu a i dpp
  CSR_Checker_Base.CSR_DP_P_is_Empty =
  CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu a i dpp
    CSR_Checker_Base.CSR_DP_P_is_Empty;
check_improved_csr_dp_termination_proof ia j u mu a i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof v) =
  CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu a i dpp
    (CSR_Checker_Base.CSR_DP_Ordinary_Proof v);
check_improved_csr_dp_termination_proof ia j u mu a i dpp
  (CSR_Checker_Base.CSR_DP_Gen_Subterm_Criterion_Proc v va vb) =
  CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu a i dpp
    (CSR_Checker_Base.CSR_DP_Gen_Subterm_Criterion_Proc v va vb);

check_improved_csr_dp_graph_components ::
  forall a b c.
    (Compare.Compare_order b, Countable.Countable b, Eq b,
      Term_Rewriting.Showl b) => Termination_Problem_Spec.Tp_ops_ext a
                                   (Labelings.Lab b [Arith.Nat]) [Arith.Char]
                                   () ->
                                   Dependency_Pair_Problem_Spec.Dpp_ops_ext c
                                     (Labelings.Lab b [Arith.Nat]) [Arith.Char]
                                     () ->
                                     Labelings.Lab b [Arith.Nat] ->
                                       [((Labelings.Lab b [Arith.Nat],
   Arith.Nat),
  [Arith.Nat])] ->
 Bool ->
   (String -> String) ->
     c -> [(Maybe (CSR_Checker_Base.Csr_dp_termination_proof b [Arith.Nat]
                    [Arith.Char]),
             [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
                Term_Rewriting.Term (Labelings.Lab b [Arith.Nat])
                  [Arith.Char])])] ->
            Sum_Type.Sum (String -> String) ();
check_improved_csr_dp_graph_components ia j u mu a i dpp [] = Sum_Type.Inr ();
check_improved_csr_dp_graph_components ia j u mu a i dpp ((Nothing, p) : rest) =
  check_improved_csr_dp_graph_components ia j u mu a
    (Term_Rewriting.add_index i Arith.one_nat) dpp rest;
check_improved_csr_dp_graph_components ia j u mu a i dpp ((Just prf, p) : rest)
  = Error_Monad.bind
      (check_improved_csr_dp_termination_proof ia j u mu a
        (Term_Rewriting.add_index i Arith.one_nat)
        (Dependency_Pair_Problem_Spec.intersect_pairs j dpp p) prf)
      (\ _ ->
        check_improved_csr_dp_graph_components ia j u mu a
          (Term_Rewriting.add_index i Arith.one_nat) dpp rest);

check_extended_csr_termination_proof ::
  forall a b c.
    (Compare.Compare_order b, Countable.Countable b, Eq b,
      Term_Rewriting.Showl b) => Termination_Problem_Spec.Tp_ops_ext a
                                   (Labelings.Lab b [Arith.Nat]) [Arith.Char]
                                   () ->
                                   Dependency_Pair_Problem_Spec.Dpp_ops_ext c
                                     (Labelings.Lab b [Arith.Nat]) [Arith.Char]
                                     () ->
                                     Bool ->
                                       (String -> String) ->
 [((Labelings.Lab b [Arith.Nat], Arith.Nat), [Arith.Nat])] ->
   [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
      Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
     Extended_csr_termination_proof b [Arith.Nat] [Arith.Char] ->
       Sum_Type.Sum (String -> String) ();
check_extended_csr_termination_proof ia j a i mu r (Direct_CSR_Proof prf) =
  CSR_Minimal_CSDP_Proofs.check_csr_termination_proof_min ia j a i mu r prf;
check_extended_csr_termination_proof ia j a i mu r
  (Orthogonality_Checked_CSR_Proof prf) =
  FOR_Preliminaries.debug i "CSR orthogonality check"
    (Error_Monad.bind
      (Error_Monad.catch_error (CSR_Innermost_Switch.check_csr_orthogonal r)
        (\ x ->
          Sum_Type.Inl
            ((i . Term_Rewriting.showsl_lit
                    ": invalid orthogonality witness\n") .
              x)))
      (\ _ ->
        Error_Monad.catch_error
          (CSR_Minimal_CSDP_Proofs.check_csr_termination_proof_min ia j a
            (Term_Rewriting.add_index i Arith.one_nat) mu r prf)
          (\ x ->
            Sum_Type.Inl
              ((i . Term_Rewriting.showsl_lit
                      ": error below CSR orthogonality check\n") .
                x))));
check_extended_csr_termination_proof ia j a i mu r
  (Improved_CSR_Dependency_Pairs u p prf) =
  FOR_Preliminaries.debug i "improved CSR dependency pairs"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (CSR_Improved_CSDP_Proofs.improved_csr_dependency_pairs_tt j u mu r p)
        (\ x ->
          Sum_Type.Inl
            ((i . Term_Rewriting.showsl_lit
                    ": invalid improved CSR-DP transformation\n") .
              x)))
      (\ dpp ->
        Error_Monad.catch_error
          (check_improved_csr_dp_termination_proof ia j u mu False
            (Term_Rewriting.add_index i Arith.one_nat) dpp prf)
          (\ x ->
            Sum_Type.Inl
              ((i . Term_Rewriting.showsl_lit
                      ": error below improved CSR dependency pairs\n") .
                x))));
check_extended_csr_termination_proof ia j a i mu r
  (CSR_Rule_Removal_Then_Improved redp rr u p prf) =
  FOR_Preliminaries.debug i
    "CSR rule removal followed by improved CSR dependency pairs"
    (Error_Monad.bind (CSR_Checker_Base.csr_rule_removal_impl redp mu rr r)
      (\ r2 ->
        Error_Monad.bind
          (Error_Monad.catch_error
            (CSR_Improved_CSDP_Proofs.improved_csr_dependency_pairs_tt j u mu r2
              p)
            (\ x ->
              Sum_Type.Inl
                ((i . Term_Rewriting.showsl_lit
                        ": invalid improved CSR-DP transformation after CSR rule removal\n") .
                  x)))
          (\ dpp ->
            Error_Monad.catch_error
              (check_improved_csr_dp_termination_proof ia j u mu False
                (Term_Rewriting.add_index i Arith.one_nat) dpp prf)
              (\ x ->
                Sum_Type.Inl
                  ((i . Term_Rewriting.showsl_lit
                          ": error below improved CSR dependency pairs after CSR rule removal\n") .
                    x)))));
check_extended_csr_termination_proof ia j a i mu r
  (Conservative_CSR_Dependency_Pairs u p s prf) =
  FOR_Preliminaries.debug i "conservative CSR dependency pairs"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (CSR_Improved_CSDP_Proofs.conservative_csr_dependency_pairs_tt j u mu r
          p s)
        (\ x ->
          Sum_Type.Inl
            ((i . Term_Rewriting.showsl_lit
                    ": invalid conservative CSR-DP transformation\n") .
              x)))
      (\ dpp ->
        Error_Monad.catch_error
          (CSR_Checker_Base.check_csr_dp_termination_proof ia j False
            (Term_Rewriting.add_index i Arith.one_nat) dpp prf)
          (\ x ->
            Sum_Type.Inl
              ((i . Term_Rewriting.showsl_lit
                      ": error below conservative CSR dependency pairs\n") .
                x))));

}
