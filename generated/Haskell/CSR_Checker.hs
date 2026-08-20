{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  CSR_Checker(check_csr_dep_graph_proc, check_csr_dp_termination_proof_core,
               check_csr_termination_proof)
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
import qualified QDP_Framework_Impl;
import qualified Check_Termination;
import qualified Subterm_Criterion_Impl;
import qualified FOR_Preliminaries;
import qualified Reduction_Pair_Implementations;
import qualified Termination_Problem_Spec;
import qualified Countable;
import qualified CSR_Checker_Base;
import qualified Context_Sensitive_Impl;
import qualified Check_Monad;
import qualified Graph;
import qualified Error_Monad;
import qualified HOL;
import qualified Dependency_Pair_Problem_Spec;
import qualified Multi_Map;
import qualified Sum_Type;
import qualified Compare;
import qualified Labelings;
import qualified Compare_Order_Instances;
import qualified Term_Rewriting;
import qualified Mapping;
import qualified Arith;

check_csr_dep_graph_proc ::
  forall a b c d.
    (Compare.Compare_order b, Eq b, Term_Rewriting.Showl b,
      Compare.Compare_order c, Eq c,
      Term_Rewriting.Showl c) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a
                                   (Labelings.Lab b c) [Arith.Char] () ->
                                   [((Labelings.Lab b c, Arith.Nat),
                                      [Arith.Nat])] ->
                                     a -> [(Maybe d,
     [(Term_Rewriting.Term (Labelings.Lab b c) [Arith.Char],
        Term_Rewriting.Term (Labelings.Lab b c) [Arith.Char])])] ->
    Sum_Type.Sum (String -> String) ();
check_csr_dep_graph_proc j mu dpp dps =
  let {
    p = Dependency_Pair_Problem_Spec.pairs j dpp;
    r = Dependency_Pair_Problem_Spec.rules j dpp;
  } in Error_Monad.bind (Term_Rewriting.check_wf_trs r)
         (\ _ ->
           Error_Monad.bind
             (Error_Monad.catch_error
               (Check_Monad.check_subseteq p (concatMap snd dps))
               (\ x ->
                 Sum_Type.Inl
                   ((Term_Rewriting.showsl_lit "CSR dependency pair " .
                      Term_Rewriting.showsl_rule x) .
                     Term_Rewriting.showsl_lit
                       " is missing in decomposition\n")))
             (\ _ ->
               Error_Monad.catch_error
                 (Graph.check_graph_decomp (Term_Rewriting.showsl_prod . fst)
                   (Multi_Map.empty ((Term_Rewriting.root . fst) . fst))
                   CSR_Checker_Base.graph_approx_csr_rt Multi_Map.insert
                   (CSR_Checker_Base.csr_dep_graph_edge_check
                     (CSR_Checker_Base.csr_dp_root_mu
                       (Context_Sensitive_Impl.mu_of mu))
                     r)
                   (map (\ (real, cs) ->
                          (not (Arith.is_none real),
                            map (\ (s, t) -> ((s, t), ())) cs))
                     dps))
                 (\ x ->
                   Sum_Type.Inl
                     ((Term_Rewriting.showsl_lit
                         "our CSR dependency-graph estimation could not show that you have a valid decomposition " .
                        Term_Rewriting.showsl_lit
                          "due to the following reason\n") .
                       x))));

check_csr_dp_termination_proof_core ::
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
                                       Bool ->
 (String -> String) ->
   c -> CSR_Checker_Base.Csr_dp_termination_proof b [Arith.Nat] [Arith.Char] ->
          Sum_Type.Sum (String -> String) ();
check_csr_dp_termination_proof_core ia j mu a i dpp
  CSR_Checker_Base.CSR_DP_P_is_Empty =
  FOR_Preliminaries.debug i "CSR-DP P is empty"
    (if null (Dependency_Pair_Problem_Spec.pairs j dpp) then Sum_Type.Inr ()
      else Sum_Type.Inl
             ((i . Term_Rewriting.showsl_lit
                     ": CSR-DP P is not empty in the following DP-problem\n") .
               QDP_Framework_Impl.showsl_dpp j dpp));
check_csr_dp_termination_proof_core ia j mu a i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof prf) =
  CSR_Checker_Base.check_csr_dp_termination_proof ia j a i dpp
    (CSR_Checker_Base.CSR_DP_Ordinary_Proof prf);
check_csr_dp_termination_proof_core ia j mu a i dpp
  (CSR_Checker_Base.CSR_DP_Subterm_Criterion_Proc p rseq pr prf) =
  CSR_Checker_Base.check_csr_dp_termination_proof ia j a i dpp
    (CSR_Checker_Base.CSR_DP_Subterm_Criterion_Proc p rseq pr prf);
check_csr_dp_termination_proof_core ia j mu a i dpp
  (CSR_Checker_Base.CSR_DP_Gen_Subterm_Criterion_Proc p pr prf) =
  CSR_Checker_Base.check_csr_dp_termination_proof ia j a i dpp
    (CSR_Checker_Base.CSR_DP_Gen_Subterm_Criterion_Proc p pr prf);
check_csr_dp_termination_proof_core ia j mu a i dpp
  (CSR_Checker_Base.CSR_DP_Usable_Rules_Proc u prf) =
  FOR_Preliminaries.debug i "CSR-DP usable rules"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (CSR_Checker_Base.csr_mu_usable_rules_proc j mu u dpp)
        (\ x ->
          Sum_Type.Inl
            ((i . Term_Rewriting.showsl_lit
                    ": error when applying CSR usable rules\n") .
              x)))
      (\ dppa ->
        Error_Monad.bind
          (Error_Monad.catch_error
            (Error_Monad.forallM
              (\ lr ->
                Check_Monad.check (Arith.membera u lr)
                  ((i . Term_Rewriting.showsl_lit
                          ": conservative CSR usable-rules checker requires the usable rules to contain ") .
                    Term_Rewriting.showsl_rule lr))
              (Dependency_Pair_Problem_Spec.rules j dpp))
            (\ x -> Sum_Type.Inl (snd x)))
          (\ _ ->
            Error_Monad.catch_error
              (check_csr_dp_termination_proof_core ia j mu a
                (Term_Rewriting.add_index i Arith.one_nat) dppa prf)
              (\ x ->
                Sum_Type.Inl
                  ((i . Term_Rewriting.showsl_lit
                          ": error below CSR usable rules\n") .
                    x)))));
check_csr_dp_termination_proof_core ia j mu a i dpp
  (CSR_Checker_Base.CSR_DP_Dep_Graph_Proc edpts) =
  FOR_Preliminaries.debug i "CSR-DP dependency graph"
    (Error_Monad.bind
      (Error_Monad.catch_error (check_csr_dep_graph_proc j mu dpp edpts)
        (\ x ->
          Sum_Type.Inl
            ((i . Term_Rewriting.showsl_lit
                    ": error when applying CSR dependency graph\n") .
              x)))
      (\ _ ->
        Error_Monad.catch_error
          (check_csr_dp_graph_components ia j mu a i dpp edpts)
          (\ x ->
            Sum_Type.Inl
              ((i . Term_Rewriting.showsl_lit
                      ": error below CSR dependency graph\n") .
                x))));
check_csr_dp_termination_proof_core ia j mu a i dpp
  (CSR_Checker_Base.CSR_DP_Instantiation_Proc st sts prf) =
  Sum_Type.Inl
    (i . Term_Rewriting.showsl_lit
           ": context-sensitive instantiation requires improved CS-DPs");
check_csr_dp_termination_proof_core ia j mu a i dpp
  (CSR_Checker_Base.CSR_DP_Forward_Instantiation_Proc st sts prf) =
  Sum_Type.Inl
    (i . Term_Rewriting.showsl_lit
           ": context-sensitive forward instantiation requires improved CS-DPs");
check_csr_dp_termination_proof_core ia j mu a i dpp
  (CSR_Checker_Base.CSR_DP_Redpair_UR_Proc redp pr u prf) =
  Sum_Type.Inl
    (i . Term_Rewriting.showsl_lit
           ": context-sensitive U3 reduction pairs require minimal CS-DPs");
check_csr_dp_termination_proof_core ia j mu a i dpp
  (CSR_Checker_Base.CSR_DP_Size_Change_Subterm_Proc graphs) =
  CSR_Checker_Base.check_csr_dp_termination_proof ia j a i dpp
    (CSR_Checker_Base.CSR_DP_Size_Change_Subterm_Proc graphs);

check_csr_dp_graph_components ::
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
                                       Bool ->
 (String -> String) ->
   c -> [(Maybe (CSR_Checker_Base.Csr_dp_termination_proof b [Arith.Nat]
                  [Arith.Char]),
           [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
              Term_Rewriting.Term (Labelings.Lab b [Arith.Nat])
                [Arith.Char])])] ->
          Sum_Type.Sum (String -> String) ();
check_csr_dp_graph_components ia j mu a i dpp [] = Sum_Type.Inr ();
check_csr_dp_graph_components ia j mu a i dpp ((Nothing, p) : rest) =
  check_csr_dp_graph_components ia j mu a
    (Term_Rewriting.add_index i Arith.one_nat) dpp rest;
check_csr_dp_graph_components ia j mu a i dpp ((Just prf, p) : rest) =
  Error_Monad.bind
    (check_csr_dp_termination_proof_core ia j mu a
      (Term_Rewriting.add_index i Arith.one_nat)
      (Dependency_Pair_Problem_Spec.intersect_pairs j dpp p) prf)
    (\ _ ->
      check_csr_dp_graph_components ia j mu a
        (Term_Rewriting.add_index i Arith.one_nat) dpp rest);

check_csr_termination_proof ::
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
     CSR_Checker_Base.Csr_termination_proof b [Arith.Nat] [Arith.Char] ->
       Sum_Type.Sum (String -> String) ();
check_csr_termination_proof ia j a i mu r CSR_Checker_Base.CSR_R_is_Empty =
  FOR_Preliminaries.debug i "CSR R is empty"
    (if null r then Sum_Type.Inr ()
      else Sum_Type.Inl (i . Term_Rewriting.showsl_lit ": CSR R is not empty"));
check_csr_termination_proof ia j a i mu r
  (CSR_Checker_Base.CSR_Rule_Removal redp rr prf) =
  FOR_Preliminaries.debug i "CSR rule removal"
    (case CSR_Checker_Base.csr_rule_removal_impl redp mu rr r of {
      Sum_Type.Inl aa -> Sum_Type.Inl aa;
      Sum_Type.Inr r2 -> check_csr_termination_proof ia j a i mu r2 prf;
    });
check_csr_termination_proof ia j a i mu r
  (CSR_Checker_Base.CSR_Dependency_Pairs p prf) =
  FOR_Preliminaries.debug i "CSR dependency pairs"
    (Error_Monad.bind
      (Error_Monad.catch_error (CSR_Checker_Base.csr_sharp_mu_check mu)
        (\ x ->
          Sum_Type.Inl
            ((i . Term_Rewriting.showsl_lit
                    ": invalid replacement map for CSR dependency pairs\n") .
              x)))
      (\ _ ->
        (case CSR_Checker_Base.mu_csr_dependency_pairs_tt Labelings.Sharp j mu r
                p
          of {
          Sum_Type.Inl _ ->
            Error_Monad.bind
              (Error_Monad.catch_error
                (CSR_Checker_Base.safe_csr_dependency_pairs_tt Labelings.Sharp j
                  mu r p)
                (\ x ->
                  Sum_Type.Inl
                    ((((((i . Term_Rewriting.showsl_lit
                                ": error when switching from CSR to a safe CS-DP problem\n") .
                          Term_Rewriting.showsl_rules r) .
                         Term_Rewriting.showsl_lit "\nwith pairs\n") .
                        Term_Rewriting.showsl_rules p) .
                       Term_Rewriting.showsl_literal "\n") .
                      x)))
              (\ dpp ->
                Error_Monad.catch_error
                  (CSR_Checker_Base.check_csr_dp_termination_proof ia j False
                    (Term_Rewriting.add_index i Arith.one_nat) dpp prf)
                  (\ x ->
                    Sum_Type.Inl
                      ((i . Term_Rewriting.showsl_lit
                              ": error below safe CSR dependency pairs\n") .
                        x)));
          Sum_Type.Inr dpp ->
            Error_Monad.catch_error
              (check_csr_dp_termination_proof_core ia j mu False
                (Term_Rewriting.add_index i Arith.one_nat) dpp prf)
              (\ x ->
                Sum_Type.Inl
                  ((i . Term_Rewriting.showsl_lit
                          ": error below replacement-map-specific CSR dependency pairs\n") .
                    x));
        })));
check_csr_termination_proof ia j a i mu r
  (CSR_Checker_Base.CSR_Safe_Dependency_Pairs p prf) =
  FOR_Preliminaries.debug i "safe CSR dependency pairs"
    (Error_Monad.bind
      (Error_Monad.catch_error (CSR_Checker_Base.csr_sharp_mu_check mu)
        (\ x ->
          Sum_Type.Inl
            ((i . Term_Rewriting.showsl_lit
                    ": invalid replacement map for safe CSR dependency pairs\n") .
              x)))
      (\ _ ->
        Error_Monad.bind
          (Error_Monad.catch_error
            (CSR_Checker_Base.safe_csr_dependency_pairs_tt Labelings.Sharp j mu
              r p)
            (\ x ->
              Sum_Type.Inl
                ((((((i . Term_Rewriting.showsl_lit
                            ": error when switching from CSR to a safe CS-DP problem\n") .
                      Term_Rewriting.showsl_rules r) .
                     Term_Rewriting.showsl_lit "\nwith pairs\n") .
                    Term_Rewriting.showsl_rules p) .
                   Term_Rewriting.showsl_literal "\n") .
                  x)))
          (\ dpp ->
            Error_Monad.catch_error
              (CSR_Checker_Base.check_csr_dp_termination_proof ia j False
                (Term_Rewriting.add_index i Arith.one_nat) dpp prf)
              (\ x ->
                Sum_Type.Inl
                  ((i . Term_Rewriting.showsl_lit
                          ": error below safe CSR dependency pairs\n") .
                    x)))));

}
