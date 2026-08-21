{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  CSR_Innermost_DP_Checker(csr_dp_root_supt_list,
                            check_innermost_csr_dep_graph_proc,
                            check_innermost_csr_dp_termination_proof)
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
import qualified CSR_Checker;
import qualified FOR_Preliminaries;
import qualified Reduction_Pair_Implementations;
import qualified Check_Termination;
import qualified Subterm_Criterion_Impl;
import qualified Termination_Problem_Spec;
import qualified Countable;
import qualified Context_Sensitive_Impl;
import qualified Check_Monad;
import qualified Graph;
import qualified Error_Monad;
import qualified HOL;
import qualified Dependency_Pair_Problem_Spec;
import qualified Multi_Map;
import qualified Sum_Type;
import qualified Compare_Order_Instances;
import qualified Mapping;
import qualified CSR_Checker_Base;
import qualified Arith;
import qualified Labelings;
import qualified Compare;
import qualified Term_Rewriting;

csr_dp_unsharp_root ::
  forall a b c.
    (Compare.Compare_order a,
      Term_Rewriting.Showl a) => Term_Rewriting.Term (Labelings.Lab a b) c ->
                                   Term_Rewriting.Term (Labelings.Lab a b) c;
csr_dp_unsharp_root (Term_Rewriting.Var x) = Term_Rewriting.Var x;
csr_dp_unsharp_root (Term_Rewriting.Fun (Labelings.Sharp f) ts) =
  Term_Rewriting.Fun f ts;
csr_dp_unsharp_root (Term_Rewriting.Fun (Labelings.Lab v va) ts) =
  Term_Rewriting.Fun (Labelings.Lab v va) ts;
csr_dp_unsharp_root (Term_Rewriting.Fun (Labelings.FunLab v va) ts) =
  Term_Rewriting.Fun (Labelings.FunLab v va) ts;
csr_dp_unsharp_root (Term_Rewriting.Fun (Labelings.UnLab v) ts) =
  Term_Rewriting.Fun (Labelings.UnLab v) ts;

csr_dp_root_supt_list ::
  forall a b c.
    (Compare.Compare_order a, Eq a, Term_Rewriting.Showl a,
      Eq b) => [((Labelings.Lab a b, Arith.Nat), [Arith.Nat])] ->
                 Term_Rewriting.Term (Labelings.Lab a b) c ->
                   [Term_Rewriting.Term (Labelings.Lab a b) c];
csr_dp_root_supt_list mu s =
  CSR_Checker_Base.mu_supt_list mu (csr_dp_unsharp_root s);

innermost_csr_lhs_blocked_check ::
  forall a b c.
    (Compare.Compare_order a, Eq a, Term_Rewriting.Showl a,
      Compare.Compare_order b, Eq b, Term_Rewriting.Showl b, Arith.Ccompare c,
      Compare.Compare_order c, Eq c,
      Mapping.Mapping_impl c) => [((Labelings.Lab a b, Arith.Nat),
                                    [Arith.Nat])] ->
                                   [(Term_Rewriting.Term (Labelings.Lab a b) c,
                                      Term_Rewriting.Term (Labelings.Lab a b)
c)] ->
                                     Term_Rewriting.Term (Labelings.Lab a b)
                                       c ->
                                       Bool;
innermost_csr_lhs_blocked_check mu r u =
  any (\ w -> any (\ (l, _) -> Term_Rewriting.matches w l) r)
    (csr_dp_root_supt_list mu u);

innermost_csr_dep_graph_edge_check ::
  forall a b c.
    (Compare.Compare_order a, Eq a, Term_Rewriting.Showl a,
      Compare.Compare_order b, Eq b, Term_Rewriting.Showl b, Arith.Ccompare c,
      Compare.Compare_order c, Eq c,
      Mapping.Mapping_impl c) => [((Labelings.Lab a b, Arith.Nat),
                                    [Arith.Nat])] ->
                                   [(Term_Rewriting.Term (Labelings.Lab a b) c,
                                      Term_Rewriting.Term (Labelings.Lab a b)
c)] ->
                                     (((Term_Rewriting.Term (Labelings.Lab a b)
  c,
 Term_Rewriting.Term (Labelings.Lab a b) c),
()),
                                       ((Term_Rewriting.Term (Labelings.Lab a b)
   c,
  Term_Rewriting.Term (Labelings.Lab a b) c),
 ())) ->
                                       Bool;
innermost_csr_dep_graph_edge_check mu r (((s, t), uu), ((u, v), uv)) =
  CSR_Checker_Base.csr_dep_graph_edge_check
    (CSR_Checker_Base.csr_dp_root_mu (Context_Sensitive_Impl.mu_of mu)) r
    (((s, t), ()), ((u, v), ())) &&
    not (innermost_csr_lhs_blocked_check mu r u);

check_innermost_csr_dep_graph_proc ::
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
check_innermost_csr_dep_graph_proc j mu dpp dps =
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
                   ((Term_Rewriting.showsl_lit
                       "innermost CSR dependency pair " .
                      Term_Rewriting.showsl_rule x) .
                     Term_Rewriting.showsl_lit
                       " is missing in decomposition\n")))
             (\ _ ->
               Error_Monad.catch_error
                 (Graph.check_graph_decomp (Term_Rewriting.showsl_prod . fst)
                   (Multi_Map.empty ((Term_Rewriting.root . fst) . fst))
                   CSR_Checker_Base.graph_approx_csr_rt Multi_Map.insert
                   (innermost_csr_dep_graph_edge_check mu r)
                   (map (\ (real, cs) ->
                          (not (Arith.is_none real),
                            map (\ (s, t) -> ((s, t), ())) cs))
                     dps))
                 (\ x ->
                   Sum_Type.Inl
                     (Term_Rewriting.showsl_lit
                        "invalid innermost CSR dependency-graph decomposition:\n" .
                       x))));

check_innermost_csr_dp_graph_components ::
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
check_innermost_csr_dp_graph_components ia j mu i dpp [] = Sum_Type.Inr ();
check_innermost_csr_dp_graph_components ia j mu i dpp ((Nothing, p) : rest) =
  check_innermost_csr_dp_graph_components ia j mu
    (Term_Rewriting.add_index i Arith.one_nat) dpp rest;
check_innermost_csr_dp_graph_components ia j mu i dpp ((Just prf, p) : rest) =
  Error_Monad.bind
    (check_innermost_csr_dp_termination_proof ia j mu
      (Term_Rewriting.add_index i Arith.one_nat)
      (Dependency_Pair_Problem_Spec.intersect_pairs j dpp p) prf)
    (\ _ ->
      check_innermost_csr_dp_graph_components ia j mu
        (Term_Rewriting.add_index i Arith.one_nat) dpp rest);

check_innermost_csr_dp_termination_proof ::
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
check_innermost_csr_dp_termination_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Dep_Graph_Proc edps) =
  FOR_Preliminaries.debug i "innermost CSR-DP dependency graph"
    (Error_Monad.bind (check_innermost_csr_dep_graph_proc j mu dpp edps)
      (\ _ -> check_innermost_csr_dp_graph_components ia j mu i dpp edps));
check_innermost_csr_dp_termination_proof ia j mu i dpp
  CSR_Checker_Base.CSR_DP_P_is_Empty =
  CSR_Checker.check_csr_dp_termination_proof_core ia j mu False i dpp
    CSR_Checker_Base.CSR_DP_P_is_Empty;
check_innermost_csr_dp_termination_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof v) =
  CSR_Checker.check_csr_dp_termination_proof_core ia j mu False i dpp
    (CSR_Checker_Base.CSR_DP_Ordinary_Proof v);
check_innermost_csr_dp_termination_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Subterm_Criterion_Proc v va vb vc) =
  CSR_Checker.check_csr_dp_termination_proof_core ia j mu False i dpp
    (CSR_Checker_Base.CSR_DP_Subterm_Criterion_Proc v va vb vc);
check_innermost_csr_dp_termination_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Gen_Subterm_Criterion_Proc v va vb) =
  CSR_Checker.check_csr_dp_termination_proof_core ia j mu False i dpp
    (CSR_Checker_Base.CSR_DP_Gen_Subterm_Criterion_Proc v va vb);
check_innermost_csr_dp_termination_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Usable_Rules_Proc v va) =
  CSR_Checker.check_csr_dp_termination_proof_core ia j mu False i dpp
    (CSR_Checker_Base.CSR_DP_Usable_Rules_Proc v va);
check_innermost_csr_dp_termination_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Instantiation_Proc v va vb) =
  CSR_Checker.check_csr_dp_termination_proof_core ia j mu False i dpp
    (CSR_Checker_Base.CSR_DP_Instantiation_Proc v va vb);
check_innermost_csr_dp_termination_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Forward_Instantiation_Proc v va vb) =
  CSR_Checker.check_csr_dp_termination_proof_core ia j mu False i dpp
    (CSR_Checker_Base.CSR_DP_Forward_Instantiation_Proc v va vb);
check_innermost_csr_dp_termination_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Redpair_UR_Proc v va vb vc) =
  CSR_Checker.check_csr_dp_termination_proof_core ia j mu False i dpp
    (CSR_Checker_Base.CSR_DP_Redpair_UR_Proc v va vb vc);
check_innermost_csr_dp_termination_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Size_Change_Subterm_Proc v) =
  CSR_Checker.check_csr_dp_termination_proof_core ia j mu False i dpp
    (CSR_Checker_Base.CSR_DP_Size_Change_Subterm_Proc v);

}
