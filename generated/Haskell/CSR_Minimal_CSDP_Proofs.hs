{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module CSR_Minimal_CSDP_Proofs(check_csr_termination_proof_min) where {

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
import qualified Check_Termination;
import qualified Subterm_Criterion_Impl;
import qualified FOR_Preliminaries;
import qualified Reduction_Pair_Implementations;
import qualified Termination_Problem_Spec;
import qualified Countable;
import qualified Mapping;
import qualified Size_Change_Termination_Processors;
import qualified Missing_List;
import qualified HOL;
import qualified Size_Change_Termination;
import qualified Product_Lexorder;
import qualified Compare_Order_Instances;
import qualified CSR_Checker;
import qualified Error_Monad;
import qualified Check_Monad;
import qualified Dependency_Pair_Problem_Spec;
import qualified Sum_Type;
import qualified Compare;
import qualified Context_Sensitive_Impl;
import qualified Arith;
import qualified Labelings;
import qualified Term_Rewriting;

csr_sct_sharp_term ::
  forall a b c. Term_Rewriting.Term (Labelings.Lab a b) c -> Bool;
csr_sct_sharp_term (Term_Rewriting.Fun (Labelings.Sharp f) ts) = True;
csr_sct_sharp_term (Term_Rewriting.Var v) = False;
csr_sct_sharp_term (Term_Rewriting.Fun (Labelings.Lab vb vc) va) = False;
csr_sct_sharp_term (Term_Rewriting.Fun (Labelings.FunLab vb vc) va) = False;
csr_sct_sharp_term (Term_Rewriting.Fun (Labelings.UnLab vb) va) = False;

qcs_ur_closed_term_check ::
  forall a b c d.
    (Eq a, Eq b,
      Eq c) => [(Term_Rewriting.Term a b, c)] ->
                 [(Term_Rewriting.Term a b, c)] ->
                   [((a, Arith.Nat), [Arith.Nat])] ->
                     Term_Rewriting.Term a d -> Bool;
qcs_ur_closed_term_check r u mu (Term_Rewriting.Var x) =
  all (Arith.membera u) r;
qcs_ur_closed_term_check r u mu (Term_Rewriting.Fun f ts) =
  all (\ lr ->
        not (Term_Rewriting.root (fst lr) == Just (f, Arith.size_list ts)) ||
          Arith.membera u lr)
    r &&
    all (\ (i, t) ->
          not (Arith.member i
                (Context_Sensitive_Impl.mu_of mu (f, Arith.size_list ts))) ||
            qcs_ur_closed_term_check r u mu t)
      (zip (Arith.upt Arith.zero_nat (Arith.size_list ts)) ts);

qcs_ur_closed_dp_rhs_check ::
  forall a b c d e.
    (Eq a, Eq b, Eq c,
      Eq d) => [(Term_Rewriting.Term (Labelings.Lab a b) c, d)] ->
                 [(Term_Rewriting.Term (Labelings.Lab a b) c, d)] ->
                   [((Labelings.Lab a b, Arith.Nat), [Arith.Nat])] ->
                     Term_Rewriting.Term (Labelings.Lab a b) e -> Bool;
qcs_ur_closed_dp_rhs_check r u mu (Term_Rewriting.Var x) = False;
qcs_ur_closed_dp_rhs_check r u mu (Term_Rewriting.Fun (Labelings.Sharp f) ts) =
  all (\ (i, t) ->
        not (Arith.member i
              (Context_Sensitive_Impl.mu_of mu (f, Arith.size_list ts))) ||
          qcs_ur_closed_term_check r u mu t)
    (zip (Arith.upt Arith.zero_nat (Arith.size_list ts)) ts);
qcs_ur_closed_dp_rhs_check r u mu (Term_Rewriting.Fun (Labelings.Lab v va) ts) =
  False;
qcs_ur_closed_dp_rhs_check r u mu
  (Term_Rewriting.Fun (Labelings.FunLab v va) ts) = False;
qcs_ur_closed_dp_rhs_check r u mu (Term_Rewriting.Fun (Labelings.UnLab v) ts) =
  False;

qcs_csr_ur_closed_check ::
  forall a b c d e f.
    (Eq a, Eq b, Eq c,
      Eq d) => [(Term_Rewriting.Term (Labelings.Lab a b) c,
                  Term_Rewriting.Term (Labelings.Lab a b) d)] ->
                 [(Term_Rewriting.Term (Labelings.Lab a b) c,
                    Term_Rewriting.Term (Labelings.Lab a b) d)] ->
                   [((Labelings.Lab a b, Arith.Nat), [Arith.Nat])] ->
                     [(e, Term_Rewriting.Term (Labelings.Lab a b) f)] -> Bool;
qcs_csr_ur_closed_check r u mu p =
  all (Arith.membera r) u &&
    all (\ lr -> qcs_ur_closed_term_check r u mu (snd lr)) u &&
      all (\ dp -> qcs_ur_closed_dp_rhs_check r u mu (snd dp)) p;

csr_qcs_usable_rules_proc ::
  forall a b c d.
    (Compare.Compare_order b, Eq b, Term_Rewriting.Showl b,
      Compare.Compare_order c, Eq c, Term_Rewriting.Showl c,
      Compare.Compare_order d, Eq d,
      Term_Rewriting.Showl d) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a
                                   (Labelings.Lab b c) d () ->
                                   [((Labelings.Lab b c, Arith.Nat),
                                      [Arith.Nat])] ->
                                     [(Term_Rewriting.Term (Labelings.Lab b c)
 d,
Term_Rewriting.Term (Labelings.Lab b c) d)] ->
                                       a -> Sum_Type.Sum (String -> String) a;
csr_qcs_usable_rules_proc j mu u dpp =
  (case Check_Monad.check
          (qcs_csr_ur_closed_check (Dependency_Pair_Problem_Spec.rules j dpp) u
            mu (Dependency_Pair_Problem_Spec.pairs j dpp))
          (Term_Rewriting.showsl_lit
            "error when checking QCS usable-rule closure")
    of {
    Sum_Type.Inl a -> Sum_Type.Inl a;
    Sum_Type.Inr _ ->
      Sum_Type.Inr (Dependency_Pair_Problem_Spec.intersect_rules j dpp u);
  });

csr_sct_active_index_check ::
  forall a b c.
    (Eq a,
      Eq b) => [((Labelings.Lab a b, Arith.Nat), [Arith.Nat])] ->
                 Term_Rewriting.Term (Labelings.Lab a b) c -> Arith.Nat -> Bool;
csr_sct_active_index_check mu (Term_Rewriting.Fun (Labelings.Sharp f) ts) i =
  Arith.less_nat Arith.zero_nat i &&
    Arith.less_eq_nat i (Arith.size_list ts) &&
      Arith.member (Arith.minus_nat i Arith.one_nat)
        (Context_Sensitive_Impl.mu_of mu (f, Arith.size_list ts));
csr_sct_active_index_check mu (Term_Rewriting.Var v) i = False;
csr_sct_active_index_check mu (Term_Rewriting.Fun (Labelings.Lab vb vc) va) i =
  False;
csr_sct_active_index_check mu (Term_Rewriting.Fun (Labelings.FunLab vb vc) va) i
  = False;
csr_sct_active_index_check mu (Term_Rewriting.Fun (Labelings.UnLab vb) va) i =
  False;

csr_rules_sharp_fresh_check ::
  forall a b c.
    [(Term_Rewriting.Term (Labelings.Lab a b) c,
       Term_Rewriting.Term (Labelings.Lab a b) c)] ->
      Sum_Type.Sum (String -> String) ();
csr_rules_sharp_fresh_check r =
  Error_Monad.catch_error
    (Error_Monad.forallM
      (\ (f, _) ->
        Check_Monad.check (not (CSR_Checker.is_sharp_lab f))
          (Term_Rewriting.showsl_lit "source CSR defines a sharp symbol"))
      (Term_Rewriting.defined_list r))
    (\ x -> Sum_Type.Inl (snd x));

csr_sct_active_subterm_proc ::
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
csr_sct_active_subterm_proc j mu gs dpp =
  let {
    p = Dependency_Pair_Problem_Spec.pairs j dpp;
    r = Dependency_Pair_Problem_Spec.rules j dpp;
  } in Error_Monad.bind
         (Error_Monad.catch_error (Check_Monad.check_subseteq p (map fst gs))
           (\ x ->
             Sum_Type.Inl
               (Term_Rewriting.showsl_lit
                  "there is no CSR size-change graph for pair " .
                 Term_Rewriting.showsl_rule x)))
         (\ _ ->
           let {
             gGs = filter (\ g -> Arith.membera p (fst g)) gs;
           } in Error_Monad.bind
                  (Error_Monad.catch_error
                    (Error_Monad.forallM
                      (\ (a, b) ->
                        (case a of {
                          (s, t) ->
                            (\ (stri, nstri) ->
                              Error_Monad.bind
                                (Check_Monad.check
                                  (csr_sct_sharp_term s && csr_sct_sharp_term t)
                                  (Term_Rewriting.showsl_lit
                                    "CSR size-change pair is not sharp-rooted"))
                                (\ _ ->
                                  Error_Monad.bind
                                    (Error_Monad.catch_error
                                      (Error_Monad.forallM
(\ (i, ja) ->
  Check_Monad.check
    (csr_sct_active_index_check mu s i &&
      csr_sct_active_index_check mu t ja &&
        Arith.membera
          (CSR_Checker.mu_supt_list mu
            (Size_Change_Termination_Processors.get_arg s i))
          (Size_Change_Termination_Processors.get_arg t ja))
    (Term_Rewriting.showsl_lit "invalid strict active CSR size-change edge"))
stri)
                                      (\ x -> Sum_Type.Inl (snd x)))
                                    (\ _ ->
                                      Error_Monad.catch_error
(Error_Monad.forallM
  (\ (i, ja) ->
    Check_Monad.check
      (csr_sct_active_index_check mu s i &&
        csr_sct_active_index_check mu t ja &&
          (Term_Rewriting.equal_term
             (Size_Change_Termination_Processors.get_arg s i)
             (Size_Change_Termination_Processors.get_arg t ja) ||
            Arith.membera
              (CSR_Checker.mu_supt_list mu
                (Size_Change_Termination_Processors.get_arg s i))
              (Size_Change_Termination_Processors.get_arg t ja)))
      (Term_Rewriting.showsl_lit
        "invalid non-strict active CSR size-change edge"))
  nstri)
(\ x -> Sum_Type.Inl (snd x)))));
                        })
                          b)
                      gGs)
                    (\ x -> Sum_Type.Inl (snd x)))
                  (\ _ ->
                    let {
                      conn =
                        (\ st uv ->
                          CSR_Checker.csr_dep_graph_edge_check
                            (CSR_Checker.csr_dp_root_mu
                              (Context_Sensitive_Impl.mu_of mu))
                            r ((st, ()), (uv, ())));
                    } in Check_Monad.check
                           (Size_Change_Termination.check_SCT conn
                             (map (\ (st, (stri, nstri)) ->
                                    Size_Change_Termination.Scg st st
                                      (Missing_List.remdups_sort stri)
                                      (Missing_List.remdups_sort nstri))
                               gGs))
                           (Term_Rewriting.showsl_lit
                             "active CSR size-change analysis failed")));

check_csr_dp_termination_proof_min ::
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
   c -> CSR_Checker.Csr_dp_termination_proof b [Arith.Nat] [Arith.Char] ->
          Sum_Type.Sum (String -> String) ();
check_csr_dp_termination_proof_min ia j mu a i dpp CSR_Checker.CSR_DP_P_is_Empty
  = CSR_Checker.check_csr_dp_termination_proof_core ia j mu a i dpp
      CSR_Checker.CSR_DP_P_is_Empty;
check_csr_dp_termination_proof_min ia j mu a i dpp
  (CSR_Checker.CSR_DP_Ordinary_Proof prf) =
  CSR_Checker.check_csr_dp_termination_proof_core ia j mu a i dpp
    (CSR_Checker.CSR_DP_Ordinary_Proof prf);
check_csr_dp_termination_proof_min ia j mu a i dpp
  (CSR_Checker.CSR_DP_Subterm_Criterion_Proc p rseq pr prf) =
  CSR_Checker.check_csr_dp_termination_proof_core ia j mu a i dpp
    (CSR_Checker.CSR_DP_Subterm_Criterion_Proc p rseq pr prf);
check_csr_dp_termination_proof_min ia j mu a i dpp
  (CSR_Checker.CSR_DP_Gen_Subterm_Criterion_Proc p pr prf) =
  CSR_Checker.check_csr_dp_termination_proof_core ia j mu a i dpp
    (CSR_Checker.CSR_DP_Gen_Subterm_Criterion_Proc p pr prf);
check_csr_dp_termination_proof_min ia j mu a i dpp
  (CSR_Checker.CSR_DP_Usable_Rules_Proc u prf) =
  FOR_Preliminaries.debug i "QCS usable rules"
    (Error_Monad.bind
      (Error_Monad.catch_error (csr_qcs_usable_rules_proc j mu u dpp)
        (\ x ->
          Sum_Type.Inl
            ((i . Term_Rewriting.showsl_lit
                    ": error when applying QCS usable rules\n") .
              x)))
      (\ dppa ->
        Error_Monad.catch_error
          (check_csr_dp_termination_proof_min ia j mu a
            (Term_Rewriting.add_index i Arith.one_nat) dppa prf)
          (\ x ->
            Sum_Type.Inl
              ((i . Term_Rewriting.showsl_lit
                      ": error below QCS usable rules\n") .
                x))));
check_csr_dp_termination_proof_min ia j mu a i dpp
  (CSR_Checker.CSR_DP_Dep_Graph_Proc edpts) =
  CSR_Checker.check_csr_dp_termination_proof_core ia j mu a i dpp
    (CSR_Checker.CSR_DP_Dep_Graph_Proc edpts);
check_csr_dp_termination_proof_min ia j mu a i dpp
  (CSR_Checker.CSR_DP_Size_Change_Subterm_Proc graphs) =
  (if Error_Monad.isOK (csr_sct_active_subterm_proc j mu graphs dpp)
    then FOR_Preliminaries.debug i "active CSR size-change" (Sum_Type.Inr ())
    else CSR_Checker.check_csr_dp_termination_proof_core ia j mu a i dpp
           (CSR_Checker.CSR_DP_Size_Change_Subterm_Proc graphs));

check_csr_termination_proof_min ::
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
     CSR_Checker.Csr_termination_proof b [Arith.Nat] [Arith.Char] ->
       Sum_Type.Sum (String -> String) ();
check_csr_termination_proof_min ia j a i mu r CSR_Checker.CSR_R_is_Empty =
  CSR_Checker.check_csr_termination_proof ia j a i mu r
    CSR_Checker.CSR_R_is_Empty;
check_csr_termination_proof_min ia j a i mu r
  (CSR_Checker.CSR_Rule_Removal redp rr prf) =
  FOR_Preliminaries.debug i "CSR rule removal"
    (case CSR_Checker.csr_rule_removal_impl redp mu rr r of {
      Sum_Type.Inl aa -> Sum_Type.Inl aa;
      Sum_Type.Inr r2 -> check_csr_termination_proof_min ia j a i mu r2 prf;
    });
check_csr_termination_proof_min ia j a i mu r
  (CSR_Checker.CSR_Dependency_Pairs p prf) =
  FOR_Preliminaries.debug i "minimal CSR dependency pairs"
    (Error_Monad.bind
      (Error_Monad.catch_error (CSR_Checker.csr_sharp_mu_check mu)
        (\ x ->
          Sum_Type.Inl
            ((i . Term_Rewriting.showsl_lit
                    ": invalid replacement map for CSR dependency pairs\n") .
              x)))
      (\ _ ->
        Error_Monad.bind
          (Error_Monad.catch_error (csr_rules_sharp_fresh_check r)
            (\ x ->
              Sum_Type.Inl
                ((i . Term_Rewriting.showsl_lit
                        ": invalid sharp symbol in source CSR\n") .
                  x)))
          (\ _ ->
            (case CSR_Checker.mu_csr_dependency_pairs_tt Labelings.Sharp j mu r
                    p
              of {
              Sum_Type.Inl _ ->
                Error_Monad.bind
                  (Error_Monad.catch_error
                    (CSR_Checker.safe_csr_dependency_pairs_tt Labelings.Sharp j
                      mu r p)
                    (\ x ->
                      Sum_Type.Inl
                        ((i . Term_Rewriting.showsl_lit
                                ": error when switching from CSR to a safe CS-DP problem\n") .
                          x)))
                  (\ dpp ->
                    Error_Monad.catch_error
                      (CSR_Checker.check_csr_dp_termination_proof ia j False
                        (Term_Rewriting.add_index i Arith.one_nat) dpp prf)
                      (\ x ->
                        Sum_Type.Inl
                          ((i . Term_Rewriting.showsl_lit
                                  ": error below safe CSR dependency pairs\n") .
                            x)));
              Sum_Type.Inr dpp ->
                Error_Monad.catch_error
                  (check_csr_dp_termination_proof_min ia j mu False
                    (Term_Rewriting.add_index i Arith.one_nat) dpp prf)
                  (\ x ->
                    Sum_Type.Inl
                      ((i . Term_Rewriting.showsl_lit
                              ": error below replacement-map-specific CSR dependency pairs\n") .
                        x));
            }))));
check_csr_termination_proof_min ia j a i mu r
  (CSR_Checker.CSR_Safe_Dependency_Pairs p prf) =
  CSR_Checker.check_csr_termination_proof ia j a i mu r
    (CSR_Checker.CSR_Safe_Dependency_Pairs p prf);

}
