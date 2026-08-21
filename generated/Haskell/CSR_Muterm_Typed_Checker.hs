{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  CSR_Muterm_Typed_Checker(muterm_recursive_target_shape_check_exec,
                            muterm_recursive_bridges_safe_check_exec,
                            muterm_recursive_pairs_safe_check_exec,
                            check_muterm_i4_root_proof)
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
import qualified CSR_Muterm_Extended_Basic;
import qualified CSR_Checker;
import qualified CSR_Muterm_Typed_General_Redpair;
import qualified RenamingN_String;
import qualified RenamingN;
import qualified Lists_are_Infinite;
import qualified Phantom_Type;
import qualified CSR_Minimal_CSDP_Proofs;
import qualified Context_Sensitive_Impl;
import qualified FOR_Preliminaries;
import qualified Complex_Constant_Removal_Impl;
import qualified Check_Termination_Common;
import qualified Bounded_Increase_Impl;
import qualified Semantic_Labeling_Carrier;
import qualified Critical_Pairs_Impl;
import qualified Subterm_Criterion_Impl;
import qualified Check_Monad;
import qualified HOL;
import qualified Mapping;
import qualified Error_Monad;
import qualified Dependency_Pair_Problem_Spec;
import qualified Reduction_Pair_Implementations;
import qualified CSR_Muterm_Usable_Rules;
import qualified Termination_Problem_Spec;
import qualified Check_Termination;
import qualified Sum_Type;
import qualified Countable;
import qualified Compare;
import qualified Compare_Order_Instances;
import qualified Term_Rewriting;
import qualified Set_Interval;
import qualified CSR_Checker_Base;
import qualified Labelings;
import qualified Arith;

muterm_i4_mu_exec ::
  forall a b c.
    (Arith.Ceq c, Arith.Ccompare c, Eq c, Arith.Interval c,
      Arith.Set_impl c) => ((Labelings.Lab a b, c) -> Arith.Set c) ->
                             (Labelings.Lab a b, c) -> Arith.Set c;
muterm_i4_mu_exec mu fn =
  (if CSR_Checker_Base.is_sharp_lab (fst fn)
    then Set_Interval.atLeastLessThan Arith.zero (snd fn) else mu fn);

muterm_i4_mu_vars_term_list_exec ::
  forall a b c.
    ((Labelings.Lab a b, Arith.Nat) -> Arith.Set Arith.Nat) ->
      Term_Rewriting.Term (Labelings.Lab a b) c -> [c];
muterm_i4_mu_vars_term_list_exec mu (Term_Rewriting.Var x) = [x];
muterm_i4_mu_vars_term_list_exec mu (Term_Rewriting.Fun f ts) =
  concat
    (Arith.map_filter
      (\ x ->
        (if CSR_Checker_Base.is_sharp_lab f ||
              Arith.member x (mu (f, Arith.size_list ts))
          then Just (muterm_i4_mu_vars_term_list_exec mu (Arith.nth ts x))
          else Nothing))
      (Arith.upt Arith.zero_nat (Arith.size_list ts)));

muterm_i4_full_check_exec ::
  forall a b c.
    (Eq c) => ((Labelings.Lab a b, Arith.Nat) -> Arith.Set Arith.Nat) ->
                Term_Rewriting.Term (Labelings.Lab a b) c -> Bool;
muterm_i4_full_check_exec mu t =
  all (Arith.membera (muterm_i4_mu_vars_term_list_exec mu t))
    (Term_Rewriting.vars_term_list t);

check_muterm_expanded_extended_basic_proof ::
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
check_muterm_expanded_extended_basic_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Dep_Graph_Proc edpts) =
  FOR_Preliminaries.debug i "expanded extended-basic MU-TERM dependency graph"
    (Error_Monad.bind (CSR_Checker.check_csr_dep_graph_proc j mu dpp edpts)
      (\ _ ->
        check_muterm_expanded_extended_basic_components ia j mu i dpp edpts));
check_muterm_expanded_extended_basic_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Redpair_UR_Proc redp pr u subprf))
  = FOR_Preliminaries.debug i "expanded extended-basic MU-TERM reduction pair"
      (Error_Monad.bind
        (CSR_Muterm_Extended_Basic.muterm_extended_basic_redpair_proc j mu
          (Reduction_Pair_Implementations.get_rel_impl redp) pr u dpp)
        (\ dppa ->
          CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu
            False (Term_Rewriting.add_index i Arith.one_nat) dppa
            (CSR_Checker_Base.CSR_DP_Ordinary_Proof subprf)));
check_muterm_expanded_extended_basic_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Instantiation_Proc st sts prf) =
  FOR_Preliminaries.debug i "expanded extended-basic MU-TERM instantiation"
    (Error_Monad.bind
      (CSR_Minimal_CSDP_Proofs.csr_instantiation_proc j mu st sts dpp)
      (\ dppa ->
        check_muterm_expanded_extended_basic_proof ia j mu
          (Term_Rewriting.add_index i Arith.one_nat) dppa prf));
check_muterm_expanded_extended_basic_proof ia j mu i dpp
  CSR_Checker_Base.CSR_DP_P_is_Empty =
  CSR_Muterm_Usable_Rules.check_muterm_expanded_csr_proof ia j mu i dpp
    CSR_Checker_Base.CSR_DP_P_is_Empty;
check_muterm_expanded_extended_basic_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof Check_Termination.P_is_Empty) =
  CSR_Muterm_Usable_Rules.check_muterm_expanded_csr_proof ia j mu i dpp
    (CSR_Checker_Base.CSR_DP_Ordinary_Proof Check_Termination.P_is_Empty);
check_muterm_expanded_extended_basic_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Subterm_Criterion_Proc va vb vc vd))
  = CSR_Muterm_Usable_Rules.check_muterm_expanded_csr_proof ia j mu i dpp
      (CSR_Checker_Base.CSR_DP_Ordinary_Proof
        (Check_Termination.Subterm_Criterion_Proc va vb vc vd));
check_muterm_expanded_extended_basic_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Gen_Subterm_Criterion_Proc va vb vc))
  = CSR_Muterm_Usable_Rules.check_muterm_expanded_csr_proof ia j mu i dpp
      (CSR_Checker_Base.CSR_DP_Ordinary_Proof
        (Check_Termination.Gen_Subterm_Criterion_Proc va vb vc));
check_muterm_expanded_extended_basic_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Redpair_Proc va vb vc))
  = CSR_Muterm_Usable_Rules.check_muterm_expanded_csr_proof ia j mu i dpp
      (CSR_Checker_Base.CSR_DP_Ordinary_Proof
        (Check_Termination.Redpair_Proc va vb vc));
check_muterm_expanded_extended_basic_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Usable_Rules_Proc va vb))
  = CSR_Muterm_Usable_Rules.check_muterm_expanded_csr_proof ia j mu i dpp
      (CSR_Checker_Base.CSR_DP_Ordinary_Proof
        (Check_Termination.Usable_Rules_Proc va vb));
check_muterm_expanded_extended_basic_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof (Check_Termination.Dep_Graph_Proc va))
  = CSR_Muterm_Usable_Rules.check_muterm_expanded_csr_proof ia j mu i dpp
      (CSR_Checker_Base.CSR_DP_Ordinary_Proof
        (Check_Termination.Dep_Graph_Proc va));
check_muterm_expanded_extended_basic_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Mono_Redpair_Proc va vb vc vd))
  = CSR_Muterm_Usable_Rules.check_muterm_expanded_csr_proof ia j mu i dpp
      (CSR_Checker_Base.CSR_DP_Ordinary_Proof
        (Check_Termination.Mono_Redpair_Proc va vb vc vd));
check_muterm_expanded_extended_basic_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Mono_URM_Redpair_Proc va vb vc vd))
  = CSR_Muterm_Usable_Rules.check_muterm_expanded_csr_proof ia j mu i dpp
      (CSR_Checker_Base.CSR_DP_Ordinary_Proof
        (Check_Termination.Mono_URM_Redpair_Proc va vb vc vd));
check_muterm_expanded_extended_basic_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Mono_Redpair_UR_Proc va vb vc vd ve))
  = CSR_Muterm_Usable_Rules.check_muterm_expanded_csr_proof ia j mu i dpp
      (CSR_Checker_Base.CSR_DP_Ordinary_Proof
        (Check_Termination.Mono_Redpair_UR_Proc va vb vc vd ve));
check_muterm_expanded_extended_basic_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Size_Change_Subterm_Proc va))
  = CSR_Muterm_Usable_Rules.check_muterm_expanded_csr_proof ia j mu i dpp
      (CSR_Checker_Base.CSR_DP_Ordinary_Proof
        (Check_Termination.Size_Change_Subterm_Proc va));
check_muterm_expanded_extended_basic_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Size_Change_Redpair_Proc va vb vc))
  = CSR_Muterm_Usable_Rules.check_muterm_expanded_csr_proof ia j mu i dpp
      (CSR_Checker_Base.CSR_DP_Ordinary_Proof
        (Check_Termination.Size_Change_Redpair_Proc va vb vc));
check_muterm_expanded_extended_basic_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Uncurry_Proc va vb vc vd ve))
  = CSR_Muterm_Usable_Rules.check_muterm_expanded_csr_proof ia j mu i dpp
      (CSR_Checker_Base.CSR_DP_Ordinary_Proof
        (Check_Termination.Uncurry_Proc va vb vc vd ve));
check_muterm_expanded_extended_basic_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Fcc_Proc va vb vc vd ve))
  = CSR_Muterm_Usable_Rules.check_muterm_expanded_csr_proof ia j mu i dpp
      (CSR_Checker_Base.CSR_DP_Ordinary_Proof
        (Check_Termination.Fcc_Proc va vb vc vd ve));
check_muterm_expanded_extended_basic_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Split_Proc va vb vc vd))
  = CSR_Muterm_Usable_Rules.check_muterm_expanded_csr_proof ia j mu i dpp
      (CSR_Checker_Base.CSR_DP_Ordinary_Proof
        (Check_Termination.Split_Proc va vb vc vd));
check_muterm_expanded_extended_basic_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Semlab_Proc va vb vc vd ve))
  = CSR_Muterm_Usable_Rules.check_muterm_expanded_csr_proof ia j mu i dpp
      (CSR_Checker_Base.CSR_DP_Ordinary_Proof
        (Check_Termination.Semlab_Proc va vb vc vd ve));
check_muterm_expanded_extended_basic_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Switch_Innermost_Proc va vb))
  = CSR_Muterm_Usable_Rules.check_muterm_expanded_csr_proof ia j mu i dpp
      (CSR_Checker_Base.CSR_DP_Ordinary_Proof
        (Check_Termination.Switch_Innermost_Proc va vb));
check_muterm_expanded_extended_basic_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Rewriting_Proc va vb vc vd ve vf vg))
  = CSR_Muterm_Usable_Rules.check_muterm_expanded_csr_proof ia j mu i dpp
      (CSR_Checker_Base.CSR_DP_Ordinary_Proof
        (Check_Termination.Rewriting_Proc va vb vc vd ve vf vg));
check_muterm_expanded_extended_basic_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Instantiation_Proc va vb vc))
  = CSR_Muterm_Usable_Rules.check_muterm_expanded_csr_proof ia j mu i dpp
      (CSR_Checker_Base.CSR_DP_Ordinary_Proof
        (Check_Termination.Instantiation_Proc va vb vc));
check_muterm_expanded_extended_basic_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Forward_Instantiation_Proc va vb vc vd))
  = CSR_Muterm_Usable_Rules.check_muterm_expanded_csr_proof ia j mu i dpp
      (CSR_Checker_Base.CSR_DP_Ordinary_Proof
        (Check_Termination.Forward_Instantiation_Proc va vb vc vd));
check_muterm_expanded_extended_basic_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Narrowing_Proc va vb vc vd))
  = CSR_Muterm_Usable_Rules.check_muterm_expanded_csr_proof ia j mu i dpp
      (CSR_Checker_Base.CSR_DP_Ordinary_Proof
        (Check_Termination.Narrowing_Proc va vb vc vd));
check_muterm_expanded_extended_basic_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Assume_Finite va vb))
  = CSR_Muterm_Usable_Rules.check_muterm_expanded_csr_proof ia j mu i dpp
      (CSR_Checker_Base.CSR_DP_Ordinary_Proof
        (Check_Termination.Assume_Finite va vb));
check_muterm_expanded_extended_basic_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Q_Reduction_Proc va vb))
  = CSR_Muterm_Usable_Rules.check_muterm_expanded_csr_proof ia j mu i dpp
      (CSR_Checker_Base.CSR_DP_Ordinary_Proof
        (Check_Termination.Q_Reduction_Proc va vb));
check_muterm_expanded_extended_basic_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Complex_Constant_Removal_Proc va vb))
  = CSR_Muterm_Usable_Rules.check_muterm_expanded_csr_proof ia j mu i dpp
      (CSR_Checker_Base.CSR_DP_Ordinary_Proof
        (Check_Termination.Complex_Constant_Removal_Proc va vb));
check_muterm_expanded_extended_basic_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.General_Redpair_Proc va vb vc vd ve))
  = CSR_Muterm_Usable_Rules.check_muterm_expanded_csr_proof ia j mu i dpp
      (CSR_Checker_Base.CSR_DP_Ordinary_Proof
        (Check_Termination.General_Redpair_Proc va vb vc vd ve));
check_muterm_expanded_extended_basic_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof (Check_Termination.To_Trs_Proc va)) =
  CSR_Muterm_Usable_Rules.check_muterm_expanded_csr_proof ia j mu i dpp
    (CSR_Checker_Base.CSR_DP_Ordinary_Proof (Check_Termination.To_Trs_Proc va));
check_muterm_expanded_extended_basic_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Subterm_Criterion_Proc v va vb vc) =
  CSR_Muterm_Usable_Rules.check_muterm_expanded_csr_proof ia j mu i dpp
    (CSR_Checker_Base.CSR_DP_Subterm_Criterion_Proc v va vb vc);
check_muterm_expanded_extended_basic_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Gen_Subterm_Criterion_Proc v va vb) =
  CSR_Muterm_Usable_Rules.check_muterm_expanded_csr_proof ia j mu i dpp
    (CSR_Checker_Base.CSR_DP_Gen_Subterm_Criterion_Proc v va vb);
check_muterm_expanded_extended_basic_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Usable_Rules_Proc v va) =
  CSR_Muterm_Usable_Rules.check_muterm_expanded_csr_proof ia j mu i dpp
    (CSR_Checker_Base.CSR_DP_Usable_Rules_Proc v va);
check_muterm_expanded_extended_basic_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Forward_Instantiation_Proc v va vb) =
  CSR_Muterm_Usable_Rules.check_muterm_expanded_csr_proof ia j mu i dpp
    (CSR_Checker_Base.CSR_DP_Forward_Instantiation_Proc v va vb);
check_muterm_expanded_extended_basic_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Redpair_UR_Proc v va vb vc) =
  CSR_Muterm_Usable_Rules.check_muterm_expanded_csr_proof ia j mu i dpp
    (CSR_Checker_Base.CSR_DP_Redpair_UR_Proc v va vb vc);
check_muterm_expanded_extended_basic_proof ia j mu i dpp
  (CSR_Checker_Base.CSR_DP_Size_Change_Subterm_Proc v) =
  CSR_Muterm_Usable_Rules.check_muterm_expanded_csr_proof ia j mu i dpp
    (CSR_Checker_Base.CSR_DP_Size_Change_Subterm_Proc v);

check_muterm_expanded_extended_basic_components ::
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
check_muterm_expanded_extended_basic_components ia j mu i dpp [] =
  Sum_Type.Inr ();
check_muterm_expanded_extended_basic_components ia j mu i dpp
  ((Nothing, c) : rest) =
  check_muterm_expanded_extended_basic_components ia j mu
    (Term_Rewriting.add_index i Arith.one_nat) dpp rest;
check_muterm_expanded_extended_basic_components ia j mu i dpp
  ((Just prf, c) : rest) =
  Error_Monad.bind
    (check_muterm_expanded_extended_basic_proof ia j mu
      (Term_Rewriting.add_index i Arith.one_nat)
      (Dependency_Pair_Problem_Spec.intersect_pairs j dpp c) prf)
    (\ _ ->
      check_muterm_expanded_extended_basic_components ia j mu
        (Term_Rewriting.add_index i Arith.one_nat) dpp rest);

check_muterm_typed_dp_proof_production ::
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
 [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
    Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
   [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
      Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
     [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
        Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
       CSR_Muterm_Usable_Rules.Muterm_typed_dp_proof b [Arith.Nat]
         [Arith.Char] ->
         Sum_Type.Sum (String -> String) ();
check_muterm_typed_dp_proof_production ia j mu i r s p
  CSR_Muterm_Usable_Rules.Muterm_Typed_P_Is_Empty =
  Check_Monad.check (null p)
    (i . Term_Rewriting.showsl_lit
           ": innermost typed MU-TERM pairs are not empty");
check_muterm_typed_dp_proof_production ia j mu i r s p
  (CSR_Muterm_Usable_Rules.Muterm_Typed_Expanded_Extended_Basic_CSR_Proof child)
  = FOR_Preliminaries.debug i
      "expanded typed extended-basic MU-TERM CSR component"
      (let {
         e = CSR_Muterm_Usable_Rules.muterm_expanded_pairs_list
               RenamingN_String.string_renameN p s;
         dpp = Dependency_Pair_Problem_Spec.mk j False False e [] [] [] r;
       } in check_muterm_expanded_extended_basic_proof ia j mu
              (Term_Rewriting.add_index i Arith.one_nat) dpp child);
check_muterm_typed_dp_proof_production ia j mu i r s p
  (CSR_Muterm_Usable_Rules.Muterm_Typed_General_Usable redp pr u child) =
  FOR_Preliminaries.debug i
    "innermost typed RTA\'08 MU-TERM usable-rule reduction pair"
    (let {
       dpp = Dependency_Pair_Problem_Spec.mk j False False p [] [] [] r;
     } in Error_Monad.bind
            (CSR_Muterm_Typed_General_Redpair.muterm_general_rta08_ur_redpair_proc
              j mu (Reduction_Pair_Implementations.get_rel_impl redp) pr u s
              dpp)
            (\ dppa ->
              check_muterm_typed_dp_proof_production ia j mu
                (Term_Rewriting.add_index i Arith.one_nat) r s
                (Dependency_Pair_Problem_Spec.pairs j dppa) child));
check_muterm_typed_dp_proof_production ia j mu i r s p
  (CSR_Muterm_Usable_Rules.Muterm_Typed_Pair_Augmentation st sts child) =
  FOR_Preliminaries.debug i "innermost typed MU-TERM pair augmentation"
    (let {
       dpp = Dependency_Pair_Problem_Spec.mk j False False p [] [] [] r;
     } in Error_Monad.bind
            (CSR_Minimal_CSDP_Proofs.csr_instantiation_proc j mu st sts dpp)
            (\ dppa ->
              Error_Monad.bind
                (Error_Monad.catch_error
                  (Check_Monad.check_subseteq p
                    (Dependency_Pair_Problem_Spec.pairs j dppa))
                  (\ _ ->
                    Sum_Type.Inl
                      (Term_Rewriting.showsl_lit
                        "typed MU-TERM augmentation removed an original pair")))
                (\ _ ->
                  check_muterm_typed_dp_proof_production ia j mu
                    (Term_Rewriting.add_index i Arith.one_nat) r s
                    (Dependency_Pair_Problem_Spec.pairs j dppa) child)));
check_muterm_typed_dp_proof_production ia j mu i r s p
  (CSR_Muterm_Usable_Rules.Muterm_Typed_CSR_Proof child) =
  FOR_Preliminaries.debug i
    "innermost typed MU-TERM noncollapsing CSR component"
    (Error_Monad.bind
      (Check_Monad.check (all ((\ t -> not (Term_Rewriting.is_Var t)) . snd) p)
        (i . Term_Rewriting.showsl_lit
               ": collapsing pair requires the typed MU-TERM processor"))
      (\ _ ->
        let {
          dpp = Dependency_Pair_Problem_Spec.mk j False False p [] [] [] r;
        } in CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu
               False (Term_Rewriting.add_index i Arith.one_nat) dpp child));
check_muterm_typed_dp_proof_production ia j mu i r s p
  (CSR_Muterm_Usable_Rules.Muterm_Typed_Local_Usable u child) =
  Sum_Type.Inl
    (i . Term_Rewriting.showsl_lit
           ": recursive local usable rules require the invariant graph checker");
check_muterm_typed_dp_proof_production ia j mu i r s p
  (CSR_Muterm_Usable_Rules.Muterm_Typed_Expanded_CSR_Proof child) =
  FOR_Preliminaries.debug i "expanded typed MU-TERM CSR component"
    (let {
       e = CSR_Muterm_Usable_Rules.muterm_expanded_pairs_list
             RenamingN_String.string_renameN p s;
       dpp = Dependency_Pair_Problem_Spec.mk j False False e [] [] [] r;
     } in CSR_Muterm_Usable_Rules.check_muterm_expanded_csr_proof ia j mu
            (Term_Rewriting.add_index i Arith.one_nat) dpp child);
check_muterm_typed_dp_proof_production ia j mu i r s p
  (CSR_Muterm_Usable_Rules.Muterm_Typed_Expanded_Local_Usable u child) =
  FOR_Preliminaries.debug i
    "expanded innermost typed MU-TERM local usable rules"
    (Error_Monad.bind
      (Check_Monad.check (all (Arith.membera r) u)
        (i . Term_Rewriting.showsl_lit ": extraneous MU-TERM usable rule"))
      (\ _ ->
        Error_Monad.bind
          (Check_Monad.check
            (all (\ lr ->
                   CSR_Minimal_CSDP_Proofs.qcs_ur_closed_term_check r u mu
                     (snd lr))
              u)
            (i . Term_Rewriting.showsl_lit
                   ": ordinary MU-TERM rule closure failed"))
          (\ _ ->
            Error_Monad.bind
              (Check_Monad.check
                (all (\ lr ->
                       CSR_Minimal_CSDP_Proofs.qcs_ur_closed_dp_rhs_check r u mu
                         (snd lr))
                  s)
                (i . Term_Rewriting.showsl_lit
                       ": MU-TERM unhiding closure failed"))
              (\ _ ->
                Error_Monad.bind
                  (Check_Monad.check
                    (all (\ dp ->
                           Term_Rewriting.is_Var (snd dp) ||
                             CSR_Minimal_CSDP_Proofs.qcs_ur_closed_dp_rhs_check
                               r u mu (snd dp))
                      p)
                    (i . Term_Rewriting.showsl_lit
                           ": MU-TERM pair closure failed"))
                  (\ _ ->
                    let {
                      e = CSR_Muterm_Usable_Rules.muterm_expanded_pairs_list
                            RenamingN_String.string_renameN p s;
                    } in Check_Termination.check_dp_termination_proof ia j False
                           (Term_Rewriting.add_index i Arith.one_nat)
                           (Dependency_Pair_Problem_Spec.mk j False False e []
                             [] [] u)
                           child)))));
check_muterm_typed_dp_proof_production ia j mu i r s p
  (CSR_Muterm_Usable_Rules.Muterm_Typed_Expanded_Ordinary child) =
  FOR_Preliminaries.debug i "expanded typed MU-TERM ordinary DP continuation"
    (let {
       e = CSR_Muterm_Usable_Rules.muterm_expanded_pairs_list
             RenamingN_String.string_renameN p s;
     } in Check_Termination.check_dp_termination_proof ia j False
            (Term_Rewriting.add_index i Arith.one_nat)
            (Dependency_Pair_Problem_Spec.mk j False False e [] [] [] r) child);
check_muterm_typed_dp_proof_production ia j mu i r s p
  (CSR_Muterm_Usable_Rules.Muterm_Typed_Dep_Graph edps) =
  FOR_Preliminaries.debug i "innermost typed MU-TERM dependency graph"
    (Error_Monad.bind
      (CSR_Muterm_Usable_Rules.check_muterm_typed_dep_graph mu r s p edps)
      (\ _ ->
        check_muterm_innermost_typed_graph_components ia j mu i r s p edps));
check_muterm_typed_dp_proof_production ia j mu i r s p
  (CSR_Muterm_Usable_Rules.Muterm_Typed_Expanded_Strong_Usable v va vb vc) =
  Sum_Type.Inl
    (i . Term_Rewriting.showsl_lit
           ": processor is not supported inside an innermost typed MU-TERM chain");

check_muterm_innermost_typed_graph_components ::
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
 [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
    Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
   [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
      Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
     [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
        Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
       [(Maybe (CSR_Muterm_Usable_Rules.Muterm_typed_dp_proof b [Arith.Nat]
                 [Arith.Char]),
          [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
             Term_Rewriting.Term (Labelings.Lab b [Arith.Nat])
               [Arith.Char])])] ->
         Sum_Type.Sum (String -> String) ();
check_muterm_innermost_typed_graph_components ia j mu i r s p [] =
  Sum_Type.Inr ();
check_muterm_innermost_typed_graph_components ia j mu i r s p
  ((Nothing, c) : rest) =
  check_muterm_innermost_typed_graph_components ia j mu
    (Term_Rewriting.add_index i Arith.one_nat) r s p rest;
check_muterm_innermost_typed_graph_components ia j mu i r s p
  ((Just child, c) : rest) =
  Error_Monad.bind
    (check_muterm_typed_dp_proof_production ia j mu
      (Term_Rewriting.add_index i Arith.one_nat) r s
      (filter (Arith.membera c) p) child)
    (\ _ ->
      check_muterm_innermost_typed_graph_components ia j mu
        (Term_Rewriting.add_index i Arith.one_nat) r s p rest);

muterm_unmarked_term_check_exec ::
  forall a b c. Term_Rewriting.Term (Labelings.Lab a b) c -> Bool;
muterm_unmarked_term_check_exec (Term_Rewriting.Var x) = True;
muterm_unmarked_term_check_exec (Term_Rewriting.Fun f ts) =
  not (CSR_Checker_Base.is_sharp_lab f) &&
    all muterm_unmarked_term_check_exec ts;

muterm_recursive_target_shape_check_exec ::
  forall a b c d e f g h.
    [(a, Term_Rewriting.Term (Labelings.Lab b c) d)] ->
      [(e, Term_Rewriting.Term (Labelings.Lab f g) h)] -> Bool;
muterm_recursive_target_shape_check_exec p b =
  all (\ lr ->
        (case snd lr of {
          Term_Rewriting.Var _ -> True;
          Term_Rewriting.Fun (Labelings.Lab _ _) _ -> False;
          Term_Rewriting.Fun (Labelings.FunLab _ _) _ -> False;
          Term_Rewriting.Fun (Labelings.UnLab _) _ -> False;
          Term_Rewriting.Fun (Labelings.Sharp f) ts ->
            not (CSR_Checker_Base.is_sharp_lab f) &&
              all muterm_unmarked_term_check_exec ts;
        }))
    p &&
    all (\ lr ->
          (case snd lr of {
            Term_Rewriting.Var _ -> False;
            Term_Rewriting.Fun (Labelings.Lab _ _) _ -> False;
            Term_Rewriting.Fun (Labelings.FunLab _ _) _ -> False;
            Term_Rewriting.Fun (Labelings.UnLab _) _ -> False;
            Term_Rewriting.Fun (Labelings.Sharp f) ts ->
              not (CSR_Checker_Base.is_sharp_lab f) &&
                all muterm_unmarked_term_check_exec ts;
          }))
      b;

muterm_i4_symbolically_covered_exec ::
  forall a b c.
    (Compare.Compare a, Eq a, Compare.Compare b, Eq b, Compare.Compare c,
      Eq c) => ((Labelings.Lab a b, Arith.Nat) -> Arith.Set Arith.Nat) ->
                 Arith.Set (Labelings.Lab a b, Arith.Nat) ->
                   Arith.Set (Term_Rewriting.Term (Labelings.Lab a b) c) ->
                     Term_Rewriting.Term (Labelings.Lab a b) c -> Bool;
muterm_i4_symbolically_covered_exec mu delta e (Term_Rewriting.Var x) = True;
muterm_i4_symbolically_covered_exec mu delta e (Term_Rewriting.Fun f ts) =
  (CSR_Checker_Base.is_sharp_lab f ||
    muterm_unmarked_term_check_exec (Term_Rewriting.Fun f ts) &&
      (Arith.member (f, Arith.size_list ts) delta ||
        Arith.member (Term_Rewriting.Fun f ts) e)) &&
    let {
      d = Arith.minus_nat (Arith.size_list ts) Arith.one_nat;
    } in (if Arith.less_nat d (Arith.size_list ts)
           then Arith.all_interval
                  (\ i ->
                    (if Arith.member i
                          (muterm_i4_mu_exec mu (f, Arith.size_list ts))
                      then muterm_i4_symbolically_covered_exec mu delta e
                             (Arith.nth ts i)
                      else True))
                  Arith.zero_nat d
           else True);

muterm_recursive_bridges_safe_check_exec ::
  forall a b c d.
    (Compare.Compare a, Eq a, Compare.Compare b, Eq b, Arith.One c, Eq c,
      Arith.Cenum d, Arith.Ceq d, Arith.Ccompare d, Compare.Compare d, Eq d,
      Arith.Set_impl d) => [(Labelings.Lab a b, c)] ->
                             ((Labelings.Lab a b, Arith.Nat) ->
                               Arith.Set Arith.Nat) ->
                               Arith.Set (Labelings.Lab a b, Arith.Nat) ->
                                 [(Term_Rewriting.Term (Labelings.Lab a b) d,
                                    Term_Rewriting.Term (Labelings.Lab a b)
                                      d)] ->
                                   Bool;
muterm_recursive_bridges_safe_check_exec ds mu delta b =
  all (\ lr ->
        Arith.less_eq_set (Term_Rewriting.vars_term (snd lr))
          (Term_Rewriting.vars_term (fst lr)) &&
          (muterm_i4_symbolically_covered_exec mu delta
             (Arith.insert (fst lr)
               (Arith.set_empty
                 (Phantom_Type.of_phantom Term_Rewriting.set_impl_term)))
             (fst lr) ||
            (case fst lr of {
              Term_Rewriting.Var _ -> False;
              Term_Rewriting.Fun _ [] -> False;
              Term_Rewriting.Fun f [u] ->
                not (Arith.membera ds (f, Arith.one)) &&
                  muterm_i4_symbolically_covered_exec mu delta
                    (Arith.insert u
                      (Arith.set_empty
                        (Phantom_Type.of_phantom Term_Rewriting.set_impl_term)))
                    (fst lr);
              Term_Rewriting.Fun _ (_ : _ : _) -> False;
            })) &&
            muterm_i4_symbolically_covered_exec mu delta
              (Arith.set_empty
                (Phantom_Type.of_phantom Term_Rewriting.set_impl_term))
              (snd lr))
    b;

muterm_no_bridge_matches_exec ::
  forall a b c d.
    (Eq a, Arith.Ccompare b, Eq b, Mapping.Mapping_impl b,
      Eq d) => [(Term_Rewriting.Term a b, c)] ->
                 Term_Rewriting.Term a d -> Bool;
muterm_no_bridge_matches_exec b q =
  all (\ (a, _) -> not (Term_Rewriting.matches q a)) b;

muterm_root_pair_selects_or_ground_blocked_exec ::
  forall a b c d e f g h i j.
    (Eq b, Eq c, Eq e, Arith.Ccompare f, Eq f, Mapping.Mapping_impl f, Eq h,
      Eq i) => a -> ((Labelings.Lab b c, Arith.Nat) -> Arith.Set Arith.Nat) ->
                      d -> [(Term_Rewriting.Term e f, g)] ->
                             Labelings.Lab b c ->
                               Arith.Nat ->
                                 [Term_Rewriting.Term e h] ->
                                   (Term_Rewriting.Term (Labelings.Lab b c) i,
                                     Term_Rewriting.Term j i) ->
                                     Bool;
muterm_root_pair_selects_or_ground_blocked_exec rs mu delta b f i ts lr =
  (case lr of {
    (Term_Rewriting.Var _, _) -> False;
    (Term_Rewriting.Fun (Labelings.Lab _ _) _, _) -> False;
    (Term_Rewriting.Fun (Labelings.FunLab _ _) _, _) -> False;
    (Term_Rewriting.Fun (Labelings.UnLab _) _, _) -> False;
    (Term_Rewriting.Fun (Labelings.Sharp g) ls, r) ->
      (if not (Labelings.equal_lab g f) then True
        else (case r of {
               Term_Rewriting.Var y ->
                 Arith.less_nat i (Arith.size_list ls) &&
                   Term_Rewriting.equal_term (Arith.nth ls i)
                     (Term_Rewriting.Var y) ||
                   let {
                     d = Arith.minus_nat (Arith.size_list ls) Arith.one_nat;
                   } in Arith.less_nat d (Arith.size_list ls) &&
                          not (Arith.all_interval
                                (not .
                                  (\ j ->
                                    Arith.less_nat j (Arith.size_list ts) &&
                                      not
(Arith.member j
  (CSR_Checker_Base.csr_dp_root_mu mu
    (Labelings.Sharp f, Arith.size_list ts))) &&
Term_Rewriting.equal_term (Arith.nth ls j) (Term_Rewriting.Var y) &&
  Term_Rewriting.ground (Arith.nth ts j) &&
    muterm_no_bridge_matches_exec b (Arith.nth ts j)))
                                Arith.zero_nat d);
               Term_Rewriting.Fun _ _ -> False;
             }));
  });

muterm_root_successors_select_or_block_check_exec ::
  forall a b c d e f g h i j.
    (Eq b, Eq c, Eq e, Eq g, Arith.Ccompare h, Eq h, Mapping.Mapping_impl h,
      Eq j) => a -> ((Labelings.Lab b c, Arith.Nat) -> Arith.Set Arith.Nat) ->
                      d -> [(Term_Rewriting.Term (Labelings.Lab b c) e,
                              Term_Rewriting.Term f e)] ->
                             [(Term_Rewriting.Term g h, i)] ->
                               Labelings.Lab b c ->
                                 Arith.Nat -> [Term_Rewriting.Term g j] -> Bool;
muterm_root_successors_select_or_block_check_exec rs mu delta p b f i ts =
  all (muterm_root_pair_selects_or_ground_blocked_exec rs mu delta b f i ts) p;

muterm_recursive_pair_safe_check_exec ::
  forall a b c d e f g h.
    (Compare.Compare a, Eq a, Compare.Compare b, Eq b, Eq d, Arith.Ccompare f,
      Eq f, Mapping.Mapping_impl f, Arith.Cenum h, Arith.Ceq h,
      Arith.Ccompare h, Compare.Compare h, Eq h,
      Arith.Set_impl h) => [(Term_Rewriting.Term (Labelings.Lab a b) c,
                              Term_Rewriting.Term (Labelings.Lab a b) c)] ->
                             ((Labelings.Lab a b, Arith.Nat) ->
                               Arith.Set Arith.Nat) ->
                               Arith.Set (Labelings.Lab a b, Arith.Nat) ->
                                 [(Term_Rewriting.Term (Labelings.Lab a b) d,
                                    Term_Rewriting.Term e d)] ->
                                   [(Term_Rewriting.Term (Labelings.Lab a b) f,
                                      g)] ->
                                     (Term_Rewriting.Term (Labelings.Lab a b) h,
                                       Term_Rewriting.Term (Labelings.Lab a b)
 h) ->
                                       Bool;
muterm_recursive_pair_safe_check_exec rs mu delta p b lr =
  (case lr of {
    (l, r) ->
      (case l of {
        Term_Rewriting.Var _ -> False;
        Term_Rewriting.Fun (Labelings.Lab _ _) _ -> False;
        Term_Rewriting.Fun (Labelings.FunLab _ _) _ -> False;
        Term_Rewriting.Fun (Labelings.UnLab _) _ -> False;
        Term_Rewriting.Fun (Labelings.Sharp _) _ ->
          muterm_i4_symbolically_covered_exec mu delta
            (Arith.set_empty
              (Phantom_Type.of_phantom Term_Rewriting.set_impl_term))
            l &&
            Arith.less_eq_set (Term_Rewriting.vars_term r)
              (Term_Rewriting.vars_term l) &&
              (case r of {
                Term_Rewriting.Var _ -> True;
                Term_Rewriting.Fun (Labelings.Lab _ _) _ -> False;
                Term_Rewriting.Fun (Labelings.FunLab _ _) _ -> False;
                Term_Rewriting.Fun (Labelings.UnLab _) _ -> False;
                Term_Rewriting.Fun (Labelings.Sharp f) ts ->
                  muterm_i4_symbolically_covered_exec mu delta
                    (Arith.set_empty
                      (Phantom_Type.of_phantom Term_Rewriting.set_impl_term))
                    r ||
                    any (\ a ->
                          (case a of {
                            (_, Term_Rewriting.Var _) -> False;
                            (_, Term_Rewriting.Fun _ []) -> False;
                            (i, Term_Rewriting.Fun g [u]) ->
                              not (Arith.member i
                                    (CSR_Checker_Base.csr_dp_root_mu mu
                                      (Labelings.Sharp f,
Arith.size_list ts))) &&
                                not (Arith.membera
                                      (Term_Rewriting.defined_list rs)
                                      (g, Arith.one_nat)) &&
                                  muterm_i4_symbolically_covered_exec mu delta
                                    (Arith.insert u
                                      (Arith.set_empty
(Phantom_Type.of_phantom Term_Rewriting.set_impl_term)))
                                    r &&
                                    muterm_root_successors_select_or_block_check_exec
                                      rs mu delta p b f i ts;
                            (_, Term_Rewriting.Fun _ (_ : _ : _)) -> False;
                          }))
                      (zip (Arith.upt Arith.zero_nat (Arith.size_list ts)) ts);
              });
      });
  });

muterm_recursive_pairs_safe_check_exec ::
  forall a b c d e f.
    (Compare.Compare a, Eq a, Compare.Compare b, Eq b, Arith.Cenum d,
      Arith.Ceq d, Arith.Ccompare d, Compare.Compare d, Eq d, Arith.Set_impl d,
      Arith.Ccompare e, Eq e,
      Mapping.Mapping_impl e) => [(Term_Rewriting.Term (Labelings.Lab a b) c,
                                    Term_Rewriting.Term (Labelings.Lab a b)
                                      c)] ->
                                   ((Labelings.Lab a b, Arith.Nat) ->
                                     Arith.Set Arith.Nat) ->
                                     Arith.Set (Labelings.Lab a b, Arith.Nat) ->
                                       [(Term_Rewriting.Term (Labelings.Lab a b)
   d,
  Term_Rewriting.Term (Labelings.Lab a b) d)] ->
 [(Term_Rewriting.Term (Labelings.Lab a b) e, f)] -> Bool;
muterm_recursive_pairs_safe_check_exec rs mu delta p b =
  all (muterm_recursive_pair_safe_check_exec rs mu delta p b) p;

muterm_i4_non_mu_vars_term_list_exec ::
  forall a b c.
    ((Labelings.Lab a b, Arith.Nat) -> Arith.Set Arith.Nat) ->
      Term_Rewriting.Term (Labelings.Lab a b) c -> [c];
muterm_i4_non_mu_vars_term_list_exec mu (Term_Rewriting.Var x) = [];
muterm_i4_non_mu_vars_term_list_exec mu (Term_Rewriting.Fun f ts) =
  concatMap
    (\ i ->
      (if CSR_Checker_Base.is_sharp_lab f ||
            Arith.member i (mu (f, Arith.size_list ts))
        then muterm_i4_non_mu_vars_term_list_exec mu (Arith.nth ts i)
        else Term_Rewriting.vars_term_list (Arith.nth ts i)))
    (Arith.upt Arith.zero_nat (Arith.size_list ts));

muterm_i4_partition_check_exec ::
  forall a b c.
    (Arith.Card_UNIV c, Arith.Ceq c, Arith.Cproper_interval c,
      Arith.Set_impl c) => ((Labelings.Lab a b, Arith.Nat) ->
                             Arith.Set Arith.Nat) ->
                             Term_Rewriting.Term (Labelings.Lab a b) c -> Bool;
muterm_i4_partition_check_exec mu t =
  Arith.is_empty
    (Arith.inf_set (Arith.set (muterm_i4_mu_vars_term_list_exec mu t))
      (Arith.set (muterm_i4_non_mu_vars_term_list_exec mu t)));

muterm_recursive_i4_shape_check_exec ::
  forall a b c d e.
    (Arith.Card_UNIV c, Arith.Ceq c, Arith.Cproper_interval c, Eq c,
      Arith.Set_impl c, Arith.Card_UNIV d, Arith.Ceq d,
      Arith.Cproper_interval d, Eq d, Arith.Set_impl d, Arith.Card_UNIV e,
      Arith.Ceq e, Arith.Cproper_interval e, Eq e,
      Arith.Set_impl e) => ((Labelings.Lab a b, Arith.Nat) ->
                             Arith.Set Arith.Nat) ->
                             [(Term_Rewriting.Term (Labelings.Lab a b) c,
                                Term_Rewriting.Term (Labelings.Lab a b) d)] ->
                               [(Term_Rewriting.Term (Labelings.Lab a b) e,
                                  Term_Rewriting.Term (Labelings.Lab a b) e)] ->
                                 Bool;
muterm_recursive_i4_shape_check_exec mu p b =
  all (\ lr ->
        muterm_i4_partition_check_exec mu (fst lr) &&
          muterm_i4_full_check_exec mu (fst lr) &&
            (Term_Rewriting.is_Var (snd lr) ||
              muterm_i4_partition_check_exec mu (snd lr) &&
                muterm_i4_full_check_exec mu (snd lr)))
    p &&
    all (\ lr ->
          muterm_i4_partition_check_exec mu (fst lr) &&
            muterm_i4_partition_check_exec mu (snd lr) &&
              muterm_i4_full_check_exec mu (snd lr) &&
                all (Arith.membera
                      (muterm_i4_mu_vars_term_list_exec mu (fst lr)))
                  (muterm_i4_mu_vars_term_list_exec mu (snd lr)))
      b;

muterm_recursive_rta08_ur_redpair_proc_exec ::
  forall a b c d e.
    (Compare.Compare a, Eq a, Term_Rewriting.Showl a, Compare.Compare b, Eq b,
      Term_Rewriting.Showl b, Arith.Card_UNIV e, Arith.Cenum e, Arith.Ceq e,
      Arith.Cproper_interval e, Compare.Compare e, Eq e, Mapping.Mapping_impl e,
      Arith.Set_impl e,
      Term_Rewriting.Showl e) => [(Term_Rewriting.Term (Labelings.Lab a b) c,
                                    Term_Rewriting.Term (Labelings.Lab a b)
                                      c)] ->
                                   ((Labelings.Lab a b, Arith.Nat) ->
                                     Arith.Set Arith.Nat) ->
                                     Arith.Set (Labelings.Lab a b, Arith.Nat) ->
                                       Dependency_Pair_Problem_Spec.Dpp_ops_ext
 d (Labelings.Lab a b) e () ->
 [((Labelings.Lab a b, Arith.Nat), [Arith.Nat])] ->
   Term_Rewriting.Rel_impl_ext (Labelings.Lab a b) e () ->
     [(Term_Rewriting.Term (Labelings.Lab a b) e,
        Term_Rewriting.Term (Labelings.Lab a b) e)] ->
       [(Term_Rewriting.Term (Labelings.Lab a b) e,
          Term_Rewriting.Term (Labelings.Lab a b) e)] ->
         [(Term_Rewriting.Term (Labelings.Lab a b) e,
            Term_Rewriting.Term (Labelings.Lab a b) e)] ->
           d -> Sum_Type.Sum (String -> String) d;
muterm_recursive_rta08_ur_redpair_proc_exec rs mu delta j m rp premove u b dpp =
  (case Error_Monad.bind (Term_Rewriting.rel_impl_redpair rp)
          (\ _ ->
            (case Dependency_Pair_Problem_Spec.split_pairs j dpp premove of {
              (ps, pns) ->
                let {
                  t = Dependency_Pair_Problem_Spec.pairs j dpp ++ b ++ u;
                } in Error_Monad.bind
                       (Check_Monad.check
                         (CSR_Muterm_Usable_Rules.muterm_innermost_ur_closed_check
                           (Dependency_Pair_Problem_Spec.rules j dpp) u m t)
                         (Term_Rewriting.showsl_lit
                           "recursive MU-TERM usable-rule closure failed"))
                       (\ _ ->
                         Error_Monad.bind
                           (Check_Monad.check
                             (CSR_Muterm_Usable_Rules.muterm_strongly_conservative_check
                               m u)
                             (Term_Rewriting.showsl_lit
                               "recursive MU-TERM strong-conservativity check failed"))
                           (\ _ ->
                             Error_Monad.bind
                               (Check_Monad.check
                                 (all ((\ ta ->
 not (Term_Rewriting.is_Var ta)) .
fst)
                                   t)
                                 (Term_Rewriting.showsl_lit
                                   "recursive MU-TERM rule has a variable left-hand side"))
                               (\ _ ->
                                 Error_Monad.bind
                                   (Check_Monad.check
                                     (muterm_recursive_pairs_safe_check_exec rs
                                       mu delta
                                       (Dependency_Pair_Problem_Spec.pairs j
 dpp)
                                       b)
                                     (Term_Rewriting.showsl_lit
                                       "recursive MU-TERM pair safety check failed"))
                                   (\ _ ->
                                     Error_Monad.bind
                                       (Check_Monad.check
 (muterm_recursive_bridges_safe_check_exec (Term_Rewriting.defined_list rs) mu
   delta b)
 (Term_Rewriting.showsl_lit "recursive MU-TERM unhiding safety check failed"))
                                       (\ _ ->
 Error_Monad.bind
   (Check_Monad.check
     (muterm_recursive_target_shape_check_exec
       (Dependency_Pair_Problem_Spec.pairs j dpp) b)
     (Term_Rewriting.showsl_lit "recursive MU-TERM target-shape check failed"))
   (\ _ ->
     Error_Monad.bind
       (Check_Monad.check
         (muterm_recursive_i4_shape_check_exec mu
           (Dependency_Pair_Problem_Spec.pairs j dpp) b)
         (Term_Rewriting.showsl_lit
           "recursive MU-TERM interpretation-shape check failed"))
       (\ _ ->
         Error_Monad.bind
           (Check_Monad.check
             (CSR_Muterm_Usable_Rules.muterm_marked_mu_equal_check m)
             (Term_Rewriting.showsl_lit
               "marked replacement-map entries differ from source symbols"))
           (\ _ ->
             Error_Monad.bind (Term_Rewriting.ce_compat rp)
               (\ _ ->
                 Error_Monad.bind
                   (Error_Monad.catch_error
                     (Term_Rewriting.rel_impl_ns rp (u ++ b ++ pns))
                     (\ x ->
                       Sum_Type.Inl
                         (Term_Rewriting.showsl_lit
                            "problem weakly orienting recursive MU-TERM rules, unhiding rules, or pairs\n" .
                           x)))
                   (\ _ ->
                     Error_Monad.catch_error (Term_Rewriting.rel_impl_s rp ps)
                       (\ x ->
                         Sum_Type.Inl
                           (Term_Rewriting.showsl_lit
                              "problem strictly orienting recursive MU-TERM pairs\n" .
                             x))))))))))));
            }))
    of {
    Sum_Type.Inl a -> Sum_Type.Inl a;
    Sum_Type.Inr _ ->
      Sum_Type.Inr
        (Dependency_Pair_Problem_Spec.delete_P_Pw j dpp premove premove);
  });

check_muterm_recursive_dp_proof ::
  forall a b c.
    (Compare.Compare b, Eq b, Term_Rewriting.Showl b, Compare.Compare c, Eq c,
      Term_Rewriting.Showl c) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a
                                   (Labelings.Lab b c) [Arith.Char] () ->
                                   [((Labelings.Lab b c, Arith.Nat),
                                      [Arith.Nat])] ->
                                     (String -> String) ->
                                       [(Term_Rewriting.Term (Labelings.Lab b c)
   [Arith.Char],
  Term_Rewriting.Term (Labelings.Lab b c) [Arith.Char])] ->
 [(Term_Rewriting.Term (Labelings.Lab b c) [Arith.Char],
    Term_Rewriting.Term (Labelings.Lab b c) [Arith.Char])] ->
   [(Term_Rewriting.Term (Labelings.Lab b c) [Arith.Char],
      Term_Rewriting.Term (Labelings.Lab b c) [Arith.Char])] ->
     [(Term_Rewriting.Term (Labelings.Lab b c) [Arith.Char],
        Term_Rewriting.Term (Labelings.Lab b c) [Arith.Char])] ->
       Check_Termination.Dp_termination_proof b c [Arith.Char] ->
         Sum_Type.Sum (String -> String) ();
check_muterm_recursive_dp_proof j m i r b u p Check_Termination.P_is_Empty =
  Check_Monad.check (null p)
    (i . Term_Rewriting.showsl_lit ": recursive MU-TERM pairs are not empty");
check_muterm_recursive_dp_proof j m i r b u p
  (Check_Termination.Redpair_Proc redp pr child) =
  FOR_Preliminaries.debug i "recursive MU-TERM reduction pair"
    (let {
       dpp = Dependency_Pair_Problem_Spec.mk j False False p [] [] [] r;
     } in Error_Monad.bind
            (muterm_recursive_rta08_ur_redpair_proc_exec
              (Dependency_Pair_Problem_Spec.rules j dpp)
              (Context_Sensitive_Impl.mu_of m)
              (CSR_Minimal_CSDP_Proofs.csr_u3_delta
                (Arith.set (Dependency_Pair_Problem_Spec.rules j dpp))
                (Arith.set u))
              j m (Reduction_Pair_Implementations.get_rel_impl redp) pr u b dpp)
            (\ dppa ->
              check_muterm_recursive_dp_proof j m
                (Term_Rewriting.add_index i Arith.one_nat) r b u
                (Dependency_Pair_Problem_Spec.pairs j dppa) child));
check_muterm_recursive_dp_proof j m i r b u p
  (Check_Termination.Dep_Graph_Proc edps) =
  FOR_Preliminaries.debug i "terminal recursive MU-TERM dependency graph"
    (Error_Monad.bind
      (CSR_Muterm_Usable_Rules.check_muterm_typed_dep_graph m r b p edps)
      (\ _ ->
        Check_Monad.check (all (\ (po, _) -> Arith.is_none po) edps)
          (i . Term_Rewriting.showsl_lit
                 ": recursive MU-TERM graph has a nonterminal component")));
check_muterm_recursive_dp_proof j m i r b u p
  (Check_Termination.Subterm_Criterion_Proc v va vb vc) =
  Sum_Type.Inl
    (i . Term_Rewriting.showsl_lit
           ": unsupported processor in recursive MU-TERM continuation");
check_muterm_recursive_dp_proof j m i r b u p
  (Check_Termination.Gen_Subterm_Criterion_Proc v va vb) =
  Sum_Type.Inl
    (i . Term_Rewriting.showsl_lit
           ": unsupported processor in recursive MU-TERM continuation");
check_muterm_recursive_dp_proof j m i r b u p
  (Check_Termination.Redpair_UR_Proc v va vb vc) =
  Sum_Type.Inl
    (i . Term_Rewriting.showsl_lit
           ": unsupported processor in recursive MU-TERM continuation");
check_muterm_recursive_dp_proof j m i r b u p
  (Check_Termination.Usable_Rules_Proc v va) =
  Sum_Type.Inl
    (i . Term_Rewriting.showsl_lit
           ": unsupported processor in recursive MU-TERM continuation");
check_muterm_recursive_dp_proof j m i r b u p
  (Check_Termination.Mono_Redpair_Proc v va vb vc) =
  Sum_Type.Inl
    (i . Term_Rewriting.showsl_lit
           ": unsupported processor in recursive MU-TERM continuation");
check_muterm_recursive_dp_proof j m i r b u p
  (Check_Termination.Mono_URM_Redpair_Proc v va vb vc) =
  Sum_Type.Inl
    (i . Term_Rewriting.showsl_lit
           ": unsupported processor in recursive MU-TERM continuation");
check_muterm_recursive_dp_proof j m i r b u p
  (Check_Termination.Mono_Redpair_UR_Proc v va vb vc vd) =
  Sum_Type.Inl
    (i . Term_Rewriting.showsl_lit
           ": unsupported processor in recursive MU-TERM continuation");
check_muterm_recursive_dp_proof j m i r b u p
  (Check_Termination.Size_Change_Subterm_Proc v) =
  Sum_Type.Inl
    (i . Term_Rewriting.showsl_lit
           ": unsupported processor in recursive MU-TERM continuation");
check_muterm_recursive_dp_proof j m i r b u p
  (Check_Termination.Size_Change_Redpair_Proc v va vb) =
  Sum_Type.Inl
    (i . Term_Rewriting.showsl_lit
           ": unsupported processor in recursive MU-TERM continuation");
check_muterm_recursive_dp_proof j m i r b u p
  (Check_Termination.Uncurry_Proc v va vb vc vd) =
  Sum_Type.Inl
    (i . Term_Rewriting.showsl_lit
           ": unsupported processor in recursive MU-TERM continuation");
check_muterm_recursive_dp_proof j m i r b u p
  (Check_Termination.Fcc_Proc v va vb vc vd) =
  Sum_Type.Inl
    (i . Term_Rewriting.showsl_lit
           ": unsupported processor in recursive MU-TERM continuation");
check_muterm_recursive_dp_proof j m i r b u p
  (Check_Termination.Split_Proc v va vb vc) =
  Sum_Type.Inl
    (i . Term_Rewriting.showsl_lit
           ": unsupported processor in recursive MU-TERM continuation");
check_muterm_recursive_dp_proof j m i r b u p
  (Check_Termination.Semlab_Proc v va vb vc vd) =
  Sum_Type.Inl
    (i . Term_Rewriting.showsl_lit
           ": unsupported processor in recursive MU-TERM continuation");
check_muterm_recursive_dp_proof j m i r b u p
  (Check_Termination.Switch_Innermost_Proc v va) =
  Sum_Type.Inl
    (i . Term_Rewriting.showsl_lit
           ": unsupported processor in recursive MU-TERM continuation");
check_muterm_recursive_dp_proof j m i r b u p
  (Check_Termination.Rewriting_Proc v va vb vc vd ve vf) =
  Sum_Type.Inl
    (i . Term_Rewriting.showsl_lit
           ": unsupported processor in recursive MU-TERM continuation");
check_muterm_recursive_dp_proof j m i r b u p
  (Check_Termination.Instantiation_Proc v va vb) =
  Sum_Type.Inl
    (i . Term_Rewriting.showsl_lit
           ": unsupported processor in recursive MU-TERM continuation");
check_muterm_recursive_dp_proof j m i r b u p
  (Check_Termination.Forward_Instantiation_Proc v va vb vc) =
  Sum_Type.Inl
    (i . Term_Rewriting.showsl_lit
           ": unsupported processor in recursive MU-TERM continuation");
check_muterm_recursive_dp_proof j m i r b u p
  (Check_Termination.Narrowing_Proc v va vb vc) =
  Sum_Type.Inl
    (i . Term_Rewriting.showsl_lit
           ": unsupported processor in recursive MU-TERM continuation");
check_muterm_recursive_dp_proof j m i r b u p
  (Check_Termination.Assume_Finite v va) =
  Sum_Type.Inl
    (i . Term_Rewriting.showsl_lit
           ": unsupported processor in recursive MU-TERM continuation");
check_muterm_recursive_dp_proof j m i r b u p
  (Check_Termination.Q_Reduction_Proc v va) =
  Sum_Type.Inl
    (i . Term_Rewriting.showsl_lit
           ": unsupported processor in recursive MU-TERM continuation");
check_muterm_recursive_dp_proof j m i r b u p
  (Check_Termination.Complex_Constant_Removal_Proc v va) =
  Sum_Type.Inl
    (i . Term_Rewriting.showsl_lit
           ": unsupported processor in recursive MU-TERM continuation");
check_muterm_recursive_dp_proof j m i r b u p
  (Check_Termination.General_Redpair_Proc v va vb vc vd) =
  Sum_Type.Inl
    (i . Term_Rewriting.showsl_lit
           ": unsupported processor in recursive MU-TERM continuation");
check_muterm_recursive_dp_proof j m i r b u p (Check_Termination.To_Trs_Proc v)
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": unsupported processor in recursive MU-TERM continuation");

check_muterm_i4_graph_component ::
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
 [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
    Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
   [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
      Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
     [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
        Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
       (Maybe (CSR_Muterm_Usable_Rules.Muterm_typed_dp_proof b [Arith.Nat]
                [Arith.Char]),
         [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
            Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])]) ->
         Sum_Type.Sum (String -> String) ();
check_muterm_i4_graph_component ia j m i r b p (Nothing, c) = Sum_Type.Inr ();
check_muterm_i4_graph_component ia j m i r b p
  (Just (CSR_Muterm_Usable_Rules.Muterm_Typed_Local_Usable u child), c) =
  Error_Monad.bind
    (Check_Monad.check
      (all (\ lr -> Arith.membera r lr || Arith.membera b lr) u)
      (i . Term_Rewriting.showsl_lit
             ": extraneous recursive MU-TERM usable rule"))
    (\ _ ->
      let {
        u0 = filter (Arith.membera r) u;
      } in check_muterm_recursive_dp_proof j m
             (Term_Rewriting.add_index i Arith.one_nat) r b u0
             (filter (Arith.membera c) p) child);
check_muterm_i4_graph_component ia j m i r b p
  (Just CSR_Muterm_Usable_Rules.Muterm_Typed_P_Is_Empty, c) =
  check_muterm_typed_dp_proof_production ia j m
    (Term_Rewriting.add_index i Arith.one_nat) r b (filter (Arith.membera c) p)
    CSR_Muterm_Usable_Rules.Muterm_Typed_P_Is_Empty;
check_muterm_i4_graph_component ia j m i r b p
  (Just (CSR_Muterm_Usable_Rules.Muterm_Typed_General_Usable v va vb vc), c) =
  check_muterm_typed_dp_proof_production ia j m
    (Term_Rewriting.add_index i Arith.one_nat) r b (filter (Arith.membera c) p)
    (CSR_Muterm_Usable_Rules.Muterm_Typed_General_Usable v va vb vc);
check_muterm_i4_graph_component ia j m i r b p
  (Just (CSR_Muterm_Usable_Rules.Muterm_Typed_Pair_Augmentation v va vb), c) =
  check_muterm_typed_dp_proof_production ia j m
    (Term_Rewriting.add_index i Arith.one_nat) r b (filter (Arith.membera c) p)
    (CSR_Muterm_Usable_Rules.Muterm_Typed_Pair_Augmentation v va vb);
check_muterm_i4_graph_component ia j m i r b p
  (Just (CSR_Muterm_Usable_Rules.Muterm_Typed_CSR_Proof v), c) =
  check_muterm_typed_dp_proof_production ia j m
    (Term_Rewriting.add_index i Arith.one_nat) r b (filter (Arith.membera c) p)
    (CSR_Muterm_Usable_Rules.Muterm_Typed_CSR_Proof v);
check_muterm_i4_graph_component ia j m i r b p
  (Just (CSR_Muterm_Usable_Rules.Muterm_Typed_Expanded_CSR_Proof v), c) =
  check_muterm_typed_dp_proof_production ia j m
    (Term_Rewriting.add_index i Arith.one_nat) r b (filter (Arith.membera c) p)
    (CSR_Muterm_Usable_Rules.Muterm_Typed_Expanded_CSR_Proof v);
check_muterm_i4_graph_component ia j m i r b p
  (Just (CSR_Muterm_Usable_Rules.Muterm_Typed_Expanded_Extended_Basic_CSR_Proof
          v),
    c)
  = check_muterm_typed_dp_proof_production ia j m
      (Term_Rewriting.add_index i Arith.one_nat) r b
      (filter (Arith.membera c) p)
      (CSR_Muterm_Usable_Rules.Muterm_Typed_Expanded_Extended_Basic_CSR_Proof
        v);
check_muterm_i4_graph_component ia j m i r b p
  (Just (CSR_Muterm_Usable_Rules.Muterm_Typed_Expanded_Local_Usable v va), c) =
  check_muterm_typed_dp_proof_production ia j m
    (Term_Rewriting.add_index i Arith.one_nat) r b (filter (Arith.membera c) p)
    (CSR_Muterm_Usable_Rules.Muterm_Typed_Expanded_Local_Usable v va);
check_muterm_i4_graph_component ia j m i r b p
  (Just (CSR_Muterm_Usable_Rules.Muterm_Typed_Expanded_Strong_Usable v va vb
          vc),
    c)
  = check_muterm_typed_dp_proof_production ia j m
      (Term_Rewriting.add_index i Arith.one_nat) r b
      (filter (Arith.membera c) p)
      (CSR_Muterm_Usable_Rules.Muterm_Typed_Expanded_Strong_Usable v va vb vc);
check_muterm_i4_graph_component ia j m i r b p
  (Just (CSR_Muterm_Usable_Rules.Muterm_Typed_Expanded_Ordinary v), c) =
  check_muterm_typed_dp_proof_production ia j m
    (Term_Rewriting.add_index i Arith.one_nat) r b (filter (Arith.membera c) p)
    (CSR_Muterm_Usable_Rules.Muterm_Typed_Expanded_Ordinary v);
check_muterm_i4_graph_component ia j m i r b p
  (Just (CSR_Muterm_Usable_Rules.Muterm_Typed_Dep_Graph v), c) =
  check_muterm_typed_dp_proof_production ia j m
    (Term_Rewriting.add_index i Arith.one_nat) r b (filter (Arith.membera c) p)
    (CSR_Muterm_Usable_Rules.Muterm_Typed_Dep_Graph v);

check_muterm_i4_graph_components ::
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
 [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
    Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
   [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
      Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
     [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
        Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
       [(Maybe (CSR_Muterm_Usable_Rules.Muterm_typed_dp_proof b [Arith.Nat]
                 [Arith.Char]),
          [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
             Term_Rewriting.Term (Labelings.Lab b [Arith.Nat])
               [Arith.Char])])] ->
         Sum_Type.Sum (String -> String) ();
check_muterm_i4_graph_components ia j m i r b p [] = Sum_Type.Inr ();
check_muterm_i4_graph_components ia j m i r b p (head : rest) =
  Error_Monad.bind (check_muterm_i4_graph_component ia j m i r b p head)
    (\ _ ->
      check_muterm_i4_graph_components ia j m
        (Term_Rewriting.add_index i Arith.one_nat) r b p rest);

check_muterm_i4_root_proof ::
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
 [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
    Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
   [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
      Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
     [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
        Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
       CSR_Muterm_Usable_Rules.Muterm_typed_dp_proof b [Arith.Nat]
         [Arith.Char] ->
         Sum_Type.Sum (String -> String) ();
check_muterm_i4_root_proof ia j m i r b p
  (CSR_Muterm_Usable_Rules.Muterm_Typed_Dep_Graph edps) =
  Error_Monad.bind
    (CSR_Muterm_Usable_Rules.check_muterm_typed_dep_graph m r b p edps)
    (\ _ -> check_muterm_i4_graph_components ia j m i r b p edps);
check_muterm_i4_root_proof ia j m i r b p
  CSR_Muterm_Usable_Rules.Muterm_Typed_P_Is_Empty =
  check_muterm_typed_dp_proof_production ia j m i r b p
    CSR_Muterm_Usable_Rules.Muterm_Typed_P_Is_Empty;
check_muterm_i4_root_proof ia j m i r b p
  (CSR_Muterm_Usable_Rules.Muterm_Typed_Local_Usable v va) =
  check_muterm_typed_dp_proof_production ia j m i r b p
    (CSR_Muterm_Usable_Rules.Muterm_Typed_Local_Usable v va);
check_muterm_i4_root_proof ia j m i r b p
  (CSR_Muterm_Usable_Rules.Muterm_Typed_General_Usable v va vb vc) =
  check_muterm_typed_dp_proof_production ia j m i r b p
    (CSR_Muterm_Usable_Rules.Muterm_Typed_General_Usable v va vb vc);
check_muterm_i4_root_proof ia j m i r b p
  (CSR_Muterm_Usable_Rules.Muterm_Typed_Pair_Augmentation v va vb) =
  check_muterm_typed_dp_proof_production ia j m i r b p
    (CSR_Muterm_Usable_Rules.Muterm_Typed_Pair_Augmentation v va vb);
check_muterm_i4_root_proof ia j m i r b p
  (CSR_Muterm_Usable_Rules.Muterm_Typed_CSR_Proof v) =
  check_muterm_typed_dp_proof_production ia j m i r b p
    (CSR_Muterm_Usable_Rules.Muterm_Typed_CSR_Proof v);
check_muterm_i4_root_proof ia j m i r b p
  (CSR_Muterm_Usable_Rules.Muterm_Typed_Expanded_CSR_Proof v) =
  check_muterm_typed_dp_proof_production ia j m i r b p
    (CSR_Muterm_Usable_Rules.Muterm_Typed_Expanded_CSR_Proof v);
check_muterm_i4_root_proof ia j m i r b p
  (CSR_Muterm_Usable_Rules.Muterm_Typed_Expanded_Extended_Basic_CSR_Proof v) =
  check_muterm_typed_dp_proof_production ia j m i r b p
    (CSR_Muterm_Usable_Rules.Muterm_Typed_Expanded_Extended_Basic_CSR_Proof v);
check_muterm_i4_root_proof ia j m i r b p
  (CSR_Muterm_Usable_Rules.Muterm_Typed_Expanded_Local_Usable v va) =
  check_muterm_typed_dp_proof_production ia j m i r b p
    (CSR_Muterm_Usable_Rules.Muterm_Typed_Expanded_Local_Usable v va);
check_muterm_i4_root_proof ia j m i r b p
  (CSR_Muterm_Usable_Rules.Muterm_Typed_Expanded_Strong_Usable v va vb vc) =
  check_muterm_typed_dp_proof_production ia j m i r b p
    (CSR_Muterm_Usable_Rules.Muterm_Typed_Expanded_Strong_Usable v va vb vc);
check_muterm_i4_root_proof ia j m i r b p
  (CSR_Muterm_Usable_Rules.Muterm_Typed_Expanded_Ordinary v) =
  check_muterm_typed_dp_proof_production ia j m i r b p
    (CSR_Muterm_Usable_Rules.Muterm_Typed_Expanded_Ordinary v);

}
