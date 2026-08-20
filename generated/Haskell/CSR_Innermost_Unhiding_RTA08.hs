{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  CSR_Innermost_Unhiding_RTA08(check_innermost_csr_or_rta08_termination_proof)
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
import qualified Termination_Problem_Spec;
import qualified Countable;
import qualified CSR_Innermost_Switch;
import qualified Compare_Order_Instances;
import qualified Check_Monad;
import qualified Complex_Constant_Removal_Impl;
import qualified Check_Termination_Common;
import qualified Bounded_Increase_Impl;
import qualified Semantic_Labeling_Carrier;
import qualified Critical_Pairs_Impl;
import qualified CSR_Minimal_CSDP_Proofs;
import qualified FOR_Preliminaries;
import qualified Error_Monad;
import qualified Dependency_Pair_Problem_Spec;
import qualified Reduction_Pair_Implementations;
import qualified CSR_Checker_Base;
import qualified Check_Termination;
import qualified Subterm_Criterion_Impl;
import qualified Sum_Type;
import qualified Arith;
import qualified Compare;
import qualified Term_Rewriting;
import qualified Labelings;

check_innermost_csr_rta08_terminal ::
  forall a b c.
    (Compare.Compare_order b, Eq b, Term_Rewriting.Showl b,
      Compare.Compare_order c, Eq c,
      Term_Rewriting.Showl c) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a
                                   (Labelings.Lab b c) [Arith.Char] () ->
                                   [((Labelings.Lab b c, Arith.Nat),
                                      [Arith.Nat])] ->
                                     (String -> String) ->
                                       a ->
 CSR_Checker_Base.Csr_dp_termination_proof b c [Arith.Char] ->
   Sum_Type.Sum (String -> String) ();
check_innermost_csr_rta08_terminal j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Redpair_UR_Proc redp pr u Check_Termination.P_is_Empty))
  = FOR_Preliminaries.debug i "terminal innermost RTA08 reduction pair"
      (Error_Monad.bind
        (CSR_Minimal_CSDP_Proofs.csr_rta08_redpair_proc j mu
          (Reduction_Pair_Implementations.get_rel_impl redp) pr dpp)
        (\ dppa ->
          Check_Monad.check
            (all (Term_Rewriting.is_Var . snd)
              (Dependency_Pair_Problem_Spec.pairs j dppa))
            (i . Term_Rewriting.showsl_lit
                   ": terminal innermost RTA08 reduction pair leaves a non-collapsing dependency pair")));
check_innermost_csr_rta08_terminal j mu i dpp CSR_Checker_Base.CSR_DP_P_is_Empty
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": innermost RTA08 proof is not a terminal reduction-pair proof");
check_innermost_csr_rta08_terminal j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof Check_Termination.P_is_Empty) =
  Sum_Type.Inl
    (i . Term_Rewriting.showsl_lit
           ": innermost RTA08 proof is not a terminal reduction-pair proof");
check_innermost_csr_rta08_terminal j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Subterm_Criterion_Proc va vb vc vd))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": innermost RTA08 proof is not a terminal reduction-pair proof");
check_innermost_csr_rta08_terminal j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Gen_Subterm_Criterion_Proc va vb vc))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": innermost RTA08 proof is not a terminal reduction-pair proof");
check_innermost_csr_rta08_terminal j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Redpair_Proc va vb vc))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": innermost RTA08 proof is not a terminal reduction-pair proof");
check_innermost_csr_rta08_terminal j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Redpair_UR_Proc va vb vc
      (Check_Termination.Subterm_Criterion_Proc ve vf vg vh)))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": innermost RTA08 proof is not a terminal reduction-pair proof");
check_innermost_csr_rta08_terminal j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Redpair_UR_Proc va vb vc
      (Check_Termination.Gen_Subterm_Criterion_Proc ve vf vg)))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": innermost RTA08 proof is not a terminal reduction-pair proof");
check_innermost_csr_rta08_terminal j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Redpair_UR_Proc va vb vc
      (Check_Termination.Redpair_Proc ve vf vg)))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": innermost RTA08 proof is not a terminal reduction-pair proof");
check_innermost_csr_rta08_terminal j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Redpair_UR_Proc va vb vc
      (Check_Termination.Redpair_UR_Proc ve vf vg vh)))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": innermost RTA08 proof is not a terminal reduction-pair proof");
check_innermost_csr_rta08_terminal j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Redpair_UR_Proc va vb vc
      (Check_Termination.Usable_Rules_Proc ve vf)))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": innermost RTA08 proof is not a terminal reduction-pair proof");
check_innermost_csr_rta08_terminal j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Redpair_UR_Proc va vb vc
      (Check_Termination.Dep_Graph_Proc ve)))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": innermost RTA08 proof is not a terminal reduction-pair proof");
check_innermost_csr_rta08_terminal j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Redpair_UR_Proc va vb vc
      (Check_Termination.Mono_Redpair_Proc ve vf vg vh)))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": innermost RTA08 proof is not a terminal reduction-pair proof");
check_innermost_csr_rta08_terminal j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Redpair_UR_Proc va vb vc
      (Check_Termination.Mono_URM_Redpair_Proc ve vf vg vh)))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": innermost RTA08 proof is not a terminal reduction-pair proof");
check_innermost_csr_rta08_terminal j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Redpair_UR_Proc va vb vc
      (Check_Termination.Mono_Redpair_UR_Proc ve vf vg vh vi)))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": innermost RTA08 proof is not a terminal reduction-pair proof");
check_innermost_csr_rta08_terminal j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Redpair_UR_Proc va vb vc
      (Check_Termination.Size_Change_Subterm_Proc ve)))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": innermost RTA08 proof is not a terminal reduction-pair proof");
check_innermost_csr_rta08_terminal j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Redpair_UR_Proc va vb vc
      (Check_Termination.Size_Change_Redpair_Proc ve vf vg)))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": innermost RTA08 proof is not a terminal reduction-pair proof");
check_innermost_csr_rta08_terminal j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Redpair_UR_Proc va vb vc
      (Check_Termination.Uncurry_Proc ve vf vg vh vi)))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": innermost RTA08 proof is not a terminal reduction-pair proof");
check_innermost_csr_rta08_terminal j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Redpair_UR_Proc va vb vc
      (Check_Termination.Fcc_Proc ve vf vg vh vi)))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": innermost RTA08 proof is not a terminal reduction-pair proof");
check_innermost_csr_rta08_terminal j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Redpair_UR_Proc va vb vc
      (Check_Termination.Split_Proc ve vf vg vh)))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": innermost RTA08 proof is not a terminal reduction-pair proof");
check_innermost_csr_rta08_terminal j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Redpair_UR_Proc va vb vc
      (Check_Termination.Semlab_Proc ve vf vg vh vi)))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": innermost RTA08 proof is not a terminal reduction-pair proof");
check_innermost_csr_rta08_terminal j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Redpair_UR_Proc va vb vc
      (Check_Termination.Switch_Innermost_Proc ve vf)))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": innermost RTA08 proof is not a terminal reduction-pair proof");
check_innermost_csr_rta08_terminal j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Redpair_UR_Proc va vb vc
      (Check_Termination.Rewriting_Proc ve vf vg vh vi vj vk)))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": innermost RTA08 proof is not a terminal reduction-pair proof");
check_innermost_csr_rta08_terminal j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Redpair_UR_Proc va vb vc
      (Check_Termination.Instantiation_Proc ve vf vg)))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": innermost RTA08 proof is not a terminal reduction-pair proof");
check_innermost_csr_rta08_terminal j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Redpair_UR_Proc va vb vc
      (Check_Termination.Forward_Instantiation_Proc ve vf vg vh)))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": innermost RTA08 proof is not a terminal reduction-pair proof");
check_innermost_csr_rta08_terminal j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Redpair_UR_Proc va vb vc
      (Check_Termination.Narrowing_Proc ve vf vg vh)))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": innermost RTA08 proof is not a terminal reduction-pair proof");
check_innermost_csr_rta08_terminal j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Redpair_UR_Proc va vb vc
      (Check_Termination.Assume_Finite ve vf)))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": innermost RTA08 proof is not a terminal reduction-pair proof");
check_innermost_csr_rta08_terminal j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Redpair_UR_Proc va vb vc
      (Check_Termination.Q_Reduction_Proc ve vf)))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": innermost RTA08 proof is not a terminal reduction-pair proof");
check_innermost_csr_rta08_terminal j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Redpair_UR_Proc va vb vc
      (Check_Termination.Complex_Constant_Removal_Proc ve vf)))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": innermost RTA08 proof is not a terminal reduction-pair proof");
check_innermost_csr_rta08_terminal j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Redpair_UR_Proc va vb vc
      (Check_Termination.General_Redpair_Proc ve vf vg vh vi)))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": innermost RTA08 proof is not a terminal reduction-pair proof");
check_innermost_csr_rta08_terminal j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Redpair_UR_Proc va vb vc
      (Check_Termination.To_Trs_Proc ve)))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": innermost RTA08 proof is not a terminal reduction-pair proof");
check_innermost_csr_rta08_terminal j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Usable_Rules_Proc va vb))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": innermost RTA08 proof is not a terminal reduction-pair proof");
check_innermost_csr_rta08_terminal j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof (Check_Termination.Dep_Graph_Proc va))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": innermost RTA08 proof is not a terminal reduction-pair proof");
check_innermost_csr_rta08_terminal j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Mono_Redpair_Proc va vb vc vd))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": innermost RTA08 proof is not a terminal reduction-pair proof");
check_innermost_csr_rta08_terminal j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Mono_URM_Redpair_Proc va vb vc vd))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": innermost RTA08 proof is not a terminal reduction-pair proof");
check_innermost_csr_rta08_terminal j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Mono_Redpair_UR_Proc va vb vc vd ve))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": innermost RTA08 proof is not a terminal reduction-pair proof");
check_innermost_csr_rta08_terminal j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Size_Change_Subterm_Proc va))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": innermost RTA08 proof is not a terminal reduction-pair proof");
check_innermost_csr_rta08_terminal j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Size_Change_Redpair_Proc va vb vc))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": innermost RTA08 proof is not a terminal reduction-pair proof");
check_innermost_csr_rta08_terminal j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Uncurry_Proc va vb vc vd ve))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": innermost RTA08 proof is not a terminal reduction-pair proof");
check_innermost_csr_rta08_terminal j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Fcc_Proc va vb vc vd ve))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": innermost RTA08 proof is not a terminal reduction-pair proof");
check_innermost_csr_rta08_terminal j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Split_Proc va vb vc vd))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": innermost RTA08 proof is not a terminal reduction-pair proof");
check_innermost_csr_rta08_terminal j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Semlab_Proc va vb vc vd ve))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": innermost RTA08 proof is not a terminal reduction-pair proof");
check_innermost_csr_rta08_terminal j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Switch_Innermost_Proc va vb))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": innermost RTA08 proof is not a terminal reduction-pair proof");
check_innermost_csr_rta08_terminal j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Rewriting_Proc va vb vc vd ve vf vg))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": innermost RTA08 proof is not a terminal reduction-pair proof");
check_innermost_csr_rta08_terminal j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Instantiation_Proc va vb vc))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": innermost RTA08 proof is not a terminal reduction-pair proof");
check_innermost_csr_rta08_terminal j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Forward_Instantiation_Proc va vb vc vd))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": innermost RTA08 proof is not a terminal reduction-pair proof");
check_innermost_csr_rta08_terminal j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Narrowing_Proc va vb vc vd))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": innermost RTA08 proof is not a terminal reduction-pair proof");
check_innermost_csr_rta08_terminal j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Assume_Finite va vb))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": innermost RTA08 proof is not a terminal reduction-pair proof");
check_innermost_csr_rta08_terminal j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Q_Reduction_Proc va vb))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": innermost RTA08 proof is not a terminal reduction-pair proof");
check_innermost_csr_rta08_terminal j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Complex_Constant_Removal_Proc va vb))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": innermost RTA08 proof is not a terminal reduction-pair proof");
check_innermost_csr_rta08_terminal j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.General_Redpair_Proc va vb vc vd ve))
  = Sum_Type.Inl
      (i . Term_Rewriting.showsl_lit
             ": innermost RTA08 proof is not a terminal reduction-pair proof");
check_innermost_csr_rta08_terminal j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof (Check_Termination.To_Trs_Proc va)) =
  Sum_Type.Inl
    (i . Term_Rewriting.showsl_lit
           ": innermost RTA08 proof is not a terminal reduction-pair proof");
check_innermost_csr_rta08_terminal j mu i dpp
  (CSR_Checker_Base.CSR_DP_Subterm_Criterion_Proc v va vb vc) =
  Sum_Type.Inl
    (i . Term_Rewriting.showsl_lit
           ": innermost RTA08 proof is not a terminal reduction-pair proof");
check_innermost_csr_rta08_terminal j mu i dpp
  (CSR_Checker_Base.CSR_DP_Gen_Subterm_Criterion_Proc v va vb) =
  Sum_Type.Inl
    (i . Term_Rewriting.showsl_lit
           ": innermost RTA08 proof is not a terminal reduction-pair proof");
check_innermost_csr_rta08_terminal j mu i dpp
  (CSR_Checker_Base.CSR_DP_Usable_Rules_Proc v va) =
  Sum_Type.Inl
    (i . Term_Rewriting.showsl_lit
           ": innermost RTA08 proof is not a terminal reduction-pair proof");
check_innermost_csr_rta08_terminal j mu i dpp
  (CSR_Checker_Base.CSR_DP_Dep_Graph_Proc v) =
  Sum_Type.Inl
    (i . Term_Rewriting.showsl_lit
           ": innermost RTA08 proof is not a terminal reduction-pair proof");
check_innermost_csr_rta08_terminal j mu i dpp
  (CSR_Checker_Base.CSR_DP_Instantiation_Proc v va vb) =
  Sum_Type.Inl
    (i . Term_Rewriting.showsl_lit
           ": innermost RTA08 proof is not a terminal reduction-pair proof");
check_innermost_csr_rta08_terminal j mu i dpp
  (CSR_Checker_Base.CSR_DP_Forward_Instantiation_Proc v va vb) =
  Sum_Type.Inl
    (i . Term_Rewriting.showsl_lit
           ": innermost RTA08 proof is not a terminal reduction-pair proof");
check_innermost_csr_rta08_terminal j mu i dpp
  (CSR_Checker_Base.CSR_DP_Redpair_UR_Proc v va vb vc) =
  Sum_Type.Inl
    (i . Term_Rewriting.showsl_lit
           ": innermost RTA08 proof is not a terminal reduction-pair proof");
check_innermost_csr_rta08_terminal j mu i dpp
  (CSR_Checker_Base.CSR_DP_Size_Change_Subterm_Proc v) =
  Sum_Type.Inl
    (i . Term_Rewriting.showsl_lit
           ": innermost RTA08 proof is not a terminal reduction-pair proof");

check_innermost_csr_rta08_dp_proof ::
  forall a b c.
    (Compare.Compare_order b, Eq b, Term_Rewriting.Showl b,
      Compare.Compare_order c, Eq c,
      Term_Rewriting.Showl c) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a
                                   (Labelings.Lab b c) [Arith.Char] () ->
                                   [((Labelings.Lab b c, Arith.Nat),
                                      [Arith.Nat])] ->
                                     (String -> String) ->
                                       a ->
 CSR_Checker_Base.Csr_dp_termination_proof b c [Arith.Char] ->
   Sum_Type.Sum (String -> String) ();
check_innermost_csr_rta08_dp_proof j mu i dpp
  (CSR_Checker_Base.CSR_DP_Dep_Graph_Proc edps) =
  FOR_Preliminaries.debug i "innermost RTA08 CSR dependency graph"
    (Error_Monad.bind
      (CSR_Minimal_CSDP_Proofs.check_csr_rta08_dep_graph_proc j mu dpp edps)
      (\ _ -> check_innermost_csr_rta08_graph_components j mu i dpp edps));
check_innermost_csr_rta08_dp_proof j mu i dpp
  (CSR_Checker_Base.CSR_DP_Redpair_UR_Proc redp pr u subprf) =
  Error_Monad.catch_error
    (FOR_Preliminaries.debug i "recursive innermost RTA08 reduction pair"
      (Error_Monad.bind
        (Error_Monad.catch_error
          (CSR_Minimal_CSDP_Proofs.csr_rta08_redpair_proc j mu
            (Reduction_Pair_Implementations.get_rel_impl redp) pr dpp)
          (\ x ->
            Sum_Type.Inl
              ((i . Term_Rewriting.showsl_lit
                      ": error when applying recursive innermost RTA08 reduction pair\n") .
                x)))
        (\ dppa ->
          Error_Monad.catch_error
            (check_innermost_csr_rta08_dp_proof j mu
              (Term_Rewriting.add_index i Arith.one_nat) dppa subprf)
            (\ x ->
              Sum_Type.Inl
                ((i . Term_Rewriting.showsl_lit
                        ": error below recursive innermost RTA08 reduction pair\n") .
                  x)))))
    (\ _ ->
      check_innermost_csr_rta08_terminal j mu i dpp
        (CSR_Checker_Base.CSR_DP_Redpair_UR_Proc redp pr u subprf));
check_innermost_csr_rta08_dp_proof j mu i dpp CSR_Checker_Base.CSR_DP_P_is_Empty
  = check_innermost_csr_rta08_terminal j mu i dpp
      CSR_Checker_Base.CSR_DP_P_is_Empty;
check_innermost_csr_rta08_dp_proof j mu i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof v) =
  check_innermost_csr_rta08_terminal j mu i dpp
    (CSR_Checker_Base.CSR_DP_Ordinary_Proof v);
check_innermost_csr_rta08_dp_proof j mu i dpp
  (CSR_Checker_Base.CSR_DP_Subterm_Criterion_Proc v va vb vc) =
  check_innermost_csr_rta08_terminal j mu i dpp
    (CSR_Checker_Base.CSR_DP_Subterm_Criterion_Proc v va vb vc);
check_innermost_csr_rta08_dp_proof j mu i dpp
  (CSR_Checker_Base.CSR_DP_Gen_Subterm_Criterion_Proc v va vb) =
  check_innermost_csr_rta08_terminal j mu i dpp
    (CSR_Checker_Base.CSR_DP_Gen_Subterm_Criterion_Proc v va vb);
check_innermost_csr_rta08_dp_proof j mu i dpp
  (CSR_Checker_Base.CSR_DP_Usable_Rules_Proc v va) =
  check_innermost_csr_rta08_terminal j mu i dpp
    (CSR_Checker_Base.CSR_DP_Usable_Rules_Proc v va);
check_innermost_csr_rta08_dp_proof j mu i dpp
  (CSR_Checker_Base.CSR_DP_Instantiation_Proc v va vb) =
  check_innermost_csr_rta08_terminal j mu i dpp
    (CSR_Checker_Base.CSR_DP_Instantiation_Proc v va vb);
check_innermost_csr_rta08_dp_proof j mu i dpp
  (CSR_Checker_Base.CSR_DP_Forward_Instantiation_Proc v va vb) =
  check_innermost_csr_rta08_terminal j mu i dpp
    (CSR_Checker_Base.CSR_DP_Forward_Instantiation_Proc v va vb);
check_innermost_csr_rta08_dp_proof j mu i dpp
  (CSR_Checker_Base.CSR_DP_Size_Change_Subterm_Proc v) =
  check_innermost_csr_rta08_terminal j mu i dpp
    (CSR_Checker_Base.CSR_DP_Size_Change_Subterm_Proc v);

check_innermost_csr_rta08_graph_components ::
  forall a b c.
    (Compare.Compare_order b, Eq b, Term_Rewriting.Showl b,
      Compare.Compare_order c, Eq c,
      Term_Rewriting.Showl c) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a
                                   (Labelings.Lab b c) [Arith.Char] () ->
                                   [((Labelings.Lab b c, Arith.Nat),
                                      [Arith.Nat])] ->
                                     (String -> String) ->
                                       a ->
 [(Maybe (CSR_Checker_Base.Csr_dp_termination_proof b c [Arith.Char]),
    [(Term_Rewriting.Term (Labelings.Lab b c) [Arith.Char],
       Term_Rewriting.Term (Labelings.Lab b c) [Arith.Char])])] ->
   Sum_Type.Sum (String -> String) ();
check_innermost_csr_rta08_graph_components j mu i dpp [] = Sum_Type.Inr ();
check_innermost_csr_rta08_graph_components j mu i dpp ((Nothing, c) : rest) =
  check_innermost_csr_rta08_graph_components j mu
    (Term_Rewriting.add_index i Arith.one_nat) dpp rest;
check_innermost_csr_rta08_graph_components j mu i dpp ((Just prf, c) : rest) =
  Error_Monad.bind
    (check_innermost_csr_rta08_dp_proof j mu
      (Term_Rewriting.add_index i Arith.one_nat)
      (Dependency_Pair_Problem_Spec.intersect_pairs j dpp c) prf)
    (\ _ ->
      check_innermost_csr_rta08_graph_components j mu
        (Term_Rewriting.add_index i Arith.one_nat) dpp rest);

check_innermost_csr_rta08_termination_proof ::
  forall a b.
    (Compare.Compare_order b, Eq b,
      Term_Rewriting.Showl b) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a
                                   (Labelings.Lab b [Arith.Nat]) [Arith.Char]
                                   () ->
                                   (String -> String) ->
                                     [((Labelings.Lab b [Arith.Nat], Arith.Nat),
[Arith.Nat])] ->
                                       [(Term_Rewriting.Term
   (Labelings.Lab b [Arith.Nat]) [Arith.Char],
  Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
 [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
    Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
   CSR_Checker_Base.Csr_dp_termination_proof b [Arith.Nat] [Arith.Char] ->
     Sum_Type.Sum (String -> String) ();
check_innermost_csr_rta08_termination_proof j i mu r p prf =
  FOR_Preliminaries.debug i "terminal innermost RTA08 CSR dependency pairs"
    (Error_Monad.bind (CSR_Innermost_Switch.check_csr_orthogonal r)
      (\ _ ->
        Error_Monad.bind (CSR_Checker_Base.csr_sharp_mu_check mu)
          (\ _ ->
            Error_Monad.bind
              (CSR_Minimal_CSDP_Proofs.csr_rta08_dependency_pairs_tt j mu r p)
              (\ dpp ->
                check_innermost_csr_rta08_dp_proof j mu
                  (Term_Rewriting.add_index i Arith.one_nat) dpp prf))));

check_innermost_csr_or_rta08_termination_proof ::
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
check_innermost_csr_or_rta08_termination_proof ia j i mu r p prf =
  (case CSR_Innermost_Active_SCT.check_innermost_csr_termination_proof_active_sct
          ia j i mu r p prf
    of {
    Sum_Type.Inl _ ->
      check_innermost_csr_rta08_termination_proof j i mu r p prf;
    Sum_Type.Inr a -> Sum_Type.Inr a;
  });

}
