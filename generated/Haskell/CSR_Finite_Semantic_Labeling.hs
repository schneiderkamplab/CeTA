{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  CSR_Finite_Semantic_Labeling(check_csr_dp_termination_proof_finite_semantic)
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
import qualified CSR_Minimal_CSDP_Proofs;
import qualified FOR_Preliminaries;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified HOL;
import qualified Dependency_Pair_Problem_Spec;
import qualified Termination_Problem_Spec;
import qualified CSR_Checker_Base;
import qualified Sum_Type;
import qualified Countable;
import qualified Compare;
import qualified Mapping;
import qualified Complex_Constant_Removal_Impl;
import qualified Reduction_Pair_Implementations;
import qualified Check_Termination_Common;
import qualified Bounded_Increase_Impl;
import qualified Check_Termination;
import qualified Critical_Pairs_Impl;
import qualified Subterm_Criterion_Impl;
import qualified Term_Rewriting;
import qualified Semantic_Labeling_Carrier;
import qualified Labelings;
import qualified Arith;

csr_finite_lab_mu ::
  forall a.
    [((Labelings.Lab a [Arith.Nat], Arith.Nat), [Arith.Nat])] ->
      Arith.Nat -> [((Labelings.Lab a [Arith.Nat], Arith.Nat), [Arith.Nat])];
csr_finite_lab_mu mu c =
  concatMap
    (\ (a, b) ->
      (case a of {
        (f, n) ->
          (\ is ->
            map (\ cs -> ((Labelings.Lab f cs, n), is))
              (Semantic_Labeling_Carrier.enum_vectors_nat
                (Arith.upt Arith.zero_nat (Arith.suc c)) n));
      })
        b)
    mu;

csr_semantic_sharp_bridge :: forall a b. Labelings.Lab a b -> Labelings.Lab a b;
csr_semantic_sharp_bridge (Labelings.Lab (Labelings.Sharp f) l) =
  Labelings.Sharp (Labelings.Lab f l);
csr_semantic_sharp_bridge (Labelings.Sharp (Labelings.Lab f l)) =
  Labelings.Lab (Labelings.Sharp f) l;
csr_semantic_sharp_bridge (Labelings.Lab (Labelings.Lab vb vc) va) =
  Labelings.Lab (Labelings.Lab vb vc) va;
csr_semantic_sharp_bridge (Labelings.Lab (Labelings.FunLab vb vc) va) =
  Labelings.Lab (Labelings.FunLab vb vc) va;
csr_semantic_sharp_bridge (Labelings.Lab (Labelings.UnLab vb) va) =
  Labelings.Lab (Labelings.UnLab vb) va;
csr_semantic_sharp_bridge (Labelings.FunLab v va) = Labelings.FunLab v va;
csr_semantic_sharp_bridge (Labelings.UnLab v) = Labelings.UnLab v;
csr_semantic_sharp_bridge (Labelings.Sharp (Labelings.FunLab va vb)) =
  Labelings.Sharp (Labelings.FunLab va vb);
csr_semantic_sharp_bridge (Labelings.Sharp (Labelings.UnLab va)) =
  Labelings.Sharp (Labelings.UnLab va);
csr_semantic_sharp_bridge (Labelings.Sharp (Labelings.Sharp va)) =
  Labelings.Sharp (Labelings.Sharp va);

csr_bridge_semantic_mu ::
  forall a b.
    [((Labelings.Lab a b, Arith.Nat), [Arith.Nat])] ->
      [((Labelings.Lab a b, Arith.Nat), [Arith.Nat])];
csr_bridge_semantic_mu mu =
  map (\ (a, b) ->
        (case a of {
          (f, n) -> (\ aa -> ((csr_semantic_sharp_bridge f, n), aa));
        })
          b)
    mu;

csr_semantic_component_shape ::
  forall a b c. Check_Termination.Dp_termination_proof a b c -> Bool;
csr_semantic_component_shape (Check_Termination.Size_Change_Subterm_Proc uu) =
  True;
csr_semantic_component_shape Check_Termination.P_is_Empty = False;
csr_semantic_component_shape
  (Check_Termination.Subterm_Criterion_Proc v va vb vc) = False;
csr_semantic_component_shape
  (Check_Termination.Gen_Subterm_Criterion_Proc v va vb) = False;
csr_semantic_component_shape (Check_Termination.Redpair_Proc v va vb) = False;
csr_semantic_component_shape (Check_Termination.Redpair_UR_Proc v va vb vc) =
  False;
csr_semantic_component_shape (Check_Termination.Usable_Rules_Proc v va) = False;
csr_semantic_component_shape (Check_Termination.Dep_Graph_Proc v) = False;
csr_semantic_component_shape (Check_Termination.Mono_Redpair_Proc v va vb vc) =
  False;
csr_semantic_component_shape
  (Check_Termination.Mono_URM_Redpair_Proc v va vb vc) = False;
csr_semantic_component_shape
  (Check_Termination.Mono_Redpair_UR_Proc v va vb vc vd) = False;
csr_semantic_component_shape
  (Check_Termination.Size_Change_Redpair_Proc v va vb) = False;
csr_semantic_component_shape (Check_Termination.Uncurry_Proc v va vb vc vd) =
  False;
csr_semantic_component_shape (Check_Termination.Fcc_Proc v va vb vc vd) = False;
csr_semantic_component_shape (Check_Termination.Split_Proc v va vb vc) = False;
csr_semantic_component_shape (Check_Termination.Semlab_Proc v va vb vc vd) =
  False;
csr_semantic_component_shape (Check_Termination.Switch_Innermost_Proc v va) =
  False;
csr_semantic_component_shape
  (Check_Termination.Rewriting_Proc v va vb vc vd ve vf) = False;
csr_semantic_component_shape (Check_Termination.Instantiation_Proc v va vb) =
  False;
csr_semantic_component_shape
  (Check_Termination.Forward_Instantiation_Proc v va vb vc) = False;
csr_semantic_component_shape (Check_Termination.Narrowing_Proc v va vb vc) =
  False;
csr_semantic_component_shape (Check_Termination.Assume_Finite v va) = False;
csr_semantic_component_shape (Check_Termination.Q_Reduction_Proc v va) = False;
csr_semantic_component_shape
  (Check_Termination.Complex_Constant_Removal_Proc v va) = False;
csr_semantic_component_shape
  (Check_Termination.General_Redpair_Proc v va vb vc vd) = False;
csr_semantic_component_shape (Check_Termination.To_Trs_Proc v) = False;

csr_semantic_tail_shape ::
  forall a b c. Check_Termination.Dp_termination_proof a b c -> Bool;
csr_semantic_tail_shape (Check_Termination.Dep_Graph_Proc edpts) =
  all (\ a -> (case a of {
                (Nothing, _) -> True;
                (Just aa, _) -> csr_semantic_component_shape aa;
              }))
    edpts;
csr_semantic_tail_shape Check_Termination.P_is_Empty = False;
csr_semantic_tail_shape (Check_Termination.Subterm_Criterion_Proc v va vb vc) =
  False;
csr_semantic_tail_shape (Check_Termination.Gen_Subterm_Criterion_Proc v va vb) =
  False;
csr_semantic_tail_shape (Check_Termination.Redpair_Proc v va vb) = False;
csr_semantic_tail_shape (Check_Termination.Redpair_UR_Proc v va vb vc) = False;
csr_semantic_tail_shape (Check_Termination.Usable_Rules_Proc v va) = False;
csr_semantic_tail_shape (Check_Termination.Mono_Redpair_Proc v va vb vc) =
  False;
csr_semantic_tail_shape (Check_Termination.Mono_URM_Redpair_Proc v va vb vc) =
  False;
csr_semantic_tail_shape (Check_Termination.Mono_Redpair_UR_Proc v va vb vc vd) =
  False;
csr_semantic_tail_shape (Check_Termination.Size_Change_Subterm_Proc v) = False;
csr_semantic_tail_shape (Check_Termination.Size_Change_Redpair_Proc v va vb) =
  False;
csr_semantic_tail_shape (Check_Termination.Uncurry_Proc v va vb vc vd) = False;
csr_semantic_tail_shape (Check_Termination.Fcc_Proc v va vb vc vd) = False;
csr_semantic_tail_shape (Check_Termination.Split_Proc v va vb vc) = False;
csr_semantic_tail_shape (Check_Termination.Semlab_Proc v va vb vc vd) = False;
csr_semantic_tail_shape (Check_Termination.Switch_Innermost_Proc v va) = False;
csr_semantic_tail_shape (Check_Termination.Rewriting_Proc v va vb vc vd ve vf) =
  False;
csr_semantic_tail_shape (Check_Termination.Instantiation_Proc v va vb) = False;
csr_semantic_tail_shape
  (Check_Termination.Forward_Instantiation_Proc v va vb vc) = False;
csr_semantic_tail_shape (Check_Termination.Narrowing_Proc v va vb vc) = False;
csr_semantic_tail_shape (Check_Termination.Assume_Finite v va) = False;
csr_semantic_tail_shape (Check_Termination.Q_Reduction_Proc v va) = False;
csr_semantic_tail_shape (Check_Termination.Complex_Constant_Removal_Proc v va) =
  False;
csr_semantic_tail_shape (Check_Termination.General_Redpair_Proc v va vb vc vd) =
  False;
csr_semantic_tail_shape (Check_Termination.To_Trs_Proc v) = False;

csr_bridge_semantic_component_proof ::
  forall a b c.
    Check_Termination.Dp_termination_proof a b c ->
      Check_Termination.Dp_termination_proof a b c;
csr_bridge_semantic_component_proof
  (Check_Termination.Size_Change_Subterm_Proc gs) =
  Check_Termination.Size_Change_Subterm_Proc
    (map (\ (st, a) ->
           (Term_Rewriting.map_funs_rule csr_semantic_sharp_bridge st, a))
      gs);
csr_bridge_semantic_component_proof Check_Termination.P_is_Empty =
  Check_Termination.P_is_Empty;
csr_bridge_semantic_component_proof
  (Check_Termination.Subterm_Criterion_Proc v va vb vc) =
  Check_Termination.Subterm_Criterion_Proc v va vb vc;
csr_bridge_semantic_component_proof
  (Check_Termination.Gen_Subterm_Criterion_Proc v va vb) =
  Check_Termination.Gen_Subterm_Criterion_Proc v va vb;
csr_bridge_semantic_component_proof (Check_Termination.Redpair_Proc v va vb) =
  Check_Termination.Redpair_Proc v va vb;
csr_bridge_semantic_component_proof
  (Check_Termination.Redpair_UR_Proc v va vb vc) =
  Check_Termination.Redpair_UR_Proc v va vb vc;
csr_bridge_semantic_component_proof (Check_Termination.Usable_Rules_Proc v va) =
  Check_Termination.Usable_Rules_Proc v va;
csr_bridge_semantic_component_proof (Check_Termination.Dep_Graph_Proc v) =
  Check_Termination.Dep_Graph_Proc v;
csr_bridge_semantic_component_proof
  (Check_Termination.Mono_Redpair_Proc v va vb vc) =
  Check_Termination.Mono_Redpair_Proc v va vb vc;
csr_bridge_semantic_component_proof
  (Check_Termination.Mono_URM_Redpair_Proc v va vb vc) =
  Check_Termination.Mono_URM_Redpair_Proc v va vb vc;
csr_bridge_semantic_component_proof
  (Check_Termination.Mono_Redpair_UR_Proc v va vb vc vd) =
  Check_Termination.Mono_Redpair_UR_Proc v va vb vc vd;
csr_bridge_semantic_component_proof
  (Check_Termination.Size_Change_Redpair_Proc v va vb) =
  Check_Termination.Size_Change_Redpair_Proc v va vb;
csr_bridge_semantic_component_proof
  (Check_Termination.Uncurry_Proc v va vb vc vd) =
  Check_Termination.Uncurry_Proc v va vb vc vd;
csr_bridge_semantic_component_proof (Check_Termination.Fcc_Proc v va vb vc vd) =
  Check_Termination.Fcc_Proc v va vb vc vd;
csr_bridge_semantic_component_proof (Check_Termination.Split_Proc v va vb vc) =
  Check_Termination.Split_Proc v va vb vc;
csr_bridge_semantic_component_proof
  (Check_Termination.Semlab_Proc v va vb vc vd) =
  Check_Termination.Semlab_Proc v va vb vc vd;
csr_bridge_semantic_component_proof
  (Check_Termination.Switch_Innermost_Proc v va) =
  Check_Termination.Switch_Innermost_Proc v va;
csr_bridge_semantic_component_proof
  (Check_Termination.Rewriting_Proc v va vb vc vd ve vf) =
  Check_Termination.Rewriting_Proc v va vb vc vd ve vf;
csr_bridge_semantic_component_proof
  (Check_Termination.Instantiation_Proc v va vb) =
  Check_Termination.Instantiation_Proc v va vb;
csr_bridge_semantic_component_proof
  (Check_Termination.Forward_Instantiation_Proc v va vb vc) =
  Check_Termination.Forward_Instantiation_Proc v va vb vc;
csr_bridge_semantic_component_proof
  (Check_Termination.Narrowing_Proc v va vb vc) =
  Check_Termination.Narrowing_Proc v va vb vc;
csr_bridge_semantic_component_proof (Check_Termination.Assume_Finite v va) =
  Check_Termination.Assume_Finite v va;
csr_bridge_semantic_component_proof (Check_Termination.Q_Reduction_Proc v va) =
  Check_Termination.Q_Reduction_Proc v va;
csr_bridge_semantic_component_proof
  (Check_Termination.Complex_Constant_Removal_Proc v va) =
  Check_Termination.Complex_Constant_Removal_Proc v va;
csr_bridge_semantic_component_proof
  (Check_Termination.General_Redpair_Proc v va vb vc vd) =
  Check_Termination.General_Redpair_Proc v va vb vc vd;
csr_bridge_semantic_component_proof (Check_Termination.To_Trs_Proc v) =
  Check_Termination.To_Trs_Proc v;

csr_bridge_semantic_rules ::
  forall a b c.
    [(Term_Rewriting.Term (Labelings.Lab a b) c,
       Term_Rewriting.Term (Labelings.Lab a b) c)] ->
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)];
csr_bridge_semantic_rules r =
  map (Term_Rewriting.map_funs_rule csr_semantic_sharp_bridge) r;

csr_bridge_semantic_tail ::
  forall a b c.
    Check_Termination.Dp_termination_proof a b c ->
      Check_Termination.Dp_termination_proof a b c;
csr_bridge_semantic_tail (Check_Termination.Dep_Graph_Proc edpts) =
  Check_Termination.Dep_Graph_Proc
    (map (\ (po, c) ->
           (Arith.map_option csr_bridge_semantic_component_proof po,
             csr_bridge_semantic_rules c))
      edpts);
csr_bridge_semantic_tail Check_Termination.P_is_Empty =
  Check_Termination.P_is_Empty;
csr_bridge_semantic_tail (Check_Termination.Subterm_Criterion_Proc v va vb vc) =
  Check_Termination.Subterm_Criterion_Proc v va vb vc;
csr_bridge_semantic_tail (Check_Termination.Gen_Subterm_Criterion_Proc v va vb)
  = Check_Termination.Gen_Subterm_Criterion_Proc v va vb;
csr_bridge_semantic_tail (Check_Termination.Redpair_Proc v va vb) =
  Check_Termination.Redpair_Proc v va vb;
csr_bridge_semantic_tail (Check_Termination.Redpair_UR_Proc v va vb vc) =
  Check_Termination.Redpair_UR_Proc v va vb vc;
csr_bridge_semantic_tail (Check_Termination.Usable_Rules_Proc v va) =
  Check_Termination.Usable_Rules_Proc v va;
csr_bridge_semantic_tail (Check_Termination.Mono_Redpair_Proc v va vb vc) =
  Check_Termination.Mono_Redpair_Proc v va vb vc;
csr_bridge_semantic_tail (Check_Termination.Mono_URM_Redpair_Proc v va vb vc) =
  Check_Termination.Mono_URM_Redpair_Proc v va vb vc;
csr_bridge_semantic_tail (Check_Termination.Mono_Redpair_UR_Proc v va vb vc vd)
  = Check_Termination.Mono_Redpair_UR_Proc v va vb vc vd;
csr_bridge_semantic_tail (Check_Termination.Size_Change_Subterm_Proc v) =
  Check_Termination.Size_Change_Subterm_Proc v;
csr_bridge_semantic_tail (Check_Termination.Size_Change_Redpair_Proc v va vb) =
  Check_Termination.Size_Change_Redpair_Proc v va vb;
csr_bridge_semantic_tail (Check_Termination.Uncurry_Proc v va vb vc vd) =
  Check_Termination.Uncurry_Proc v va vb vc vd;
csr_bridge_semantic_tail (Check_Termination.Fcc_Proc v va vb vc vd) =
  Check_Termination.Fcc_Proc v va vb vc vd;
csr_bridge_semantic_tail (Check_Termination.Split_Proc v va vb vc) =
  Check_Termination.Split_Proc v va vb vc;
csr_bridge_semantic_tail (Check_Termination.Semlab_Proc v va vb vc vd) =
  Check_Termination.Semlab_Proc v va vb vc vd;
csr_bridge_semantic_tail (Check_Termination.Switch_Innermost_Proc v va) =
  Check_Termination.Switch_Innermost_Proc v va;
csr_bridge_semantic_tail (Check_Termination.Rewriting_Proc v va vb vc vd ve vf)
  = Check_Termination.Rewriting_Proc v va vb vc vd ve vf;
csr_bridge_semantic_tail (Check_Termination.Instantiation_Proc v va vb) =
  Check_Termination.Instantiation_Proc v va vb;
csr_bridge_semantic_tail
  (Check_Termination.Forward_Instantiation_Proc v va vb vc) =
  Check_Termination.Forward_Instantiation_Proc v va vb vc;
csr_bridge_semantic_tail (Check_Termination.Narrowing_Proc v va vb vc) =
  Check_Termination.Narrowing_Proc v va vb vc;
csr_bridge_semantic_tail (Check_Termination.Assume_Finite v va) =
  Check_Termination.Assume_Finite v va;
csr_bridge_semantic_tail (Check_Termination.Q_Reduction_Proc v va) =
  Check_Termination.Q_Reduction_Proc v va;
csr_bridge_semantic_tail (Check_Termination.Complex_Constant_Removal_Proc v va)
  = Check_Termination.Complex_Constant_Removal_Proc v va;
csr_bridge_semantic_tail (Check_Termination.General_Redpair_Proc v va vb vc vd)
  = Check_Termination.General_Redpair_Proc v va vb vc vd;
csr_bridge_semantic_tail (Check_Termination.To_Trs_Proc v) =
  Check_Termination.To_Trs_Proc v;

csr_unlab_sharp_root_check ::
  forall a b c. Term_Rewriting.Term (Labelings.Lab a b) c -> Bool;
csr_unlab_sharp_root_check
  (Term_Rewriting.Fun (Labelings.Sharp (Labelings.UnLab f)) ts) = True;
csr_unlab_sharp_root_check (Term_Rewriting.Var v) = False;
csr_unlab_sharp_root_check (Term_Rewriting.Fun (Labelings.Lab vb vc) va) =
  False;
csr_unlab_sharp_root_check (Term_Rewriting.Fun (Labelings.FunLab vb vc) va) =
  False;
csr_unlab_sharp_root_check (Term_Rewriting.Fun (Labelings.UnLab vb) va) = False;
csr_unlab_sharp_root_check
  (Term_Rewriting.Fun (Labelings.Sharp (Labelings.Lab vc vd)) va) = False;
csr_unlab_sharp_root_check
  (Term_Rewriting.Fun (Labelings.Sharp (Labelings.FunLab vc vd)) va) = False;
csr_unlab_sharp_root_check
  (Term_Rewriting.Fun (Labelings.Sharp (Labelings.Sharp vc)) va) = False;

csr_unlab_sharp_pairs_check ::
  forall a b c.
    [(Term_Rewriting.Term (Labelings.Lab a b) c,
       Term_Rewriting.Term (Labelings.Lab a b) c)] ->
      Bool;
csr_unlab_sharp_pairs_check p =
  all (\ (s, t) -> csr_unlab_sharp_root_check s && csr_unlab_sharp_root_check t)
    p;

check_csr_dp_termination_proof_finite_semantic ::
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
check_csr_dp_termination_proof_finite_semantic ia j mu a i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Semlab_Proc (Semantic_Labeling_Carrier.Finitelab sli) lP
      lQ lR subprf))
  = FOR_Preliminaries.debug i "exact minimal CSR finite semantic labeling"
      (let {
         base =
           Dependency_Pair_Problem_Spec.mk j False False
             (Dependency_Pair_Problem_Spec.pairs j dpp) [] [] []
             (Dependency_Pair_Problem_Spec.rules j dpp);
       } in Error_Monad.bind
              (Check_Monad.check
                (csr_unlab_sharp_pairs_check
                  (Dependency_Pair_Problem_Spec.pairs j dpp))
                (Term_Rewriting.showsl_lit
                  "exact CSR semantic labeling requires original marked pairs"))
              (\ _ ->
                Error_Monad.bind
                  (Error_Monad.catch_error
                    (Semantic_Labeling_Carrier.semlab_fin_proc j
                      (Semantic_Labeling_Carrier.Finitelab sli) lP lQ lR base)
                    (\ x ->
                      Sum_Type.Inl
                        ((i . Term_Rewriting.showsl_lit
                                ": error when applying exact CSR semantic labeling\n") .
                          x)))
                  (\ dppa ->
                    Error_Monad.bind
                      (Check_Monad.check (csr_semantic_tail_shape subprf)
                        (Term_Rewriting.showsl_lit
                          "unsupported proof below exact CSR semantic labeling"))
                      (\ _ ->
                        let {
                          bdpp =
                            Dependency_Pair_Problem_Spec.mk j False False
                              (csr_bridge_semantic_rules
                                (Dependency_Pair_Problem_Spec.pairs j dppa))
                              [] [] []
                              (csr_bridge_semantic_rules
                                (Dependency_Pair_Problem_Spec.rules j dppa));
                        } in Error_Monad.catch_error
                               (CSR_Minimal_CSDP_Proofs.check_csr_dp_after_u3_tail
                                 ia j
                                 (csr_bridge_semantic_mu
                                   (csr_finite_lab_mu mu
                                     (Semantic_Labeling_Carrier.get_largest_element
                                       sli)))
                                 a (Term_Rewriting.add_index i Arith.one_nat)
                                 bdpp (csr_bridge_semantic_tail subprf))
                               (\ x ->
                                 Sum_Type.Inl
                                   ((i . Term_Rewriting.showsl_lit
   ": error below exact CSR semantic labeling\n") .
                                     x))))));
check_csr_dp_termination_proof_finite_semantic ia j mu a i dpp
  CSR_Checker_Base.CSR_DP_P_is_Empty =
  CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu a i dpp
    CSR_Checker_Base.CSR_DP_P_is_Empty;
check_csr_dp_termination_proof_finite_semantic ia j mu a i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof Check_Termination.P_is_Empty) =
  CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu a i dpp
    (CSR_Checker_Base.CSR_DP_Ordinary_Proof Check_Termination.P_is_Empty);
check_csr_dp_termination_proof_finite_semantic ia j mu a i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Subterm_Criterion_Proc va vb vc vd))
  = CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu a i dpp
      (CSR_Checker_Base.CSR_DP_Ordinary_Proof
        (Check_Termination.Subterm_Criterion_Proc va vb vc vd));
check_csr_dp_termination_proof_finite_semantic ia j mu a i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Gen_Subterm_Criterion_Proc va vb vc))
  = CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu a i dpp
      (CSR_Checker_Base.CSR_DP_Ordinary_Proof
        (Check_Termination.Gen_Subterm_Criterion_Proc va vb vc));
check_csr_dp_termination_proof_finite_semantic ia j mu a i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Redpair_Proc va vb vc))
  = CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu a i dpp
      (CSR_Checker_Base.CSR_DP_Ordinary_Proof
        (Check_Termination.Redpair_Proc va vb vc));
check_csr_dp_termination_proof_finite_semantic ia j mu a i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Redpair_UR_Proc va vb vc vd))
  = CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu a i dpp
      (CSR_Checker_Base.CSR_DP_Ordinary_Proof
        (Check_Termination.Redpair_UR_Proc va vb vc vd));
check_csr_dp_termination_proof_finite_semantic ia j mu a i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Usable_Rules_Proc va vb))
  = CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu a i dpp
      (CSR_Checker_Base.CSR_DP_Ordinary_Proof
        (Check_Termination.Usable_Rules_Proc va vb));
check_csr_dp_termination_proof_finite_semantic ia j mu a i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof (Check_Termination.Dep_Graph_Proc va))
  = CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu a i dpp
      (CSR_Checker_Base.CSR_DP_Ordinary_Proof
        (Check_Termination.Dep_Graph_Proc va));
check_csr_dp_termination_proof_finite_semantic ia j mu a i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Mono_Redpair_Proc va vb vc vd))
  = CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu a i dpp
      (CSR_Checker_Base.CSR_DP_Ordinary_Proof
        (Check_Termination.Mono_Redpair_Proc va vb vc vd));
check_csr_dp_termination_proof_finite_semantic ia j mu a i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Mono_URM_Redpair_Proc va vb vc vd))
  = CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu a i dpp
      (CSR_Checker_Base.CSR_DP_Ordinary_Proof
        (Check_Termination.Mono_URM_Redpair_Proc va vb vc vd));
check_csr_dp_termination_proof_finite_semantic ia j mu a i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Mono_Redpair_UR_Proc va vb vc vd ve))
  = CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu a i dpp
      (CSR_Checker_Base.CSR_DP_Ordinary_Proof
        (Check_Termination.Mono_Redpair_UR_Proc va vb vc vd ve));
check_csr_dp_termination_proof_finite_semantic ia j mu a i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Size_Change_Subterm_Proc va))
  = CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu a i dpp
      (CSR_Checker_Base.CSR_DP_Ordinary_Proof
        (Check_Termination.Size_Change_Subterm_Proc va));
check_csr_dp_termination_proof_finite_semantic ia j mu a i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Size_Change_Redpair_Proc va vb vc))
  = CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu a i dpp
      (CSR_Checker_Base.CSR_DP_Ordinary_Proof
        (Check_Termination.Size_Change_Redpair_Proc va vb vc));
check_csr_dp_termination_proof_finite_semantic ia j mu a i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Uncurry_Proc va vb vc vd ve))
  = CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu a i dpp
      (CSR_Checker_Base.CSR_DP_Ordinary_Proof
        (Check_Termination.Uncurry_Proc va vb vc vd ve));
check_csr_dp_termination_proof_finite_semantic ia j mu a i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Fcc_Proc va vb vc vd ve))
  = CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu a i dpp
      (CSR_Checker_Base.CSR_DP_Ordinary_Proof
        (Check_Termination.Fcc_Proc va vb vc vd ve));
check_csr_dp_termination_proof_finite_semantic ia j mu a i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Split_Proc va vb vc vd))
  = CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu a i dpp
      (CSR_Checker_Base.CSR_DP_Ordinary_Proof
        (Check_Termination.Split_Proc va vb vc vd));
check_csr_dp_termination_proof_finite_semantic ia j mu a i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Semlab_Proc (Semantic_Labeling_Carrier.Rootlab vf) vb vc
      vd ve))
  = CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu a i dpp
      (CSR_Checker_Base.CSR_DP_Ordinary_Proof
        (Check_Termination.Semlab_Proc (Semantic_Labeling_Carrier.Rootlab vf) vb
          vc vd ve));
check_csr_dp_termination_proof_finite_semantic ia j mu a i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Semlab_Proc
      (Semantic_Labeling_Carrier.QuasiFinitelab vf vg) vb vc vd ve))
  = CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu a i dpp
      (CSR_Checker_Base.CSR_DP_Ordinary_Proof
        (Check_Termination.Semlab_Proc
          (Semantic_Labeling_Carrier.QuasiFinitelab vf vg) vb vc vd ve));
check_csr_dp_termination_proof_finite_semantic ia j mu a i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Switch_Innermost_Proc va vb))
  = CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu a i dpp
      (CSR_Checker_Base.CSR_DP_Ordinary_Proof
        (Check_Termination.Switch_Innermost_Proc va vb));
check_csr_dp_termination_proof_finite_semantic ia j mu a i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Rewriting_Proc va vb vc vd ve vf vg))
  = CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu a i dpp
      (CSR_Checker_Base.CSR_DP_Ordinary_Proof
        (Check_Termination.Rewriting_Proc va vb vc vd ve vf vg));
check_csr_dp_termination_proof_finite_semantic ia j mu a i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Instantiation_Proc va vb vc))
  = CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu a i dpp
      (CSR_Checker_Base.CSR_DP_Ordinary_Proof
        (Check_Termination.Instantiation_Proc va vb vc));
check_csr_dp_termination_proof_finite_semantic ia j mu a i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Forward_Instantiation_Proc va vb vc vd))
  = CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu a i dpp
      (CSR_Checker_Base.CSR_DP_Ordinary_Proof
        (Check_Termination.Forward_Instantiation_Proc va vb vc vd));
check_csr_dp_termination_proof_finite_semantic ia j mu a i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Narrowing_Proc va vb vc vd))
  = CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu a i dpp
      (CSR_Checker_Base.CSR_DP_Ordinary_Proof
        (Check_Termination.Narrowing_Proc va vb vc vd));
check_csr_dp_termination_proof_finite_semantic ia j mu a i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Assume_Finite va vb))
  = CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu a i dpp
      (CSR_Checker_Base.CSR_DP_Ordinary_Proof
        (Check_Termination.Assume_Finite va vb));
check_csr_dp_termination_proof_finite_semantic ia j mu a i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Q_Reduction_Proc va vb))
  = CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu a i dpp
      (CSR_Checker_Base.CSR_DP_Ordinary_Proof
        (Check_Termination.Q_Reduction_Proc va vb));
check_csr_dp_termination_proof_finite_semantic ia j mu a i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.Complex_Constant_Removal_Proc va vb))
  = CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu a i dpp
      (CSR_Checker_Base.CSR_DP_Ordinary_Proof
        (Check_Termination.Complex_Constant_Removal_Proc va vb));
check_csr_dp_termination_proof_finite_semantic ia j mu a i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof
    (Check_Termination.General_Redpair_Proc va vb vc vd ve))
  = CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu a i dpp
      (CSR_Checker_Base.CSR_DP_Ordinary_Proof
        (Check_Termination.General_Redpair_Proc va vb vc vd ve));
check_csr_dp_termination_proof_finite_semantic ia j mu a i dpp
  (CSR_Checker_Base.CSR_DP_Ordinary_Proof (Check_Termination.To_Trs_Proc va)) =
  CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu a i dpp
    (CSR_Checker_Base.CSR_DP_Ordinary_Proof (Check_Termination.To_Trs_Proc va));
check_csr_dp_termination_proof_finite_semantic ia j mu a i dpp
  (CSR_Checker_Base.CSR_DP_Subterm_Criterion_Proc v va vb vc) =
  CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu a i dpp
    (CSR_Checker_Base.CSR_DP_Subterm_Criterion_Proc v va vb vc);
check_csr_dp_termination_proof_finite_semantic ia j mu a i dpp
  (CSR_Checker_Base.CSR_DP_Gen_Subterm_Criterion_Proc v va vb) =
  CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu a i dpp
    (CSR_Checker_Base.CSR_DP_Gen_Subterm_Criterion_Proc v va vb);
check_csr_dp_termination_proof_finite_semantic ia j mu a i dpp
  (CSR_Checker_Base.CSR_DP_Usable_Rules_Proc v va) =
  CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu a i dpp
    (CSR_Checker_Base.CSR_DP_Usable_Rules_Proc v va);
check_csr_dp_termination_proof_finite_semantic ia j mu a i dpp
  (CSR_Checker_Base.CSR_DP_Dep_Graph_Proc v) =
  CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu a i dpp
    (CSR_Checker_Base.CSR_DP_Dep_Graph_Proc v);
check_csr_dp_termination_proof_finite_semantic ia j mu a i dpp
  (CSR_Checker_Base.CSR_DP_Instantiation_Proc v va vb) =
  CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu a i dpp
    (CSR_Checker_Base.CSR_DP_Instantiation_Proc v va vb);
check_csr_dp_termination_proof_finite_semantic ia j mu a i dpp
  (CSR_Checker_Base.CSR_DP_Forward_Instantiation_Proc v va vb) =
  CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu a i dpp
    (CSR_Checker_Base.CSR_DP_Forward_Instantiation_Proc v va vb);
check_csr_dp_termination_proof_finite_semantic ia j mu a i dpp
  (CSR_Checker_Base.CSR_DP_Redpair_UR_Proc v va vb vc) =
  CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu a i dpp
    (CSR_Checker_Base.CSR_DP_Redpair_UR_Proc v va vb vc);
check_csr_dp_termination_proof_finite_semantic ia j mu a i dpp
  (CSR_Checker_Base.CSR_DP_Size_Change_Subterm_Proc v) =
  CSR_Minimal_CSDP_Proofs.check_csr_dp_termination_proof_min ia j mu a i dpp
    (CSR_Checker_Base.CSR_DP_Size_Change_Subterm_Proc v);

}
