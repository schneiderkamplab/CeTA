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
import qualified HOL;
import qualified CSR_Checker_Base;
import qualified Mapping;
import qualified CSR_Minimal_CSDP_Proofs;
import qualified FOR_Preliminaries;
import qualified Termination_Problem_Spec;
import qualified Countable;
import qualified CSR_Hybrid_Recursive_Subterm;
import qualified CSR_Frozen_Recursive_Subterm;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified Compare_Order_Instances;
import qualified CSR_Checker;
import qualified Dependency_Pair_Problem_Spec;
import qualified Sum_Type;
import qualified Compare;
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

csr_frozen_sct_fresh ::
  forall a b.
    (Eq a) => a -> [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] -> Bool;
csr_frozen_sct_fresh u r =
  all (\ (f, _) -> not (f == u)) (Term_Rewriting.funas_trs_list r);

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
csr_semantic_component_shape Check_Termination.P_is_Empty = True;
csr_semantic_component_shape (Check_Termination.Redpair_Proc uv uw prf) =
  csr_semantic_component_shape prf;
csr_semantic_component_shape
  (Check_Termination.Subterm_Criterion_Proc ux uy uz prf) =
  csr_semantic_component_shape prf;
csr_semantic_component_shape
  (Check_Termination.Gen_Subterm_Criterion_Proc va vb prf) =
  csr_semantic_component_shape prf;
csr_semantic_component_shape (Check_Termination.Dep_Graph_Proc edpts) =
  all (\ (po, _) -> Arith.is_none po) edpts;
csr_semantic_component_shape (Check_Termination.Redpair_UR_Proc vc vd ve prf) =
  csr_semantic_component_shape prf;
csr_semantic_component_shape (Check_Termination.Mono_Redpair_Proc vf vg vh prf)
  = csr_semantic_component_shape prf;
csr_semantic_component_shape
  (Check_Termination.Mono_URM_Redpair_Proc vi vj vk prf) =
  csr_semantic_component_shape prf;
csr_semantic_component_shape
  (Check_Termination.Mono_Redpair_UR_Proc vl vm vn vo prf) =
  csr_semantic_component_shape prf;
csr_semantic_component_shape (Check_Termination.Usable_Rules_Proc v va) = False;
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

csr_frozen_sct_graph_tail ::
  forall a b c.
    (Compare.Compare_order b, Eq b, Term_Rewriting.Showl b,
      Compare.Compare_order c, Eq c,
      Term_Rewriting.Showl c) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a
                                   (Labelings.Lab b c) [Arith.Char] () ->
                                   [((Labelings.Lab b c, Arith.Nat),
                                      [Arith.Nat])] ->
                                     a -> Sum_Type.Sum (String -> String) ();
csr_frozen_sct_graph_tail j mu dpp =
  (CSR_Checker.check_csr_dep_graph_proc ::
    Dependency_Pair_Problem_Spec.Dpp_ops_ext a (Labelings.Lab b c) [Arith.Char]
      () ->
      [((Labelings.Lab b c, Arith.Nat), [Arith.Nat])] ->
        a -> [(Maybe (),
                [(Term_Rewriting.Term (Labelings.Lab b c) [Arith.Char],
                   Term_Rewriting.Term (Labelings.Lab b c) [Arith.Char])])] ->
               Sum_Type.Sum (String -> String) ())
    j mu dpp [(Nothing, Dependency_Pair_Problem_Spec.pairs j dpp)];

csr_frozen_sct_graph_projection ::
  forall a b c d.
    (Arith.Minus d, Arith.One d, Arith.Zero d,
      Eq d) => ((Term_Rewriting.Term a b, Term_Rewriting.Term a c),
                 ([(d, d)], [(d, d)])) ->
                 Maybe ([((a, Arith.Nat), d)],
                         [(Term_Rewriting.Term a b, Term_Rewriting.Term a c)]);
csr_frozen_sct_graph_projection ((l, r), (stri, nstri)) =
  (case stri ++ nstri of {
    [] -> Nothing;
    [(i, j)] ->
      (case (Term_Rewriting.root l, Term_Rewriting.root r) of {
        (Nothing, _) -> Nothing;
        (Just _, Nothing) -> Nothing;
        (Just lf, Just rf) ->
          (if i == Arith.zero || j == Arith.zero then Nothing
            else Just ([(lf, Arith.minusa i Arith.one),
                         (rf, Arith.minusa j Arith.one)],
                        (if null stri then [] else [(l, r)])));
      });
    (_, _) : _ : _ -> Nothing;
  });

csr_frozen_sct_projection ::
  forall a b c d.
    (Arith.Minus d, Arith.One d, Arith.Zero d,
      Eq d) => [((Term_Rewriting.Term a b, Term_Rewriting.Term a c),
                  ([(d, d)], [(d, d)]))] ->
                 Maybe ([((a, Arith.Nat), d)],
                         [(Term_Rewriting.Term a b, Term_Rewriting.Term a c)]);
csr_frozen_sct_projection [] = Just ([], []);
csr_frozen_sct_projection (g : gs) =
  (case (csr_frozen_sct_graph_projection g, csr_frozen_sct_projection gs) of {
    (Nothing, _) -> Nothing;
    (Just (_, _), Nothing) -> Nothing;
    (Just (p, pr), Just (ps, prs)) -> Just (p ++ ps, pr ++ prs);
  });

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

csr_frozen_sct_unsharp_candidate ::
  forall a b c.
    [(Term_Rewriting.Term (Labelings.Lab a b) c,
       Term_Rewriting.Term (Labelings.Lab a b) c)] ->
      Maybe (Labelings.Lab a b);
csr_frozen_sct_unsharp_candidate
  ((Term_Rewriting.Fun (Labelings.Sharp f) ts, r) : p) =
  Just (Labelings.FunLab f []);
csr_frozen_sct_unsharp_candidate [] = Nothing;
csr_frozen_sct_unsharp_candidate ((Term_Rewriting.Var vd, vc) : va) = Nothing;
csr_frozen_sct_unsharp_candidate
  ((Term_Rewriting.Fun (Labelings.Lab vf vg) ve, vc) : va) = Nothing;
csr_frozen_sct_unsharp_candidate
  ((Term_Rewriting.Fun (Labelings.FunLab vf vg) ve, vc) : va) = Nothing;
csr_frozen_sct_unsharp_candidate
  ((Term_Rewriting.Fun (Labelings.UnLab vf) ve, vc) : va) = Nothing;

csr_frozen_sct_subterm_proc ::
  forall a b.
    (Compare.Compare_order b, Eq b,
      Term_Rewriting.Showl b) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a
                                   (Labelings.Lab b [Arith.Nat]) [Arith.Char]
                                   () ->
                                   [((Labelings.Lab b [Arith.Nat], Arith.Nat),
                                      [Arith.Nat])] ->
                                     [((Term_Rewriting.Term
  (Labelings.Lab b [Arith.Nat]) [Arith.Char],
 Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char]),
([(Arith.Nat, Arith.Nat)], [(Arith.Nat, Arith.Nat)]))] ->
                                       a -> Sum_Type.Sum (String -> String) ();
csr_frozen_sct_subterm_proc j mu gs dpp =
  (case csr_frozen_sct_projection gs of {
    Nothing ->
      Sum_Type.Inl
        (Term_Rewriting.showsl_lit
          "size-change graphs do not encode a frozen projection");
    Just (p, pr) ->
      (case csr_frozen_sct_unsharp_candidate
              (Dependency_Pair_Problem_Spec.pairs j dpp)
        of {
        Nothing ->
          Sum_Type.Inl
            (Term_Rewriting.showsl_lit
              "frozen projection has no sharp source root");
        Just u ->
          Error_Monad.bind
            (Check_Monad.check
              (csr_frozen_sct_fresh u
                (Dependency_Pair_Problem_Spec.rules j dpp))
              (Term_Rewriting.showsl_lit
                "derived frozen projection symbol is not fresh"))
            (\ _ ->
              Error_Monad.bind
                (CSR_Frozen_Recursive_Subterm.csr_frozen_recursive_subterm_proc
                  j u mu (Subterm_Criterion_Impl.Projection p) [] pr dpp)
                (\ dppa ->
                  Error_Monad.bind (csr_frozen_sct_graph_tail j mu dppa)
                    (\ _ -> Sum_Type.Inr ())));
      });
  });

csr_hybrid_sct_subterm_proc ::
  forall a b.
    (Compare.Compare_order b, Eq b,
      Term_Rewriting.Showl b) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a
                                   (Labelings.Lab b [Arith.Nat]) [Arith.Char]
                                   () ->
                                   [((Labelings.Lab b [Arith.Nat], Arith.Nat),
                                      [Arith.Nat])] ->
                                     [((Term_Rewriting.Term
  (Labelings.Lab b [Arith.Nat]) [Arith.Char],
 Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char]),
([(Arith.Nat, Arith.Nat)], [(Arith.Nat, Arith.Nat)]))] ->
                                       a -> Sum_Type.Sum (String -> String) ();
csr_hybrid_sct_subterm_proc j mu gs dpp =
  (case csr_frozen_sct_projection gs of {
    Nothing ->
      Sum_Type.Inl
        (Term_Rewriting.showsl_lit
          "size-change graphs do not encode a hybrid projection");
    Just (p, pr) ->
      (case csr_frozen_sct_unsharp_candidate
              (Dependency_Pair_Problem_Spec.pairs j dpp)
        of {
        Nothing ->
          Sum_Type.Inl
            (Term_Rewriting.showsl_lit
              "hybrid projection has no sharp source root");
        Just u ->
          Error_Monad.bind
            (Check_Monad.check
              (csr_frozen_sct_fresh u
                (Dependency_Pair_Problem_Spec.rules j dpp))
              (Term_Rewriting.showsl_lit
                "derived hybrid projection symbol is not fresh"))
            (\ _ ->
              Error_Monad.bind
                (CSR_Hybrid_Recursive_Subterm.csr_hybrid_recursive_subterm_proc
                  j u mu (Subterm_Criterion_Impl.Projection p) [] pr dpp)
                (\ dppa ->
                  Error_Monad.bind (csr_frozen_sct_graph_tail j mu dppa)
                    (\ _ -> Sum_Type.Inr ())));
      });
  });

csr_unlab_sharp_pairs_check ::
  forall a b c.
    [(Term_Rewriting.Term (Labelings.Lab a b) c,
       Term_Rewriting.Term (Labelings.Lab a b) c)] ->
      Bool;
csr_unlab_sharp_pairs_check p =
  all (\ (s, t) -> csr_unlab_sharp_root_check s && csr_unlab_sharp_root_check t)
    p;

check_csr_finite_semantic_component ::
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
   c -> Check_Termination.Dp_termination_proof b [Arith.Nat] [Arith.Char] ->
          Sum_Type.Sum (String -> String) ();
check_csr_finite_semantic_component ia j mu a i dpp
  (Check_Termination.Size_Change_Subterm_Proc gs) =
  (if Error_Monad.isOK (csr_frozen_sct_subterm_proc j mu gs dpp)
    then FOR_Preliminaries.debug i "frozen recursive semantic CSR subterm"
           (Sum_Type.Inr ())
    else (if Error_Monad.isOK (csr_hybrid_sct_subterm_proc j mu gs dpp)
           then FOR_Preliminaries.debug i
                  "hybrid recursive semantic CSR subterm" (Sum_Type.Inr ())
           else CSR_Minimal_CSDP_Proofs.check_csr_dp_component_core ia j mu a i
                  dpp (Check_Termination.Size_Change_Subterm_Proc gs)));
check_csr_finite_semantic_component ia j mu a i dpp Check_Termination.P_is_Empty
  = CSR_Minimal_CSDP_Proofs.check_csr_dp_component_core ia j mu a i dpp
      Check_Termination.P_is_Empty;
check_csr_finite_semantic_component ia j mu a i dpp
  (Check_Termination.Subterm_Criterion_Proc v va vb vc) =
  CSR_Minimal_CSDP_Proofs.check_csr_dp_component_core ia j mu a i dpp
    (Check_Termination.Subterm_Criterion_Proc v va vb vc);
check_csr_finite_semantic_component ia j mu a i dpp
  (Check_Termination.Gen_Subterm_Criterion_Proc v va vb) =
  CSR_Minimal_CSDP_Proofs.check_csr_dp_component_core ia j mu a i dpp
    (Check_Termination.Gen_Subterm_Criterion_Proc v va vb);
check_csr_finite_semantic_component ia j mu a i dpp
  (Check_Termination.Redpair_Proc v va vb) =
  CSR_Minimal_CSDP_Proofs.check_csr_dp_component_core ia j mu a i dpp
    (Check_Termination.Redpair_Proc v va vb);
check_csr_finite_semantic_component ia j mu a i dpp
  (Check_Termination.Redpair_UR_Proc v va vb vc) =
  CSR_Minimal_CSDP_Proofs.check_csr_dp_component_core ia j mu a i dpp
    (Check_Termination.Redpair_UR_Proc v va vb vc);
check_csr_finite_semantic_component ia j mu a i dpp
  (Check_Termination.Usable_Rules_Proc v va) =
  CSR_Minimal_CSDP_Proofs.check_csr_dp_component_core ia j mu a i dpp
    (Check_Termination.Usable_Rules_Proc v va);
check_csr_finite_semantic_component ia j mu a i dpp
  (Check_Termination.Dep_Graph_Proc v) =
  CSR_Minimal_CSDP_Proofs.check_csr_dp_component_core ia j mu a i dpp
    (Check_Termination.Dep_Graph_Proc v);
check_csr_finite_semantic_component ia j mu a i dpp
  (Check_Termination.Mono_Redpair_Proc v va vb vc) =
  CSR_Minimal_CSDP_Proofs.check_csr_dp_component_core ia j mu a i dpp
    (Check_Termination.Mono_Redpair_Proc v va vb vc);
check_csr_finite_semantic_component ia j mu a i dpp
  (Check_Termination.Mono_URM_Redpair_Proc v va vb vc) =
  CSR_Minimal_CSDP_Proofs.check_csr_dp_component_core ia j mu a i dpp
    (Check_Termination.Mono_URM_Redpair_Proc v va vb vc);
check_csr_finite_semantic_component ia j mu a i dpp
  (Check_Termination.Mono_Redpair_UR_Proc v va vb vc vd) =
  CSR_Minimal_CSDP_Proofs.check_csr_dp_component_core ia j mu a i dpp
    (Check_Termination.Mono_Redpair_UR_Proc v va vb vc vd);
check_csr_finite_semantic_component ia j mu a i dpp
  (Check_Termination.Size_Change_Redpair_Proc v va vb) =
  CSR_Minimal_CSDP_Proofs.check_csr_dp_component_core ia j mu a i dpp
    (Check_Termination.Size_Change_Redpair_Proc v va vb);
check_csr_finite_semantic_component ia j mu a i dpp
  (Check_Termination.Uncurry_Proc v va vb vc vd) =
  CSR_Minimal_CSDP_Proofs.check_csr_dp_component_core ia j mu a i dpp
    (Check_Termination.Uncurry_Proc v va vb vc vd);
check_csr_finite_semantic_component ia j mu a i dpp
  (Check_Termination.Fcc_Proc v va vb vc vd) =
  CSR_Minimal_CSDP_Proofs.check_csr_dp_component_core ia j mu a i dpp
    (Check_Termination.Fcc_Proc v va vb vc vd);
check_csr_finite_semantic_component ia j mu a i dpp
  (Check_Termination.Split_Proc v va vb vc) =
  CSR_Minimal_CSDP_Proofs.check_csr_dp_component_core ia j mu a i dpp
    (Check_Termination.Split_Proc v va vb vc);
check_csr_finite_semantic_component ia j mu a i dpp
  (Check_Termination.Semlab_Proc v va vb vc vd) =
  CSR_Minimal_CSDP_Proofs.check_csr_dp_component_core ia j mu a i dpp
    (Check_Termination.Semlab_Proc v va vb vc vd);
check_csr_finite_semantic_component ia j mu a i dpp
  (Check_Termination.Switch_Innermost_Proc v va) =
  CSR_Minimal_CSDP_Proofs.check_csr_dp_component_core ia j mu a i dpp
    (Check_Termination.Switch_Innermost_Proc v va);
check_csr_finite_semantic_component ia j mu a i dpp
  (Check_Termination.Rewriting_Proc v va vb vc vd ve vf) =
  CSR_Minimal_CSDP_Proofs.check_csr_dp_component_core ia j mu a i dpp
    (Check_Termination.Rewriting_Proc v va vb vc vd ve vf);
check_csr_finite_semantic_component ia j mu a i dpp
  (Check_Termination.Instantiation_Proc v va vb) =
  CSR_Minimal_CSDP_Proofs.check_csr_dp_component_core ia j mu a i dpp
    (Check_Termination.Instantiation_Proc v va vb);
check_csr_finite_semantic_component ia j mu a i dpp
  (Check_Termination.Forward_Instantiation_Proc v va vb vc) =
  CSR_Minimal_CSDP_Proofs.check_csr_dp_component_core ia j mu a i dpp
    (Check_Termination.Forward_Instantiation_Proc v va vb vc);
check_csr_finite_semantic_component ia j mu a i dpp
  (Check_Termination.Narrowing_Proc v va vb vc) =
  CSR_Minimal_CSDP_Proofs.check_csr_dp_component_core ia j mu a i dpp
    (Check_Termination.Narrowing_Proc v va vb vc);
check_csr_finite_semantic_component ia j mu a i dpp
  (Check_Termination.Assume_Finite v va) =
  CSR_Minimal_CSDP_Proofs.check_csr_dp_component_core ia j mu a i dpp
    (Check_Termination.Assume_Finite v va);
check_csr_finite_semantic_component ia j mu a i dpp
  (Check_Termination.Q_Reduction_Proc v va) =
  CSR_Minimal_CSDP_Proofs.check_csr_dp_component_core ia j mu a i dpp
    (Check_Termination.Q_Reduction_Proc v va);
check_csr_finite_semantic_component ia j mu a i dpp
  (Check_Termination.Complex_Constant_Removal_Proc v va) =
  CSR_Minimal_CSDP_Proofs.check_csr_dp_component_core ia j mu a i dpp
    (Check_Termination.Complex_Constant_Removal_Proc v va);
check_csr_finite_semantic_component ia j mu a i dpp
  (Check_Termination.General_Redpair_Proc v va vb vc vd) =
  CSR_Minimal_CSDP_Proofs.check_csr_dp_component_core ia j mu a i dpp
    (Check_Termination.General_Redpair_Proc v va vb vc vd);
check_csr_finite_semantic_component ia j mu a i dpp
  (Check_Termination.To_Trs_Proc v) =
  CSR_Minimal_CSDP_Proofs.check_csr_dp_component_core ia j mu a i dpp
    (Check_Termination.To_Trs_Proc v);

check_csr_finite_semantic_components ::
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
   c -> [(Maybe (Check_Termination.Dp_termination_proof b [Arith.Nat]
                  [Arith.Char]),
           [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
              Term_Rewriting.Term (Labelings.Lab b [Arith.Nat])
                [Arith.Char])])] ->
          Sum_Type.Sum (String -> String) ();
check_csr_finite_semantic_components ia j mu a i dpp [] = Sum_Type.Inr ();
check_csr_finite_semantic_components ia j mu a i dpp ((Nothing, p) : rest) =
  check_csr_finite_semantic_components ia j mu a
    (Term_Rewriting.add_index i Arith.one_nat) dpp rest;
check_csr_finite_semantic_components ia j mu a i dpp ((Just prf, p) : rest) =
  Error_Monad.bind
    (check_csr_finite_semantic_component ia j mu a
      (Term_Rewriting.add_index i Arith.one_nat)
      (Dependency_Pair_Problem_Spec.intersect_pairs j dpp p) prf)
    (\ _ ->
      check_csr_finite_semantic_components ia j mu a
        (Term_Rewriting.add_index i Arith.one_nat) dpp rest);

check_csr_finite_semantic_tail ::
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
   c -> Check_Termination.Dp_termination_proof b [Arith.Nat] [Arith.Char] ->
          Sum_Type.Sum (String -> String) ();
check_csr_finite_semantic_tail ia j mu a i dpp prf =
  (case prf of {
    Check_Termination.P_is_Empty ->
      check_csr_finite_semantic_component ia j mu a i dpp prf;
    Check_Termination.Subterm_Criterion_Proc _ _ _ _ ->
      check_csr_finite_semantic_component ia j mu a i dpp prf;
    Check_Termination.Gen_Subterm_Criterion_Proc _ _ _ ->
      check_csr_finite_semantic_component ia j mu a i dpp prf;
    Check_Termination.Redpair_Proc _ _ _ ->
      check_csr_finite_semantic_component ia j mu a i dpp prf;
    Check_Termination.Redpair_UR_Proc _ _ _ _ ->
      check_csr_finite_semantic_component ia j mu a i dpp prf;
    Check_Termination.Usable_Rules_Proc _ _ ->
      check_csr_finite_semantic_component ia j mu a i dpp prf;
    Check_Termination.Dep_Graph_Proc edpts ->
      Error_Monad.bind (CSR_Checker.check_csr_dep_graph_proc j mu dpp edpts)
        (\ _ -> check_csr_finite_semantic_components ia j mu a i dpp edpts);
    Check_Termination.Mono_Redpair_Proc _ _ _ _ ->
      check_csr_finite_semantic_component ia j mu a i dpp prf;
    Check_Termination.Mono_URM_Redpair_Proc _ _ _ _ ->
      check_csr_finite_semantic_component ia j mu a i dpp prf;
    Check_Termination.Mono_Redpair_UR_Proc _ _ _ _ _ ->
      check_csr_finite_semantic_component ia j mu a i dpp prf;
    Check_Termination.Size_Change_Subterm_Proc _ ->
      check_csr_finite_semantic_component ia j mu a i dpp prf;
    Check_Termination.Size_Change_Redpair_Proc _ _ _ ->
      check_csr_finite_semantic_component ia j mu a i dpp prf;
    Check_Termination.Uncurry_Proc _ _ _ _ _ ->
      check_csr_finite_semantic_component ia j mu a i dpp prf;
    Check_Termination.Fcc_Proc _ _ _ _ _ ->
      check_csr_finite_semantic_component ia j mu a i dpp prf;
    Check_Termination.Split_Proc _ _ _ _ ->
      check_csr_finite_semantic_component ia j mu a i dpp prf;
    Check_Termination.Semlab_Proc _ _ _ _ _ ->
      check_csr_finite_semantic_component ia j mu a i dpp prf;
    Check_Termination.Switch_Innermost_Proc _ _ ->
      check_csr_finite_semantic_component ia j mu a i dpp prf;
    Check_Termination.Rewriting_Proc _ _ _ _ _ _ _ ->
      check_csr_finite_semantic_component ia j mu a i dpp prf;
    Check_Termination.Instantiation_Proc _ _ _ ->
      check_csr_finite_semantic_component ia j mu a i dpp prf;
    Check_Termination.Forward_Instantiation_Proc _ _ _ _ ->
      check_csr_finite_semantic_component ia j mu a i dpp prf;
    Check_Termination.Narrowing_Proc _ _ _ _ ->
      check_csr_finite_semantic_component ia j mu a i dpp prf;
    Check_Termination.Assume_Finite _ _ ->
      check_csr_finite_semantic_component ia j mu a i dpp prf;
    Check_Termination.Q_Reduction_Proc _ _ ->
      check_csr_finite_semantic_component ia j mu a i dpp prf;
    Check_Termination.Complex_Constant_Removal_Proc _ _ ->
      check_csr_finite_semantic_component ia j mu a i dpp prf;
    Check_Termination.General_Redpair_Proc _ _ _ _ _ ->
      check_csr_finite_semantic_component ia j mu a i dpp prf;
    Check_Termination.To_Trs_Proc _ ->
      check_csr_finite_semantic_component ia j mu a i dpp prf;
  });

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
                               (check_csr_finite_semantic_tail ia j
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
