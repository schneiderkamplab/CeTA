{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Check_Termination(Rfc_closure_certificate(..), Unknown_proof(..),
                     Fptrs_termination_proof(..), Trs_termination_proof(..),
                     Dp_termination_proof(..), check_unknown_proof,
                     check_fptrs_termination_proof, check_trs_termination_proof,
                     check_dp_termination_proof)
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
import qualified Right_Ground_Termination_Impl;
import qualified RFC_Matchbounds_Ext;
import qualified DP_Transformation_Impl;
import qualified String_Reversal_Impl;
import qualified Argument_Filter_Impl;
import qualified Generic_Reduction_Pair_Processor_Impl;
import qualified Size_Change_Termination_Processors_Impl;
import qualified AC_Subterm_Criterion_Impl;
import qualified Innermost_Usable_Rules_Impl;
import qualified Innermost_Switch_Impl;
import qualified Reduction_Pair_Proc_Impl;
import qualified Instantiation_Impl;
import qualified Dependency_Graph_Impl;
import qualified Flat_Context_Closure_Impl;
import qualified Q_Reduction_Impl;
import qualified Uncurry_Impl;
import qualified Renaming2_String;
import qualified Rewriting_Impl;
import qualified Narrowing_Impl;
import qualified Split_Impl;
import qualified Non_Inf_Order_Impl;
import qualified Renaming2;
import qualified Compare_Order_Instances;
import qualified List_Lexorder;
import qualified Lists_are_Infinite;
import qualified FOR_Preliminaries;
import qualified Mapping;
import qualified Q_Restricted_Rewriting_Impl;
import qualified QDP_Framework_Impl;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified HOL;
import qualified Sum_Type;
import qualified Compare;
import qualified Countable;
import qualified Dependency_Pair_Problem_Spec;
import qualified Termination_Problem_Spec;
import qualified Monadic_Rewriting_Impl;
import qualified Matchbounds_Impl;
import qualified Complex_Constant_Removal_Impl;
import qualified Reduction_Pair_Implementations;
import qualified Bounded_Increase_Impl;
import qualified Semantic_Labeling_Carrier;
import qualified Critical_Pairs_Impl;
import qualified Subterm_Criterion_Impl;
import qualified Labelings;
import qualified Term_Rewriting;
import qualified Check_Termination_Common;
import qualified Arith;

data Rfc_closure_certificate = RFC_Explicit | RFC_Automaton_Closed
  | RFC_Matchbox;

data Unknown_proof a b c =
  Assume_Unknown [Arith.Char]
    [Check_Termination_Common.Generic_assm_proof a b c
       (Trs_termination_proof a b c) (Dp_termination_proof a b c)
       (Fptrs_termination_proof a b c) () (Unknown_proof a b c)];

data Fptrs_termination_proof a b c =
  Assume_FP_SN
    ([(Term_Rewriting.Actxt (Labelings.Lab a b)
         (Term_Rewriting.Term (Labelings.Lab a b) c),
        (Term_Rewriting.Term (Labelings.Lab a b) c, Term_Rewriting.Location))],
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)])
    [Check_Termination_Common.Generic_assm_proof a b c
       (Trs_termination_proof a b c) (Dp_termination_proof a b c)
       (Fptrs_termination_proof a b c) () (Unknown_proof a b c)];

data Trs_termination_proof a b c =
  DP_Trans Bool Bool
    [(Term_Rewriting.Term (Labelings.Lab a b) c,
       Term_Rewriting.Term (Labelings.Lab a b) c)]
    (Dp_termination_proof a b c)
  | Rule_Removal
      (Reduction_Pair_Implementations.Redtriple_impl (Labelings.Lab a b))
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      (Trs_termination_proof a b c)
  | String_Reversal (Trs_termination_proof a b c)
  | Constant_String
      (Monadic_Rewriting_Impl.Const_string_sound_proof (Labelings.Lab a b) c)
      (Trs_termination_proof a b c)
  | Bounds (Matchbounds_Impl.Bounds_info (Labelings.Lab a b) c)
  | Relative_Bounds (Matchbounds_Impl.Bounds_info (Labelings.Lab a b) c)
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      (Trs_termination_proof a b c)
  | Rfc_Bounds_Proc Rfc_closure_certificate
      (Matchbounds_Impl.Bounds_info (Labelings.Lab a b) c)
      [Term_Rewriting.Term (Labelings.Lab a b) c]
      (Maybe ([(Term_Rewriting.Term (Labelings.Lab a b) c,
                 Term_Rewriting.Term (Labelings.Lab a b) c)],
               Trs_termination_proof a b c))
  | Uncurry
      (Labelings.Lab a b,
        ([((Labelings.Lab a b, Arith.Nat), [Labelings.Lab a b])],
          ([(Term_Rewriting.Term (Labelings.Lab a b) c,
              Term_Rewriting.Term (Labelings.Lab a b) c)],
            [(Term_Rewriting.Term (Labelings.Lab a b) c,
               Term_Rewriting.Term (Labelings.Lab a b) c)])))
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      (Trs_termination_proof a b c)
  | Semlab (Semantic_Labeling_Carrier.Sl_variant (Labelings.Lab a b) c)
      [Term_Rewriting.Term (Labelings.Lab a b) c]
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      (Trs_termination_proof a b c)
  | R_is_Empty
  | Fcc [Term_Rewriting.Actxt (Labelings.Lab a b)
           (Term_Rewriting.Term (Labelings.Lab a b) c)]
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      (Trs_termination_proof a b c)
  | Split [(Term_Rewriting.Term (Labelings.Lab a b) c,
             Term_Rewriting.Term (Labelings.Lab a b) c)]
      (Trs_termination_proof a b c) (Trs_termination_proof a b c)
  | Switch_Innermost (Critical_Pairs_Impl.Join_info (Labelings.Lab a b) c)
      (Trs_termination_proof a b c)
  | Drop_Equality (Trs_termination_proof a b c)
  | Remove_Nonapplicable_Rules
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      (Trs_termination_proof a b c)
  | Permuting_AFS [((Labelings.Lab a b, Arith.Nat), Term_Rewriting.Af_entry)]
      (Trs_termination_proof a b c)
  | Right_Ground_Termination
  | Assume_SN
      (Bool,
        ([Term_Rewriting.Term (Labelings.Lab a b) c],
          ([(Term_Rewriting.Term (Labelings.Lab a b) c,
              Term_Rewriting.Term (Labelings.Lab a b) c)],
            [(Term_Rewriting.Term (Labelings.Lab a b) c,
               Term_Rewriting.Term (Labelings.Lab a b) c)])))
      [Check_Termination_Common.Generic_assm_proof a b c
         (Trs_termination_proof a b c) (Dp_termination_proof a b c)
         (Fptrs_termination_proof a b c) () (Unknown_proof a b c)];

data Dp_termination_proof a b c = P_is_Empty
  | Subterm_Criterion_Proc (Subterm_Criterion_Impl.ProjL (Labelings.Lab a b))
      [((Term_Rewriting.Term (Labelings.Lab a b) c,
          Term_Rewriting.Term (Labelings.Lab a b) c),
         [([Arith.Nat],
            ((Term_Rewriting.Term (Labelings.Lab a b) c,
               Term_Rewriting.Term (Labelings.Lab a b) c),
              Term_Rewriting.Term (Labelings.Lab a b) c))])]
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      (Dp_termination_proof a b c)
  | Gen_Subterm_Criterion_Proc [((Labelings.Lab a b, Arith.Nat), [Arith.Nat])]
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      (Dp_termination_proof a b c)
  | Redpair_Proc
      (Reduction_Pair_Implementations.Redtriple_impl (Labelings.Lab a b))
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      (Dp_termination_proof a b c)
  | Redpair_UR_Proc
      (Reduction_Pair_Implementations.Redtriple_impl (Labelings.Lab a b))
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      (Dp_termination_proof a b c)
  | Usable_Rules_Proc
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      (Dp_termination_proof a b c)
  | Dep_Graph_Proc
      [(Maybe (Dp_termination_proof a b c),
         [(Term_Rewriting.Term (Labelings.Lab a b) c,
            Term_Rewriting.Term (Labelings.Lab a b) c)])]
  | Mono_Redpair_Proc
      (Reduction_Pair_Implementations.Redtriple_impl (Labelings.Lab a b))
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      (Dp_termination_proof a b c)
  | Mono_URM_Redpair_Proc
      (Reduction_Pair_Implementations.Redtriple_impl (Labelings.Lab a b))
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      (Dp_termination_proof a b c)
  | Mono_Redpair_UR_Proc
      (Reduction_Pair_Implementations.Redtriple_impl (Labelings.Lab a b))
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      (Dp_termination_proof a b c)
  | Size_Change_Subterm_Proc
      [((Term_Rewriting.Term (Labelings.Lab a b) c,
          Term_Rewriting.Term (Labelings.Lab a b) c),
         ([(Arith.Nat, Arith.Nat)], [(Arith.Nat, Arith.Nat)]))]
  | Size_Change_Redpair_Proc
      (Reduction_Pair_Implementations.Redtriple_impl (Labelings.Lab a b))
      (Maybe [(Term_Rewriting.Term (Labelings.Lab a b) c,
                Term_Rewriting.Term (Labelings.Lab a b) c)])
      [((Term_Rewriting.Term (Labelings.Lab a b) c,
          Term_Rewriting.Term (Labelings.Lab a b) c),
         ([(Arith.Nat, Arith.Nat)], [(Arith.Nat, Arith.Nat)]))]
  | Uncurry_Proc (Maybe Arith.Nat)
      (Labelings.Lab a b,
        ([((Labelings.Lab a b, Arith.Nat), [Labelings.Lab a b])],
          ([(Term_Rewriting.Term (Labelings.Lab a b) c,
              Term_Rewriting.Term (Labelings.Lab a b) c)],
            [(Term_Rewriting.Term (Labelings.Lab a b) c,
               Term_Rewriting.Term (Labelings.Lab a b) c)])))
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      (Dp_termination_proof a b c)
  | Fcc_Proc (Labelings.Lab a b)
      [Term_Rewriting.Actxt (Labelings.Lab a b)
         (Term_Rewriting.Term (Labelings.Lab a b) c)]
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      (Dp_termination_proof a b c)
  | Split_Proc
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      (Dp_termination_proof a b c) (Dp_termination_proof a b c)
  | Semlab_Proc (Semantic_Labeling_Carrier.Sl_variant (Labelings.Lab a b) c)
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      [Term_Rewriting.Term (Labelings.Lab a b) c]
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      (Dp_termination_proof a b c)
  | Switch_Innermost_Proc (Critical_Pairs_Impl.Join_info (Labelings.Lab a b) c)
      (Dp_termination_proof a b c)
  | Rewriting_Proc
      (Maybe [(Term_Rewriting.Term (Labelings.Lab a b) c,
                Term_Rewriting.Term (Labelings.Lab a b) c)])
      (Term_Rewriting.Term (Labelings.Lab a b) c,
        Term_Rewriting.Term (Labelings.Lab a b) c)
      (Term_Rewriting.Term (Labelings.Lab a b) c,
        Term_Rewriting.Term (Labelings.Lab a b) c)
      (Term_Rewriting.Term (Labelings.Lab a b) c,
        Term_Rewriting.Term (Labelings.Lab a b) c)
      (Term_Rewriting.Term (Labelings.Lab a b) c,
        Term_Rewriting.Term (Labelings.Lab a b) c)
      [Arith.Nat] (Dp_termination_proof a b c)
  | Instantiation_Proc
      (Term_Rewriting.Term (Labelings.Lab a b) c,
        Term_Rewriting.Term (Labelings.Lab a b) c)
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      (Dp_termination_proof a b c)
  | Forward_Instantiation_Proc
      (Term_Rewriting.Term (Labelings.Lab a b) c,
        Term_Rewriting.Term (Labelings.Lab a b) c)
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      (Maybe [(Term_Rewriting.Term (Labelings.Lab a b) c,
                Term_Rewriting.Term (Labelings.Lab a b) c)])
      (Dp_termination_proof a b c)
  | Narrowing_Proc
      (Term_Rewriting.Term (Labelings.Lab a b) c,
        Term_Rewriting.Term (Labelings.Lab a b) c)
      [Arith.Nat]
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      (Dp_termination_proof a b c)
  | Assume_Finite
      (Bool,
        (Bool,
          ([(Term_Rewriting.Term (Labelings.Lab a b) c,
              Term_Rewriting.Term (Labelings.Lab a b) c)],
            ([(Term_Rewriting.Term (Labelings.Lab a b) c,
                Term_Rewriting.Term (Labelings.Lab a b) c)],
              ([Term_Rewriting.Term (Labelings.Lab a b) c],
                ([(Term_Rewriting.Term (Labelings.Lab a b) c,
                    Term_Rewriting.Term (Labelings.Lab a b) c)],
                  [(Term_Rewriting.Term (Labelings.Lab a b) c,
                     Term_Rewriting.Term (Labelings.Lab a b) c)]))))))
      [Check_Termination_Common.Generic_assm_proof a b c
         (Trs_termination_proof a b c) (Dp_termination_proof a b c)
         (Fptrs_termination_proof a b c) () (Unknown_proof a b c)]
  | Q_Reduction_Proc [Term_Rewriting.Term (Labelings.Lab a b) c]
      (Dp_termination_proof a b c)
  | Complex_Constant_Removal_Proc
      (Complex_Constant_Removal_Impl.Complex_constant_removal_prf
        (Labelings.Lab a b) c)
      (Dp_termination_proof a b c)
  | General_Redpair_Proc
      (Reduction_Pair_Implementations.Redtriple_impl (Labelings.Lab a b))
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      (Bounded_Increase_Impl.Cond_red_pair_prf (Labelings.Lab a b) c)
      [Dp_termination_proof a b c]
  | To_Trs_Proc (Trs_termination_proof a b c);

mk_tp ::
  forall a b c d.
    Termination_Problem_Spec.Tp_ops_ext a b c d ->
      (Bool,
        ([Term_Rewriting.Term b c],
          ([(Term_Rewriting.Term b c, Term_Rewriting.Term b c)],
            [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)]))) ->
        a;
mk_tp i (nfs, (q, (r, rw))) = Termination_Problem_Spec.mk i nfs q r rw;

mk_dpp ::
  forall a b c d.
    Dependency_Pair_Problem_Spec.Dpp_ops_ext a b c d ->
      (Bool,
        (Bool,
          ([(Term_Rewriting.Term b c, Term_Rewriting.Term b c)],
            ([(Term_Rewriting.Term b c, Term_Rewriting.Term b c)],
              ([Term_Rewriting.Term b c],
                ([(Term_Rewriting.Term b c, Term_Rewriting.Term b c)],
                  [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)])))))) ->
        a;
mk_dpp i (nfs, (m, (p, (pw, (q, (r, rw)))))) =
  Dependency_Pair_Problem_Spec.mk i nfs m p pw q r rw;

check_assm ::
  forall a b c d e f g.
    (Compare.Compare_order b, Countable.Countable b,
      Term_Rewriting.Showl b) => Termination_Problem_Spec.Tp_ops_ext a
                                   (Labelings.Lab b [Arith.Nat]) [Arith.Char]
                                   () ->
                                   Dependency_Pair_Problem_Spec.Dpp_ops_ext c
                                     (Labelings.Lab b [Arith.Nat]) [Arith.Char]
                                     () ->
                                     (a -> d ->
     Sum_Type.Sum (String -> String) ()) ->
                                       (c ->
 e -> Sum_Type.Sum (String -> String) ()) ->
 (([(Term_Rewriting.Actxt (Labelings.Lab b [Arith.Nat])
       (Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char]),
      (Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
        Term_Rewriting.Location))],
    [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
       Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])]) ->
   f -> Sum_Type.Sum (String -> String) ()) ->
   ([Arith.Char] -> g -> Sum_Type.Sum (String -> String) ()) ->
     Check_Termination_Common.Generic_assm_proof b [Arith.Nat] [Arith.Char] d e
       f () g ->
       Sum_Type.Sum (String -> String) ();
check_assm j i tp_check dp_check fptp_check unk_check
  (Check_Termination_Common.SN_assm_proof t prf) = tp_check (mk_tp j t) prf;
check_assm j i tp_check dp_check fptp_check unk_check
  (Check_Termination_Common.Finite_assm_proof t prf) =
  dp_check (mk_dpp i t) prf;
check_assm j i tp_check dp_check fptp_check unk_check
  (Check_Termination_Common.Unknown_assm_proof t prf) = unk_check t prf;
check_assm j i tp_check dp_check fptp_check unk_check
  (Check_Termination_Common.SN_FP_assm_proof t prf) = fptp_check t prf;
check_assm j i uu uv uw ux (Check_Termination_Common.Not_SN_assm_proof v va) =
  Sum_Type.Inl
    (Term_Rewriting.showsl_lit
      "no support for non-termination assumptions in termination proof");
check_assm j i uu uv uw ux (Check_Termination_Common.Infinite_assm_proof v va) =
  Sum_Type.Inl
    (Term_Rewriting.showsl_lit
      "no support for non-termination assumptions in termination proof");
check_assm j i uu uv uw ux (Check_Termination_Common.Not_RelSN_assm_proof v va)
  = Sum_Type.Inl
      (Term_Rewriting.showsl_lit
        "no support for non-termination assumptions in termination proof");
check_assm j i uu uv uw ux (Check_Termination_Common.Not_SN_FP_assm_proof v va)
  = Sum_Type.Inl
      (Term_Rewriting.showsl_lit
        "no support for non-termination assumptions in termination proof");
check_assm j i uu uv uw ux (Check_Termination_Common.Complexity_assm_proof v va)
  = Sum_Type.Inl
      (Term_Rewriting.showsl_lit
        "no support for non-termination assumptions in termination proof");

get_fcc_option ::
  forall a b c.
    Dp_termination_proof a b c ->
      Maybe (Labelings.Lab a b,
              ([Term_Rewriting.Actxt (Labelings.Lab a b)
                  (Term_Rewriting.Term (Labelings.Lab a b) c)],
                ([(Term_Rewriting.Term (Labelings.Lab a b) c,
                    Term_Rewriting.Term (Labelings.Lab a b) c)],
                  ([(Term_Rewriting.Term (Labelings.Lab a b) c,
                      Term_Rewriting.Term (Labelings.Lab a b) c)],
                    Dp_termination_proof a b c))));
get_fcc_option (Fcc_Proc f fcs pb rb prf) = Just (f, (fcs, (pb, (rb, prf))));
get_fcc_option P_is_Empty = Nothing;
get_fcc_option (Subterm_Criterion_Proc v va vb vc) = Nothing;
get_fcc_option (Gen_Subterm_Criterion_Proc v va vb) = Nothing;
get_fcc_option (Redpair_Proc v va vb) = Nothing;
get_fcc_option (Redpair_UR_Proc v va vb vc) = Nothing;
get_fcc_option (Usable_Rules_Proc v va) = Nothing;
get_fcc_option (Dep_Graph_Proc v) = Nothing;
get_fcc_option (Mono_Redpair_Proc v va vb vc) = Nothing;
get_fcc_option (Mono_URM_Redpair_Proc v va vb vc) = Nothing;
get_fcc_option (Mono_Redpair_UR_Proc v va vb vc vd) = Nothing;
get_fcc_option (Size_Change_Subterm_Proc v) = Nothing;
get_fcc_option (Size_Change_Redpair_Proc v va vb) = Nothing;
get_fcc_option (Uncurry_Proc v va vb vc vd) = Nothing;
get_fcc_option (Split_Proc v va vb vc) = Nothing;
get_fcc_option (Semlab_Proc v va vb vc vd) = Nothing;
get_fcc_option (Switch_Innermost_Proc v va) = Nothing;
get_fcc_option (Rewriting_Proc v va vb vc vd ve vf) = Nothing;
get_fcc_option (Instantiation_Proc v va vb) = Nothing;
get_fcc_option (Forward_Instantiation_Proc v va vb vc) = Nothing;
get_fcc_option (Narrowing_Proc v va vb vc) = Nothing;
get_fcc_option (Assume_Finite v va) = Nothing;
get_fcc_option (Q_Reduction_Proc v va) = Nothing;
get_fcc_option (Complex_Constant_Removal_Proc v va) = Nothing;
get_fcc_option (General_Redpair_Proc v va vb vc vd) = Nothing;
get_fcc_option (To_Trs_Proc v) = Nothing;

check_compatible_nfs ::
  forall a b.
    (Term_Rewriting.Showl a, Eq b,
      Term_Rewriting.Showl b) => Bool ->
                                   (Term_Rewriting.Term a b -> Bool) ->
                                     [(Term_Rewriting.Term a b,
Term_Rewriting.Term a b)] ->
                                       Bool ->
 [Term_Rewriting.Term a b] -> Bool;
check_compatible_nfs nfs1 nf1 r1 nfs2 q2 =
  nfs1 == nfs2 ||
    (null q2 ||
      Error_Monad.isOK (Q_Restricted_Rewriting_Impl.check_wwf_qtrs nf1 r1));

check_tp_subsumes ::
  forall a b c d.
    (Eq b, Term_Rewriting.Showl b, Eq c, Term_Rewriting.Showl c, Eq d,
      Term_Rewriting.Showl d) => Termination_Problem_Spec.Tp_ops_ext a
                                   (Labelings.Lab b c) d () ->
                                   (Bool,
                                     ([Term_Rewriting.Term (Labelings.Lab b c)
 d],
                                       ([(Term_Rewriting.Term
    (Labelings.Lab b c) d,
   Term_Rewriting.Term (Labelings.Lab b c) d)],
 [(Term_Rewriting.Term (Labelings.Lab b c) d,
    Term_Rewriting.Term (Labelings.Lab b c) d)]))) ->
                                     a -> Sum_Type.Sum (String -> String) ();
check_tp_subsumes i (nfs, (q, (r, rw))) tp =
  Error_Monad.catch_error
    (let {
       nfsa = Termination_Problem_Spec.nfs i tp;
       qa = Termination_Problem_Spec.is_QNF i tp;
       ra = Termination_Problem_Spec.r i tp;
       rwa = Termination_Problem_Spec.rw i tp;
       rb = r ++ rw;
       nf1 = Termination_Problem_Spec.is_QNF i tp;
     } in Error_Monad.bind
            (Check_Monad.check (check_compatible_nfs nfsa nf1 (ra ++ rwa) nfs q)
              (Term_Rewriting.showsl_lit
                "incompatible substitutions-in-normal-form flags"))
            (\ _ ->
              Error_Monad.bind
                (Error_Monad.catch_error
                  (Q_Restricted_Rewriting_Impl.check_NF_terms_subset qa q)
                  (\ x ->
                    Sum_Type.Inl
                      (Term_Rewriting.showsl_lit
                         "problem with innermost strategy due to term " .
                        Term_Rewriting.showsl_terma x)))
                (\ _ ->
                  Error_Monad.bind
                    (Error_Monad.catch_error (Check_Monad.check_subseteq ra r)
                      (\ x ->
                        Sum_Type.Inl
                          (Check_Termination_Common.toomuch "rule"
                            (Term_Rewriting.showsl_rule x))))
                    (\ _ ->
                      Error_Monad.bind
                        (Error_Monad.catch_error
                          (Check_Monad.check_subseteq rwa rb)
                          (\ x ->
                            Sum_Type.Inl
                              (Check_Termination_Common.toomuch "relative rule"
                                (Term_Rewriting.showsl_rule x))))
                        (\ _ -> Sum_Type.Inr ())))))
    (\ x ->
      Sum_Type.Inl
        ((((((Term_Rewriting.showsl_lit "termination of the problem\n" .
               QDP_Framework_Impl.showsl_tp i tp) .
              Term_Rewriting.showsl_lit
                "\nmay not be concluded from assuming termination of the problem\n") .
             QDP_Framework_Impl.showsl_tp i
               (Termination_Problem_Spec.mk i nfs q r rw)) .
            Term_Rewriting.showsl_literal "\n") .
           x) .
          Term_Rewriting.showsl_literal "\n"));

check_dpp_subsumes ::
  forall a b c d.
    (Compare.Compare_order b, Eq b, Term_Rewriting.Showl b,
      Compare.Compare_order c, Eq c, Term_Rewriting.Showl c, Arith.Ccompare d,
      Eq d, Mapping.Mapping_impl d,
      Term_Rewriting.Showl d) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a
                                   (Labelings.Lab b c) d () ->
                                   (Bool,
                                     (Bool,
                                       ([(Term_Rewriting.Term
    (Labelings.Lab b c) d,
   Term_Rewriting.Term (Labelings.Lab b c) d)],
 ([(Term_Rewriting.Term (Labelings.Lab b c) d,
     Term_Rewriting.Term (Labelings.Lab b c) d)],
   ([Term_Rewriting.Term (Labelings.Lab b c) d],
     ([(Term_Rewriting.Term (Labelings.Lab b c) d,
         Term_Rewriting.Term (Labelings.Lab b c) d)],
       [(Term_Rewriting.Term (Labelings.Lab b c) d,
          Term_Rewriting.Term (Labelings.Lab b c) d)])))))) ->
                                     a -> Sum_Type.Sum (String -> String) ();
check_dpp_subsumes i (nfs, (m, (p, (pw, (q, (r, rw)))))) d =
  Error_Monad.catch_error
    (let {
       pa = Dependency_Pair_Problem_Spec.p i d;
       pwa = Dependency_Pair_Problem_Spec.pw i d;
       qa = Dependency_Pair_Problem_Spec.q i d;
       ra = Dependency_Pair_Problem_Spec.r i d;
       rwa = Dependency_Pair_Problem_Spec.rw i d;
       nfsa = Dependency_Pair_Problem_Spec.nfs i d;
       ma = Dependency_Pair_Problem_Spec.minimal i d;
       pb = p ++ pw;
       rb = ra ++ rwa;
       rba = r ++ rw;
     } in Error_Monad.bind
            (Check_Monad.check (ma == m)
              (Term_Rewriting.showsl_lit "incompatible minimality flags"))
            (\ _ ->
              Error_Monad.bind
                (Check_Monad.check (nfsa == nfs)
                  (Term_Rewriting.showsl_lit
                    "incompatible substitutions-in-normal-form flags"))
                (\ _ ->
                  Error_Monad.bind
                    (Error_Monad.catch_error (Check_Monad.check_subseteq pa p)
                      (\ x ->
                        Sum_Type.Inl
                          (Check_Termination_Common.toomuch "pair"
                            (Term_Rewriting.showsl_rule x))))
                    (\ _ ->
                      Error_Monad.bind
                        (Error_Monad.catch_error
                          (Check_Monad.check_subseteq pwa pb)
                          (\ x ->
                            Sum_Type.Inl
                              (Check_Termination_Common.toomuch "weak pair"
                                (Term_Rewriting.showsl_rule x))))
                        (\ _ ->
                          Error_Monad.bind
                            (Error_Monad.catch_error
                              (Q_Restricted_Rewriting_Impl.check_NF_terms_eq qa
                                q)
                              (\ x ->
                                Sum_Type.Inl
                                  (Term_Rewriting.showsl_lit
                                     "NF(Q) differs due to term " .
                                    Term_Rewriting.showsl_terma x)))
                            (\ _ ->
                              Error_Monad.bind
                                (Error_Monad.catch_error
                                  (Check_Monad.check_subseteq ra r)
                                  (\ x ->
                                    Sum_Type.Inl
                                      (Check_Termination_Common.toomuch
"strict rule" (Term_Rewriting.showsl_rule x))))
                                (\ _ ->
                                  Error_Monad.bind
                                    (Error_Monad.catch_error
                                      (Check_Monad.check_subseteq rb rba)
                                      (\ x ->
Sum_Type.Inl
  (Check_Termination_Common.toomuch "strict/weak rule"
    (Term_Rewriting.showsl_rule x))))
                                    (\ _ ->
                                      Error_Monad.bind
(Error_Monad.catch_error (Check_Monad.check_subseteq rba rb)
  (\ x ->
    Sum_Type.Inl
      (Check_Termination_Common.missing "strict/weak rule"
        (Term_Rewriting.showsl_rule x))))
(\ _ -> Sum_Type.Inr ())))))))))
    (\ x ->
      Sum_Type.Inl
        ((((((Term_Rewriting.showsl_lit "finiteness of the problem\n" .
               QDP_Framework_Impl.showsl_dpp i d) .
              Term_Rewriting.showsl_lit
                "\nmay not be concluded from assuming finiteness of the problem\n") .
             QDP_Framework_Impl.showsl_dpp i
               (Dependency_Pair_Problem_Spec.mk i nfs m p pw q r rw)) .
            Term_Rewriting.showsl_literal "\n") .
           x) .
          Term_Rewriting.showsl_literal "\n"));

check_unknown_proof ::
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
 [Arith.Char] ->
   Unknown_proof b [Arith.Nat] [Arith.Char] ->
     Sum_Type.Sum (String -> String) ();
check_unknown_proof j ia assms i tpa (Assume_Unknown tp ass) =
  FOR_Preliminaries.debug i "Unknown Proof"
    (if assms
      then Error_Monad.bind
             (Error_Monad.catch_error
               (Check_Monad.check (tpa == tp)
                 ((((Term_Rewriting.showsl_lit
                       "unknown problems are not identical: \n" .
                      Term_Rewriting.showsl_lista tpa) .
                     Term_Rewriting.showsl_literal "\n") .
                    Term_Rewriting.showsl_lit " vs \n") .
                   Term_Rewriting.showsl_lista tp))
               (\ x ->
                 Sum_Type.Inl
                   (((i . Term_Rewriting.showsl_lit
                            ": error in termination assumption or unknown proof\n") .
                      x) .
                     Term_Rewriting.showsl_literal "\n")))
             (\ _ ->
               Error_Monad.catch_error
                 (Error_Monad.forallM_index
                   (\ asa ja ->
                     check_assm j ia
                       (check_trs_termination_proof j ia assms
                         (Term_Rewriting.add_index i (Arith.suc ja)))
                       (check_dp_termination_proof j ia assms
                         (Term_Rewriting.add_index i (Arith.suc ja)))
                       (check_fptrs_termination_proof j ia assms
                         (Term_Rewriting.add_index i (Arith.suc ja)))
                       (check_unknown_proof j ia assms
                         (Term_Rewriting.add_index i (Arith.suc ja)))
                       asa)
                   ass)
                 (\ x -> Sum_Type.Inl (snd x)))
      else Sum_Type.Inl
             (i . Term_Rewriting.showsl_lit
                    ": the proof contains an unknown proof\n"));

check_fptrs_termination_proof ::
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
 ([(Term_Rewriting.Actxt (Labelings.Lab b [Arith.Nat])
      (Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char]),
     (Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
       Term_Rewriting.Location))],
   [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
      Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])]) ->
   Fptrs_termination_proof b [Arith.Nat] [Arith.Char] ->
     Sum_Type.Sum (String -> String) ();
check_fptrs_termination_proof j ia assms i tpa (Assume_FP_SN tp ass) =
  FOR_Preliminaries.debug i "Outermost Termination Assumption or Unknown Proof"
    (if assms
      then Error_Monad.bind
             (Check_Monad.check (tpa == tp)
               (Term_Rewriting.showsl_lit
                 "outermost assumption does not match current goal"))
             (\ _ ->
               Error_Monad.catch_error
                 (Error_Monad.forallM_index
                   (\ asa ja ->
                     check_assm j ia
                       (check_trs_termination_proof j ia assms
                         (Term_Rewriting.add_index i (Arith.suc ja)))
                       (check_dp_termination_proof j ia assms
                         (Term_Rewriting.add_index i (Arith.suc ja)))
                       (check_fptrs_termination_proof j ia assms
                         (Term_Rewriting.add_index i (Arith.suc ja)))
                       (check_unknown_proof j ia assms
                         (Term_Rewriting.add_index i (Arith.suc ja)))
                       asa)
                   ass)
                 (\ x -> Sum_Type.Inl (snd x)))
      else Sum_Type.Inl
             (i . Term_Rewriting.showsl_lit
                    ": the proof contains a termination assumption or unknown proof\n"));

check_trs_termination_proof ::
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
 a -> Trs_termination_proof b [Arith.Nat] [Arith.Char] ->
        Sum_Type.Sum (String -> String) ();
check_trs_termination_proof j ia assms i tp R_is_Empty =
  FOR_Preliminaries.debug i "R is empty"
    (if null (Termination_Problem_Spec.r j tp) then Sum_Type.Inr ()
      else Sum_Type.Inl
             ((i . Term_Rewriting.showsl_lit
                     ": R is not empty in the following termination-problem \n") .
               QDP_Framework_Impl.showsl_tp j tp));
check_trs_termination_proof j ia assms i tp (Rule_Removal redp rr prf) =
  FOR_Preliminaries.debug i "Rule Removal"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (Reduction_Pair_Proc_Impl.rule_removal_tt j
          (Reduction_Pair_Implementations.get_rel_impl redp) rr tp)
        (\ x ->
          Sum_Type.Inl
            ((((((i . Term_Rewriting.showsl_lit
                        ": error when applying the rule removal technique on \n") .
                  QDP_Framework_Impl.showsl_tp j tp) .
                 Term_Rewriting.showsl_lit "\n to remove the rules \n") .
                Term_Rewriting.showsl_rules rr) .
               Term_Rewriting.showsl_literal "\n") .
              x)))
      (\ tpa ->
        Error_Monad.catch_error
          (check_trs_termination_proof j ia assms
            (Term_Rewriting.add_index i Arith.one_nat) tpa prf)
          (\ x ->
            Sum_Type.Inl
              ((i . Term_Rewriting.showsl_lit
                      ": error below the rule removal technique\n") .
                x))));
check_trs_termination_proof j ia assms i tp (DP_Trans nfs m p prf) =
  FOR_Preliminaries.debug i "DP trans"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (DP_Transformation_Impl.dependency_pairs_tt Labelings.Sharp j ia tp nfs
          m p)
        (\ x ->
          Sum_Type.Inl
            ((((((i . Term_Rewriting.showsl_lit
                        ": error when switching from the TRS\n") .
                  QDP_Framework_Impl.showsl_tp j tp) .
                 Term_Rewriting.showsl_lit
                   "\nto the initial DP problem with pairs \n") .
                Term_Rewriting.showsl_rules p) .
               Term_Rewriting.showsl_literal "\n") .
              x)))
      (\ dpp ->
        Error_Monad.catch_error
          (check_dp_termination_proof j ia assms
            (Term_Rewriting.add_index i Arith.one_nat) dpp prf)
          (\ x ->
            Sum_Type.Inl
              ((i . Term_Rewriting.showsl_lit
                      ": error below switch to dependency pairs\n") .
                x))));
check_trs_termination_proof j ia assms i tp (String_Reversal prf) =
  FOR_Preliminaries.debug i "String Reversal"
    (Error_Monad.bind
      (Error_Monad.catch_error (String_Reversal_Impl.string_reversal_tt j tp)
        (\ x ->
          Sum_Type.Inl
            ((((i . Term_Rewriting.showsl_lit
                      ": error when applying string reversal on \n") .
                QDP_Framework_Impl.showsl_tp j tp) .
               Term_Rewriting.showsl_literal "\n") .
              x)))
      (\ tpa ->
        Error_Monad.catch_error
          (check_trs_termination_proof j ia assms
            (Term_Rewriting.add_index i Arith.one_nat) tpa prf)
          (\ x ->
            Sum_Type.Inl
              ((i . Term_Rewriting.showsl_lit
                      ": error below the string reversal technique\n") .
                x))));
check_trs_termination_proof j ia assms i tp (Constant_String p prf) =
  FOR_Preliminaries.debug i "Constant to Unary"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (Monadic_Rewriting_Impl.const_to_string_sound_tt p j tp)
        (\ x ->
          Sum_Type.Inl
            (((((i . Term_Rewriting.showsl_lit
                       ": error when turning constants into unary symbols on ") .
                 Term_Rewriting.showsl_literal "\n") .
                QDP_Framework_Impl.showsl_tp j tp) .
               Term_Rewriting.showsl_literal "\n") .
              x)))
      (\ tpa ->
        Error_Monad.catch_error
          (check_trs_termination_proof j ia assms
            (Term_Rewriting.add_index i Arith.one_nat) tpa prf)
          (\ x ->
            Sum_Type.Inl
              ((i . Term_Rewriting.showsl_lit
                      ": error below the constant to unary technique\n") .
                x))));
check_trs_termination_proof j ia assms i tp (Semlab sli lQ lAll prf) =
  FOR_Preliminaries.debug i "Semlab"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (Semantic_Labeling_Carrier.semlab_fin_tt j sli lQ lAll tp)
        (\ x ->
          Sum_Type.Inl
            (((((i . Term_Rewriting.showsl_lit
                       ": error when applying semantic labelling on ") .
                 Term_Rewriting.showsl_literal "\n") .
                QDP_Framework_Impl.showsl_tp j tp) .
               Term_Rewriting.showsl_literal "\n") .
              x)))
      (\ tpa ->
        Error_Monad.catch_error
          (check_trs_termination_proof j ia assms
            (Term_Rewriting.add_index i Arith.one_nat) tpa prf)
          (\ x ->
            Sum_Type.Inl
              ((i . Term_Rewriting.showsl_lit
                      ": error below the sem.lab technique\n") .
                x))));
check_trs_termination_proof j ia assms i tp (Bounds info) =
  FOR_Preliminaries.debug i "Bounds"
    (Error_Monad.catch_error (Matchbounds_Impl.bounds_tt j info tp)
      (\ x ->
        Sum_Type.Inl
          ((((i . Term_Rewriting.showsl_lit
                    ": error when applying bounds on the termination problem \n") .
              QDP_Framework_Impl.showsl_tp j tp) .
             Term_Rewriting.showsl_literal "\n") .
            x)));
check_trs_termination_proof j ia assms i tp (Relative_Bounds info rr prf) =
  FOR_Preliminaries.debug i "Relative Bounds"
    (Error_Monad.bind
      (Error_Monad.catch_error (Matchbounds_Impl.bounds_rel_tt j info rr tp)
        (\ x ->
          Sum_Type.Inl
            ((((((i . Term_Rewriting.showsl_lit
                        ": error when applying relative bounds on the termination problem \n") .
                  QDP_Framework_Impl.showsl_tp j tp) .
                 Term_Rewriting.showsl_lit "\n to remove the rules \n") .
                Term_Rewriting.showsl_rules rr) .
               Term_Rewriting.showsl_literal "\n") .
              x)))
      (\ tpa ->
        Error_Monad.catch_error
          (check_trs_termination_proof j ia assms
            (Term_Rewriting.add_index i Arith.one_nat) tpa prf)
          (\ x ->
            Sum_Type.Inl
              ((i . Term_Rewriting.showsl_lit
                      ": error below relative bounds\n") .
                x))));
check_trs_termination_proof j ia assms i tp
  (Rfc_Bounds_Proc RFC_Explicit info initial_terms Nothing) =
  FOR_Preliminaries.debug i "RFC Bounds"
    (Error_Monad.catch_error
      (Matchbounds_Impl.rfc_bounds_tt j info initial_terms tp)
      (\ x ->
        Sum_Type.Inl
          ((((i . Term_Rewriting.showsl_lit
                    ": error when applying RFC bounds on the termination problem \n") .
              QDP_Framework_Impl.showsl_tp j tp) .
             Term_Rewriting.showsl_literal "\n") .
            x)));
check_trs_termination_proof j ia assms i tp
  (Rfc_Bounds_Proc RFC_Automaton_Closed info initial_terms Nothing) =
  FOR_Preliminaries.debug i "RFC Automaton-Closed Bounds"
    (Error_Monad.catch_error
      (RFC_Matchbounds_Ext.rfc_automaton_closed_bounds_tt j info initial_terms
        tp)
      (\ x ->
        Sum_Type.Inl
          ((((i . Term_Rewriting.showsl_lit
                    ": error when applying RFC automaton-closed bounds on the termination problem \n") .
              QDP_Framework_Impl.showsl_tp j tp) .
             Term_Rewriting.showsl_literal "\n") .
            x)));
check_trs_termination_proof j ia assms i tp
  (Rfc_Bounds_Proc RFC_Explicit info initial_terms (Just (rr, prf))) =
  FOR_Preliminaries.debug i "RFC Relative Bounds"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (RFC_Matchbounds_Ext.rfc_relative_bounds_tt j info initial_terms rr tp)
        (\ x ->
          Sum_Type.Inl
            ((((((i . Term_Rewriting.showsl_lit
                        ": error when applying RFC relative bounds on the termination problem \n") .
                  QDP_Framework_Impl.showsl_tp j tp) .
                 Term_Rewriting.showsl_lit "\n to remove the rules \n") .
                Term_Rewriting.showsl_rules rr) .
               Term_Rewriting.showsl_literal "\n") .
              x)))
      (\ tpa ->
        Error_Monad.catch_error
          (check_trs_termination_proof j ia assms
            (Term_Rewriting.add_index i Arith.one_nat) tpa prf)
          (\ x ->
            Sum_Type.Inl
              ((i . Term_Rewriting.showsl_lit
                      ": error below RFC relative bounds\n") .
                x))));
check_trs_termination_proof j ia assms i tp
  (Rfc_Bounds_Proc RFC_Automaton_Closed info initial_terms (Just (rr, prf))) =
  FOR_Preliminaries.debug i "RFC Automaton-Closed Relative Bounds"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (RFC_Matchbounds_Ext.rfc_automaton_closed_relative_bounds_tt j info
          initial_terms rr tp)
        (\ x ->
          Sum_Type.Inl
            ((((((i . Term_Rewriting.showsl_lit
                        ": error when applying RFC automaton-closed relative bounds on the termination problem \n") .
                  QDP_Framework_Impl.showsl_tp j tp) .
                 Term_Rewriting.showsl_lit "\n to remove the rules \n") .
                Term_Rewriting.showsl_rules rr) .
               Term_Rewriting.showsl_literal "\n") .
              x)))
      (\ tpa ->
        Error_Monad.catch_error
          (check_trs_termination_proof j ia assms
            (Term_Rewriting.add_index i Arith.one_nat) tpa prf)
          (\ x ->
            Sum_Type.Inl
              ((i . Term_Rewriting.showsl_lit
                      ": error below RFC automaton-closed relative bounds\n") .
                x))));
check_trs_termination_proof j ia assms i tp (Uncurry u_info rR prf) =
  FOR_Preliminaries.debug i "Uncurry"
    (Error_Monad.bind
      (Error_Monad.catch_error (Uncurry_Impl.uncurry_tt j u_info rR tp)
        (\ x ->
          Sum_Type.Inl
            ((i . Term_Rewriting.showsl_lit
                    ": error when applying currying transformation\n") .
              x)))
      (\ tpa ->
        Error_Monad.catch_error
          (check_trs_termination_proof j ia assms
            (Term_Rewriting.add_index i Arith.one_nat) tpa prf)
          (\ x ->
            Sum_Type.Inl
              ((i . Term_Rewriting.showsl_lit
                      ": error below the uncurrying technique\n") .
                x))));
check_trs_termination_proof j ia assms i tp (Fcc fcs r prf) =
  FOR_Preliminaries.debug i "Fcc"
    (Error_Monad.bind
      (Error_Monad.catch_error (Flat_Context_Closure_Impl.fcc_tt j fcs r tp)
        (\ x ->
          Sum_Type.Inl
            ((i . Term_Rewriting.showsl_lit
                    ": error when applying flat context closure\n") .
              x)))
      (\ tpa ->
        Error_Monad.catch_error
          (check_trs_termination_proof j ia assms
            (Term_Rewriting.add_index i Arith.one_nat) tpa prf)
          (\ x ->
            Sum_Type.Inl
              ((i . Term_Rewriting.showsl_lit
                      ": error below flat context closure\n") .
                x))));
check_trs_termination_proof j ia assms i tp (Split rrem prf1 prf2) =
  FOR_Preliminaries.debug i "Split"
    (case Split_Impl.split_tt j tp rrem of {
      (tp1, tp2) ->
        Error_Monad.bind
          (Error_Monad.catch_error
            (check_trs_termination_proof j ia assms
              (Term_Rewriting.add_index i Arith.one_nat) tp1 prf1)
            (\ x ->
              Sum_Type.Inl
                ((i . Term_Rewriting.showsl_lit
                        ": error below the splitting\n") .
                  x)))
          (\ _ ->
            Error_Monad.catch_error
              (check_trs_termination_proof j ia assms
                (Term_Rewriting.add_index i
                  (Arith.nat_of_integer (2 :: Integer)))
                tp2 prf2)
              (\ x ->
                Sum_Type.Inl
                  ((i . Term_Rewriting.showsl_lit
                          ": error below the splitting\n") .
                    x)));
    });
check_trs_termination_proof j ia assms i tp (Switch_Innermost joins prf) =
  FOR_Preliminaries.debug i "Switch Innermost"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (Innermost_Switch_Impl.switch_innermost_tt
          Renaming2_String.string_rename j joins tp)
        (\ x ->
          Sum_Type.Inl
            ((((i . Term_Rewriting.showsl_lit
                      ": error when switching to innermost on \n") .
                QDP_Framework_Impl.showsl_tp j tp) .
               Term_Rewriting.showsl_literal "\n") .
              x)))
      (\ tpa ->
        Error_Monad.catch_error
          (check_trs_termination_proof j ia assms
            (Term_Rewriting.add_index i Arith.one_nat) tpa prf)
          (\ x ->
            Sum_Type.Inl
              ((i . Term_Rewriting.showsl_lit
                      ": error below the switch to innermost\n") .
                x))));
check_trs_termination_proof j ia assms i tp (Drop_Equality prf) =
  FOR_Preliminaries.debug i "Drop Equality"
    (let {
       tpa = Termination_Problem_Spec.mk j (Termination_Problem_Spec.nfs j tp)
               (Termination_Problem_Spec.q j tp)
               (Termination_Problem_Spec.r j tp)
               (filter (\ (l, r) -> not (Term_Rewriting.equal_term l r))
                 (Termination_Problem_Spec.rw j tp));
     } in Error_Monad.catch_error
            (check_trs_termination_proof j ia assms
              (Term_Rewriting.add_index i Arith.one_nat) tpa prf)
            (\ x ->
              Sum_Type.Inl
                ((i . Term_Rewriting.showsl_lit
                        ": error below dropping equality rules\n") .
                  x)));
check_trs_termination_proof j ia assms i tp (Remove_Nonapplicable_Rules r prf) =
  FOR_Preliminaries.debug i "Removing non-applicable rules"
    (let {
       _ = Termination_Problem_Spec.r j tp;
     } in Error_Monad.bind
            (Error_Monad.catch_error
              (Q_Restricted_Rewriting_Impl.check_non_applicable_rules
                (Termination_Problem_Spec.is_QNF j tp) r)
              (\ x ->
                Sum_Type.Inl
                  ((i . Term_Rewriting.showsl_lit
                          ": error when removing non-applicable rules\n") .
                    Term_Rewriting.showsl_rule x .
                      Term_Rewriting.showsl_lit " is applicable")))
            (\ _ ->
              let {
                tpa = Termination_Problem_Spec.delete_R_Rw j tp r r;
              } in Error_Monad.catch_error
                     (check_trs_termination_proof j ia assms
                       (Term_Rewriting.add_index i Arith.one_nat) tpa prf)
                     (\ x ->
                       Sum_Type.Inl
                         ((i . Term_Rewriting.showsl_lit
                                 ": error below the non-applicable rules removal\n") .
                           x))));
check_trs_termination_proof j ia assms i tp (Permuting_AFS pi prf) =
  FOR_Preliminaries.debug i "Permuting some rules"
    (Error_Monad.bind
      (Error_Monad.catch_error (Argument_Filter_Impl.argument_filter_tt j pi tp)
        (\ x ->
          Sum_Type.Inl
            ((((i . Term_Rewriting.showsl_lit
                      ": error when permuting arguments on \n") .
                QDP_Framework_Impl.showsl_tp j tp) .
               Term_Rewriting.showsl_literal "\n") .
              x)))
      (\ tpa ->
        Error_Monad.catch_error
          (check_trs_termination_proof j ia assms
            (Term_Rewriting.add_index i Arith.one_nat) tpa prf)
          (\ x ->
            Sum_Type.Inl
              ((i . Term_Rewriting.showsl_lit
                      ": error below the permutation of arguments\n") .
                x))));
check_trs_termination_proof j ia assms i tp Right_Ground_Termination =
  FOR_Preliminaries.debug i "Right_Ground_Termination"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (Right_Ground_Termination_Impl.right_ground_tt j tp)
        (\ x ->
          Sum_Type.Inl
            ((((i . Term_Rewriting.showsl_lit
                      ": error when applying right-ground decision procedure \n") .
                QDP_Framework_Impl.showsl_tp j tp) .
               Term_Rewriting.showsl_literal "\n") .
              x)))
      (\ _ -> Sum_Type.Inr ()));
check_trs_termination_proof j ia assms i tpa (Assume_SN tp ass) =
  FOR_Preliminaries.debug i "Termination Assumption or Unknown Proof"
    (if assms
      then Error_Monad.bind
             (Error_Monad.catch_error (check_tp_subsumes j tp tpa)
               (\ x ->
                 Sum_Type.Inl
                   (((i . Term_Rewriting.showsl_lit
                            ": error in termination assumption or unknown proof\n") .
                      x) .
                     Term_Rewriting.showsl_literal "\n")))
             (\ _ ->
               Error_Monad.catch_error
                 (Error_Monad.forallM_index
                   (\ asa ja ->
                     check_assm j ia
                       (check_trs_termination_proof j ia assms
                         (Term_Rewriting.add_index i (Arith.suc ja)))
                       (check_dp_termination_proof j ia assms
                         (Term_Rewriting.add_index i (Arith.suc ja)))
                       (check_fptrs_termination_proof j ia assms
                         (Term_Rewriting.add_index i (Arith.suc ja)))
                       (check_unknown_proof j ia assms
                         (Term_Rewriting.add_index i (Arith.suc ja)))
                       asa)
                   ass)
                 (\ x -> Sum_Type.Inl (snd x)))
      else Sum_Type.Inl
             (i . Term_Rewriting.showsl_lit
                    ": the proof contains a termination assumption or unknown proof\n"));
check_trs_termination_proof j ia assms i tp
  (Rfc_Bounds_Proc RFC_Matchbox info initial_terms (Just (rr, prf))) =
  FOR_Preliminaries.debug i "RFC Matchbox Relative Bounds"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (RFC_Matchbounds_Ext.rfc_matchbox_relative_bounds_tt j info
          initial_terms rr tp)
        (\ x ->
          Sum_Type.Inl
            ((((((i . Term_Rewriting.showsl_lit
                        ": error when applying RFC Matchbox-style relative bounds on the termination problem \n") .
                  QDP_Framework_Impl.showsl_tp j tp) .
                 Term_Rewriting.showsl_lit "\n to remove the rules \n") .
                Term_Rewriting.showsl_rules rr) .
               Term_Rewriting.showsl_literal "\n") .
              x)))
      (\ tpa ->
        Error_Monad.catch_error
          (check_trs_termination_proof j ia assms
            (Term_Rewriting.add_index i Arith.one_nat) tpa prf)
          (\ x ->
            Sum_Type.Inl
              ((i . Term_Rewriting.showsl_lit
                      ": error below RFC Matchbox-style relative bounds\n") .
                x))));
check_trs_termination_proof j ia assms i tp
  (Rfc_Bounds_Proc RFC_Matchbox info initial_terms Nothing) =
  Sum_Type.Inl
    (i . Term_Rewriting.showsl_lit
           ": direct RFC Matchbox bounds are not supported");

check_dp_termination_proof ::
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
 c -> Dp_termination_proof b [Arith.Nat] [Arith.Char] ->
        Sum_Type.Sum (String -> String) ();
check_dp_termination_proof j ia assms i dpp P_is_Empty =
  FOR_Preliminaries.debug i "P is empty"
    (if null (Dependency_Pair_Problem_Spec.p ia dpp) &&
          (null (Dependency_Pair_Problem_Spec.pw ia dpp) ||
            null (Dependency_Pair_Problem_Spec.r ia dpp))
      then Sum_Type.Inr ()
      else Sum_Type.Inl
             ((i . Term_Rewriting.showsl_lit
                     ": P is not empty in the following DP-problem\n") .
               QDP_Framework_Impl.showsl_dpp ia dpp));
check_dp_termination_proof j ia assms i dpp
  (Subterm_Criterion_Proc p rseq pr prf) =
  FOR_Preliminaries.debug i "Subterm_Criterion_Proc"
    (let {
       _ = Dependency_Pair_Problem_Spec.pairs ia dpp;
     } in Error_Monad.bind
            (Error_Monad.catch_error
              (Subterm_Criterion_Impl.subterm_criterion_proc ia p rseq pr dpp)
              (\ x ->
                Sum_Type.Inl
                  ((((((i . Term_Rewriting.showsl_lit
                              ": error when applying the subterm criterion to the DP problem\n") .
                        QDP_Framework_Impl.showsl_dpp ia dpp) .
                       Term_Rewriting.showsl_lit
                         "\nand trying to remove the pairs\n") .
                      Term_Rewriting.showsl_rules pr) .
                     Term_Rewriting.showsl_literal "\n") .
                    x)))
            (\ dppa ->
              Error_Monad.catch_error
                (check_dp_termination_proof j ia assms
                  (Term_Rewriting.add_index i Arith.one_nat) dppa prf)
                (\ x ->
                  Sum_Type.Inl
                    ((i . Term_Rewriting.showsl_lit
                            ": error below the subterm criterion\n") .
                      x))));
check_dp_termination_proof j ia assms i dpp
  (Gen_Subterm_Criterion_Proc p pr prf) =
  FOR_Preliminaries.debug i "Gen_Subterm_Criterion_Proc"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (AC_Subterm_Criterion_Impl.generalized_subterm_proc ia p pr dpp)
        (\ x ->
          Sum_Type.Inl
            ((((((i . Term_Rewriting.showsl_lit
                        ": error when applying the generalized subterm criterion to the DP problem\n") .
                  QDP_Framework_Impl.showsl_dpp ia dpp) .
                 Term_Rewriting.showsl_lit
                   "\nand trying to remove the pairs\n") .
                Term_Rewriting.showsl_rules pr) .
               Term_Rewriting.showsl_literal "\n") .
              x)))
      (\ dppa ->
        Error_Monad.catch_error
          (check_dp_termination_proof j ia assms
            (Term_Rewriting.add_index i Arith.one_nat) dppa prf)
          (\ x ->
            Sum_Type.Inl
              ((i . Term_Rewriting.showsl_lit
                      ": error below the generalized subterm criterion\n") .
                x))));
check_dp_termination_proof j ia assms i dpp (Redpair_Proc redp pr prf) =
  FOR_Preliminaries.debug i "Redpair_Proc"
    (let {
       _ = Dependency_Pair_Problem_Spec.pairs ia dpp;
       proc =
         let {
           rp = Reduction_Pair_Implementations.get_rel_impl redp;
         } in (if Error_Monad.isOK (Term_Rewriting.standard rp)
                then Generic_Reduction_Pair_Processor_Impl.generic_ur_af_redtriple_proc
                       ia rp Nothing
                else Generic_Reduction_Pair_Processor_Impl.generic_ur_af_root_redtriple_proc
                       ia rp Nothing);
     } in Error_Monad.bind
            (Error_Monad.catch_error (proc pr dpp)
              (\ x ->
                Sum_Type.Inl
                  ((((((i . Term_Rewriting.showsl_lit
                              ": error when applying the reduction pair processor to remove from the DP problem\n") .
                        QDP_Framework_Impl.showsl_dpp ia dpp) .
                       Term_Rewriting.showsl_lit "\n the pairs\n") .
                      Term_Rewriting.showsl_rules pr) .
                     Term_Rewriting.showsl_literal "\n") .
                    x)))
            (\ dppa ->
              Error_Monad.catch_error
                (check_dp_termination_proof j ia assms
                  (Term_Rewriting.add_index i Arith.one_nat) dppa prf)
                (\ x ->
                  Sum_Type.Inl
                    ((i . Term_Rewriting.showsl_lit
                            ": error below the reduction pair processor\n") .
                      x))));
check_dp_termination_proof j ia assms i dpp (Usable_Rules_Proc u prf) =
  FOR_Preliminaries.debug i "Usable_Rules_Proc"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (Innermost_Usable_Rules_Impl.usable_rules_proc ia u dpp)
        (\ x ->
          Sum_Type.Inl
            ((((((i . Term_Rewriting.showsl_lit
                        ": error when applying the usable rules processor to restrict the DP problem\n") .
                  QDP_Framework_Impl.showsl_dpp ia dpp) .
                 Term_Rewriting.showsl_lit "\nto the usable rules\n") .
                Term_Rewriting.showsl_rules u) .
               Term_Rewriting.showsl_literal "\n") .
              x)))
      (\ dppa ->
        Error_Monad.catch_error
          (check_dp_termination_proof j ia assms
            (Term_Rewriting.add_index i Arith.one_nat) dppa prf)
          (\ x ->
            Sum_Type.Inl
              ((i . Term_Rewriting.showsl_lit
                      ": error below the usable rules processor\n") .
                x))));
check_dp_termination_proof j ia assms i dpp (Q_Reduction_Proc q prf) =
  FOR_Preliminaries.debug i "Q_Reduction_Proc"
    (Error_Monad.bind
      (Error_Monad.catch_error (Q_Reduction_Impl.q_reduction_proc ia q dpp)
        (\ x ->
          Sum_Type.Inl
            ((i . Term_Rewriting.showsl_lit
                    ": error when applying the Q-reduction processor\n") .
              x)))
      (\ dppa ->
        Error_Monad.catch_error
          (check_dp_termination_proof j ia assms
            (Term_Rewriting.add_index i Arith.one_nat) dppa prf)
          (\ x ->
            Sum_Type.Inl
              ((i . Term_Rewriting.showsl_lit
                      ": error below the Q-reduction processor\n") .
                x))));
check_dp_termination_proof j ia assms i dpp (Mono_Redpair_Proc redp pr rr prf) =
  FOR_Preliminaries.debug i "Mono_Redpair_Proc"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (Reduction_Pair_Proc_Impl.mono_redpair_proc ia
          (Reduction_Pair_Implementations.get_rel_impl redp) pr rr dpp)
        (\ x ->
          Sum_Type.Inl
            ((((((((i . Term_Rewriting.showsl_lit
                          ": error when applying the mono reduction pair processor to remove from the DP problem\n") .
                    QDP_Framework_Impl.showsl_dpp ia dpp) .
                   Term_Rewriting.showsl_lit "\n the pairs\n") .
                  Term_Rewriting.showsl_rules pr) .
                 Term_Rewriting.showsl_lit "\n and the rules\n") .
                Term_Rewriting.showsl_rules rr) .
               Term_Rewriting.showsl_literal "\n") .
              x)))
      (\ dppa ->
        Error_Monad.catch_error
          (check_dp_termination_proof j ia assms
            (Term_Rewriting.add_index i Arith.one_nat) dppa prf)
          (\ x ->
            Sum_Type.Inl
              ((i . Term_Rewriting.showsl_lit
                      ": error below the mono reduction pair processor\n") .
                x))));
check_dp_termination_proof j ia assms i dpp
  (Mono_URM_Redpair_Proc redp pr rr prf) =
  FOR_Preliminaries.debug i "Mono_URM_Redpair_Proc"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (Reduction_Pair_Proc_Impl.mono_urm_redpair_proc ia
          (Reduction_Pair_Implementations.get_rel_impl redp) pr rr dpp)
        (\ x ->
          Sum_Type.Inl
            ((((((((i . Term_Rewriting.showsl_lit
                          ": error when applying the mono reduction pair processor with usable repl. map to remove from the DP problem\n") .
                    QDP_Framework_Impl.showsl_dpp ia dpp) .
                   Term_Rewriting.showsl_lit "\n the pairs\n") .
                  Term_Rewriting.showsl_rules pr) .
                 Term_Rewriting.showsl_lit "\n and the rules\n") .
                Term_Rewriting.showsl_rules rr) .
               Term_Rewriting.showsl_literal "\n") .
              x)))
      (\ dppa ->
        Error_Monad.catch_error
          (check_dp_termination_proof j ia assms
            (Term_Rewriting.add_index i Arith.one_nat) dppa prf)
          (\ x ->
            Sum_Type.Inl
              ((i . Term_Rewriting.showsl_lit
                      ": error below the mono reduction pair processor\n") .
                x))));
check_dp_termination_proof j ia assms i dpp (Dep_Graph_Proc edpts) =
  FOR_Preliminaries.debug i "Dep_Graph_Proc"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (Dependency_Graph_Impl.dep_graph_proc ia dpp edpts)
        (\ x ->
          Sum_Type.Inl
            ((((i . Term_Rewriting.showsl_lit
                      ": error while trying to perform Sctxt_closure-decomposition  on\n") .
                QDP_Framework_Impl.showsl_dpp ia dpp) .
               Term_Rewriting.showsl_literal "\n") .
              x)))
      (\ pdpps ->
        Error_Monad.catch_error
          (Error_Monad.catch_error
            (Error_Monad.forallM_index
              (\ (prof, dppa) ja ->
                check_dp_termination_proof j ia assms
                  (Term_Rewriting.add_index i (Arith.suc ja)) dppa prof)
              pdpps)
            (\ x -> Sum_Type.Inl (snd x)))
          (\ x ->
            Sum_Type.Inl
              ((i . Term_Rewriting.showsl_lit
                      ": error below the dependency graph processor\n") .
                x))));
check_dp_termination_proof j ia assms i dpp (Redpair_UR_Proc redp pr ur prf) =
  FOR_Preliminaries.debug i "Redpair_UR_Proc"
    (let {
       proc =
         let {
           rp = Reduction_Pair_Implementations.get_rel_impl redp;
         } in (if Error_Monad.isOK (Term_Rewriting.standard rp)
                then Generic_Reduction_Pair_Processor_Impl.generic_ur_af_redtriple_proc
                       ia rp (Just ur)
                else Generic_Reduction_Pair_Processor_Impl.generic_ur_af_root_redtriple_proc
                       ia rp (Just ur));
     } in Error_Monad.bind
            (Error_Monad.catch_error (proc pr dpp)
              (\ x ->
                Sum_Type.Inl
                  ((((((i . Term_Rewriting.showsl_lit
                              ": error when applying the reduction pair processor with usable rules to remove from the DP problem\n") .
                        QDP_Framework_Impl.showsl_dpp ia dpp) .
                       Term_Rewriting.showsl_lit "\n the pairs\n") .
                      Term_Rewriting.showsl_rules pr) .
                     Term_Rewriting.showsl_literal "\n") .
                    x)))
            (\ dppa ->
              Error_Monad.catch_error
                (check_dp_termination_proof j ia assms
                  (Term_Rewriting.add_index i Arith.one_nat) dppa prf)
                (\ x ->
                  Sum_Type.Inl
                    ((i . Term_Rewriting.showsl_lit
                            ": error below the reduction pair processor\n") .
                      x))));
check_dp_termination_proof j ia assms i dpp
  (Mono_Redpair_UR_Proc redp pr rr ur prf) =
  FOR_Preliminaries.debug i "Mono_Redpair_UR_Proc"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (Generic_Reduction_Pair_Processor_Impl.generic_mono_ur_redpair_proc ia
          (Reduction_Pair_Implementations.get_rel_impl redp) pr rr ur dpp)
        (\ x ->
          Sum_Type.Inl
            ((((((((i . Term_Rewriting.showsl_lit
                          ": error when applying the mono reduction pair processor with usable rules to remove from the DP problem\n") .
                    QDP_Framework_Impl.showsl_dpp ia dpp) .
                   Term_Rewriting.showsl_lit "\n the pairs\n") .
                  Term_Rewriting.showsl_rules pr) .
                 Term_Rewriting.showsl_lit "\n and the rules\n") .
                Term_Rewriting.showsl_rules rr) .
               Term_Rewriting.showsl_literal "\n") .
              x)))
      (\ dppa ->
        Error_Monad.catch_error
          (check_dp_termination_proof j ia assms
            (Term_Rewriting.add_index i Arith.one_nat) dppa prf)
          (\ x ->
            Sum_Type.Inl
              ((i . Term_Rewriting.showsl_lit
                      ": error below the mono reduction pair processor with usable rules\n") .
                x))));
check_dp_termination_proof j ia assms i dpp (Uncurry_Proc mode u_info p r prf) =
  FOR_Preliminaries.debug i "Uncurry_Proc"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (Uncurry_Impl.uncurry_proc_both ia mode u_info p r dpp)
        (\ x ->
          Sum_Type.Inl
            ((((i . Term_Rewriting.showsl_lit
                      ": error when applying the uncurrying processor on the DP problem\n") .
                QDP_Framework_Impl.showsl_dpp ia dpp) .
               Term_Rewriting.showsl_literal "\n") .
              x)))
      (\ dppa ->
        Error_Monad.catch_error
          (check_dp_termination_proof j ia assms
            (Term_Rewriting.add_index i Arith.one_nat) dppa prf)
          (\ x ->
            Sum_Type.Inl
              ((i . Term_Rewriting.showsl_lit
                      ": error below the uncurrying processor\n") .
                x))));
check_dp_termination_proof j ia assms i dpp (Size_Change_Subterm_Proc graphs) =
  FOR_Preliminaries.debug i "Size_Change_Subterm_Proc"
    (Error_Monad.catch_error
      (Size_Change_Termination_Processors_Impl.sct_subterm_proc ia graphs dpp)
      (\ x ->
        Sum_Type.Inl
          ((((i . Term_Rewriting.showsl_lit
                    ": error when applying the size-change (subterm) processor on the DP problem\n") .
              QDP_Framework_Impl.showsl_dpp ia dpp) .
             Term_Rewriting.showsl_literal "\n") .
            x)));
check_dp_termination_proof j ia assms i dpp
  (Size_Change_Redpair_Proc redp u_opt graphs) =
  FOR_Preliminaries.debug i "Size_Change_Redpair_Proc"
    (Error_Monad.catch_error
      (Size_Change_Termination_Processors_Impl.sct_ur_af_proc ia
        (Reduction_Pair_Implementations.get_rel_impl redp) graphs u_opt dpp)
      (\ x ->
        Sum_Type.Inl
          ((((i . Term_Rewriting.showsl_lit
                    ": error when applying the size-change (redpair) processor on the DP problem\n") .
              QDP_Framework_Impl.showsl_dpp ia dpp) .
             Term_Rewriting.showsl_literal "\n") .
            x)));
check_dp_termination_proof j ia assms i dpp (Fcc_Proc f fcs pb r prf) =
  FOR_Preliminaries.debug i "Fcc_Proc"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (Flat_Context_Closure_Impl.fcc_proc ia f fcs pb r dpp)
        (\ x ->
          Sum_Type.Inl
            ((((i . Term_Rewriting.showsl_lit
                      ": error when applying the flat context closure processor on the DP problem\n") .
                QDP_Framework_Impl.showsl_dpp ia dpp) .
               Term_Rewriting.showsl_literal "\n") .
              x)))
      (\ dppa ->
        Error_Monad.catch_error
          (check_dp_termination_proof j ia assms
            (Term_Rewriting.add_index i Arith.one_nat) dppa prf)
          (\ x ->
            Sum_Type.Inl
              ((i . Term_Rewriting.showsl_lit
                      ": error below the flat context closure processor\n") .
                x))));
check_dp_termination_proof j ia assms i dpp (Split_Proc prem rrem prf1 prf2) =
  FOR_Preliminaries.debug i "Split_Proc"
    (case get_fcc_option prf1 of {
      Nothing ->
        (case Split_Impl.split_proc ia dpp prem rrem of {
          (dpp1, dpp2) ->
            Error_Monad.bind
              (Error_Monad.catch_error
                (check_dp_termination_proof j ia assms
                  (Term_Rewriting.add_index i Arith.one_nat) dpp1 prf1)
                (\ x ->
                  Sum_Type.Inl
                    ((i . Term_Rewriting.showsl_lit
                            ": error below the split processor\n") .
                      x)))
              (\ _ ->
                Error_Monad.catch_error
                  (check_dp_termination_proof j ia assms
                    (Term_Rewriting.add_index i
                      (Arith.nat_of_integer (2 :: Integer)))
                    dpp2 prf2)
                  (\ x ->
                    Sum_Type.Inl
                      ((i . Term_Rewriting.showsl_lit
                              ": error below the split processor\n") .
                        x)));
        });
      Just (f, (fcs, (pb, (rb, prf1a)))) ->
        FOR_Preliminaries.debug i "Split_ProcFcc"
          (Error_Monad.bind
            (Flat_Context_Closure_Impl.fcc_split_proc ia f fcs pb rb prem rrem
              dpp)
            (\ (dpp1, dpp2) ->
              Error_Monad.bind
                (Error_Monad.catch_error
                  (check_dp_termination_proof j ia assms
                    (Term_Rewriting.add_index
                      (Term_Rewriting.add_index i Arith.one_nat) Arith.one_nat)
                    dpp1 prf1a)
                  (\ x ->
                    Sum_Type.Inl
                      ((i . Term_Rewriting.showsl_lit
                              ": error below the split and fcc processor\n") .
                        x)))
                (\ _ ->
                  Error_Monad.catch_error
                    (check_dp_termination_proof j ia assms
                      (Term_Rewriting.add_index i
                        (Arith.nat_of_integer (2 :: Integer)))
                      dpp2 prf2)
                    (\ x ->
                      Sum_Type.Inl
                        ((i . Term_Rewriting.showsl_lit
                                ": error below the split processor\n") .
                          x)))));
    });
check_dp_termination_proof j ia assms i dpp (Semlab_Proc sli lP lQ lR prf) =
  FOR_Preliminaries.debug i "Semlab_Proc"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (Semantic_Labeling_Carrier.semlab_fin_proc ia sli lP lQ lR dpp)
        (\ x ->
          Sum_Type.Inl
            ((((i . Term_Rewriting.showsl_lit
                      ": error when applying the semlab processor on the DP problem\n") .
                QDP_Framework_Impl.showsl_dpp ia dpp) .
               Term_Rewriting.showsl_literal "\n") .
              x)))
      (\ dppa ->
        Error_Monad.catch_error
          (check_dp_termination_proof j ia assms
            (Term_Rewriting.add_index i Arith.one_nat) dppa prf)
          (\ x ->
            Sum_Type.Inl
              ((i . Term_Rewriting.showsl_lit
                      ": error below the semlab processor\n") .
                x))));
check_dp_termination_proof j ia assms i dpp (Switch_Innermost_Proc joins prf) =
  FOR_Preliminaries.debug i "Switch_Innermost_Proc"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (Innermost_Switch_Impl.switch_innermost_proc
          Renaming2_String.string_rename ia joins dpp)
        (\ x ->
          Sum_Type.Inl
            ((((i . Term_Rewriting.showsl_lit
                      ": error when applying the processor to switch to innermost on the DP problem\n") .
                QDP_Framework_Impl.showsl_dpp ia dpp) .
               Term_Rewriting.showsl_literal "\n") .
              x)))
      (\ dppa ->
        Error_Monad.catch_error
          (check_dp_termination_proof j ia assms
            (Term_Rewriting.add_index i Arith.one_nat) dppa prf)
          (\ x ->
            Sum_Type.Inl
              ((i . Term_Rewriting.showsl_lit
                      ": error below the switch to innermost processor\n") .
                x))));
check_dp_termination_proof j ia assms i dppa (Assume_Finite dpp ass) =
  FOR_Preliminaries.debug i "Finiteness Assumption or Unknown Proof"
    (if assms
      then Error_Monad.bind
             (Error_Monad.catch_error (check_dpp_subsumes ia dpp dppa)
               (\ x ->
                 Sum_Type.Inl
                   (((i . Term_Rewriting.showsl_lit
                            ": error in finiteness assumption or unknown proof\n") .
                      x) .
                     Term_Rewriting.showsl_literal "\n")))
             (\ _ ->
               Error_Monad.catch_error
                 (Error_Monad.catch_error
                   (Error_Monad.forallM_index
                     (\ asa ja ->
                       check_assm j ia
                         (check_trs_termination_proof j ia assms
                           (Term_Rewriting.add_index i (Arith.suc ja)))
                         (check_dp_termination_proof j ia assms
                           (Term_Rewriting.add_index i (Arith.suc ja)))
                         (check_fptrs_termination_proof j ia assms
                           (Term_Rewriting.add_index i (Arith.suc ja)))
                         (check_unknown_proof j ia assms
                           (Term_Rewriting.add_index i (Arith.suc ja)))
                         asa)
                     ass)
                   (\ x -> Sum_Type.Inl (snd x)))
                 (\ x ->
                   Sum_Type.Inl
                     ((i . Term_Rewriting.showsl_lit
                             ": error below unknown proof\n") .
                       x)))
      else Sum_Type.Inl
             (i . Term_Rewriting.showsl_lit
                    ": the proof contains a finiteness assumption or unknown proof\n"));
check_dp_termination_proof j ia assms i dpp
  (Rewriting_Proc u_opt stb sta st lr p prf) =
  FOR_Preliminaries.debug i "Rewriting_Proc"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (Rewriting_Impl.rewriting_proc ia u_opt stb sta st lr p dpp)
        (\ x ->
          Sum_Type.Inl
            ((((((i . Term_Rewriting.showsl_lit
                        ": error when applying the rewriting processor to rewrite the pair \n") .
                  Term_Rewriting.showsl_rule stb) .
                 Term_Rewriting.showsl_lit "\n to the pair \n") .
                Term_Rewriting.showsl_rule st) .
               Term_Rewriting.showsl_literal "\n") .
              x)))
      (\ dppa ->
        Error_Monad.catch_error
          (check_dp_termination_proof j ia assms
            (Term_Rewriting.add_index i Arith.one_nat) dppa prf)
          (\ x ->
            Sum_Type.Inl
              ((i . Term_Rewriting.showsl_lit
                      ": error below the rewriting processor\n") .
                x))));
check_dp_termination_proof j ia assms i dpp (Narrowing_Proc st p sts prf) =
  FOR_Preliminaries.debug i "Narrowing_Proc"
    (Error_Monad.bind
      (Error_Monad.catch_error (Narrowing_Impl.narrowing_proc ia st p sts dpp)
        (\ x ->
          Sum_Type.Inl
            ((((((i . Term_Rewriting.showsl_lit
                        ": error when applying the narrowing processor to narrow the pair \n") .
                  Term_Rewriting.showsl_rule st) .
                 Term_Rewriting.showsl_lit "\n to the pairs \n") .
                Term_Rewriting.showsl_trs sts) .
               Term_Rewriting.showsl_literal "\n") .
              x)))
      (\ dppa ->
        Error_Monad.catch_error
          (check_dp_termination_proof j ia assms
            (Term_Rewriting.add_index i Arith.one_nat) dppa prf)
          (\ x ->
            Sum_Type.Inl
              ((i . Term_Rewriting.showsl_lit
                      ": error below the narrowing processor\n") .
                x))));
check_dp_termination_proof j ia assms i dpp (Instantiation_Proc st sts prf) =
  FOR_Preliminaries.debug i "Instantiation_Proc"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (Instantiation_Impl.instantiation_proc ia st sts dpp)
        (\ x ->
          Sum_Type.Inl
            ((((((i . Term_Rewriting.showsl_lit
                        ": error when applying the instantiation processor to instantiate the pair \n") .
                  Term_Rewriting.showsl_rule st) .
                 Term_Rewriting.showsl_lit "\n to the pairs \n") .
                Term_Rewriting.showsl_trs sts) .
               Term_Rewriting.showsl_literal "\n") .
              x)))
      (\ dppa ->
        Error_Monad.catch_error
          (check_dp_termination_proof j ia assms
            (Term_Rewriting.add_index i Arith.one_nat) dppa prf)
          (\ x ->
            Sum_Type.Inl
              ((i . Term_Rewriting.showsl_lit
                      ": error below the instantiation processor\n") .
                x))));
check_dp_termination_proof j ia assms i dpp
  (Forward_Instantiation_Proc st sts u_opt prf) =
  FOR_Preliminaries.debug i "Forward_Instantiation_Proc"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (Instantiation_Impl.forward_instantiation_proc ia st sts u_opt dpp)
        (\ x ->
          Sum_Type.Inl
            ((((((i . Term_Rewriting.showsl_lit
                        ": error when applying the forward_instantiation processor to instantiate the pair \n") .
                  Term_Rewriting.showsl_rule st) .
                 Term_Rewriting.showsl_lit "\n to the pairs \n") .
                Term_Rewriting.showsl_trs sts) .
               Term_Rewriting.showsl_literal "\n") .
              x)))
      (\ dppa ->
        Error_Monad.catch_error
          (check_dp_termination_proof j ia assms
            (Term_Rewriting.add_index i Arith.one_nat) dppa prf)
          (\ x ->
            Sum_Type.Inl
              ((i . Term_Rewriting.showsl_lit
                      ": error below the forward instantiation processor\n") .
                x))));
check_dp_termination_proof j ia assms i dpp
  (General_Redpair_Proc rp ps pb prof prfs) =
  FOR_Preliminaries.debug i "General_Redpair_ProcProc"
    (let {
       n = Arith.size_list prfs;
     } in Error_Monad.bind
            (Check_Monad.check (Arith.less_nat Arith.zero_nat n)
              (Term_Rewriting.showsl_lit "at least one subproof is required"))
            (\ _ ->
              let {
                merge = Arith.equal_nat n Arith.one_nat;
              } in Error_Monad.bind
                     (Error_Monad.catch_error
                       (Bounded_Increase_Impl.conditional_general_reduction_pair_proc
                         ia (Reduction_Pair_Implementations.get_non_inf_order
                              rp)
                         ps pb prof merge dpp)
                       (\ x ->
                         Sum_Type.Inl
                           ((((i . Term_Rewriting.showsl_lit
                                     ": error when applying the generic reduction pair processor to the DP problem\n") .
                               QDP_Framework_Impl.showsl_dpp ia dpp) .
                              Term_Rewriting.showsl_literal "\n") .
                             x)))
                     (\ dpps ->
                       Error_Monad.bind
                         (Error_Monad.catch_error
                           (check_dp_termination_proof j ia assms
                             (Term_Rewriting.add_index i Arith.one_nat)
                             (Arith.nth dpps Arith.zero_nat)
                             (Arith.nth prfs Arith.zero_nat))
                           (\ x ->
                             Sum_Type.Inl
                               ((i . Term_Rewriting.showsl_lit
                                       ": error below the generic reduction pair processor\n") .
                                 x)))
                         (\ _ ->
                           (if merge then Sum_Type.Inr ()
                             else Error_Monad.catch_error
                                    (check_dp_termination_proof j ia assms
                                      (Term_Rewriting.add_index i
(Arith.nat_of_integer (2 :: Integer)))
                                      (Arith.nth dpps Arith.one_nat)
                                      (Arith.nth prfs Arith.one_nat))
                                    (\ x ->
                                      Sum_Type.Inl
((i . Term_Rewriting.showsl_lit
        ": error below the generic reduction pair processor\n") .
  x)))))));
check_dp_termination_proof j ia assms i dpp
  (Complex_Constant_Removal_Proc p prf) =
  FOR_Preliminaries.debug i "Complex_Constant_Removal_Proc"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (Complex_Constant_Removal_Impl.complex_constant_removal_proc
          Renaming2_String.string_rename ia p dpp)
        (\ x ->
          Sum_Type.Inl
            ((((i . Term_Rewriting.showsl_lit
                      ": error when applying the complex constant removal processor to the DP problem\n") .
                QDP_Framework_Impl.showsl_dpp ia dpp) .
               Term_Rewriting.showsl_literal "\n") .
              x)))
      (\ dppa ->
        Error_Monad.catch_error
          (check_dp_termination_proof j ia assms
            (Term_Rewriting.add_index i Arith.one_nat) dppa prf)
          (\ x ->
            Sum_Type.Inl
              ((i . Term_Rewriting.showsl_lit
                      ": error below the complex constant removal processor\n") .
                x))));
check_dp_termination_proof j ia assms i dpp (To_Trs_Proc prf) =
  FOR_Preliminaries.debug i "To_Trs_Proc"
    (Error_Monad.catch_error
      (check_trs_termination_proof j ia assms
        (Term_Rewriting.add_index i Arith.one_nat)
        (mk_tp j
          (Dependency_Pair_Problem_Spec.nfs ia dpp,
            (Dependency_Pair_Problem_Spec.q ia dpp,
              (Dependency_Pair_Problem_Spec.p ia dpp ++
                 Dependency_Pair_Problem_Spec.r ia dpp,
                Dependency_Pair_Problem_Spec.pw ia dpp ++
                  Dependency_Pair_Problem_Spec.rw ia dpp))))
        prf)
      (\ x ->
        Sum_Type.Inl
          ((i . Term_Rewriting.showsl_lit
                  ": error below the To-Trs processor\n") .
            x)));

}
