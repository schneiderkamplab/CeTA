{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Check_Nontermination(Neg_unknown_proof(..), Reltrs_nontermination_proof(..),
                        Fp_trs_nontermination_proof,
                        Trs_nontermination_proof(..),
                        Dp_nontermination_proof(..), check_unknown_disproof,
                        check_reltrs_nontermination_proof,
                        check_trs_nontermination_proof,
                        check_fp_nontermination_proof,
                        check_dp_nontermination_proof,
                        trs_nontermination_proof_to_fp)
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
import qualified String_Reversal_Impl;
import qualified Forbidden_Pattern_Loops_Impl;
import qualified Termination_Switch_Impl;
import qualified Renaming2_String;
import qualified QDP_Framework_Impl;
import qualified Renaming2;
import qualified Compare_Order_Instances;
import qualified Lists_are_Infinite;
import qualified FOR_Preliminaries;
import qualified Q_Restricted_Rewriting_Impl;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified HOL;
import qualified Labelings_Impl;
import qualified Mapping;
import qualified Complexity;
import qualified Sum_Type;
import qualified Compare;
import qualified Shows_Literal;
import qualified Dependency_Pair_Problem_Spec;
import qualified Termination_Problem_Spec;
import qualified Forbidden_Patterns;
import qualified Monadic_Rewriting_Impl;
import qualified Not_WN_Tree_Automaton_Impl;
import qualified Nonloop_SRS;
import qualified Uncurry_Impl;
import qualified Q_Reduction_Nonterm_Impl;
import qualified Instantiation_Impl;
import qualified Nontermination_Impl;
import qualified Rewriting_Impl;
import qualified Narrowing_Impl;
import qualified Critical_Pairs_Impl;
import qualified Nonloop_Impl;
import qualified Loops_Impl;
import qualified Labelings;
import qualified Term_Rewriting;
import qualified Check_Termination_Common;
import qualified Arith;

data Neg_unknown_proof a b c =
  Assume_NT_Unknown [Arith.Char]
    [Check_Termination_Common.Generic_assm_proof a b c
       (Trs_nontermination_proof a b c) (Dp_nontermination_proof a b c)
       (Reltrs_nontermination_proof a b c) (Fp_trs_nontermination_proof a b c)
       (Neg_unknown_proof a b c)];

data Reltrs_nontermination_proof a b c =
  Rel_Loop (Loops_Impl.Rel_trs_loop_prf (Labelings.Lab a b) c)
  | Rel_TRS_String_Reversal (Reltrs_nontermination_proof a b c)
  | Rel_Not_Well_Formed
  | Rel_Rule_Removal
      (Nontermination_Impl.Rule_removal_nonterm_reltrs_prf (Labelings.Lab a b)
        c)
      (Reltrs_nontermination_proof a b c)
  | Rel_R_Not_SN (Trs_nontermination_proof a b c)
  | Rel_TRS_Assume_Not_SN
      (Bool,
        ([Term_Rewriting.Term (Labelings.Lab a b) c],
          ([(Term_Rewriting.Term (Labelings.Lab a b) c,
              Term_Rewriting.Term (Labelings.Lab a b) c)],
            [(Term_Rewriting.Term (Labelings.Lab a b) c,
               Term_Rewriting.Term (Labelings.Lab a b) c)])))
      [Check_Termination_Common.Generic_assm_proof a b c
         (Trs_nontermination_proof a b c) (Dp_nontermination_proof a b c)
         (Reltrs_nontermination_proof a b c) (Fp_trs_nontermination_proof a b c)
         (Neg_unknown_proof a b c)];

data Fp_trs_nontermination_proof a b c =
  FP_TRS_Loop (Loops_Impl.Trs_loop_prf (Labelings.Lab a b) c)
  | FP_TRS_Rule_Removal
      (Nontermination_Impl.Rule_removal_nonterm_trs_prf (Labelings.Lab a b) c)
      (Fp_trs_nontermination_proof a b c)
  | FPTRS_Assume_Not_SN
      ([(Term_Rewriting.Actxt (Labelings.Lab a b)
           (Term_Rewriting.Term (Labelings.Lab a b) c),
          (Term_Rewriting.Term (Labelings.Lab a b) c,
            Forbidden_Patterns.Location))],
        [(Term_Rewriting.Term (Labelings.Lab a b) c,
           Term_Rewriting.Term (Labelings.Lab a b) c)])
      [Check_Termination_Common.Generic_assm_proof a b c
         (Trs_nontermination_proof a b c) (Dp_nontermination_proof a b c)
         (Reltrs_nontermination_proof a b c) (Fp_trs_nontermination_proof a b c)
         (Neg_unknown_proof a b c)];

data Trs_nontermination_proof a b c =
  TRS_Loop (Loops_Impl.Trs_loop_prf (Labelings.Lab a b) c) | TRS_Not_Well_Formed
  | TRS_Rule_Removal
      (Nontermination_Impl.Rule_removal_nonterm_trs_prf (Labelings.Lab a b) c)
      (Trs_nontermination_proof a b c)
  | TRS_String_Reversal (Trs_nontermination_proof a b c)
  | TRS_Constant_String
      (Monadic_Rewriting_Impl.Const_string_complete_proof (Labelings.Lab a b) c)
      (Trs_nontermination_proof a b c)
  | TRS_DP_Trans (Nontermination_Impl.Dp_trans_nontermination_tt_prf a b c)
      (Dp_nontermination_proof a b c)
  | TRS_Termination_Switch (Critical_Pairs_Impl.Join_info (Labelings.Lab a b) c)
      (Trs_nontermination_proof a b c)
  | TRS_Nonloop (Nonloop_Impl.Non_loop_prf (Labelings.Lab a b) c)
  | TRS_Nonloop_SRS (Nonloop_SRS.Non_loop_srs_proof (Labelings.Lab a b))
  | TRS_Q_Increase
      (Nontermination_Impl.Q_increase_nonterm_trs_prf (Labelings.Lab a b) c)
      (Trs_nontermination_proof a b c)
  | TRS_Uncurry (Uncurry_Impl.Uncurry_nt_proof a b c)
      (Trs_nontermination_proof a b c)
  | TRS_Not_WN_Tree_Automaton
      (Not_WN_Tree_Automaton_Impl.Not_wn_ta_prf (Labelings.Lab a b) c)
  | TRS_Not_RG_Decision
  | TRS_Assume_Not_SN
      (Bool,
        ([Term_Rewriting.Term (Labelings.Lab a b) c],
          [(Term_Rewriting.Term (Labelings.Lab a b) c,
             Term_Rewriting.Term (Labelings.Lab a b) c)]))
      [Check_Termination_Common.Generic_assm_proof a b c
         (Trs_nontermination_proof a b c) (Dp_nontermination_proof a b c)
         (Reltrs_nontermination_proof a b c) (Fp_trs_nontermination_proof a b c)
         (Neg_unknown_proof a b c)];

data Dp_nontermination_proof a b c =
  DP_Loop (Loops_Impl.Dp_loop_prf (Labelings.Lab a b) c)
  | DP_Nonloop (Nonloop_Impl.Non_loop_prf (Labelings.Lab a b) c)
  | DP_Rule_Removal
      (Nontermination_Impl.Rule_removal_nonterm_dp_prf (Labelings.Lab a b) c)
      (Dp_nontermination_proof a b c)
  | DP_Q_Increase
      (Nontermination_Impl.Q_increase_nonterm_dp_prf (Labelings.Lab a b) c)
      (Dp_nontermination_proof a b c)
  | DP_Q_Reduction
      (Q_Reduction_Nonterm_Impl.Dp_q_reduction_nonterm_prf (Labelings.Lab a b)
        c)
      (Dp_nontermination_proof a b c)
  | DP_Termination_Switch (Critical_Pairs_Impl.Join_info (Labelings.Lab a b) c)
      (Dp_nontermination_proof a b c)
  | DP_Instantiation
      (Instantiation_Impl.Instantiation_complete_proc_prf (Labelings.Lab a b) c)
      (Dp_nontermination_proof a b c)
  | DP_Rewriting
      (Rewriting_Impl.Rewriting_complete_proc_prf (Labelings.Lab a b) c)
      (Dp_nontermination_proof a b c)
  | DP_Narrowing
      (Narrowing_Impl.Narrowing_complete_proc_prf (Labelings.Lab a b) c)
      (Dp_nontermination_proof a b c)
  | DP_Assume_Infinite
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
         (Trs_nontermination_proof a b c) (Dp_nontermination_proof a b c)
         (Reltrs_nontermination_proof a b c) (Fp_trs_nontermination_proof a b c)
         (Neg_unknown_proof a b c)];

mk_tp ::
  forall a b c d.
    Termination_Problem_Spec.Tp_ops_ext a b c d ->
      (Bool,
        ([Term_Rewriting.Term b c],
          [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)])) ->
        a;
mk_tp i (nfs, (q, r)) = Termination_Problem_Spec.mk i nfs q r [];

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

mk_rel_tp ::
  forall a b c d.
    Termination_Problem_Spec.Tp_ops_ext a b c d ->
      (Bool,
        ([Term_Rewriting.Term b c],
          ([(Term_Rewriting.Term b c, Term_Rewriting.Term b c)],
            [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)]))) ->
        a;
mk_rel_tp i (nfs, (q, (r, rw))) = Termination_Problem_Spec.mk i nfs q r rw;

check_assm ::
  forall a b c d e f g h i.
    (Compare.Compare_order b, Shows_Literal.Showl b, Compare.Compare_order c,
      Shows_Literal.Showl c) => Termination_Problem_Spec.Tp_ops_ext a
                                  (Labelings.Lab b c) [Arith.Char] () ->
                                  Dependency_Pair_Problem_Spec.Dpp_ops_ext d
                                    (Labelings.Lab b c) [Arith.Char] () ->
                                    (a -> e ->
    Sum_Type.Sum (String -> String) ()) ->
                                      (d ->
f -> Sum_Type.Sum (String -> String) ()) ->
(a -> g -> Sum_Type.Sum (String -> String) ()) ->
  (([(Term_Rewriting.Actxt (Labelings.Lab b c)
        (Term_Rewriting.Term (Labelings.Lab b c) [Arith.Char]),
       (Term_Rewriting.Term (Labelings.Lab b c) [Arith.Char],
         Forbidden_Patterns.Location))],
     [(Term_Rewriting.Term (Labelings.Lab b c) [Arith.Char],
        Term_Rewriting.Term (Labelings.Lab b c) [Arith.Char])]) ->
    h -> Sum_Type.Sum (String -> String) ()) ->
    ([Arith.Char] -> i -> Sum_Type.Sum (String -> String) ()) ->
      Check_Termination_Common.Generic_assm_proof b c [Arith.Char] e f g h i ->
        Sum_Type.Sum (String -> String) ();
check_assm i j tp_check dp_check rtp_check fptp_check unk_check
  (Check_Termination_Common.Not_SN_assm_proof t prf) = tp_check (mk_tp i t) prf;
check_assm i j tp_check dp_check rtp_check fptp_check unk_check
  (Check_Termination_Common.Not_RelSN_assm_proof t prf) =
  rtp_check (mk_rel_tp i t) prf;
check_assm i j tp_check dp_check rtp_check fptp_check unk_check
  (Check_Termination_Common.Infinite_assm_proof t prf) =
  dp_check (mk_dpp j t) prf;
check_assm i j tp_check dp_check rtp_check fptp_check unk_check
  (Check_Termination_Common.Not_SN_FP_assm_proof t prf) = fptp_check t prf;
check_assm i j tp_check dp_check rtp_check fptp_check unk_check
  (Check_Termination_Common.Unknown_assm_proof t prf) = unk_check t prf;
check_assm i j uu uv uw ux uy (Check_Termination_Common.SN_assm_proof v va) =
  Sum_Type.Inl
    (Shows_Literal.showsl_lit
      "no support for termination assumptions in non-termination proof");
check_assm i j uu uv uw ux uy (Check_Termination_Common.Finite_assm_proof v va)
  = Sum_Type.Inl
      (Shows_Literal.showsl_lit
        "no support for termination assumptions in non-termination proof");
check_assm i j uu uv uw ux uy (Check_Termination_Common.SN_FP_assm_proof v va) =
  Sum_Type.Inl
    (Shows_Literal.showsl_lit
      "no support for termination assumptions in non-termination proof");
check_assm i j uu uv uw ux uy
  (Check_Termination_Common.Complexity_assm_proof v va) =
  Sum_Type.Inl
    (Shows_Literal.showsl_lit
      "no support for termination assumptions in non-termination proof");

check_tp_subsumes ::
  forall a b c.
    (Compare.Compare_order b, Eq b, Shows_Literal.Showl b,
      Compare.Compare_order c, Eq c,
      Shows_Literal.Showl c) => Termination_Problem_Spec.Tp_ops_ext a
                                  (Labelings.Lab b c) [Arith.Char] () ->
                                  (Bool,
                                    ([Term_Rewriting.Term (Labelings.Lab b c)
[Arith.Char]],
                                      [(Term_Rewriting.Term (Labelings.Lab b c)
  [Arith.Char],
 Term_Rewriting.Term (Labelings.Lab b c) [Arith.Char])])) ->
                                    a -> Sum_Type.Sum (String -> String) ();
check_tp_subsumes i t tp =
  (case t of {
    (nfs, (q, rs)) ->
      let {
        nfsa = Termination_Problem_Spec.nfs i tp;
        rsa = Termination_Problem_Spec.rules i tp;
        qa = Termination_Problem_Spec.q i tp;
      } in Error_Monad.catch_error
             (Error_Monad.bind
               (Check_Monad.check
                 (if not (null q) then (if nfsa then nfs else True) else True)
                 (Shows_Literal.showsl_lit
                   "incompatible substitutions-in-normal-form flags"))
               (\ _ ->
                 Error_Monad.bind
                   (Error_Monad.catch_error (Check_Monad.check_subseteq rs rsa)
                     (\ x ->
                       Sum_Type.Inl
                         (Check_Termination_Common.toomuch "rule"
                           (Term_Rewriting.showsl_rule x))))
                   (\ _ ->
                     Error_Monad.catch_error
                       (Q_Restricted_Rewriting_Impl.check_NF_terms_subset
                         (Term_Rewriting.is_NF_terms q) qa)
                       (\ x ->
                         Sum_Type.Inl
                           (Shows_Literal.showsl_lit
                              "NF(Q) differs due to term " .
                             Term_Rewriting.showsl_terma x)))))
             (\ x ->
               Sum_Type.Inl
                 (Shows_Literal.showsl_lit
                    "problem in showing subsumption for non-termination\n" .
                   x));
  });

check_dpp_subsumes ::
  forall a b c.
    (Compare.Compare_order b, Eq b, Shows_Literal.Showl b,
      Compare.Compare_order c, Eq c,
      Shows_Literal.Showl c) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a
                                  (Labelings.Lab b c) [Arith.Char] () ->
                                  (Bool,
                                    (Bool,
                                      ([(Term_Rewriting.Term (Labelings.Lab b c)
   [Arith.Char],
  Term_Rewriting.Term (Labelings.Lab b c) [Arith.Char])],
([(Term_Rewriting.Term (Labelings.Lab b c) [Arith.Char],
    Term_Rewriting.Term (Labelings.Lab b c) [Arith.Char])],
  ([Term_Rewriting.Term (Labelings.Lab b c) [Arith.Char]],
    ([(Term_Rewriting.Term (Labelings.Lab b c) [Arith.Char],
        Term_Rewriting.Term (Labelings.Lab b c) [Arith.Char])],
      [(Term_Rewriting.Term (Labelings.Lab b c) [Arith.Char],
         Term_Rewriting.Term (Labelings.Lab b c) [Arith.Char])])))))) ->
                                    a -> Sum_Type.Sum (String -> String) ();
check_dpp_subsumes j dp dpp =
  (case dp of {
    (nfs, (_, (p, (pw, (q, (r, rw)))))) ->
      let {
        pairs = p ++ pw;
        rules = r ++ rw;
        nfsa = Dependency_Pair_Problem_Spec.nfs j dpp;
        pairsa = Dependency_Pair_Problem_Spec.pairs j dpp;
        rulesa = Dependency_Pair_Problem_Spec.rules j dpp;
        qa = Dependency_Pair_Problem_Spec.q j dpp;
      } in Error_Monad.catch_error
             (Error_Monad.bind
               (Check_Monad.check
                 (if not (null q) then (if nfsa then nfs else True) else True)
                 (Shows_Literal.showsl_lit
                   "incompatible substitutions-in-normal-form flags"))
               (\ _ ->
                 Error_Monad.bind
                   (Error_Monad.catch_error
                     (Check_Monad.check_subseteq pairs pairsa)
                     (\ x ->
                       Sum_Type.Inl
                         (Check_Termination_Common.toomuch "pair"
                           (Term_Rewriting.showsl_rule x))))
                   (\ _ ->
                     Error_Monad.bind
                       (Error_Monad.catch_error
                         (Check_Monad.check_subseteq rules rulesa)
                         (\ x ->
                           Sum_Type.Inl
                             (Check_Termination_Common.toomuch "rule"
                               (Term_Rewriting.showsl_rule x))))
                       (\ _ ->
                         Error_Monad.catch_error
                           (Q_Restricted_Rewriting_Impl.check_NF_terms_subset
                             (Term_Rewriting.is_NF_terms q) qa)
                           (\ x ->
                             Sum_Type.Inl
                               (Shows_Literal.showsl_lit
                                  "NF(Q) differs due to term " .
                                 Term_Rewriting.showsl_terma x))))))
             (\ x ->
               Sum_Type.Inl
                 (Shows_Literal.showsl_lit
                    "problem is showing subsumption for non-termination\n" .
                   x));
  });

check_fp_tp_subsumes ::
  forall a b.
    (Compare.Compare_order a, Eq a, Shows_Literal.Showl a,
      Compare.Compare_order b, Eq b,
      Shows_Literal.Showl b) => ([(Term_Rewriting.Actxt (Labelings.Lab a b)
                                     (Term_Rewriting.Term (Labelings.Lab a b)
                                       [Arith.Char]),
                                    (Term_Rewriting.Term (Labelings.Lab a b)
                                       [Arith.Char],
                                      Forbidden_Patterns.Location))],
                                  [(Term_Rewriting.Term (Labelings.Lab a b)
                                      [Arith.Char],
                                     Term_Rewriting.Term (Labelings.Lab a b)
                                       [Arith.Char])]) ->
                                  ([(Term_Rewriting.Actxt (Labelings.Lab a b)
                                       (Term_Rewriting.Term (Labelings.Lab a b)
 [Arith.Char]),
                                      (Term_Rewriting.Term (Labelings.Lab a b)
 [Arith.Char],
Forbidden_Patterns.Location))],
                                    [(Term_Rewriting.Term (Labelings.Lab a b)
[Arith.Char],
                                       Term_Rewriting.Term (Labelings.Lab a b)
 [Arith.Char])]) ->
                                    Sum_Type.Sum (String -> String) ();
check_fp_tp_subsumes ta t =
  (case (ta, t) of {
    ((p, r), (pa, ra)) ->
      Error_Monad.catch_error
        (Error_Monad.bind
          (Check_Monad.check (p == pa)
            (Shows_Literal.showsl_lit
              "difference in forbidden patterns strategy"))
          (\ _ ->
            Error_Monad.catch_error (Check_Monad.check_subseteq r ra)
              (\ x ->
                Sum_Type.Inl
                  (Check_Termination_Common.toomuch "rule"
                    (Term_Rewriting.showsl_rule x)))))
        (\ x ->
          Sum_Type.Inl
            (Shows_Literal.showsl_lit
               "problem in showing subsumption for non-termination\n" .
              x));
  });

check_rel_tp_subsumes ::
  forall a b c.
    (Compare.Compare_order b, Eq b, Shows_Literal.Showl b,
      Compare.Compare_order c, Eq c,
      Shows_Literal.Showl c) => Termination_Problem_Spec.Tp_ops_ext a
                                  (Labelings.Lab b c) [Arith.Char] () ->
                                  (Bool,
                                    ([Term_Rewriting.Term (Labelings.Lab b c)
[Arith.Char]],
                                      ([(Term_Rewriting.Term (Labelings.Lab b c)
   [Arith.Char],
  Term_Rewriting.Term (Labelings.Lab b c) [Arith.Char])],
[(Term_Rewriting.Term (Labelings.Lab b c) [Arith.Char],
   Term_Rewriting.Term (Labelings.Lab b c) [Arith.Char])]))) ->
                                    a -> Sum_Type.Sum (String -> String) ();
check_rel_tp_subsumes i t tp =
  (case t of {
    (nfs, (q, (r, rw))) ->
      let {
        nfsa = Termination_Problem_Spec.nfs i tp;
        rules = Termination_Problem_Spec.rules i tp;
        ra = Termination_Problem_Spec.r i tp;
        qa = Termination_Problem_Spec.q i tp;
      } in Error_Monad.catch_error
             (Error_Monad.bind
               (Check_Monad.check
                 (if not (null q) then (if nfsa then nfs else True) else True)
                 (Shows_Literal.showsl_lit
                   "incompatible substitutions-in-normal-form flags"))
               (\ _ ->
                 Error_Monad.bind
                   (Error_Monad.catch_error
                     (Check_Monad.check_subseteq rw rules)
                     (\ x ->
                       Sum_Type.Inl
                         (Check_Termination_Common.toomuch "rule"
                           (Term_Rewriting.showsl_rule x))))
                   (\ _ ->
                     Error_Monad.bind
                       (Error_Monad.catch_error
                         (Check_Monad.check_subseteq r ra)
                         (\ x ->
                           Sum_Type.Inl
                             (Check_Termination_Common.toomuch "rule"
                               (Term_Rewriting.showsl_rule x))))
                       (\ _ ->
                         Error_Monad.catch_error
                           (Q_Restricted_Rewriting_Impl.check_NF_terms_subset
                             (Term_Rewriting.is_NF_terms q) qa)
                           (\ x ->
                             Sum_Type.Inl
                               (Shows_Literal.showsl_lit
                                  "NF(Q) differs due to term " .
                                 Term_Rewriting.showsl_terma x))))))
             (\ x ->
               Sum_Type.Inl
                 (Shows_Literal.showsl_lit
                    "problem in showing subsumption for non-termination\n" .
                   x));
  });

check_unknown_disproof ::
  forall a b c d.
    (Compare.Compare_order b, HOL.Default b, Eq b, Shows_Literal.Showl b,
      Compare.Compare_order c, Eq c,
      Shows_Literal.Showl c) => Termination_Problem_Spec.Tp_ops_ext a
                                  (Labelings.Lab b c) [Arith.Char] () ->
                                  Dependency_Pair_Problem_Spec.Dpp_ops_ext d
                                    (Labelings.Lab b c) [Arith.Char] () ->
                                    Bool ->
                                      (String -> String) ->
[Arith.Char] ->
  Neg_unknown_proof b c [Arith.Char] -> Sum_Type.Sum (String -> String) ();
check_unknown_disproof ia j assms i tpa (Assume_NT_Unknown tp ass) =
  FOR_Preliminaries.debug i "Unknown Proof"
    (if assms
      then Error_Monad.bind
             (Error_Monad.catch_error
               (Check_Monad.check (tpa == tp)
                 (((Shows_Literal.showsl_lit
                      "unknown problems are not identical:\n" .
                     Shows_Literal.showsl_lista tpa) .
                    Shows_Literal.showsl_lit "\n vs\n") .
                   Shows_Literal.showsl_lista tp))
               (\ x ->
                 Sum_Type.Inl
                   (((i . Shows_Literal.showsl_lit
                            ": error in nontermination assumption or unknown proof\n") .
                      x) .
                     Shows_Literal.showsl_literal "\n")))
             (\ _ ->
               Error_Monad.catch_error
                 (Error_Monad.forallM_index
                   (\ asa ja ->
                     check_assm ia j
                       (check_trs_nontermination_proof ia j assms
                         (Shows_Literal.add_index i (Arith.suc ja)))
                       (check_dp_nontermination_proof ia j assms
                         (Shows_Literal.add_index i (Arith.suc ja)))
                       (check_reltrs_nontermination_proof ia j assms
                         (Shows_Literal.add_index i (Arith.suc ja)))
                       (check_fp_nontermination_proof ia j assms
                         (Shows_Literal.add_index i (Arith.suc ja)))
                       (check_unknown_disproof ia j assms
                         (Shows_Literal.add_index i (Arith.suc ja)))
                       asa)
                   ass)
                 (\ x -> Sum_Type.Inl (snd x)))
      else Sum_Type.Inl
             (i . Shows_Literal.showsl_lit
                    ": the proof contains an unknown proof\n"));

check_reltrs_nontermination_proof ::
  forall a b c d.
    (Compare.Compare_order b, HOL.Default b, Eq b, Shows_Literal.Showl b,
      Compare.Compare_order c, Eq c,
      Shows_Literal.Showl c) => Termination_Problem_Spec.Tp_ops_ext a
                                  (Labelings.Lab b c) [Arith.Char] () ->
                                  Dependency_Pair_Problem_Spec.Dpp_ops_ext d
                                    (Labelings.Lab b c) [Arith.Char] () ->
                                    Bool ->
                                      (String -> String) ->
a -> Reltrs_nontermination_proof b c [Arith.Char] ->
       Sum_Type.Sum (String -> String) ();
check_reltrs_nontermination_proof ia j assms i tp (Rel_Loop p) =
  FOR_Preliminaries.debug i "Loop"
    (Error_Monad.catch_error (Loops_Impl.check_rel_trs_loop ia tp p)
      (\ x ->
        Sum_Type.Inl
          ((i . Shows_Literal.showsl_lit ": error in loop proof\n") . x)));
check_reltrs_nontermination_proof ia j assms i tp (Rel_R_Not_SN prf) =
  Error_Monad.bind (Nontermination_Impl.reltrs_as_trs ia tp)
    (\ tpa ->
      Error_Monad.catch_error
        (check_trs_nontermination_proof ia j assms
          (Shows_Literal.add_index i Arith.one_nat) tpa prf)
        (\ x ->
          Sum_Type.Inl
            ((i . Shows_Literal.showsl_lit
                    ": error below the nontermination proof for R\n") .
              x)));
check_reltrs_nontermination_proof ia j assms i tp Rel_Not_Well_Formed =
  FOR_Preliminaries.debug i "Not Well-Formed"
    (Error_Monad.catch_error (Nontermination_Impl.check_not_wf_reltrs ia tp)
      (\ x ->
        Sum_Type.Inl
          ((i . Shows_Literal.showsl_lit ": error in not-well-formed proof\n") .
            x)));
check_reltrs_nontermination_proof ia j assms i tp (Rel_TRS_String_Reversal prf)
  = FOR_Preliminaries.debug i "String Reversal"
      (Error_Monad.bind
        (Error_Monad.catch_error
          (String_Reversal_Impl.string_reversal_complete_rel_tt ia tp)
          (\ x ->
            Sum_Type.Inl
              ((((i . Shows_Literal.showsl_lit
                        ": error when applying string reversal on\n") .
                  QDP_Framework_Impl.showsl_tp ia tp) .
                 Shows_Literal.showsl_literal "\n") .
                x)))
        (\ tpa ->
          Error_Monad.catch_error
            (check_reltrs_nontermination_proof ia j assms
              (Shows_Literal.add_index i Arith.one_nat) tpa prf)
            (\ x ->
              Sum_Type.Inl
                ((i . Shows_Literal.showsl_lit
                        ": error below the string reversal technique\n") .
                  x))));
check_reltrs_nontermination_proof ia j assms i tp (Rel_Rule_Removal p prf) =
  FOR_Preliminaries.debug i "Rule Removal"
    (Error_Monad.bind (Nontermination_Impl.rule_removal_nonterm_reltrs ia tp p)
      (\ tpa ->
        Error_Monad.catch_error
          (check_reltrs_nontermination_proof ia j assms
            (Shows_Literal.add_index i Arith.one_nat) tpa prf)
          (\ x ->
            Sum_Type.Inl
              ((i . Shows_Literal.showsl_lit
                      ": error below the rule removal\n") .
                x))));
check_reltrs_nontermination_proof ia j assms i tp (Rel_TRS_Assume_Not_SN t ass)
  = FOR_Preliminaries.debug i "Finiteness Assumption or Unknown Proof"
      (if assms
        then Error_Monad.bind
               (Error_Monad.catch_error (check_rel_tp_subsumes ia t tp)
                 (\ x ->
                   Sum_Type.Inl
                     (((i . Shows_Literal.showsl_lit
                              ": error in non-termination assumption or unknown proof\n") .
                        x) .
                       Shows_Literal.showsl_literal "\n")))
               (\ _ ->
                 Error_Monad.catch_error
                   (Error_Monad.catch_error
                     (Error_Monad.forallM_index
                       (\ asa ja ->
                         check_assm ia j
                           (check_trs_nontermination_proof ia j assms
                             (Shows_Literal.add_index i (Arith.suc ja)))
                           (check_dp_nontermination_proof ia j assms
                             (Shows_Literal.add_index i (Arith.suc ja)))
                           (check_reltrs_nontermination_proof ia j assms
                             (Shows_Literal.add_index i (Arith.suc ja)))
                           (check_fp_nontermination_proof ia j assms
                             (Shows_Literal.add_index i (Arith.suc ja)))
                           (check_unknown_disproof ia j assms
                             (Shows_Literal.add_index i (Arith.suc ja)))
                           asa)
                       ass)
                     (\ x -> Sum_Type.Inl (snd x)))
                   (\ x ->
                     Sum_Type.Inl
                       ((i . Shows_Literal.showsl_lit
                               ": error below unknown proof\n") .
                         x)))
        else Sum_Type.Inl
               (i . Shows_Literal.showsl_lit
                      ": the proof contains an assumption or unknown proof\n"));

check_trs_nontermination_proof ::
  forall a b c d.
    (Compare.Compare_order b, HOL.Default b, Eq b, Shows_Literal.Showl b,
      Compare.Compare_order c, Eq c,
      Shows_Literal.Showl c) => Termination_Problem_Spec.Tp_ops_ext a
                                  (Labelings.Lab b c) [Arith.Char] () ->
                                  Dependency_Pair_Problem_Spec.Dpp_ops_ext d
                                    (Labelings.Lab b c) [Arith.Char] () ->
                                    Bool ->
                                      (String -> String) ->
a -> Trs_nontermination_proof b c [Arith.Char] ->
       Sum_Type.Sum (String -> String) ();
check_trs_nontermination_proof ia j assms i tp (TRS_Loop p) =
  FOR_Preliminaries.debug i "Loop"
    (Error_Monad.catch_error (Loops_Impl.check_trs_loop ia tp p)
      (\ x ->
        Sum_Type.Inl
          ((((i . Shows_Literal.showsl_lit ": error when checking loop of\n") .
              QDP_Framework_Impl.showsl_tp ia tp) .
             Shows_Literal.showsl_literal "\n") .
            x)));
check_trs_nontermination_proof ia j assms i tp (TRS_Nonloop p) =
  FOR_Preliminaries.debug i "Nonloop"
    (Error_Monad.catch_error (Nonloop_Impl.check_non_loop_trs_prf ia tp p)
      (\ x ->
        Sum_Type.Inl
          ((Shows_Literal.showsl_lit
              "problem in checking possibly non-looping infinite reduction for\n" .
             QDP_Framework_Impl.showsl_tp ia tp) .
            x)));
check_trs_nontermination_proof ia j assms i tp (TRS_Nonloop_SRS p) =
  FOR_Preliminaries.debug i "Nonloop SRS"
    (Error_Monad.catch_error (Nonloop_SRS.check_non_loop_srs_prf ia tp p)
      (\ x ->
        Sum_Type.Inl
          ((Shows_Literal.showsl_lit
              "problem in checking possibly non-looping infinite reduction for\n" .
             QDP_Framework_Impl.showsl_tp ia tp) .
            x)));
check_trs_nontermination_proof ia j assms i tp TRS_Not_Well_Formed =
  FOR_Preliminaries.debug i "Not Well-Formed"
    (Error_Monad.catch_error (Nontermination_Impl.check_not_wwf_qtrs ia tp)
      (\ x ->
        Sum_Type.Inl
          ((i . Shows_Literal.showsl_lit ": error in not well-formed proof\n") .
            x)));
check_trs_nontermination_proof ia j assms i tp (TRS_Termination_Switch p prf) =
  FOR_Preliminaries.debug i "Switch to Termination"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (Termination_Switch_Impl.switch_termination_tt
          Renaming2_String.string_rename ia p tp)
        (\ x ->
          Sum_Type.Inl
            ((((i . Shows_Literal.showsl_lit
                      ": error in switching to full strategy for the DP-problem\n") .
                QDP_Framework_Impl.showsl_tp ia tp) .
               Shows_Literal.showsl_literal "\n") .
              x)))
      (\ tpa ->
        Error_Monad.catch_error
          (check_trs_nontermination_proof ia j assms
            (Shows_Literal.add_index i Arith.one_nat) tpa prf)
          (\ x ->
            Sum_Type.Inl
              ((i . Shows_Literal.showsl_lit
                      ": error below the termination switch technique\n") .
                x))));
check_trs_nontermination_proof ia j assms i tp (TRS_Rule_Removal p prf) =
  FOR_Preliminaries.debug i "Rule Removal"
    (Error_Monad.bind (Nontermination_Impl.rule_removal_nonterm_trs ia tp p)
      (\ tpa ->
        Error_Monad.catch_error
          (check_trs_nontermination_proof ia j assms
            (Shows_Literal.add_index i Arith.one_nat) tpa prf)
          (\ x ->
            Sum_Type.Inl
              ((i . Shows_Literal.showsl_lit
                      ": error below the rule removal\n") .
                x))));
check_trs_nontermination_proof ia j assms i tp (TRS_String_Reversal prf) =
  FOR_Preliminaries.debug i "String Reversal"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (String_Reversal_Impl.string_reversal_complete_tt ia tp)
        (\ x ->
          Sum_Type.Inl
            ((((i . Shows_Literal.showsl_lit
                      ": error when applying string reversal on\n") .
                QDP_Framework_Impl.showsl_tp ia tp) .
               Shows_Literal.showsl_literal "\n") .
              x)))
      (\ tpa ->
        Error_Monad.catch_error
          (check_trs_nontermination_proof ia j assms
            (Shows_Literal.add_index i Arith.one_nat) tpa prf)
          (\ x ->
            Sum_Type.Inl
              ((i . Shows_Literal.showsl_lit
                      ": error below the string reversal technique\n") .
                x))));
check_trs_nontermination_proof ia j assms i tp (TRS_Constant_String p prf) =
  FOR_Preliminaries.debug i "Constants into Unary"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (Monadic_Rewriting_Impl.const_to_string_complete_tt ia tp p)
        (\ x ->
          Sum_Type.Inl
            ((((i . Shows_Literal.showsl_lit
                      ": error when turning constants into strings on\n") .
                QDP_Framework_Impl.showsl_tp ia tp) .
               Shows_Literal.showsl_literal "\n") .
              x)))
      (\ tpa ->
        Error_Monad.catch_error
          (check_trs_nontermination_proof ia j assms
            (Shows_Literal.add_index i Arith.one_nat) tpa prf)
          (\ x ->
            Sum_Type.Inl
              ((i . Shows_Literal.showsl_lit
                      ": error below the constants into string technique\n") .
                x))));
check_trs_nontermination_proof ia j assms i tp (TRS_DP_Trans p prf) =
  FOR_Preliminaries.debug i "DP Transformation"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (Nontermination_Impl.dp_trans_nontermination_tt ia j tp p)
        (\ x ->
          Sum_Type.Inl
            ((((i . Shows_Literal.showsl_lit
                      ": error in DP transformation on\n") .
                QDP_Framework_Impl.showsl_tp ia tp) .
               Shows_Literal.showsl_literal "\n") .
              x)))
      (\ dpp ->
        Error_Monad.catch_error
          (check_dp_nontermination_proof ia j assms
            (Shows_Literal.add_index i Arith.one_nat) dpp prf)
          (\ x ->
            Sum_Type.Inl
              ((i . Shows_Literal.showsl_lit
                      ": error below the DP transformation\n") .
                x))));
check_trs_nontermination_proof ia j assms i tp (TRS_Q_Increase p prf) =
  FOR_Preliminaries.debug i "Q increase"
    (Error_Monad.bind (Nontermination_Impl.q_increase_nonterm_trs ia tp p)
      (\ tpa ->
        Error_Monad.catch_error
          (check_trs_nontermination_proof ia j assms
            (Shows_Literal.add_index i Arith.one_nat) tpa prf)
          (\ x ->
            Sum_Type.Inl
              ((i . Shows_Literal.showsl_lit
                      ": error below the Q increase technique\n") .
                x))));
check_trs_nontermination_proof ia j assms i tp (TRS_Uncurry p prf) =
  FOR_Preliminaries.debug i "Uncurrying"
    (Error_Monad.bind (Uncurry_Impl.uncurry_nonterm_tt ia p tp)
      (\ tpa ->
        Error_Monad.catch_error
          (check_trs_nontermination_proof ia j assms
            (Shows_Literal.add_index i Arith.one_nat) tpa prf)
          (\ x ->
            Sum_Type.Inl
              ((i . Shows_Literal.showsl_lit
                      ": error below the uncurrying technique\n") .
                x))));
check_trs_nontermination_proof ia j assms i tp (TRS_Not_WN_Tree_Automaton prf) =
  Error_Monad.catch_error
    (Not_WN_Tree_Automaton_Impl.check_not_wn_ta_prf ia tp prf)
    (\ x ->
      Sum_Type.Inl
        ((Shows_Literal.showsl_lit
            "error in tree automaton based non-termination proof for\n" .
           QDP_Framework_Impl.showsl_tp ia tp) .
          x));
check_trs_nontermination_proof ia j assms i tp TRS_Not_RG_Decision =
  Error_Monad.catch_error
    (Right_Ground_Termination_Impl.right_ground_nonterm ia tp)
    (\ x ->
      Sum_Type.Inl
        ((Shows_Literal.showsl_lit
            "error in application of right-ground decision procedure for\n" .
           QDP_Framework_Impl.showsl_tp ia tp) .
          x));
check_trs_nontermination_proof ia j assms i tp (TRS_Assume_Not_SN t ass) =
  FOR_Preliminaries.debug i "Finiteness Assumption or Unknown Proof"
    (if assms
      then Error_Monad.bind
             (Error_Monad.catch_error (check_tp_subsumes ia t tp)
               (\ x ->
                 Sum_Type.Inl
                   (((i . Shows_Literal.showsl_lit
                            ": error in non-termination assumption or unknown proof\n") .
                      x) .
                     Shows_Literal.showsl_literal "\n")))
             (\ _ ->
               Error_Monad.catch_error
                 (Error_Monad.catch_error
                   (Error_Monad.forallM_index
                     (\ asa ja ->
                       check_assm ia j
                         (check_trs_nontermination_proof ia j assms
                           (Shows_Literal.add_index i (Arith.suc ja)))
                         (check_dp_nontermination_proof ia j assms
                           (Shows_Literal.add_index i (Arith.suc ja)))
                         (check_reltrs_nontermination_proof ia j assms
                           (Shows_Literal.add_index i (Arith.suc ja)))
                         (check_fp_nontermination_proof ia j assms
                           (Shows_Literal.add_index i (Arith.suc ja)))
                         (check_unknown_disproof ia j assms
                           (Shows_Literal.add_index i (Arith.suc ja)))
                         asa)
                     ass)
                   (\ x -> Sum_Type.Inl (snd x)))
                 (\ x ->
                   Sum_Type.Inl
                     ((i . Shows_Literal.showsl_lit
                             ": error below unknown proof\n") .
                       x)))
      else Sum_Type.Inl
             (i . Shows_Literal.showsl_lit
                    ": the proof contains an assumption or unknown proof\n"));

check_fp_nontermination_proof ::
  forall a b c d.
    (Compare.Compare_order b, HOL.Default b, Eq b, Shows_Literal.Showl b,
      Compare.Compare_order c, Eq c,
      Shows_Literal.Showl c) => Termination_Problem_Spec.Tp_ops_ext a
                                  (Labelings.Lab b c) [Arith.Char] () ->
                                  Dependency_Pair_Problem_Spec.Dpp_ops_ext d
                                    (Labelings.Lab b c) [Arith.Char] () ->
                                    Bool ->
                                      (String -> String) ->
([(Term_Rewriting.Actxt (Labelings.Lab b c)
     (Term_Rewriting.Term (Labelings.Lab b c) [Arith.Char]),
    (Term_Rewriting.Term (Labelings.Lab b c) [Arith.Char],
      Forbidden_Patterns.Location))],
  [(Term_Rewriting.Term (Labelings.Lab b c) [Arith.Char],
     Term_Rewriting.Term (Labelings.Lab b c) [Arith.Char])]) ->
  Fp_trs_nontermination_proof b c [Arith.Char] ->
    Sum_Type.Sum (String -> String) ();
check_fp_nontermination_proof ia j assms i (pa, r) (FP_TRS_Loop p) =
  (case p of {
    Loops_Impl.TRS_loop_prf a b c d ->
      FOR_Preliminaries.debug i "Loop"
        (Error_Monad.catch_error
          (Forbidden_Pattern_Loops_Impl.check_fploop r pa
            (Forbidden_Pattern_Loops_Impl.FP_loop_prf d c a b))
          (\ x ->
            Sum_Type.Inl
              ((i . Shows_Literal.showsl_lit
                      ": error when checking forbidden pattern loop\n") .
                x)));
  });
check_fp_nontermination_proof ia j assms i (pa, r) (FP_TRS_Rule_Removal p prf) =
  FOR_Preliminaries.debug i "Rule Removal"
    (Error_Monad.bind
      (Nontermination_Impl.rule_removal_nonterm_trs ia
        (Termination_Problem_Spec.mk ia False [] r []) p)
      (\ tp ->
        Error_Monad.catch_error
          (check_fp_nontermination_proof ia j assms
            (Shows_Literal.add_index i Arith.one_nat)
            (pa, Termination_Problem_Spec.rules ia tp) prf)
          (\ x ->
            Sum_Type.Inl
              ((i . Shows_Literal.showsl_lit
                      ": error below the rule removal\n") .
                x))));
check_fp_nontermination_proof ia j assms i tp (FPTRS_Assume_Not_SN t ass) =
  FOR_Preliminaries.debug i "Finiteness Assumption or Unknown Proof"
    (if assms
      then Error_Monad.bind
             (Error_Monad.catch_error (check_fp_tp_subsumes t tp)
               (\ x ->
                 Sum_Type.Inl
                   (((i . Shows_Literal.showsl_lit
                            ": error in non-termination assumption or unknown proof\n") .
                      x) .
                     Shows_Literal.showsl_literal "\n")))
             (\ _ ->
               Error_Monad.catch_error
                 (Error_Monad.catch_error
                   (Error_Monad.forallM_index
                     (\ asa ja ->
                       check_assm ia j
                         (check_trs_nontermination_proof ia j assms
                           (Shows_Literal.add_index i (Arith.suc ja)))
                         (check_dp_nontermination_proof ia j assms
                           (Shows_Literal.add_index i (Arith.suc ja)))
                         (check_reltrs_nontermination_proof ia j assms
                           (Shows_Literal.add_index i (Arith.suc ja)))
                         (check_fp_nontermination_proof ia j assms
                           (Shows_Literal.add_index i (Arith.suc ja)))
                         (check_unknown_disproof ia j assms
                           (Shows_Literal.add_index i (Arith.suc ja)))
                         asa)
                     ass)
                   (\ x -> Sum_Type.Inl (snd x)))
                 (\ x ->
                   Sum_Type.Inl
                     ((i . Shows_Literal.showsl_lit
                             ": error below unknown proof\n") .
                       x)))
      else Sum_Type.Inl
             (i . Shows_Literal.showsl_lit
                    ": the proof contains an assumption or unknown proof\n"));

check_dp_nontermination_proof ::
  forall a b c d.
    (Compare.Compare_order b, HOL.Default b, Eq b, Shows_Literal.Showl b,
      Compare.Compare_order c, Eq c,
      Shows_Literal.Showl c) => Termination_Problem_Spec.Tp_ops_ext a
                                  (Labelings.Lab b c) [Arith.Char] () ->
                                  Dependency_Pair_Problem_Spec.Dpp_ops_ext d
                                    (Labelings.Lab b c) [Arith.Char] () ->
                                    Bool ->
                                      (String -> String) ->
d -> Dp_nontermination_proof b c [Arith.Char] ->
       Sum_Type.Sum (String -> String) ();
check_dp_nontermination_proof ia j assms i dpp (DP_Loop p) =
  FOR_Preliminaries.debug i "Loop"
    (Error_Monad.catch_error (Loops_Impl.check_dp_loop j dpp p)
      (\ x ->
        Sum_Type.Inl
          ((((i . Shows_Literal.showsl_lit
                    ": error in checking loop for the following DP-problem\n") .
              QDP_Framework_Impl.showsl_dpp j dpp) .
             Shows_Literal.showsl_literal "\n") .
            x)));
check_dp_nontermination_proof ia j assms i dpp (DP_Nonloop p) =
  FOR_Preliminaries.debug i "Nonloop"
    (Error_Monad.catch_error (Nonloop_Impl.check_non_loop_dp_prf j dpp p)
      (\ x ->
        Sum_Type.Inl
          ((((i . Shows_Literal.showsl_lit
                    ": error in checking nonloop for the following DP-problem\n") .
              QDP_Framework_Impl.showsl_dpp j dpp) .
             Shows_Literal.showsl_literal "\n") .
            x)));
check_dp_nontermination_proof ia j assms i dpp (DP_Rule_Removal p prf) =
  FOR_Preliminaries.debug i "Rule Removal"
    (Error_Monad.bind (Nontermination_Impl.rule_removal_nonterm_dp j dpp p)
      (\ dppa ->
        Error_Monad.catch_error
          (check_dp_nontermination_proof ia j assms
            (Shows_Literal.add_index i Arith.one_nat) dppa prf)
          (\ x ->
            Sum_Type.Inl
              ((i . Shows_Literal.showsl_lit
                      ": error below the pair and rule removal\n") .
                x))));
check_dp_nontermination_proof ia j assms i dpp (DP_Q_Reduction p prf) =
  FOR_Preliminaries.debug i "Q reduction"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (Q_Reduction_Nonterm_Impl.dp_q_reduction_nonterm j dpp p)
        (\ x ->
          Sum_Type.Inl
            ((((i . Shows_Literal.showsl_lit
                      ": error in reducing the innermost lhss in the following DP-problem\n") .
                QDP_Framework_Impl.showsl_dpp j dpp) .
               Shows_Literal.showsl_literal "\n") .
              x)))
      (\ dppa ->
        Error_Monad.catch_error
          (check_dp_nontermination_proof ia j assms
            (Shows_Literal.add_index i Arith.one_nat) dppa prf)
          (\ x ->
            Sum_Type.Inl
              ((i . Shows_Literal.showsl_lit
                      ": error below the Q reduction\n") .
                x))));
check_dp_nontermination_proof ia j assms i dpp (DP_Q_Increase p prf) =
  FOR_Preliminaries.debug i "Q increase"
    (Error_Monad.bind (Nontermination_Impl.q_increase_nonterm_dp j dpp p)
      (\ dppa ->
        Error_Monad.catch_error
          (check_dp_nontermination_proof ia j assms
            (Shows_Literal.add_index i Arith.one_nat) dppa prf)
          (\ x ->
            Sum_Type.Inl
              ((i . Shows_Literal.showsl_lit ": error below the Q increase\n") .
                x))));
check_dp_nontermination_proof ia j assms i dpp (DP_Termination_Switch p prf) =
  FOR_Preliminaries.debug i "Switch to Termination"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (Termination_Switch_Impl.switch_termination_proc
          Renaming2_String.string_rename j p dpp)
        (\ x ->
          Sum_Type.Inl
            ((((i . Shows_Literal.showsl_lit
                      ": error in switching to full strategy for the DP-problem\n") .
                QDP_Framework_Impl.showsl_dpp j dpp) .
               Shows_Literal.showsl_literal "\n") .
              x)))
      (\ dppa ->
        Error_Monad.catch_error
          (check_dp_nontermination_proof ia j assms
            (Shows_Literal.add_index i Arith.one_nat) dppa prf)
          (\ x ->
            Sum_Type.Inl
              ((i . Shows_Literal.showsl_lit
                      ": error below the termination switch processor\n") .
                x))));
check_dp_nontermination_proof ia j assms i dpp (DP_Instantiation p prf) =
  FOR_Preliminaries.debug i "Instantiation"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (Instantiation_Impl.instantiation_complete_proc j dpp p)
        (\ x ->
          Sum_Type.Inl
            ((((i . Shows_Literal.showsl_lit
                      ": error when applying the instantiation processor on\n") .
                QDP_Framework_Impl.showsl_dpp j dpp) .
               Shows_Literal.showsl_literal "\n") .
              x)))
      (\ dppa ->
        Error_Monad.catch_error
          (check_dp_nontermination_proof ia j assms
            (Shows_Literal.add_index i Arith.one_nat) dppa prf)
          (\ x ->
            Sum_Type.Inl
              ((i . Shows_Literal.showsl_lit
                      ": error below the instantiation processor\n") .
                x))));
check_dp_nontermination_proof ia j assms i dpp (DP_Rewriting p prf) =
  FOR_Preliminaries.debug i "Rewriting"
    (Error_Monad.bind
      (Error_Monad.catch_error (Rewriting_Impl.rewriting_complete_proc j p dpp)
        (\ x ->
          Sum_Type.Inl
            ((i . Shows_Literal.showsl_lit
                    ": error when applying the rewriting processor\n") .
              x)))
      (\ dppa ->
        Error_Monad.catch_error
          (check_dp_nontermination_proof ia j assms
            (Shows_Literal.add_index i Arith.one_nat) dppa prf)
          (\ x ->
            Sum_Type.Inl
              ((i . Shows_Literal.showsl_lit
                      ": error below the rewriting processor\n") .
                x))));
check_dp_nontermination_proof ia j assms i dpp (DP_Narrowing p prf) =
  FOR_Preliminaries.debug i "Narrowing"
    (Error_Monad.bind
      (Error_Monad.catch_error (Narrowing_Impl.narrowing_complete_proc j p dpp)
        (\ x ->
          Sum_Type.Inl
            ((i . Shows_Literal.showsl_lit
                    ": error when applying the narrowing processor\n") .
              x)))
      (\ dppa ->
        Error_Monad.catch_error
          (check_dp_nontermination_proof ia j assms
            (Shows_Literal.add_index i Arith.one_nat) dppa prf)
          (\ x ->
            Sum_Type.Inl
              ((i . Shows_Literal.showsl_lit
                      ": error below the rewriting processor") .
                x))));
check_dp_nontermination_proof ia j assms i dpp (DP_Assume_Infinite dp ass) =
  FOR_Preliminaries.debug i "Finiteness Assumption or Unknown Proof"
    (if assms
      then Error_Monad.bind
             (Error_Monad.catch_error (check_dpp_subsumes j dp dpp)
               (\ x ->
                 Sum_Type.Inl
                   (((i . Shows_Literal.showsl_lit
                            ": error in finiteness assumption or unknown proof\n") .
                      x) .
                     Shows_Literal.showsl_literal "\n")))
             (\ _ ->
               Error_Monad.catch_error
                 (Error_Monad.catch_error
                   (Error_Monad.forallM_index
                     (\ asa ja ->
                       check_assm ia j
                         (check_trs_nontermination_proof ia j assms
                           (Shows_Literal.add_index i (Arith.suc ja)))
                         (check_dp_nontermination_proof ia j assms
                           (Shows_Literal.add_index i (Arith.suc ja)))
                         (check_reltrs_nontermination_proof ia j assms
                           (Shows_Literal.add_index i (Arith.suc ja)))
                         (check_fp_nontermination_proof ia j assms
                           (Shows_Literal.add_index i (Arith.suc ja)))
                         (check_unknown_disproof ia j assms
                           (Shows_Literal.add_index i (Arith.suc ja)))
                         asa)
                     ass)
                   (\ x -> Sum_Type.Inl (snd x)))
                 (\ x ->
                   Sum_Type.Inl
                     ((i . Shows_Literal.showsl_lit
                             ": error below unknown proof\n") .
                       x)))
      else Sum_Type.Inl
             (i . Shows_Literal.showsl_lit
                    ": the proof contains an assumption or unknown proof\n"));

trs_nontermination_proof_to_fp ::
  forall a b c.
    Trs_nontermination_proof a b c ->
      Sum_Type.Sum (String -> String) (Fp_trs_nontermination_proof a b c);
trs_nontermination_proof_to_fp (TRS_Loop x) = Sum_Type.Inr (FP_TRS_Loop x);
trs_nontermination_proof_to_fp (TRS_Rule_Removal x p) =
  Error_Monad.bind (trs_nontermination_proof_to_fp p)
    (\ pa -> Sum_Type.Inr (FP_TRS_Rule_Removal x pa));
trs_nontermination_proof_to_fp TRS_Not_Well_Formed =
  Sum_Type.Inl
    (Shows_Literal.showsl_lit
      "for the given strategy, only loops and rule removal are supported as nontermination techniques");
trs_nontermination_proof_to_fp (TRS_String_Reversal v) =
  Sum_Type.Inl
    (Shows_Literal.showsl_lit
      "for the given strategy, only loops and rule removal are supported as nontermination techniques");
trs_nontermination_proof_to_fp (TRS_Constant_String v va) =
  Sum_Type.Inl
    (Shows_Literal.showsl_lit
      "for the given strategy, only loops and rule removal are supported as nontermination techniques");
trs_nontermination_proof_to_fp (TRS_DP_Trans v va) =
  Sum_Type.Inl
    (Shows_Literal.showsl_lit
      "for the given strategy, only loops and rule removal are supported as nontermination techniques");
trs_nontermination_proof_to_fp (TRS_Termination_Switch v va) =
  Sum_Type.Inl
    (Shows_Literal.showsl_lit
      "for the given strategy, only loops and rule removal are supported as nontermination techniques");
trs_nontermination_proof_to_fp (TRS_Nonloop v) =
  Sum_Type.Inl
    (Shows_Literal.showsl_lit
      "for the given strategy, only loops and rule removal are supported as nontermination techniques");
trs_nontermination_proof_to_fp (TRS_Nonloop_SRS v) =
  Sum_Type.Inl
    (Shows_Literal.showsl_lit
      "for the given strategy, only loops and rule removal are supported as nontermination techniques");
trs_nontermination_proof_to_fp (TRS_Q_Increase v va) =
  Sum_Type.Inl
    (Shows_Literal.showsl_lit
      "for the given strategy, only loops and rule removal are supported as nontermination techniques");
trs_nontermination_proof_to_fp (TRS_Uncurry v va) =
  Sum_Type.Inl
    (Shows_Literal.showsl_lit
      "for the given strategy, only loops and rule removal are supported as nontermination techniques");
trs_nontermination_proof_to_fp (TRS_Not_WN_Tree_Automaton v) =
  Sum_Type.Inl
    (Shows_Literal.showsl_lit
      "for the given strategy, only loops and rule removal are supported as nontermination techniques");
trs_nontermination_proof_to_fp TRS_Not_RG_Decision =
  Sum_Type.Inl
    (Shows_Literal.showsl_lit
      "for the given strategy, only loops and rule removal are supported as nontermination techniques");
trs_nontermination_proof_to_fp (TRS_Assume_Not_SN v va) =
  Sum_Type.Inl
    (Shows_Literal.showsl_lit
      "for the given strategy, only loops and rule removal are supported as nontermination techniques");

}
