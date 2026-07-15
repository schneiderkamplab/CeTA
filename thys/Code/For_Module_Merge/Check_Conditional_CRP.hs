{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Check_Conditional_CRP(Ccr_transformation(..), Conditional_cr_proof(..),
                         Conditional_ncr_proof(..), check_conditional_cr_proof,
                         check_conditional_ncr_proof)
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
import qualified Compare_Order_Instances;
import qualified Unraveling_Impl;
import qualified Container_Setup;
import qualified Mapping_Impl;
import qualified Inline_Conditions_Impl;
import qualified FOR_Preliminaries;
import qualified Missing_List;
import qualified Error_Monad;
import qualified Dependency_Pair_Problem_Spec;
import qualified Termination_Problem_Spec;
import qualified Sum_Type;
import qualified Countable;
import qualified HOL;
import qualified Compare;
import qualified Labelings_Impl;
import qualified Str;
import qualified Collection_Order;
import qualified Cardinality;
import qualified Collection_Enum;
import qualified Set_Impl;
import qualified Collection_Eq;
import qualified Shows_Literal;
import qualified Compare_Instances;
import qualified Arith;
import qualified Reduction_Pair_Implementations;
import qualified Conditional_Rewriting_Impl;
import qualified Non_Confluence_Impl;
import qualified Check_Level_Confluence;
import qualified Check_Quasi_Reductive;
import qualified Check_AL94;
import qualified Check_CRP;
import qualified Check_Infeasibility;
import qualified Labelings;
import qualified Term;

data Ccr_transformation a b c d =
  Inline_Conditions_CCRT
    [((Term.Term (Labelings.Lab a b) c, Term.Term (Labelings.Lab a b) c),
       [(Term.Term (Labelings.Lab a b) c, Term.Term (Labelings.Lab a b) c)])]
    [(((Term.Term (Labelings.Lab a b) c, Term.Term (Labelings.Lab a b) c),
        [(Term.Term (Labelings.Lab a b) c, Term.Term (Labelings.Lab a b) c)]),
       [(Term.Term (Labelings.Lab a b) c, Term.Term (Labelings.Lab a b) c)])]
  | Infeasible_Rule_Removal_CCRT
      [(((Term.Term (Labelings.Lab a b) c, Term.Term (Labelings.Lab a b) c),
          [(Term.Term (Labelings.Lab a b) c, Term.Term (Labelings.Lab a b) c)]),
         Check_Infeasibility.Infeasibility_proof a c d b)];

data Conditional_cr_proof a b c d = Unconditional_CR (Check_CRP.Cr_proof a b c)
  | Unravel_CR
      [(((Term.Term (Labelings.Lab a b) c, Term.Term (Labelings.Lab a b) c),
          [(Term.Term (Labelings.Lab a b) c, Term.Term (Labelings.Lab a b) c)]),
         [(Term.Term (Labelings.Lab a b) c, Term.Term (Labelings.Lab a b) c)])]
      (Check_CRP.Cr_proof a b c)
  | Transformation_CR (Ccr_transformation a b c d)
      (Conditional_cr_proof a b c d)
  | Almost_Orthogonal_CR
  | Almost_Orthogonal_Modulo_Infeasibility_CR
      [([(Term.Term (Labelings.Lab a b) c, Term.Term (Labelings.Lab a b) c)],
         ([(Term.Term (Labelings.Lab a b) c, Term.Term (Labelings.Lab a b) c)],
           Check_Level_Confluence.Ao_infeasibility_proof a c d b))]
  | AL94_CR (Check_Quasi_Reductive.Quasi_reductive_proof a b c)
      [(Term.Term (Labelings.Lab a b) c,
         (Term.Term (Labelings.Lab a b) c,
           ([(Term.Term (Labelings.Lab a b) c,
               Term.Term (Labelings.Lab a b) c)],
             Check_AL94.Context_joinable_proof (Labelings.Lab a b) c)))]
      [([(Term.Term (Labelings.Lab a b) c, Term.Term (Labelings.Lab a b) c)],
         Check_Infeasibility.Infeasibility_proof a c d b)]
      [(c -> Term.Term (Labelings.Lab a b) c,
         Check_AL94.Unfeasible_proof (Labelings.Lab a b) c)];

data Conditional_ncr_proof a b c d e =
  Unconditional_CNCR (Check_CRP.Ncr_proof a b c d)
  | Transformation_CNCR (Ccr_transformation a b c e)
      (Conditional_ncr_proof a b c d e)
  | Non_Join_CNCR (Term.Term (Labelings.Lab a b) c)
      (Term.Term (Labelings.Lab a b) c) (Term.Term (Labelings.Lab a b) c)
      [Conditional_Rewriting_Impl.Cstep_proof (Labelings.Lab a b) c]
      [Conditional_Rewriting_Impl.Cstep_proof (Labelings.Lab a b) c]
      (Non_Confluence_Impl.Non_join_info (Labelings.Lab a b) c d
        (Reduction_Pair_Implementations.Redtriple_impl (Labelings.Lab a b)));

ru_impl ::
  forall a b.
    [((Term.Term a b, Term.Term a b), [(Term.Term a b, Term.Term a b)])] ->
      [(Term.Term a b, Term.Term a b)];
ru_impl r = map fst r;

check_ccr_trans ::
  forall a b c d e.
    (Compare.Compare_order c, Countable.Countable c, HOL.Default c, Eq c,
      Shows_Literal.Showl c) => a -> (String -> String) ->
                                       Termination_Problem_Spec.Tp_ops_ext b
 (Labelings.Lab c [Arith.Nat]) [Str.Char] () ->
 Dependency_Pair_Problem_Spec.Dpp_ops_ext d (Labelings.Lab c [Arith.Nat])
   [Str.Char] () ->
   [((Term.Term (Labelings.Lab c [Arith.Nat]) [Str.Char],
       Term.Term (Labelings.Lab c [Arith.Nat]) [Str.Char]),
      [(Term.Term (Labelings.Lab c [Arith.Nat]) [Str.Char],
         Term.Term (Labelings.Lab c [Arith.Nat]) [Str.Char])])] ->
     Ccr_transformation c [Arith.Nat] [Str.Char] e ->
       Sum_Type.Sum (String -> String)
         [((Term.Term (Labelings.Lab c [Arith.Nat]) [Str.Char],
             Term.Term (Labelings.Lab c [Arith.Nat]) [Str.Char]),
            [(Term.Term (Labelings.Lab c [Arith.Nat]) [Str.Char],
               Term.Term (Labelings.Lab c [Arith.Nat]) [Str.Char])])];
check_ccr_trans a ia i j ra (Inline_Conditions_CCRT r rcs) =
  FOR_Preliminaries.debug ia "Inline Conditions"
    (Error_Monad.bind (Inline_Conditions_Impl.check_inline_conds ra r rcs)
      (\ _ -> Sum_Type.Inr r));
check_ccr_trans a ia i j r (Infeasible_Rule_Removal_CCRT rps) =
  FOR_Preliminaries.debug ia "Infeasible Rule Removal"
    (Error_Monad.bind
      (Check_Infeasibility.check_infeasible_rules a ia i j
        (Missing_List.list_diff r (map fst rps)) rps)
      (\ _ -> Sum_Type.Inr (Missing_List.list_diff r (map fst rps))));

check_conditional_non_cr ::
  forall a b c.
    (Compare.Compare_order a, HOL.Default a, Eq a, Shows_Literal.Showl a,
      Cardinality.Card_UNIV b, Collection_Enum.Cenum b, Collection_Eq.Ceq b,
      Collection_Order.Cproper_interval b, Compare.Compare_order b, Eq b,
      Set_Impl.Set_impl b,
      Shows_Literal.Showl b) => [((Term.Term (Labelings.Lab a [Arith.Nat])
                                     [Str.Char],
                                    Term.Term (Labelings.Lab a [Arith.Nat])
                                      [Str.Char]),
                                   [(Term.Term (Labelings.Lab a [Arith.Nat])
                                       [Str.Char],
                                      Term.Term (Labelings.Lab a [Arith.Nat])
[Str.Char])])] ->
                                  Term.Term (Labelings.Lab a [Arith.Nat])
                                    [Str.Char] ->
                                    Term.Term (Labelings.Lab a [Arith.Nat])
                                      [Str.Char] ->
                                      Term.Term (Labelings.Lab a [Arith.Nat])
[Str.Char] ->
[Conditional_Rewriting_Impl.Cstep_proof (Labelings.Lab a [Arith.Nat])
   [Str.Char]] ->
  [Conditional_Rewriting_Impl.Cstep_proof (Labelings.Lab a [Arith.Nat])
     [Str.Char]] ->
    Non_Confluence_Impl.Non_join_info (Labelings.Lab a [Arith.Nat]) [Str.Char] b
      c ->
      Sum_Type.Sum (String -> String) ();
check_conditional_non_cr r s t u ps qs reason =
  Error_Monad.bind (Conditional_Rewriting_Impl.check_csteps r s t ps)
    (\ _ ->
      Error_Monad.bind (Conditional_Rewriting_Impl.check_csteps r s u qs)
        (\ _ ->
          Non_Confluence_Impl.check_non_join (ru_impl r) (ru_impl r) t u
            reason));

check_conditional_cr_proof ::
  forall a b c d.
    (Compare.Compare_order b, Countable.Countable b, HOL.Default b, Eq b,
      Shows_Literal.Showl b) => Bool ->
                                  (String -> String) ->
                                    Termination_Problem_Spec.Tp_ops_ext a
                                      (Labelings.Lab b [Arith.Nat]) [Str.Char]
                                      () ->
                                      Dependency_Pair_Problem_Spec.Dpp_ops_ext c
(Labelings.Lab b [Arith.Nat]) [Str.Char] () ->
[((Term.Term (Labelings.Lab b [Arith.Nat]) [Str.Char],
    Term.Term (Labelings.Lab b [Arith.Nat]) [Str.Char]),
   [(Term.Term (Labelings.Lab b [Arith.Nat]) [Str.Char],
      Term.Term (Labelings.Lab b [Arith.Nat]) [Str.Char])])] ->
  Conditional_cr_proof b [Arith.Nat] [Str.Char] d ->
    Sum_Type.Sum (String -> String) ();
check_conditional_cr_proof a ia i j ctrs (Unconditional_CR prf) =
  FOR_Preliminaries.debug ia "Unconditional"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (Error_Monad.catch_error
          (Error_Monad.forallM
            (\ x -> (if null (snd x) then Sum_Type.Inr () else Sum_Type.Inl x))
            ctrs)
          (\ x -> Sum_Type.Inl (snd x)))
        (\ x ->
          Sum_Type.Inl
            ((Shows_Literal.showsl_lit "rule with non-empty conditions" .
               Shows_Literal.showsl_literal "\n") .
              Conditional_Rewriting_Impl.showsl_crule x)))
      (\ _ -> Check_CRP.check_cr_proof a ia i j (map fst ctrs) prf));
check_conditional_cr_proof a ia i j ctrs (Unravel_CR u_info prf) =
  FOR_Preliminaries.debug ia "Unravel"
    (Error_Monad.bind
      (Error_Monad.catch_error (Unraveling_Impl.check_sp_unraveling u_info ctrs)
        (\ x ->
          Sum_Type.Inl
            (((ia . Shows_Literal.showsl_lit ": error in unraveling") .
               Shows_Literal.showsl_literal "\n") .
              x)))
      (\ r ->
        Error_Monad.catch_error
          (Check_CRP.check_cr_proof a (Shows_Literal.add_index ia Arith.one_nat)
            i j r prf)
          (\ x ->
            Sum_Type.Inl
              (((ia . Shows_Literal.showsl_lit
                        ": error below confluence proof") .
                 Shows_Literal.showsl_literal "\n") .
                x))));
check_conditional_cr_proof a ia i j ctrs (Transformation_CR t prf) =
  FOR_Preliminaries.debug ia "CR Reflecting Transformation"
    (Error_Monad.bind (check_ccr_trans a ia i j ctrs t)
      (\ ctrsa -> check_conditional_cr_proof a ia i j ctrsa prf));
check_conditional_cr_proof a ia i j ctrs Almost_Orthogonal_CR =
  FOR_Preliminaries.debug ia "Almost-Orthogonal"
    (Check_Level_Confluence.check_level_confluence ctrs);
check_conditional_cr_proof a ia i j ctrs
  (Almost_Orthogonal_Modulo_Infeasibility_CR cps) =
  FOR_Preliminaries.debug ia
    "Almost-Orthogonal modulo Infeasibility + meet-to-join"
    (Check_Level_Confluence.check_level_confluence_modulo_infeasibility a ia i j
      cps ctrs);
check_conditional_cr_proof a ia i j ctrs (AL94_CR qrp cj icp ucp) =
  FOR_Preliminaries.debug ia "AL94"
    (Error_Monad.bind
      (Check_Quasi_Reductive.check_quasi_reductive_proof a ia i j ctrs qrp)
      (\ _ -> Check_AL94.check_al94 a ia i j cj icp ucp ctrs));

check_conditional_ncr_proof ::
  forall a b c d.
    (Compare.Compare_order b, Countable.Countable b, HOL.Default b, Eq b,
      Shows_Literal.Showl b) => Bool ->
                                  (String -> String) ->
                                    Termination_Problem_Spec.Tp_ops_ext a
                                      (Labelings.Lab b [Arith.Nat]) [Str.Char]
                                      () ->
                                      Dependency_Pair_Problem_Spec.Dpp_ops_ext c
(Labelings.Lab b [Arith.Nat]) [Str.Char] () ->
[((Term.Term (Labelings.Lab b [Arith.Nat]) [Str.Char],
    Term.Term (Labelings.Lab b [Arith.Nat]) [Str.Char]),
   [(Term.Term (Labelings.Lab b [Arith.Nat]) [Str.Char],
      Term.Term (Labelings.Lab b [Arith.Nat]) [Str.Char])])] ->
  Conditional_ncr_proof b [Arith.Nat] [Str.Char] [Str.Char] d ->
    Sum_Type.Sum (String -> String) ();
check_conditional_ncr_proof a ia i j r (Unconditional_CNCR prf) =
  FOR_Preliminaries.debug ia "Unconditional"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (Error_Monad.catch_error
          (Error_Monad.forallM
            (\ x -> (if null (snd x) then Sum_Type.Inr () else Sum_Type.Inl x))
            r)
          (\ x -> Sum_Type.Inl (snd x)))
        (\ x ->
          Sum_Type.Inl
            ((Shows_Literal.showsl_lit "rule with non-empty conditions" .
               Shows_Literal.showsl_literal "\n") .
              Conditional_Rewriting_Impl.showsl_crule x)))
      (\ _ -> Check_CRP.check_ncr_proof a ia i j (map fst r) prf));
check_conditional_ncr_proof a ia i j r (Transformation_CNCR t prf) =
  FOR_Preliminaries.debug ia "CR Preserving Transformation"
    (Error_Monad.bind (check_ccr_trans a ia i j r t)
      (\ ra -> check_conditional_ncr_proof a ia i j ra prf));
check_conditional_ncr_proof a ia i j r (Non_Join_CNCR s t u ps qs prf) =
  FOR_Preliminaries.debug ia "Conditional Non-Joinability"
    (Error_Monad.catch_error (check_conditional_non_cr r s t u ps qs prf)
      (\ x ->
        Sum_Type.Inl
          ((((ia . Shows_Literal.showsl_lit "error when disproving CR of ") .
              Conditional_Rewriting_Impl.showsl_ctrs r) .
             Shows_Literal.showsl_literal "\n") .
            x)));

}
