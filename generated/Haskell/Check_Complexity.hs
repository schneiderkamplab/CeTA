{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Check_Complexity(Complexity_proof(..), check_complexity_proof) where {

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
import qualified Quasi_Order;
import qualified Complexity_Impl;
import qualified Q_Restricted_Rewriting_Impl;
import qualified Usable_Rules_Complexity_Impl;
import qualified Complexity_Framework_Impl;
import qualified QDP_Framework_Impl;
import qualified FOR_Preliminaries;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified HOL;
import qualified Mapping;
import qualified Compare_Order_Instances;
import qualified List_Lexorder;
import qualified Product_Lexorder;
import qualified Sum_Type;
import qualified Termination_Problem_Spec;
import qualified Arith;
import qualified Compare;
import qualified Reduction_Pair_Implementations;
import qualified DT_Transformation_Impl;
import qualified Check_Termination_Common;
import qualified WDP_Transformation_Impl;
import qualified Matchbounds_Impl;
import qualified Labelings;
import qualified Term_Rewriting;

data Complexity_proof a b c =
  Rule_Shift_Complexity
    (Reduction_Pair_Implementations.Redtriple_impl (Labelings.Lab a b))
    [(Term_Rewriting.Term (Labelings.Lab a b) c,
       Term_Rewriting.Term (Labelings.Lab a b) c)]
    (Maybe [(Term_Rewriting.Term (Labelings.Lab a b) c,
              Term_Rewriting.Term (Labelings.Lab a b) c)])
    (Complexity_proof a b c)
  | RisEmpty_Complexity
  | Remove_Nonapplicable_Rules_Complexity
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      (Complexity_proof a b c)
  | Matchbounds_Complexity (Matchbounds_Impl.Bounds_info (Labelings.Lab a b) c)
  | Matchbounds_Rel_Complexity
      (Matchbounds_Impl.Bounds_info (Labelings.Lab a b) c)
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      (Complexity_proof a b c)
  | DT_Transformation
      (DT_Transformation_Impl.Dt_transformation_info (Labelings.Lab a b) c)
      (Complexity_proof a b c)
  | WDP_Transformation
      (WDP_Transformation_Impl.Wdp_trans_info (Labelings.Lab a b) c)
      (Complexity_proof a b c)
  | Complexity_Assumption
      ([Term_Rewriting.Term (Labelings.Lab a b) c],
        ([(Term_Rewriting.Term (Labelings.Lab a b) c,
            Term_Rewriting.Term (Labelings.Lab a b) c)],
          ([(Term_Rewriting.Term (Labelings.Lab a b) c,
              Term_Rewriting.Term (Labelings.Lab a b) c)],
            (Term_Rewriting.Complexity_measure (Labelings.Lab a b) c,
              Term_Rewriting.Complexity_class))))
      [Check_Termination_Common.Generic_assm_proof a b c
         (Complexity_proof a b c) () () () ()]
  | Usable_Rules_Complexity
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      (Complexity_proof a b c)
  | Split_Complexity
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      (Complexity_proof a b c) (Complexity_proof a b c);

mk_cpx ::
  forall a b c d e.
    (Compare.Compare_order b, Term_Rewriting.Showl b, Compare.Compare_order c,
      Term_Rewriting.Showl c) => Termination_Problem_Spec.Tp_ops_ext a
                                   (Labelings.Lab b c) [Arith.Char] () ->
                                   ([Term_Rewriting.Term (Labelings.Lab b c)
                                       [Arith.Char]],
                                     ([(Term_Rewriting.Term (Labelings.Lab b c)
  [Arith.Char],
 Term_Rewriting.Term (Labelings.Lab b c) [Arith.Char])],
                                       ([(Term_Rewriting.Term
    (Labelings.Lab b c) [Arith.Char],
   Term_Rewriting.Term (Labelings.Lab b c) [Arith.Char])],
 (d, e)))) ->
                                     (a, (d, e));
mk_cpx i (q, (s, (w, (cm, cc)))) =
  (Termination_Problem_Spec.mk i False q s w, (cm, cc));

check_assm ::
  forall a b c d.
    (Compare.Compare_order b, Term_Rewriting.Showl b, Compare.Compare_order c,
      Term_Rewriting.Showl c) => Termination_Problem_Spec.Tp_ops_ext a
                                   (Labelings.Lab b c) [Arith.Char] () ->
                                   ((a, (Term_Rewriting.Complexity_measure
   (Labelings.Lab b c) [Arith.Char],
  Term_Rewriting.Complexity_class)) ->
                                     d -> Sum_Type.Sum (String -> String) ()) ->
                                     Check_Termination_Common.Generic_assm_proof
                                       b c [Arith.Char] d () () () () ->
                                       Sum_Type.Sum (String -> String) ();
check_assm i cpx_check (Check_Termination_Common.Complexity_assm_proof cp prf) =
  cpx_check (mk_cpx i cp) prf;
check_assm i uu (Check_Termination_Common.SN_assm_proof v va) =
  Sum_Type.Inl
    (Term_Rewriting.showsl_lit
      "no support for termination or non-termination assumptions in complexity proof");
check_assm i uu (Check_Termination_Common.Finite_assm_proof v va) =
  Sum_Type.Inl
    (Term_Rewriting.showsl_lit
      "no support for termination or non-termination assumptions in complexity proof");
check_assm i uu (Check_Termination_Common.SN_FP_assm_proof v va) =
  Sum_Type.Inl
    (Term_Rewriting.showsl_lit
      "no support for termination or non-termination assumptions in complexity proof");
check_assm i uu (Check_Termination_Common.Not_SN_assm_proof v va) =
  Sum_Type.Inl
    (Term_Rewriting.showsl_lit
      "no support for termination or non-termination assumptions in complexity proof");
check_assm i uu (Check_Termination_Common.Infinite_assm_proof v va) =
  Sum_Type.Inl
    (Term_Rewriting.showsl_lit
      "no support for termination or non-termination assumptions in complexity proof");
check_assm i uu (Check_Termination_Common.Not_RelSN_assm_proof v va) =
  Sum_Type.Inl
    (Term_Rewriting.showsl_lit
      "no support for termination or non-termination assumptions in complexity proof");
check_assm i uu (Check_Termination_Common.Not_SN_FP_assm_proof v va) =
  Sum_Type.Inl
    (Term_Rewriting.showsl_lit
      "no support for termination or non-termination assumptions in complexity proof");
check_assm i uu (Check_Termination_Common.Unknown_assm_proof v va) =
  Sum_Type.Inl
    (Term_Rewriting.showsl_lit
      "no support for termination or non-termination assumptions in complexity proof");

showsl_complexity_measure ::
  forall a b.
    (Quasi_Order.Linorder a,
      Term_Rewriting.Showl a) => Term_Rewriting.Complexity_measure a b ->
                                   String -> String;
showsl_complexity_measure (Term_Rewriting.Runtime_Complexity c d) =
  (((Term_Rewriting.showsl_lit "basic terms f(c1,..,cn) where f in\n" .
      Term_Rewriting.showsl_lista (Arith.sort_key (\ x -> x) d)) .
     Term_Rewriting.showsl_lit "\n and ci is term over signature\n ") .
    Term_Rewriting.showsl_lista (Arith.sort_key (\ x -> x) c)) .
    Term_Rewriting.showsl_literal "\n";
showsl_complexity_measure (Term_Rewriting.Derivational_Complexity f) =
  (Term_Rewriting.showsl_lit "all terms over signature\n" .
    Term_Rewriting.showsl_lista (Arith.sort_key (\ x -> x) f)) .
    Term_Rewriting.showsl_literal "\n";

showsl_complexityLL ::
  forall a b c.
    (Compare.Compare_order a, Term_Rewriting.Showl a, Compare.Compare_order b,
      Term_Rewriting.Showl b, Compare.Compare_order c,
      Term_Rewriting.Showl c) => ([Term_Rewriting.Term (Labelings.Lab a b) c],
                                   ([(Term_Rewriting.Term (Labelings.Lab a b) c,
                                       Term_Rewriting.Term (Labelings.Lab a b)
 c)],
                                     ([(Term_Rewriting.Term (Labelings.Lab a b)
  c,
 Term_Rewriting.Term (Labelings.Lab a b) c)],
                                       (Term_Rewriting.Complexity_measure
  (Labelings.Lab a b) c,
 Term_Rewriting.Complexity_class)))) ->
                                   String -> String;
showsl_complexityLL (q, (s, (w, (cm, cc)))) =
  (((((((((Term_Rewriting.showsl_lit "strict rules\n" .
            Term_Rewriting.showsl_rules (Arith.sort_key (\ x -> x) s)) .
           Term_Rewriting.showsl_lit "\n\nweak rules\n") .
          Term_Rewriting.showsl_rules (Arith.sort_key (\ x -> x) w)) .
         Term_Rewriting.showsl_lit "\n\ninnermost lhss (Q)\n") .
        Term_Rewriting.showsl_lines "empty" (Arith.sort_key (\ x -> x) q)) .
       Term_Rewriting.showsl_lit "\n\nstarting terms: ") .
      showsl_complexity_measure cm) .
     Term_Rewriting.showsl_lit "\nintended complexity: ") .
    Term_Rewriting.showsl_complexity_class cc) .
    Term_Rewriting.showsl_literal "\n";

check_complexity_subsumes ::
  forall a b c.
    (Compare.Compare_order a, Eq a, Term_Rewriting.Showl a,
      Compare.Compare_order b, Eq b, Term_Rewriting.Showl b, Arith.Ccompare c,
      Compare.Compare_order c, Eq c, Mapping.Mapping_impl c,
      Term_Rewriting.Showl c) => ([Term_Rewriting.Term (Labelings.Lab a b) c],
                                   ([(Term_Rewriting.Term (Labelings.Lab a b) c,
                                       Term_Rewriting.Term (Labelings.Lab a b)
 c)],
                                     ([(Term_Rewriting.Term (Labelings.Lab a b)
  c,
 Term_Rewriting.Term (Labelings.Lab a b) c)],
                                       (Term_Rewriting.Complexity_measure
  (Labelings.Lab a b) c,
 Term_Rewriting.Complexity_class)))) ->
                                   ([Term_Rewriting.Term (Labelings.Lab a b) c],
                                     ([(Term_Rewriting.Term (Labelings.Lab a b)
  c,
 Term_Rewriting.Term (Labelings.Lab a b) c)],
                                       ([(Term_Rewriting.Term
    (Labelings.Lab a b) c,
   Term_Rewriting.Term (Labelings.Lab a b) c)],
 (Term_Rewriting.Complexity_measure (Labelings.Lab a b) c,
   Term_Rewriting.Complexity_class)))) ->
                                     Sum_Type.Sum (String -> String) ();
check_complexity_subsumes (q1, (s1, (w1, (cm1, cc1))))
  (q2, (s2, (w2, (cm2, cc2)))) =
  Error_Monad.catch_error
    (Error_Monad.bind
      (Error_Monad.catch_error (Check_Monad.check_subseteq s2 s1)
        (\ x ->
          Sum_Type.Inl
            ((Term_Rewriting.showsl_lit "strict rule " .
               Term_Rewriting.showsl_rule x) .
              Term_Rewriting.showsl_lit " is missing")))
      (\ _ ->
        Error_Monad.bind
          (Error_Monad.catch_error (Check_Monad.check_subseteq w2 w1)
            (\ x ->
              Sum_Type.Inl
                ((Term_Rewriting.showsl_lit "weak rule " .
                   Term_Rewriting.showsl_rule x) .
                  Term_Rewriting.showsl_lit " is missing")))
          (\ _ ->
            Error_Monad.bind
              (Error_Monad.catch_error
                (Q_Restricted_Rewriting_Impl.check_NF_terms_subset
                  (Term_Rewriting.is_NF_terms q2) q1)
                (\ x ->
                  Sum_Type.Inl
                    (Term_Rewriting.showsl_lit "NF(Q) differs due to term " .
                      Term_Rewriting.showsl_terma x)))
              (\ _ ->
                Error_Monad.bind
                  (Check_Monad.check
                    (Term_Rewriting.less_eq_complexity_class cc1 cc2)
                    (Term_Rewriting.showsl_lit
                      "complexity classes do not match"))
                  (\ _ -> Complexity_Impl.check_terms_of_nat cm2 cm1)))))
    (\ x ->
      Sum_Type.Inl
        (((((Term_Rewriting.showsl_lit
               "could not ensure that assumption matches current complexity problem\n" .
              x) .
             Term_Rewriting.showsl_lit "\n\nassumption is\n") .
            showsl_complexityLL (q1, (s1, (w1, (cm1, cc1))))) .
           Term_Rewriting.showsl_lit "\n\ncurrent problem is\n") .
          showsl_complexityLL (q2, (s2, (w2, (cm2, cc2))))));

check_complexity_proof ::
  forall a b c.
    (Compare.Compare_order b, Eq b, Term_Rewriting.Showl b,
      Compare.Compare_order c, Eq c,
      Term_Rewriting.Showl c) => Termination_Problem_Spec.Tp_ops_ext a
                                   (Labelings.Lab b c) [Arith.Char] () ->
                                   Bool ->
                                     (String -> String) ->
                                       (a,
 (Term_Rewriting.Complexity_measure (Labelings.Lab b c) [Arith.Char],
   Term_Rewriting.Complexity_class)) ->
 Complexity_proof b c [Arith.Char] -> Sum_Type.Sum (String -> String) ();
check_complexity_proof ia assms i (tp, (cm, cc))
  (Rule_Shift_Complexity redp rdelete ur_opt prf) =
  FOR_Preliminaries.debug i "Rule Removal Complexity"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (Usable_Rules_Complexity_Impl.smart_rule_shift_complexity ia
          (Reduction_Pair_Implementations.get_rel_impl redp) rdelete ur_opt cm
          cc tp)
        (\ x ->
          Sum_Type.Inl
            ((((i . Term_Rewriting.showsl_lit
                      ": error when applying the rule shifting technique on\n") .
                QDP_Framework_Impl.showsl_tp ia tp) .
               Term_Rewriting.showsl_literal "\n") .
              x)))
      (\ tpa ->
        Error_Monad.catch_error
          (check_complexity_proof ia assms
            (Term_Rewriting.add_index i Arith.one_nat) (tpa, (cm, cc)) prf)
          (\ x ->
            Sum_Type.Inl
              ((i . Term_Rewriting.showsl_lit
                      ": error below the rule shifting processor\n") .
                x))));
check_complexity_proof ia assms i (tp, (cm, cc)) RisEmpty_Complexity =
  FOR_Preliminaries.debug i "R is empty for complexity"
    (Check_Monad.check (null (Termination_Problem_Spec.r ia tp))
      ((i . Term_Rewriting.showsl_lit ": R is not empty in\n") .
        QDP_Framework_Impl.showsl_tp ia tp));
check_complexity_proof ia assms i (tp, (cm, cc))
  (Remove_Nonapplicable_Rules_Complexity r prf) =
  FOR_Preliminaries.debug i "Removing non-applicable rules"
    (let {
       _ = Termination_Problem_Spec.r ia tp;
     } in Error_Monad.bind
            (Error_Monad.catch_error
              (Q_Restricted_Rewriting_Impl.check_non_applicable_rules
                (Termination_Problem_Spec.is_QNF ia tp) r)
              (\ x ->
                Sum_Type.Inl
                  ((i . Term_Rewriting.showsl_lit
                          ": error when removing non-applicable rules\n") .
                    Term_Rewriting.showsl_rule x .
                      Term_Rewriting.showsl_lit " is applicable")))
            (\ _ ->
              let {
                tpa = Termination_Problem_Spec.delete_R_Rw ia tp r r;
              } in Error_Monad.catch_error
                     (check_complexity_proof ia assms
                       (Term_Rewriting.add_index i Arith.one_nat)
                       (tpa, (cm, cc)) prf)
                     (\ x ->
                       Sum_Type.Inl
                         ((i . Term_Rewriting.showsl_lit
                                 ": error below the non-applicable rules removal\n") .
                           x))));
check_complexity_proof ia assms i (tp, (cm, cc)) (Matchbounds_Complexity info) =
  FOR_Preliminaries.debug i "Matchbounds"
    (Error_Monad.catch_error
      (Matchbounds_Impl.bounds_complexity ia info cm cc tp)
      (\ x ->
        Sum_Type.Inl
          ((i . Term_Rewriting.showsl_lit
                  ": error when applying matchbounds\n") .
            x)));
check_complexity_proof ia assms i (tp, (cm, cc))
  (Matchbounds_Rel_Complexity info rdel prf) =
  FOR_Preliminaries.debug i "Matchbounds-Rel"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (Matchbounds_Impl.bounds_complexity_rel ia info rdel cm cc tp)
        (\ x ->
          Sum_Type.Inl
            ((i . Term_Rewriting.showsl_lit
                    ": error when applying relative matchbounds\n") .
              x)))
      (\ tpa ->
        Error_Monad.catch_error
          (check_complexity_proof ia assms
            (Term_Rewriting.add_index i Arith.one_nat) (tpa, (cm, cc)) prf)
          (\ x ->
            Sum_Type.Inl
              ((i . Term_Rewriting.showsl_lit
                      ": error below applying relative matchbounds\n") .
                x))));
check_complexity_proof ia assms i (tp, (cm, cc)) (DT_Transformation info prf) =
  FOR_Preliminaries.debug i "DT Transformation"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (DT_Transformation_Impl.dt_transformation Labelings.Sharp ia info cm cc
          tp)
        (\ x ->
          Sum_Type.Inl
            ((((i . Term_Rewriting.showsl_lit
                      ": error when applying the DT transformation on\n") .
                QDP_Framework_Impl.showsl_tp ia tp) .
               Term_Rewriting.showsl_literal "\n") .
              x)))
      (\ (cma, tpa) ->
        Error_Monad.catch_error
          (check_complexity_proof ia assms
            (Term_Rewriting.add_index i Arith.one_nat) (tpa, (cma, cc)) prf)
          (\ x ->
            Sum_Type.Inl
              ((i . Term_Rewriting.showsl_lit
                      ": error below the DT transformation\n") .
                x))));
check_complexity_proof ia assms i (tp, (cm, cc)) (WDP_Transformation info prf) =
  FOR_Preliminaries.debug i "WDP Transformation"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (WDP_Transformation_Impl.check_wdp_trans Labelings.Sharp ia info cm cc
          tp)
        (\ x ->
          Sum_Type.Inl
            ((((i . Term_Rewriting.showsl_lit
                      ": error when applying the WDP transformation on\n") .
                QDP_Framework_Impl.showsl_tp ia tp) .
               Term_Rewriting.showsl_literal "\n") .
              x)))
      (\ (cma, tpa) ->
        Error_Monad.catch_error
          (check_complexity_proof ia assms
            (Term_Rewriting.add_index i Arith.one_nat) (tpa, (cma, cc)) prf)
          (\ x ->
            Sum_Type.Inl
              ((i . Term_Rewriting.showsl_lit
                      ": error below the WDP transformation\n") .
                x))));
check_complexity_proof ia assms i (tp, (cm, cc))
  (Usable_Rules_Complexity ur prf) =
  FOR_Preliminaries.debug i "Usable Rules"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (Usable_Rules_Complexity_Impl.usable_rules_complexity ia ur cm cc tp)
        (\ x ->
          Sum_Type.Inl
            ((i . Term_Rewriting.showsl_lit
                    ": error when applying usable rules\n") .
              x)))
      (\ tpa ->
        Error_Monad.catch_error
          (check_complexity_proof ia assms
            (Term_Rewriting.add_index i Arith.one_nat) (tpa, (cm, cc)) prf)
          (\ x ->
            Sum_Type.Inl
              ((i . Term_Rewriting.showsl_lit
                      ": error below applying usable rules\n") .
                x))));
check_complexity_proof ia assms i (tp, (cm, cc)) (Complexity_Assumption a ass) =
  FOR_Preliminaries.debug i "Complexity Assumption"
    (if assms
      then Error_Monad.bind
             (Error_Monad.catch_error
               (check_complexity_subsumes a
                 (Termination_Problem_Spec.q ia tp,
                   (Termination_Problem_Spec.r ia tp,
                     (Termination_Problem_Spec.rw ia tp, (cm, cc)))))
               (\ x ->
                 Sum_Type.Inl
                   ((i . Term_Rewriting.showsl_lit
                           ": error in complexity assumption or unknown proof\n") .
                     x)))
             (\ _ ->
               Error_Monad.catch_error
                 (Error_Monad.catch_error
                   (Error_Monad.forallM_index
                     (\ asa j ->
                       check_assm ia
                         (check_complexity_proof ia assms
                           (Term_Rewriting.add_index i (Arith.suc j)))
                         asa)
                     ass)
                   (\ x -> Sum_Type.Inl (snd x)))
                 (\ x ->
                   Sum_Type.Inl
                     ((i . Term_Rewriting.showsl_lit
                             ": error below unknown proof\n") .
                       x)))
      else Sum_Type.Inl
             (Term_Rewriting.showsl_lit
               "the proof contains an assumption or unknown proof which have to be manually allowed"));
check_complexity_proof ia assms i (tp, (cm, cc))
  (Split_Complexity info prf1 prf2) =
  FOR_Preliminaries.debug i "Split"
    (Error_Monad.bind
      (Error_Monad.catch_error
        (Complexity_Framework_Impl.split_proc_complexity ia info tp)
        (\ x ->
          Sum_Type.Inl
            ((i . Term_Rewriting.showsl_lit
                    ": error when applying split processor\n") .
              x)))
      (\ (tp1, tp2) ->
        Error_Monad.bind
          (Error_Monad.catch_error
            (check_complexity_proof ia assms
              (Term_Rewriting.add_index i Arith.one_nat) (tp1, (cm, cc)) prf1)
            (\ x ->
              Sum_Type.Inl
                ((i . Term_Rewriting.showsl_lit
                        ": error below applying split processor\n") .
                  x)))
          (\ _ ->
            Error_Monad.catch_error
              (check_complexity_proof ia assms
                (Term_Rewriting.add_index i
                  (Arith.nat_of_integer (2 :: Integer)))
                (tp2, (cm, cc)) prf2)
              (\ x ->
                Sum_Type.Inl
                  ((i . Term_Rewriting.showsl_lit
                          ": error below applying split processor\n") .
                    x)))));

}
