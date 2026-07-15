{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Q_Reduction_Impl(q_reduction_proc) where {

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
import qualified Q_Restricted_Rewriting_Impl;
import qualified QDP_Framework_Impl;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified HOL;
import qualified Dependency_Pair_Problem_Spec;
import qualified Sum_Type;
import qualified Term_Rewriting;
import qualified Mapping;
import qualified Arith;
import qualified Compare;
import qualified Shows_Literal;

q_reduction_proc_non_min ::
  forall a b c.
    (Shows_Literal.Showl b,
      Shows_Literal.Showl c) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b c
                                  () ->
                                  [Term_Rewriting.Term b c] ->
                                    a -> Sum_Type.Sum (String -> String) a;
q_reduction_proc_non_min i q dpp =
  (case Error_Monad.catch_error
          (Error_Monad.bind
            (Error_Monad.catch_error
              (Q_Restricted_Rewriting_Impl.check_NF_terms_subset
                (Dependency_Pair_Problem_Spec.is_QNF i dpp) q)
              (\ x ->
                Sum_Type.Inl
                  ((Shows_Literal.showsl_lit "the term " .
                     Term_Rewriting.showsl_terma x) .
                    Shows_Literal.showsl_lit " is not allowed in Q\' ")))
            (\ _ -> Sum_Type.Inr ()))
          (\ x ->
            Sum_Type.Inl
              (((((Shows_Literal.showsl_lit
                     "problem when reducing Q in the DP problem\n" .
                    QDP_Framework_Impl.showsl_dpp i dpp) .
                   Shows_Literal.showsl_lit "\nto the set\n") .
                  QDP_Framework_Impl.showsl_terms "Q\':" q) .
                 Shows_Literal.showsl_literal "\n") .
                x))
    of {
    Sum_Type.Inl a -> Sum_Type.Inl a;
    Sum_Type.Inr _ ->
      Sum_Type.Inr
        (Dependency_Pair_Problem_Spec.mk i
          (Dependency_Pair_Problem_Spec.nfs i dpp) False
          (Dependency_Pair_Problem_Spec.p i dpp)
          (Dependency_Pair_Problem_Spec.pw i dpp) q
          (Dependency_Pair_Problem_Spec.r i dpp)
          (Dependency_Pair_Problem_Spec.rw i dpp));
  });

q_reduction_proc_min_inn ::
  forall a b c.
    (Compare.Compare_order b, Eq b, Shows_Literal.Showl b, Arith.Ccompare c,
      Eq c, Mapping.Mapping_impl c,
      Shows_Literal.Showl c) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b c
                                  () ->
                                  [Term_Rewriting.Term b c] ->
                                    a -> Sum_Type.Sum (String -> String) a;
q_reduction_proc_min_inn i q dpp =
  let {
    pb = Dependency_Pair_Problem_Spec.pairs i dpp;
    rb = Dependency_Pair_Problem_Spec.rules i dpp;
    f = map Just (Term_Rewriting.funas_trs_list (pb ++ rb));
    qa = Dependency_Pair_Problem_Spec.q i dpp;
    isnf = Dependency_Pair_Problem_Spec.is_QNF i dpp;
    qq = filter (\ qb -> all isnf (Term_Rewriting.args qb)) qa;
    rQ = filter (\ qb -> Arith.membera f (Term_Rewriting.root qb)) qq;
  } in (case Error_Monad.catch_error
               (Error_Monad.bind
                 (Check_Monad.check
                   (Dependency_Pair_Problem_Spec.nFQ_subset_NF_rules i dpp)
                   (Shows_Literal.showsl_lit "innermost rewriting required"))
                 (\ _ ->
                   Error_Monad.bind (Term_Rewriting.check_wf_trs rb)
                     (\ _ ->
                       Error_Monad.bind
                         (Error_Monad.catch_error
                           (Q_Restricted_Rewriting_Impl.check_NF_terms_subset
                             (Term_Rewriting.is_NF_terms q) rQ)
                           (\ x ->
                             Sum_Type.Inl
                               ((Shows_Literal.showsl_lit "the term " .
                                  Term_Rewriting.showsl_terma x) .
                                 Shows_Literal.showsl_lit
                                   " is missing in Q\' ")))
                         (\ _ ->
                           Error_Monad.bind
                             (Error_Monad.catch_error
                               (Q_Restricted_Rewriting_Impl.check_NF_terms_subset
                                 (Term_Rewriting.is_NF_terms qq) q)
                               (\ x ->
                                 Sum_Type.Inl
                                   ((Shows_Literal.showsl_lit "the term " .
                                      Term_Rewriting.showsl_terma x) .
                                     Shows_Literal.showsl_lit
                                       " is not allowed in Q\' ")))
                             (\ _ ->
                               (if Dependency_Pair_Problem_Spec.nfs i dpp
                                 then Sum_Type.Inr ()
                                 else Term_Rewriting.check_varcond_subset
pb))))))
               (\ x ->
                 Sum_Type.Inl
                   (((((Shows_Literal.showsl_lit
                          "problem when reducing Q in the DP problem\n" .
                         QDP_Framework_Impl.showsl_dpp i dpp) .
                        Shows_Literal.showsl_lit "\nto the set\n") .
                       QDP_Framework_Impl.showsl_terms "Q\':" q) .
                      Shows_Literal.showsl_literal "\n") .
                     x))
         of {
         Sum_Type.Inl a -> Sum_Type.Inl a;
         Sum_Type.Inr _ ->
           Sum_Type.Inr
             (Dependency_Pair_Problem_Spec.mk i
               (Dependency_Pair_Problem_Spec.nfs i dpp)
               (Dependency_Pair_Problem_Spec.minimal i dpp)
               (Dependency_Pair_Problem_Spec.p i dpp)
               (Dependency_Pair_Problem_Spec.pw i dpp) q
               (Dependency_Pair_Problem_Spec.r i dpp)
               (Dependency_Pair_Problem_Spec.rw i dpp));
       });

q_reduction_proc ::
  forall a b c.
    (Compare.Compare_order b, Eq b, Shows_Literal.Showl b, Arith.Ccompare c,
      Eq c, Mapping.Mapping_impl c,
      Shows_Literal.Showl c) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b c
                                  () ->
                                  [Term_Rewriting.Term b c] ->
                                    a -> Sum_Type.Sum (String -> String) a;
q_reduction_proc i q dpp =
  (case q_reduction_proc_min_inn i q dpp of {
    Sum_Type.Inl _ -> q_reduction_proc_non_min i q dpp;
    Sum_Type.Inr a -> Sum_Type.Inr a;
  });

}
