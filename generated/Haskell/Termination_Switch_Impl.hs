{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Termination_Switch_Impl(switch_termination_tt, switch_termination_proc)
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
import qualified Dependency_Pair_Problem_Spec;
import qualified Q_Restricted_Rewriting_Impl;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified HOL;
import qualified Termination_Problem_Spec;
import qualified Critical_Pairs_Impl;
import qualified Renaming2;
import qualified Sum_Type;
import qualified Mapping;
import qualified Arith;
import qualified Term_Rewriting;
import qualified Fresh;
import qualified Compare;

switch_termination_tt ::
  forall a b c.
    (Arith.Ccompare a, Compare.Compare a, Fresh.Infinite a, Eq a,
      Mapping.Mapping_impl a, Term_Rewriting.Showl a, Compare.Compare_order c,
      Eq c,
      Term_Rewriting.Showl c) => Renaming2.Renaming2 a ->
                                   Termination_Problem_Spec.Tp_ops_ext b c a
                                     () ->
                                     Critical_Pairs_Impl.Join_info c a ->
                                       b -> Sum_Type.Sum (String -> String) b;
switch_termination_tt ren i joins_i tp =
  let {
    r = Termination_Problem_Spec.rules i tp;
    q = Termination_Problem_Spec.q i tp;
  } in (case let {
               cp = Critical_Pairs_Impl.critical_pairs_impl ren r r;
             } in Error_Monad.bind
                    (Error_Monad.catch_error
                      (Error_Monad.forallM
                        (\ (b, _) ->
                          Check_Monad.check b
                            (Term_Rewriting.showsl_lit "rules are not overlay"))
                        cp)
                      (\ x -> Sum_Type.Inl (snd x)))
                    (\ _ ->
                      Error_Monad.bind (Term_Rewriting.check_wf_trs r)
                        (\ _ ->
                          Error_Monad.bind
                            (Critical_Pairs_Impl.check_critical_pairs r cp
                              joins_i)
                            (\ _ ->
                              Error_Monad.catch_error
                                (Q_Restricted_Rewriting_Impl.check_NF_trs_subset
                                  r q)
                                (\ x ->
                                  Sum_Type.Inl
                                    (Term_Rewriting.showsl_terma x .
                                      Term_Rewriting.showsl_lit
" is not in normal form w.r.t. R")))))
         of {
         Sum_Type.Inl a -> Sum_Type.Inl a;
         Sum_Type.Inr _ ->
           Sum_Type.Inr
             (Termination_Problem_Spec.mk i (Termination_Problem_Spec.nfs i tp)
               [] r []);
       });

switch_termination_proc ::
  forall a b c.
    (Arith.Ccompare a, Compare.Compare a, Fresh.Infinite a, Eq a,
      Mapping.Mapping_impl a, Term_Rewriting.Showl a, Compare.Compare_order c,
      Eq c,
      Term_Rewriting.Showl c) => Renaming2.Renaming2 a ->
                                   Dependency_Pair_Problem_Spec.Dpp_ops_ext b c
                                     a () ->
                                     Critical_Pairs_Impl.Join_info c a ->
                                       b -> Sum_Type.Sum (String -> String) b;
switch_termination_proc ren i joins_i dpp =
  let {
    p = Dependency_Pair_Problem_Spec.pairs i dpp;
    r = Dependency_Pair_Problem_Spec.rules i dpp;
    q = Dependency_Pair_Problem_Spec.q i dpp;
  } in (case let {
               cp = Critical_Pairs_Impl.critical_pairs_impl ren r r;
             } in Error_Monad.bind
                    (Error_Monad.catch_error
                      (Error_Monad.forallM
                        (\ (b, _) ->
                          Check_Monad.check b
                            (Term_Rewriting.showsl_lit "rules are not overlay"))
                        cp)
                      (\ x -> Sum_Type.Inl (snd x)))
                    (\ _ ->
                      Error_Monad.bind (Term_Rewriting.check_wf_trs r)
                        (\ _ ->
                          Error_Monad.bind
                            (Critical_Pairs_Impl.check_critical_pairs r cp
                              joins_i)
                            (\ _ ->
                              Error_Monad.bind
                                (Check_Monad.check
                                  (null (Critical_Pairs_Impl.critical_pairs_impl
  ren p r))
                                  (Term_Rewriting.showsl_lit
                                    "there are overlaps between P and R"))
                                (\ _ ->
                                  Error_Monad.catch_error
                                    (Q_Restricted_Rewriting_Impl.check_NF_trs_subset
                                      r q)
                                    (\ x ->
                                      Sum_Type.Inl
(Term_Rewriting.showsl_terma x .
  Term_Rewriting.showsl_lit " is not in normal form w.r.t. R"))))))
         of {
         Sum_Type.Inl a -> Sum_Type.Inl a;
         Sum_Type.Inr _ ->
           Sum_Type.Inr
             (Dependency_Pair_Problem_Spec.mk i
               (Dependency_Pair_Problem_Spec.nfs i dpp) False p [] [] [] r);
       });

}
