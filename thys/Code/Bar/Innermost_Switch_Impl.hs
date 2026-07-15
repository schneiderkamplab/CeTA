{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Innermost_Switch_Impl(switch_innermost_tt, switch_innermost_proc) where {

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
import qualified Check_Monad;
import qualified Error_Monad;
import qualified HOL;
import qualified Termination_Problem_Spec;
import qualified Critical_Pairs_Impl;
import qualified Renaming2;
import qualified Sum_Type;
import qualified Term_Rewriting;
import qualified Mapping;
import qualified Arith;
import qualified Shows_Literal;
import qualified Compare;
import qualified Fresh;

switch_innermost_tt ::
  forall a b c.
    (Arith.Ccompare a, Compare.Compare a, Fresh.Infinite a, Eq a,
      Mapping.Mapping_impl a, Shows_Literal.Showl a, Compare.Compare c, Eq c,
      Shows_Literal.Showl c) => Renaming2.Renaming2 a ->
                                  Termination_Problem_Spec.Tp_ops_ext b c a
                                    () ->
                                    Critical_Pairs_Impl.Join_info c a ->
                                      b -> Sum_Type.Sum (String -> String) b;
switch_innermost_tt ren i joins_i trs =
  let {
    r = Termination_Problem_Spec.rules i trs;
  } in (case let {
               cp = Critical_Pairs_Impl.critical_pairs_impl ren r r;
             } in Error_Monad.bind
                    (Error_Monad.catch_error
                      (Error_Monad.forallM
                        (\ (b, _) ->
                          Check_Monad.check b
                            (Shows_Literal.showsl_lit "rules are not overlay"))
                        cp)
                      (\ x -> Sum_Type.Inl (snd x)))
                    (\ _ ->
                      Error_Monad.bind
                        (Critical_Pairs_Impl.check_critical_pairs r cp joins_i)
                        (\ _ -> Term_Rewriting.check_wf_trs r))
         of {
         Sum_Type.Inl a -> Sum_Type.Inl a;
         Sum_Type.Inr _ ->
           Sum_Type.Inr (Termination_Problem_Spec.mk i True (map fst r) r []);
       });

switch_innermost_proc ::
  forall a b c.
    (Arith.Ccompare a, Compare.Compare a, Fresh.Infinite a, Eq a,
      Mapping.Mapping_impl a, Shows_Literal.Showl a, Compare.Compare c, Eq c,
      Shows_Literal.Showl c) => Renaming2.Renaming2 a ->
                                  Dependency_Pair_Problem_Spec.Dpp_ops_ext b c a
                                    () ->
                                    Critical_Pairs_Impl.Join_info c a ->
                                      b -> Sum_Type.Sum (String -> String) b;
switch_innermost_proc ren i joins_i dpp =
  let {
    r = Dependency_Pair_Problem_Spec.rw i dpp;
    p = Dependency_Pair_Problem_Spec.p i dpp;
    pw = Dependency_Pair_Problem_Spec.pw i dpp;
    nfs = Dependency_Pair_Problem_Spec.nfs i dpp;
  } in (case Error_Monad.bind
               (Error_Monad.catch_error
                 (Error_Monad.forallM
                   (\ (l, _) ->
                     Check_Monad.check (not (Term_Rewriting.is_Var l))
                       (Shows_Literal.showsl_lit
                         "left variables in R forbidden"))
                   (if nfs then r else []))
                 (\ x -> Sum_Type.Inl (snd x)))
               (\ _ ->
                 Error_Monad.bind
                   (Check_Monad.check
                     (Dependency_Pair_Problem_Spec.minimal i dpp)
                     (Shows_Literal.showsl_lit "minimality required"))
                   (\ _ ->
                     Error_Monad.bind
                       (Check_Monad.check
                         (null (Dependency_Pair_Problem_Spec.q i dpp))
                         (Shows_Literal.showsl_lit
                           "non-empty Q not yet supported"))
                       (\ _ ->
                         Error_Monad.bind
                           (Check_Monad.check
                             (null (Dependency_Pair_Problem_Spec.r i dpp))
                             (Shows_Literal.showsl_lit
                               "strict rules not allowed"))
                           (\ _ ->
                             Error_Monad.bind
                               (Check_Monad.check
                                 (null (Critical_Pairs_Impl.critical_pairs_impl
 ren (p ++ pw) r))
                                 (Shows_Literal.showsl_lit
                                   "overlaps between P and R not allowed"))
                               (\ _ ->
                                 Critical_Pairs_Impl.check_critical_pairs r
                                   (Critical_Pairs_Impl.critical_pairs_impl ren
                                     r r)
                                   joins_i)))))
         of {
         Sum_Type.Inl a -> Sum_Type.Inl a;
         Sum_Type.Inr _ ->
           Sum_Type.Inr
             (Dependency_Pair_Problem_Spec.mk i nfs True p pw (map fst r) [] r);
       });

}
