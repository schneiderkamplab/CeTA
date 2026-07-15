{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  AC_Reduction_Pair_Processor_Impl(ac_rule_removal, ac_ur_redpair_proc,
                                    ac_mono_ur_redpair_proc)
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
import qualified Term_Order;
import qualified AC_Rewriting_Impl;
import qualified Usable_Rules_Impl;
import qualified Check_Monad;
import qualified AC_Dependency_Pair_Problem_Spec;
import qualified Mapping;
import qualified Error_Monad;
import qualified HOL;
import qualified AC_Termination_Problem_Spec;
import qualified Sum_Type;
import qualified Shows_Literal;
import qualified Compare;
import qualified Arith;
import qualified Term_Rewriting;

ac_rule_removal ::
  forall a b c.
    (Compare.Compare b, Eq b, Shows_Literal.Showl b, Compare.Compare c, Eq c,
      Shows_Literal.Showl c) => AC_Termination_Problem_Spec.Ac_tp_ops_ext a b c
                                  () ->
                                  Term_Rewriting.Rel_impl_ext b c () ->
                                    [(Term_Rewriting.Term b c,
                                       Term_Rewriting.Term b c)] ->
                                      a -> Sum_Type.Sum (String -> String) a;
ac_rule_removal i rp r_remove tp =
  (case Error_Monad.catch_error
          (let {
             r = AC_Termination_Problem_Spec.r i tp;
             e = AC_Termination_Problem_Spec.e i tp;
             rremove = Arith.set r_remove;
             rns = filter (\ lr -> not (Arith.member lr rremove)) r;
           } in Error_Monad.bind
                  (Term_Rewriting.rel_impl_mono_redpair rp r_remove (rns ++ e))
                  (\ _ ->
                    Error_Monad.bind
                      (Error_Monad.catch_error
                        (Term_Rewriting.rel_impl_ns rp rns)
                        (\ x ->
                          Sum_Type.Inl
                            (Shows_Literal.showsl_lit
                               "problem when orienting weak rules\n" .
                              x)))
                      (\ _ ->
                        Error_Monad.bind
                          (Error_Monad.catch_error
                            (Term_Rewriting.rel_impl_ns rp e)
                            (\ x ->
                              Sum_Type.Inl
                                (Shows_Literal.showsl_lit
                                   "problem when orienting equations\n" .
                                  x)))
                          (\ _ ->
                            Error_Monad.catch_error
                              (Term_Rewriting.rel_impl_s rp r_remove)
                              (\ x ->
                                Sum_Type.Inl
                                  (Shows_Literal.showsl_lit
                                     "problem when orienting strict rules\n" .
                                    x))))))
          (\ x ->
            Sum_Type.Inl
              (((Shows_Literal.showsl_lit
                   "could not apply AC rule removal with the following\n" .
                  Term_Rewriting.desc rp) .
                 Shows_Literal.showsl_literal "\n") .
                x))
    of {
    Sum_Type.Inl a -> Sum_Type.Inl a;
    Sum_Type.Inr _ ->
      Sum_Type.Inr (AC_Termination_Problem_Spec.delete_rules i tp r_remove);
  });

ac_ur_redpair_proc ::
  forall a b c.
    (Arith.Cenum b, Arith.Ceq b, Arith.Ccompare b, Compare.Compare b, Eq b,
      Arith.Set_impl b, Shows_Literal.Showl b, Arith.Ccompare c,
      Compare.Compare c, Eq c, Mapping.Mapping_impl c,
      Shows_Literal.Showl c) => AC_Dependency_Pair_Problem_Spec.Ac_dpp_ops_ext a
                                  b c () ->
                                  Term_Rewriting.Rel_impl_ext b c () ->
                                    [(Term_Rewriting.Term b c,
                                       Term_Rewriting.Term b c)] ->
                                      [(Term_Rewriting.Term b c,
 Term_Rewriting.Term b c)] ->
a -> Sum_Type.Sum (String -> String) a;
ac_ur_redpair_proc i rp p_remove ur dpp =
  (case Error_Monad.catch_error
          (let {
             p = AC_Dependency_Pair_Problem_Spec.pairs i dpp;
             _ = AC_Dependency_Pair_Problem_Spec.rules i dpp;
             e = AC_Dependency_Pair_Problem_Spec.e i dpp;
             premove = Arith.set p_remove;
           } in (case Arith.partition (\ lr -> Arith.member lr premove) p of {
                  (ps, pns) ->
                    let {
                      rm = AC_Dependency_Pair_Problem_Spec.eq_rules_map i dpp;
                      pi = Term_Rewriting.af rp;
                    } in Error_Monad.bind (Term_Rewriting.rel_impl_redtriple rp)
                           (\ _ ->
                             Error_Monad.bind (Term_Rewriting.ce_compat rp)
                               (\ _ ->
                                 Error_Monad.bind
                                   (Error_Monad.catch_error
                                     (AC_Rewriting_Impl.check_symmetric_AC_theory
                                       e)
                                     (\ x ->
                                       Sum_Type.Inl
 (Shows_Literal.showsl_lit "usable rules demand symmetric AC theory\n" . x)))
                                   (\ _ ->
                                     Error_Monad.bind
                                       (Error_Monad.catch_error
 (Error_Monad.forallM
   (\ (l, _) ->
     Check_Monad.check (not (Term_Rewriting.is_Var l))
       (Shows_Literal.showsl_lit "variables as lhss not allowed"))
   (AC_Dependency_Pair_Problem_Spec.r i dpp ++
     AC_Dependency_Pair_Problem_Spec.rw i dpp))
 (\ x -> Sum_Type.Inl (snd x)))
                                       (\ _ ->
 Error_Monad.bind (Usable_Rules_Impl.check_ur_P_closed_rm_af rm ur pi p)
   (\ _ ->
     Error_Monad.bind
       (Error_Monad.catch_error (Term_Rewriting.rel_impl_ns rp ur)
         (\ x ->
           Sum_Type.Inl
             (Shows_Literal.showsl_lit "problem when orienting usable rules\n" .
               x)))
       (\ _ ->
         Error_Monad.bind
           (Error_Monad.catch_error (Term_Rewriting.rel_impl_nst rp pns)
             (\ x ->
               Sum_Type.Inl
                 (Shows_Literal.showsl_lit "problem when orienting DPs\n" . x)))
           (\ _ ->
             Error_Monad.catch_error (Term_Rewriting.rel_impl_s rp ps)
               (\ x ->
                 Sum_Type.Inl
                   (Shows_Literal.showsl_lit "problem when orienting DPs\n" .
                     x)))))))));
                }))
          (\ x ->
            Sum_Type.Inl
              (((Shows_Literal.showsl_lit
                   "could not apply the AC reduction pair processor with usable rules and the following\n" .
                  Term_Rewriting.desc rp) .
                 Shows_Literal.showsl_literal "\n") .
                x))
    of {
    Sum_Type.Inl a -> Sum_Type.Inl a;
    Sum_Type.Inr _ ->
      Sum_Type.Inr
        (AC_Dependency_Pair_Problem_Spec.delete_pairs_rules i dpp p_remove []);
  });

ac_mono_ur_redpair_proc ::
  forall a b c.
    (Arith.Cenum b, Arith.Ceq b, Arith.Ccompare b, Compare.Compare b, Eq b,
      Arith.Set_impl b, Shows_Literal.Showl b, Arith.Ccompare c,
      Compare.Compare c, Eq c, Mapping.Mapping_impl c,
      Shows_Literal.Showl c) => AC_Dependency_Pair_Problem_Spec.Ac_dpp_ops_ext a
                                  b c () ->
                                  Term_Rewriting.Rel_impl_ext b c () ->
                                    [(Term_Rewriting.Term b c,
                                       Term_Rewriting.Term b c)] ->
                                      [(Term_Rewriting.Term b c,
 Term_Rewriting.Term b c)] ->
[(Term_Rewriting.Term b c, Term_Rewriting.Term b c)] ->
  a -> Sum_Type.Sum (String -> String) a;
ac_mono_ur_redpair_proc i rp p_remove r_remove ur dpp =
  (case Error_Monad.catch_error
          (let {
             p = AC_Dependency_Pair_Problem_Spec.pairs i dpp;
             _ = AC_Dependency_Pair_Problem_Spec.rules i dpp;
             e = AC_Dependency_Pair_Problem_Spec.e i dpp;
             premove = Arith.set p_remove;
             rremove = Arith.set r_remove;
             us = Arith.foldr (Arith.sup_set . Term_Rewriting.funas_term . snd)
                    (p ++ ur) Arith.bot_set;
             filt =
               (\ lr ->
                 Arith.ball (Term_Rewriting.funas_term (fst lr))
                   (\ f -> Arith.member f us));
           } in (case Arith.partition
                        (\ lr -> Arith.member lr premove && filt lr) p
                  of {
                  (ps, pns) ->
                    (case Arith.partition
                            (\ lr -> Arith.member lr rremove && filt lr) ur
                      of {
                      (urs, urns) ->
                        let {
                          rm = AC_Dependency_Pair_Problem_Spec.eq_rules_map i
                                 dpp;
                        } in Error_Monad.bind
                               (Term_Rewriting.rel_impl_mono_ce_redpair rp
                                 (ps ++ urs) (urns ++ pns))
                               (\ _ ->
                                 Error_Monad.bind
                                   (Error_Monad.catch_error
                                     (AC_Rewriting_Impl.check_symmetric_AC_theory
                                       e)
                                     (\ x ->
                                       Sum_Type.Inl
 (Shows_Literal.showsl_lit "usable rules demand symmetric AC theory\n" . x)))
                                   (\ _ ->
                                     Error_Monad.bind
                                       (Error_Monad.catch_error
 (Error_Monad.forallM
   (\ (l, _) ->
     Check_Monad.check (not (Term_Rewriting.is_Var l))
       (Shows_Literal.showsl_lit "variables as lhss not allowed"))
   (AC_Dependency_Pair_Problem_Spec.r i dpp ++
     AC_Dependency_Pair_Problem_Spec.rw i dpp))
 (\ x -> Sum_Type.Inl (snd x)))
                                       (\ _ ->
 Error_Monad.bind
   (Usable_Rules_Impl.check_ur_P_closed_rm_af rm ur Term_Order.full_af p)
   (\ _ ->
     Error_Monad.bind
       (Error_Monad.catch_error (Term_Rewriting.rel_impl_ns rp urns)
         (\ x ->
           Sum_Type.Inl
             (Shows_Literal.showsl_lit "problem when orienting usable rules\n" .
               x)))
       (\ _ ->
         Error_Monad.bind
           (Error_Monad.catch_error (Term_Rewriting.rel_impl_s rp urs)
             (\ x ->
               Sum_Type.Inl
                 (Shows_Literal.showsl_lit
                    "problem when orienting usable rules\n" .
                   x)))
           (\ _ ->
             Error_Monad.bind
               (Error_Monad.catch_error (Term_Rewriting.rel_impl_ns rp pns)
                 (\ x ->
                   Sum_Type.Inl
                     (Shows_Literal.showsl_lit "problem when orienting DPs\n" .
                       x)))
               (\ _ ->
                 Error_Monad.catch_error (Term_Rewriting.rel_impl_s rp ps)
                   (\ x ->
                     Sum_Type.Inl
                       (Shows_Literal.showsl_lit
                          "problem when orienting DPs\n" .
                         x)))))))));
                    });
                }))
          (\ x ->
            Sum_Type.Inl
              (((Shows_Literal.showsl_lit
                   "could not apply the monotonic AC reduction pair processor with usable rules and the following\n" .
                  Term_Rewriting.desc rp) .
                 Shows_Literal.showsl_literal "\n") .
                x))
    of {
    Sum_Type.Inl a -> Sum_Type.Inl a;
    Sum_Type.Inr _ ->
      Sum_Type.Inr
        (AC_Dependency_Pair_Problem_Spec.delete_pairs_rules i dpp p_remove
          r_remove);
  });

}
