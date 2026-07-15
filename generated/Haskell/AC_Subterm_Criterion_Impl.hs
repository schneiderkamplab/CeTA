{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module AC_Subterm_Criterion_Impl(ac_subterm_proc, generalized_subterm_proc)
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
import qualified AC_Rewriting_Impl;
import qualified Status_Impl;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified HOL;
import qualified AC_Dependency_Pair_Problem_Spec;
import qualified Sum_Type;
import qualified AC_Subterm_Criterion;
import qualified Multiset;
import qualified Status;
import qualified Arith;
import qualified Compare;
import qualified Term_Rewriting;

weak_supt_mul ::
  forall a b.
    (Arith.Ceq a, Arith.Ccompare a, Compare.Compare a, Eq a, Compare.Compare b,
      Eq b) => Status.Status a ->
                 Arith.Set (a, Arith.Nat) ->
                   Term_Rewriting.Term a b -> Term_Rewriting.Term a b -> Bool;
weak_supt_mul =
  (\ proj f s t ->
    Multiset.multeqp_code (\ x y -> Term_Rewriting.supt_impl y x)
      (AC_Subterm_Criterion.proj_term proj f t)
      (AC_Subterm_Criterion.proj_term proj f s));

check_supteqproj_pred ::
  forall a b.
    (Arith.Ceq a, Arith.Ccompare a, Compare.Compare a, Eq a,
      Term_Rewriting.Showl a, Compare.Compare b, Eq b,
      Term_Rewriting.Showl b) => Status.Status a ->
                                   Arith.Set (a, Arith.Nat) ->
                                     (Term_Rewriting.Term a b,
                                       Term_Rewriting.Term a b) ->
                                       Sum_Type.Sum (String -> String) ();
check_supteqproj_pred pi f lr =
  Check_Monad.check (case lr of {
                      (a, b) -> weak_supt_mul pi f a b;
                    })
    ((Term_Rewriting.showsl_lit "could not orient rule " .
       Term_Rewriting.showsl_rule lr) .
      Term_Rewriting.showsl_lit " by supteq^mul");

strict_supt_mul ::
  forall a b.
    (Arith.Ceq a, Arith.Ccompare a, Compare.Compare a, Eq a, Compare.Compare b,
      Eq b) => Status.Status a ->
                 Arith.Set (a, Arith.Nat) ->
                   Term_Rewriting.Term a b -> Term_Rewriting.Term a b -> Bool;
strict_supt_mul =
  (\ proj f s t ->
    Multiset.multeqp_code (\ x y -> Term_Rewriting.supt_impl y x)
      (AC_Subterm_Criterion.proj_term proj f t)
      (AC_Subterm_Criterion.proj_term proj f s) &&
      not (Multiset.equal_multiset (AC_Subterm_Criterion.proj_term proj f s)
            (AC_Subterm_Criterion.proj_term proj f t)));

check_suptproj_pred ::
  forall a b.
    (Arith.Ceq a, Arith.Ccompare a, Compare.Compare a, Eq a,
      Term_Rewriting.Showl a, Compare.Compare b, Eq b,
      Term_Rewriting.Showl b) => Status.Status a ->
                                   Arith.Set (a, Arith.Nat) ->
                                     (Term_Rewriting.Term a b,
                                       Term_Rewriting.Term a b) ->
                                       Sum_Type.Sum (String -> String) ();
check_suptproj_pred pi f lr =
  Check_Monad.check (case lr of {
                      (a, b) -> strict_supt_mul pi f a b;
                    })
    ((Term_Rewriting.showsl_lit "could not orient rule " .
       Term_Rewriting.showsl_rule lr) .
      Term_Rewriting.showsl_lit " by supt^mul");

ac_subterm_proc ::
  forall a b c.
    (Arith.Ceq b, Arith.Ccompare b, Compare.Compare b, Eq b, Arith.Set_impl b,
      Term_Rewriting.Showl b, Compare.Compare c, Eq c,
      Term_Rewriting.Showl c) => AC_Dependency_Pair_Problem_Spec.Ac_dpp_ops_ext
                                   a b c () ->
                                   [((b, Arith.Nat), [Arith.Nat])] ->
                                     [(Term_Rewriting.Term b c,
Term_Rewriting.Term b c)] ->
                                       a -> Sum_Type.Sum (String -> String) a;
ac_subterm_proc i pi p_remove dpp =
  (case Error_Monad.catch_error
          (let {
             p = AC_Dependency_Pair_Problem_Spec.pairs i dpp;
             r = AC_Dependency_Pair_Problem_Spec.rules i dpp;
             e = AC_Dependency_Pair_Problem_Spec.e i dpp;
             re = r ++ e;
             f = map fst pi;
             ff = Arith.set f;
             pi_opt = Status_Impl.status_of pi;
           } in Error_Monad.bind
                  (Check_Monad.check (not (Arith.is_none pi_opt))
                    (Term_Rewriting.showsl_lit
                      "argument filter lists invalid positions"))
                  (\ _ ->
                    let {
                      pia = Arith.the pi_opt;
                      premove = Arith.set p_remove;
                    } in (case Arith.partition (\ lr -> Arith.member lr premove)
                                 p
                           of {
                           (ps, pns) ->
                             Error_Monad.bind
                               (Error_Monad.catch_error
                                 (Error_Monad.forallM
                                   (\ fa ->
                                     Check_Monad.check
                                       (not (null (Status.status pia fa)))
                                       ((Term_Rewriting.showsl_lit
   "status of symbol " .
  Term_Rewriting.showsl_prod fa) .
 Term_Rewriting.showsl_lit " in F must be non-empty"))
                                   f)
                                 (\ x -> Sum_Type.Inl (snd x)))
                               (\ _ ->
                                 Error_Monad.bind
                                   (Error_Monad.catch_error
                                     (AC_Rewriting_Impl.check_size_preserving_trs
                                       e)
                                     (\ x ->
                                       Sum_Type.Inl
 (Term_Rewriting.showsl_lit "E is not size preserving\n" . x)))
                                   (\ _ ->
                                     Error_Monad.bind
                                       (Error_Monad.catch_error
 (Error_Monad.forallM
   (\ (l, _) ->
     Check_Monad.check (not (Term_Rewriting.is_Var l))
       (Term_Rewriting.showsl_lit "variables as lhss not allowed"))
   re)
 (\ x -> Sum_Type.Inl (snd x)))
                                       (\ _ ->
 Error_Monad.bind
   (Error_Monad.catch_error
     (Error_Monad.catch_error
       (Error_Monad.forallM (check_supteqproj_pred pia ff)
         (filter
           (\ lr -> Arith.member (Arith.the (Term_Rewriting.root (fst lr))) ff)
           re))
       (\ x -> Sum_Type.Inl (snd x)))
     (\ x ->
       Sum_Type.Inl
         (Term_Rewriting.showsl_lit
            "problem when orienting rules with root in F\n" .
           x)))
   (\ _ ->
     Error_Monad.bind
       (Error_Monad.catch_error
         (Error_Monad.catch_error
           (Error_Monad.forallM (check_supteqproj_pred pia ff) pns)
           (\ x -> Sum_Type.Inl (snd x)))
         (\ x ->
           Sum_Type.Inl
             (Term_Rewriting.showsl_lit "problem when orienting DPs\n" . x)))
       (\ _ ->
         Error_Monad.catch_error
           (Error_Monad.catch_error
             (Error_Monad.forallM (check_suptproj_pred pia ff) ps)
             (\ x -> Sum_Type.Inl (snd x)))
           (\ x ->
             Sum_Type.Inl
               (Term_Rewriting.showsl_lit "problem when orienting DPs\n" .
                 x)))))));
                         })))
          (\ x ->
            Sum_Type.Inl
              (Term_Rewriting.showsl_lit
                 "could not apply the AC subterm processor\n" .
                x))
    of {
    Sum_Type.Inl a -> Sum_Type.Inl a;
    Sum_Type.Inr _ ->
      Sum_Type.Inr
        (AC_Dependency_Pair_Problem_Spec.delete_pairs_rules i dpp p_remove []);
  });

generalized_subterm_proc ::
  forall a b c.
    (Arith.Ceq b, Arith.Ccompare b, Compare.Compare b, Eq b, Arith.Set_impl b,
      Term_Rewriting.Showl b, Compare.Compare c, Eq c,
      Term_Rewriting.Showl c) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b c
                                   () ->
                                   [((b, Arith.Nat), [Arith.Nat])] ->
                                     [(Term_Rewriting.Term b c,
Term_Rewriting.Term b c)] ->
                                       a -> Sum_Type.Sum (String -> String) a;
generalized_subterm_proc i pi p_remove dpp =
  (case Error_Monad.catch_error
          (let {
             p = Dependency_Pair_Problem_Spec.pairs i dpp;
             r = Dependency_Pair_Problem_Spec.rules i dpp;
             f = map fst pi;
             ff = Arith.set f;
             pi_opt = Status_Impl.status_of pi;
           } in Error_Monad.bind
                  (Check_Monad.check
                    (null (Dependency_Pair_Problem_Spec.q i dpp))
                    (Term_Rewriting.showsl_lit
                      "currently generalized subterm criterion does not support strategies"))
                  (\ _ ->
                    Error_Monad.bind
                      (Check_Monad.check
                        (Dependency_Pair_Problem_Spec.minimal i dpp)
                        (Term_Rewriting.showsl_lit "minimality required"))
                      (\ _ ->
                        Error_Monad.bind
                          (Check_Monad.check (not (Arith.is_none pi_opt))
                            (Term_Rewriting.showsl_lit
                              "argument filter lists invalid positions"))
                          (\ _ ->
                            let {
                              pia = Arith.the pi_opt;
                              premove = Arith.set p_remove;
                            } in (case Arith.partition
 (\ lr -> Arith.member lr premove) p
                                   of {
                                   (ps, pns) ->
                                     Error_Monad.bind
                                       (Error_Monad.catch_error
 (Error_Monad.forallM
   (\ fa ->
     Check_Monad.check (not (null (Status.status pia fa)))
       ((Term_Rewriting.showsl_lit "status of symbol " .
          Term_Rewriting.showsl_prod fa) .
         Term_Rewriting.showsl_lit " in F must be non-empty"))
   f)
 (\ x -> Sum_Type.Inl (snd x)))
                                       (\ _ ->
 Error_Monad.bind
   (Error_Monad.catch_error
     (Error_Monad.forallM
       (\ (l, _) ->
         Check_Monad.check (not (Term_Rewriting.is_Var l))
           (Term_Rewriting.showsl_lit "variables as lhss not allowed"))
       r)
     (\ x -> Sum_Type.Inl (snd x)))
   (\ _ ->
     Error_Monad.bind
       (Error_Monad.catch_error
         (Error_Monad.catch_error
           (Error_Monad.forallM (check_supteqproj_pred pia ff)
             (filter
               (\ lr ->
                 Arith.member (Arith.the (Term_Rewriting.root (fst lr))) ff)
               r))
           (\ x -> Sum_Type.Inl (snd x)))
         (\ x ->
           Sum_Type.Inl
             (Term_Rewriting.showsl_lit
                "problem when orienting rules with root in F\n" .
               x)))
       (\ _ ->
         Error_Monad.bind
           (Error_Monad.catch_error
             (Error_Monad.catch_error
               (Error_Monad.forallM (check_supteqproj_pred pia ff) pns)
               (\ x -> Sum_Type.Inl (snd x)))
             (\ x ->
               Sum_Type.Inl
                 (Term_Rewriting.showsl_lit "problem when orienting DPs\n" .
                   x)))
           (\ _ ->
             Error_Monad.catch_error
               (Error_Monad.catch_error
                 (Error_Monad.forallM (check_suptproj_pred pia ff) ps)
                 (\ x -> Sum_Type.Inl (snd x)))
               (\ x ->
                 Sum_Type.Inl
                   (Term_Rewriting.showsl_lit "problem when orienting DPs\n" .
                     x))))));
                                 })))))
          (\ x ->
            Sum_Type.Inl
              (Term_Rewriting.showsl_lit
                 "could not apply the subterm processor\n" .
                x))
    of {
    Sum_Type.Inl a -> Sum_Type.Inl a;
    Sum_Type.Inr _ ->
      Sum_Type.Inr
        (Dependency_Pair_Problem_Spec.delete_P_Pw i dpp p_remove p_remove);
  });

}
