{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Usable_Rules_Impl(check_ur_P_closed_rm_af, mono_ur_redpair_proc) where {

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
import qualified Check_Monad;
import qualified Error_Monad;
import qualified HOL;
import qualified Dependency_Pair_Problem_Spec;
import qualified Sum_Type;
import qualified Compare;
import qualified Tcap_Impl;
import qualified Term_Rewriting;
import qualified Arith;

matchCapRMBelow ::
  forall a b.
    (Eq a,
      Eq b) => ((a, Arith.Nat) ->
                 [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]) ->
                 Term_Rewriting.Term a b -> Term_Rewriting.Term a b -> Bool;
matchCapRMBelow rm l (Term_Rewriting.Fun f ts) =
  Term_Rewriting.matcha (Term_Rewriting.GCFun f (map (Tcap_Impl.tcapRM2 rm) ts))
    l;

check_ur_closed_term_rm_af ::
  forall a b.
    (Eq a, Term_Rewriting.Showl a, Eq b,
      Term_Rewriting.Showl b) => ((a, Arith.Nat) ->
                                   [(Term_Rewriting.Term a b,
                                      Term_Rewriting.Term a b)]) ->
                                   [(Term_Rewriting.Term a b,
                                      Term_Rewriting.Term a b)] ->
                                     ((a, Arith.Nat) -> Arith.Set Arith.Nat) ->
                                       Term_Rewriting.Term a b ->
 Sum_Type.Sum (String -> String) ();
check_ur_closed_term_rm_af uu uv uw (Term_Rewriting.Var x) = Sum_Type.Inr ();
check_ur_closed_term_rm_af rm ur pi (Term_Rewriting.Fun f ts) =
  let {
    n = Arith.size_list ts;
    pia = pi (f, n);
  } in Error_Monad.bind
         (Error_Monad.catch_error
           (Error_Monad.forallM_index
             (\ t i ->
               (if Arith.member i pia then check_ur_closed_term_rm_af rm ur pi t
                 else Sum_Type.Inr ()))
             ts)
           (\ x -> Sum_Type.Inl (snd x)))
         (\ _ ->
           Error_Monad.catch_error
             (Error_Monad.forallM
               (\ lr ->
                 Check_Monad.check
                   (Arith.membera ur lr ||
                     not (matchCapRMBelow rm (fst lr)
                           (Term_Rewriting.Fun f ts)))
                   ((((Term_Rewriting.showsl_lit "due to the subterm " .
                        Term_Rewriting.showsl_terma (Term_Rewriting.Fun f ts)) .
                       Term_Rewriting.showsl_lit " of some usable rhs, rule ") .
                      Term_Rewriting.showsl_rule lr) .
                     Term_Rewriting.showsl_lit " should be usable."))
               (rm (f, n)))
             (\ x -> Sum_Type.Inl (snd x)));

check_ur_P_closed_rm_af ::
  forall a b.
    (Eq a, Term_Rewriting.Showl a, Eq b,
      Term_Rewriting.Showl b) => ((a, Arith.Nat) ->
                                   [(Term_Rewriting.Term a b,
                                      Term_Rewriting.Term a b)]) ->
                                   [(Term_Rewriting.Term a b,
                                      Term_Rewriting.Term a b)] ->
                                     ((a, Arith.Nat) -> Arith.Set Arith.Nat) ->
                                       [(Term_Rewriting.Term a b,
  Term_Rewriting.Term a b)] ->
 Sum_Type.Sum (String -> String) ();
check_ur_P_closed_rm_af rm ur pi p =
  Error_Monad.bind
    (Error_Monad.catch_error
      (Error_Monad.catch_error
        (Error_Monad.forallM
          (\ lr -> check_ur_closed_term_rm_af rm ur pi (snd lr)) ur)
        (\ x -> Sum_Type.Inl (snd x)))
      (\ x ->
        Sum_Type.Inl
          (Term_Rewriting.showsl_lit
             "error when checking closure properties of rhs of usable rules\n" .
            x)))
    (\ _ ->
      Error_Monad.catch_error
        (Error_Monad.catch_error
          (Error_Monad.forallM
            (\ st -> check_ur_closed_term_rm_af rm ur pi (snd st)) p)
          (\ x -> Sum_Type.Inl (snd x)))
        (\ x ->
          Sum_Type.Inl
            (Term_Rewriting.showsl_lit
               "error when checking closure properties of rhs of DPs\n" .
              x)));

mono_ur_redpair_proc ::
  forall a b c.
    (Arith.Ceq b, Arith.Ccompare b, Compare.Compare b, Eq b, Arith.Set_impl b,
      Term_Rewriting.Showl b, Compare.Compare c, Eq c,
      Term_Rewriting.Showl c) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b c
                                   () ->
                                   Term_Rewriting.Rel_impl_ext b c () ->
                                     [(Term_Rewriting.Term b c,
Term_Rewriting.Term b c)] ->
                                       [(Term_Rewriting.Term b c,
  Term_Rewriting.Term b c)] ->
 [(Term_Rewriting.Term b c, Term_Rewriting.Term b c)] ->
   a -> Sum_Type.Sum (String -> String) a;
mono_ur_redpair_proc i rp premove rrem ur dpp =
  let {
    r = Dependency_Pair_Problem_Spec.rules i dpp;
    ura = Arith.set ur;
    non_ur = filter (\ ra -> not (Arith.member ra ura)) r;
    rremove = non_ur ++ rrem;
  } in (case Error_Monad.catch_error
               (Error_Monad.bind
                 (Check_Monad.check (Dependency_Pair_Problem_Spec.minimal i dpp)
                   (Term_Rewriting.showsl_lit "minimality required"))
                 (\ _ ->
                   Error_Monad.bind
                     (Check_Monad.check
                       (if Dependency_Pair_Problem_Spec.nfs i dpp
                         then (if not (Dependency_Pair_Problem_Spec.q_empty i
dpp)
                                then Dependency_Pair_Problem_Spec.wwf_rules i
                                       dpp
                                else True)
                         else True)
                       (Term_Rewriting.showsl_lit "well formedness required"))
                     (\ _ ->
                       let {
                         p = Dependency_Pair_Problem_Spec.pairs i dpp;
                         us = Arith.foldr
                                (Arith.sup_set .
                                  Term_Rewriting.funas_term . snd)
                                (p ++ ur) Arith.bot_set;
                         rr = Arith.set rremove;
                         filt =
                           (\ lr ->
                             Arith.ball (Term_Rewriting.funas_term (fst lr))
                               (\ f -> Arith.member f us));
                       } in (case Dependency_Pair_Problem_Spec.split_pairs i dpp
                                    premove
                              of {
                              (pms, pns) ->
                                (case Arith.partition filt pms of {
                                  (ps, pnwf) ->
                                    (case Arith.partition
    (\ u -> Arith.member u rr) ur
                                      of {
                                      (urms, urns) ->
(case Arith.partition filt urms of {
  (urs, urnwf) ->
    let {
      rm = Dependency_Pair_Problem_Spec.rules_map i dpp;
    } in Error_Monad.bind
           (Term_Rewriting.rel_impl_mono_ce_redpair rp (ps ++ urs)
             (urns ++ urnwf ++ pns ++ pnwf))
           (\ _ ->
             Error_Monad.bind
               (check_ur_P_closed_rm_af rm ur Term_Order.full_af p)
               (\ _ ->
                 Error_Monad.bind
                   (Error_Monad.catch_error
                     (Error_Monad.forallM
                       (\ (l, _) ->
                         Check_Monad.check (not (Term_Rewriting.is_Var l))
                           (Term_Rewriting.showsl_lit
                             "variables as lhss not allowed"))
                       (Dependency_Pair_Problem_Spec.rules i dpp))
                     (\ x -> Sum_Type.Inl (snd x)))
                   (\ _ ->
                     Error_Monad.bind
                       (Error_Monad.catch_error
                         (Term_Rewriting.rel_impl_ns rp (urns ++ urnwf))
                         (\ x ->
                           Sum_Type.Inl
                             (Term_Rewriting.showsl_lit
                                "problem when orienting usable rules\n" .
                               x)))
                       (\ _ ->
                         Error_Monad.bind
                           (Error_Monad.catch_error
                             (Term_Rewriting.rel_impl_s rp urs)
                             (\ x ->
                               Sum_Type.Inl
                                 (Term_Rewriting.showsl_lit
                                    "problem when orienting usable rules\n" .
                                   x)))
                           (\ _ ->
                             Error_Monad.bind
                               (Error_Monad.catch_error
                                 (Term_Rewriting.rel_impl_ns rp (pns ++ pnwf))
                                 (\ x ->
                                   Sum_Type.Inl
                                     (Term_Rewriting.showsl_lit
"problem when orienting DPs\n" .
                                       x)))
                               (\ _ ->
                                 Error_Monad.catch_error
                                   (Term_Rewriting.rel_impl_s rp ps)
                                   (\ x ->
                                     Sum_Type.Inl
                                       (Term_Rewriting.showsl_lit
  "problem when orienting DPs\n" .
 x))))))));
});
                                    });
                                });
                            }))))
               (\ x ->
                 Sum_Type.Inl
                   (((Term_Rewriting.showsl_lit
                        "could not apply the monotonic reduction pair processor with the following\n" .
                       Term_Rewriting.desc rp) .
                      Term_Rewriting.showsl_literal "\n") .
                     x))
         of {
         Sum_Type.Inl a -> Sum_Type.Inl a;
         Sum_Type.Inr _ ->
           Sum_Type.Inr
             (Dependency_Pair_Problem_Spec.delete_R_Rw i
               (Dependency_Pair_Problem_Spec.delete_P_Pw i dpp premove premove)
               rremove rremove);
       });

}
