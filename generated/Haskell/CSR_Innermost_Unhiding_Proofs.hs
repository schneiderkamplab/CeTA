{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  CSR_Innermost_Unhiding_Proofs(muterm_unhiding_safe_list,
                                 muterm_exact_unhiding_rules_list)
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
import qualified Sharp_Syntax;
import qualified Compare;
import qualified CSR_Checker_Base;
import qualified Context_Sensitive_Impl;
import qualified Term_Rewriting;
import qualified Arith;

muterm_frozen_roots_list ::
  forall a b.
    (Eq a) => [((a, Arith.Nat), [Arith.Nat])] ->
                Term_Rewriting.Term a b -> [Term_Rewriting.Term a b];
muterm_frozen_roots_list mu (Term_Rewriting.Var x) = [];
muterm_frozen_roots_list mu (Term_Rewriting.Fun f ts) =
  concatMap
    (\ i ->
      (if Arith.member i
            (Context_Sensitive_Impl.mu_of mu (f, Arith.size_list ts))
        then muterm_frozen_roots_list mu (Arith.nth ts i)
        else [Arith.nth ts i]))
    (Arith.upt Arith.zero_nat (Arith.size_list ts));

muterm_safe_frozen_fun_vars_list ::
  forall a b.
    (Eq a,
      Eq b) => [((a, Arith.Nat), [Arith.Nat])] ->
                 [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] -> Bool;
muterm_safe_frozen_fun_vars_list mu r =
  all (\ (l, ra) ->
        all (\ h ->
              (if not (Term_Rewriting.is_Var h)
                then all (Arith.membera
                           (CSR_Checker_Base.mu_vars_term_list mu l))
                       (CSR_Checker_Base.mu_vars_term_list mu h)
                else True))
          (muterm_frozen_roots_list mu ra))
    r;

muterm_safe_migrating_vars_list ::
  forall a b.
    (Eq a,
      Eq b) => [((a, Arith.Nat), [Arith.Nat])] ->
                 [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] -> Bool;
muterm_safe_migrating_vars_list mu r =
  all (\ (l, ra) ->
        all (\ x ->
              Arith.membera (muterm_frozen_roots_list mu l)
                (Term_Rewriting.Var x))
          (filter
            (\ x ->
              not (Arith.membera (CSR_Checker_Base.mu_vars_term_list mu l) x))
            (Arith.remdups (CSR_Checker_Base.mu_vars_term_list mu ra))))
    r;

muterm_safe_frozen_vars_list ::
  forall a b.
    (Eq a,
      Eq b) => [((a, Arith.Nat), [Arith.Nat])] ->
                 [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] -> Bool;
muterm_safe_frozen_vars_list mu r =
  all (\ (l, ra) ->
        all (\ x ->
              Arith.membera (CSR_Checker_Base.mu_vars_term_list mu l) x ||
                Arith.membera (muterm_frozen_roots_list mu l)
                  (Term_Rewriting.Var x))
          (filter
            (\ x ->
              Arith.membera (muterm_frozen_roots_list mu ra)
                (Term_Rewriting.Var x))
            (Arith.remdups (Term_Rewriting.vars_term_list ra))))
    r;

muterm_unhiding_safe_list ::
  forall a b.
    (Eq a,
      Eq b) => [((a, Arith.Nat), [Arith.Nat])] ->
                 [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] -> Bool;
muterm_unhiding_safe_list mu r =
  muterm_safe_frozen_fun_vars_list mu r &&
    muterm_safe_migrating_vars_list mu r &&
      muterm_safe_frozen_vars_list mu r &&
        all (\ (_, ra) ->
              all (\ h ->
                    (if not (Term_Rewriting.is_Var h)
                      then null (muterm_frozen_roots_list mu h) else True))
                (muterm_frozen_roots_list mu ra))
          r;

muterm_active_defined_calls_list ::
  forall a b.
    (Eq a) => [((a, Arith.Nat), [Arith.Nat])] ->
                [(a, Arith.Nat)] ->
                  Term_Rewriting.Term a b -> [Term_Rewriting.Term a b];
muterm_active_defined_calls_list mu d (Term_Rewriting.Var x) = [];
muterm_active_defined_calls_list mu d (Term_Rewriting.Fun f ts) =
  (if Arith.membera d (f, Arith.size_list ts) then [Term_Rewriting.Fun f ts]
    else []) ++
    concat
      (Arith.map_filter
        (\ x ->
          (if Arith.member x
                (Context_Sensitive_Impl.mu_of mu (f, Arith.size_list ts))
            then Just (muterm_active_defined_calls_list mu d (Arith.nth ts x))
            else Nothing))
        (Arith.upt Arith.zero_nat (Arith.size_list ts)));

muterm_exact_unhiding_rules_list ::
  forall a b.
    (Compare.Compare_order a, Eq a, Term_Rewriting.Showl a,
      Eq b) => (a -> a) ->
                 [((a, Arith.Nat), [Arith.Nat])] ->
                   [(a, Arith.Nat)] ->
                     [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
                       [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)];
muterm_exact_unhiding_rules_list shp mu d r =
  Arith.remdups
    (concatMap
      (\ (_, ra) ->
        concatMap
          (\ h ->
            map (\ t -> (h, Sharp_Syntax.sharp_term shp t))
              (muterm_active_defined_calls_list mu d h))
          (muterm_frozen_roots_list mu ra))
      r);

}
