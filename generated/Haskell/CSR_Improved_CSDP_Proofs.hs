{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module CSR_Improved_CSDP_Proofs(conservative_csr_dependency_pairs_tt) where {

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
import qualified Check_Monad;
import qualified Error_Monad;
import qualified Dependency_Pair_Problem_Spec;
import qualified Sum_Type;
import qualified Compare;
import qualified Labelings;
import qualified Context_Sensitive_Impl;
import qualified Name;
import qualified HOL;
import qualified CSR_Checker;
import qualified Sharp_Syntax;
import qualified Term_Rewriting;
import qualified Arith;

collapsing_mu_CSDP_list ::
  forall a b.
    (Eq a,
      Eq b) => (a -> a) ->
                 a -> [((a, Arith.Nat), [Arith.Nat])] ->
                        [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
                          [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)];
collapsing_mu_CSDP_list shp u mu r =
  concatMap
    (\ (l, ra) ->
      Arith.map_filter
        (\ x ->
          (if not (Arith.membera (CSR_Checker.mu_vars_term_list mu l) x)
            then Just (Sharp_Syntax.sharp_term shp l,
                        Term_Rewriting.Fun u [Term_Rewriting.Var x])
            else Nothing))
        (Arith.remdups (CSR_Checker.mu_vars_term_list mu ra)))
    r;

conservative_marking_rules_list ::
  forall a.
    (a -> a) ->
      a -> [(a, Arith.Nat)] ->
             [(Term_Rewriting.Term a [Arith.Char],
                Term_Rewriting.Term a [Arith.Char])];
conservative_marking_rules_list shp u d =
  map (\ (f, n) ->
        let {
          xs = map Term_Rewriting.Var (Name.x_1_to_x_n n);
        } in (Term_Rewriting.Fun u [Term_Rewriting.Fun f xs],
               Sharp_Syntax.sharp_term shp (Term_Rewriting.Fun f xs)))
    d;

conservative_projection_rules_list ::
  forall a.
    (Eq a) => a -> [((a, Arith.Nat), [Arith.Nat])] ->
                     [(a, Arith.Nat)] ->
                       [(Term_Rewriting.Term a [Arith.Char],
                          Term_Rewriting.Term a [Arith.Char])];
conservative_projection_rules_list u mu f =
  concatMap
    (\ (fa, n) ->
      let {
        xs = map Term_Rewriting.Var (Name.x_1_to_x_n n);
      } in Arith.map_filter
             (\ x ->
               (if Arith.member x (Context_Sensitive_Impl.mu_of mu (fa, n))
                 then Just (Term_Rewriting.Fun u [Term_Rewriting.Fun fa xs],
                             Term_Rewriting.Fun u [Arith.nth xs x])
                 else Nothing))
             (Arith.upt Arith.zero_nat n))
    f;

conservative_csr_dependency_pairs_tt ::
  forall a b.
    (Compare.Compare_order b, Eq b,
      Term_Rewriting.Showl b) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a
                                   (Labelings.Lab b [Arith.Nat]) [Arith.Char]
                                   () ->
                                   Labelings.Lab b [Arith.Nat] ->
                                     [((Labelings.Lab b [Arith.Nat], Arith.Nat),
[Arith.Nat])] ->
                                       [(Term_Rewriting.Term
   (Labelings.Lab b [Arith.Nat]) [Arith.Char],
  Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
 [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
    Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
   [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
      Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
     Sum_Type.Sum (String -> String) a;
conservative_csr_dependency_pairs_tt j u mu r p s =
  let {
    d = Term_Rewriting.defined_list r;
    f = Term_Rewriting.funas_trs_list r;
  } in (case Error_Monad.bind (Term_Rewriting.check_wf_trs r)
               (\ _ ->
                 Error_Monad.bind
                   (Error_Monad.catch_error
                     (Error_Monad.forallM
                       (\ (fa, n) ->
                         Check_Monad.check
                           (not (Arith.membera d (Labelings.Sharp fa, n)))
                           (Term_Rewriting.showsl_lit
                             "sharping yields a defined symbol"))
                       d)
                     (\ x -> Sum_Type.Inl (snd x)))
                   (\ _ ->
                     Error_Monad.bind
                       (Error_Monad.catch_error
                         (Error_Monad.catch_error
                           (Error_Monad.forallM
                             (\ x ->
                               (if Arith.membera p x then Sum_Type.Inr ()
                                 else Sum_Type.Inl x))
                             (CSR_Checker.mu_CSDP_list Labelings.Sharp r mu d))
                           (\ x -> Sum_Type.Inl (snd x)))
                         (\ _ ->
                           Sum_Type.Inl
                             (Term_Rewriting.showsl_lit
                               "missing replacement-map dependency pair")))
                       (\ _ ->
                         Error_Monad.bind
                           (Error_Monad.catch_error
                             (Error_Monad.catch_error
                               (Error_Monad.forallM
                                 (\ x ->
                                   (if Arith.membera p x then Sum_Type.Inr ()
                                     else Sum_Type.Inl x))
                                 (collapsing_mu_CSDP_list Labelings.Sharp u mu
                                   r))
                               (\ x -> Sum_Type.Inl (snd x)))
                             (\ _ ->
                               Sum_Type.Inl
                                 (Term_Rewriting.showsl_lit
                                   "missing collapsing dependency pair")))
                           (\ _ ->
                             Error_Monad.bind
                               (Error_Monad.catch_error
                                 (Error_Monad.catch_error
                                   (Error_Monad.forallM
                                     (\ x ->
                                       (if Arith.membera s x
 then Sum_Type.Inr () else Sum_Type.Inl x))
                                     r)
                                   (\ x -> Sum_Type.Inl (snd x)))
                                 (\ _ ->
                                   Sum_Type.Inl
                                     (Term_Rewriting.showsl_lit
                                       "missing original weak rule")))
                               (\ _ ->
                                 Error_Monad.bind
                                   (Error_Monad.catch_error
                                     (Error_Monad.catch_error
                                       (Error_Monad.forallM
 (\ x -> (if Arith.membera s x then Sum_Type.Inr () else Sum_Type.Inl x))
 (conservative_projection_rules_list u mu f))
                                       (\ x -> Sum_Type.Inl (snd x)))
                                     (\ _ ->
                                       Sum_Type.Inl
 (Term_Rewriting.showsl_lit "missing unhiding projection rule")))
                                   (\ _ ->
                                     Error_Monad.catch_error
                                       (Error_Monad.catch_error
 (Error_Monad.forallM
   (\ x -> (if Arith.membera s x then Sum_Type.Inr () else Sum_Type.Inl x))
   (conservative_marking_rules_list Labelings.Sharp u d))
 (\ x -> Sum_Type.Inl (snd x)))
                                       (\ _ ->
 Sum_Type.Inl (Term_Rewriting.showsl_lit "missing unhiding marking rule"))))))))
         of {
         Sum_Type.Inl a -> Sum_Type.Inl a;
         Sum_Type.Inr _ ->
           Sum_Type.Inr
             (Dependency_Pair_Problem_Spec.mk j False False p [] [] [] s);
       });

}
