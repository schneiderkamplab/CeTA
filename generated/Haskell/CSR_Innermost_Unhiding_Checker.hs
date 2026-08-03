{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module CSR_Innermost_Unhiding_Checker(direct_innermost_csr_dependency_pairs_tt)
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
import qualified Check_Monad;
import qualified Error_Monad;
import qualified Dependency_Pair_Problem_Spec;
import qualified Sum_Type;
import qualified Labelings;
import qualified CSR_Improved_CSDP_Proofs;
import qualified Name;
import qualified HOL;
import qualified CSR_Checker_Base;
import qualified Sharp_Syntax;
import qualified Compare;
import qualified Term_Rewriting;
import qualified Arith;

direct_hidden_mu_CSDP_list ::
  forall a b.
    (Arith.Ceq a, Arith.Ccompare a, Compare.Compare_order a, Eq a,
      Arith.Set_impl a,
      Term_Rewriting.Showl a) => (a -> a) ->
                                   [((a, Arith.Nat), [Arith.Nat])] ->
                                     [(a, Arith.Nat)] ->
                                       [(Term_Rewriting.Term a b,
  Term_Rewriting.Term a b)] ->
 [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)];
direct_hidden_mu_CSDP_list shp mu d r =
  concatMap
    (\ (_, ra) ->
      Arith.map_filter
        (\ x ->
          (if not (Arith.membera (CSR_Checker_Base.mu_fun_poss_list mu ra) x) &&
                Arith.member (Term_Rewriting.root (Term_Rewriting.subt_at ra x))
                  (Arith.image Just (Arith.set d))
            then Just (Term_Rewriting.subt_at ra x,
                        Sharp_Syntax.sharp_term shp
                          (Term_Rewriting.subt_at ra x))
            else Nothing))
        (Term_Rewriting.fun_poss_list ra))
    r;

direct_projection_rules_list ::
  forall a b.
    (Arith.Ceq a, Arith.Ccompare a, Eq a, Arith.Set_impl a,
      Eq b) => [((a, Arith.Nat), [Arith.Nat])] ->
                 [(a, Arith.Nat)] ->
                   [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
                     [(Term_Rewriting.Term a [Arith.Char],
                        Term_Rewriting.Term a [Arith.Char])];
direct_projection_rules_list mu d r =
  concatMap
    (\ (f, n) ->
      let {
        xs = map Term_Rewriting.Var (Name.x_1_to_x_n n);
      } in Arith.map_filter
             (\ x ->
               (if CSR_Improved_CSDP_Proofs.hides_position_list mu d r f n x
                 then Just (Term_Rewriting.Fun f xs, Arith.nth xs x)
                 else Nothing))
             (Arith.upt Arith.zero_nat n))
    (Arith.remdups (Term_Rewriting.funas_trs_list r));

direct_collapsing_mu_CSDP_list ::
  forall a b.
    (Eq a,
      Eq b) => (a -> a) ->
                 [((a, Arith.Nat), [Arith.Nat])] ->
                   [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
                     [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)];
direct_collapsing_mu_CSDP_list shp mu r =
  concatMap
    (\ (l, ra) ->
      Arith.map_filter
        (\ x ->
          (if not (Arith.membera (CSR_Checker_Base.mu_vars_term_list mu l) x)
            then Just (Sharp_Syntax.sharp_term shp l, Term_Rewriting.Var x)
            else Nothing))
        (Arith.remdups (CSR_Checker_Base.mu_vars_term_list mu ra)))
    r;

direct_innermost_csr_dependency_pairs_tt ::
  forall a b.
    (Compare.Compare_order b, Eq b,
      Term_Rewriting.Showl b) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a
                                   (Labelings.Lab b [Arith.Nat]) [Arith.Char]
                                   () ->
                                   [((Labelings.Lab b [Arith.Nat], Arith.Nat),
                                      [Arith.Nat])] ->
                                     [(Term_Rewriting.Term
 (Labelings.Lab b [Arith.Nat]) [Arith.Char],
Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
                                       [(Term_Rewriting.Term
   (Labelings.Lab b [Arith.Nat]) [Arith.Char],
  Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
 [(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
    Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
   Sum_Type.Sum (String -> String) a;
direct_innermost_csr_dependency_pairs_tt j mu r p s =
  let {
    d = Term_Rewriting.defined_list r;
    s0 = r ++ direct_projection_rules_list mu d r;
  } in (case Error_Monad.bind (Term_Rewriting.check_wf_trs r)
               (\ _ ->
                 Error_Monad.bind
                   (Error_Monad.catch_error
                     (Error_Monad.forallM
                       (\ (f, n) ->
                         Check_Monad.check
                           (not (Arith.membera d (Labelings.Sharp f, n)))
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
                             (CSR_Checker_Base.mu_CSDP_list Labelings.Sharp r mu
                               d))
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
                                 (direct_collapsing_mu_CSDP_list Labelings.Sharp
                                   mu r))
                               (\ x -> Sum_Type.Inl (snd x)))
                             (\ _ ->
                               Sum_Type.Inl
                                 (Term_Rewriting.showsl_lit
                                   "missing direct collapsing dependency pair")))
                           (\ _ ->
                             Error_Monad.bind
                               (Error_Monad.catch_error
                                 (Error_Monad.catch_error
                                   (Error_Monad.forallM
                                     (\ x ->
                                       (if Arith.membera p x
 then Sum_Type.Inr () else Sum_Type.Inl x))
                                     (direct_hidden_mu_CSDP_list Labelings.Sharp
                                       mu d r))
                                   (\ x -> Sum_Type.Inl (snd x)))
                                 (\ _ ->
                                   Sum_Type.Inl
                                     (Term_Rewriting.showsl_lit
                                       "missing direct hidden-term dependency pair")))
                               (\ _ ->
                                 Error_Monad.bind
                                   (Error_Monad.catch_error
                                     (Error_Monad.catch_error
                                       (Error_Monad.forallM
 (\ x -> (if Arith.membera s x then Sum_Type.Inr () else Sum_Type.Inl x)) r)
                                       (\ x -> Sum_Type.Inl (snd x)))
                                     (\ _ ->
                                       Sum_Type.Inl
 (Term_Rewriting.showsl_lit "missing original weak rule")))
                                   (\ _ ->
                                     Error_Monad.catch_error
                                       (Error_Monad.catch_error
 (Error_Monad.forallM
   (\ x -> (if Arith.membera s x then Sum_Type.Inr () else Sum_Type.Inl x))
   (direct_projection_rules_list mu d r))
 (\ x -> Sum_Type.Inl (snd x)))
                                       (\ _ ->
 Sum_Type.Inl
   (Term_Rewriting.showsl_lit "missing direct unhiding projection rule"))))))))
         of {
         Sum_Type.Inl a -> Sum_Type.Inl a;
         Sum_Type.Inr _ ->
           Sum_Type.Inr
             (Dependency_Pair_Problem_Spec.mk j False False p [] [] [] s0);
       });

}
