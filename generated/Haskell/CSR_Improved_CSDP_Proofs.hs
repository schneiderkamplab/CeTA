{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  CSR_Improved_CSDP_Proofs(improved_csr_dependency_pairs_tt,
                            conservative_csr_dependency_pairs_tt)
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
import qualified Compare;
import qualified Labelings;
import qualified Name;
import qualified HOL;
import qualified Context_Sensitive_Impl;
import qualified CSR_Checker_Base;
import qualified Sharp_Syntax;
import qualified Term_Rewriting;
import qualified Arith;

hidden_mu_CSDP_list ::
  forall a b.
    (Arith.Ceq a, Arith.Ccompare a, Eq a,
      Arith.Set_impl a) => (a -> a) ->
                             a -> [((a, Arith.Nat), [Arith.Nat])] ->
                                    [(a, Arith.Nat)] ->
                                      [(Term_Rewriting.Term a b,
 Term_Rewriting.Term a b)] ->
[(Term_Rewriting.Term a b, Term_Rewriting.Term a b)];
hidden_mu_CSDP_list shp u mu d r =
  concatMap
    (\ (_, ra) ->
      Arith.map_filter
        (\ x ->
          (if not (Arith.membera (CSR_Checker_Base.mu_fun_poss_list mu ra) x) &&
                Arith.member (Term_Rewriting.root (Term_Rewriting.subt_at ra x))
                  (Arith.image Just (Arith.set d))
            then Just (Term_Rewriting.Fun u [Term_Rewriting.subt_at ra x],
                        Sharp_Syntax.sharp_term shp
                          (Term_Rewriting.subt_at ra x))
            else Nothing))
        (Term_Rewriting.fun_poss_list ra))
    r;

hides_position_list ::
  forall a b.
    (Arith.Ceq a, Arith.Ccompare a, Eq a,
      Arith.Set_impl a) => [((a, Arith.Nat), [Arith.Nat])] ->
                             [(a, Arith.Nat)] ->
                               [(Term_Rewriting.Term a b,
                                  Term_Rewriting.Term a b)] ->
                                 a -> Arith.Nat -> Arith.Nat -> Bool;
hides_position_list mu d r f n i =
  any (\ (_, ra) ->
        any (\ p ->
              not (Arith.membera (CSR_Checker_Base.mu_fun_poss_list mu ra) p) &&
                (case Term_Rewriting.subt_at ra p of {
                  Term_Rewriting.Var _ -> False;
                  Term_Rewriting.Fun g ts ->
                    g == f &&
                      Arith.equal_nat (Arith.size_list ts) n &&
                        Arith.less_nat i (Arith.size_list ts) &&
                          Arith.member i
                            (Context_Sensitive_Impl.mu_of mu
                              (g, Arith.size_list ts)) &&
                            any (\ q ->
                                  Term_Rewriting.is_Var
                                    (Term_Rewriting.subt_at (Arith.nth ts i)
                                      q) ||
                                    Arith.member
                                      (Term_Rewriting.root
(Term_Rewriting.subt_at (Arith.nth ts i) q))
                                      (Arith.image Just (Arith.set d)))
                              (CSR_Checker_Base.mu_poss_list mu
                                (Arith.nth ts i));
                }))
          (Term_Rewriting.fun_poss_list ra))
    r;

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
          (if not (Arith.membera (CSR_Checker_Base.mu_vars_term_list mu l) x)
            then Just (Sharp_Syntax.sharp_term shp l,
                        Term_Rewriting.Fun u [Term_Rewriting.Var x])
            else Nothing))
        (Arith.remdups (CSR_Checker_Base.mu_vars_term_list mu ra)))
    r;

improved_projection_pairs_list ::
  forall a b.
    (Arith.Ceq a, Arith.Ccompare a, Eq a,
      Arith.Set_impl a) => a -> [((a, Arith.Nat), [Arith.Nat])] ->
                                  [(a, Arith.Nat)] ->
                                    [(Term_Rewriting.Term a b,
                                       Term_Rewriting.Term a b)] ->
                                      [(Term_Rewriting.Term a [Arith.Char],
 Term_Rewriting.Term a [Arith.Char])];
improved_projection_pairs_list u mu d r =
  concatMap
    (\ (f, n) ->
      let {
        xs = map Term_Rewriting.Var (Name.x_1_to_x_n n);
      } in Arith.map_filter
             (\ x ->
               (if hides_position_list mu d r f n x
                 then Just (Term_Rewriting.Fun u [Term_Rewriting.Fun f xs],
                             Term_Rewriting.Fun u [Arith.nth xs x])
                 else Nothing))
             (Arith.upt Arith.zero_nat n))
    (Arith.remdups (Term_Rewriting.funas_trs_list r));

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

improved_csr_dependency_pairs_tt ::
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
   Sum_Type.Sum (String -> String) a;
improved_csr_dependency_pairs_tt j u mu r p =
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
                         (Error_Monad.forallM
                           (\ (fa, _) ->
                             Check_Monad.check
                               (not (CSR_Checker_Base.is_sharp_lab fa))
                               (Term_Rewriting.showsl_lit
                                 "source CSR defines a sharp symbol"))
                           d)
                         (\ x -> Sum_Type.Inl (snd x)))
                       (\ _ ->
                         Error_Monad.bind
                           (Error_Monad.catch_error
                             (Error_Monad.forallM
                               (\ (fa, _) ->
                                 Check_Monad.check
                                   (not (Labelings.equal_lab fa u))
                                   (Term_Rewriting.showsl_lit
                                     "unhiding symbol is not fresh"))
                               f)
                             (\ x -> Sum_Type.Inl (snd x)))
                           (\ _ ->
                             Error_Monad.bind
                               (Check_Monad.check
                                 (not (CSR_Checker_Base.is_sharp_lab u))
                                 (Term_Rewriting.showsl_lit
                                   "unhiding symbol must not be sharp"))
                               (\ _ ->
                                 Error_Monad.bind
                                   (Error_Monad.catch_error
                                     (Error_Monad.catch_error
                                       (Error_Monad.forallM
 (\ x -> (if Arith.membera p x then Sum_Type.Inr () else Sum_Type.Inl x))
 (CSR_Checker_Base.mu_CSDP_list Labelings.Sharp r mu d))
                                       (\ x -> Sum_Type.Inl (snd x)))
                                     (\ _ ->
                                       Sum_Type.Inl
 (Term_Rewriting.showsl_lit "missing replacement-map dependency pair")))
                                   (\ _ ->
                                     Error_Monad.bind
                                       (Error_Monad.catch_error
 (Error_Monad.catch_error
   (Error_Monad.forallM
     (\ x -> (if Arith.membera p x then Sum_Type.Inr () else Sum_Type.Inl x))
     (collapsing_mu_CSDP_list Labelings.Sharp u mu r))
   (\ x -> Sum_Type.Inl (snd x)))
 (\ _ ->
   Sum_Type.Inl
     (Term_Rewriting.showsl_lit "missing collapsing dependency pair")))
                                       (\ _ ->
 Error_Monad.bind
   (Error_Monad.catch_error
     (Error_Monad.catch_error
       (Error_Monad.forallM
         (\ x ->
           (if Arith.membera p x then Sum_Type.Inr () else Sum_Type.Inl x))
         (hidden_mu_CSDP_list Labelings.Sharp u mu d r))
       (\ x -> Sum_Type.Inl (snd x)))
     (\ _ ->
       Sum_Type.Inl
         (Term_Rewriting.showsl_lit "missing hidden-term dependency pair")))
   (\ _ ->
     Error_Monad.catch_error
       (Error_Monad.catch_error
         (Error_Monad.forallM
           (\ x ->
             (if Arith.membera p x then Sum_Type.Inr () else Sum_Type.Inl x))
           (improved_projection_pairs_list u mu d r))
         (\ x -> Sum_Type.Inl (snd x)))
       (\ _ ->
         Sum_Type.Inl
           (Term_Rewriting.showsl_lit
             "missing unhiding projection pair"))))))))))
         of {
         Sum_Type.Inl a -> Sum_Type.Inl a;
         Sum_Type.Inr _ ->
           Sum_Type.Inr
             (Dependency_Pair_Problem_Spec.mk j False False p [] [] [] r);
       });

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
                                       (if Arith.membera p x
 then Sum_Type.Inr () else Sum_Type.Inl x))
                                     (hidden_mu_CSDP_list Labelings.Sharp u mu d
                                       r))
                                   (\ x -> Sum_Type.Inl (snd x)))
                                 (\ _ ->
                                   Sum_Type.Inl
                                     (Term_Rewriting.showsl_lit
                                       "missing hidden-term dependency pair")))
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
                                     Error_Monad.bind
                                       (Error_Monad.catch_error
 (Error_Monad.catch_error
   (Error_Monad.forallM
     (\ x -> (if Arith.membera s x then Sum_Type.Inr () else Sum_Type.Inl x))
     (conservative_projection_rules_list u mu f))
   (\ x -> Sum_Type.Inl (snd x)))
 (\ _ ->
   Sum_Type.Inl (Term_Rewriting.showsl_lit "missing unhiding projection rule")))
                                       (\ _ ->
 Error_Monad.catch_error
   (Error_Monad.catch_error
     (Error_Monad.forallM
       (\ x -> (if Arith.membera s x then Sum_Type.Inr () else Sum_Type.Inl x))
       (conservative_marking_rules_list Labelings.Sharp u d))
     (\ x -> Sum_Type.Inl (snd x)))
   (\ _ ->
     Sum_Type.Inl
       (Term_Rewriting.showsl_lit "missing unhiding marking rule")))))))))
         of {
         Sum_Type.Inl a -> Sum_Type.Inl a;
         Sum_Type.Inr _ ->
           Sum_Type.Inr
             (Dependency_Pair_Problem_Spec.mk j False False p [] [] [] s);
       });

}
