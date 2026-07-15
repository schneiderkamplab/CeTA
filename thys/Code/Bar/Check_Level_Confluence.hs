{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Check_Level_Confluence(Ao_infeasibility_proof(..), check_level_confluence,
                          check_level_confluence_modulo_infeasibility)
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
import qualified Fresh;
import qualified Lists_are_Infinite;
import qualified Conditional_Rewriting_Impl;
import qualified Equational_Reasoning_Impl;
import qualified Labelings_Impl;
import qualified Trs_Impl_More;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified Dependency_Pair_Problem_Spec;
import qualified Termination_Problem_Spec;
import qualified Sum_Type;
import qualified Compare;
import qualified Shows_Literal;
import qualified Countable;
import qualified HOL;
import qualified Mapping;
import qualified Arith;
import qualified Check_Nonreachability;
import qualified Check_Infeasibility;
import qualified Labelings;
import qualified Term_Rewriting;

data Ao_infeasibility_proof a b c d =
  AO_Infeasibility_Proof (Check_Infeasibility.Infeasibility_proof a b c d)
  | AO_Lhss_Equal (Term_Rewriting.Term (Labelings.Lab a d) b)
      (Term_Rewriting.Term (Labelings.Lab a d) b)
      (Term_Rewriting.Term (Labelings.Lab a d) b)
      (Check_Nonreachability.Nonjoinability_proof a b c d);

check_ao_infeasiblea ::
  forall a b c d e.
    (Compare.Compare_order c, Countable.Countable c, HOL.Default c, Eq c,
      Shows_Literal.Showl c) => a -> (String -> String) ->
                                       Termination_Problem_Spec.Tp_ops_ext b
 (Labelings.Lab c [Arith.Nat]) [Arith.Char] () ->
 Dependency_Pair_Problem_Spec.Dpp_ops_ext d (Labelings.Lab c [Arith.Nat])
   [Arith.Char] () ->
   [((Term_Rewriting.Term (Labelings.Lab c [Arith.Nat]) [Arith.Char],
       Term_Rewriting.Term (Labelings.Lab c [Arith.Nat]) [Arith.Char]),
      [(Term_Rewriting.Term (Labelings.Lab c [Arith.Nat]) [Arith.Char],
         Term_Rewriting.Term (Labelings.Lab c [Arith.Nat]) [Arith.Char])])] ->
     [(Term_Rewriting.Term (Labelings.Lab c [Arith.Nat]) [Arith.Char],
        Term_Rewriting.Term (Labelings.Lab c [Arith.Nat]) [Arith.Char])] ->
       [(Term_Rewriting.Term (Labelings.Lab c [Arith.Nat]) [Arith.Char],
          Term_Rewriting.Term (Labelings.Lab c [Arith.Nat]) [Arith.Char])] ->
         Ao_infeasibility_proof c [Arith.Char] e [Arith.Nat] ->
           Sum_Type.Sum (String -> String) ();
check_ao_infeasiblea a ia i j r cs_1 cs_2 (AO_Infeasibility_Proof p) =
  Check_Infeasibility.check_infeasible a ia i j r (cs_1 ++ cs_2) p;
check_ao_infeasiblea a ia i j r cs_1 cs_2 (AO_Lhss_Equal s t u p) =
  Error_Monad.bind
    (Check_Monad.check (Arith.membera cs_1 (s, t))
      ((Equational_Reasoning_Impl.showsl_eq (s, t) .
         Shows_Literal.showsl_lit " is not an equation in ") .
        Conditional_Rewriting_Impl.showsl_conditions cs_1))
    (\ _ ->
      Error_Monad.bind
        (Check_Monad.check (Arith.membera cs_2 (s, u))
          ((Equational_Reasoning_Impl.showsl_eq (s, u) .
             Shows_Literal.showsl_lit " is not an equation in ") .
            Conditional_Rewriting_Impl.showsl_conditions cs_2))
        (\ _ ->
          Check_Nonreachability.check_nonjoinable a ia i j (map fst r) t u p));

check_ao_infeasible ::
  forall a b c d e.
    (Compare.Compare_order c, Countable.Countable c, HOL.Default c, Eq c,
      Shows_Literal.Showl c) => a -> (String -> String) ->
                                       Termination_Problem_Spec.Tp_ops_ext b
 (Labelings.Lab c [Arith.Nat]) [Arith.Char] () ->
 Dependency_Pair_Problem_Spec.Dpp_ops_ext d (Labelings.Lab c [Arith.Nat])
   [Arith.Char] () ->
   [([(Term_Rewriting.Term (Labelings.Lab c [Arith.Nat]) [Arith.Char],
        Term_Rewriting.Term (Labelings.Lab c [Arith.Nat]) [Arith.Char])],
      ([(Term_Rewriting.Term (Labelings.Lab c [Arith.Nat]) [Arith.Char],
          Term_Rewriting.Term (Labelings.Lab c [Arith.Nat]) [Arith.Char])],
        Ao_infeasibility_proof c [Arith.Char] e [Arith.Nat]))] ->
     [((Term_Rewriting.Term (Labelings.Lab c [Arith.Nat]) [Arith.Char],
         Term_Rewriting.Term (Labelings.Lab c [Arith.Nat]) [Arith.Char]),
        [(Term_Rewriting.Term (Labelings.Lab c [Arith.Nat]) [Arith.Char],
           Term_Rewriting.Term (Labelings.Lab c [Arith.Nat]) [Arith.Char])])] ->
       [(Term_Rewriting.Term (Labelings.Lab c [Arith.Nat]) [Arith.Char],
          Term_Rewriting.Term (Labelings.Lab c [Arith.Nat]) [Arith.Char])] ->
         [(Term_Rewriting.Term (Labelings.Lab c [Arith.Nat]) [Arith.Char],
            Term_Rewriting.Term (Labelings.Lab c [Arith.Nat]) [Arith.Char])] ->
           Sum_Type.Sum (String -> String) ();
check_ao_infeasible a ia i j css r cs_1 cs_2 =
  Error_Monad.catch_error
    (Error_Monad.existsM
      (\ (cs_1a, (cs_2a, p)) ->
        let {
          cs = cs_1 ++ cs_2;
          csa = cs_1a ++ cs_2a;
        } in Error_Monad.bind
               (Check_Monad.check
                 (Arith.equal_nat (Arith.size_list cs_1a)
                    (Arith.size_list cs_1) &&
                   Arith.equal_nat (Arith.size_list cs_2a)
                     (Arith.size_list cs_2))
                 (Shows_Literal.showsl_lit "lengths differ"))
               (\ _ ->
                 Error_Monad.bind
                   (Check_Monad.check
                     (not (Arith.is_none (Trs_Impl_More.match_rules csa cs)) &&
                       not (Arith.is_none (Trs_Impl_More.match_rules cs csa)))
                     id)
                   (\ _ -> check_ao_infeasiblea a ia i j r cs_1a cs_2a p)))
      css)
    (\ x ->
      Sum_Type.Inl
        (Shows_Literal.showsl_sep id (Shows_Literal.showsl_literal "\n") x));

check_overlap ::
  forall a b.
    (Arith.Ccompare a, Fresh.Infinite a, Eq a, Mapping.Mapping_impl a,
      Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => (a -> a) ->
                                  (a -> a) ->
                                    ([((Term_Rewriting.Term b a,
 Term_Rewriting.Term b a),
[(Term_Rewriting.Term b a, Term_Rewriting.Term b a)])] ->
                                      [(Term_Rewriting.Term b a,
 Term_Rewriting.Term b a)] ->
[(Term_Rewriting.Term b a, Term_Rewriting.Term b a)] ->
  Sum_Type.Sum (String -> String) ()) ->
                                      [((Term_Rewriting.Term b a,
  Term_Rewriting.Term b a),
 [(Term_Rewriting.Term b a, Term_Rewriting.Term b a)])] ->
((Term_Rewriting.Term b a, Term_Rewriting.Term b a),
  [(Term_Rewriting.Term b a, Term_Rewriting.Term b a)]) ->
  ((Term_Rewriting.Term b a, Term_Rewriting.Term b a),
    [(Term_Rewriting.Term b a, Term_Rewriting.Term b a)]) ->
    [Arith.Nat] -> Sum_Type.Sum (String -> String) ();
check_overlap xvar yvar check_infeasible r rho_1 rho_2 p =
  Error_Monad.catch_error
    (case Term_Rewriting.mgu_var_disjoint_generic xvar yvar
            (Term_Rewriting.subt_at (fst (fst rho_1)) p) (fst (fst rho_2))
      of {
      Nothing -> Sum_Type.Inr ();
      Just (sigma_1, sigma_2) ->
        Error_Monad.catch_error
          (Error_Monad.choice
            [Check_Monad.check
               (null p &&
                 Term_Rewriting.equal_term
                   (Term_Rewriting.eval_term Term_Rewriting.Fun
                     (snd (fst rho_1)) sigma_1)
                   (Term_Rewriting.eval_term Term_Rewriting.Fun
                     (snd (fst rho_2)) sigma_2))
               (Shows_Literal.showsl_lit "is not a trivial root-overlap"),
              Check_Monad.check
                (null p &&
                  not (Arith.is_none
                        (Conditional_Rewriting_Impl.match_crule rho_1 rho_2)) &&
                    not (Arith.is_none
                          (Conditional_Rewriting_Impl.match_crule rho_2 rho_1)))
                (Shows_Literal.showsl_lit
                  "is not a root-overlap of variants of the same rule"),
              Error_Monad.catch_error
                (check_infeasible r
                   (Term_Rewriting.subst_list sigma_1 (snd rho_1))
                  (Term_Rewriting.subst_list sigma_2 (snd rho_2)))
                (\ x ->
                  Sum_Type.Inl
                    (Shows_Literal.showsl_lit
                       "could not be shown to be infeasible\n" .
                      x))])
          (\ x ->
            Sum_Type.Inl
              (Shows_Literal.showsl_sep id (Shows_Literal.showsl_literal "\n")
                x));
    })
    (\ x ->
      Sum_Type.Inl
        (((Shows_Literal.showsl_lit "the " .
            Conditional_Rewriting_Impl.showsl_coverlap rho_1 rho_2 p) .
           Shows_Literal.showsl_literal "\n") .
          x));

check_almost_orthogonal ::
  forall a.
    (Eq a,
      Shows_Literal.Showl a) => [((Term_Rewriting.Term a [Arith.Char],
                                    Term_Rewriting.Term a [Arith.Char]),
                                   [(Term_Rewriting.Term a [Arith.Char],
                                      Term_Rewriting.Term a [Arith.Char])])] ->
                                  Sum_Type.Sum (String -> String) ();
check_almost_orthogonal r =
  Error_Monad.bind (Term_Rewriting.check_left_linear_trs (map fst r))
    (\ _ ->
      Error_Monad.catch_error
        (Error_Monad.forallM
          (\ rho_1 ->
            let {
              l_1 = fst (fst rho_1);
            } in Error_Monad.catch_error
                   (Error_Monad.forallM
                     (\ rho_2 ->
                       Error_Monad.catch_error
                         (Error_Monad.forallM
                           (check_overlap (\ a -> Arith.char_0x78 : a)
                             (\ a -> Arith.char_0x79 : a)
                             (\ _ _ _ ->
                               Sum_Type.Inl
                                 (Shows_Literal.showsl_lit
                                   "infeasibility check not supported"))
                             r rho_1 rho_2)
                           (Term_Rewriting.fun_poss_list l_1))
                         (\ x -> Sum_Type.Inl (snd x)))
                     r)
                   (\ x -> Sum_Type.Inl (snd x)))
          r)
        (\ x -> Sum_Type.Inl (snd x)));

check_level_confluence ::
  forall a.
    (Arith.Finite_UNIV a, Arith.Cenum a, Arith.Ceq a, Arith.Cproper_interval a,
      Compare.Compare_order a, Eq a, Arith.Set_impl a,
      Shows_Literal.Showl a) => [((Term_Rewriting.Term a [Arith.Char],
                                    Term_Rewriting.Term a [Arith.Char]),
                                   [(Term_Rewriting.Term a [Arith.Char],
                                      Term_Rewriting.Term a [Arith.Char])])] ->
                                  Sum_Type.Sum (String -> String) ();
check_level_confluence r =
  Error_Monad.bind (Term_Rewriting.check_varcond_no_Var_lhs (map fst r))
    (\ _ ->
      Error_Monad.bind (Conditional_Rewriting_Impl.check_type3 r)
        (\ _ ->
          Error_Monad.bind
            (Conditional_Rewriting_Impl.check_extended_properly_oriented r)
            (\ _ ->
              Error_Monad.bind (Conditional_Rewriting_Impl.check_right_stable r)
                (\ _ -> check_almost_orthogonal r))));

check_ao ::
  forall a b.
    (Arith.Ceq a, Arith.Ccompare a, Fresh.Infinite a, Eq a,
      Mapping.Mapping_impl a, Arith.Set_impl a, Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => (a -> a) ->
                                  (a -> a) ->
                                    ([((Term_Rewriting.Term b a,
 Term_Rewriting.Term b a),
[(Term_Rewriting.Term b a, Term_Rewriting.Term b a)])] ->
                                      [(Term_Rewriting.Term b a,
 Term_Rewriting.Term b a)] ->
[(Term_Rewriting.Term b a, Term_Rewriting.Term b a)] ->
  Sum_Type.Sum (String -> String) ()) ->
                                      [((Term_Rewriting.Term b a,
  Term_Rewriting.Term b a),
 [(Term_Rewriting.Term b a, Term_Rewriting.Term b a)])] ->
Sum_Type.Sum (String -> String) ();
check_ao xvar yvar check_infeasible r =
  Error_Monad.bind (Term_Rewriting.check_left_linear_trs (map fst r))
    (\ _ ->
      Error_Monad.catch_error
        (Error_Monad.forallM
          (\ rho_1 ->
            let {
              l_1 = fst (fst rho_1);
            } in Error_Monad.catch_error
                   (Error_Monad.forallM
                     (\ rho_2 ->
                       Error_Monad.catch_error
                         (Error_Monad.forallM
                           (check_overlap xvar yvar check_infeasible r rho_1
                             rho_2)
                           (Term_Rewriting.fun_poss_list l_1))
                         (\ x -> Sum_Type.Inl (snd x)))
                     r)
                   (\ x -> Sum_Type.Inl (snd x)))
          r)
        (\ x -> Sum_Type.Inl (snd x)));

check_level_confluence_modulo_infeasibility ::
  forall a b c d e.
    (Compare.Compare_order c, Countable.Countable c, HOL.Default c, Eq c,
      Shows_Literal.Showl c) => a -> (String -> String) ->
                                       Termination_Problem_Spec.Tp_ops_ext b
 (Labelings.Lab c [Arith.Nat]) [Arith.Char] () ->
 Dependency_Pair_Problem_Spec.Dpp_ops_ext d (Labelings.Lab c [Arith.Nat])
   [Arith.Char] () ->
   [([(Term_Rewriting.Term (Labelings.Lab c [Arith.Nat]) [Arith.Char],
        Term_Rewriting.Term (Labelings.Lab c [Arith.Nat]) [Arith.Char])],
      ([(Term_Rewriting.Term (Labelings.Lab c [Arith.Nat]) [Arith.Char],
          Term_Rewriting.Term (Labelings.Lab c [Arith.Nat]) [Arith.Char])],
        Ao_infeasibility_proof c [Arith.Char] e [Arith.Nat]))] ->
     [((Term_Rewriting.Term (Labelings.Lab c [Arith.Nat]) [Arith.Char],
         Term_Rewriting.Term (Labelings.Lab c [Arith.Nat]) [Arith.Char]),
        [(Term_Rewriting.Term (Labelings.Lab c [Arith.Nat]) [Arith.Char],
           Term_Rewriting.Term (Labelings.Lab c [Arith.Nat]) [Arith.Char])])] ->
       Sum_Type.Sum (String -> String) ();
check_level_confluence_modulo_infeasibility a ia i j css r =
  Error_Monad.bind (Term_Rewriting.check_varcond_no_Var_lhs (map fst r))
    (\ _ ->
      Error_Monad.bind (Conditional_Rewriting_Impl.check_type3 r)
        (\ _ ->
          Error_Monad.bind
            (Conditional_Rewriting_Impl.check_extended_properly_oriented r)
            (\ _ ->
              Error_Monad.bind (Conditional_Rewriting_Impl.check_right_stable r)
                (\ _ ->
                  check_ao (\ aa -> Arith.char_0x78 : aa)
                    (\ aa -> Arith.char_0x79 : aa)
                    (check_ao_infeasible a ia i j css) r))));

}
