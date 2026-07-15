{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Check_Infeasibility(Feasibility_proof(..), Inf_transformation(..),
                       Infeasibility_proof(..), check_infeasible,
                       check_infeasible_rules, check_feasibility_proof)
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
import qualified Mapping;
import qualified Fresh;
import qualified Left_Inline_Conditions_Impl;
import qualified Inline_Conditions_Impl;
import qualified Ifrit_Impl;
import qualified Equational_Reasoning_Impl;
import qualified Unraveling_Impl;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified Dependency_Pair_Problem_Spec;
import qualified Termination_Problem_Spec;
import qualified Sum_Type;
import qualified Countable;
import qualified HOL;
import qualified Compare;
import qualified Labelings_Impl;
import qualified Shows_Literal;
import qualified Arith;
import qualified Check_Nonreachability;
import qualified Labelings;
import qualified Conditional_Rewriting_Impl;
import qualified Term_Rewriting;

data Feasibility_proof a b =
  Feasible_Witness [(b, Term_Rewriting.Term a b)]
    [[Conditional_Rewriting_Impl.Cstep_proof a b]];

data Inf_transformation a b =
  Ifrit_Rules_Inf
    [((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
       [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)])]
  | Left_Inline_Conditions_Inf
      [((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
         [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)])]
      [(((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
          [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]),
         [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)])]
  | Right_Inline_Conditions_Inf
      [((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
         [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)])]
      [(((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
          [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]),
         [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)])];

data Infeasibility_proof a b c d =
  Infeasible_Compound_Conditions (Labelings.Lab a d)
    (Check_Nonreachability.Nonreachability_proof a b c d)
  | Infeasible_Equation (Term_Rewriting.Term (Labelings.Lab a d) b)
      (Term_Rewriting.Term (Labelings.Lab a d) b)
      (Check_Nonreachability.Nonreachability_proof a b c d)
  | Infeasible_Subset
      [(Term_Rewriting.Term (Labelings.Lab a d) b,
         Term_Rewriting.Term (Labelings.Lab a d) b)]
      (Infeasibility_proof a b c d)
  | Infeasible_Rhss_Equal (Term_Rewriting.Term (Labelings.Lab a d) b)
      (Term_Rewriting.Term (Labelings.Lab a d) b)
      (Term_Rewriting.Term (Labelings.Lab a d) b)
      (Check_Nonreachability.Nonjoinability_proof a b c d)
  | Infeasible_Trans (Term_Rewriting.Term (Labelings.Lab a d) b)
      (Term_Rewriting.Term (Labelings.Lab a d) b)
      (Term_Rewriting.Term (Labelings.Lab a d) b)
      (Check_Nonreachability.Nonreachability_proof a b c d)
  | Infeasible_Transform (Inf_transformation (Labelings.Lab a d) b)
      (Infeasibility_proof a b c d)
  | Infeasible_Split_If
      (Term_Rewriting.Term (Labelings.Lab a d) b,
        (Term_Rewriting.Term (Labelings.Lab a d) b,
          [(((Term_Rewriting.Term (Labelings.Lab a d) b,
               Term_Rewriting.Term (Labelings.Lab a d) b),
              [(Term_Rewriting.Term (Labelings.Lab a d) b,
                 Term_Rewriting.Term (Labelings.Lab a d) b)]),
             (Labelings.Lab a d,
               [Term_Rewriting.Term (Labelings.Lab a d) b]))]))
      (Check_Nonreachability.Nonreachability_proof a b c d)
  | Infeasible_Goal_Lifting (Labelings.Lab a d) (Labelings.Lab a d)
      (Infeasibility_proof a b c d);

check_inf_transform ::
  forall a b.
    (Compare.Compare a, Eq a, Shows_Literal.Showl a, Arith.Finite_UNIV b,
      Arith.Cenum b, Arith.Ceq b, Arith.Cproper_interval b, Compare.Compare b,
      Eq b, Arith.Set_impl b,
      Shows_Literal.Showl b) => [((Term_Rewriting.Term a b,
                                    Term_Rewriting.Term a b),
                                   [(Term_Rewriting.Term a b,
                                      Term_Rewriting.Term a b)])] ->
                                  Inf_transformation a b ->
                                    Sum_Type.Sum (String -> String)
                                      [((Term_Rewriting.Term a b,
  Term_Rewriting.Term a b),
 [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)])];
check_inf_transform ra (Ifrit_Rules_Inf r) =
  Error_Monad.bind
    (Check_Monad.check (Ifrit_Impl.check_Ifrit_rules_iff ra r)
      (Shows_Literal.showsl_lit "Given rules are not sound wrt Ifrit."))
    (\ _ -> Sum_Type.Inr r);
check_inf_transform ra (Left_Inline_Conditions_Inf r rcs) =
  Error_Monad.bind
    (Left_Inline_Conditions_Impl.check_left_inline_conds ra r rcs)
    (\ _ -> Sum_Type.Inr r);
check_inf_transform ra (Right_Inline_Conditions_Inf r rcs) =
  Error_Monad.bind (Inline_Conditions_Impl.check_inline_conds ra r rcs)
    (\ _ -> Sum_Type.Inr r);

check_infeasible ::
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
       Infeasibility_proof c [Arith.Char] e [Arith.Nat] ->
         Sum_Type.Sum (String -> String) ();
check_infeasible a ia i j r cs (Infeasible_Compound_Conditions f p) =
  Check_Nonreachability.check_nonreachable a ia i j (map fst r)
    (Term_Rewriting.Fun f (map fst cs)) (Term_Rewriting.Fun f (map snd cs)) p;
check_infeasible a ia i j r cs (Infeasible_Equation s t p) =
  Error_Monad.bind
    (Check_Monad.check (Arith.membera cs (s, t))
      ((Shows_Literal.showsl_lit "equation " .
         Equational_Reasoning_Impl.showsl_eq (s, t)) .
        Shows_Literal.showsl_lit " is not in list of conditions\n"))
    (\ _ ->
      Check_Nonreachability.check_nonreachable a ia i j (map fst r) s t p);
check_infeasible a ia i j r csa (Infeasible_Subset cs p) =
  Error_Monad.bind
    (Error_Monad.catch_error (Check_Monad.check_subseteq cs csa)
      (\ x ->
        Sum_Type.Inl
          ((Shows_Literal.showsl_lit "equation " .
             Equational_Reasoning_Impl.showsl_eq x) .
            Shows_Literal.showsl_lit " is not in list of conditions\n")))
    (\ _ -> check_infeasible a ia i j r cs p);
check_infeasible a ia i j r cs (Infeasible_Rhss_Equal s t u p) =
  Error_Monad.bind
    (Check_Monad.check (Arith.membera cs (s, u))
      ((Shows_Literal.showsl_lit "equation " .
         Equational_Reasoning_Impl.showsl_eq (s, u)) .
        Shows_Literal.showsl_lit " is not in list of conditions\n"))
    (\ _ ->
      Error_Monad.bind
        (Check_Monad.check (Arith.membera cs (t, u))
          ((Shows_Literal.showsl_lit "equation " .
             Equational_Reasoning_Impl.showsl_eq (t, u)) .
            Shows_Literal.showsl_lit " is not in list of conditions\n"))
        (\ _ ->
          Check_Nonreachability.check_nonjoinable a ia i j (map fst r) s t p));
check_infeasible a ia i j r cs (Infeasible_Trans s t u p) =
  Error_Monad.bind
    (Check_Monad.check (Arith.membera cs (s, t))
      ((Shows_Literal.showsl_lit "equation " .
         Equational_Reasoning_Impl.showsl_eq (s, t)) .
        Shows_Literal.showsl_lit " is not in list of conditions\n"))
    (\ _ ->
      Error_Monad.bind
        (Check_Monad.check (Arith.membera cs (t, u))
          ((Shows_Literal.showsl_lit "equation " .
             Equational_Reasoning_Impl.showsl_eq (t, u)) .
            Shows_Literal.showsl_lit " is not in list of conditions\n"))
        (\ _ ->
          Check_Nonreachability.check_nonreachable a ia i j (map fst r) s u p));
check_infeasible a ia i j r cs (Infeasible_Transform t p) =
  Error_Monad.bind (check_inf_transform r t)
    (\ ra -> check_infeasible a ia i j ra cs p);
check_infeasible a ia i j r cs (Infeasible_Split_If s p) =
  (case s of {
    (t, (f, _)) ->
      Error_Monad.bind
        (Check_Monad.check (Term_Rewriting.ground t)
          ((Shows_Literal.showsl_lit "the term " .
             Term_Rewriting.showsl_terma t) .
            Shows_Literal.showsl_lit " is not ground"))
        (\ _ ->
          Error_Monad.bind
            (Check_Monad.check (Term_Rewriting.ground f)
              ((Shows_Literal.showsl_lit "the term " .
                 Term_Rewriting.showsl_terma f) .
                Shows_Literal.showsl_lit " is not ground"))
            (\ _ ->
              Error_Monad.bind
                (Check_Monad.check (Arith.membera cs (t, f))
                  ((Shows_Literal.showsl_lit "the equation " .
                     Equational_Reasoning_Impl.showsl_eq (t, f)) .
                    Shows_Literal.showsl_lit
                      " is not contained in the infeasibility query"))
                (\ _ ->
                  Check_Nonreachability.check_nonreachable a ia i j
                    (Unraveling_Impl.split_if s r cs) t f p)));
  });
check_infeasible a ia i j r cs (Infeasible_Goal_Lifting t f p) =
  check_infeasible a ia i j
    (((Term_Rewriting.Fun t [], Term_Rewriting.Fun f []), cs) : r)
    [(Term_Rewriting.Fun t [], Term_Rewriting.Fun f [])] p;

check_infeasible_rules ::
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
     [(((Term_Rewriting.Term (Labelings.Lab c [Arith.Nat]) [Arith.Char],
          Term_Rewriting.Term (Labelings.Lab c [Arith.Nat]) [Arith.Char]),
         [(Term_Rewriting.Term (Labelings.Lab c [Arith.Nat]) [Arith.Char],
            Term_Rewriting.Term (Labelings.Lab c [Arith.Nat]) [Arith.Char])]),
        Infeasibility_proof c [Arith.Char] e [Arith.Nat])] ->
       Sum_Type.Sum (String -> String) ();
check_infeasible_rules a ia i j r =
  (\ xs ->
    Error_Monad.catch_error
      (Error_Monad.forallM
        (\ (ra, ps) ->
          Error_Monad.catch_error (check_infeasible a ia i j r (snd ra) ps)
            (\ x ->
              Sum_Type.Inl
                (((Shows_Literal.showsl_lit "rule " .
                    Conditional_Rewriting_Impl.showsl_crule ra) .
                   Shows_Literal.showsl_lit " is not infeasible\n") .
                  x)))
        xs)
      (\ x -> Sum_Type.Inl (snd x)));

check_feasibility_proof ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Arith.Ccompare b, Fresh.Infinite b, Eq b,
      Mapping.Mapping_impl b,
      Shows_Literal.Showl b) => [((Term_Rewriting.Term a b,
                                    Term_Rewriting.Term a b),
                                   [(Term_Rewriting.Term a b,
                                      Term_Rewriting.Term a b)])] ->
                                  [(Term_Rewriting.Term a b,
                                     Term_Rewriting.Term a b)] ->
                                    Feasibility_proof a b ->
                                      Sum_Type.Sum (String -> String) ();
check_feasibility_proof r cs (Feasible_Witness sigma prf) =
  Error_Monad.catch_error
    (Conditional_Rewriting_Impl.check_feasibility r cs
      (Term_Rewriting.subst_of sigma) prf)
    (\ x ->
      Sum_Type.Inl
        ((((((Shows_Literal.showsl_lit
                "problem in proving feasibility of conditions\n" .
               Shows_Literal.showsl_lines "" cs) .
              Shows_Literal.showsl_literal "\n") .
             Shows_Literal.showsl_lit "via substitution ") .
            Shows_Literal.showsl_lista sigma) .
           Shows_Literal.showsl_literal "\n") .
          x));

}
