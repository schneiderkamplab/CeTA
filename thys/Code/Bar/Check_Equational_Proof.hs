{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Check_Equational_Proof(Equational_proof(..), Equational_disproof(..),
                          check_equational_proof, check_equational_disproof)
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
import qualified Check_Joins;
import qualified FOR_Preliminaries;
import qualified HOL;
import qualified Dependency_Pair_Problem_Spec;
import qualified Termination_Problem_Spec;
import qualified Countable;
import qualified Compare;
import qualified Labelings_Impl;
import qualified Mapping;
import qualified Equational_Reasoning_Impl;
import qualified Error_Monad;
import qualified Sum_Type;
import qualified Shows_Literal;
import qualified Ordered_Completion_Impl;
import qualified Arith;
import qualified Check_Completion_Proof;
import qualified Equational_Reasoning;
import qualified Labelings;
import qualified Term_Rewriting;

data Equational_proof a b c =
  Equational_Proof_Tree (Equational_Reasoning.Eq_proof (Labelings.Lab a b) c)
  | Completion_and_Normalization
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      (Check_Completion_Proof.Completion_proof a b c)
  | Conversion [Term_Rewriting.Term (Labelings.Lab a b) c]
  | Conversion_With_History
      [((Term_Rewriting.Term (Labelings.Lab a b) c,
          Term_Rewriting.Term (Labelings.Lab a b) c),
         [Term_Rewriting.Term (Labelings.Lab a b) c])];

data Equational_disproof a b c =
  Completion_and_Normalization_Different
    [(Term_Rewriting.Term (Labelings.Lab a b) c,
       Term_Rewriting.Term (Labelings.Lab a b) c)]
    (Check_Completion_Proof.Completion_proof a b c)
  | Approx_and_Completion_and_Normalization_Different
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      (Check_Completion_Proof.Approx_completion_proof a b c)
  | Ordered_Completion_and_Normalization_Different
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      [(Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char],
         Term_Rewriting.Term (Labelings.Lab a b) [Arith.Char])]
      (Ordered_Completion_Impl.Reduction_order_input (Labelings.Lab a b))
      (Ordered_Completion_Impl.Ordered_completion_proof (Labelings.Lab a b) c)
  | Approx_and_Ordered_Completion_and_Normalization_Different
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      [(Term_Rewriting.Term (Labelings.Lab a b) c,
         Term_Rewriting.Term (Labelings.Lab a b) c)]
      (Ordered_Completion_Impl.Reduction_order_input (Labelings.Lab a b));

check_proves ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => [(Term_Rewriting.Term a b,
                                   Term_Rewriting.Term a b)] ->
                                  Equational_Reasoning.Eq_proof a b ->
                                    Sum_Type.Sum (String -> String)
                                      (Term_Rewriting.Term a b,
Term_Rewriting.Term a b);
check_proves e (Equational_Reasoning.Refl s) = Sum_Type.Inr (s, s);
check_proves e (Equational_Reasoning.Sym p) =
  Error_Monad.bind (check_proves e p) (\ (s, t) -> Sum_Type.Inr (t, s));
check_proves e (Equational_Reasoning.Trans p1 p2) =
  Error_Monad.bind (check_proves e p1)
    (\ (s, t) ->
      Error_Monad.bind (check_proves e p2)
        (\ (ta, u) ->
          (if Term_Rewriting.equal_term t ta then Sum_Type.Inr (s, u)
            else Sum_Type.Inl
                   (((((Shows_Literal.showsl_lit
                          "the error occurs in the following part \n" .
                         fst (Equational_Reasoning_Impl.eq_proof_lines
                               (Equational_Reasoning.Trans p1 p2)
                               Arith.zero_nat)) .
                        Shows_Literal.showsl_lit "\n\n") .
                       Term_Rewriting.showsl_terma t) .
                      Shows_Literal.showsl_lit " is not equal to ") .
                     Term_Rewriting.showsl_terma ta))));
check_proves e (Equational_Reasoning.Assm (l, r) sigma) =
  (if Arith.membera e (l, r)
    then Sum_Type.Inr
           (Term_Rewriting.eval_term Term_Rewriting.Fun l sigma,
             Term_Rewriting.eval_term Term_Rewriting.Fun r sigma)
    else Sum_Type.Inl
           (((((Shows_Literal.showsl_lit
                  "the error occurs in the following part \n" .
                 fst (Equational_Reasoning_Impl.eq_proof_lines
                       (Equational_Reasoning.Assm (l, r) sigma)
                       Arith.zero_nat)) .
                Shows_Literal.showsl_lit "\n\n") .
               Equational_Reasoning_Impl.showsl_eq (l, r)) .
              Shows_Literal.showsl_lit " is not in the ") .
             Equational_Reasoning_Impl.showsl_eqs e));
check_proves e (Equational_Reasoning.Cong f ps) =
  Error_Monad.bind (Error_Monad.mapM (check_proves e) ps)
    (\ sts ->
      Sum_Type.Inr
        (Term_Rewriting.Fun f (map fst sts),
          Term_Rewriting.Fun f (map snd sts)));

check_eq_proof ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => [(Term_Rewriting.Term a b,
                                   Term_Rewriting.Term a b)] ->
                                  Equational_Reasoning.Eq_proof a b ->
                                    (Term_Rewriting.Term a b,
                                      Term_Rewriting.Term a b) ->
                                      Sum_Type.Sum (String -> String) ();
check_eq_proof e p eq =
  Error_Monad.catch_error
    (Error_Monad.bind (check_proves e p)
      (\ eqa ->
        (if eq == eqa then Sum_Type.Inr ()
          else Sum_Type.Inl
                 (Shows_Literal.showsl_lit "the proof does not fit the goal"))))
    (\ x ->
      Sum_Type.Inl
        (((((((Shows_Literal.showsl_lit
                 "there is an error in the equational logic proof\n" .
                fst (Equational_Reasoning_Impl.eq_proof_lines p
                      Arith.zero_nat)) .
               Shows_Literal.showsl_lit "\n\nfor proving the equation\n\n") .
              Equational_Reasoning_Impl.showsl_eq eq) .
             Shows_Literal.showsl_lit "\n\nusing the ") .
            Equational_Reasoning_Impl.showsl_eqs e) .
           Shows_Literal.showsl_literal "\n") .
          x));

check_equational_proof ::
  forall a b c.
    (Compare.Compare_order b, Countable.Countable b, Eq b,
      Shows_Literal.Showl b) => Bool ->
                                  (String -> String) ->
                                    Termination_Problem_Spec.Tp_ops_ext a
                                      (Labelings.Lab b [Arith.Nat]) [Arith.Char]
                                      () ->
                                      Dependency_Pair_Problem_Spec.Dpp_ops_ext c
(Labelings.Lab b [Arith.Nat]) [Arith.Char] () ->
[(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
   Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
  (Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
    Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char]) ->
    Equational_proof b [Arith.Nat] [Arith.Char] ->
      Sum_Type.Sum (String -> String) ();
check_equational_proof a ia i j e eq (Equational_Proof_Tree p) =
  FOR_Preliminaries.debug ia "Equational_Proof_Tree" (check_eq_proof e p eq);
check_equational_proof a ia i j e eq (Conversion eseq) =
  FOR_Preliminaries.debug ia "Conversion"
    (Check_Joins.check_conversion_sequence e (fst eq) (snd eq) eseq);
check_equational_proof a ia i j e eq (Conversion_With_History convs) =
  FOR_Preliminaries.debug ia "Conversion with History"
    (Equational_Reasoning_Impl.check_single_subsumption eq e convs);
check_equational_proof a ia i j e eq (Completion_and_Normalization r p) =
  FOR_Preliminaries.debug ia "Completion_and_Normalization"
    (Error_Monad.bind
      (Check_Completion_Proof.check_completion_proof a ia i j e r p)
      (\ _ ->
        let {
          s = fst eq;
          t = snd eq;
        } in (case (Term_Rewriting.compute_rstep_NF r s,
                     Term_Rewriting.compute_rstep_NF r t)
               of {
               (Nothing, _) ->
                 Sum_Type.Inl
                   (((Shows_Literal.showsl_lit
                        "error when computing normal forms of " .
                       Term_Rewriting.showsl_terma s) .
                      Shows_Literal.showsl_lit " and ") .
                     Term_Rewriting.showsl_terma t);
               (Just _, Nothing) ->
                 Sum_Type.Inl
                   (((Shows_Literal.showsl_lit
                        "error when computing normal forms of " .
                       Term_Rewriting.showsl_terma s) .
                      Shows_Literal.showsl_lit " and ") .
                     Term_Rewriting.showsl_terma t);
               (Just sa, Just ta) ->
                 (if Term_Rewriting.equal_term sa ta then Sum_Type.Inr ()
                   else Sum_Type.Inl
                          (((Term_Rewriting.showsl_terma s .
                              Shows_Literal.showsl_lit " and ") .
                             Term_Rewriting.showsl_terma t) .
                            Shows_Literal.showsl_lit
                              " have different normal forms"));
             })));

check_equational_disproof ::
  forall a b c.
    (Compare.Compare_order b, Countable.Countable b, Eq b,
      Shows_Literal.Showl b) => Bool ->
                                  (String -> String) ->
                                    Termination_Problem_Spec.Tp_ops_ext a
                                      (Labelings.Lab b [Arith.Nat]) [Arith.Char]
                                      () ->
                                      Dependency_Pair_Problem_Spec.Dpp_ops_ext c
(Labelings.Lab b [Arith.Nat]) [Arith.Char] () ->
[(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
   Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char])] ->
  (Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char],
    Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) [Arith.Char]) ->
    Equational_disproof b [Arith.Nat] [Arith.Char] ->
      Sum_Type.Sum (String -> String) ();
check_equational_disproof a ia i j e eq
  (Completion_and_Normalization_Different r p) =
  FOR_Preliminaries.debug ia "Completion_and_Normalization"
    (Error_Monad.bind
      (Check_Completion_Proof.check_completion_proof a ia i j e r p)
      (\ _ ->
        let {
          s = fst eq;
          t = snd eq;
        } in (case (Term_Rewriting.compute_rstep_NF r s,
                     Term_Rewriting.compute_rstep_NF r t)
               of {
               (Nothing, _) ->
                 Sum_Type.Inl
                   (((Shows_Literal.showsl_lit
                        "error when computing normal forms of " .
                       Term_Rewriting.showsl_terma s) .
                      Shows_Literal.showsl_lit " and ") .
                     Term_Rewriting.showsl_terma t);
               (Just _, Nothing) ->
                 Sum_Type.Inl
                   (((Shows_Literal.showsl_lit
                        "error when computing normal forms of " .
                       Term_Rewriting.showsl_terma s) .
                      Shows_Literal.showsl_lit " and ") .
                     Term_Rewriting.showsl_terma t);
               (Just sa, Just ta) ->
                 (if not (Term_Rewriting.equal_term sa ta) then Sum_Type.Inr ()
                   else Sum_Type.Inl
                          ((((Term_Rewriting.showsl_terma s .
                               Shows_Literal.showsl_lit " and ") .
                              Term_Rewriting.showsl_terma t) .
                             Shows_Literal.showsl_lit
                               " have same normal form ") .
                            Term_Rewriting.showsl_terma sa));
             })));
check_equational_disproof a ia i j e eq
  (Approx_and_Completion_and_Normalization_Different r p) =
  FOR_Preliminaries.debug ia "Approx_and_Completion_and_Normalization"
    (Error_Monad.bind
      (Check_Completion_Proof.check_approx_completion_proof a ia i j e r p)
      (\ _ ->
        let {
          s = fst eq;
          t = snd eq;
        } in (case (Term_Rewriting.compute_rstep_NF r s,
                     Term_Rewriting.compute_rstep_NF r t)
               of {
               (Nothing, _) ->
                 Sum_Type.Inl
                   (((Shows_Literal.showsl_lit
                        "error when computing normal forms of " .
                       Term_Rewriting.showsl_terma s) .
                      Shows_Literal.showsl_lit " and ") .
                     Term_Rewriting.showsl_terma t);
               (Just _, Nothing) ->
                 Sum_Type.Inl
                   (((Shows_Literal.showsl_lit
                        "error when computing normal forms of " .
                       Term_Rewriting.showsl_terma s) .
                      Shows_Literal.showsl_lit " and ") .
                     Term_Rewriting.showsl_terma t);
               (Just sa, Just ta) ->
                 (if not (Term_Rewriting.equal_term sa ta) then Sum_Type.Inr ()
                   else Sum_Type.Inl
                          ((((Term_Rewriting.showsl_terma s .
                               Shows_Literal.showsl_lit " and ") .
                              Term_Rewriting.showsl_terma t) .
                             Shows_Literal.showsl_lit
                               " have same normal form ") .
                            Term_Rewriting.showsl_terma sa));
             })));
check_equational_disproof a ia i j e_0 eq
  (Ordered_Completion_and_Normalization_Different r e ro p) =
  FOR_Preliminaries.debug ia "Ordered_Completion_and_Normalization"
    (Ordered_Completion_Impl.check_equational_disproof_oc ia eq e_0 e r ro p);
check_equational_disproof a ia i j e_0 eq
  (Approx_and_Ordered_Completion_and_Normalization_Different r e ro) =
  FOR_Preliminaries.debug ia "Approx_and_Ordered_Completion_and_Normalization"
    (Ordered_Completion_Impl.check_equational_disproof_by_ground_complete_system
      ia eq e_0 e r ro);

}
