{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Subterm_Criterion_Impl(ProjL(..), create_proj, subterm_criterion_proc)
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
import qualified Q_Restricted_Rewriting_Impl;
import qualified Mapping;
import qualified Map_Choice;
import qualified HOL;
import qualified Compare;
import qualified Compare_Order_Instances;
import qualified Subterm_Criterion;
import qualified Error_Monad;
import qualified Check_Monad;
import qualified Sum_Type;
import qualified Term_Rewriting;
import qualified Shows_Literal;
import qualified Arith;

newtype ProjL a = Projection [((a, Arith.Nat), Arith.Nat)];

check_weak ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => ((a, Arith.Nat) -> Arith.Nat) ->
                                  (Term_Rewriting.Term a b,
                                    Term_Rewriting.Term a b) ->
                                    Sum_Type.Sum (String -> String) ();
check_weak p r =
  Error_Monad.catch_error
    (Check_Monad.check
      (Term_Rewriting.equal_term (Subterm_Criterion.proj_term p (fst r))
        (Subterm_Criterion.proj_term p (snd r)))
      (Shows_Literal.showsl_lit
        "the projected lhs is not equal to the projected rhs\n"))
    (\ x ->
      Sum_Type.Inl
        (((((((Shows_Literal.showsl_lit "Could not orient rule " .
                Term_Rewriting.showsl_rule r) .
               Shows_Literal.showsl_lit ", since\n") .
              Term_Rewriting.showsl_terma
                (Subterm_Criterion.proj_term p (fst r))) .
             Shows_Literal.showsl_lit " != ") .
            Term_Rewriting.showsl_terma
              (Subterm_Criterion.proj_term p (snd r))) .
           Shows_Literal.showsl_literal "\n") .
          x));

create_proj ::
  forall a. (Compare.Compare_order a) => ProjL a -> (a, Arith.Nat) -> Arith.Nat;
create_proj (Projection p) = let {
                               i = Map_Choice.ceta_map_of p;
                             } in (\ f -> (case i f of {
    Nothing -> Arith.zero_nat;
    Just n -> n;
  }));

create_rseq_map ::
  forall a b.
    (Compare.Compare_order a,
      Compare.Compare_order b) => [((Term_Rewriting.Term a b,
                                      Term_Rewriting.Term a b),
                                     [([Arith.Nat],
((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
  Term_Rewriting.Term a b))])] ->
                                    (Term_Rewriting.Term a b,
                                      Term_Rewriting.Term a b) ->
                                      Maybe [([Arith.Nat],
       ((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
         Term_Rewriting.Term a b))];
create_rseq_map rseqs = Map_Choice.ceta_map_of rseqs;

check_strict_rstep ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b,
      Shows_Literal.Showl b) => [(Term_Rewriting.Term a b,
                                   Term_Rewriting.Term a b)] ->
                                  ((Term_Rewriting.Term a b,
                                     Term_Rewriting.Term a b) ->
                                    Maybe [([Arith.Nat],
     ((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
       Term_Rewriting.Term a b))]) ->
                                    ((a, Arith.Nat) -> Arith.Nat) ->
                                      (Term_Rewriting.Term a b,
Term_Rewriting.Term a b) ->
Sum_Type.Sum (String -> String) ();
check_strict_rstep ra rseqm p r =
  let {
    s = Subterm_Criterion.proj_term p (fst r);
    t = Subterm_Criterion.proj_term p (snd r);
  } in (case rseqm r of {
         Nothing -> Term_Rewriting.check_supt s t;
         Just rseq ->
           (if Arith.equal_nat (Arith.size_list rseq) Arith.zero_nat
             then Term_Rewriting.check_supt s t
             else Error_Monad.bind
                    (Q_Restricted_Rewriting_Impl.check_rsteps_last ra s rseq)
                    (\ _ ->
                      Term_Rewriting.check_supteq
                        (Q_Restricted_Rewriting_Impl.rseq_last s rseq) t));
       });

check_strict_one_rstep ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b,
      Shows_Literal.Showl b) => [(Term_Rewriting.Term a b,
                                   Term_Rewriting.Term a b)] ->
                                  ((Term_Rewriting.Term a b,
                                     Term_Rewriting.Term a b) ->
                                    Maybe [([Arith.Nat],
     ((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
       Term_Rewriting.Term a b))]) ->
                                    ((a, Arith.Nat) -> Arith.Nat) ->
                                      (Term_Rewriting.Term a b,
Term_Rewriting.Term a b) ->
Sum_Type.Sum (String -> String) ();
check_strict_one_rstep ra rseqm p r =
  let {
    s = Subterm_Criterion.proj_term p (fst r);
    t = Subterm_Criterion.proj_term p (snd r);
  } in (case rseqm r of {
         Nothing -> Term_Rewriting.check_supt s t;
         Just [] ->
           Sum_Type.Inl
             (Shows_Literal.showsl_lit
               "more than a single rewrite step is not allowed");
         Just [(pos, (rule, u))] ->
           Error_Monad.bind
             (Q_Restricted_Rewriting_Impl.check_qrstep (\ _ -> True) False ra
               pos rule s u)
             (\ _ -> Term_Rewriting.check_supteq u t);
         Just ((_, (_, _)) : _ : _) ->
           Sum_Type.Inl
             (Shows_Literal.showsl_lit
               "more than a single rewrite step is not allowed");
       });

subterm_criterion_proc ::
  forall a b c.
    (Compare.Compare_order b, Eq b, Shows_Literal.Showl b, Arith.Ccompare c,
      Compare.Compare_order c, Eq c, Mapping.Mapping_impl c,
      Shows_Literal.Showl c) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b c
                                  () ->
                                  ProjL b ->
                                    [((Term_Rewriting.Term b c,
Term_Rewriting.Term b c),
                                       [([Arith.Nat],
  ((Term_Rewriting.Term b c, Term_Rewriting.Term b c),
    Term_Rewriting.Term b c))])] ->
                                      [(Term_Rewriting.Term b c,
 Term_Rewriting.Term b c)] ->
a -> Sum_Type.Sum (String -> String) a;
subterm_criterion_proc i pL rseqmL prm dpp =
  (case let {
          p = create_proj pL;
          rseqm = create_rseq_map rseqmL;
          pa = Dependency_Pair_Problem_Spec.pairs i dpp;
          _ = Dependency_Pair_Problem_Spec.nfs i dpp;
          r = Dependency_Pair_Problem_Spec.rules i dpp;
          pb = snd (Dependency_Pair_Problem_Spec.split_pairs i dpp prm);
          wfR = Term_Rewriting.wf_rules_impl r;
        } in Error_Monad.bind
               (Error_Monad.catch_error
                 (Error_Monad.forallM
                   (\ (l, ra) ->
                     Error_Monad.bind (Term_Rewriting.check_no_var l)
                       (\ _ ->
                         Error_Monad.bind (Term_Rewriting.check_no_var ra)
                           (\ _ ->
                             Q_Restricted_Rewriting_Impl.check_no_defined_root
                               (\ fn ->
                                 not (null (Dependency_Pair_Problem_Spec.rules_map
     i dpp fn)))
                               ra)))
                   pa)
                 (\ x -> Sum_Type.Inl (snd x)))
               (\ _ ->
                 Error_Monad.bind
                   (Check_Monad.check
                     (Dependency_Pair_Problem_Spec.minimal i dpp ||
                       Dependency_Pair_Problem_Spec.nFQ_subset_NF_rules i dpp)
                     (Shows_Literal.showsl_lit
                       "minimality or innermost required"))
                   (\ _ ->
                     Error_Monad.bind
                       (Error_Monad.catch_error
                         (Error_Monad.forallM
                           (\ (l, _) -> Term_Rewriting.check_no_var l) r)
                         (\ x -> Sum_Type.Inl (snd x)))
                       (\ _ ->
                         Error_Monad.bind
                           (if Dependency_Pair_Problem_Spec.q_empty i dpp
                             then Error_Monad.catch_error
                                    (Error_Monad.forallM
                                      (check_strict_rstep r rseqm p) prm)
                                    (\ x -> Sum_Type.Inl (snd x))
                             else Error_Monad.catch_error
                                    (Error_Monad.forallM
                                      (check_strict_one_rstep wfR rseqm p) prm)
                                    (\ x -> Sum_Type.Inl (snd x)))
                           (\ _ ->
                             Error_Monad.catch_error
                               (Error_Monad.forallM (check_weak p) pb)
                               (\ x -> Sum_Type.Inl (snd x))))))
    of {
    Sum_Type.Inl a -> Sum_Type.Inl a;
    Sum_Type.Inr _ ->
      Sum_Type.Inr (Dependency_Pair_Problem_Spec.delete_P_Pw i dpp prm prm);
  });

}
