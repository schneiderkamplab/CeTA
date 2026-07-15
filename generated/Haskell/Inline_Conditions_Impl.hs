{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Inline_Conditions_Impl(find_index, check_inline_conds) where {

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
import qualified Complete_Lattices;
import qualified Inline_Conditions;
import qualified HOL;
import qualified Conditional_Rewriting_Impl;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified Compare;
import qualified Term_Rewriting;
import qualified Sum_Type;
import qualified Arith;

find_index ::
  forall a. (Eq a) => Arith.Nat -> a -> [a] -> Sum_Type.Sum () Arith.Nat;
find_index i x [] = Sum_Type.Inl ();
find_index i x (y : ys) =
  (if x == y then Sum_Type.Inr i else find_index (Arith.suc i) x ys);

check_inline_conds_rule ::
  forall a b.
    (Compare.Compare a, Eq a, Term_Rewriting.Showl a, Arith.Finite_UNIV b,
      Arith.Cenum b, Arith.Ceq b, Arith.Cproper_interval b, Compare.Compare b,
      Eq b, Arith.Set_impl b,
      Term_Rewriting.Showl b) => [((Term_Rewriting.Term a b,
                                     Term_Rewriting.Term a b),
                                    [(Term_Rewriting.Term a b,
                                       Term_Rewriting.Term a b)])] ->
                                   ((Term_Rewriting.Term a b,
                                      Term_Rewriting.Term a b),
                                     [(Term_Rewriting.Term a b,
Term_Rewriting.Term a b)]) ->
                                     [(Term_Rewriting.Term a b,
Term_Rewriting.Term a b)] ->
                                       Sum_Type.Sum (String -> String)
 ([((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
     [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)])],
   ((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
     [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]));
check_inline_conds_rule r rho [] = Sum_Type.Inr (r, rho);
check_inline_conds_rule r rho (c : cs) =
  Error_Monad.catch_error
    (case rho of {
      (a, b) ->
        (case a of {
          (l, _) ->
            (\ csa ->
              (case c of {
                (s, t) ->
                  Error_Monad.bind
                    (Check_Monad.check (Term_Rewriting.is_Var t)
                      (Term_Rewriting.showsl_lit
                        "condition with non-variable rhs"))
                    (\ _ ->
                      let {
                        x = Term_Rewriting.the_Var t;
                      } in Error_Monad.bind
                             (Error_Monad.catch_error
                               (find_index Arith.zero_nat c csa)
                               (\ xa ->
                                 Sum_Type.Inl
                                   (case xa of {
                                     () -> Term_Rewriting.showsl_lit
     "condition does not occur in rule";
                                   })))
                             (\ i ->
                               Error_Monad.bind
                                 (Check_Monad.check
                                   (not (Term_Rewriting.contains_var_term x s))
                                   (Term_Rewriting.showsl_lit
                                     "occurs check failed"))
                                 (\ _ ->
                                   Error_Monad.bind
                                     (Check_Monad.check
                                       (not
 (Term_Rewriting.contains_var_term x l))
                                       (Term_Rewriting.showsl_lit
 "inlining not allowed in lhs of rule"))
                                     (\ _ ->
                                       Error_Monad.bind
 (Check_Monad.check
   (not (Arith.member x
          (Arith.sup_set
            (Complete_Lattices.sup_set
              (Arith.image Term_Rewriting.vars_term
                (Arith.image snd (Arith.set (Arith.take i csa)))))
            (Complete_Lattices.sup_set
              (Arith.image Term_Rewriting.vars_term
                (Arith.image snd
                  (Arith.set (Arith.drop (Arith.suc i) csa))))))))
   (Term_Rewriting.showsl_lit "inlining not allowed in rhss of conditions"))
 (\ _ ->
   check_inline_conds_rule
     (Inline_Conditions.inline i rho : Arith.removeAll rho r)
     (Inline_Conditions.inline i rho)
     (map (\ (u, aa) ->
            (Term_Rewriting.eval_term Term_Rewriting.Fun u
               (Term_Rewriting.subst x s),
              aa))
       cs))))));
              }));
        })
          b;
    })
    (\ x ->
      Sum_Type.Inl
        (((((Term_Rewriting.showsl_lit "error while inlining condition " .
              Conditional_Rewriting_Impl.showsl_eq c) .
             Term_Rewriting.showsl_lit " of rule ") .
            Conditional_Rewriting_Impl.showsl_crule rho) .
           Term_Rewriting.showsl_literal "\n") .
          x));

check_inline_conds_ctrs ::
  forall a b.
    (Compare.Compare a, Eq a, Term_Rewriting.Showl a, Arith.Finite_UNIV b,
      Arith.Cenum b, Arith.Ceq b, Arith.Cproper_interval b, Compare.Compare b,
      Eq b, Arith.Set_impl b,
      Term_Rewriting.Showl b) => [((Term_Rewriting.Term a b,
                                     Term_Rewriting.Term a b),
                                    [(Term_Rewriting.Term a b,
                                       Term_Rewriting.Term a b)])] ->
                                   [(((Term_Rewriting.Term a b,
Term_Rewriting.Term a b),
                                       [(Term_Rewriting.Term a b,
  Term_Rewriting.Term a b)]),
                                      [(Term_Rewriting.Term a b,
 Term_Rewriting.Term a b)])] ->
                                     Sum_Type.Sum (String -> String)
                                       [((Term_Rewriting.Term a b,
   Term_Rewriting.Term a b),
  [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)])];
check_inline_conds_ctrs r [] = Sum_Type.Inr r;
check_inline_conds_ctrs ra ((r, cs) : rcs) =
  Error_Monad.catch_error
    (Error_Monad.bind
      (Check_Monad.check (Arith.membera ra r)
        (Conditional_Rewriting_Impl.showsl_crule r .
          Term_Rewriting.showsl_lit " does not occur in the input CTRS"))
      (\ _ ->
        Error_Monad.bind (check_inline_conds_rule ra r cs)
          (\ (rb, raa) ->
            check_inline_conds_ctrs (raa : Arith.removeAll raa rb) rcs)))
    (\ x ->
      Sum_Type.Inl
        (Term_Rewriting.showsl_lit "error while inlining conditions\n" . x));

check_inline_conds ::
  forall a b.
    (Compare.Compare a, Eq a, Term_Rewriting.Showl a, Arith.Finite_UNIV b,
      Arith.Cenum b, Arith.Ceq b, Arith.Cproper_interval b, Compare.Compare b,
      Eq b, Arith.Set_impl b,
      Term_Rewriting.Showl b) => [((Term_Rewriting.Term a b,
                                     Term_Rewriting.Term a b),
                                    [(Term_Rewriting.Term a b,
                                       Term_Rewriting.Term a b)])] ->
                                   [((Term_Rewriting.Term a b,
                                       Term_Rewriting.Term a b),
                                      [(Term_Rewriting.Term a b,
 Term_Rewriting.Term a b)])] ->
                                     [(((Term_Rewriting.Term a b,
  Term_Rewriting.Term a b),
 [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]),
[(Term_Rewriting.Term a b, Term_Rewriting.Term a b)])] ->
                                       Sum_Type.Sum (String -> String) ();
check_inline_conds ra r rcs =
  Error_Monad.bind (check_inline_conds_ctrs ra rcs)
    (\ raa ->
      Error_Monad.catch_error (Check_Monad.check_same_set r raa)
        (\ _ ->
          Sum_Type.Inl
            ((((Term_Rewriting.showsl_lit "error while inlining:" .
                 Term_Rewriting.showsl_lit "\ninternally computed CTRS\n") .
                Conditional_Rewriting_Impl.showsl_ctrs raa) .
               Term_Rewriting.showsl_lit "\nbut certificate contains CTRS\n") .
              Conditional_Rewriting_Impl.showsl_ctrs r)));

}
