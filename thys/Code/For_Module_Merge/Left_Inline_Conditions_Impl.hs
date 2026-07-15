{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Left_Inline_Conditions_Impl(check_left_inline_conds) where {

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
import qualified Left_Inline_Conditions;
import qualified Inline_Conditions_Impl;
import qualified Term_Impl;
import qualified Term_More;
import qualified HOL;
import qualified Set;
import qualified Arith;
import qualified Container_Setup;
import qualified Product_Type;
import qualified List;
import qualified Conditional_Rewriting_Impl;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified Sum_Type;
import qualified Collection_Order;
import qualified Cardinality;
import qualified Collection_Enum;
import qualified Shows_Literal;
import qualified Set_Impl;
import qualified Collection_Eq;
import qualified Compare;
import qualified Term;

check_left_inline_conds_rule ::
  forall a b.
    (Compare.Compare a, Eq a, Shows_Literal.Showl a, Cardinality.Finite_UNIV b,
      Collection_Enum.Cenum b, Collection_Eq.Ceq b,
      Collection_Order.Cproper_interval b, Compare.Compare b, Eq b,
      Set_Impl.Set_impl b,
      Shows_Literal.Showl b) => [((Term.Term a b, Term.Term a b),
                                   [(Term.Term a b, Term.Term a b)])] ->
                                  ((Term.Term a b, Term.Term a b),
                                    [(Term.Term a b, Term.Term a b)]) ->
                                    [(Term.Term a b, Term.Term a b)] ->
                                      Sum_Type.Sum (String -> String)
([((Term.Term a b, Term.Term a b), [(Term.Term a b, Term.Term a b)])],
  ((Term.Term a b, Term.Term a b), [(Term.Term a b, Term.Term a b)]));
check_left_inline_conds_rule r rho [] = Sum_Type.Inr (r, rho);
check_left_inline_conds_rule r rho (c : cs) =
  Error_Monad.catch_error
    (case rho of {
      (a, b) ->
        (case a of {
          (l, ra) ->
            (\ csa ->
              Error_Monad.bind
                (Check_Monad.check (Term_More.linear_term l)
                  (Shows_Literal.showsl_lit "non-linear lhs in rule"))
                (\ _ ->
                  (case c of {
                    (s, t) ->
                      Error_Monad.bind
                        (Check_Monad.check (Term.is_Var s)
                          (Shows_Literal.showsl_lit
                            "condition with non-variable lhs"))
                        (\ _ ->
                          let {
                            x = Term.the_Var s;
                          } in Error_Monad.bind
                                 (Error_Monad.catch_error
                                   (Inline_Conditions_Impl.find_index
                                     Arith.zero_nat c csa)
                                   (\ xa ->
                                     Sum_Type.Inl
                                       (case xa of {
 () -> Shows_Literal.showsl_lit "condition does not occur in rule";
                                       })))
                                 (\ i ->
                                   Error_Monad.bind
                                     (Check_Monad.check
                                       (not (Term_Impl.contains_var_term x t))
                                       (Shows_Literal.showsl_lit
 "occurs check failed"))
                                     (\ _ ->
                                       Error_Monad.bind
 (Check_Monad.check (not (Term_Impl.contains_var_term x ra))
   (Shows_Literal.showsl_lit "left-inlining not allowed in rhs of rule"))
 (\ _ ->
   Error_Monad.bind
     (Check_Monad.check
       (not (Set.member x
              (Set.sup_set
                (Complete_Lattices.sup_set
                  (Set.image Term.vars_term
                    (Set.image fst (List.set (List.take i csa)))))
                (Complete_Lattices.sup_set
                  (Set.image Term.vars_term
                    (Set.image fst
                      (List.set (List.drop (Arith.suc i) csa))))))))
       (Shows_Literal.showsl_lit
         "left-inlining not allowed in lhss of conditions"))
     (\ _ ->
       check_left_inline_conds_rule
         (Left_Inline_Conditions.left_inline i rho : List.removeAll rho r)
         (Left_Inline_Conditions.left_inline i rho)
         (map (\ (u, v) -> (u, Term.eval_term Term.Fun v (Term.subst x t)))
           cs))))));
                  })));
        })
          b;
    })
    (\ x ->
      Sum_Type.Inl
        (((((Shows_Literal.showsl_lit "error while left-inlining condition " .
              Conditional_Rewriting_Impl.showsl_eq c) .
             Shows_Literal.showsl_lit " of rule ") .
            Conditional_Rewriting_Impl.showsl_crule rho) .
           Shows_Literal.showsl_literal "\n") .
          x));

check_left_inline_conds_ctrs ::
  forall a b.
    (Compare.Compare a, Eq a, Shows_Literal.Showl a, Cardinality.Finite_UNIV b,
      Collection_Enum.Cenum b, Collection_Eq.Ceq b,
      Collection_Order.Cproper_interval b, Compare.Compare b, Eq b,
      Set_Impl.Set_impl b,
      Shows_Literal.Showl b) => [((Term.Term a b, Term.Term a b),
                                   [(Term.Term a b, Term.Term a b)])] ->
                                  [(((Term.Term a b, Term.Term a b),
                                      [(Term.Term a b, Term.Term a b)]),
                                     [(Term.Term a b, Term.Term a b)])] ->
                                    Sum_Type.Sum (String -> String)
                                      [((Term.Term a b, Term.Term a b),
 [(Term.Term a b, Term.Term a b)])];
check_left_inline_conds_ctrs r [] = Sum_Type.Inr r;
check_left_inline_conds_ctrs ra ((r, cs) : rcs) =
  Error_Monad.catch_error
    (Error_Monad.bind
      (Check_Monad.check (List.member ra r)
        (Conditional_Rewriting_Impl.showsl_crule r .
          Shows_Literal.showsl_lit " does not occur in the input CTRS"))
      (\ _ ->
        Error_Monad.bind (check_left_inline_conds_rule ra r cs)
          (\ (rb, raa) ->
            check_left_inline_conds_ctrs (raa : List.removeAll raa rb) rcs)))
    (\ x ->
      Sum_Type.Inl
        (Shows_Literal.showsl_lit "error while left-inlining conditions\n" .
          x));

check_left_inline_conds ::
  forall a b.
    (Compare.Compare a, Eq a, Shows_Literal.Showl a, Cardinality.Finite_UNIV b,
      Collection_Enum.Cenum b, Collection_Eq.Ceq b,
      Collection_Order.Cproper_interval b, Compare.Compare b, Eq b,
      Set_Impl.Set_impl b,
      Shows_Literal.Showl b) => [((Term.Term a b, Term.Term a b),
                                   [(Term.Term a b, Term.Term a b)])] ->
                                  [((Term.Term a b, Term.Term a b),
                                     [(Term.Term a b, Term.Term a b)])] ->
                                    [(((Term.Term a b, Term.Term a b),
[(Term.Term a b, Term.Term a b)]),
                                       [(Term.Term a b, Term.Term a b)])] ->
                                      Sum_Type.Sum (String -> String) ();
check_left_inline_conds ra r rcs =
  Error_Monad.bind (check_left_inline_conds_ctrs ra rcs)
    (\ raa ->
      Error_Monad.catch_error (Check_Monad.check_same_set r raa)
        (\ _ ->
          Sum_Type.Inl
            ((((Shows_Literal.showsl_lit "error while left-inlining:" .
                 Shows_Literal.showsl_lit "\ninternally computed CTRS\n") .
                Conditional_Rewriting_Impl.showsl_ctrs raa) .
               Shows_Literal.showsl_lit "\nbut certificate contains CTRS\n") .
              Conditional_Rewriting_Impl.showsl_ctrs r)));

}
