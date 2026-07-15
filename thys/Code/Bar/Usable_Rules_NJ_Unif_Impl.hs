{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Usable_Rules_NJ_Unif_Impl(check_usable_rules_unif) where {

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
import qualified Error_Monad;
import qualified Check_Monad;
import qualified Tcap;
import qualified HOL;
import qualified Sum_Type;
import qualified Compare;
import qualified Term_Rewriting;
import qualified Mapping;
import qualified Shows_Literal;
import qualified Arith;

check_contains_U0 ::
  forall a.
    (Compare.Compare a, Eq a,
      Shows_Literal.Showl a) => [(Term_Rewriting.Term a [Arith.Char],
                                   Term_Rewriting.Term a [Arith.Char])] ->
                                  Arith.Set
                                    (Term_Rewriting.Term a [Arith.Char],
                                      Term_Rewriting.Term a [Arith.Char]) ->
                                    Term_Rewriting.Term a [Arith.Char] ->
                                      Sum_Type.Sum (String -> String) ();
check_contains_U0 r u s =
  Error_Monad.catch_error
    (Error_Monad.forallM
      (\ fts ->
        (case fts of {
          Term_Rewriting.Var _ -> Sum_Type.Inr ();
          Term_Rewriting.Fun f ts ->
            let {
              tcapb = Term_Rewriting.GCFun f (map (Tcap.tcap u) ts);
            } in Error_Monad.catch_error
                   (Error_Monad.forallM
                     (\ lr ->
                       (case Term_Rewriting.gc_matcher tcapb (fst lr) of {
                         Nothing -> Sum_Type.Inr ();
                         Just sigma ->
                           let {
                             irule =
                               (Term_Rewriting.eval_term Term_Rewriting.Fun
                                  (fst lr) sigma,
                                 Term_Rewriting.eval_term Term_Rewriting.Fun
                                   (snd lr) sigma);
                           } in Check_Monad.check
                                  (case irule of {
                                    (a, b) -> Term_Rewriting.is_rstep u a b;
                                  })
                                  ((((((((((Shows_Literal.showsl_literal
      "When considering the subterm " .
     Term_Rewriting.showsl_terma fts) .
    Shows_Literal.showsl_literal "\nand the rule ") .
   Term_Rewriting.showsl_rule lr) .
  Shows_Literal.showsl_literal "\nthe capped subterm is ") .
 Term_Rewriting.showsl_gctxt tcapb) .
Shows_Literal.showsl_literal "\nleading to the mgu with the lhs: ") .
                                       Shows_Literal.showsl_list_prod
 (map (\ x -> (x, sigma x)) (Term_Rewriting.vars_term_list (fst lr)))) .
                                      Shows_Literal.showsl_literal
"\nThe instantiated rule ") .
                                     Term_Rewriting.showsl_rule irule) .
                                    Shows_Literal.showsl_literal
                                      "\ncannot be simulated by the given set of usable rules");
                       }))
                     r)
                   (\ x -> Sum_Type.Inl (snd x));
        }))
      (Term_Rewriting.supteq_list s))
    (\ x -> Sum_Type.Inl (snd x));

check_usable_instantiation ::
  forall a.
    (Compare.Compare a, Eq a,
      Shows_Literal.Showl a) => [(Term_Rewriting.Term a [Arith.Char],
                                   Term_Rewriting.Term a [Arith.Char])] ->
                                  [(Term_Rewriting.Term a [Arith.Char],
                                     Term_Rewriting.Term a [Arith.Char])] ->
                                    Term_Rewriting.Term a [Arith.Char] ->
                                      Sum_Type.Sum (String -> String) ();
check_usable_instantiation r u s =
  let {
    uu = Arith.set u;
  } in Error_Monad.bind
         (Error_Monad.catch_error (check_contains_U0 r uu s)
           (\ x ->
             Sum_Type.Inl
               (Shows_Literal.showsl_literal "U <= U0(R,s) required\n" . x)))
         (\ _ ->
           Error_Monad.catch_error
             (Error_Monad.forallM
               (\ ra ->
                 Error_Monad.catch_error (check_contains_U0 r uu ra)
                   (\ x ->
                     Sum_Type.Inl
                       (((Shows_Literal.showsl_literal
                            "U <= U0(R,r) for rhs r = " .
                           Term_Rewriting.showsl_terma ra) .
                          Shows_Literal.showsl_literal " required\n") .
                         x)))
               (map snd u))
             (\ x -> Sum_Type.Inl (snd x)));

check_usable_rules_unif ::
  forall a.
    (Compare.Compare a, Eq a,
      Shows_Literal.Showl a) => [(Term_Rewriting.Term a [Arith.Char],
                                   Term_Rewriting.Term a [Arith.Char])] ->
                                  [(Term_Rewriting.Term a [Arith.Char],
                                     Term_Rewriting.Term a [Arith.Char])] ->
                                    Term_Rewriting.Term a [Arith.Char] ->
                                      Sum_Type.Sum (String -> String) ();
check_usable_rules_unif r u s =
  Error_Monad.catch_error
    (Error_Monad.bind
      (Check_Monad.check
        (Term_Rewriting.ground s ||
          all (\ l -> not (Term_Rewriting.is_Var l)) (map fst r))
        ((Shows_Literal.showsl_literal "since " .
           Term_Rewriting.showsl_terma s) .
          Shows_Literal.showsl_literal
            " is not ground, left-hand sides of R must not be variables"))
      (\ _ ->
        Error_Monad.bind (Term_Rewriting.check_varcond_subset u)
          (\ _ ->
            Error_Monad.catch_error (check_usable_instantiation r u s)
              (\ x ->
                Sum_Type.Inl
                  (Shows_Literal.showsl_literal
                     "closure properties of usable rules not satisfied\n" .
                    x)))))
    (\ x ->
      Sum_Type.Inl
        (((((((Shows_Literal.showsl_literal
                 "problem in checking validity of usable rules U =\n" .
                Term_Rewriting.showsl_trs u) .
               Shows_Literal.showsl_literal "\nfor term ") .
              Term_Rewriting.showsl_terma s) .
             Shows_Literal.showsl_literal "\nwrt TRS R =\n") .
            Term_Rewriting.showsl_trs r) .
           Shows_Literal.showsl_literal "\n") .
          x));

}
