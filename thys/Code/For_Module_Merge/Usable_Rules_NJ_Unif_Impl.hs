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
import qualified List;
import qualified Set_Impl;
import qualified Collection_Eq;
import qualified Container_Setup;
import qualified Ground_Context_Impl;
import qualified Product_Type;
import qualified Option;
import qualified Term_Impl;
import qualified Error_Monad;
import qualified Trs_Impl;
import qualified Check_Monad;
import qualified Tcap;
import qualified HOL;
import qualified Ground_Context;
import qualified Sum_Type;
import qualified Term;
import qualified Set;
import qualified Compare;
import qualified Str;
import qualified Term_More;
import qualified Mapping_Impl;
import qualified Collection_Order;
import qualified Shows_Literal;
import qualified Compare_Instances;

check_contains_U0 ::
  forall a.
    (Compare.Compare a, Eq a,
      Shows_Literal.Showl a) => [(Term.Term a [Str.Char],
                                   Term.Term a [Str.Char])] ->
                                  Set.Set
                                    (Term.Term a [Str.Char],
                                      Term.Term a [Str.Char]) ->
                                    Term.Term a [Str.Char] ->
                                      Sum_Type.Sum (String -> String) ();
check_contains_U0 r u s =
  Error_Monad.catch_error
    (Error_Monad.forallM
      (\ fts ->
        (case fts of {
          Term.Var _ -> Sum_Type.Inr ();
          Term.Fun f ts ->
            let {
              tcapb = Ground_Context.GCFun f (map (Tcap.tcap u) ts);
            } in Error_Monad.catch_error
                   (Error_Monad.forallM
                     (\ lr ->
                       (case Ground_Context_Impl.gc_matcher tcapb (fst lr) of {
                         Nothing -> Sum_Type.Inr ();
                         Just sigma ->
                           let {
                             irule =
                               (Term.eval_term Term.Fun (fst lr) sigma,
                                 Term.eval_term Term.Fun (snd lr) sigma);
                           } in Check_Monad.check
                                  (case irule of {
                                    (a, b) -> Trs_Impl.is_rstep u a b;
                                  })
                                  ((((((((((Shows_Literal.showsl_literal
      "When considering the subterm " .
     Term_More.showsl_terma fts) .
    Shows_Literal.showsl_literal "\nand the rule ") .
   Trs_Impl.showsl_rule lr) .
  Shows_Literal.showsl_literal "\nthe capped subterm is ") .
 Ground_Context_Impl.showsl_gctxt tcapb) .
Shows_Literal.showsl_literal "\nleading to the mgu with the lhs: ") .
                                       Shows_Literal.showsl_list_prod
 (map (\ x -> (x, sigma x)) (Term_More.vars_term_list (fst lr)))) .
                                      Shows_Literal.showsl_literal
"\nThe instantiated rule ") .
                                     Trs_Impl.showsl_rule irule) .
                                    Shows_Literal.showsl_literal
                                      "\ncannot be simulated by the given set of usable rules");
                       }))
                     r)
                   (\ x -> Sum_Type.Inl (snd x));
        }))
      (Term_Impl.supteq_list s))
    (\ x -> Sum_Type.Inl (snd x));

check_usable_instantiation ::
  forall a.
    (Compare.Compare a, Eq a,
      Shows_Literal.Showl a) => [(Term.Term a [Str.Char],
                                   Term.Term a [Str.Char])] ->
                                  [(Term.Term a [Str.Char],
                                     Term.Term a [Str.Char])] ->
                                    Term.Term a [Str.Char] ->
                                      Sum_Type.Sum (String -> String) ();
check_usable_instantiation r u s =
  let {
    uu = List.set u;
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
                           Term_More.showsl_terma ra) .
                          Shows_Literal.showsl_literal " required\n") .
                         x)))
               (map snd u))
             (\ x -> Sum_Type.Inl (snd x)));

check_usable_rules_unif ::
  forall a.
    (Compare.Compare a, Eq a,
      Shows_Literal.Showl a) => [(Term.Term a [Str.Char],
                                   Term.Term a [Str.Char])] ->
                                  [(Term.Term a [Str.Char],
                                     Term.Term a [Str.Char])] ->
                                    Term.Term a [Str.Char] ->
                                      Sum_Type.Sum (String -> String) ();
check_usable_rules_unif r u s =
  Error_Monad.catch_error
    (Error_Monad.bind
      (Check_Monad.check
        (Term.ground s || all (\ l -> not (Term.is_Var l)) (map fst r))
        ((Shows_Literal.showsl_literal "since " . Term_More.showsl_terma s) .
          Shows_Literal.showsl_literal
            " is not ground, left-hand sides of R must not be variables"))
      (\ _ ->
        Error_Monad.bind (Trs_Impl.check_varcond_subset u)
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
                Trs_Impl.showsl_trs u) .
               Shows_Literal.showsl_literal "\nfor term ") .
              Term_More.showsl_terma s) .
             Shows_Literal.showsl_literal "\nwrt TRS R =\n") .
            Trs_Impl.showsl_trs r) .
           Shows_Literal.showsl_literal "\n") .
          x));

}
