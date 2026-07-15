{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Development_Closed_Impl(check_development_closed,
                           check_development_closed_comm)
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
import qualified Critical_Pairs_Impl;
import qualified Rewrite_Relations_Impl;
import qualified Check_Joins;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified Renaming2;
import qualified Sum_Type;
import qualified Term_Rewriting;
import qualified Mapping;
import qualified Arith;
import qualified Compare;
import qualified Fresh;
import qualified Shows_Literal;

check_development_closed ::
  forall a b.
    (Arith.Ceq a, Arith.Ccompare a, Compare.Compare a, Fresh.Infinite a, Eq a,
      Mapping.Mapping_impl a, Arith.Set_impl a, Shows_Literal.Showl a,
      Compare.Compare b, Eq b,
      Shows_Literal.Showl b) => Renaming2.Renaming2 a ->
                                  [(Term_Rewriting.Term b a,
                                     Term_Rewriting.Term b a)] ->
                                    Maybe Arith.Nat ->
                                      Sum_Type.Sum (String -> String) ();
check_development_closed ren r n =
  Error_Monad.catch_error
    (Error_Monad.bind (Term_Rewriting.check_wf_trs r)
      (\ _ ->
        Error_Monad.bind (Term_Rewriting.check_left_linear_trs r)
          (\ _ ->
            Error_Monad.catch_error
              (Error_Monad.forallM
                (\ a ->
                  (case a of {
                    (True, (s, t)) ->
                      Check_Monad.check (Check_Joins.is_mstep_join r r n s t)
                        ((((((Shows_Literal.showsl_lit "the critical pair " .
                               Term_Rewriting.showsl_terma s) .
                              Shows_Literal.showsl_lit " <- . -> ") .
                             Term_Rewriting.showsl_terma t) .
                            Shows_Literal.showsl_lit
                              " is not almost development closed within ") .
                           Shows_Literal.showsl_option n) .
                          Shows_Literal.showsl_lit " steps.");
                    (False, (s, t)) ->
                      Check_Monad.check (Rewrite_Relations_Impl.is_mstep r s t)
                        (((((Shows_Literal.showsl_lit
                               "the inner critical pair " .
                              Term_Rewriting.showsl_terma s) .
                             Shows_Literal.showsl_lit " S<- . ->R ") .
                            Term_Rewriting.showsl_terma t) .
                           Shows_Literal.showsl_lit
                             " is not closed with a multi-step over R") .
                          Shows_Literal.showsl_option n);
                  }))
                (Critical_Pairs_Impl.critical_pairs_impl ren r r))
              (\ x -> Sum_Type.Inl (snd x)))))
    (\ x ->
      Sum_Type.Inl
        ((x . Shows_Literal.showsl_lit
                "\nhence the following TRS is not development closed\n") .
          Term_Rewriting.showsl_trs r));

check_development_closed_comm ::
  forall a b.
    (Arith.Ceq a, Arith.Ccompare a, Compare.Compare a, Fresh.Infinite a, Eq a,
      Mapping.Mapping_impl a, Arith.Set_impl a, Shows_Literal.Showl a,
      Compare.Compare b, Eq b,
      Shows_Literal.Showl b) => Renaming2.Renaming2 a ->
                                  [(Term_Rewriting.Term b a,
                                     Term_Rewriting.Term b a)] ->
                                    [(Term_Rewriting.Term b a,
                                       Term_Rewriting.Term b a)] ->
                                      Maybe Arith.Nat ->
Sum_Type.Sum (String -> String) ();
check_development_closed_comm ren r s n =
  Error_Monad.catch_error
    (Error_Monad.bind (Term_Rewriting.check_wf_trs r)
      (\ _ ->
        Error_Monad.bind (Term_Rewriting.check_wf_trs s)
          (\ _ ->
            Error_Monad.bind (Term_Rewriting.check_left_linear_trs r)
              (\ _ ->
                Error_Monad.bind (Term_Rewriting.check_left_linear_trs s)
                  (\ _ ->
                    Error_Monad.bind
                      (Error_Monad.catch_error
                        (Error_Monad.forallM
                          (\ (_, (sa, t)) ->
                            Check_Monad.check
                              (Check_Joins.is_mstep_join s r n sa t)
                              ((((((Shows_Literal.showsl_lit
                                      "the critical pair " .
                                     Term_Rewriting.showsl_terma sa) .
                                    Shows_Literal.showsl_lit " R<- . ->S ") .
                                   Term_Rewriting.showsl_terma t) .
                                  Shows_Literal.showsl_lit
                                    " is not almost development closed within ") .
                                 Shows_Literal.showsl_option n) .
                                Shows_Literal.showsl_lit " steps."))
                          (Critical_Pairs_Impl.critical_pairs_impl ren s r))
                        (\ x -> Sum_Type.Inl (snd x)))
                      (\ _ ->
                        Error_Monad.catch_error
                          (Error_Monad.forallM
                            (\ (b, (sa, t)) ->
                              Check_Monad.check
                                (b || Rewrite_Relations_Impl.is_mstep r sa t)
                                (((((Shows_Literal.showsl_lit
                                       "the inner critical pair " .
                                      Term_Rewriting.showsl_terma sa) .
                                     Shows_Literal.showsl_lit " S<- . ->R ") .
                                    Term_Rewriting.showsl_terma t) .
                                   Shows_Literal.showsl_lit
                                     " is not closed with multi-step over R") .
                                  Shows_Literal.showsl_option n))
                            (Critical_Pairs_Impl.critical_pairs_impl ren r s))
                          (\ x -> Sum_Type.Inl (snd x))))))))
    (\ x ->
      Sum_Type.Inl
        ((((x . Shows_Literal.showsl_lit
                  "\nhence the almost development closed check for the following TRSs could not be proven\nR: ") .
            Term_Rewriting.showsl_trs r) .
           Shows_Literal.showsl_lit "\n\nS: ") .
          Term_Rewriting.showsl_trs s));

}
