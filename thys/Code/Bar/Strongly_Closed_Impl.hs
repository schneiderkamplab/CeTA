{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Strongly_Closed_Impl(check_strongly_closed) where {

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
import qualified Check_Monad;
import qualified Error_Monad;
import qualified Renaming2;
import qualified Sum_Type;
import qualified Mapping;
import qualified Shows_Literal;
import qualified Arith;
import qualified Fresh;
import qualified Term_Rewriting;

check_strongly_closed ::
  forall a b.
    (Arith.Ceq a, Arith.Ccompare a, Fresh.Infinite a, Eq a,
      Mapping.Mapping_impl a, Arith.Set_impl a, Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => Renaming2.Renaming2 a ->
                                  [(Term_Rewriting.Term b a,
                                     Term_Rewriting.Term b a)] ->
                                    Arith.Nat ->
                                      Sum_Type.Sum (String -> String) ();
check_strongly_closed ren r n =
  Error_Monad.catch_error
    (Error_Monad.bind (Term_Rewriting.check_linear_trs r)
      (\ _ ->
        Error_Monad.catch_error
          (Error_Monad.forallM
            (\ (_, (s, t)) ->
              Check_Monad.check
                (not (Arith.is_none
                       (Arith.find
                         (Arith.membera (Term_Rewriting.reachable_terms r s n))
                         (Term_Rewriting.reachable_terms r t
                           (Arith.suc Arith.zero_nat)))) &&
                  not (Arith.is_none
                        (Arith.find
                          (Arith.membera (Term_Rewriting.reachable_terms r t n))
                          (Term_Rewriting.reachable_terms r s
                            (Arith.suc Arith.zero_nat)))))
                ((((((Shows_Literal.showsl_lit "the critical pair " .
                       Term_Rewriting.showsl_terma s) .
                      Shows_Literal.showsl_lit " <- . -> ") .
                     Term_Rewriting.showsl_terma t) .
                    Shows_Literal.showsl_lit
                      " is not strongly closed within ") .
                   Shows_Literal.showsl_nat n) .
                  Shows_Literal.showsl_lit " steps."))
            (Critical_Pairs_Impl.critical_pairs_impl ren r r))
          (\ x -> Sum_Type.Inl (snd x))))
    (\ x ->
      Sum_Type.Inl
        ((x . Shows_Literal.showsl_lit
                "\nhence the following TRS is not strongly closed\n") .
          Term_Rewriting.showsl_trs r));

}
