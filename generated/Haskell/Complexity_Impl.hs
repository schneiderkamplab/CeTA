{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Complexity_Impl(check_terms_of_nat) where {

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
import qualified Check_Monad;
import qualified Arith;
import qualified Error_Monad;
import qualified Sum_Type;
import qualified Term_Rewriting;

check_terms_of_main ::
  forall a b.
    (Eq a,
      Term_Rewriting.Showl a) => Term_Rewriting.Complexity_measure a b ->
                                   Term_Rewriting.Complexity_measure a b ->
                                     Sum_Type.Sum (String -> String) ();
check_terms_of_main (Term_Rewriting.Derivational_Complexity f)
  (Term_Rewriting.Derivational_Complexity g) =
  Error_Monad.catch_error (Check_Monad.check_subseteq f g)
    (\ x ->
      Sum_Type.Inl
        (Term_Rewriting.showsl_lit "consider of symbol " .
          Term_Rewriting.showsl_prod x));
check_terms_of_main (Term_Rewriting.Runtime_Complexity f h)
  (Term_Rewriting.Derivational_Complexity g) =
  Error_Monad.catch_error (Check_Monad.check_subseteq (f ++ h) g)
    (\ x ->
      Sum_Type.Inl
        (Term_Rewriting.showsl_lit "consider of symbol " .
          Term_Rewriting.showsl_prod x));
check_terms_of_main (Term_Rewriting.Runtime_Complexity f h)
  (Term_Rewriting.Runtime_Complexity f1 h1) =
  Error_Monad.bind
    (Error_Monad.catch_error (Check_Monad.check_subseteq f f1)
      (\ x ->
        Sum_Type.Inl
          (Term_Rewriting.showsl_lit "consider symbol " .
            Term_Rewriting.showsl_prod x)))
    (\ _ ->
      Error_Monad.catch_error (Check_Monad.check_subseteq h h1)
        (\ x ->
          Sum_Type.Inl
            (Term_Rewriting.showsl_lit "consider symbol " .
              Term_Rewriting.showsl_prod x)));
check_terms_of_main (Term_Rewriting.Derivational_Complexity g)
  (Term_Rewriting.Runtime_Complexity f1 h1) =
  Sum_Type.Inl
    (Term_Rewriting.showsl_lit
      "mixing runtime complexity and derivational complexity");

check_terms_of_nat ::
  forall a b.
    (Eq a,
      Term_Rewriting.Showl a) => Term_Rewriting.Complexity_measure a b ->
                                   Term_Rewriting.Complexity_measure a b ->
                                     Sum_Type.Sum (String -> String) ();
check_terms_of_nat cm1 cm2 =
  Error_Monad.catch_error (check_terms_of_main cm1 cm2)
    (\ x ->
      Sum_Type.Inl
        (Term_Rewriting.showsl_lit "error comparing start terms\n" . x));

}
