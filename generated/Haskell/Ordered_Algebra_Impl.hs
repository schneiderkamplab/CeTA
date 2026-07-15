{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Ordered_Algebra_Impl(e, check_encoding, showsl_encoding) where {

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
import qualified Set_Interval;
import qualified Error_Monad;
import qualified Check_Monad;
import qualified Sum_Type;
import qualified Map_Choice;
import qualified Map;
import qualified Term_Rewriting;
import qualified Arith;

e :: forall a b.
       (Eq a, Term_Rewriting.Showl a,
         Term_Rewriting.Showl b) => [((a, Arith.Nat),
                                       Term_Rewriting.Term b Arith.Nat)] ->
                                      (Arith.Nat -> b) ->
a -> Arith.Nat -> Term_Rewriting.Term b Arith.Nat;
e alist default_fun =
  Arith.curry
    (Map_Choice.fun_of_map_fun (Map.map_of alist)
      (\ (_, n) ->
        Term_Rewriting.Fun (default_fun n)
          (map Term_Rewriting.Var (Arith.upt Arith.zero_nat n))));

check_encoding ::
  forall a b.
    (Term_Rewriting.Showl a,
      Term_Rewriting.Showl b) => [((a, Arith.Nat),
                                    Term_Rewriting.Term b Arith.Nat)] ->
                                   Sum_Type.Sum (String -> String) ();
check_encoding alist =
  Error_Monad.catch_error
    (Error_Monad.forallM
      (\ (a, b) ->
        (case a of {
          (f, n) ->
            (\ t ->
              Check_Monad.check
                (Arith.less_eq_set (Term_Rewriting.vars_term t)
                  (Set_Interval.atLeastLessThan Arith.zero_nat n))
                ((((Term_Rewriting.showsl_lit "interpretation of " .
                     Term_Rewriting.showsl f) .
                    Term_Rewriting.showsl_lit " arity ") .
                   Term_Rewriting.showsl_nat n) .
                  Term_Rewriting.showsl_lit " has extra parameter"));
        })
          b)
      alist)
    (\ x -> Sum_Type.Inl (snd x));

showsl_encoding ::
  forall a b.
    (Term_Rewriting.Showl a,
      Term_Rewriting.Showl b) => [((a, Arith.Nat),
                                    Term_Rewriting.Term b Arith.Nat)] ->
                                   String -> String;
showsl_encoding alist =
  Term_Rewriting.showsl_sep
    (\ (a, b) ->
      (case a of {
        (f, n) ->
          (\ e ->
            (Term_Rewriting.showsl f .
              Term_Rewriting.showsl_list_gen
                (\ i ->
                  Term_Rewriting.showsl_lit "x" . Term_Rewriting.showsl_nat i)
                " = " "(" "," ") = " (Arith.upt Arith.zero_nat n)) .
              Term_Rewriting.showsl_term Term_Rewriting.showsl
                (\ i ->
                  Term_Rewriting.showsl_lit "x" . Term_Rewriting.showsl_nat i)
                e);
      })
        b)
    (Term_Rewriting.showsl_literal "\n") alist;

}
