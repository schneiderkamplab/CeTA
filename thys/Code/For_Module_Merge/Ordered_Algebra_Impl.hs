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
import qualified Term_More;
import qualified Set_Interval;
import qualified Error_Monad;
import qualified Check_Monad;
import qualified Sum_Type;
import qualified Set;
import qualified Collection_Order;
import qualified Collection_Enum;
import qualified Set_Impl;
import qualified Collection_Eq;
import qualified Map_Choice;
import qualified Product_Type;
import qualified Map;
import qualified List;
import qualified Term;
import qualified Shows_Literal;
import qualified Arith;

e :: forall a b.
       (Eq a, Shows_Literal.Showl a,
         Shows_Literal.Showl b) => [((a, Arith.Nat), Term.Term b Arith.Nat)] ->
                                     (Arith.Nat -> b) ->
                                       a -> Arith.Nat -> Term.Term b Arith.Nat;
e alist default_fun =
  Product_Type.curry
    (Map_Choice.fun_of_map_fun (Map.map_of alist)
      (\ (_, n) ->
        Term.Fun (default_fun n) (map Term.Var (List.upt Arith.zero_nat n))));

check_encoding ::
  forall a b.
    (Shows_Literal.Showl a,
      Shows_Literal.Showl b) => [((a, Arith.Nat), Term.Term b Arith.Nat)] ->
                                  Sum_Type.Sum (String -> String) ();
check_encoding alist =
  Error_Monad.catch_error
    (Error_Monad.forallM
      (\ (a, b) ->
        (case a of {
          (f, n) ->
            (\ t ->
              Check_Monad.check
                (Set.less_eq_set (Term.vars_term t)
                  (Set_Interval.atLeastLessThan Arith.zero_nat n))
                ((((Shows_Literal.showsl_lit "interpretation of " .
                     Shows_Literal.showsl f) .
                    Shows_Literal.showsl_lit " arity ") .
                   Shows_Literal.showsl_nat n) .
                  Shows_Literal.showsl_lit " has extra parameter"));
        })
          b)
      alist)
    (\ x -> Sum_Type.Inl (snd x));

showsl_encoding ::
  forall a b.
    (Shows_Literal.Showl a,
      Shows_Literal.Showl b) => [((a, Arith.Nat), Term.Term b Arith.Nat)] ->
                                  String -> String;
showsl_encoding alist =
  Shows_Literal.showsl_sep
    (\ (a, b) ->
      (case a of {
        (f, n) ->
          (\ e ->
            (Shows_Literal.showsl f .
              Shows_Literal.showsl_list_gen
                (\ i ->
                  Shows_Literal.showsl_lit "x" . Shows_Literal.showsl_nat i)
                " = " "(" "," ") = " (List.upt Arith.zero_nat n)) .
              Term_More.showsl_term Shows_Literal.showsl
                (\ i ->
                  Shows_Literal.showsl_lit "x" . Shows_Literal.showsl_nat i)
                e);
      })
        b)
    (Shows_Literal.showsl_literal "\n") alist;

}
