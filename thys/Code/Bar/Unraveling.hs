{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Unraveling(lhs_n, rhs_n) where {

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
import qualified Term_Rewriting;
import qualified Arith;

lhs_n ::
  forall a b.
    (((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
       [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]) ->
      Arith.Nat -> Term_Rewriting.Actxt a (Term_Rewriting.Term a b)) ->
      ((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
        [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]) ->
        Arith.Nat -> Term_Rewriting.Term a b;
lhs_n u (lr, cs) n =
  (if Arith.equal_nat n Arith.zero_nat then fst lr
    else Term_Rewriting.intp_actxt Term_Rewriting.Fun
           (u (lr, cs) (Arith.minus_nat n Arith.one_nat))
           (snd (Arith.nth cs (Arith.minus_nat n Arith.one_nat))));

rhs_n ::
  forall a b.
    (((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
       [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]) ->
      Arith.Nat -> Term_Rewriting.Actxt a (Term_Rewriting.Term a b)) ->
      ((Term_Rewriting.Term a b, Term_Rewriting.Term a b),
        [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)]) ->
        Arith.Nat -> Term_Rewriting.Term a b;
rhs_n u (lr, cs) n =
  (if Arith.less_nat n (Arith.size_list cs)
    then Term_Rewriting.intp_actxt Term_Rewriting.Fun (u (lr, cs) n)
           (fst (Arith.nth cs n))
    else snd lr);

}
