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
import qualified List;
import qualified Subterm_and_Context;
import qualified Term;
import qualified Arith;

lhs_n ::
  forall a b.
    (((Term.Term a b, Term.Term a b), [(Term.Term a b, Term.Term a b)]) ->
      Arith.Nat -> Subterm_and_Context.Actxt a (Term.Term a b)) ->
      ((Term.Term a b, Term.Term a b), [(Term.Term a b, Term.Term a b)]) ->
        Arith.Nat -> Term.Term a b;
lhs_n u (lr, cs) n =
  (if Arith.equal_nat n Arith.zero_nat then fst lr
    else Subterm_and_Context.intp_actxt Term.Fun
           (u (lr, cs) (Arith.minus_nat n Arith.one_nat))
           (snd (List.nth cs (Arith.minus_nat n Arith.one_nat))));

rhs_n ::
  forall a b.
    (((Term.Term a b, Term.Term a b), [(Term.Term a b, Term.Term a b)]) ->
      Arith.Nat -> Subterm_and_Context.Actxt a (Term.Term a b)) ->
      ((Term.Term a b, Term.Term a b), [(Term.Term a b, Term.Term a b)]) ->
        Arith.Nat -> Term.Term a b;
rhs_n u (lr, cs) n =
  (if Arith.less_nat n (List.size_list cs)
    then Subterm_and_Context.intp_actxt Term.Fun (u (lr, cs) n)
           (fst (List.nth cs n))
    else snd lr);

}
