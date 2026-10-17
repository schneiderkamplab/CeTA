{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module AAECC_Innermost_Switch(aaecc_signature_separated_impl) where {

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
import qualified HOL;
import qualified Term_Rewriting;
import qualified Arith;

aaecc_signature_impl ::
  forall a b.
    (Eq a) => [a] ->
                [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
                  [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
                    [(a, Arith.Nat)];
aaecc_signature_impl fs r1 r2 =
  filter (\ (f, _) -> Arith.membera fs f)
    (Term_Rewriting.funas_trs_list (r1 ++ r2));

aaecc_signature_separated_impl ::
  forall a b.
    (Arith.Ceq a, Arith.Ccompare a, Eq a,
      Arith.Set_impl a) => [a] ->
                             [(Term_Rewriting.Term a b,
                                Term_Rewriting.Term a b)] ->
                               [(Term_Rewriting.Term a b,
                                  Term_Rewriting.Term a b)] ->
                                 Bool;
aaecc_signature_separated_impl fs r1 r2 =
  let {
    f = Arith.set (aaecc_signature_impl fs r1 r2);
  } in all (\ fa -> not (Arith.member fa f))
         (Term_Rewriting.funas_trs_list r1) &&
         all (\ (l, r) ->
               not (Term_Rewriting.is_Var r) &&
                 Arith.member (Term_Rewriting.root l) (Arith.image Just f) &&
                   Arith.member (Term_Rewriting.root r) (Arith.image Just f) &&
                     all (\ fa -> not (Arith.member fa f))
                       (Term_Rewriting.funas_args_term_list l) &&
                       all (\ fa -> not (Arith.member fa f))
                         (Term_Rewriting.funas_args_term_list r))
           r2;

}
