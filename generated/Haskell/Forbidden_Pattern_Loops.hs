{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Forbidden_Pattern_Loops(n0, n0b, h_match_probs) where {

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
import qualified Context_Substitution;
import qualified Phantom_Type;
import qualified Compare;
import qualified HOL;
import qualified Position;
import qualified Arith;
import qualified Term_Rewriting;

n0 :: [Arith.Nat] -> [Arith.Nat] -> [Arith.Nat] -> Arith.Nat;
n0 p q oo =
  Arith.nat
    (Term_Rewriting.ceiling
      (Term_Rewriting.divide_rat
        (Arith.of_nat
          (Arith.minus_nat (Arith.size_list oo) (Arith.size_list q)))
        (Arith.of_nat (Arith.size_list p))));

n0b :: [Arith.Nat] -> [Arith.Nat] -> [Arith.Nat] -> Arith.Nat;
n0b p q oo =
  Arith.nat
    (Term_Rewriting.ceiling
      (Term_Rewriting.divide_rat
        (Arith.of_nat
          (Arith.minus_nat (Arith.suc (Arith.size_list oo))
            (Arith.size_list q)))
        (Arith.of_nat (Arith.size_list p))));

pos_dec ::
  [Arith.Nat] -> [Arith.Nat] -> [Arith.Nat] -> Maybe (Arith.Nat, [Arith.Nat]);
pos_dec p q oo =
  (if null p then (case Position.remove_suffix oo q of {
                    Nothing -> Nothing;
                    Just r -> Just (Arith.zero_nat, r);
                  })
    else let {
           n0 = Arith.nat
                  (Term_Rewriting.ceiling
                    (Term_Rewriting.divide_rat
                      (Arith.of_nat
                        (Arith.minus_nat (Arith.size_list oo)
                          (Arith.size_list q)))
                      (Arith.of_nat (Arith.size_list p))));
         } in (case Position.remove_suffix oo (Arith.power p n0 ++ q) of {
                Nothing -> Nothing;
                Just r -> Just (n0, r);
              }));

h_match_probs ::
  forall a b.
    (Compare.Compare a, Eq a, Compare.Compare b,
      Eq b) => (a -> Term_Rewriting.Term b a) ->
                 Term_Rewriting.Term b a ->
                   [Arith.Nat] ->
                     [Arith.Nat] ->
                       Term_Rewriting.Actxt b (Term_Rewriting.Term b a) ->
                         Term_Rewriting.Term b a ->
                           Arith.Set
                             (Term_Rewriting.Term b a, Term_Rewriting.Term b a);
h_match_probs mu l oo q c t =
  (case pos_dec (Term_Rewriting.hole_pos c) q oo of {
    Nothing ->
      Arith.set_empty
        (Phantom_Type.of_phantom
          (Arith.set_impl_prod ::
            Phantom_Type.Phantom
              (Term_Rewriting.Term b a, Term_Rewriting.Term b a)
              Arith.Set_impla));
    Just (n, o) ->
      Arith.insert
        (Term_Rewriting.subt_at (Context_Substitution.ctxt_subst c mu n t) o, l)
        (Arith.set_empty
          (Phantom_Type.of_phantom
            (Arith.set_impl_prod ::
              Phantom_Type.Phantom
                (Term_Rewriting.Term b a, Term_Rewriting.Term b a)
                Arith.Set_impla)));
  });

}
