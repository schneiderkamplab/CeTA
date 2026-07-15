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
import qualified Product_Type;
import qualified Term_More;
import qualified Subterm_and_Context;
import qualified Phantom_Type;
import qualified Set_Impl;
import qualified Term;
import qualified Set;
import qualified Compare;
import qualified Collection_Order;
import qualified Collection_Eq;
import qualified Container_Setup;
import qualified Option;
import qualified HOL;
import qualified Position;
import qualified List;
import qualified Archimedean_Field;
import qualified Arith;
import qualified Rat;

n0 :: [Arith.Nat] -> [Arith.Nat] -> [Arith.Nat] -> Arith.Nat;
n0 p q oo =
  Arith.nat
    (Archimedean_Field.ceiling
      (Rat.divide_rat
        (Arith.of_nat (Arith.minus_nat (List.size_list oo) (List.size_list q)))
        (Arith.of_nat (List.size_list p))));

n0b :: [Arith.Nat] -> [Arith.Nat] -> [Arith.Nat] -> Arith.Nat;
n0b p q oo =
  Arith.nat
    (Archimedean_Field.ceiling
      (Rat.divide_rat
        (Arith.of_nat
          (Arith.minus_nat (Arith.suc (List.size_list oo)) (List.size_list q)))
        (Arith.of_nat (List.size_list p))));

pos_dec ::
  [Arith.Nat] -> [Arith.Nat] -> [Arith.Nat] -> Maybe (Arith.Nat, [Arith.Nat]);
pos_dec p q oo =
  (if null p then (case Position.remove_suffix oo q of {
                    Nothing -> Nothing;
                    Just r -> Just (Arith.zero_nat, r);
                  })
    else let {
           n0 = Arith.nat
                  (Archimedean_Field.ceiling
                    (Rat.divide_rat
                      (Arith.of_nat
                        (Arith.minus_nat (List.size_list oo)
                          (List.size_list q)))
                      (Arith.of_nat (List.size_list p))));
         } in (case Position.remove_suffix oo (Arith.power p n0 ++ q) of {
                Nothing -> Nothing;
                Just r -> Just (n0, r);
              }));

h_match_probs ::
  forall a b.
    (Compare.Compare a, Eq a, Compare.Compare b,
      Eq b) => (a -> Term.Term b a) ->
                 Term.Term b a ->
                   [Arith.Nat] ->
                     [Arith.Nat] ->
                       Subterm_and_Context.Actxt b (Term.Term b a) ->
                         Term.Term b a ->
                           Set.Set (Term.Term b a, Term.Term b a);
h_match_probs mu l oo q c t =
  (case pos_dec (Term_More.hole_pos c) q oo of {
    Nothing ->
      Set_Impl.set_empty
        (Phantom_Type.of_phantom
          (Set_Impl.set_impl_prod ::
            Phantom_Type.Phantom (Term.Term b a, Term.Term b a)
              Set_Impl.Set_impla));
    Just (n, o) ->
      Set.insert
        (Term_More.subt_at (Context_Substitution.ctxt_subst c mu n t) o, l)
        (Set_Impl.set_empty
          (Phantom_Type.of_phantom
            (Set_Impl.set_impl_prod ::
              Phantom_Type.Phantom (Term.Term b a, Term.Term b a)
                Set_Impl.Set_impla)));
  });

}
