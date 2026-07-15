{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Icap(class_to_term, mgu_class) where {

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
import qualified Sum_Type;
import qualified Term_Rewriting;
import qualified Arith;

class_to_term_intern ::
  forall a b.
    (Arith.Nat -> a) ->
      Arith.Nat ->
        Term_Rewriting.Term b (Sum_Type.Sum () a) ->
          (Arith.Nat, Term_Rewriting.Term b a);
class_to_term_intern iv i (Term_Rewriting.Fun f ts) =
  (case Arith.foldr (\ t (j, ss) -> (case class_to_term_intern iv j t of {
                                      (k, s) -> (k, s : ss);
                                    }))
          ts (i, [])
    of {
    (k, ss) -> (k, Term_Rewriting.Fun f ss);
  });
class_to_term_intern iv i (Term_Rewriting.Var (Sum_Type.Inl uu)) =
  (Arith.plus_nat i Arith.one_nat, Term_Rewriting.Var (iv i));
class_to_term_intern iv i (Term_Rewriting.Var (Sum_Type.Inr x)) =
  (i, Term_Rewriting.Var x);

class_to_term ::
  forall a.
    Arith.Char ->
      Term_Rewriting.Term a (Sum_Type.Sum () [Arith.Char]) ->
        Term_Rewriting.Term a [Arith.Char];
class_to_term c t =
  snd (class_to_term_intern
        (\ i -> c : Term_Rewriting.shows_prec_nat Arith.zero_nat i [])
        Arith.zero_nat t);

mgu_class ::
  forall a.
    (Eq a) => Term_Rewriting.Term a (Sum_Type.Sum () [Arith.Char]) ->
                Term_Rewriting.Term a [Arith.Char] ->
                  Maybe ([Arith.Char] -> Term_Rewriting.Term a [Arith.Char]);
mgu_class cs t =
  Term_Rewriting.mgu (class_to_term Arith.char_0x7A cs)
    (Term_Rewriting.map_term (\ x -> x) (\ a -> Arith.char_0x79 : a) t);

}
