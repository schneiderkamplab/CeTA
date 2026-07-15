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
import qualified Product_Type;
import qualified List;
import qualified HOL;
import qualified Show_Instances;
import qualified Arith;
import qualified Unification;
import qualified Sum_Type;
import qualified Term;
import qualified Str;

class_to_term_intern ::
  forall a b.
    (Arith.Nat -> a) ->
      Arith.Nat ->
        Term.Term b (Sum_Type.Sum () a) -> (Arith.Nat, Term.Term b a);
class_to_term_intern iv i (Term.Fun f ts) =
  (case List.foldr (\ t (j, ss) -> (case class_to_term_intern iv j t of {
                                     (k, s) -> (k, s : ss);
                                   }))
          ts (i, [])
    of {
    (k, ss) -> (k, Term.Fun f ss);
  });
class_to_term_intern iv i (Term.Var (Sum_Type.Inl uu)) =
  (Arith.plus_nat i Arith.one_nat, Term.Var (iv i));
class_to_term_intern iv i (Term.Var (Sum_Type.Inr x)) = (i, Term.Var x);

class_to_term ::
  forall a.
    Str.Char ->
      Term.Term a (Sum_Type.Sum () [Str.Char]) -> Term.Term a [Str.Char];
class_to_term c t =
  snd (class_to_term_intern
        (\ i -> c : Show_Instances.shows_prec_nat Arith.zero_nat i [])
        Arith.zero_nat t);

mgu_class ::
  forall a.
    (Eq a) => Term.Term a (Sum_Type.Sum () [Str.Char]) ->
                Term.Term a [Str.Char] ->
                  Maybe ([Str.Char] -> Term.Term a [Str.Char]);
mgu_class cs t =
  Unification.mgu (class_to_term Str.char_0x7A cs)
    (Term.map_term (\ x -> x) (\ a -> Str.char_0x79 : a) t);

}
