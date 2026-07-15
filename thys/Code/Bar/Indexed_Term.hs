{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Indexed_Term(index, stored, name_of, index_term) where {

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

index ::
  forall a b.
    Term_Rewriting.Term (a, (Term_Rewriting.Term a b, Arith.Int))
      (b, (Term_Rewriting.Term a b, Arith.Int)) ->
      Arith.Int;
index (Term_Rewriting.Var (uu, (uv, i))) = i;
index (Term_Rewriting.Fun (uw, (ux, i)) uy) = i;

stored ::
  forall a b.
    Term_Rewriting.Term (a, (Term_Rewriting.Term a b, Arith.Int))
      (b, (Term_Rewriting.Term a b, Arith.Int)) ->
      Term_Rewriting.Term a b;
stored (Term_Rewriting.Var (v, (s, uu))) = s;
stored (Term_Rewriting.Fun (f, (s, uv)) ts) = s;

name_of :: forall a b. (a, b) -> a;
name_of (a, uu) = a;

index_term_aux ::
  forall a b.
    Arith.Int ->
      Term_Rewriting.Term a b ->
        (Arith.Int,
          Term_Rewriting.Term (a, (Term_Rewriting.Term a b, Arith.Int))
            (b, (Term_Rewriting.Term a b, Arith.Int)));
index_term_aux i (Term_Rewriting.Var v) =
  (Arith.plus_int i Arith.one_int,
    Term_Rewriting.Var (v, (Term_Rewriting.Var v, i)));
index_term_aux i (Term_Rewriting.Fun f ts) =
  (case index_term_aux_list i ts of {
    (j, ss) ->
      (Arith.plus_int j Arith.one_int,
        Term_Rewriting.Fun (f, (Term_Rewriting.Fun f ts, j)) ss);
  });

index_term_aux_list ::
  forall a b.
    Arith.Int ->
      [Term_Rewriting.Term a b] ->
        (Arith.Int,
          [Term_Rewriting.Term (a, (Term_Rewriting.Term a b, Arith.Int))
             (b, (Term_Rewriting.Term a b, Arith.Int))]);
index_term_aux_list i [] = (i, []);
index_term_aux_list i (t : ts) =
  (case index_term_aux i t of {
    (j, s) -> Arith.map_prod id (\ a -> s : a) (index_term_aux_list j ts);
  });

index_term ::
  forall a b.
    Term_Rewriting.Term a b ->
      Term_Rewriting.Term (a, (Term_Rewriting.Term a b, Arith.Int))
        (b, (Term_Rewriting.Term a b, Arith.Int));
index_term t = snd (index_term_aux Arith.zero_int t);

}
