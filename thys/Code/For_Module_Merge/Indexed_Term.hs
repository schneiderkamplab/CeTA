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
import qualified Product_Type;
import qualified Term;
import qualified Arith;

index ::
  forall a b.
    Term.Term (a, (Term.Term a b, Arith.Int)) (b, (Term.Term a b, Arith.Int)) ->
      Arith.Int;
index (Term.Var (uu, (uv, i))) = i;
index (Term.Fun (uw, (ux, i)) uy) = i;

stored ::
  forall a b.
    Term.Term (a, (Term.Term a b, Arith.Int)) (b, (Term.Term a b, Arith.Int)) ->
      Term.Term a b;
stored (Term.Var (v, (s, uu))) = s;
stored (Term.Fun (f, (s, uv)) ts) = s;

name_of :: forall a b. (a, b) -> a;
name_of (a, uu) = a;

index_term_aux ::
  forall a b.
    Arith.Int ->
      Term.Term a b ->
        (Arith.Int,
          Term.Term (a, (Term.Term a b, Arith.Int))
            (b, (Term.Term a b, Arith.Int)));
index_term_aux i (Term.Var v) =
  (Arith.plus_int i Arith.one_int, Term.Var (v, (Term.Var v, i)));
index_term_aux i (Term.Fun f ts) =
  (case index_term_aux_list i ts of {
    (j, ss) ->
      (Arith.plus_int j Arith.one_int, Term.Fun (f, (Term.Fun f ts, j)) ss);
  });

index_term_aux_list ::
  forall a b.
    Arith.Int ->
      [Term.Term a b] ->
        (Arith.Int,
          [Term.Term (a, (Term.Term a b, Arith.Int))
             (b, (Term.Term a b, Arith.Int))]);
index_term_aux_list i [] = (i, []);
index_term_aux_list i (t : ts) =
  (case index_term_aux i t of {
    (j, s) ->
      Product_Type.map_prod id (\ a -> s : a) (index_term_aux_list j ts);
  });

index_term ::
  forall a b.
    Term.Term a b ->
      Term.Term (a, (Term.Term a b, Arith.Int)) (b, (Term.Term a b, Arith.Int));
index_term t = snd (index_term_aux Arith.zero_int t);

}
