{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Invariants_To_Assertions(fix_invariants) where {

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
import qualified Error_Monad;
import qualified HOL;
import qualified Sum_Type;
import qualified Term_Rewriting;
import qualified Mapping;
import qualified Arith;
import qualified Shows_Literal;

fix_invariants ::
  forall a b c d e.
    (Arith.Ccompare d, Eq d, Mapping.Mapping_impl d, Shows_Literal.Showl d,
      Shows_Literal.Showl e) => Term_Rewriting.Lts_impl a b c d e ->
                                  (d -> Term_Rewriting.Formula
  (Term_Rewriting.Term a (b, c))) ->
                                    Sum_Type.Sum (String -> String)
                                      (Term_Rewriting.Lts_impl a b c d e);
fix_invariants p phi =
  Error_Monad.catch_error
    (let {
       ls = Term_Rewriting.nodes_lts_impl p;
       _ = Term_Rewriting.assertion_of p;
     } in Sum_Type.Inr
            (Term_Rewriting.Lts_Impl (Term_Rewriting.initiala p)
              (Term_Rewriting.transitions_impl p) (map (\ l -> (l, phi l)) ls)))
    (\ x ->
      Sum_Type.Inl
        (Shows_Literal.showsl_lit
           "problem when fixing invariants as assertions\n" .
          x));

}
