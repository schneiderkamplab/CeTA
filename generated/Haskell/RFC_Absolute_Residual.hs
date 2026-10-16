{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module RFC_Absolute_Residual(rfc_matchbox_absolute_bounds_tt) where {

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
import qualified RFC_Matchbounds_Ext;
import qualified Error_Monad;
import qualified Termination_Problem_Spec;
import qualified Matchbounds_Impl;
import qualified Sum_Type;
import qualified Mapping;
import qualified Arith;
import qualified Compare;
import qualified Term_Rewriting;

rfc_matchbox_absolute_bounds_tt ::
  forall a b c.
    (Compare.Compare_order b, Eq b, Term_Rewriting.Showl b, Arith.Ccompare c,
      Compare.Compare_order c, Eq c, Mapping.Mapping_impl c,
      Term_Rewriting.Showl c) => Termination_Problem_Spec.Tp_ops_ext a b
                                   [Arith.Char] () ->
                                   Matchbounds_Impl.Bounds_info b c ->
                                     [Term_Rewriting.Term b [Arith.Char]] ->
                                       [(Term_Rewriting.Term b [Arith.Char],
  Term_Rewriting.Term b [Arith.Char])] ->
 a -> Sum_Type.Sum (String -> String) a;
rfc_matchbox_absolute_bounds_tt i info initial_terms d tp =
  Error_Monad.bind
    (RFC_Matchbounds_Ext.rfc_matchbox_relative_bounds_tt i info initial_terms d
      tp)
    (\ tpa ->
      Sum_Type.Inr
        (Termination_Problem_Spec.mk i (Termination_Problem_Spec.nfs i tpa)
          (Termination_Problem_Spec.q i tpa) (Termination_Problem_Spec.r i tpa)
          []));

}
