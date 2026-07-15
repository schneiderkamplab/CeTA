{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Litsim_Trs_Impl(check_litsim_trs) where {

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
import qualified Trs_Impl_More;
import qualified Error_Monad;
import qualified Sum_Type;
import qualified Term_Rewriting;
import qualified Mapping;
import qualified Arith;
import qualified Shows_Literal;

check_litsim_trs ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b,
      Shows_Literal.Showl b) => [(Term_Rewriting.Term a b,
                                   Term_Rewriting.Term a b)] ->
                                  [(Term_Rewriting.Term a b,
                                     Term_Rewriting.Term a b)] ->
                                    Sum_Type.Sum (String -> String) ();
check_litsim_trs ra r =
  Error_Monad.catch_error
    (Error_Monad.bind (Trs_Impl_More.check_variants_trs ra r)
      (\ _ -> Trs_Impl_More.check_variants_trs r ra))
    (\ x ->
      Sum_Type.Inl
        (((Term_Rewriting.showsl_trs ra .
            Shows_Literal.showsl_lit "\nis not literally similar to ") .
           Term_Rewriting.showsl_trs r) .
          x));

}
