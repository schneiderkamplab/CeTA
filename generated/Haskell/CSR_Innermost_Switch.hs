{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module CSR_Innermost_Switch(check_csr_orthogonal) where {

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
import qualified Critical_Pairs_Impl;
import qualified Renaming2_String;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified Renaming2;
import qualified Sum_Type;
import qualified Compare;
import qualified Term_Rewriting;
import qualified Arith;
import qualified Lists_are_Infinite;

check_csr_orthogonal ::
  forall a.
    (Compare.Compare_order a, Eq a,
      Term_Rewriting.Showl a) => [(Term_Rewriting.Term a [Arith.Char],
                                    Term_Rewriting.Term a [Arith.Char])] ->
                                   Sum_Type.Sum (String -> String) ();
check_csr_orthogonal r =
  Error_Monad.bind
    (Error_Monad.catch_error (Term_Rewriting.check_left_linear_trs r)
      (\ x ->
        Sum_Type.Inl
          (Term_Rewriting.showsl_lit "the CSR is not left-linear\n" . x)))
    (\ _ ->
      Error_Monad.catch_error
        (Error_Monad.forallM
          (\ (at_root, (s, t)) ->
            Check_Monad.check (at_root && Term_Rewriting.equal_term s t)
              (((Term_Rewriting.showsl_lit
                   "the CSR has a non-root or non-trivial overlap: " .
                  Term_Rewriting.showsl_terma s) .
                 Term_Rewriting.showsl_lit " <- . -> ") .
                Term_Rewriting.showsl_terma t))
          (Critical_Pairs_Impl.critical_pairs_impl
            Renaming2_String.string_rename r r))
        (\ x -> Sum_Type.Inl (snd x)));

}
