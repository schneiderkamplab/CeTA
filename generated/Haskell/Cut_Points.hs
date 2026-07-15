{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Cut_Points(check_cut_points) where {

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
import qualified Gabow_SCC_RBT;
import qualified Error_Monad;
import qualified Sum_Type;
import qualified Compare;
import qualified Term_Rewriting;
import qualified Arith;

check_acyclic ::
  forall a.
    (Arith.Ceq a, Arith.Ccompare a, Compare.Compare_order a, Eq a,
      Arith.Set_impl a,
      Term_Rewriting.Showl a) => [(a, a)] -> Sum_Type.Sum (String -> String) ();
check_acyclic r =
  Error_Monad.catch_error
    (Error_Monad.catch_error
      (Error_Monad.forallM
        (\ scc ->
          Sum_Type.Inl
            ((Term_Rewriting.showsl_lit "SCC " .
               Term_Rewriting.showsl_list scc) .
              Term_Rewriting.showsl_lit " detected "))
        (Gabow_SCC_RBT.scc_decomp r))
      (\ x -> Sum_Type.Inl (snd x)))
    (\ x ->
      Sum_Type.Inl
        (((Term_Rewriting.showsl_lit "\ngraph " .
            Term_Rewriting.showsl_list_prod r) .
           Term_Rewriting.showsl_lit " not acyclic\n") .
          x));

check_cut_points ::
  forall a.
    (Arith.Ceq a, Arith.Ccompare a, Compare.Compare_order a, Eq a,
      Arith.Set_impl a,
      Term_Rewriting.Showl a) => [(a, a)] ->
                                   Arith.Set a ->
                                     Sum_Type.Sum (String -> String) ();
check_cut_points r x =
  check_acyclic
    (filter
      (\ ab -> not (Arith.member (fst ab) x) && not (Arith.member (snd ab) x))
      r);

}
