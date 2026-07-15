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
import qualified Set;
import qualified Gabow_SCC_RBT;
import qualified Error_Monad;
import qualified Sum_Type;
import qualified Collection_Order;
import qualified Compare;
import qualified Shows_Literal;
import qualified Set_Impl;
import qualified Collection_Eq;

check_acyclic ::
  forall a.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a, Compare.Compare_order a,
      Eq a, Set_Impl.Set_impl a,
      Shows_Literal.Showl a) => [(a, a)] -> Sum_Type.Sum (String -> String) ();
check_acyclic r =
  Error_Monad.catch_error
    (Error_Monad.catch_error
      (Error_Monad.forallM
        (\ scc ->
          Sum_Type.Inl
            ((Shows_Literal.showsl_lit "SCC " . Shows_Literal.showsl_list scc) .
              Shows_Literal.showsl_lit " detected "))
        (Gabow_SCC_RBT.scc_decomp r))
      (\ x -> Sum_Type.Inl (snd x)))
    (\ x ->
      Sum_Type.Inl
        (((Shows_Literal.showsl_lit "\ngraph " .
            Shows_Literal.showsl_list_prod r) .
           Shows_Literal.showsl_lit " not acyclic\n") .
          x));

check_cut_points ::
  forall a.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a, Compare.Compare_order a,
      Eq a, Set_Impl.Set_impl a,
      Shows_Literal.Showl a) => [(a, a)] ->
                                  Set.Set a ->
                                    Sum_Type.Sum (String -> String) ();
check_cut_points r x =
  check_acyclic
    (filter (\ ab -> not (Set.member (fst ab) x) && not (Set.member (snd ab) x))
      r);

}
