{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Matrix_Comparison(mat_ge) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import Data.Bits ((.&.), (.|.), (.^.));
import qualified Prelude;
import qualified Data.Bits;
import qualified HOL;
import qualified Matrix;
import qualified Orderings;
import qualified List;
import qualified Arith;

mat_ge :: forall a. (Orderings.Ord a) => Matrix.Mat a -> Matrix.Mat a -> Bool;
mat_ge a b =
  let {
    d = Arith.minus_nat (Matrix.dim_row a) Arith.one_nat;
  } in (if Arith.less_nat d (Matrix.dim_row a)
         then List.all_interval
                (\ i ->
                  let {
                    da = Arith.minus_nat (Matrix.dim_col a) Arith.one_nat;
                  } in (if Arith.less_nat da (Matrix.dim_col a)
                         then List.all_interval
                                (\ j ->
                                  Orderings.less_eq (Matrix.index_mat b (i, j))
                                    (Matrix.index_mat a (i, j)))
                                Arith.Zero_nat da
                         else True))
                Arith.Zero_nat d
         else True);

}
