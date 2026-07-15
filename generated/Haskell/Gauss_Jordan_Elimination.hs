{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Gauss_Jordan_Elimination(mat_multrow_gen, mat_swaprows, mat_addrow_gen,
                            gauss_jordan_single, pivot_positions_gen)
  where {

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
import qualified Gauss_Jordan_IArray_Impl;
import qualified HOL;
import qualified Matrix;
import qualified Arith;

eliminate_entries_gen ::
  forall a.
    (a -> a -> a) ->
      (a -> a -> a) ->
        (Arith.Nat -> a) ->
          Matrix.Mat a -> Arith.Nat -> Arith.Nat -> Matrix.Mat a;
eliminate_entries_gen minus times v a i j =
  Matrix.mat (Matrix.dim_row a) (Matrix.dim_col a)
    (\ (ia, ja) ->
      (if not (Arith.equal_nat ia i)
        then minus (Matrix.index_mat a (ia, ja))
               (times (v ia) (Matrix.index_mat a (i, ja)))
        else Matrix.index_mat a (ia, ja)));

mat_multrow_gen ::
  forall a. (a -> a -> a) -> Arith.Nat -> a -> Matrix.Mat a -> Matrix.Mat a;
mat_multrow_gen mul k aa (Matrix.Mat_impl a) =
  Matrix.Mat_impl (Gauss_Jordan_IArray_Impl.mat_multrow_gen_impl mul k aa a);

mat_swaprows ::
  forall a. Arith.Nat -> Arith.Nat -> Matrix.Mat a -> Matrix.Mat a;
mat_swaprows k l (Matrix.Mat_impl a) =
  let {
    nr = Matrix.dim_row_impl a;
  } in (if Arith.less_nat l nr && Arith.less_nat k nr
         then Matrix.Mat_impl (Gauss_Jordan_IArray_Impl.mat_swaprows_impl k l a)
         else (error :: forall a. String -> (() -> a) -> a)
                "index out of bounds in mat_swaprows"
                (\ _ -> mat_swaprows k l (Matrix.Mat_impl a)));

gauss_jordan_main ::
  forall a.
    (Arith.Field a,
      Eq a) => Matrix.Mat a ->
                 Matrix.Mat a ->
                   Arith.Nat -> Arith.Nat -> (Matrix.Mat a, Matrix.Mat a);
gauss_jordan_main a b i j =
  let {
    nr = Matrix.dim_row a;
    nc = Matrix.dim_col a;
  } in (if Arith.less_nat i nr && Arith.less_nat j nc
         then let {
                aij = Matrix.index_mat a (i, j);
              } in (if aij == Arith.zero
                     then (case concatMap
                                  (\ ia ->
                                    (if not
  (Matrix.index_mat a (ia, j) == Arith.zero)
                                      then [ia] else []))
                                  (Arith.upt (Arith.suc i) nr)
                            of {
                            [] -> gauss_jordan_main a b i (Arith.suc j);
                            ia : _ ->
                              gauss_jordan_main (mat_swaprows i ia a)
                                (mat_swaprows i ia b) i j;
                          })
                     else (if aij == Arith.one
                            then let {
                                   v = (\ ia -> Matrix.index_mat a (ia, j));
                                 } in gauss_jordan_main
(eliminate_entries_gen Arith.minusa Arith.times v a i j)
(eliminate_entries_gen Arith.minusa Arith.times v b i j) (Arith.suc i)
(Arith.suc j)
                            else let {
                                   iaij = Arith.inverse aij;
                                   aa = mat_multrow_gen Arith.times i iaij a;
                                   ba = mat_multrow_gen Arith.times i iaij b;
                                   v = (\ ia -> Matrix.index_mat aa (ia, j));
                                 } in gauss_jordan_main
(eliminate_entries_gen Arith.minusa Arith.times v aa i j)
(eliminate_entries_gen Arith.minusa Arith.times v ba i j) (Arith.suc i)
(Arith.suc j)))
         else (a, b));

gauss_jordan ::
  forall a.
    (Arith.Field a,
      Eq a) => Matrix.Mat a -> Matrix.Mat a -> (Matrix.Mat a, Matrix.Mat a);
gauss_jordan a b = gauss_jordan_main a b Arith.zero_nat Arith.zero_nat;

mat_addrow_gen ::
  forall a.
    (a -> a -> a) ->
      (a -> a -> a) ->
        a -> Arith.Nat -> Arith.Nat -> Matrix.Mat a -> Matrix.Mat a;
mat_addrow_gen ad mul aa k l (Matrix.Mat_impl a) =
  (if Arith.less_nat l (Matrix.dim_row_impl a)
    then Matrix.Mat_impl
           (Gauss_Jordan_IArray_Impl.mat_addrow_gen_impl ad mul aa k l a)
    else (error :: forall a. String -> (() -> a) -> a)
           "index out of bounds in mat_addrow"
           (\ _ -> mat_addrow_gen ad mul aa k l (Matrix.Mat_impl a)));

gauss_jordan_single ::
  forall a. (Arith.Field a, Eq a) => Matrix.Mat a -> Matrix.Mat a;
gauss_jordan_single a =
  fst (gauss_jordan a (Matrix.zero_mat (Matrix.dim_row a) Arith.zero_nat));

pivot_positions_main_gen ::
  forall a.
    (Eq a) => a -> Matrix.Mat a ->
                     Arith.Nat ->
                       Arith.Nat ->
                         Arith.Nat -> Arith.Nat -> [(Arith.Nat, Arith.Nat)];
pivot_positions_main_gen zero a nr nc i j =
  (if Arith.less_nat i nr
    then (if Arith.less_nat j nc
           then (if Matrix.index_mat a (i, j) == zero
                  then pivot_positions_main_gen zero a nr nc i (Arith.suc j)
                  else (i, j) :
                         pivot_positions_main_gen zero a nr nc (Arith.suc i)
                           (Arith.suc j))
           else [])
    else []);

pivot_positions_gen ::
  forall a. (Eq a) => a -> Matrix.Mat a -> [(Arith.Nat, Arith.Nat)];
pivot_positions_gen zer a =
  pivot_positions_main_gen zer a (Matrix.dim_row a) (Matrix.dim_col a)
    Arith.zero_nat Arith.zero_nat;

}
