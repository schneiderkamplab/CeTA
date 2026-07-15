{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Matrix_IArray_Impl(Mat_impl(..), rep_mat_impl, equal_mat, Vec_impl,
                      mat_of_fun, vec_of_fun, dim_col_impl, dim_row_impl,
                      dim_vec_impl, index_mat_impl, vec_index_impl,
                      vec_of_list_impl)
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
import qualified Product_Type;
import qualified List;
import qualified IArraya;
import qualified Arith;
import qualified Matrix;

newtype Mat_impl a = Abs_mat_impl
  (Arith.Nat, (Arith.Nat, IArray.IArray (IArray.IArray a)));

rep_mat_impl ::
  forall a.
    Mat_impl a -> (Arith.Nat, (Arith.Nat, IArray.IArray (IArray.IArray a)));
rep_mat_impl (Abs_mat_impl x) = x;

mat_equal_impl :: forall a. (Eq a) => Mat_impl a -> Mat_impl a -> Bool;
mat_equal_impl xa xc =
  (case rep_mat_impl xa of {
    (nr1, (nc1, m1)) ->
      (\ (nr2, (nc2, m2)) ->
        Arith.equal_nat nr1 nr2 &&
          Arith.equal_nat nc1 nc2 && IArraya.equal_iarray m1 m2);
  })
    (rep_mat_impl xc);

equal_mat :: forall a. (Eq a) => Matrix.Mat a -> Matrix.Mat a -> Bool;
equal_mat (Matrix.Mat_impl m1) (Matrix.Mat_impl m2) = mat_equal_impl m1 m2;

instance (Eq a) => Eq (Matrix.Mat a) where {
  a == b = equal_mat a b;
};

newtype Vec_impl a = Abs_vec_impl (Arith.Nat, IArray.IArray a);

mat_of_fun ::
  forall a.
    Arith.Nat -> Arith.Nat -> ((Arith.Nat, Arith.Nat) -> a) -> Mat_impl a;
mat_of_fun xc xd xe =
  Abs_mat_impl
    (xc, (xd, IArraya.of_fun (\ i -> IArraya.of_fun (\ j -> xe (i, j)) xd) xc));

vec_of_fun :: forall a. Arith.Nat -> (Arith.Nat -> a) -> Vec_impl a;
vec_of_fun xb xc = Abs_vec_impl (xb, IArraya.of_fun xc xb);

dim_col_impl :: forall a. Mat_impl a -> Arith.Nat;
dim_col_impl xa = fst (snd (rep_mat_impl xa));

dim_row_impl :: forall a. Mat_impl a -> Arith.Nat;
dim_row_impl xa = fst (rep_mat_impl xa);

rep_vec_impl :: forall a. Vec_impl a -> (Arith.Nat, IArray.IArray a);
rep_vec_impl (Abs_vec_impl x) = x;

dim_vec_impl :: forall a. Vec_impl a -> Arith.Nat;
dim_vec_impl xa = fst (rep_vec_impl xa);

index_mat_impl :: forall a. Mat_impl a -> (Arith.Nat, Arith.Nat) -> a;
index_mat_impl xa =
  (case rep_mat_impl xa of {
    (nr, (_, m)) ->
      (\ (i, j) ->
        (if Arith.less_nat i nr then IArraya.sub (IArraya.sub m i) j
          else IArraya.sub (IArray.of_list (List.nth [] (Arith.minus_nat i nr)))
                 j));
  });

vec_index_impl :: forall a. Vec_impl a -> Arith.Nat -> a;
vec_index_impl xa = (case rep_vec_impl xa of {
                      (_, a) -> IArraya.sub a;
                    });

vec_of_list_impl :: forall a. [a] -> Vec_impl a;
vec_of_list_impl xa = Abs_vec_impl (List.size_list xa, IArray.of_list xa);

}
