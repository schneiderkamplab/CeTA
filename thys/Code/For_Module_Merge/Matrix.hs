{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Matrix(Mat(..), Vec, index_mat, dim_row, mat, dim_col, map_mat, one_mat,
          vec_index, pow_mat, diag_mat, plus_mat, carrier_mat, zero_mat,
          ring_mat, smult_mat, mat_of_rows, mat_to_list, vec_of_list,
          elements_mat, upper_triangular, minus_mat, uminus_mat)
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
import qualified Collection_Order;
import qualified Set_Impl;
import qualified Collection_Eq;
import qualified Groups_List;
import qualified Congruence;
import qualified Group;
import qualified Ring;
import qualified Set;
import qualified HOL;
import qualified List;
import qualified Product_Type;
import qualified Arith;
import qualified Matrix_IArray_Impl;

newtype Mat a = Mat_impl (Matrix_IArray_Impl.Mat_impl a);

newtype Vec a = Vec_impl (Matrix_IArray_Impl.Vec_impl a);

index_mat :: forall a. Mat a -> (Arith.Nat, Arith.Nat) -> a;
index_mat (Mat_impl m) ij = Matrix_IArray_Impl.index_mat_impl m ij;

dim_row :: forall a. Mat a -> Arith.Nat;
dim_row (Mat_impl m) = Matrix_IArray_Impl.dim_row_impl m;

vec :: forall a. Arith.Nat -> (Arith.Nat -> a) -> Vec a;
vec n f = Vec_impl (Matrix_IArray_Impl.vec_of_fun n f);

col :: forall a. Mat a -> Arith.Nat -> Vec a;
col a j = vec (dim_row a) (\ i -> index_mat a (i, j));

mat ::
  forall a. Arith.Nat -> Arith.Nat -> ((Arith.Nat, Arith.Nat) -> a) -> Mat a;
mat nr nc f = Mat_impl (Matrix_IArray_Impl.mat_of_fun nr nc f);

dim_col :: forall a. Mat a -> Arith.Nat;
dim_col (Mat_impl m) = Matrix_IArray_Impl.dim_col_impl m;

row :: forall a. Mat a -> Arith.Nat -> Vec a;
row a i = vec (dim_col a) (\ j -> index_mat a (i, j));

dim_vec :: forall a. Vec a -> Arith.Nat;
dim_vec (Vec_impl v) = Matrix_IArray_Impl.dim_vec_impl v;

map_mat :: forall a b. (a -> b) -> Mat a -> Mat b;
map_mat f a = mat (dim_row a) (dim_col a) (\ ij -> f (index_mat a ij));

one_mat :: forall a. (Arith.One a, Arith.Zero a) => Arith.Nat -> Mat a;
one_mat n =
  mat n n (\ (i, j) -> (if Arith.equal_nat i j then Arith.one else Arith.zero));

vec_index :: forall a. Vec a -> Arith.Nat -> a;
vec_index (Vec_impl v) i = Matrix_IArray_Impl.vec_index_impl v i;

scalar_prod :: forall a. (Arith.Semiring_0 a) => Vec a -> Vec a -> a;
scalar_prod v w =
  let {
    d = Arith.minus_nat (dim_vec w) Arith.one_nat;
  } in (if Arith.less_nat d (dim_vec w)
         then Groups_List.sum_list
                (map (\ i -> Arith.times (vec_index v i) (vec_index w i))
                  (List.interval Arith.zero_nat d))
         else Arith.zero);

times_mat :: forall a. (Arith.Semiring_0 a) => Mat a -> Mat a -> Mat a;
times_mat a b =
  mat (dim_row a) (dim_col b) (\ (i, j) -> scalar_prod (row a i) (col b j));

pow_mat :: forall a. (Arith.Semiring_1 a) => Mat a -> Arith.Nat -> Mat a;
pow_mat a k =
  (if Arith.equal_nat k Arith.zero_nat then one_mat (dim_row a)
    else times_mat (pow_mat a (Arith.minus_nat k Arith.one_nat)) a);

diag_mat :: forall a. Mat a -> [a];
diag_mat a =
  map (\ i -> index_mat a (i, i)) (List.upt Arith.zero_nat (dim_row a));

plus_mat :: forall a. (Arith.Plus a) => Mat a -> Mat a -> Mat a;
plus_mat a b =
  mat (dim_row b) (dim_col b)
    (\ ij -> Arith.plus (index_mat a ij) (index_mat b ij));

carrier_mat :: forall a. Arith.Nat -> Arith.Nat -> Set.Set (Mat a);
carrier_mat nr nc =
  Set.Collect_set
    (\ a -> Arith.equal_nat (dim_row a) nr && Arith.equal_nat (dim_col a) nc);

zero_mat :: forall a. (Arith.Zero a) => Arith.Nat -> Arith.Nat -> Mat a;
zero_mat nr nc = mat nr nc (\ _ -> Arith.zero);

ring_mat ::
  forall a b.
    (Arith.Semiring_1 a) => HOL.Itself a ->
                              Arith.Nat ->
                                b -> Congruence.Partial_object_ext (Mat a)
                                       (Group.Monoid_ext (Mat a)
 (Ring.Ring_ext (Mat a) b));
ring_mat ty n b =
  Congruence.Partial_object_ext (carrier_mat n n)
    (Group.Monoid_ext times_mat (one_mat n)
      (Ring.Ring_ext (zero_mat n n) plus_mat b));

smult_mat :: forall a. (Arith.Times a) => a -> Mat a -> Mat a;
smult_mat aa a = map_mat (Arith.times aa) a;

mat_of_rows :: forall a. Arith.Nat -> [Vec a] -> Mat a;
mat_of_rows n rs =
  mat (List.size_list rs) n (\ (i, a) -> vec_index (List.nth rs i) a);

mat_to_list :: forall a. Mat a -> [[a]];
mat_to_list a =
  map (\ i ->
        map (\ j -> index_mat a (i, j)) (List.upt Arith.zero_nat (dim_col a)))
    (List.upt Arith.zero_nat (dim_row a));

vec_of_list :: forall a. [a] -> Vec a;
vec_of_list v = Vec_impl (Matrix_IArray_Impl.vec_of_list_impl v);

elements_mat ::
  forall a.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a,
      Set_Impl.Set_impl a) => Mat a -> Set.Set a;
elements_mat a =
  List.set
    (concatMap
      (\ i ->
        map (\ j -> index_mat a (i, j)) (List.upt Arith.zero_nat (dim_col a)))
      (List.upt Arith.zero_nat (dim_row a)));

upper_triangular :: forall a. (Arith.Zero a, Eq a) => Mat a -> Bool;
upper_triangular a =
  let {
    d = Arith.minus_nat (dim_row a) Arith.one_nat;
  } in (if Arith.less_nat d (dim_row a)
         then List.all_interval
                (\ i ->
                  let {
                    da = Arith.minus_nat i Arith.one_nat;
                  } in (if Arith.less_nat da i
                         then List.all_interval
                                (\ j -> index_mat a (i, j) == Arith.zero)
                                Arith.zero_nat da
                         else True))
                Arith.zero_nat d
         else True);

minus_mat :: forall a. (Arith.Minus a) => Mat a -> Mat a -> Mat a;
minus_mat a b =
  mat (dim_row b) (dim_col b)
    (\ ij -> Arith.minus (index_mat a ij) (index_mat b ij));

uminus_mat :: forall a. (Arith.Uminus a) => Mat a -> Mat a;
uminus_mat a =
  mat (dim_row a) (dim_col a) (\ ij -> Arith.uminus (index_mat a ij));

}
