{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Matrix(Mat_impl(..), rep_mat_impl, Mat(..), equal_mat, Vec_impl, Vec,
          index_mat, dim_row_impl, dim_row, mat, dim_col, map_mat, one_mat,
          vec_index, times_mat, pow_mat, diag_mat, plus_mat, carrier_mat,
          zero_mat, ring_mat, smult_mat, mat_of_rows, mat_to_list, vec_of_list,
          elements_mat, upper_triangular, less_mat, minus_mat, uminus_mat)
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
import qualified IArraya;
import qualified Quasi_Order;
import qualified Groups_List;
import qualified Congruence;
import qualified Group;
import qualified Ring;
import qualified HOL;
import qualified Arith;

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

newtype Mat a = Mat_impl (Mat_impl a);

equal_mat :: forall a. (Eq a) => Mat a -> Mat a -> Bool;
equal_mat (Mat_impl m1) (Mat_impl m2) = mat_equal_impl m1 m2;

instance (Eq a) => Eq (Mat a) where {
  a == b = equal_mat a b;
};

newtype Vec_impl a = Abs_vec_impl (Arith.Nat, IArray.IArray a);

newtype Vec a = Vec_impl (Vec_impl a);

index_mat_impl :: forall a. Mat_impl a -> (Arith.Nat, Arith.Nat) -> a;
index_mat_impl xa =
  (case rep_mat_impl xa of {
    (nr, (_, m)) ->
      (\ (i, j) ->
        (if Arith.less_nat i nr then IArraya.sub (IArraya.sub m i) j
          else IArraya.sub
                 (IArray.of_list (Arith.nth [] (Arith.minus_nat i nr))) j));
  });

index_mat :: forall a. Mat a -> (Arith.Nat, Arith.Nat) -> a;
index_mat (Mat_impl m) ij = index_mat_impl m ij;

dim_row_impl :: forall a. Mat_impl a -> Arith.Nat;
dim_row_impl xa = fst (rep_mat_impl xa);

dim_row :: forall a. Mat a -> Arith.Nat;
dim_row (Mat_impl m) = dim_row_impl m;

vec_of_fun :: forall a. Arith.Nat -> (Arith.Nat -> a) -> Vec_impl a;
vec_of_fun xb xc = Abs_vec_impl (xb, IArraya.of_fun xc xb);

vec :: forall a. Arith.Nat -> (Arith.Nat -> a) -> Vec a;
vec n f = Vec_impl (vec_of_fun n f);

col :: forall a. Mat a -> Arith.Nat -> Vec a;
col a j = vec (dim_row a) (\ i -> index_mat a (i, j));

mat_of_fun ::
  forall a.
    Arith.Nat -> Arith.Nat -> ((Arith.Nat, Arith.Nat) -> a) -> Mat_impl a;
mat_of_fun xc xd xe =
  Abs_mat_impl
    (xc, (xd, IArraya.of_fun (\ i -> IArraya.of_fun (\ j -> xe (i, j)) xd) xc));

mat ::
  forall a. Arith.Nat -> Arith.Nat -> ((Arith.Nat, Arith.Nat) -> a) -> Mat a;
mat nr nc f = Mat_impl (mat_of_fun nr nc f);

dim_col_impl :: forall a. Mat_impl a -> Arith.Nat;
dim_col_impl xa = fst (snd (rep_mat_impl xa));

dim_col :: forall a. Mat a -> Arith.Nat;
dim_col (Mat_impl m) = dim_col_impl m;

row :: forall a. Mat a -> Arith.Nat -> Vec a;
row a i = vec (dim_col a) (\ j -> index_mat a (i, j));

rep_vec_impl :: forall a. Vec_impl a -> (Arith.Nat, IArray.IArray a);
rep_vec_impl (Abs_vec_impl x) = x;

dim_vec_impl :: forall a. Vec_impl a -> Arith.Nat;
dim_vec_impl xa = fst (rep_vec_impl xa);

dim_vec :: forall a. Vec a -> Arith.Nat;
dim_vec (Vec_impl v) = dim_vec_impl v;

map_mat :: forall a b. (a -> b) -> Mat a -> Mat b;
map_mat f a = mat (dim_row a) (dim_col a) (\ ij -> f (index_mat a ij));

one_mat :: forall a. (Arith.One a, Arith.Zero a) => Arith.Nat -> Mat a;
one_mat n =
  mat n n (\ (i, j) -> (if Arith.equal_nat i j then Arith.one else Arith.zero));

vec_index_impl :: forall a. Vec_impl a -> Arith.Nat -> a;
vec_index_impl xa = (case rep_vec_impl xa of {
                      (_, a) -> IArraya.sub a;
                    });

vec_index :: forall a. Vec a -> Arith.Nat -> a;
vec_index (Vec_impl v) i = vec_index_impl v i;

scalar_prod :: forall a. (Arith.Semiring_0 a) => Vec a -> Vec a -> a;
scalar_prod v w =
  let {
    d = Arith.minus_nat (dim_vec w) Arith.one_nat;
  } in (if Arith.less_nat d (dim_vec w)
         then Groups_List.sum_list
                (map (\ i -> Arith.times (vec_index v i) (vec_index w i))
                  (Arith.interval Arith.zero_nat d))
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
  map (\ i -> index_mat a (i, i)) (Arith.upt Arith.zero_nat (dim_row a));

plus_mat :: forall a. (Arith.Plus a) => Mat a -> Mat a -> Mat a;
plus_mat a b =
  mat (dim_row b) (dim_col b)
    (\ ij -> Arith.plus (index_mat a ij) (index_mat b ij));

carrier_mat :: forall a. Arith.Nat -> Arith.Nat -> Arith.Set (Mat a);
carrier_mat nr nc =
  Arith.Collect_set
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
  mat (Arith.size_list rs) n (\ (i, a) -> vec_index (Arith.nth rs i) a);

mat_to_list :: forall a. Mat a -> [[a]];
mat_to_list a =
  map (\ i ->
        map (\ j -> index_mat a (i, j)) (Arith.upt Arith.zero_nat (dim_col a)))
    (Arith.upt Arith.zero_nat (dim_row a));

vec_of_list_impl :: forall a. [a] -> Vec_impl a;
vec_of_list_impl xa = Abs_vec_impl (Arith.size_list xa, IArray.of_list xa);

vec_of_list :: forall a. [a] -> Vec a;
vec_of_list v = Vec_impl (vec_of_list_impl v);

elements_mat ::
  forall a.
    (Arith.Ceq a, Arith.Ccompare a, Arith.Set_impl a) => Mat a -> Arith.Set a;
elements_mat a =
  Arith.set
    (concatMap
      (\ i ->
        map (\ j -> index_mat a (i, j)) (Arith.upt Arith.zero_nat (dim_col a)))
      (Arith.upt Arith.zero_nat (dim_row a)));

upper_triangular :: forall a. (Arith.Zero a, Eq a) => Mat a -> Bool;
upper_triangular a =
  let {
    d = Arith.minus_nat (dim_row a) Arith.one_nat;
  } in (if Arith.less_nat d (dim_row a)
         then Arith.all_interval
                (\ i ->
                  let {
                    da = Arith.minus_nat i Arith.one_nat;
                  } in (if Arith.less_nat da i
                         then Arith.all_interval
                                (\ j -> index_mat a (i, j) == Arith.zero)
                                Arith.zero_nat da
                         else True))
                Arith.zero_nat d
         else True);

less_eq_mat :: forall a. (Quasi_Order.Ord a) => Mat a -> Mat a -> Bool;
less_eq_mat a b =
  Arith.equal_nat (dim_row a) (dim_row b) &&
    Arith.equal_nat (dim_col a) (dim_col b) &&
      let {
        d = Arith.minus_nat (dim_row b) Arith.one_nat;
      } in (if Arith.less_nat d (dim_row b)
             then Arith.all_interval
                    (\ i ->
                      let {
                        da = Arith.minus_nat (dim_col b) Arith.one_nat;
                      } in (if Arith.less_nat da (dim_col b)
                             then Arith.all_interval
                                    (\ j ->
                                      Quasi_Order.less_eq (index_mat a (i, j))
(index_mat b (i, j)))
                                    Arith.zero_nat da
                             else True))
                    Arith.zero_nat d
             else True);

less_mat :: forall a. (Quasi_Order.Ord a) => Mat a -> Mat a -> Bool;
less_mat a b = less_eq_mat a b && not (less_eq_mat b a);

minus_mat :: forall a. (Arith.Minus a) => Mat a -> Mat a -> Mat a;
minus_mat a b =
  mat (dim_row b) (dim_col b)
    (\ ij -> Arith.minusa (index_mat a ij) (index_mat b ij));

uminus_mat :: forall a. (Arith.Uminus a) => Mat a -> Mat a;
uminus_mat a =
  mat (dim_row a) (dim_col a) (\ ij -> Arith.uminus (index_mat a ij));

}
