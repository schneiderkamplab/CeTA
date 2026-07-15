{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Matrix(Mat, index_mat, dim_row, mat, dim_col, zero_mat, ring_mat) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import Data.Bits ((.&.), (.|.), (.^.));
import qualified Prelude;
import qualified Data.Bits;
import qualified Groups_List;
import qualified List;
import qualified Congruence;
import qualified Group;
import qualified Ring;
import qualified Set;
import qualified HOL;
import qualified Product_Type;
import qualified Arith;

newtype Mat a = Abs_mat (Arith.Nat, (Arith.Nat, (Arith.Nat, Arith.Nat) -> a));

newtype Vec a = Abs_vec (Arith.Nat, Arith.Nat -> a);

rep_mat ::
  forall a. Mat a -> (Arith.Nat, (Arith.Nat, (Arith.Nat, Arith.Nat) -> a));
rep_mat (Abs_mat x) = x;

index_mat :: forall a. Mat a -> (Arith.Nat, Arith.Nat) -> a;
index_mat x = snd (snd (rep_mat x));

dim_row :: forall a. Mat a -> Arith.Nat;
dim_row x = fst (rep_mat x);

undef_vec :: forall a. Arith.Nat -> a;
undef_vec i = List.nth [] i;

mk_vec :: forall a. Arith.Nat -> (Arith.Nat -> a) -> Arith.Nat -> a;
mk_vec n f =
  (\ i ->
    (if Arith.less_nat i n then f i else undef_vec (Arith.minus_nat i n)));

vec :: forall a. Arith.Nat -> (Arith.Nat -> a) -> Vec a;
vec xb xc = Abs_vec (xb, mk_vec xb xc);

col :: forall a. Mat a -> Arith.Nat -> Vec a;
col a j = vec (dim_row a) (\ i -> index_mat a (i, j));

undef_mat ::
  forall a.
    Arith.Nat ->
      Arith.Nat -> ((Arith.Nat, Arith.Nat) -> a) -> (Arith.Nat, Arith.Nat) -> a;
undef_mat nr nc f =
  (\ (i, a) ->
    List.nth
      (List.nth
        (map (\ ia -> map (\ j -> f (ia, j)) (List.upt Arith.Zero_nat nc))
          (List.upt Arith.Zero_nat nr))
        i)
      a);

mk_mat ::
  forall a.
    Arith.Nat ->
      Arith.Nat -> ((Arith.Nat, Arith.Nat) -> a) -> (Arith.Nat, Arith.Nat) -> a;
mk_mat nr nc f =
  (\ (i, j) ->
    (if Arith.less_nat i nr && Arith.less_nat j nc then f (i, j)
      else undef_mat nr nc f (i, j)));

mat ::
  forall a. Arith.Nat -> Arith.Nat -> ((Arith.Nat, Arith.Nat) -> a) -> Mat a;
mat xc xd xe = Abs_mat (xc, (xd, mk_mat xc xd xe));

dim_col :: forall a. Mat a -> Arith.Nat;
dim_col x = fst (snd (rep_mat x));

row :: forall a. Mat a -> Arith.Nat -> Vec a;
row a i = vec (dim_col a) (\ j -> index_mat a (i, j));

rep_vec :: forall a. Vec a -> (Arith.Nat, Arith.Nat -> a);
rep_vec (Abs_vec x) = x;

dim_vec :: forall a. Vec a -> Arith.Nat;
dim_vec x = fst (rep_vec x);

one_mat :: forall a. (Arith.One a, Arith.Zero a) => Arith.Nat -> Mat a;
one_mat n =
  mat n n (\ (i, j) -> (if Arith.equal_nat i j then Arith.one else Arith.zero));

vec_index :: forall a. Vec a -> Arith.Nat -> a;
vec_index x = snd (rep_vec x);

scalar_prod :: forall a. (Arith.Semiring_0 a) => Vec a -> Vec a -> a;
scalar_prod v w =
  let {
    d = Arith.minus_nat (dim_vec w) Arith.one_nat;
  } in (if Arith.less_nat d (dim_vec w)
         then Groups_List.sum_list
                (map (\ i -> Arith.times (vec_index v i) (vec_index w i))
                  (List.interval Arith.Zero_nat d))
         else Arith.zero);

times_mat :: forall a. (Arith.Semiring_0 a) => Mat a -> Mat a -> Mat a;
times_mat a b =
  mat (dim_row a) (dim_col b) (\ (i, j) -> scalar_prod (row a i) (col b j));

plus_mat :: forall a. (Arith.Plus a) => Mat a -> Mat a -> Mat a;
plus_mat a b =
  mat (dim_row b) (dim_col b)
    (\ ij -> Arith.plus (index_mat a ij) (index_mat b ij));

carrier_mat :: forall a. Arith.Nat -> Arith.Nat -> Set.Set (Mat a);
carrier_mat _ _ = error "Matrix.carrier_mat";

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

}
