{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Matrix_Comparison(mat_mono, mat_arc_posI, mat_ge, mat_ordered_semiring,
                     mat_default, mat_both_ordered_semiring)
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
import qualified Ordered_Semiring;
import qualified Congruence;
import qualified Group;
import qualified Ring;
import qualified SN_Orders;
import qualified Orderings;
import qualified HOL;
import qualified Matrix;
import qualified List;
import qualified Arith;

mat_mono :: forall a. (a -> Bool) -> Arith.Nat -> Matrix.Mat a -> Bool;
mat_mono p sd a =
  let {
    d = Arith.minus_nat sd Arith.one_nat;
  } in (if Arith.less_nat d sd
         then List.all_interval
                (\ j ->
                  let {
                    da = Arith.minus_nat sd Arith.one_nat;
                  } in Arith.less_nat da sd &&
                         not (List.all_interval
                               (not . (\ i -> p (Matrix.index_mat a (i, j))))
                               Arith.zero_nat da))
                Arith.zero_nat d
         else True);

mat_arc_posI :: forall a. (a -> Bool) -> Matrix.Mat a -> Bool;
mat_arc_posI ap a = ap (Matrix.index_mat a (Arith.zero_nat, Arith.zero_nat));

mat_comp_all ::
  forall a. (a -> a -> Bool) -> Matrix.Mat a -> Matrix.Mat a -> Bool;
mat_comp_all r a b =
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
                                  r (Matrix.index_mat a (i, j))
                                    (Matrix.index_mat b (i, j)))
                                Arith.zero_nat da
                         else True))
                Arith.zero_nat d
         else True);

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
                                Arith.zero_nat da
                         else True))
                Arith.zero_nat d
         else True);

mat_gt ::
  forall a.
    (Orderings.Ord a) => (a -> a -> Bool) ->
                           Arith.Nat -> Matrix.Mat a -> Matrix.Mat a -> Bool;
mat_gt gt sd a b =
  mat_ge a b &&
    let {
      d = Arith.minus_nat sd Arith.one_nat;
    } in Arith.less_nat d sd &&
           not (List.all_interval
                 (not .
                   (\ i ->
                     let {
                       da = Arith.minus_nat sd Arith.one_nat;
                     } in Arith.less_nat da sd &&
                            not (List.all_interval
                                  (not .
                                    (\ j ->
                                      gt (Matrix.index_mat a (i, j))
(Matrix.index_mat b (i, j))))
                                  Arith.zero_nat da)))
                 Arith.zero_nat d);

mat_max ::
  forall a. (Orderings.Ord a) => Matrix.Mat a -> Matrix.Mat a -> Matrix.Mat a;
mat_max a b =
  Matrix.mat (Matrix.dim_row a) (Matrix.dim_col a)
    (\ ij -> Orderings.max (Matrix.index_mat a ij) (Matrix.index_mat b ij));

mat_ordered_semiring ::
  forall a b.
    (SN_Orders.Ordered_semiring_1 a) => Arith.Nat ->
  Arith.Nat ->
    (a -> a -> Bool) ->
      b -> Congruence.Partial_object_ext (Matrix.Mat a)
             (Group.Monoid_ext (Matrix.Mat a)
               (Ring.Ring_ext (Matrix.Mat a)
                 (Ordered_Semiring.Ordered_semiring_ext (Matrix.Mat a) b)));
mat_ordered_semiring n sd gt b =
  Matrix.ring_mat HOL.Type n
    (Ordered_Semiring.Ordered_semiring_ext mat_ge (mat_gt gt sd) mat_max b);

mat_default :: forall a. (Arith.Zero a) => a -> Arith.Nat -> Matrix.Mat a;
mat_default d n =
  Matrix.mat n n (\ (i, j) -> (if Arith.equal_nat i j then d else Arith.zero));

mat_both_ordered_semiring ::
  forall a b.
    (SN_Orders.Ordered_semiring_1 a) => Arith.Nat ->
  (a -> a -> Bool) ->
    b -> Congruence.Partial_object_ext (Matrix.Mat a)
           (Group.Monoid_ext (Matrix.Mat a)
             (Ring.Ring_ext (Matrix.Mat a)
               (Ordered_Semiring.Ordered_semiring_ext (Matrix.Mat a) b)));
mat_both_ordered_semiring n gt b =
  Matrix.ring_mat HOL.Type n
    (Ordered_Semiring.Ordered_semiring_ext mat_ge (mat_comp_all gt) mat_max b);

}
