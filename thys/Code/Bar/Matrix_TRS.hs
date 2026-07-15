{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Matrix_TRS(default_mat_inter, matsemiring) where {

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
import qualified Matrix_Comparison;
import qualified Linear_Poly_Interpretation;
import qualified Ordered_Semiring;
import qualified Congruence;
import qualified Group;
import qualified Ring;
import qualified SN_Orders;
import qualified Quasi_Order;
import qualified Matrix;
import qualified Arith;

default_mat_inter ::
  forall a.
    (Arith.Ring_1 a) => Arith.Nat ->
                          Arith.Nat -> ([Matrix.Mat a], Matrix.Mat a);
default_mat_inter n n1 =
  (Arith.replicate n1 (Matrix.one_mat n), Matrix.one_mat n);

matsemiring ::
  forall a.
    (Arith.Ordered_semiring_0 a, Arith.Ring_1 a,
      SN_Orders.Ordered_semiring_1 a) => Arith.Nat ->
   (a -> a -> Bool) ->
     Congruence.Partial_object_ext (Matrix.Mat a)
       (Group.Monoid_ext (Matrix.Mat a)
         (Ring.Ring_ext (Matrix.Mat a)
           (Ordered_Semiring.Ordered_semiring_ext (Matrix.Mat a)
             (Linear_Poly_Interpretation.Explicit_minus_semiring_ext
               (Matrix.Mat a) ()))));
matsemiring n gt =
  Congruence.Partial_object_ext (Matrix.carrier_mat n n)
    (Group.Monoid_ext Matrix.times_mat (Matrix.one_mat n)
      (Ring.Ring_ext (Matrix.zero_mat n n) Matrix.plus_mat
        (Ordered_Semiring.Ordered_semiring_ext Matrix_Comparison.mat_ge
          (Matrix_Comparison.mat_gt gt n)
          (\ a b -> (if Matrix.less_mat b a then a else b))
          (Linear_Poly_Interpretation.Explicit_minus_semiring_ext
            Matrix.uminus_mat ()))));

}
