{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Matrix_Core_Order(SN_delta_order, check_lpoly_generic_EI) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import Data.Bits ((.&.), (.|.), (.^.));
import qualified Prelude;
import qualified Data.Bits;
import qualified Matrix_Comparison;
import qualified Congruence;
import qualified Linear_Polynomial;
import qualified Group;
import qualified Ring;
import qualified HOL;
import qualified Product_Type;
import qualified Matrix;
import qualified Set;
import qualified SN_Orders;
import qualified Arith;

class (Arith.Linordered_idom a,
        SN_Orders.Ordered_semiring_1 a) => SN_delta_order a where {
};

oneE_I ::
  forall a.
    (SN_delta_order a) => Arith.Nat -> Set.Set Arith.Nat -> Matrix.Mat a;
oneE_I n i =
  Matrix.mat n n
    (\ (ia, j) ->
      (if Arith.equal_nat ia j && Set.member ia i then Arith.one
        else Arith.zero));

check_lpoly_generic_EI ::
  forall a b.
    (SN_delta_order a) => Arith.Nat ->
                            Set.Set Arith.Nat ->
                              (Matrix.Mat a -> Bool) ->
                                Linear_Polynomial.L_poly b (Matrix.Mat a) ->
                                  Bool;
check_lpoly_generic_EI n i cond (Linear_Polynomial.LPoly c cs) =
  cond (Linear_Polynomial.eval_lpoly (Matrix.ring_mat HOL.Type n ())
         (\ _ -> oneE_I n i) (Linear_Polynomial.LPoly c cs)) &&
    all (\ xci -> Matrix_Comparison.mat_ge (snd xci) (Matrix.zero_mat n n)) cs;

}
