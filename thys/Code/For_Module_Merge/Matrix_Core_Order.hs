{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Matrix_Core_Order(SN_delta_order, core_mat_af, inter_lpoly, oneE_I,
                     check_lpoly_EI_N, check_lpoly_EI_EI, check_lpoly_EI_PI,
                     alpha_list_to_Alpha, alpha_lhs_minus_rhs)
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
import qualified Term;
import qualified Option;
import qualified Map;
import qualified Matrix_Comparison;
import qualified Set;
import qualified Collection_Order;
import qualified Set_Impl;
import qualified Collection_Eq;
import qualified List;
import qualified Product_Type;
import qualified Congruence;
import qualified Linear_Polynomial;
import qualified Group;
import qualified Ring;
import qualified Matrix;
import qualified HOL;
import qualified Matrix_IArray_Impl;
import qualified Orderings;
import qualified SN_Orders;
import qualified SN_Order_Carrier;
import qualified Arith;

class (Arith.Linordered_idom a,
        SN_Orders.Ordered_semiring_1 a) => SN_delta_order a where {
};

instance SN_delta_order Arith.Int where {
};

alphap ::
  forall a b c.
    (Eq b, SN_delta_order b,
      Eq c) => Arith.Nat ->
                 ((a, Arith.Nat) -> ([Matrix.Mat b], Matrix.Mat b)) ->
                   a -> [Linear_Polynomial.L_poly c (Matrix.Mat b)] ->
                          Linear_Polynomial.L_poly c (Matrix.Mat b);
alphap n alpha f lps =
  (case alpha (f, List.size_list lps) of {
    (cs, c) ->
      Linear_Polynomial.sum_lpoly (Matrix.ring_mat HOL.Type n ())
        (Linear_Polynomial.sum_list_lpoly (Matrix.ring_mat HOL.Type n ())
          (map (\ (a, b) ->
                 Linear_Polynomial.mul_lpoly (Matrix.ring_mat HOL.Type n ()) a
                   b)
            (zip cs lps)))
        (Linear_Polynomial.LPoly c []);
  });

sub_lpoly ::
  forall a b.
    (Eq a, Eq b,
      SN_delta_order b) => Arith.Nat ->
                             Linear_Polynomial.L_poly a (Matrix.Mat b) ->
                               Linear_Polynomial.L_poly a (Matrix.Mat b) ->
                                 Linear_Polynomial.L_poly a (Matrix.Mat b);
sub_lpoly n p q =
  Linear_Polynomial.sum_lpoly (Matrix.ring_mat HOL.Type n ()) p
    (Linear_Polynomial.mul_lpoly (Matrix.ring_mat HOL.Type n ())
      (Matrix.uminus_mat (Matrix.one_mat n)) q);

core_mat_af ::
  forall a b.
    (Eq b,
      SN_delta_order b) => Arith.Nat ->
                             ((a, Arith.Nat) ->
                               ([Matrix.Mat b], Matrix.Mat b)) ->
                               (a, Arith.Nat) -> Set.Set Arith.Nat;
core_mat_af n alpha f =
  (case alpha f of {
    (cs, _) ->
      List.set
        (List.map_filter
          (\ x ->
            (if not (Matrix_IArray_Impl.equal_mat (snd x) (Matrix.zero_mat n n))
              then Just (fst x) else Nothing))
          (zip (List.upt Arith.zero_nat (List.size_list cs)) cs));
  });

inter_lpoly ::
  forall a b.
    (Eq b,
      SN_delta_order b) => Arith.Nat ->
                             ((a, Arith.Nat) ->
                               ([Matrix.Mat b], Matrix.Mat b)) ->
                               (a, Arith.Nat) ->
                                 Linear_Polynomial.L_poly Arith.Nat
                                   (Matrix.Mat b);
inter_lpoly n alpha fk =
  (case alpha fk of {
    (cs, c) ->
      Linear_Polynomial.sum_lpoly (Matrix.ring_mat HOL.Type n ())
        (Linear_Polynomial.sum_list_lpoly (Matrix.ring_mat HOL.Type n ())
          (map (\ (x, y) ->
                 Linear_Polynomial.mul_lpoly (Matrix.ring_mat HOL.Type n ()) x
                   (Linear_Polynomial.var_lpoly (Matrix.ring_mat HOL.Type n ())
                     y))
            (zip cs (List.upt Arith.zero_nat (List.size_list cs)))))
        (Linear_Polynomial.LPoly c []);
  });

oneE_I ::
  forall a.
    (SN_delta_order a) => Arith.Nat -> Set.Set Arith.Nat -> Matrix.Mat a;
oneE_I n i =
  Matrix.mat n n
    (\ (ia, j) ->
      (if Arith.equal_nat ia j && Set.member ia i then Arith.one
        else Arith.zero));

default_Alpha ::
  forall a b.
    (SN_delta_order a) => Arith.Nat ->
                            Matrix.Mat a ->
                              (b, Arith.Nat) -> ([Matrix.Mat a], Matrix.Mat a);
default_Alpha n def fk = let {
                           k = snd fk;
                         } in (List.replicate k (Matrix.one_mat n), def);

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

check_lpoly_EI_N ::
  forall a b.
    (SN_delta_order b) => Arith.Nat ->
                            Set.Set Arith.Nat ->
                              Linear_Polynomial.L_poly a (Matrix.Mat b) -> Bool;
check_lpoly_EI_N n i =
  check_lpoly_generic_EI n i
    (\ a -> Matrix_Comparison.mat_ge a (Matrix.zero_mat n n));

check_lpoly_EI_EI ::
  forall a b.
    (SN_delta_order b) => Arith.Nat ->
                            Set.Set Arith.Nat ->
                              Linear_Polynomial.L_poly a (Matrix.Mat b) -> Bool;
check_lpoly_EI_EI n i =
  check_lpoly_generic_EI n i (\ a -> Matrix_Comparison.mat_ge a (oneE_I n i));

check_lpoly_EI_PI ::
  forall a b.
    (SN_delta_order a) => Arith.Nat ->
                            a -> Set.Set Arith.Nat ->
                                   [Arith.Nat] ->
                                     Linear_Polynomial.L_poly b
                                       (Matrix.Mat a) ->
                                       Bool;
check_lpoly_EI_PI n delta i il =
  check_lpoly_generic_EI n i
    (\ a ->
      Matrix_Comparison.mat_ge a (Matrix.zero_mat n n) &&
        any (\ ia ->
              any (\ j -> Orderings.less_eq delta (Matrix.index_mat a (ia, j)))
                il)
          il);

alpha_list_to_Alpha ::
  forall a b.
    (SN_delta_order a,
      Eq b) => Arith.Nat ->
                 Matrix.Mat a ->
                   [((b, Arith.Nat), ([Matrix.Mat a], Matrix.Mat a))] ->
                     (b, Arith.Nat) -> ([Matrix.Mat a], Matrix.Mat a);
alpha_list_to_Alpha n def fk_cs fk = (case Map.map_of fk_cs fk of {
                                       Nothing -> default_Alpha n def fk;
                                       Just i -> i;
                                     });

alpha_lhs_minus_rhs ::
  forall a b c.
    (Eq b, SN_delta_order b,
      Eq c) => Arith.Nat ->
                 ((a, Arith.Nat) -> ([Matrix.Mat b], Matrix.Mat b)) ->
                   (Term.Term a c, Term.Term a c) ->
                     Linear_Polynomial.L_poly c (Matrix.Mat b);
alpha_lhs_minus_rhs n alpha (l, r) =
  sub_lpoly n
    (Term.eval_term (alphap n alpha) l
      (Linear_Polynomial.var_lpoly (Matrix.ring_mat HOL.Type n ())))
    (Term.eval_term (alphap n alpha) r
      (Linear_Polynomial.var_lpoly (Matrix.ring_mat HOL.Type n ())));

}
