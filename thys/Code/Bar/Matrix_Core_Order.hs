{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Matrix_Core_Order(oneE_I, iI_list_to_II, inter_lpoly_N, poly_of_rule_N,
                     check_lpoly_N_N, check_lpoly_N_E_I, check_lpoly_N_P_I)
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
import qualified Matrix_Comparison;
import qualified Quasi_Order;
import qualified Term_Rewriting;
import qualified Map;
import qualified Congruence;
import qualified Linear_Polynomial;
import qualified Group;
import qualified Ring;
import qualified HOL;
import qualified SN_Orders;
import qualified Arith;
import qualified Matrix;

sum_list_lpoly ::
  forall a b.
    (Eq a, Arith.Ordered_ab_group_add b, Eq b, Arith.Ordered_semiring_0 b,
      Arith.Ring_1 b, Arith.Zero_less_one b,
      SN_Orders.Ordered_semiring_1 b) => Arith.Nat ->
   [Linear_Polynomial.L_poly a (Matrix.Mat b)] ->
     Linear_Polynomial.L_poly a (Matrix.Mat b);
sum_list_lpoly n =
  Arith.rec_list
    (Linear_Polynomial.LPoly (Ring.zero (Matrix.ring_mat HOL.Type n ())) [])
    (\ x _ -> Linear_Polynomial.sum_lpoly (Matrix.ring_mat HOL.Type n ()) x);

alphap ::
  forall a b c.
    (Arith.Ordered_ab_group_add b, Eq b, Arith.Ordered_semiring_0 b,
      Arith.Ring_1 b, Arith.Zero_less_one b, SN_Orders.Ordered_semiring_1 b,
      Eq c) => Arith.Nat ->
                 ((a, Arith.Nat) -> ([Matrix.Mat b], Matrix.Mat b)) ->
                   a -> [Linear_Polynomial.L_poly c (Matrix.Mat b)] ->
                          Linear_Polynomial.L_poly c (Matrix.Mat b);
alphap n ii f lps =
  (case ii (f, Arith.size_list lps) of {
    (cs, c) ->
      Linear_Polynomial.sum_lpoly (Matrix.ring_mat HOL.Type n ())
        (sum_list_lpoly n
          (map (\ (a, b) ->
                 Linear_Polynomial.mul_lpoly (Matrix.ring_mat HOL.Type n ()) a
                   b)
            (zip cs lps)))
        (Linear_Polynomial.LPoly c []);
  });

sub_lpoly ::
  forall a b.
    (Eq a, Arith.Ordered_ab_group_add b, Eq b, Arith.Ordered_semiring_0 b,
      Arith.Ring_1 b, Arith.Zero_less_one b,
      SN_Orders.Ordered_semiring_1 b) => Arith.Nat ->
   Linear_Polynomial.L_poly a (Matrix.Mat b) ->
     Linear_Polynomial.L_poly a (Matrix.Mat b) ->
       Linear_Polynomial.L_poly a (Matrix.Mat b);
sub_lpoly n p q =
  Linear_Polynomial.sum_lpoly (Matrix.ring_mat HOL.Type n ()) p
    (Linear_Polynomial.mul_lpoly (Matrix.ring_mat HOL.Type n ())
      (Matrix.uminus_mat (Matrix.one_mat n)) q);

default_II ::
  forall a b.
    (Arith.Ordered_ab_group_add a, Arith.Ordered_semiring_0 a, Arith.Ring_1 a,
      Arith.Zero_less_one a,
      SN_Orders.Ordered_semiring_1 a) => Arith.Nat ->
   a -> (b, Arith.Nat) -> ([Matrix.Mat a], Matrix.Mat a);
default_II n delta fk =
  let {
    k = snd fk;
  } in (Arith.replicate k (Matrix.one_mat n),
         Matrix.smult_mat (Arith.plus delta Arith.one) (Matrix.one_mat n));

inter_lpoly ::
  forall a b.
    (Arith.Ordered_ab_group_add b, Eq b, Arith.Ordered_semiring_0 b,
      Arith.Ring_1 b, Arith.Zero_less_one b,
      SN_Orders.Ordered_semiring_1 b) => Arith.Nat ->
   ((a, Arith.Nat) -> ([Matrix.Mat b], Matrix.Mat b)) ->
     (a, Arith.Nat) -> Linear_Polynomial.L_poly Arith.Nat (Matrix.Mat b);
inter_lpoly n ii fk =
  (case ii fk of {
    (cs, c) ->
      Linear_Polynomial.sum_lpoly (Matrix.ring_mat HOL.Type n ())
        (sum_list_lpoly n
          (map (\ (x, y) ->
                 Linear_Polynomial.mul_lpoly (Matrix.ring_mat HOL.Type n ()) x
                   (Linear_Polynomial.var_lpoly (Matrix.ring_mat HOL.Type n ())
                     y))
            (zip cs (Arith.upt Arith.zero_nat (Arith.size_list cs)))))
        (Linear_Polynomial.LPoly c []);
  });

subst_lpoly ::
  forall a b c.
    (Eq b, Arith.Ordered_ab_group_add c, Eq c, Arith.Ordered_semiring_0 c,
      Arith.Ring_1 c, Arith.Zero_less_one c,
      SN_Orders.Ordered_semiring_1 c) => Arith.Nat ->
   (a -> Linear_Polynomial.L_poly b (Matrix.Mat c)) ->
     Linear_Polynomial.L_poly a (Matrix.Mat c) ->
       Linear_Polynomial.L_poly b (Matrix.Mat c);
subst_lpoly n sigma (Linear_Polynomial.LPoly c cs) =
  Linear_Polynomial.sum_lpoly (Matrix.ring_mat HOL.Type n ())
    (sum_list_lpoly n
      (map (\ (x, cx) ->
             Linear_Polynomial.mul_lpoly (Matrix.ring_mat HOL.Type n ()) cx
               (sigma x))
        cs))
    (Linear_Polynomial.LPoly c []);

oneE_I ::
  forall a.
    (Arith.Ordered_ab_group_add a, Arith.Ordered_semiring_0 a, Arith.Ring_1 a,
      Arith.Zero_less_one a,
      SN_Orders.Ordered_semiring_1 a) => Arith.Nat ->
   Arith.Set Arith.Nat -> Matrix.Mat a;
oneE_I n i =
  Matrix.mat n n
    (\ (ia, j) ->
      (if Arith.equal_nat ia j && Arith.member ia i then Arith.one
        else Arith.zero));

iI_list_to_II ::
  forall a b.
    (Arith.Ordered_ab_group_add a, Arith.Ordered_semiring_0 a, Arith.Ring_1 a,
      Arith.Zero_less_one a, SN_Orders.Ordered_semiring_1 a,
      Eq b) => Arith.Nat ->
                 a -> [((b, Arith.Nat), ([Matrix.Mat a], Matrix.Mat a))] ->
                        (b, Arith.Nat) -> ([Matrix.Mat a], Matrix.Mat a);
iI_list_to_II n delta fk_cs fk = (case Map.map_of fk_cs fk of {
                                   Nothing -> default_II n delta fk;
                                   Just i -> i;
                                 });

switchE_IN ::
  forall a b.
    (Eq a, Arith.Ordered_ab_group_add b, Eq b, Arith.Ordered_semiring_0 b,
      Arith.Ring_1 b, Arith.Zero_less_one b,
      SN_Orders.Ordered_semiring_1 b) => Arith.Nat ->
   Arith.Set Arith.Nat ->
     Linear_Polynomial.L_poly a (Matrix.Mat b) ->
       Linear_Polynomial.L_poly a (Matrix.Mat b);
switchE_IN n i p =
  subst_lpoly n
    (\ x ->
      Linear_Polynomial.sum_lpoly (Matrix.ring_mat HOL.Type n ())
        (Linear_Polynomial.var_lpoly (Matrix.ring_mat HOL.Type n ()) x)
        (Linear_Polynomial.LPoly (oneE_I n i) []))
    p;

inter_lpoly_N ::
  forall a b.
    (Arith.Ordered_ab_group_add b, Eq b, Arith.Ordered_semiring_0 b,
      Arith.Ring_1 b, Arith.Zero_less_one b,
      SN_Orders.Ordered_semiring_1 b) => Arith.Nat ->
   ((a, Arith.Nat) -> ([Matrix.Mat b], Matrix.Mat b)) ->
     Arith.Set Arith.Nat ->
       (a, Arith.Nat) -> Linear_Polynomial.L_poly Arith.Nat (Matrix.Mat b);
inter_lpoly_N n ii i = switchE_IN n i . inter_lpoly n ii;

poly_of_rule_N ::
  forall a b c.
    (Arith.Ordered_ab_group_add b, Eq b, Arith.Ordered_semiring_0 b,
      Arith.Ring_1 b, Arith.Zero_less_one b, SN_Orders.Ordered_semiring_1 b,
      Eq c) => Arith.Nat ->
                 ((a, Arith.Nat) -> ([Matrix.Mat b], Matrix.Mat b)) ->
                   Arith.Set Arith.Nat ->
                     (Term_Rewriting.Term a c, Term_Rewriting.Term a c) ->
                       Linear_Polynomial.L_poly c (Matrix.Mat b);
poly_of_rule_N n ii i (l, r) =
  switchE_IN n i
    (sub_lpoly n
      (Term_Rewriting.eval_term (alphap n ii) l
        (Linear_Polynomial.var_lpoly (Matrix.ring_mat HOL.Type n ())))
      (Term_Rewriting.eval_term (alphap n ii) r
        (Linear_Polynomial.var_lpoly (Matrix.ring_mat HOL.Type n ()))));

check_lpoly_generic ::
  forall a b.
    (Arith.Ordered_ab_group_add a, Arith.Ordered_semiring_0 a, Arith.Ring_1 a,
      Arith.Zero_less_one a,
      SN_Orders.Ordered_semiring_1 a) => Arith.Nat ->
   (Matrix.Mat a -> Bool) -> Linear_Polynomial.L_poly b (Matrix.Mat a) -> Bool;
check_lpoly_generic n cond (Linear_Polynomial.LPoly c cs) =
  cond c &&
    all (\ xci -> Matrix_Comparison.mat_ge (snd xci) (Matrix.zero_mat n n)) cs;

check_lpoly_N_N ::
  forall a b.
    (Arith.Ordered_ab_group_add b, Arith.Ordered_semiring_0 b, Arith.Ring_1 b,
      Arith.Zero_less_one b,
      SN_Orders.Ordered_semiring_1 b) => Arith.Nat ->
   Linear_Polynomial.L_poly a (Matrix.Mat b) -> Bool;
check_lpoly_N_N n =
  check_lpoly_generic n
    (\ a -> Matrix_Comparison.mat_ge a (Matrix.zero_mat n n));

check_lpoly_N_E_I ::
  forall a b.
    (Arith.Ordered_ab_group_add b, Arith.Ordered_semiring_0 b, Arith.Ring_1 b,
      Arith.Zero_less_one b,
      SN_Orders.Ordered_semiring_1 b) => Arith.Nat ->
   Arith.Set Arith.Nat -> Linear_Polynomial.L_poly a (Matrix.Mat b) -> Bool;
check_lpoly_N_E_I n i =
  check_lpoly_generic n (\ a -> Matrix_Comparison.mat_ge a (oneE_I n i));

check_lpoly_N_P_I ::
  forall a b.
    (Arith.Ordered_ab_group_add a, Arith.Ordered_semiring_0 a, Arith.Ring_1 a,
      Arith.Zero_less_one a,
      SN_Orders.Ordered_semiring_1 a) => Arith.Nat ->
   a -> [Arith.Nat] -> Linear_Polynomial.L_poly b (Matrix.Mat a) -> Bool;
check_lpoly_N_P_I n delta il =
  check_lpoly_generic n
    (\ a ->
      Matrix_Comparison.mat_ge a (Matrix.zero_mat n n) &&
        any (\ i ->
              any (\ j -> Quasi_Order.less_eq delta (Matrix.index_mat a (i, j)))
                il)
          il);

}
