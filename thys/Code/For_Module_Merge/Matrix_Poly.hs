{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Matrix_Poly(check_def_pos, mat_lpoly_order, check_dimensions,
               class_lpoly_order, check_arc_dimension, mat_arc_lpoly_order,
               class_arc_lpoly_order)
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
import qualified HOL;
import qualified Collection_Order;
import qualified Set_Impl;
import qualified Collection_Eq;
import qualified Error_Monad;
import qualified Matrix_Comparison;
import qualified Linear_Poly_Complexity;
import qualified Ordered_Semiring;
import qualified Congruence;
import qualified Group;
import qualified Ring;
import qualified Ring_Hom_Matrix;
import qualified SN_Orders;
import qualified Jordan_Normal_Form_Complexity_Approximation;
import qualified Matrix;
import qualified Complexity_Carrier;
import qualified Check_Monad;
import qualified Sum_Type;
import qualified Orderings;
import qualified Arith;
import qualified SN_Order_Carrier;
import qualified Shows_Literal;

showsl_arctic :: SN_Order_Carrier.Arctic -> String -> String;
showsl_arctic SN_Order_Carrier.MinInfty = Shows_Literal.showsl_lit "-infinity";
showsl_arctic (SN_Order_Carrier.Num_arc i) = Shows_Literal.showsl_int i;

showsl_list_arctic :: [SN_Order_Carrier.Arctic] -> String -> String;
showsl_list_arctic xs = Shows_Literal.default_showsl_list showsl_arctic xs;

instance Shows_Literal.Showl SN_Order_Carrier.Arctic where {
  showsl = showsl_arctic;
  showsl_list = showsl_list_arctic;
};

showsl_arctic_delta ::
  forall a.
    (Shows_Literal.Showl a) => SN_Order_Carrier.Arctic_delta a ->
                                 String -> String;
showsl_arctic_delta SN_Order_Carrier.MinInfty_delta =
  Shows_Literal.showsl_lit "-infinity";
showsl_arctic_delta (SN_Order_Carrier.Num_arc_delta x) = Shows_Literal.showsl x;

showsl_list_arctic_delta ::
  forall a.
    (Shows_Literal.Showl a) => [SN_Order_Carrier.Arctic_delta a] ->
                                 String -> String;
showsl_list_arctic_delta xs =
  Shows_Literal.default_showsl_list showsl_arctic_delta xs;

instance (Shows_Literal.Showl a) => Shows_Literal.Showl (SN_Order_Carrier.Arctic_delta
                  a) where {
  showsl = showsl_arctic_delta;
  showsl_list = showsl_list_arctic_delta;
};

check_def_pos ::
  forall a.
    (Arith.Zero a, Orderings.Ord a) => a -> Sum_Type.Sum (String -> String) ();
check_def_pos d =
  Check_Monad.check (Orderings.less Arith.zero d)
    (Shows_Literal.showsl_lit "default value must be positive");

mat_complexity ::
  forall a.
    (Complexity_Carrier.Large_real_ordered_semiring_1 a) => Arith.Nat ->
                      Matrix.Mat a ->
                        Arith.Nat -> Sum_Type.Sum (String -> String) ();
mat_complexity n m d =
  Jordan_Normal_Form_Complexity_Approximation.mat_estimate_complexity_jb
    (Arith.suc d) m;

mat_lpoly_order ::
  forall a.
    (Complexity_Carrier.Large_real_ordered_semiring_1 a) => Arith.Nat ->
                      Arith.Nat ->
                        a -> (a -> Bool) ->
                               (a -> a -> Bool) ->
                                 Congruence.Partial_object_ext (Matrix.Mat a)
                                   (Group.Monoid_ext (Matrix.Mat a)
                                     (Ring.Ring_ext (Matrix.Mat a)
                                       (Ordered_Semiring.Ordered_semiring_ext
 (Matrix.Mat a)
 (Linear_Poly_Complexity.Lpoly_order_semiring_ext (Matrix.Mat a) ()))));
mat_lpoly_order n sd def cmon gtt =
  Matrix_Comparison.mat_ordered_semiring n sd gtt
    (Linear_Poly_Complexity.Lpoly_order_semiring_ext True
      (Matrix_Comparison.mat_default def n) (\ _ -> True)
      (Matrix_Comparison.mat_mono cmon sd) (\ _ -> Arith.zero_nat)
      (mat_complexity n) (Shows_Literal.showsl_lit "matrix interpretation") ());

check_dimensions ::
  Arith.Nat ->
    Arith.Nat ->
      Sum_Type.Sum (String -> String) () -> Sum_Type.Sum (String -> String) ();
check_dimensions n sd c =
  Error_Monad.bind c
    (\ _ ->
      Check_Monad.check
        (Arith.less_eq_nat sd n && Arith.less_nat Arith.zero_nat sd)
        (Shows_Literal.showsl_literal
          "strict dimension must be at least 1 and less than total dimension"));

class_complexity ::
  forall a.
    (SN_Orders.Ordered_semiring_1 a) => a ->
  Arith.Nat -> Sum_Type.Sum (String -> String) ();
class_complexity a deg =
  Check_Monad.check (Orderings.less_eq a Arith.one)
    (Shows_Literal.showsl_literal "value is larger than 1");

class_lpoly_order ::
  forall a.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a,
      SN_Orders.Ordered_semiring_1 a,
      Set_Impl.Set_impl a) => a -> (a -> Bool) ->
                                     (a -> a -> Bool) ->
                                       Congruence.Partial_object_ext a
 (Group.Monoid_ext a
   (Ring.Ring_ext a
     (Ordered_Semiring.Ordered_semiring_ext a
       (Linear_Poly_Complexity.Lpoly_order_semiring_ext a ()))));
class_lpoly_order def cmon gtt =
  Ordered_Semiring.class_ordered_semiring HOL.Type gtt
    (Linear_Poly_Complexity.Lpoly_order_semiring_ext True def (\ _ -> True) cmon
      (\ _ -> Arith.zero_nat) class_complexity
      (Shows_Literal.showsl_literal "polynomial interpretation") ());

mat_arc_complexity ::
  forall a. a -> Arith.Nat -> Sum_Type.Sum (String -> String) ();
mat_arc_complexity m deg =
  Sum_Type.Inl
    (Shows_Literal.showsl_lit "complexity for arctic matrices not supported");

check_arc_dimension ::
  forall a.
    (Arith.Zero a, Orderings.Ord a) => a -> Sum_Type.Sum (String -> String) ();
check_arc_dimension n =
  Check_Monad.check (Orderings.less Arith.zero n)
    (Shows_Literal.showsl_lit "dimension must be at least 1");

mat_arc_lpoly_order ::
  forall a.
    (SN_Orders.Ordered_semiring_1 a) => Arith.Nat ->
  a -> (a -> Bool) ->
         (a -> a -> Bool) ->
           Congruence.Partial_object_ext (Matrix.Mat a)
             (Group.Monoid_ext (Matrix.Mat a)
               (Ring.Ring_ext (Matrix.Mat a)
                 (Ordered_Semiring.Ordered_semiring_ext (Matrix.Mat a)
                   (Linear_Poly_Complexity.Lpoly_order_semiring_ext
                     (Matrix.Mat a) ()))));
mat_arc_lpoly_order n def apos gtt =
  Matrix_Comparison.mat_both_ordered_semiring n gtt
    (Linear_Poly_Complexity.Lpoly_order_semiring_ext False
      (Matrix_Comparison.mat_default def n)
      (Matrix_Comparison.mat_arc_posI apos) (\ _ -> False)
      (\ _ -> Arith.zero_nat) mat_arc_complexity
      (Shows_Literal.showsl_lit "arctic matrix interpretation") ());

class_arc_complexity ::
  forall a. a -> Arith.Nat -> Sum_Type.Sum (String -> String) ();
class_arc_complexity a deg =
  Sum_Type.Inl
    (Shows_Literal.showsl_literal
      "complexity for arctic semirings not supported");

class_arc_lpoly_order ::
  forall a.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a,
      SN_Orders.Ordered_semiring_1 a,
      Set_Impl.Set_impl a) => a -> (a -> Bool) ->
                                     (a -> a -> Bool) ->
                                       Congruence.Partial_object_ext a
 (Group.Monoid_ext a
   (Ring.Ring_ext a
     (Ordered_Semiring.Ordered_semiring_ext a
       (Linear_Poly_Complexity.Lpoly_order_semiring_ext a ()))));
class_arc_lpoly_order def apos gtt =
  Ordered_Semiring.class_ordered_semiring HOL.Type gtt
    (Linear_Poly_Complexity.Lpoly_order_semiring_ext False def apos
      (\ _ -> False) (\ _ -> Arith.zero_nat) class_arc_complexity
      (Shows_Literal.showsl_lit
        "polynomial interpretation over arctic semiring")
      ());

}
