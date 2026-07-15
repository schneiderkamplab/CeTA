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
import qualified Quasi_Order;
import qualified Arith;
import qualified Term_Rewriting;

showsl_arctic :: Term_Rewriting.Arctic -> String -> String;
showsl_arctic Term_Rewriting.MinInfty = Term_Rewriting.showsl_lit "-infinity";
showsl_arctic (Term_Rewriting.Num_arc i) = Term_Rewriting.showsl_int i;

showsl_list_arctic :: [Term_Rewriting.Arctic] -> String -> String;
showsl_list_arctic xs = Term_Rewriting.default_showsl_list showsl_arctic xs;

instance Term_Rewriting.Showl Term_Rewriting.Arctic where {
  showsl = showsl_arctic;
  showsl_list = showsl_list_arctic;
};

showsl_arctic_delta ::
  forall a.
    (Term_Rewriting.Showl a) => Term_Rewriting.Arctic_delta a ->
                                  String -> String;
showsl_arctic_delta Term_Rewriting.MinInfty_delta =
  Term_Rewriting.showsl_lit "-infinity";
showsl_arctic_delta (Term_Rewriting.Num_arc_delta x) = Term_Rewriting.showsl x;

showsl_list_arctic_delta ::
  forall a.
    (Term_Rewriting.Showl a) => [Term_Rewriting.Arctic_delta a] ->
                                  String -> String;
showsl_list_arctic_delta xs =
  Term_Rewriting.default_showsl_list showsl_arctic_delta xs;

instance (Term_Rewriting.Showl a) => Term_Rewriting.Showl (Term_Rewriting.Arctic_delta
                    a) where {
  showsl = showsl_arctic_delta;
  showsl_list = showsl_list_arctic_delta;
};

check_def_pos ::
  forall a.
    (Arith.Zero a,
      Quasi_Order.Ord a) => a -> Sum_Type.Sum (String -> String) ();
check_def_pos d =
  Check_Monad.check (Quasi_Order.less Arith.zero d)
    (Term_Rewriting.showsl_lit "default value must be positive");

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
      (mat_complexity n) (Term_Rewriting.showsl_lit "matrix interpretation")
      ());

check_dimensions ::
  Arith.Nat ->
    Arith.Nat ->
      Sum_Type.Sum (String -> String) () -> Sum_Type.Sum (String -> String) ();
check_dimensions n sd c =
  Error_Monad.bind c
    (\ _ ->
      Check_Monad.check
        (Arith.less_eq_nat sd n && Arith.less_nat Arith.zero_nat sd)
        (Term_Rewriting.showsl_literal
          "strict dimension must be at least 1 and less than total dimension"));

class_complexity ::
  forall a.
    (SN_Orders.Ordered_semiring_1 a) => a ->
  Arith.Nat -> Sum_Type.Sum (String -> String) ();
class_complexity a deg =
  Check_Monad.check (Quasi_Order.less_eq a Arith.one)
    (Term_Rewriting.showsl_literal "value is larger than 1");

class_lpoly_order ::
  forall a.
    (Arith.Ceq a, Arith.Ccompare a, SN_Orders.Ordered_semiring_1 a,
      Arith.Set_impl a) => a -> (a -> Bool) ->
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
      (Term_Rewriting.showsl_literal "polynomial interpretation") ());

mat_arc_complexity ::
  forall a. a -> Arith.Nat -> Sum_Type.Sum (String -> String) ();
mat_arc_complexity m deg =
  Sum_Type.Inl
    (Term_Rewriting.showsl_lit "complexity for arctic matrices not supported");

check_arc_dimension ::
  forall a.
    (Arith.Zero a,
      Quasi_Order.Ord a) => a -> Sum_Type.Sum (String -> String) ();
check_arc_dimension n =
  Check_Monad.check (Quasi_Order.less Arith.zero n)
    (Term_Rewriting.showsl_lit "dimension must be at least 1");

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
      (Term_Rewriting.showsl_lit "arctic matrix interpretation") ());

class_arc_complexity ::
  forall a. a -> Arith.Nat -> Sum_Type.Sum (String -> String) ();
class_arc_complexity a deg =
  Sum_Type.Inl
    (Term_Rewriting.showsl_literal
      "complexity for arctic semirings not supported");

class_arc_lpoly_order ::
  forall a.
    (Arith.Ceq a, Arith.Ccompare a, SN_Orders.Ordered_semiring_1 a,
      Arith.Set_impl a) => a -> (a -> Bool) ->
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
      (Term_Rewriting.showsl_lit
        "polynomial interpretation over arctic semiring")
      ());

}
