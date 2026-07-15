{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Real(Real(..), equal_real, times_real, uminus_real, zero_real, plus_real,
        minus_real, less_real, abs_real, one_real, sgn_real, divide_real,
        less_eq_real, floor_real, ratreal)
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
import qualified Real_Impl;
import qualified Rat;
import qualified Real_Unique_Impl;
import qualified Matrix_Core_Order;
import qualified Archimedean_Field;
import qualified Max_Polynomial_Aux;
import qualified SN_Orders;
import qualified Norms;
import qualified Missing_Lemmas;
import qualified Quasi_Order;
import qualified Orderings;
import qualified Unique_Factorization;
import qualified Arith;

newtype Real = Real_of_u Real_Unique_Impl.Mini_alg_unique;

equal_real :: Real -> Real -> Bool;
equal_real (Real_of_u r1) (Real_of_u r2) = Real_Unique_Impl.mau_equal r1 r2;

instance Eq Real where {
  a == b = equal_real a b;
};

times_real :: Real -> Real -> Real;
times_real (Real_of_u r1) (Real_of_u r2) =
  (if Real_Unique_Impl.mau_compatible r1 r2
    then Real_of_u (Real_Unique_Impl.mau_times r1 r2)
    else (error :: forall a. String -> (() -> a) -> a) "different base"
           (\ _ -> times_real (Real_of_u r1) (Real_of_u r2)));

instance Arith.Times Real where {
  times = times_real;
};

instance Arith.Dvd Real where {
};

uminus_real :: Real -> Real;
uminus_real (Real_of_u r) = Real_of_u (Real_Unique_Impl.mau_uminus r);

zero_real :: Real;
zero_real = Real_of_u (Real_Unique_Impl.mau_of_rat Rat.zero_rat);

plus_real :: Real -> Real -> Real;
plus_real (Real_of_u r1) (Real_of_u r2) =
  (if Real_Unique_Impl.mau_compatible r1 r2
    then Real_of_u (Real_Unique_Impl.mau_plus r1 r2)
    else (error :: forall a. String -> (() -> a) -> a) "different base"
           (\ _ -> plus_real (Real_of_u r1) (Real_of_u r2)));

minus_real :: Real -> Real -> Real;
minus_real x y = plus_real x (uminus_real y);

less_real :: Real -> Real -> Bool;
less_real (Real_of_u x) (Real_of_u y) =
  not (equal_real (Real_of_u x) (Real_of_u y)) &&
    (if Real_Unique_Impl.mau_compatible x y
      then Real_Impl.ge_0 (minus_real (Real_of_u y) (Real_of_u x))
      else Real_Unique_Impl.real_lt (Real_of_u x) (Real_of_u y));

abs_real :: Real -> Real;
abs_real a = (if less_real a zero_real then uminus_real a else a);

instance Arith.Abs Real where {
  absa = abs_real;
};

one_real :: Real;
one_real = Real_of_u (Real_Unique_Impl.mau_of_rat Rat.one_rat);

instance Arith.One Real where {
  one = one_real;
};

sgn_real :: Real -> Real;
sgn_real a =
  (if equal_real a zero_real then zero_real
    else (if less_real zero_real a then one_real else uminus_real one_real));

instance Arith.Sgn Real where {
  sgn = sgn_real;
};

instance Arith.Plus Real where {
  plus = plus_real;
};

instance Arith.Semigroup_add Real where {
};

instance Arith.Cancel_semigroup_add Real where {
};

instance Arith.Ab_semigroup_add Real where {
};

instance Arith.Minus Real where {
  minus = minus_real;
};

instance Arith.Cancel_ab_semigroup_add Real where {
};

instance Arith.Zero Real where {
  zero = zero_real;
};

instance Arith.Monoid_add Real where {
};

instance Arith.Comm_monoid_add Real where {
};

instance Arith.Cancel_comm_monoid_add Real where {
};

instance Arith.Mult_zero Real where {
};

instance Arith.Semigroup_mult Real where {
};

instance Arith.Semiring Real where {
};

instance Arith.Semiring_0 Real where {
};

instance Arith.Semiring_0_cancel Real where {
};

instance Arith.Ab_semigroup_mult Real where {
};

instance Arith.Comm_semiring Real where {
};

instance Arith.Comm_semiring_0 Real where {
};

instance Arith.Comm_semiring_0_cancel Real where {
};

instance Arith.Power Real where {
};

instance Arith.Monoid_mult Real where {
};

instance Arith.Numeral Real where {
};

instance Arith.Semiring_numeral Real where {
};

instance Arith.Zero_neq_one Real where {
};

instance Arith.Semiring_1 Real where {
};

instance Arith.Semiring_1_cancel Real where {
};

instance Arith.Comm_monoid_mult Real where {
};

instance Arith.Comm_semiring_1 Real where {
};

instance Arith.Comm_semiring_1_cancel Real where {
};

instance Arith.Comm_semiring_1_cancel_crossproduct Real where {
};

instance Arith.Semiring_no_zero_divisors Real where {
};

instance Arith.Semiring_1_no_zero_divisors Real where {
};

instance Arith.Semiring_no_zero_divisors_cancel Real where {
};

instance Arith.Uminus Real where {
  uminus = uminus_real;
};

instance Arith.Group_add Real where {
};

instance Arith.Ab_group_add Real where {
};

instance Arith.Ring Real where {
};

instance Arith.Ring_no_zero_divisors Real where {
};

instance Arith.Neg_numeral Real where {
};

instance Arith.Ring_1 Real where {
};

instance Arith.Ring_1_no_zero_divisors Real where {
};

instance Arith.Comm_ring Real where {
};

instance Arith.Comm_ring_1 Real where {
};

instance Arith.Semidom Real where {
};

instance Arith.Idom Real where {
};

inverse_real :: Real -> Real;
inverse_real (Real_of_u r) = Real_of_u (Real_Unique_Impl.mau_inverse r);

divide_real :: Real -> Real -> Real;
divide_real x y = times_real x (inverse_real y);

instance Unique_Factorization.Ufd Real where {
};

instance Arith.Divide Real where {
  divide = divide_real;
};

instance Arith.Divide_trivial Real where {
};

instance Arith.Inverse Real where {
  inverse = inverse_real;
};

instance Arith.Division_ring Real where {
};

instance Arith.Semidom_divide Real where {
};

instance Arith.Idom_divide Real where {
};

instance Arith.Field Real where {
};

less_eq_real :: Real -> Real -> Bool;
less_eq_real (Real_of_u x) (Real_of_u y) =
  equal_real (Real_of_u x) (Real_of_u y) ||
    (if Real_Unique_Impl.mau_compatible x y
      then Real_Impl.ge_0 (minus_real (Real_of_u y) (Real_of_u x))
      else Real_Unique_Impl.real_lt (Real_of_u x) (Real_of_u y));

instance Orderings.Ord Real where {
  less_eq = less_eq_real;
  less = less_real;
};

instance Arith.Abs_if Real where {
};

instance Arith.Semiring_char_0 Real where {
};

instance Arith.Ring_char_0 Real where {
};

instance Quasi_Order.Quasi_order Real where {
};

instance Quasi_Order.Weak_order Real where {
};

instance Orderings.Preorder Real where {
};

instance Orderings.Order Real where {
};

instance Orderings.No_bot Real where {
};

instance Orderings.No_top Real where {
};

instance Orderings.Linorder Real where {
};

instance Arith.Idom_abs_sgn Real where {
};

instance Arith.Ordered_ab_semigroup_add Real where {
};

instance Arith.Strict_ordered_ab_semigroup_add Real where {
};

instance Arith.Ordered_cancel_ab_semigroup_add Real where {
};

instance Max_Polynomial_Aux.Ordered_semigroup_mult_zero Real where {
};

instance Arith.Ordered_comm_monoid_add Real where {
};

instance Arith.Ordered_semiring Real where {
};

instance Arith.Ordered_semiring_0 Real where {
};

instance Arith.Ordered_cancel_semiring Real where {
};

instance Arith.Ordered_ab_semigroup_add_imp_le Real where {
};

instance Arith.Strict_ordered_comm_monoid_add Real where {
};

instance Arith.Ordered_cancel_comm_monoid_add Real where {
};

instance Arith.Ordered_ab_semigroup_monoid_add_imp_le Real where {
};

instance Arith.Ordered_ab_group_add Real where {
};

instance Arith.Ordered_ring Real where {
};

instance Arith.Field_char_0 Real where {
};

instance Arith.Zero_less_one Real where {
};

instance Arith.Field_abs_sgn Real where {
};

instance Orderings.Dense_order Real where {
};

instance Arith.Ordered_semiring_strict Real where {
};

instance Arith.Linordered_ab_semigroup_add Real where {
};

instance Arith.Linordered_cancel_ab_semigroup_add Real where {
};

instance Arith.Linordered_semiring Real where {
};

instance Arith.Linordered_semiring_strict Real where {
};

instance Arith.Ordered_semiring_1 Real where {
};

instance Arith.Ordered_semiring_1_strict Real where {
};

instance Max_Polynomial_Aux.Ordered_semiring_1 Real where {
};

instance Arith.Linordered_semiring_1 Real where {
};

instance Arith.Linordered_semiring_1_strict Real where {
};

instance Arith.Ordered_ab_group_add_abs Real where {
};

instance Arith.Linordered_ab_group_add Real where {
};

instance Arith.Linordered_ring Real where {
};

instance Arith.Linordered_ring_strict Real where {
};

instance Arith.Ordered_comm_semiring Real where {
};

instance Arith.Ordered_cancel_comm_semiring Real where {
};

instance Arith.Ordered_comm_semiring_strict Real where {
};

instance Arith.Linordered_comm_semiring_strict Real where {
};

instance Arith.Linordered_nonzero_semiring Real where {
};

instance Arith.Linordered_semidom Real where {
};

instance Arith.Ordered_comm_ring Real where {
};

instance Arith.Ordered_ring_abs Real where {
};

instance Arith.Linordered_idom Real where {
};

instance SN_Orders.Non_strict_order Real where {
};

instance SN_Orders.Ordered_ab_semigroup Real where {
};

instance SN_Orders.Ordered_semiring_0 Real where {
};

instance SN_Orders.Ordered_semiring_1 Real where {
};

instance SN_Orders.Poly_carrier Real where {
};

instance Orderings.Unbounded_dense_order Real where {
};

instance Orderings.Dense_linorder Real where {
};

instance Orderings.Unbounded_dense_linorder Real where {
};

instance Arith.Linordered_field Real where {
};

floor_real :: Real -> Arith.Int;
floor_real (Real_of_u r) = Real_Unique_Impl.mau_floor r;

instance Archimedean_Field.Archimedean_field Real where {
};

instance SN_Orders.Large_ordered_semiring_1 Real where {
};

instance Matrix_Core_Order.SN_delta_order Real where {
};

instance Archimedean_Field.Floor_ceiling Real where {
  floor = floor_real;
};

ratreal :: Rat.Rat -> Real;
ratreal = Real_of_u . Real_Unique_Impl.mau_of_rat;

}
